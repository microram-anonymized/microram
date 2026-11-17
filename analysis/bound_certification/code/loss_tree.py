"""Positive, fixed-point certificates for a binary shadow-loss tree.
All distribution entries are upper integers / 2**BITS. Thinning and
convolution use exact nonnegative integer arithmetic, rounded upwards.
An optional GMP helper accelerates integer squaring; no floating-point FFT.
"""
from __future__ import annotations
import ctypes
import math
import sys
import time
from pathlib import Path
from fractions import Fraction
from decimal import Decimal, localcontext

HERE=Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from certify_oram import (LAM, UP, ZERO, ONE, exp_upper, upper_fraction,
                              weighted_poisson_pmf, certificate, describe)
BITS=512
SCALE=1<<BITS
K=256
Z=64

def ceildiv(x:int,y:int)->int:
    return (x+y-1)//y

def dec_scaled(x:Decimal)->int:
    f=Fraction(x)*SCALE
    return ceildiv(f.numerator,f.denominator)

def initial():
    p=weighted_poisson_pmf(LAM,Fraction(0),K)
    f=[[0]*(K+1) for _ in range(Z+1)]
    for n in range(K+1):
        f[min(n,Z)][max(n-Z,0)]=dec_scaled(p[n])
    return f

def thin_matrix(f):
    """Independently thin main and shadow counts with probability 1/2."""
    # B[r][j] / 2**K = Bin(r,1/2) mass at j.
    B=[[math.comb(r,j) << (K-r) for j in range(r+1)] for r in range(K+1)]
    t=[[0]*(K+1) for _ in range(Z+1)]
    for m in range(Z+1):
        accum=[0]*(K+1)
        for r,fr in enumerate(f[m]):
            if fr:
                for j,w in enumerate(B[r]):
                    accum[j]+=fr*w
        t[m]=[ceildiv(a,1<<K) for a in accum]
    C=[[math.comb(m,i) << (Z-m) for i in range(m+1)] for m in range(Z+1)]
    q=[[0]*(K+1) for _ in range(Z+1)]
    for j in range(K+1):
        accum=[0]*(Z+1)
        for m in range(Z+1):
            if t[m][j]:
                for i,w in enumerate(C[m]):
                    accum[i]+=t[m][j]*w
        for i,a in enumerate(accum):
            q[i][j]=ceildiv(a,1<<Z)
    return q

_warned_no_gmp=False

def _warn_no_gmp():
    """Once per process: the fallback is exact but can turn minutes into hours."""
    global _warned_no_gmp
    if _warned_no_gmp: return
    _warned_no_gmp=True
    headers=any(Path(p).exists() for p in
                ('/usr/include/gmp.h','/usr/include/x86_64-linux-gnu/gmp.h'))
    hint=('' if headers else
          ' GMP headers were not found; install them first (Debian/Ubuntu: '
          'sudo apt install libgmp-dev).')
    print(f'WARNING: {HERE/"libgmp_square.so"} is missing, so exact squaring '
          'runs in pure Python; certify_separated_sources.py can take hours. '
          f'Build it with: g++ -O3 -shared -fPIC {HERE/"gmp_square.cpp"} '
          f'-lgmp -o {HERE/"libgmp_square.so"}.{hint}',
          file=sys.stderr, flush=True)

def square_bytes(raw:bytes)->bytes:
    libpath=HERE/'libgmp_square.so'
    if libpath.exists():
        lib=ctypes.CDLL(str(libpath))
        fn=lib.square_le
        fn.argtypes=[ctypes.c_void_p,ctypes.c_size_t,ctypes.c_void_p,ctypes.c_size_t]
        fn.restype=ctypes.c_int
        src=ctypes.create_string_buffer(raw)
        dst=ctypes.create_string_buffer(2*len(raw))
        status=fn(src,len(raw),dst,len(dst))
        if status: raise RuntimeError(f'GMP square status {status}')
        return dst.raw
    # Same exact arithmetic without an external dependency; slower.
    _warn_no_gmp()
    value=int.from_bytes(raw,'little')
    return (value*value).to_bytes(2*len(raw),'little')

def next_tree(f):
    q=thin_matrix(f)
    stride=2*K+1
    digit_bytes=(2*BITS+20+7)//8
    max_index=Z*stride+K
    assert max(max(row) for row in q) <= 2*SCALE
    # A convolution coefficient has at most (Z+1)(K+1) products.
    assert (Z+1)*(K+1)*(2*SCALE)**2 < 1 << (8*digit_bytes)
    raw=bytearray((max_index+1)*digit_bytes)
    for m in range(Z+1):
        for r,value in enumerate(q[m]):
            idx=m*stride+r
            raw[idx*digit_bytes:(idx+1)*digit_bytes]=value.to_bytes(digit_bytes,'little')
    sq=square_bytes(bytes(raw))
    result=[[0]*(K+1) for _ in range(Z+1)]
    for u in range(2*Z+1):
        for v in range(K-u+1):
            idx=u*stride+v
            coefficient=int.from_bytes(sq[idx*digit_bytes:(idx+1)*digit_bytes],'little')
            result[min(u,Z)][v+max(u-Z,0)]+=coefficient
    return [[ceildiv(value,SCALE) for value in row] for row in result]

def thinned_weights(f,h):
    raw=[sum(f[m][r] for m in range(Z+1)) for r in range(K+1)]
    if h==0:
        return raw
    d=1<<h
    acc=[0]*(K+1)
    den=1<<(h*K)
    powers=[(d-1)**i for i in range(K+1)]
    for r,pr in enumerate(raw):
        if pr:
            factor=pr << (h*(K-r))
            for e in range(r+1):
                acc[e]+=factor*math.comb(r,e)*powers[r-e]
    return [ceildiv(a,den) for a in acc]

def truncation_error(t,g,h):
    # Every node's ideal main+shadow population is Pois(LAM).
    p=weighted_poisson_pmf(LAM,Fraction(0),K+1)[K+1]
    with localcontext(UP):
        # tail <= p[K+1]/(1-LAM/(K+2)); denominator evaluated exactly.
        tail=p*upper_fraction(1/(1-LAM/Fraction(K+2)))
        mu=LAM/Fraction(1<<h)
        second=upper_fraction(mu+mu*mu)
        value=second*((1<<t)-1)*tail
        root=UP.next_plus(UP.sqrt(value))
        return g*root

def loss_certificate(f,t,g,h,patterns=1,slots=64):
    wi=thinned_weights(f,h)
    w=[ZERO]+[upper_fraction(Fraction(wi[e],SCALE)) for e in range(1,K+1)]
    with localcontext(UP):
        w2=sum((w[e]*(1<<e) for e in range(1,K+1)),ZERO)
        base=certificate(w,w2,g,slots)
        err=truncation_error(t,g,h)
        return patterns*(base+err)

def save_tree(f,t):
    import json
    path=HERE/f'tree_{t}.json'
    path.write_text(json.dumps({'bits':BITS,'cutoff':K,'depth':t,'upper_scaled':f}))
    return path

def load_tree(t):
    import json
    a=json.loads((HERE/f'tree_{t}.json').read_text())
    assert a['bits']==BITS and a['cutoff']==K and a['depth']==t
    return a['upper_scaled']

if __name__=='__main__':
    f=initial()
    for t in range(1,5):
        start=time.time()
        save_tree(f,t)
        for h,g in [(0,2**16),(1,2**17),(2,2**18),(4,2**20)]:
            b=loss_certificate(f,t,g,h,64)
            print(t,h,g,describe('',b)['approximate_log2_for_display_only'],flush=True)
        if t<4:
            f=next_tree(f)
        print('elapsed',time.time()-start,flush=True)
