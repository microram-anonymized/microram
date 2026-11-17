from hier import *
import sys
avg = lambda B: (B+1)/2 - 1/B
def ms(B, L1, tc, **kw):
    return max(min_speed(B, L1, lo=avg(B)*0.999, top_cycles=tc, **kw), avg(B))
def main():
    for B, L1, tc in ((4,4,40),(8,3,16)):
        for adopt in ('move','pointer'):
            row=[]
            for cap in range(3*B-1, 4*B+1):
                row.append(f'{cap}:{ms(B,L1,tc,policy="fungible",cap=cap,adopt=adopt):.3f}')
            print(B, adopt, ' '.join(row), flush=True)
big_stack(main)
