from hier import *
import time, sys
avg = lambda B: (B+1)/2 - 1/B
def ms(B, L1, tc, **kw):
    v = min_speed(B, L1, lo=avg(B)*0.999, **kw, top_cycles=tc)
    return max(v, avg(B))
def main():
    Bsel = [int(x) for x in sys.argv[1:]] or [2,4,8]
    cfg = {2: [(4,400),(6,100),(8,25)], 4: [(3,100),(4,50),(5,12)], 8: [(3,20),(4,4)]}
    cases = [
        ('paper/move   (f=2,W=2)', dict(policy='lease', f=2, W=2, adopt='move')),
        ('paper/pointer(f=2,W=2)', dict(policy='lease', f=2, W=2, adopt='pointer')),
        ('code', None),
        ('fungible 3B-1 move', dict(policy='fungible', adopt='move')),
        ('fungible 3B-1 pointer', dict(policy='fungible', adopt='pointer')),
        ('lease W=3 pointer (4B-1)', dict(policy='lease', f=2, W=3, adopt='pointer')),
    ]
    for B in Bsel:
        for name, kw in cases:
            if kw is None:
                if B == 2: kw = dict(policy='lease', f=2, W=2, adopt='install', install_cost=1.0)
                elif B == 4: kw = dict(policy='lease', f=2, W=2, adopt='pointer')
                else: kw = dict(policy='lease', f=4, W=2, adopt='pointer')
            row = []
            for L1, tc in cfg[B]:
                t = time.time()
                row.append(f'L1={L1},tc={tc}: {ms(B, L1, tc, **kw):.4f}')
            print(f'B={B} {name:28s}', ' | '.join(row), flush=True)
big_stack(main)
