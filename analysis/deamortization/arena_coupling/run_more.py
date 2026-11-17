from hier import *
avg = lambda B: (B+1)/2 - 1/B
def ms(B, L1, tc, **kw):
    return max(min_speed(B, L1, lo=avg(B)*0.999, top_cycles=tc, **kw), avg(B))
def main():
    print('B=4 code (pointer,f=2) L1=6', ms(4,6,4,policy='lease',f=2,W=2,adopt='pointer'), flush=True)
    print('B=8 code (pointer,f=4) L1=5', ms(8,5,2,policy='lease',f=4,W=2,adopt='pointer'), flush=True)
    print('B=8 paper move f=2 L1=5', ms(8,5,2,policy='lease',f=2,W=2,adopt='move'), flush=True)
    print('B=8 code but move (f=4) L1=4', ms(8,4,4,policy='lease',f=4,W=2,adopt='move'), flush=True)
    for adopt in ('move','pointer'):
        print('B=4 S=B+1 (13 units) lease f=4', adopt, ms(4,5,12,policy='lease',f=4,W=2,adopt=adopt), flush=True)
    for x in (0.1,0.25,0.5,1.0):
        print('B=2 code install x=',x, ms(2,6,100,policy='lease',f=2,W=2,adopt='install',install_cost=x), flush=True)
    for x in (0.1,0.25,0.5,1.0):
        print('B=4 paper f=2 copy-adopt x=',x, ms(4,5,12,policy='lease',f=2,W=2,adopt='install',install_cost=x), flush=True)
    for x in (0.0,0.1,0.25,0.5):
        print('B=8 code f=4 copy-adopt x=',x, ms(8,4,4,policy='lease',f=4,W=2,adopt='install',install_cost=x), flush=True)
big_stack(main)
