"""B = 4, s = 2.25: the model's schedule at level 2 (0-based 1) and the times at
which the next level frees the full-size regions, in level-2 carry intervals,
relative to the arrival of the cycle's first carry."""
from hier import *
def main():
    B, s, L1 = 4, 2.25, 4
    sim = Sim(B, L1, s, policy='model', top_cycles=10, adopt='move').run()
    l = 1; dl = sim.delta[l]
    for c in range(40, 48):
        t0 = sim.arr(l, c * B)
        rel = lambda t: (t - t0) / dl
        n = c * B
        st = [rel(sim.Pst[l][n + k]) for k in range(1, B)]
        Dn = [rel(sim.D[l][n + k]) for k in range(B)]
        r2 = rel(sim.ret(l + 1, c - 2)); r1 = rel(sim.ret(l + 1, c - 1))
        print(f'cycle {c}: P(c-2) is next-level digit {(c-2)%B+1}, freed {r2:5.2f}; P(c-1) digit {(c-1)%B+1} freed {r1:5.2f}; '
              f'publications {[round(x,2) for x in Dn]}; merge starts {[round(x,2) for x in st]}')
big_stack(main)
