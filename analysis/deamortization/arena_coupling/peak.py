"""Peak storage that the model's own schedule (policy 'model', speed s*) occupies
at one level, counting every table the level must keep: outgoing tables until
the next level retires them, its published partial until the next merge
publishes, and the output under construction from the start of pre-routing."""
from hier import *
def peak(B, L1, s, tc, adopt):
    sim = Sim(B, L1, s, policy='model', top_cycles=tc, adopt=adopt).run()
    best = {}
    for l in range(L1 - 1):          # levels whose consumer is non-top
        ev = []
        cnt = sim.counts[l]
        for n in range(cnt - 1):
            j = n % B + 1
            if j == 1:
                if adopt == 'move' or l == 0:
                    ev.append((sim.D[l][n], +1)); ev.append((sim.D[l][n+1], -1))
                continue
            st = sim.Pst[l][n]
            if j < B:
                ev.append((st, +j)); ev.append((sim.D[l][n+1], -j))
            else:
                m = n // B
                r = sim.ret(l+1, m)
                if r == INF: continue
                ev.append((st, +B)); ev.append((r, -B))
        ev.sort(key=lambda e: (e[0], e[1]))   # frees before allocations at ties
        cur = mx = 0
        for t, dlt in ev:
            cur += dlt; mx = max(mx, cur)
        best[l] = mx
    return best
def main():
    for B, s, L1, tc in ((2, 1.0, 5, 40), (4, 2.25, 4, 20), (8, 4.5, 3, 12)):
        for adopt in ('move', 'pointer'):
            print(f'B={B} s={s} {adopt:7s} peak units per level (own carry units; 3B-1 = {3*B-1}):', peak(B, L1, s, tc, adopt))
big_stack(main)
