from hier import *
import time
def main():
    for B, L1, tc in ((2,4,2000),(4,4,100),(8,3,40)):
        t=time.time()
        print(B, L1, tc, 'model', min_speed(B, L1, policy='model', top_cycles=tc), f'{time.time()-t:.1f}s', flush=True)
big_stack(main)
