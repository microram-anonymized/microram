"""Check the B-ary closed forms against both event simulators.

Run from the repository root:
python analysis/deamortization/prior_work/check_closed_form.py
The checks are in analysis/deamortization; this adds the B-ary simulator in
simulate.py as a second implementation of the same model.
"""
from simulate import branching_probe_average, branching_streamable_no_stall
# simulate.py puts analysis/deamortization on the module path.
from check_deamortization_closed_form import check
from deamortization_analysis import average_probes_per_level, streamable_no_stall


def main() -> None:
    check((streamable_no_stall, branching_streamable_no_stall),
          (average_probes_per_level, branching_probe_average))
    print("Both event simulators agree for B=2..64, including threshold checks.")


if __name__ == "__main__":
    main()
