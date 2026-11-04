# Results saved for the next research session

These manuscripts and exact certificates preserve work in progress. They
are **not closed gates** in the main roadmap. Their supplied exact replays
passed during discovery, but an independent mathematical/source audit is
still required before promotion. No result here closes either unrestricted
radial case.

- `LEAF_NEIGHBOR_RADIUS.md`: localizes a full-angle stress leaf's neighbor
  inside radius 6/5, potentially linking graph leaves to the four-core shell.
- `FIVE_CORE_JUNCTION_EXCLUSION.md`: excludes a four-way junction from a
  retained five-body stress component and derives planar physical contacts.
- `ring_geometry/`: single-ring width and two common-point sector
  certificates. At circle radius 5/4 the certified single width is 63/100
  and the pair span exceeds 27/20. At circle radius 27/20 the pair span
  exceeds 36/25, for centers at radius at least 11/10.

Run the saved ring replays from the repository root:

```sh
PYTHONPATH=research/eleven/arc_budget python3 research/eleven/pending/ring_geometry/check_ring_width_cover.py
PYTHONPATH=research/eleven/arc_budget python3 research/eleven/pending/ring_geometry/check_sector_point135_cover.py
PYTHONPATH=research/eleven/arc_budget python3 research/eleven/pending/ring_geometry/check_native_sector_point_cover.py
PYTHONPATH=research/eleven/arc_budget python3 research/eleven/pending/ring_geometry/check_four_core_gap_counterexample.py
```

The checkers import the established `exact_arcs.py` but no optimizer or
generator. Future review must check geometric normalization, endpoint
formulas, rotation intervals, and Taylor bounds as well as replaying nodes.
Shared arithmetic between generator and replay does not constitute an
independent mathematical audit.

On the radius-5/4 circle, a split core arc can enclose a ring arc in its
internal gap. Keep the raw components there. The main split-gap theorem
allows filling only on the radius-27/20 circle. A capacity-at-most-six
conjecture for four cores failed with the earlier 13/10 pair threshold;
the stronger 27/20 threshold had promising searches but no exhaustive proof.
