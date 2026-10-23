# Eleven squares exact feasible upper bound

The eleven unit squares specified in `RATIONAL_WITNESS.json` fit in the disk
centered at the origin with squared radius

\[
U=\frac{49013}{10000}=4.9013.
\]

This proves an upper bound on the unrestricted optimum. It does not identify
the sharp radius, reproduce the record exactly, prove a global lower bound, or
classify equality packings.

## Source and candidate provenance

Friedman's [Squares in Circles page](https://github.com/erich-friedman/erich-friedman.github.io/blob/fdd850479b5ce687899a4400135ac3cb6fcf5b56/packing/squincir/index.html)
credits Milan Kovacic, May 2006, with the eleven-square packing and prints
`r = 2.21386+`. The same page says that only cases one through eight have been
proved optimal. Its [eleven-square illustration](https://github.com/erich-friedman/erich-friedman.github.io/blob/fdd850479b5ce687899a4400135ac3cb6fcf5b56/packing/squincir/11.gif)
is a source for a candidate layout, not an exact coordinate or lower-bound
certificate. Both sources were read through the GitHub connector on 23 October
2026; the pinned source commit is `fdd850479b5ce687899a4400135ac3cb6fcf5b56`.

The rational witness below was discovered from that layout with seven parallel
squares and two differently tilted pairs. A numerical fixed-owner optimization
found squared radius approximately `4.901206412408145`, radius approximately
`2.2138668461332864`. Those decimals are discovery diagnostics only. Centers were
expanded slightly and both centers and half-angle parameters rounded to
rationals; the resulting rational data was then checked independently of the
optimizer with exact integer arithmetic. The certificate has no dependency on
SciPy, floating-point rounding, or the printed record decimal.

## Exact square data

Set `D = 100000000`. A row `(X,Y,T)` denotes center `(X/D,Y/D)` and frame

\[
t=T/D,\quad c=\frac{1-t^2}{1+t^2},\quad s=\frac{2t}{1+t^2},\qquad
u=(c,s),\quad v=(-s,c).
\]

The identity `(1-t²)²+4t²=(1+t²)²` proves that this is an orthonormal frame,
without a trigonometric approximation. The square is
`{p + a u + b v : |a|≤1/2, |b|≤1/2}`.

| Label | X | Y | T |
| --- | ---: | ---: | ---: |
| 0 | 39752991 | 152377206 | 0 |
| 1 | 32432465 | 52377106 | 0 |
| 2 | 139753091 | 64043397 | 0 |
| 3 | 154018573 | -35956703 | 0 |
| 4 | 54018473 | -47622994 | 0 |
| 5 | 49785997 | -147623094 | 0 |
| 6 | -50214103 | -147406347 | 0 |
| 7 | -152244639 | -65322531 | 20547404 |
| 8 | -61645756 | -22864064 | 20547404 |
| 9 | -141301807 | 52567893 | 24971819 |
| 10 | -77883254 | 146217858 | 24971819 |

## Finite feasibility certificate

For a unit direction `a`, define the square's support half-width

\[
h_i(a)=\tfrac12\bigl(|a\cdot u_i|+|a\cdot v_i|\bigr).
\]

The JSON lists one signed direction `a = sign * u_owner` or
`a = sign * v_owner` for each unordered pair `i<j`. It has exactly the 55
possible pairs, with no omissions or duplicates. Direct rational evaluation
establishes the following two finite statements:

1. For all eleven labels and all four sign pairs `(e,f)∈{−1,1}²`,
   `|p_i + (e u_i + f v_i)/2|² ≤ U − 1/20000`.
2. For every listed pair separator,
   `a·(p_j−p_i) ≥ h_i(a)+h_j(a)+1/2000000`.

These statements imply disk containment and disjoint interiors. The four
vertices of each square lie in a convex disk, so their convex hull does too.
For a listed direction, the projection intervals of the two squares are
separated by at least `1/2000000`, so the squares are disjoint even as closed
sets. The support formula follows by maximizing two independent linear
coordinates over `[-1/2,1/2]²`.

`check_rational_witness.py` checks exactly those two statements with Python's
standard-library `Fraction`, including the unit-frame identities and complete
pair coverage. Its successful run reports 11 frames, 44 vertex bounds, and
55 pair separators. This is an auditable exact arithmetic check of one
explicit witness; it is not a Lean kernel proof or an exhaustive packing
classification. The arithmetic obligations and their margins are stated here
so a later formal proof can reproduce them without trusting Python.

Run from the directory containing both files:

```sh
python check_rational_witness.py
```

## A small hand-checkable fallback

An independent, weaker witness gives squared radius `5`. Start with all
axis-parallel unit squares centered at

\[
(x,y)\in\{-3/2,-1/2,1/2,3/2\}^2
\]

except the four choices with `|x|=|y|=3/2`, and delete any one of the remaining
twelve squares. Grid spacing gives disjoint interiors. Every retained square
has its farthest vertex with absolute coordinates at most `(2,1)` or `(1,2)`,
so its squared norm is at most five. This verifies a simple baseline without
large rational constants.

## Gate consequences

- A feasible unrestricted eleven-square upper bound is closed: `q_opt ≤ U`.
- Subsequent global reductions may restrict attention to `0 ≤ q ≤ U`.
- No proof of the exact Kovacic candidate, its stationarity, sharp lower bound,
  or its complete equality family follows from this certificate. Those are
  separate open gates.

[The contact-system construction](CANDIDATE_CONTACT_SYSTEM.md) separately
closes exact existence and local root isolation for the reconstructed family,
with a slightly tighter attained squared radius q_c. The rational witness
above remains an independent simple certificate and a safe search-window
bound. Unrestricted optimality and complete equality remain open.
