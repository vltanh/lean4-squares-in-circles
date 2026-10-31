# Root review: the complete weak quarter-disk nine-square obstruction

Date: October 26, 2026.

**Decision: ACCEPT the uniform weak-distance arc-measure lemma and the
whole nine-square central-disk exclusion.** The additional fan root-margin
premise remains explicitly open.

Reviewed source: `CHORDED_HEXAGON_QUARTER_DISK_COMPLETION_OBSTRUCTION.md`.
Exact mathematical source pin before acceptance-status edits:

    1cbdbfea6a19153074850222d7beb8ae48f9b35fbd215dae9998d9542ad25d59

The full source and the complete Section 1 of
`GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md` were read together. The new
proof uses only contained actual unit geometry and angular measure;
it does not inherit a simple-cycle force or connected-arc premise at
the weak endpoint.

## 1. Complete weak-distance extension

Normalize the actual square to [A,a] by [B,b], a=A+1, b=B+1 and
a>=b>=1/2, as in the existing whole-orientation proof. For a>5/4,
the entire old inner-face proof uses A>1/4 and the upper radius bound,
not strictness of the given nearest distance. Its strict arc-length
reserves therefore apply unchanged.

For a<=5/4 and B>0, k^2=A^2+B^2 is now at least 1/16. The exact
outer-outer derivative factor

    (A-B)[(A+B-1/4)^2+(k^2-1/16)(A+B+1)]

remains nonnegative. The symmetric endpoint lower bound is weak in k,
but its final comparison with pi/4 remains strict by the existing
positive reserve (16-9sqrt(2))/100. The other three interval-difference
estimates keep their old strict reserves. Infinite derivative endpoints
are included by continuity, not omitted.

The only genuinely new case B<=0 has A=1/4, a=5/4 and
-1/2<=B<=0. The right-circle branch has y strictly between B and B+1;
throughout it x>=3/4>1/4. The outer x restriction removes only theta=0,
if that point was present. It does not change angular measure. The
total measure is

    asin(b/(5/4))-asin((b-1)/(5/4))
      >=2 asin(2/5)>pi/4.

The difference is minimized at b=1/2 by its exact derivative sign.
The possible two open arcs and the lost radial outer-face point are
explicitly retained. Thus no connectedness or radial-point-interior
claim is mistakenly extended to equality.

## 2. Complete nine-body application

If a real unit H contains closed D_(1/4), open D_(1/4) lies in int H.
No other physical unit can contain even a boundary point of that open
disk, since its open interior would then meet int H nearby. Every other
unit has nearest distance at least 1/4. Its open-interior circle subset
has measure greater than pi/4 by the full lemma above.

The eight subsets are pairwise disjoint because the eight unit open
interiors are disjoint. Their total measure exceeds 2pi, impossible.
All eight physical squares count, whether or not they are in a positive
component or touch the containing circle. The theorem includes every
weak containment endpoint and uses only R^2<=1105/256.

In H's actual own coordinates, containing the closed quarter-disk is
exactly |x|<=1/4 and |y|<=1/4 for its center. Therefore every physical
unit in such a nine-packing has max(|x|,|y|)>1/4. This is a proved
necessary condition, not an arbitrary choice of an advantageous frame.

## 3. Original fan limitations

The full triangulated exterior fan has zero central capacity, and its
direct boundary-pair exterior pockets are empty. Its three extra units
therefore lie in its actual remaining hub pocket. The new theorem
would exclude that whole graph if a separate proof forced its actual
hub to contain D_(1/4). That margin has not been proved here. In
particular neither a numerical star search nor a relaxed center model
can supply it, and no degree-five hub is made a transmitter.

No graph/load label or coarse cell closes by this source alone. All
actual masks, mean endpoints and positive forces remain in its intended
fan application. No sampled pose, Lean compilation, CI or shared-ledger
edit was used in this review.
