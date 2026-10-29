# Independent audit of the two pending two-row extensions

Date: 2026-10-29. Reviewer: `audit_two_rows`.

**Result: both stated conditional theorems pass the mathematical audit.**
No gap was found in either extension. This is a review of hand arguments,
not a Lean or other kernel verification. It does not prove that an arbitrary
four-inner-square configuration has the required two-row form.

The audit read `WIDE_DISPLACEMENT_TWO_ROW.md`,
`SEPARATED_LOWER_TWO_ROW.md`, `EXTREME_ASYMMETRIC_TWO_ROW.md`,
`ASYMMETRIC_TWO_ROW_COMPLETION.md`,
`GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md`, and `THREE_SQUARE_CAP.md`.
The already established center-radius arc theorem, universal center bound,
corner lemma and sharp cap theorem are used as cited dependencies.

## Wider displacement theorem

The statement is valid for the touching lower pair, unequal upper offsets,
and the full open range `0<t<3/2-2^(-1/4)`.

1. The constant replacements in the small-displacement branch are valid.
   In particular, the tight comparison is
   `81/121-1071/1600=9/193600>0`. The upper-sector horizontal estimate is
   exactly `772125/978944<81/100`, and the middle-opening clearance bound
   is exactly `39049/160000<1/4`. The replacements also preserve every
   corner-separator exclusion: `z>43/40`, `A-z<39/80<1/2`, the positive
   support projection exceeds `17/16`, and the auxiliary-vector squared
   norm is at most `2t<17/20<1`. The unchanged noncrossing branch is
   independent of the enlarged upper endpoint for `t`.
2. In the remaining range, the lower rectangle covers every unit-disk
   horizontal coordinate below `h`; the upper pair has horizontal miss
   at most `B-1/2<9/20` and vertical miss less than `1/6`. Thus the
   stated distance bound `829/3600<1/4` proves all additional centers
   exterior, including the case `h<0` and `z<1`.
3. The lower traces have `delta>pi/4`, and the upper-left retained trace
   has `alpha<=gamma<beta`. Consequently the complementary gaps have
   strict bounds `<pi/2`, `<pi/2`, and `<pi`, giving capacities `1,1,3`.
   Clipping the retained upper trace to its quadrant when `h<=0` creates
   no extra gap; it only makes `alpha=0` possible.
4. For completeness, the upper-left inward top corner is inside the
   test circle because
   `(b_L-1/2)^2+z^2 <= 5/2-t-b_L <= 2-t < 2-t_* < r^2`.
   The last inequality follows already from `t_*>1/3` and `r^2>5/3`.
   The other inward corner has an even smaller absolute vertical
   coordinate. This fills in a harmless unstated estimate in Section 3.

The endpoint `t=t_*` is covered by Section 1. The upper endpoint of the
whole theorem is correctly strict, as required by the outward-corner and
retained-arc inequalities.

## Separated lower pair theorem

The statement is valid for `1/2<=a<=1/sqrt(2)` and `0<t<=5/12`, with the
same upper-center constraints and arbitrary orientations of the extras.

1. The unit-disk clearance estimate is uniform in the lower gap:
   `d<1/4`, `t>1/8`, and `d^2+(1/2-t)^2<13/64<1/4`.
   The upper-pair estimate uses only its upper-center constraints.
2. The lower arc angles satisfy `pi/8<=gamma_a<=gamma_0<pi/4`.
   If the lower pair does not cross the circle, then `t<=t_0`, so the
   earlier noncrossing proof applies. If it crosses, `delta>gamma_a`
   keeps the bottom capacity at most two. The side capacities and the
   impossibility of two double side gaps follow with `gamma_a` replacing
   `gamma_0`; in particular `r*sin(gamma_a)<=2^(-1/4)`.
   The upper-sector clearance proof is independent of the lower pair's
   touching and applies unchanged.
3. In the extreme-asymmetry branch, `b_R<1/4` implies
   `t>1-sqrt(7)/4>1/3`. The three retained gaps have capacities `1,2,3`,
   and six extras therefore require three in the large gap. The prior
   upper-sector clearance reduces their center angles exactly as stated.
4. The virtual rectangle argument is valid. Its slot has
   `d<=1/sqrt(2)-1/2<1/4`. Its whole top is in the upper-right square:
   `b_R-1/2<-1/4<-d` and `b_R+1/2>d`.
   Its two sides are in the lower squares. Any hypothetical interior
   point of an extra square in the slot forces its center to satisfy
   `0<x<d+1/sqrt(2)<11/12` and
   `y>-187/240>-5/6>-t-1/2`.
   The center is outside the closed slot, whose points all have norm
   less than one. The segment from the interior slot point to the center
   stays in the extra square's interior and above the open bottom, so it
   exits through a side or top contained in an actual core square.
   Even a boundary point of a full-dimensional core square cannot be
   interior to a disjoint extra square. This is the desired contradiction.
   Openness separately excludes the otherwise uncovered slot bottom.
5. The subsequent corner lemma uses only separation from this virtual
   rectangle, the stated center-angle bounds, `t>1/4`, and the upper
   constraints. It does not require that the virtual rectangle be
   literally filled by the original core. The corner auxiliary-vector
   bounds and cap-rigidity contradiction therefore remain valid.

Optional exposition improvements are to insert the explicit upper inward
corner estimate in the wider theorem and the explicit slot-top inclusion
in the separated-pair theorem. They are consequences of the displayed
hypotheses, not additional assumptions or repairs to the proofs.
