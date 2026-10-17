# Exact center-only relaxation witness for the surviving S2 / k=4 case

Research continuation, 2026-10-12. This is a **negative-results
guardrail about a relaxation**, not an eight-square packing.

The exclusive S2=(3+0,2+2) status branch with k=3 is now
eliminated analytically, but S2/k=4 remains open.
A tempting next shortcut would be to exclude its subcase
with both *near* 2+2 centers inner and two of the
perpendicular triple centers outer **using only the following**:

1. the radius-\(1/2\) inscribed-disk center separation \(|p_i-p_j|\ge1\);
2. each square's necessary radial center envelope
   \(r_i^2+r_i+1/2\le9789/2500\);
3. a central center \((a,b)\in(-1/2,1/2)^2\);
4. the central whole-side projection **necessary** inequalities
   \(p_x\ge h_R+1/2\), \(p_y\ge h_U+1/2\),
   \(p_y\le-(3/2-h_U)\);
5. the chosen labels' center norms <1 or >=1.

The following **exact rational coordinates satisfy every one**
of these necessary constraints, all with strict margins.
Therefore a proof must use actual square frames, true disk vertices,
or real square-square separating axes to rule out this S2/k4 region.
These eight points are **not claimed to support eight unit squares**.

## Rational center data

Take
\[
q_{\rm plus}=9789/2500,\quad
h_R=1/1000,\quad h_U=293/1000,\quad
h_D=1-h_U=707/1000.
\]
The central square center is
\[
p_C=(h_R-1/2,h_U-1/2)=(-499/1000,-207/1000).
\]

All coordinates in the table are exactly the displayed
five-decimal rationals (denominator 100000):

| Center | Intended membership | x | y | Intended radial class |
| --- | --- | ---: | ---: | --- |
| R1 | R triple | 1.11097 | -0.87476 | outer |
| R2 | R triple | 1.32379 | 0.49704 | outer |
| R3 | R triple | 0.50311 | -0.07805 | inner |
| U1 | nearer U pair | 0.39160 | 0.91784 | inner |
| U2 | nearer U pair | -0.60297 | 0.79511 | inner |
| D1 | farther D pair | -0.73315 | -1.20911 | outer |
| D2 | farther D pair | 0.25226 | -1.39134 | outer |
| C | unique designated central center | -0.49900 | -0.20700 | inner |

Notice the **actual rational offsets** satisfy
\(h_R>0\) and \(7/24<h_U<(\sqrt3-1)/2\),
as required for the surviving S2/k4 geometry.
The table is a **relaxed center assignment**; its
membership column refers only to the *necessary*
normal-projection inequalities, not an actual claim that
a unit square of a feasible orientation fits each cap.

## Exact verification of the relaxation

Treat the decimals as fractions of denominator \(10^5\);
no floating-point inference is needed.

For **all 28 distinct center pairs**,
\[
|p_i-p_j|^2\ge1+
\frac{21156861}{5000000000}>1.
\]
Thus the open radius-\(1/2\) disks about all
eight centers are pairwise disjoint.

The intended four outer-center labels R1,R2,D1,D2
have squared center norms \(>1\); the three other
exterior labels R3,U1,U2 and central C have
squared center norms \(<1\).
The largest inner squared norm is strictly below
\(1\), with margin \(>4/1000\).

The necessary cap center-coordinate inequalities have
positive margin at least \(211/100000=0.00211\):
\[
\begin{array}{ll}
p_{Ri}.x\ge h_R+1/2 &(i=1,2,3),\\
p_{Uj}.y\ge h_U+1/2 &(j=1,2),\\
p_{Dj}.y\le -(h_D+1/2)&(j=1,2).
\end{array}
\]

For the **radial necessary square-containment envelope**,
put \(v_i=|p_i|^2\) and \(T_i=q_{\rm plus}-1/2-v_i\).
The condition \(v_i+\sqrt{v_i}+1/2\le q_{\rm plus}\)
is equivalent to \(T_i\ge0\) and \(T_i^2\ge v_i\).
Direct rational comparisons give, for all eight
centers,
\[
T_i>0,\qquad T_i^2-v_i>0.
\]
A short exact-fraction verifier in
[verify_s2_k4_center_relaxation.py](verify_s2_k4_center_relaxation.py)
checks every 28-pair inequality, radial class, cap projection,
and squared envelope condition from the printed coordinates.

## Meaning and limitations

This establishes **only** that these weaker necessary
inequalities do not rule out S2/k=4's
two-inner-near-cap/two-outer-triple pattern.

It does not assign orthonormal square frames. In particular,
the scalar inequality \(r^2+r+1/2\le q\) is only
a **necessary bound** from the true farthest-vertex formula;
achieving it may require frames incompatible with cap
memberships or inter-square separation. No actual packing
at the claimed radius is exhibited.

The sharp unrestricted \(R_8\ge\widehat R\) theorem
and S2/k4 remain OPEN. The point of this exact
counterexample is to prevent an invalid promotion of
center-disk feasibility to square-packing feasibility.


## Important audit: the witness fails an already proved outer-angle theorem

The center-only list (1)--(5) above **does not include**
the stronger, already hand-proved two-outer-center angular
separation \(>\pi/4-1/500\) at the n=8 disk ceiling.
Consequently this exact center witness **does not** satisfy
all previously known necessary packing constraints.
It cannot serve as evidence that the full S2/k4 near-inner
configuration is geometrically realizable.

Indeed take the printed rational center vectors
\(R1=(1.11097,-0.87476)\),
\(D2=(0.25226,-1.39134)\), both marked outer.
They have strictly positive dot product and exact
smaller-angle tangent
\[
\tan\angle(R1,D2)
=\frac{|\det(R1,D2)|}{R1\cdot D2}
=\frac{6625350211}{7486709353}<\frac9{10}.
\]
The outer pair \(D1,D2\) independently has
\[
\tan\angle(D1,D2)
=\frac{3312677524}{3743346721}<\frac9{10}.
\]
But \(\tan(1/500)<1/250\) gives
\[
\tan(\pi/4-1/500)
=\frac{1-\tan(1/500)}{1+\tan(1/500)}
>\frac{249}{251}>\frac9{10}.
\]
Since all compared acute angles lie in \((0,\pi/2)\),
**both** rational pairs have angular separation
strictly **less** than \(\pi/4-1/500\).
Thus the witness violates
HUMAN_STABLE_OUTER_ANGLE.md (which legitimately
uses full square geometry in proving its center-angle
inequality). This is a **failure of the witness under
stronger necessary conditions**, not a counterexample
to the valid outer-angle theorem.

The logical conclusion is deliberately limited:
the original *five weak center-only tests* are
insufficient to reject this S2/k4 pattern. It remains
possible that **stronger analytically derived
center-ray inequalities alone**, together with
the cap projections, could exclude this branch.
We do **not** assert here that introducing new
square-frame variables is logically necessary.

The new explicit all-frame S2 restrictions in
HUMAN_S2_K4_NEAR_INNER_FIVE_HUNDREDTHS.md and
HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md remain
independent and fully compatible with this correction.
