# Independent full review of the zero-individual-weight radial C6 boundary

Date: October 26, 2026.

**Verdict: PASS.** The source
SIX_CYCLE_ONE_RADIAL_ZERO_CORNER_WEIGHT_EXCLUSION.md excludes both
original zero-weight endpoints of the physical one-radial,
all-side-transmitter alternating C6. It preserves the two physical
circle corners of the radial square and proves the scalar extension
needed at its weak corner equality.

This review checks the full source, its local radial prerequisites,
the actual contact-type cover, every row of the scalar dependency
table, and the final supported-corner angle contradiction. No
limiting packing, change of corner weights, numerical sample, new
finite coefficient calculation, Lean build, or CI result is used.
The remaining radial domain with two positive individual weights
is not excluded by this review.

## 1. Actual radial support, torque, and supported corner

The complete support cover in
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md, Section 1, excludes
outer supports, the inner radial axis, and both tangential axes
using the original next-loaded application and physical containment.
Those arguments are independent of the individual radial corner
weights. The distinct-port torque calculation in
SIX_CYCLE_ZERO_DIAGONAL_TWO_RADIAL_EXCLUSION.md, Section 1,
also applies locally to a single radial unit: using the same inner
vertex twice gives two pair torques of the same strict sign.

Consequently the source correctly retains the two distinct strict
inner vertices
\[
 P_+=(d,1/2),\quad P_-=(d,-1/2),
\]
with normals
\[
 g_+=(-\cos\alpha,\sin\alpha),\quad
 g_-=(-\cos\beta,-\sin\beta),\qquad
                       0<\alpha,\beta<\pi/2.
\]
Neither interface at the radial unit is genuinely shared, since
its normal is strictly inside its vertex cone and is not a side
normal of that square. The actual two-port chord is one.

Reflecting the whole original packing to put its already supported
corner at \((d+1,1/2)\) preserves both physical circle corners and
both original weights. With \(a=\tan\alpha\), \(b=\tan\beta\),
the intersection of the two actual normal lines is
\[
 q_S=\left(d+\frac1{a+b},\frac{b-a}{2(a+b)}\right).
\]
The original force and torque equations, with the other original
corner weight zero, put this concurrence on the positive ray through
the supported corner. Equating the two coordinate ratios gives
exactly
\[
                       b-(2d+1)a=1.
\]
It follows that \(b>1\), \(a+b=1+2(d+1)a>1\), and the stated
strict interior coordinates of \(q_S\) follow. This special
interior-concurrence conclusion is proved from the zero weight;
it is not imported from an invalid general radial premise.

## 2. Short-port bound and the complete strict-turn reduction

The full local unique-corner turn proof in
SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md, Section 1, does not
use a diagonal transmitter in its local calculation. Its actual
premises hold separately at the two unique loads here. It gives
\(\theta_B,\theta_C\le3\pi/4\), so the original turn sum gives
\(\theta_S\ge\pi/2\), equivalently
\(\alpha+\beta\le\pi/2\). Hence \(ab\le1\).

Using \(d>9/10\), the supported-corner identity gives
\[
 1\ge ab=a+(2d+1)a^2>a+\frac{14}{5}a^2.
\]
If \(\alpha\ge12/25\), then \(a=\tan\alpha\ge\alpha\)
and the right side is at least \(3516/3125>1\). I checked
that exact fraction independently. Thus the actual port adjacent
to the original supported corner has
\(\alpha<12/25\).

Since \(b>1\), one has \(\beta>\pi/4\) and therefore
\(\theta_S<3\pi/4\). The turn sum then makes both other
turns strictly greater than \(\pi/2\). If
\(\theta_S=\pi/2\), Sections 1--4 of the accepted
SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md give
\(\alpha=\beta=\pi/4\), independently of its two weights.
The supported-corner identity would become \(-2d=1\),
which is impossible. This uses the actual endpoint classification,
not a completion estimate or an unproved limiting case.

All three turns therefore lie in
\((\pi/2,3\pi/4]\). The local unique-corner owner/vertex cover,
together with the actual-transmitter overlap argument, now puts
the two unique loads' distinct original applications on one inner
side, with at most one genuine share each. The radial unit's
corresponding facts were already derived directly. No all-unique
global turn theorem is applied to the radial unit.

## 3. Selected-corner norm model and the weak physical equality

At the radial unit the selected point is exactly its original
positive-weight corner. Thus the original circle resultant is a
positive multiple of that point and the identity
\[
                         z_i=RF_i/|F_i|
\]
holds for each of the three actual selected corners. The other
physical radial corner remains in the actual square.

The shared-mean chart at the two unique loads is unchanged. At the
radial unit the original endpoints are vertices, so its chord is
one. I checked that the torque identity about each actual selected
corner gives the same \(g_i=K_i+JF_i\), and that the support
identity gives \(u_i\cdot g_i>0\). The supported radial corner
maximizes \(F_i\) on its actual square; uniqueness as a physical
circle corner is unnecessary for that assertion. Its own
coordinates in the two support directions are positive even where
one equals \(1/2\).

Consequently the norm directions, the original channel closure,
and the exact virial identity used in the scalar sources all hold
without change. The identity would generally fail if both radial
corner weights were positive; the present proof explicitly uses
the given zero coefficient at this step.

Containment supplies weak inequalities
\[
 z_i\cdot v_i\ge1/2,\qquad
 (2\chi_i-1)z_i\cdot u_i\ge1/2
\]
at the radial unit. The source does not silently strengthen either.
Instead, for a nonshared bit-one unit,
\[
 ED\le2Ra(a-bc),\qquad E^2-D^2=a^2+2ab\sin\theta>0.
\]
The strict second inequality yields \(ED>D^2\), so with
\(x=b/a>0\), \(k=-c\ge0\),
\[
 x^2<(2R-2)kx+2R-1.
\]
The bit-zero version interchanges \(a,b\). With the actual radius
and turn bounds, this gives
\[
 x^2-\frac{6831}{4480}x-\frac{101}{32}<0.
\]
I independently checked its value \(151/8960>0\) at \(x=27/10\)
and its strictly positive derivative on \(x\ge27/10\).
Therefore the required force-ratio bound \(x<27/10\) remains
strict under the weak physical corner inequalities.

This is the only additional nonshared corner input used in the
imported scalar contradictions. Every genuinely shared loaded
unit remains one of the original physically unique units.

## 4. Complete share count and doubly shared channel

The radial unit has no share and each unique unit has at most one.
Thus the counts zero, one, and two are exhaustive. If a transmitter
is shared at both ends, those two endpoints must be the two unique
loads.

I checked the claimed use of Sections 1--2 of
SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md directly. The
two unique shared endpoints give the actual horizontal equation
\(a+c=3\), their other actual normal angles in
\([\pi/4,\pi/2)\), and their sum equal to the third force turn,
which is in \((\pi/2,3\pi/4]\). The two original support
inequalities at the third square give
\[
 0<\Delta_x=1-\cos\eta_B-\cos\eta_C<1-1/\sqrt2,
 \qquad |\phi|\le\pi/4.
\]
The sum-to-product proof of the strict upper bound includes all
permitted \(\pi/4\) endpoints. It uses no circle-coordinate
inequality at the third load. Thus its actual port chord is
less than \(\sqrt2-1<1\), directly contradicting the radial
unit's actual chord one. No all-unique double-shared theorem
or later scalar coefficient packet is being applied at the radial
unit.

After this exclusion, two shares form a matching. The bit
transformation under reflection and cyclic reversal depends only
on the actual directed-side chart. It carries the original
supported corner and its weight along; it does not select the
other physical corner. The zero-, one-, and two-share covers in
the source are therefore exhaustive for this mask boundary.

## 5. Audit of every scalar dependency

The following table records the inputs actually used after the
physical chart and strict-turn facts above have been established.

| Scalar row | Additional input beyond the exact norm, mean, closure, and virial model | Audit conclusion |
| --- | --- | --- |
| Zero shares, mixed bits | None | The strict vertical projection is purely angular and retains positive forces at its equality endpoint. |
| Zero shares, constant bits | None | Closure makes zero a minimizer of the convex six-point functional; the force points form a nondegenerate counterclockwise triangle. The cited triangle-square-corner Fermat inequality is independent of physical circle masks. |
| Constant one share | \(p<27/10\) at nonshared unit 1 | Supplied by the weak-mask proof above if that unit is radial. It suffices for the strict direction lower bound and the same single angle triangle. The six existing rational matrices are unchanged. |
| Mixed one share at unit 1 | None | The complete vertical projection uses the strict turns and actual shortened chord only. |
| Mixed one share at unit 2 | None | The complete diagonal projection uses the strict turn at unit 1 and the actual incoming-share chord only. |
| Constant two shares | None | Its angular projection and full force-gap estimate use the norm, closure, mean, and virial formulas only. The six existing rational matrices are unchanged. |
| Mixed two shares at units 0 and 1 | None | The force lower bound \(p>1+1/\sqrt2\), angular restrictions, Cauchy elimination, monotonicities, and endpoint join all follow from those scalar inputs. No nonshared strict corner inequality or upper force bound is needed. |
| Mixed two shares at units 0 and 2, \(q\ge p\) | None | The whole small-force branch uses closure and its complete scalar radius gap; no physical corner bound is used after the model is established. |
| Mixed two shares at units 0 and 2, \(q<p\) | \(p<27/10\) at nonshared unit 1 | Supplied by the weak-mask proof. All remaining steps of the complete force-gap contradiction are unchanged. |

I checked these dependency statements against the actual saved
sources, including the constant-one-share direction estimate, the
mixed-01 closure and completed join, both mixed-02 force branches,
and both mixed one-share projection proofs. The scalar signs in
these sources already have independent complete reviews; this audit
checks their unchanged inputs and valid extension to the present
mask, rather than asserting physical uniqueness at the radial unit.

The constant zero-share force triangle has the correct orientation:
its successive direction gaps are the strict force turns, all less
than \(\pi\), and sum to \(2\pi\); with positive magnitudes the
origin is inside the triangle. The derived corners are exactly
the constant-bit formulas. The convex minimization and radius
identity thus provide all premises of the Fermat bound.

The two force orderings in mixed-02 are exhaustive, with equality
assigned to \(q\ge p\). Every shared-mean endpoint remains in
each scalar source; any excluded endpoint has its stated exact
closure contradiction. No bound involving the strict shared-corner
ratio \(\sqrt{1041}/8\) is required at the radial unit.

## 6. The sole residue has the required actual adjacent-corner channel

The only remaining contact word and share placement are
\(\chi=(1,1,0)\), with sole outgoing share at unit 0. The
radial unit cannot be unit 0, so it is unit 1 or unit 2. Both
are nonshared and retain their actual full side chords.

In either placement the original channel between units 1 and 2
has the exact endpoint relations
\[
                         z_1=p_1^++v_1,\qquad
                         z_2=p_2^-+v_2.
\]
Thus at the radial endpoint this channel uses the actual inner
vertex adjacent to its original supported corner. At its other
endpoint it uses an actual vertex at distance one from that
unique unit's actual circle corner. These facts hold for either
incoming or outgoing placement of the radial unit; reversing
which endpoint is being viewed does not change the channel or
its original application.

The short-port lemma therefore gives \(\alpha<12/25\) for
this channel after the allowed global reflection. The local
theorem in SIX_CYCLE_RADIAL_INCIDENT_NEAR_CORNER_ANGLE_BOUND.md
uses precisely its actual equation
\[
 Q=(d-\cos\alpha,1/2+\sin\alpha),\qquad |z-Q|\le1,\quad |z|=R,
\]
and gives \(\alpha>12/25\). I checked the complete radius
monotonicity, the \(d(79/40)>91/100\) reserve \(101/40000\),
and the final negative quadratic reserve \(-21/62500\).
That proof has no concurrence-containment or positive-every-corner
premise. It applies here without changing any corner, mean, or
physical square.

This contradiction excludes both possible radial placements in
the sole residue. Together with the complete scalar cover, it
closes the entire original zero-individual-weight boundary.

## 7. Accepted conclusion and limits

Both original zero-weight choices at the radial square are
impossible in the full original radius interval. Every actual
one-radial all-side C6 still under consideration must therefore
have both individual circle weights strictly positive. The
physical two-corner mask has been retained throughout; this is
not a uniqueness-from-weight argument.

All nine squares, original positive pair forces, actual
transmitter sliders, genuine shared means and their endpoints,
physical boundary masks and completion squares remain. The proof
is a core contradiction and imposes no completion placement.
It adds no new computational certificate and does not close the
remaining two-positive-weight radial domain, the whole C6 gate,
the global sharp inequality, or its equality classification.
