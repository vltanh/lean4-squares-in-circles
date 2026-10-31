# Independent review: the mixed physical mask with both parallel roots owning AB

Date: October 27, 2026.

Reviewer: hexagon, independently of the proof author rooted_blocks.

**Verdict: ACCEPTED in full at the exact stated original-domain scope.**
No mathematical correction or missing endpoint was found. This is a full
source and prerequisite review, not a check of only the last calculation.

## Sources read and fixed pins

The complete source reviewed is
ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_EXCLUSION.md,
SHA-256
`a57c2f2892d46db72877f66632fdefba094180f26b6e89b07797de0545391523`.

I also read the complete direct owner reduction
RADIAL_BOUNDARY_UNIT_ADJACENT_GENUINE_ROOT_OWNER_REDUCTION.md,
SHA-256
`6001d1f35e59ddd786747d674e0c9a90e47b41809a370bb9f84a0bde3327adae`.
Its actual radial-square contact cover, true B3 moment equations, fixed
singleton determinant selection and original-mean scope were checked.
The sharp minimum-support equality and the genuine boundary-neighbor D2
concurrence are used only in their already reviewed original forms. In
particular the assertion that the radial concurrence lies in D is invoked
only after imposing D's one-physical-circle-corner mask.

## 1. Original component and exact owner-reduction scope

The source keeps AB, BC, CD, DA, AL and BM, with the true degrees
A3, B3, C2, D2, L1 and M1. All three other physical units remain in the
containing circle. C has two physical circle corners, with either one of
their individual weights permitted to be zero, while D has one physical
circle corner and positive total circle load. Both roots own the original
AB axis; there is no replacement by a three-force equation at a body of
larger degree.

The direct reduction genuinely supplies the B-owned South contact at its
actual C corner. At a tilted B, its vertex norms omit the required annulus,
so this is a side-interior support. The aligned-leaf B alternative gives
a strict, rather than B-owned, BA normal and is therefore excluded by the
present premise. The remaining actual B means are exactly

    P_BC=(t,V-1), delta<t<U,
    P_AB=(delta,V*t/U),
    |F_BA|:|F_BC|=U:V.

I checked the complete C contact cover, including every C-owned North
mean Q_C+z*e, 0<=z<=1. The fixed-point preselection in the prerequisite
does not freeze that mean. Its free-AB determinant uses an actual fixed
B vertex and the actual fixed BC point; its noncollinearity and absence
of a coupled four-junction parameter are established before extraction.
No new free normal is selected in the proof under review.

The reflected mixed physical mask is obtained by interchanging the two
root/boundary pairs. It is not an assumption that both boundary squares
are radial, nor that D is parallel to either root.

## 2. All genuine A-leaf features

The five listed alternatives are exhaustive because A's vertical interval
contains the strictly positive original AB mean. The omitted South and
lower-right alternatives put its upper edge below zero; an East radial
support would require delta=d. Zero-coordinate limits belong to the
corresponding owned-axis cases.

For a lower-left leaf, the full A3 vertical force puts AD on A's actual
upper support. Its gap from the real CD point exceeds 49/30, using
w+V<11/30. This is a diameter contradiction for the actual D square,
independent of D's orientation or normal ownership.

For North and upper-right leaves, I re-derived (7) and (8) from the full
A3 torque. The horizontal leaf component is nonnegative and the vertical
component has the displayed strict bound. The actual C circle corner's
dot product with the two leaf forces exceeds 311/1800 after division by
the positive original scale. The acute physical C-D theorem applies to
every actual circle corner, so its use remains valid when one C weight
is zero. The contradiction uses the unchanged full component force sum.

For an owned West leaf, West AD would duplicate the genuine L by the
sharp minimum-support equality. East AD keeps its entire original mean
range. The actual C corner lies strictly to the left of D's support half
plane, leaving only C-owned North. The two genuine D2 rays then have
incompatible heights, respectively at least -1 and strictly below -1.
No D alignment or endpoint replacement is used.

## 3. Complete remaining A3 force and lower contact cover

For the surviving upper-left leaf, the full A3 equation gives exactly

    F_AD/alpha=(p0*a-U,-p0*k).

Its negative vertical component leaves Southwest, Southeast, or the
actual South-side mean. I re-derived both moment identities in (12),
the South mean in (17), and the strict bounds on k,V,s and c.

The Southwest proof uses a real inward unit segment at the actual minimum
support point of D. This segment exists at a side or at a vertex and
does not assume that the AD normal is D-owned. The scalar S is increasing
on its asserted interval. The split at 43/240 and 1/4 covers the entire
range; the exact 1/28800 reserve, the bound t/U<4/5, and both radical
comparisons give the strict circle violation claimed.

In Southeast, the actual point's C-tangent coordinate is below 1/2,
which excludes the C-owned North half plane. At C's remaining corner,
the original two proper rays have incompatible horizontal coordinates.
Their weak proper-distance endpoints do not remove the strict gap.

For South, X=a is correctly retained as an actual side endpoint. The
bound s<1/3 follows from the original AB mean rather than a newly chosen
point. I checked the exact reserve
1568401/2170087200 and the physical point-distance bound

    |Q_C-P_AD|^2<1924/2025<1.

## 4. Both complete D frame alternatives

If D owns the South axis, its actual vertical interval is [k-2,k-1].
The positive radial concurrence and one-physical-corner premise force
the lower-left circle corner. The positive horizontal CD normal has
three exhaustive vertical-sign alternatives. Positive or negative sign
gives the stated actual-height contradiction, so the East mean is the
only survivor. The bound T>A0-B0*V is strict and positive throughout.

I independently expanded the completed-square identity (22), including
its constant, using exact rational arithmetic:

    constant = 53631019/784569600 > 0.

Since the added quadratic constraint on its left side is negative,
the identity has the asserted direction and excludes the entire
parallel-D interval, including every contact-mean endpoint.

Otherwise the actual South port is D's strict uppermost vertex, with
the displayed two inward orthogonal axes. Its positive projection on
j_D leaves exactly two possible physical farthest corners. The proper
radial point lies on the actual vertical line through P and in D; this
first excludes p>q for an opposite circle corner and then gives
X*N>=w*M. The resulting lower bound

    |Z|>=sqrt(2)+w>R

includes p=q and zero proper distance. The unique-circle mask makes
P dot f<-1/2 strict after that exclusion. Thus Section 8 is also a valid
local opposite-circle exclusion at precisely its stated negative-height
vertical-port scope; it does not extend the radial-interior conclusion
to a two-physical-corner mask.

## 5. Full D2 force, owned C mean and final radius comparison

The full D2 equation has negative f component at the surviving actual
circle corner. Its incoming South force has positive f component, so
the original outgoing g has positive f component. Every actual CD mean
therefore lies on D's far-f side, including its endpoints. Its distance
from P is at least one, which eliminates C's strict corner by the
previous strict distance bound.

In the remaining C-owned North case, the signs of g on both actual D
axes fix the real CD point to P+f. I re-derived the proper-ray identity
(27) without altering either application. The exact bound

    w-(s/c)X > 311/840

makes A_r positive; B_t is positive from the physical frame. The two
components have squared norm two. Keeping the original z>=0 gives the
strict final inequality (29). Its last rational comparison is exactly

    1+7/5-2*(61/60)=11/30.

Both the C side endpoints z=0,1 and all original D proper-distance
endpoints are included. No part of this calculation changes C's two
physical corner mask or assigns its individual circle weights a positive
lower bound.

## 6. Accepted exact join and limitations

Sections 2 through 10 exhaust the A genuine-leaf features, its actual
AD supports, both D orientations at the surviving South mean, both
possible unique D circle corners, and every actual C support feature.
The proof therefore closes the **entire mixed physical mask with both
roots owning AB**, in either labeling, at the original LCD.SS component
and same-nine completion scope.

The exactly-one-owner mixed mask and the unique/unique physical mask
remain outside this source. The proof does not assert that a smaller
balanced core is impossible after removing any original force. No
compilation, CI, numerical pose, remote write or shared-metadata edit
was used in this review. Exact arithmetic above verifies transparent
identities already displayed in the human proof; it is not a numerical
certificate.
