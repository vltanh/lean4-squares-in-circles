# Root review: the exact contact lens, full unloaded stars and the 39/20 endpoint threshold

Date: October 30, 2026 UTC.

**Verdict: PASS for the entire frozen source and all four stated theorems.**

The complete manuscript
`EXACT_CONTACT_LENS_AND_FAR_ENDPOINT_POSITIVE_LOAD_AT_THIRTY_NINE_TWENTIETHS_2026_10_30.md`
was read and reconstructed. Its SHA256 is
`3e9a96293ae14e5ed3e9f2952c396cbef82d44ddd6a9643e54ab597a63e951e3`.
The proof is self-contained; its two historical chord sources are cited
for provenance rather than used to supply an unproved additional premise.

## 1. The entire supporting-face chord and exact contact locus

Write a unit square in its actual orthonormal frame as P0+[0,1]u+[0,1]v.
For a minimizing point p of the unit normal n=au+bv, a positive coefficient
forces the corresponding own coordinate of p to zero, a negative one
forces it to one, and a zero coefficient leaves it unrestricted. Since
|a|,|b|<=1, adding tn for 0<=t<=1 keeps both coordinates in [0,1].

This proves the entire inward unit segment from every supporting point,
including all points and endpoints of a side, every vertex, and every
normal in a vertex cone. Applying it to the two original contacting
squares gives actual occupied points p-n and p+n. Both belong to D_R,
so direct expansion gives

    |p|^2+1+2|p.n|<=R^2,
    (|p.n|+1)^2+(p.Jn)^2<=R^2.

The locus for fixed n is precisely the intersection of two radius-R
disks centered at plus/minus n. It is correctly called a lens. No new
application point or replacement normal has been chosen. The formula
holds for an actual common mean anywhere along a shared side segment.

Dropping the normal term gives |p|<=sqrt(R^2-1). If R<1 the inequalities
already make a pair contact impossible; thus the square root is used
only on its legitimate nonnegative domain. Every physical pair contact
has a common separator by convexity, including zero selected pairs,
so the radius bound applies beyond a chosen stress. At Q its value is
sqrt(849)/16.

The source's two-square family [-1,0]x[r-1,r], [0,1]x[r-1,r] for r>=1/2
attains this closed radius bound at p=(0,r). Its farthest corner norm
is r^2+1, because |r-1|<=r. This is a valid sharpness example for the
force-free pair bound and makes no nine-unit completion claim.

## 2. Actual normal directions near the outer contact radius

For |p|=r>0, dividing the lens inequality gives the asserted bound on
|e.n|. The function (Q-1-r^2)/(2r) decreases strictly, and it is below
one when r>R-1. Its exact values at 7/4 and 9/5 are 65/896 and 163/7680,
respectively, below 1/12 and 1/40. Thus the inequalities control the
original common normal, not a center chord or a guessed contact tangent.
At the maximal contact radius the original normal is perpendicular to p;
a radial normal instead yields the separate bound r<=R-1.

## 3. Whole-side clearance and complete unloaded stars

If an entire closed own side lies outside the universal closed contact
disk, it has no actual contact, including its two vertices. A supporting
normal with positive component on that side's own axis would have its
support face inside that same side, so all actual contact normals have
nonpositive component on the axis.

Projecting the complete zero-circle-load force equation onto that axis
then forces every positive contact normal to be perpendicular to it.
Any strictly inward original normal, or any pair of nonparallel positive
normals, therefore forces positive circle load. This argument includes
the whole original positive star at arbitrary true degree and uses no
moment equation.

The minimum squared radius on an own side is the stated sum of the fixed
own-coordinate square and the squared distance of the other coordinate
interval from zero. Applying the contrapositive to both outward own-axis
signs proves both inequalities (10). In particular |c.u|>=4/3 places
the whole outward side beyond radius 11/6, whose squared reserve above
Q-1 is 103/2304. The resulting parallel-star conclusion is valid.

The source expressly keeps the possibility of several positive neighbors
with parallel normals. It does not turn arbitrary such stars into true
degree-two transmitters or suppress their bodies without justification.

## 4. Continuous endpoint support gap and exact free-side bounds

The farthest-corner estimate again gives |c|<M=91/60, with strict reserve
31/57600 at Q. If two actual support intervals have gap at least 39/20
along the specified direction d, each endpoint has outward signed center
projection greater than

    39/20+1-M=43/30.

Their halfwidth sum is less than 13/12, so either halfwidth is less than
7/12. For a dominant outward own axis with components a>=b>=0, one has
a+b<7/6 and hence

    (a-b)^2>23/36>(19/24)^2,
    23/36-(19/24)^2=7/576.

Every point of the entire outward own side, including both endpoints,
therefore has signed d-projection exceeding

    43/30+19/48=439/240.

The exact squared reserve is

    (439/240)^2-(Q-1)=53/1800>0.

This proves the full side has no physical contacts. It uses only the
specified actual support gap, and does not silently replace that premise
by a center-distance or unlabelled pair-distance condition.

## 5. Positive endpoint loads retain every original force

At the first endpoint, the original inward contact along d has strictly
negative projection on its dominant outward own axis. Every other positive
contact has nonpositive projection because the whole outward side is
contact-free. Thus the complete body-force projection is strictly negative.
Zero total circle load is impossible. The same argument applies to the
opposite endpoint using its original inward contact along -d.

The full positive-load theorem has no torque, planarity or endpoint-degree
condition. It retains original normals, means, weights and zero-weight
physical contacts. A genuine two-internal-body run is a literal caller:
its complete force equations give the same normal through both bodies,
and support telescoping gives actual endpoint set-support gap at least two,
which is greater than 39/20. Its endpoint inward contacts remain positive
terms of the same certificate. Continuous gaps between 39/20 and two are
also covered without inventing a new integer run type.

The previous 29/15 contact-radius source remains true and frozen. The new
source proves a stronger closed bound and a wider continuous endpoint
criterion by a simpler occupied-chord argument. Neither source resolves
all unloaded branching blocks or the sharp completion theorem alone.

## 6. Verification boundary

All displayed rational comparisons and the elementary function monotonicity
were independently recomputed. The complete proofs cover weak support-gap
endpoints, side endpoints, vertex cones, two-circle-corner bodies and
arbitrary full positive degrees. There is no replacement stress, discrete
orientation search, numerical packing certificate, Lean compilation or CI
premise. No original fine/coarse flag or common-selection claim is changed.
