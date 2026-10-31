# Root review: one common comparison point and the complete mixed-share radius bound

Date: October 26, 2026.

**Result: PASS for the complete geometric common-point theorem and its
unchanged physical implication R<2.** I independently read both
TRIANGLE_MIXED_COLLAPSED_SHARE_FERMAT_BOUND.md and
TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md in full, reconstructed
their continuous inequalities and every displayed fixed arithmetic
witness, and checked the original support-functional identities.
The three-extra completion problem remains open.

## 1. The endpoint theorem covers every original Fermat case

For D(a,b)^2=a^2+ab+b^2 and
E(a,b)^2=2a^2+(1+sqrt(3))ab+b^2, I recovered the Hessian of
G=2D-E. Its scalar coefficient is

    (3/2)/D^3 - (1-sqrt(3)/2)/E^3 > 0.

Homogeneity gives the rank-one positive semidefinite matrix in the
source. Convexity therefore holds jointly in both positive arguments
and extends continuously to the closed quadrant. The argument order
E(c,b) in the mixed endpoint is retained correctly.

At an interior Fermat point the actual three rays have 120-degree
separation. I reconstructed all five derived norms and the fixed
sqrt(2) edge term. Convex symmetrization in a,c and
D(a,c)>=sqrt(3)(a+c)/2 reduce the gap to m*f(b/m), with
m=(a+c)/2. The scalar f is strictly convex on the whole nonnegative
half-line. Its two derivative signs bracket the minimum between
9/20 and 23/50, while its tangent at 9/20 gives the uniform strict
reserve 19/20000.

I independently rebuilt every positive squared reserve in the
endpoint's radical bounds using exact rational arithmetic, then
substituted the bounds in the original value and derivative formulas.
They give exactly 137/100000 for the value lower estimate and the
three signed derivative fractions displayed in the source. The
directions are correct for both denominators and subtracted positive
numerators. This verifies fixed arithmetic identities and inequalities;
the full half-line sign comes from strict convexity, not interpolation
of numerical samples.

When a Fermat point is a vertex, the subgradient criterion gives
an angle at least 120 degrees, including equality. I checked all
three cases directly. At f1, the opposite side length is at least
sqrt(3)(a+c)/2, exceeding (a+c)/sqrt(2). At f0 and f2, the triangle
inequality and d>=b/2+c (with the reflected roles at f2) give the
strict gap (3-2sqrt(2)) times the other nonzero ray. Thus the
collapsed endpoint theorem has no omitted vertex or limiting angle.

## 2. The uncollapsed Fermat gap is globally convex

In the common-point source the c=1 normalization only scales the
auxiliary triangle inequality by a positive original ray length.
Its derived norms give exactly

    G0(a,b)=G(a,b)+G(1,b)+G(1,a)-(a+b+1).

This is globally convex throughout the positive quadrant. The
single rectangle Q=[2/5,7/10] x [1/5,1/2] is used to enclose
a convex sublevel set; no original physical force ratio is assumed
to lie there.

I independently checked every uniform coefficient in its Hessian
bound. For G(1,t), E^2>(8/5)D^2 and (8/5)^3>4 give
E^3>2D^3. The two respective t ranges then give the diagonal
bounds 13/30 and 3/5. For G(a,b), D^2<=109/100 and D<11/10
give the rank-one coefficient greater than 10/9. Completing the
square in each direction yields the two separate bounds

    v^T Hess(G0) v >= (9/20) v_a^2,
    v^T Hess(G0) v >= (7/10) v_b^2.

The Schur-complement reserves are 41/6180 and 1/120. These are
valid for every direction and every point of Q. The proof never
adds those two separate inequalities as though they were one
stronger matrix bound.

## 3. The one fixed witness and the complete exterior domain

The single rational point is (5417/10000,3303/10000). I reconstructed
all seven radical enclosures independently, including their nested
sqrt(3) bounds. Multiplication by 10^14 gives exactly every positive
integer reserve in the displayed table. Independent substitution into
the original value and the two original partial derivatives gives
the source's bounds (17), and therefore

    -447/100000 < G0 < 0,  |G0_a|,|G0_b| < 1/10000.

The full L1 displacement in Q is at most 41/125. The global tangent
therefore bounds G0 below by more than -1/200 everywhere in Q.
For its boundary, integration of the appropriate directional Hessian
bound gives the smaller quadratic contribution
(9/40)(1417/10000)^2. The exact comparison of vertical and horizontal
face contributions has reserve 5698325 in the stated integer scaling.
Combining all terms gives exactly 59801/4000000000>0 on the entire
boundary.

Since G0 is globally convex and negative at the fixed interior point,
any point outside Q with G0<=0 would force a negative value at the
intervening boundary point. This contradicts the uniform boundary
bound. The complete positive quadrant is therefore covered: every
failure of the original Fermat point lies in Q's interior, and the
gap there is greater than -1/200. The one fixed witness is explicit
arithmetic; no grid, angle subdivision or unproved root isolation
supplies the global conclusion.

## 4. The second endpoint has enough reserve on the same enclosure

The source retains the exact D(a,1)-sqrt(3)(a+1)/2 remainder from
the endpoint symmetrization. Its rationalized numerator is
(1-a)^2, and the full Q bounds give the strict lower value 9/1195.
Combining that with m>=7/10, f>19/20000 and
2-sqrt(2)>7/12 yields

    G1 > 133/200000 + 21/4780 > 1/200.

The exact final reserve is 2787/47800000. This holds on all of Q,
without a restriction on b/m and without changing the original
endpoint functional.

## 5. Both endpoints are controlled at one actual comparison point

I reconstructed the three derived vectors in the oriented Fermat
frame and their dot products with v=e2-e0. They give the stated
functions Z(z), V(a). Direct differentiation gives
Z'=(3/2-sqrt(3))*zb/E^3<0, with its complete range between
(3+sqrt(3))/(2sqrt(2)) and sqrt(3). Its range width is below
3/50 by the exact reserve 1/14850. The separate V derivative is
positive; the lower endpoint comparison gives V>98/181>27/50.
Consequently the original Phi0 derivative is below -12/25 and
the Psi derivative below 3/50. The three original radial-unit
derivatives sum to zero at the Fermat point, as required.

I checked each of the six norm second derivatives on the full
segment 0<=tau<=1/50, larger than the used segment 1/55. The
determinant formula, lower norm bounds and nonvanishing conditions
give, respectively, 15/8, 15, 7/8, 1/3, 2/15 and 2 as upper
bounds. In particular the g1 ratio maximum occurs at a=2/5 after
decreasing b to 1/5, and the g0 relative displacement bound uses
its strict norm greater than 7/4. Their sum is 1213/60<21.
Psi omits only one varying norm, so the same bound applies.

Integrating to the one common point o+v/55 decreases Phi0 by
more than 1/200 and increases Psi by less than 1/200. I checked
the two exact reserves 31/121000 and 53/121000. Therefore the
point works for both endpoint functionals on every possible G0<=0
case. If G0>0, the original Fermat point already works for both.
Norm convexity is then applied at this same point for every
delta in [0,1]. Separate endpoint minimizers are never substituted.

## 6. All degenerate cases have an honest common-point join

I separately checked the two endpoint estimates at each vertex
Fermat point. At f0 they coincide. At f2 the uncollapsed endpoint
is strictly smaller than the collapsed endpoint. At f1 the additional
positive-square comparison is exactly

    2[a-(1-1/sqrt(2))c]^2 + (6sqrt(2)-8)c^2 > 0.

This gives the missing uncollapsed bound there. The same arguments
cover all collinear triples of distinct points at their median.
For each of the three coincident pairs, direct evaluation reproduces
the table's larger endpoint value, strictly below 2P. For a constant
triple the source correctly states only the zero equality. That
exception is absent from the physical force triangle.

## 7. Original physical closure and virial imply R<2

I checked the original identities against
SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md, Section 3, and the retained
mixed110 outgoing-share domain. The only relabeling is the exact
parameter delta=1-ell0 of the actual original mean. Its g0 vector
has the coefficient ell0 on f0; g1 and g2 have the stated mixed
corner order. All original norms are nonzero.

The actual channel equations give
sum n_i + ell0*u0 + u1 + u2=0, exactly the negative gradient
of Phi_delta at the original force-plane origin. Convexity makes
that origin a global minimizer. The unchanged physical virial is
R*P=Phi_delta(0). The actual canonical force triangle is strictly
counterclockwise: its signed determinant is a sum of positive terms
in the positive force magnitudes and positive sines/cosines. Thus
P>0 and the common-point theorem applies.

It follows, without a force or angle box premise, that

    R*P = Phi_delta(0) <= Phi_delta(x) < 2P,

hence R<2 for the entire original remaining physical orbit. The
comparison point is in the auxiliary force functional; no square,
circle corner, actual mean, normal, force magnitude or transmitter
slider is moved. All nine original units remain.

This supplies only the radius hypothesis of the conditional cap-0
criterion. Its other coordinate hypotheses and all seven completion
allocations remain unproved by this theorem. No original coarse gate,
global bound, equality classification or Lean integration is closed
by this radius reduction. The proof uses the displayed fixed rational
witness openly, and adds no coefficient-sign packet or angular grid.
