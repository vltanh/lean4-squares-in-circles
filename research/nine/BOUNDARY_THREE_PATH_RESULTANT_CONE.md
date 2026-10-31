# The middle load of a three-body boundary path lies in the endpoint force cone

**Status: complete uniform hand implication and whole-mask applications;
root and separate independent full hand audits passed, including both
complete attachment applications.**
Work in the common radius window

    79/40 <= R <= sqrt(1105)/16.

Let A,K,B be three distinct interior-disjoint contained unit squares,
all physically circle-touching, with actual physical contacts AK and
KB. Assign nonnegative original circle-corner weights of positive
total to each body, and write F_A,F_K,F_B for the resulting forces.
The bodies may have arbitrary additional positive neighbors and loads.
No force or torque equation at any of these three bodies is assumed.

## 1. The complete angular cone

CIRCLE_CONTACT_ANGULAR_ORDER.md proves that a touching boundary pair
has consecutive center directions in the full physical circle order,
with center-angle gap less than 2*pi/5. CENTERED_INNER_ARC.md gives
a center-angle gap strictly greater than 2*pi/9 for any two boundary
bodies. Thus K's two distinct boundary neighbors occur on opposite
sides of K in that order. After reflection, choose angle lifts

    alpha_A < alpha_K < alpha_B,

with each of the two successive gaps in (2*pi/9,2*pi/5). In particular

    alpha_B-alpha_A < 4*pi/5.                       (1)

The local all-mask theorem in Section1 of
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md puts each body's actual
nonzero circle resultant within pi/12 of its center direction. It
needs no four-body path or force-sum premise. Both physical circle
corners and zero individual weights are included. Write the compatible
force-direction lifts beta_A,beta_K,beta_B. Then

    beta_K-beta_A > 2*pi/9 - pi/6 = pi/18 > 0,
    beta_B-beta_K > pi/18 > 0,

and

    beta_B-beta_A < 4*pi/5 + pi/6 = 29*pi/30 < pi.    (2)

Consequently the actual nonzero middle force belongs to the open
positive cone of the two actual endpoint forces. Explicitly there
are lambda,mu>0 such that

    F_K = lambda F_A + mu F_B.                      (3)

For completeness, choose the oriented frame in which F_A has angle
zero and F_B angle theta in (0,pi). If F_K has intermediate angle
phi in (0,theta), the two coefficients are

    lambda = |F_K| sin(theta-phi) / (|F_A| sin(theta)),
    mu     = |F_K| sin(phi)       / (|F_B| sin(theta)).

Every denominator and numerator is strictly positive by (2). These
are the original resultant vectors, including the real unequal
two-corner weights. No load has been rotated or split.

## 2. Negative total projection occurs at an endpoint

For any fixed vector c, equation (3) gives

    c . (F_A+F_K+F_B)
      = (1+lambda)c.F_A + (1+mu)c.F_B.               (4)

Therefore a strictly negative projection of the three-body total
requires c.F_A<0 or c.F_B<0. If both endpoint projections are
nonnegative, the total is nonnegative. If both are positive, every
one of the three projections is positive.

This is a complete geometric consequence for a physical boundary
path, independent of the positive degrees at its middle body. In
particular K is not being treated as a degree-two tip.

## 3. The triangle attached at a diamond hub has a negative unique tip

Use the exact C2.34.b0 diamond-hub layout from
TRIANGLE_FOUR_BODY_BLOCK_LOAD_COVER.md. Its edges are

    HK, HA, HB, KA, KB, HX, XY, YH.

H is physically clear with positive degree five. K has degree three;
A,B,X,Y have degree two and are loaded. The positive block-load set
is exactly KAB, and A--K--B is an actual physical boundary path.

The intact end triangle H--X--Y--H has

    c_H . (F_X+F_Y) > 0.

Summing every genuine force equation in the component gives

    F_A+F_K+F_B = -(F_X+F_Y).

Thus (4), with c=c_H, implies that at least one of the actual
degree-two endpoint tips A,B has negative pressure at c_H.
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md makes every physical two-corner
neighbor of H strictly positive there. The negative endpoint therefore
has one physical circle corner z with c_H.z<0.

Exchange A,B if necessary and call that endpoint A. The complete
remaining necessary domain has:

* A is physically unique, with its actual corner satisfying c_H.z_A<0;
* B has either one or two physical circle corners;
* K has either one or two physical circle corners, with every true
  degree-three force and torque equation retained.

This is the four whole physical-mask family cover, in the order K,A,B,

    (S,U,S), (U,U,S), (S,U,U), (U,U,U),              (5)

where U means one physical circle corner and S means two. Every
individual corner weight and every actual shared mean remains.

In particular the entire former (U,S,S) family is excluded, alongside
the previously excluded (S,S,S) family: two radial endpoint tips cannot
supply the required negative total projection, regardless of K's
physical mask or three incident positive forces.

The labeling in (5) is legitimate. With one unique endpoint, that
endpoint must be the negative one. With two unique endpoints, the
root-preserving A/B reflection permits choosing a negative endpoint
as A. If both are negative either choice is allowed. No symmetry
exchanges K with a degree-two endpoint.

This closes a whole physical-mask family, not the entire diamond-hub
attachment. All four residual domains, every original root force and
all three arbitrary extra squares remain. No new normal selection,
motion, sampled-angle premise, Lean compilation or CI is used.


## 4. The all-three-loaded C4 attachment also has a negative unique endpoint

Use the exact four-cycle H--A--B--C--H with attached triangle
H--X--Y--H, and the full block-load set ABC. H has true positive
degree four; A,B,C,X,Y each have true degree two and positive load.
A--B--C is an actual physical boundary path. Applying Sections1--2
with B as the middle vertex gives

    F_B = lambda F_A + mu F_C,   lambda,mu>0.

The intact end-triangle pressure and the complete force sum give

    c_H . (F_A+F_B+F_C) = -c_H . (F_X+F_Y) < 0.

Therefore c_H.F_A<0 or c_H.F_C<0. Both endpoints physically touch H,
so the radial-neighbor theorem makes a negative endpoint physically
unique. The exact root reflection exchanges A,C and fixes B. Label
a negative endpoint A. Its unique corner obeys c_H.z_A<0, while
B and C each retain either physical circle mask.

The complete remaining necessary mask representatives, in the order
(B,A,C), are again

    (S,U,S), (U,U,S), (S,U,U), (U,U,U).

If both endpoints are unique, choosing a negative one as A uses only
the stated root reflection; if only one is unique, it must supply the
negative pressure. Every original circle weight, physical extra contact,
H force and application mean remains. In particular the whole family
with both endpoints A,C physically radial is excluded for either
physical B mask. No claim is made about closing any of the four
remaining entire mask families, the ABC orbit or C2.34.b0.

The geometric bounds of NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md
apply to this actual H/A intersection. They retain the original circle
origin; their stronger R²>=17/4 conclusion is used only in that full
high-radius domain. All three arbitrary extra squares remain.
