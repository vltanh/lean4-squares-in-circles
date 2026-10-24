# The middle resultant of a three-body boundary path lies between its endpoints

**Status: complete hand implication at the stated full physical scope;
root and separate independent full hand audits passed.** Throughout,
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]
All squares are actual unit squares contained in the disk, with disjoint
open interiors. All physical circle corners are retained, including
corners whose individual multiplier vanishes.

## 1. The whole three-body path cone

Let A, B, C be distinct circle-touching squares with actual contacts AB
and BC. Give the physical circle corners of each body arbitrary
nonnegative weights of strictly positive total, and write
\[
 F_S=\sum_{z\text{ a physical circle corner of }S}\lambda_{S,z}z
 \qquad(S=A,B,C).
 \tag{2}
\]
The harmless common factor2 used in the stress convention is omitted.

**Theorem.** There are strictly positive numbers u,v such that
\[
                         F_B=uF_A+vF_C.
 \tag{3}
\]
No force balance, degree assumption, contact owner, singleton
application or fixed shared-side mean is needed. In particular this
applies to an internal degree-three vertex of a larger positive graph.

The physical angular-neighbor theorem
`CIRCLE_CONTACT_ANGULAR_ORDER.md` puts A,B,C in their actual consecutive
circular order: at B the two different touching boundary neighbors
occupy opposite neighboring positions in that order. Reflecting if
necessary, choose center-angle lifts
\[
                    \alpha_A<\alpha_B<\alpha_C.
 \tag{4}
\]
Each consecutive gap is less than
\[
                         \theta=\arccos\frac9{25}.
 \tag{5}
\]
Indeed every boundary center has norm greater than5/4, and touching
centers have distance at most \(\sqrt2\). The cosine-law calculation
in `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`, Section3, gives (5)
for each actual contact without any equal-radius assumption.

Section1 of that source also proves that every physical circle corner,
and every nonzero nonnegative circle resultant, is at angular distance
strictly less than \(\pi/12\) from its own center. Every resultant in
(2) is nonzero because its physical corners lie in this same cone of
aperture less than \(\pi/6\). The established centered inner-circle
arcs put distinct boundary center directions more than40 degrees
apart. Therefore these open 30-degree corner intervals are disjoint,
and the corresponding resultant lifts obey
\[
 \beta_A<\beta_B<\beta_C,
 \qquad
 \beta_C-\beta_A<2\theta+\frac\pi6<\pi.
 \tag{6}
\]
For the final exact comparison, \(\theta<5\pi/12\). For example
\[
 \cos\frac{5\pi}{12}<\frac13<\frac9{25}.
\]
The first inequality follows by squaring positive quantities:
\((2-\sqrt3)/4<1/9\), equivalent to \(\sqrt3>14/9\), whose
square is \(243>196\). Cosine is strictly decreasing on [0,pi].

Thus all three resultants lie in one open cone of aperture less than
pi, with B strictly between the two endpoints. More explicitly,
\[
 u=\frac{\det(F_B,F_C)}{\det(F_A,F_C)}>0,
 \qquad
 v=\frac{\det(F_A,F_B)}{\det(F_A,F_C)}>0.
 \tag{7}
\]
The planar determinant identity gives (3). Both physical two-corner
masks, unequal corner weights and zero individual weights are included.
The same proof works with any independently chosen positive corner
weights at the three bodies; there is no relation between those
choices in the geometric theorem.

## 2. A complete four-load house mask is impossible

Use the house labeling of `FIVE_BODY_BICONNECTED_REDUCTION.md`:
\[
 E=\{13,14,15,24,25,35\},
 \qquad\text{loaded bodies }\{1,2,3,4\},
\]
with the clear hub H=5. Its three actual positive neighbors are1,2,3;
vertex4 is not added as a neighbor. The actual boundary path is
\(3\! -\!1\! -\!4\! -\!2\).

**Corollary.** The three hub-neighbor bodies1,2,3 cannot all have two
physical circle corners. This excludes that entire mask regardless of
the physical circle mask of vertex4.

Suppose all three have the radial-S two-corner mask. Since H physically
touches each, `RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md` gives
\[
                          c_H\cdot F_i>0
                         \qquad(i=1,2,3).
 \tag{8}
\]
The result holds for every circle-weight split, with zero individual
corner weights permitted. Apply Section1 to the actual path1--4--2:
\[
                          F_4=uF_1+vF_2,
                          \qquad u,v>0.
 \tag{9}
\]
Summing the full component's force equations cancels every internal
pair force. The clear hub has no circle load, so
\[
 0=F_1+F_2+F_3+F_4=(1+u)F_1+(1+v)F_2+F_3.
 \tag{10}
\]
Taking the scalar product with its true center c_H contradicts (8).
Reflection gives the corresponding four-load house mask with hub1 and
loaded neighbors3,4,5. All four completion squares remain in place.

## 3. The sole unique-corner body of a four-load fan cannot be internal

Consider the selected four-load fan with clear universal hub H and
actual boundary path \(u_1-u_2-u_3-u_4\). All four path bodies have
positive total circle load. Suppose every path body has two physical
circle corners except possibly one of the internal vertices u_2,u_3.

**Corollary.** This entire physical-mask family is impossible.

If all four bodies have two physical corners, the whole-component
pressure contradiction is already Section3 of
`RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md`. Otherwise reflect the path so
the sole one-corner body is u_2. The three radial-S bodies satisfy
\[
                  c_H\cdot F_1>0,\quad
                  c_H\cdot F_3>0,\quad
                  c_H\cdot F_4>0.
 \tag{11}
\]
The actual path u_1--u_2--u_3 and Section1 give
\(F_2=uF_1+vF_3\) with u,v>0. Hence its projection on c_H is
also strictly positive. This contradicts the full component balance
\(F_1+F_2+F_3+F_4=0\).

Only the physical masks and the true boundary path were used. No
degree-two force equation was imposed on either internal fan body.
All seven positive graph edges, every free normal and actual shared
mean, and all four arbitrary completion squares are retained.

## 4. Scope

These are complete mask exclusions, not closure of either parent
graph. In a surviving four-load house at least one of the three actual
neighbors of its clear hub has a unique physical circle corner. In a
surviving four-load fan there is either a unique-corner endpoint or at
least two unique-corner bodies. No claim is made here about those
remaining masks or their exterior completion capacity. No numerical
probe, Lean compilation or CI is used as a premise.
