# A four-load fan cannot have both endpoint normals owned by its hub

**Status: complete hand implication at the stated full physical scope;
root and separate independent full hand audits passed.** Work in 79/40<=R<=sqrt(1105)/16 with the selected exact
positive fan component

\[
 Hu_i\quad(1\le i\le4),\qquad
 u_1u_2,\quad u_2u_3,\quad u_3u_4.
\tag{1}
\]

H is unloaded and physically circle-clear. All four path bodies are
loaded, the endpoints have positive degree2, and the two internal path
bodies have positive degree3. Every actual contact point and shared
application mean, physical circle-corner mask and individual zero corner
weight is retained, together with all four completion squares.

**Theorem.** The actual normals from H to u_1 and u_4 cannot both be
side axes of H. This includes every positive-length shared endpoint
side and every endpoint-valued application mean. No new normal choice
or motion of a square is made in this theorem.

The proof uses the full four-force hub equation and the two genuine
endpoint equations. It does not assign a degree-two equation to an
internal path body.

## 1. Whole-path endpoint angle and contact restrictions

FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md gives two facts for this
entire four-load path:

1. Every pair P in H intersect u_1 and Q in H intersect u_4 has
   |P-Q|>1. Actual side means belong to those contact sets.
2. The minor endpoint center angle is strictly greater than5pi/6,
   while each actual circle-resultant direction is strictly within
   pi/12 of its own center direction.

The triangle inequality for angular distance on the unit circle gives
the following useful further consequence. If F_1,F_4 are the nonzero
endpoint circle resultants, their minor directional separation obeys

\[
                 \angle(F_1,F_4)>
                 \frac{5\pi}{6}-2\frac\pi{12}
                 =\frac{2\pi}{3}.
\tag{2}
\]

All statements include physical two-corner endpoints with unequal or
zero individual weights. Directions are measured about the true disk
origin. A subsequent rigid coordinate translation for contact geometry
does not translate a force vector.

## 2. Two contact triangles facts, with their precise scopes

First, UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md says that if one of
two actual normals from H to touching neighbors is a side axis of H,
their scalar product is nonnegative. This is purely geometric and
requires no load or degree assumption on those neighbors.

Second, two neighbors attached at opposite H vertices with strict
opposite vertex-cone normals cannot touch. Here is the complete short
proof. Normalize H=[0,1]^2 and write the actual H-to-neighbor normals
as

\[
 n=(-a,-b),\qquad m=(c,d),\qquad a,b,c,d>0,
 \qquad |n|=|m|=1.
\tag{3}
\]

Their H applications are necessarily P=(0,0) and Q=(1,1).
P is a minimum-n support point of the first neighbor S. Since
n dot m<0, the strict support-span lemma in that same source gives

\[
                       \max_{x\in S}m\cdot x<1.
\tag{4}
\]

The other neighbor T lies in m dot x>=m dot Q=c+d>1, where the last
inequality follows from c,d>0 and c²+d²=1. Thus S,T are closed-disjoint.
Reflections and rotations give every pair of opposite H vertices.
Side-axis limits are handled by the first triangle fact rather than
by replacing the strict inequalities in (3).

## 3. Equal endpoint axes are impossible

Let n_i be the actual unit normal from H to u_i and mu_i>0 its
magnitude. If n_1=n_4, both complete contact sets lie on the same
unit side of H. Any two of their application points have distance at
most1, contrary to Section1. This removes the entire common-axis case,
including all overlaps or endpoint-valued means.

## 4. Opposite endpoint axes are impossible

After a rotation take

\[
                         n_1=e_y,
                         \qquad n_4=-e_y.
\tag{5}
\]

The physical triangles H,u_1,u_2 and H,u_3,u_4 and the first fact of
Section2 give

\[
                    (n_2)_y\ge0,\qquad(n_3)_y\le0.
\tag{6}
\]

The complete unloaded hub equation is

\[
                   \sum_{i=1}^4\mu_i n_i=0.
\tag{7}
\]

Its horizontal coordinate says mu_2(n_2)_x+mu_3(n_3)_x=0.
Thus the two horizontal components are either both zero or have
strict opposite signs.

If both vanish, (6) and unit length give n_2=e_y,n_3=-e_y.
Their negative scalar product contradicts the first triangle fact
at the actual physical triangle H,u_2,u_3.

If their horizontal signs oppose and at least one of n_2,n_3 is
a side axis of H, then

\[
                     n_2\cdot n_3<0
\tag{8}
\]

by (6) and the strictly negative product of horizontal components.
The same side-normal triangle fact again gives a contradiction.
If neither is a side axis, their vertical signs in (6) are strict
as well. They strictly expose opposite H vertices, so the second
fact of Section2 makes u_2,u_3 disjoint, contrary to their positive
edge. This exhausts (5).

## 5. Perpendicular endpoint axes force all four hub normals

After a rigid choice of the two axis directions take

\[
                         n_1=e_y,
                         \qquad n_4=e_x.
\tag{9}
\]

The two endpoint contact triangles give

\[
                    (n_2)_y\ge0,\qquad(n_3)_x\ge0.
\tag{10}
\]

The two coordinates of the full hub balance (7), using mu_1,mu_4>0,
then force

\[
                         (n_2)_x<0,
                    \qquad(n_3)_y<0.
\tag{11}
\]

If both normals are non-axis, (10)--(11) place them in the strict
northwest and southeast H vertex cones. They would attach at opposite
vertices and could not touch, by Section2. If exactly one is an axis,
their scalar product is strictly negative, contradicting the first
triangle fact. The only remaining possibility is therefore

\[
                         n_2=-e_x,
                         \qquad n_3=-e_y.
\tag{12}
\]

This is a conclusion about the four actual force directions. It does
not align any of the four boundary squares with H and does not fix
their application means.

## 6. The true endpoint equations contradict their angular separation

Use only the **geometric** direction lemma in Section2 of
BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md. For two physically touching
neighbors of perpendicular H sides, its short inward-segment proof
controls every actual normal between the neighbors, including a shared
side and a common triple junction. Its later degree-two force argument
is not used for either internal fan body.

For H normals n_1=e_y,n_2=-e_x, this lemma says that the actual
boundary-pair normal g_12 directed u_1 to u_2 has

\[
                         (g_{12})_x\le0,
                         \qquad(g_{12})_y\le0.
\tag{13}
\]

For H normals n_3=-e_y,n_4=e_x, its rotated version says that the
actual g_34 directed u_3 to u_4 has

\[
                         (g_{34})_x\ge0,
                         \qquad(g_{34})_y\ge0.
\tag{14}
\]

Let gamma_12,gamma_34>0 be the two actual boundary-edge magnitudes.
The genuine degree-two endpoint equations, with the actual circle
resultants based at the disk origin, are

\[
 F_1=\mu_1 e_y-\gamma_{12}g_{12},
 \qquad
 F_4=\mu_4 e_x+\gamma_{34}g_{34}.
\tag{15}
\]

By (13)--(14), both vectors are in the closed northeast quadrant;
F_1 has strictly positive vertical component and F_4 strictly positive
horizontal component. They are nonzero and their minor directional
angle is at mostpi/2. This contradicts (2), which makes that angle
strictly greater than2pi/3.

The perpendicular case is therefore excluded. Equal, opposite and
perpendicular directions exhaust two side axes of one square, so the
theorem follows.

## 7. Whole-family scope and the remaining owner cover

This excludes every fan whose two endpoint normals are both owned by H,
whether an endpoint contact is a singleton or a shared side with its
mean at any actual point. All one-/two-circle-corner masks, inner
degree-three equations, hub magnitudes and four extras remain. The
argument does not use a secondary minimizer or a new normal selection.

Together with FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, the completed
two-endpoint owner families are now both-tip-owned singleton contacts
and both-hub-owned axes. A mixed hub/tip pair, a shared endpoint
opposite a tip-owned singleton, and genuine free vertex/vertex
endpoint contacts remain outside these two theorems. Those full
physical domains require separate treatment before the fan or its
five-body parent is closed.

No numerical pose search, Lean compilation or CI is used.
