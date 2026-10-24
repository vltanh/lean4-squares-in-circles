# A four-load house cannot have both endpoint contacts owned by its tips

**Status: complete hand implication at the stated full physical scope;
root and separate independent full hand audits passed.** Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}
\]
with the selected positive house graph
\[
 E=\{13,14,15,24,25,35\},
 \qquad\text{loaded bodies }\{1,2,3,4\}.
 \tag{1}
\]
The clear hub is H=5. Its actual positive neighbors are3,1,2, and the
four boundary bodies form the path3--1--4--2. Its endpoint bodies3,2
have positive degree two. Vertex1 has degree three; no degree-two
equation will be used for it.

**Theorem.** The two physical intersections \(H\cap3\) and
\(H\cap2\) cannot both be singleton points in relative side interiors
of their respective boundary tips.

This is the complete two-tip-owned endpoint family, with every other
owner, free normal, actual shared mean and physical circle mask retained.
The reflection of (1) is included. The four arbitrary completion
squares remain in place. In particular no positive or physical H--4
contact is inserted.

## 1. The three actual hub neighbors supply the true-origin bound

Let F_i be the original positive circle resultants. Summing the full
component force equations gives
\[
                         F_1+F_2+F_3+F_4=0.
 \tag{2}
\]
The actual path1--4--2 and
`THREE_BOUNDARY_PATH_RESULTANT_CONE.md` give numbers u,v>0 with
\[
 F_4=uF_1+vF_2,
 \qquad (1+u)F_1+(1+v)F_2+F_3=0.
 \tag{3}
\]
Scale the physical circle-corner weights on bodies1,2,3 by the three
positive coefficients in (3), and normalize their total to1. These
are weights for a convex-combination identity only; the original
certificate and every body force equation remain unchanged.

Every one of the corners z carrying one of these weights is on a body
actually touching H. Hence \(|z-c_H|\le3/\sqrt2\), using its actual
common point, the unit-square diameter and H's circumradius. Since
\(\sum\lambda_z z=0\) and \(|z|=R\),
\[
                   R^2+|c_H|^2
                    =\sum_z\lambda_z|z-c_H|^2\le\frac92.
 \tag{4}
\]
This does not use a bound on the distance of any corner of vertex4
from H. It is the only geometric averaging step that must be changed
from the fan proof below.

## 2. The actual three-port hub gives the same endpoint signs

The whole-path theorem `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`
makes every pair of actual endpoint applications on H have distance
greater than1. Under the theorem's two singleton side-owner hypotheses,
they are H vertices and therefore opposite. Rotate, without translating
the true circle origin, so
\[
 P_3=(x-\sigma,h),\qquad P_2=(x+\sigma,h),
 \qquad \sigma=1/\sqrt2.
 \tag{5}
\]

At either endpoint, the boundary tip occupies a half-plane tangent
sector and H a right-angle sector, with a strict singleton side contact.
Their complement has no sector of angle90 degrees. No third physical
square can contain that endpoint. In particular the actual H--1
application cannot equal either point in (5).

The selected physical planar house has outer face
H--3--1--4--2--H: all four circle-touching path bodies lie on the
unbounded face. Thus the one inner positive H--1 spoke lies on one
of the two H boundary arcs between (5), in the path order3,1,2.
Reflect so this is the lower arc through \((x,h-\sigma)\). A shared
H--1 mean stays on its actual side of that arc. The compatible physical
junction untangling preserves the two distinct endpoint sectors and
this port order.

For every point X on the lower arc and every actual outward H normal n,
\[
              \det(X-P_3,n)\le0,
              \qquad\det(X-P_2,n)\ge0.
 \tag{6}
\]
These are exactly the two lower-side/vertex calculations in
`FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md`, Section2; they concern a single
application and do not require two internal hub spokes. Apply the full
three-force hub torque equation about each endpoint. Its two endpoint
outward normals therefore have the form
\[
 n_3=(-b_3,a_3),\qquad n_2=(b_2,a_2),
 \qquad0\le a_i\le b_i,\quad a_i^2+b_i^2=1.
 \tag{7}
\]
All magnitudes are positive, and no fourth hub term is used.

The actual extended spokes from H through3,1,2 to their circle corners
preserve the same circular port order. The boundary path3,1,4,2 thus
runs counterclockwise along the complementary lower circle arc. As in
the fan proof, zero-stress physical contacts do not change this order.

## 3. Endpoint torque and all physical circle masks

Equation (4) and the boundary-contact lower radius
\(|P_i|\ge R-\sqrt2\) imply
\[
                            -\sigma<x<\sigma.
 \tag{8}
\]
Indeed x>=sigma would give
\(|P_3|^2\le4-R^2<(R-\sqrt2)^2\); the final strict inequality
holds for every R in the window since
\(R^2-\sqrt2R-1>0\), with the exact lower bound887/11200 after
replacing \(\sqrt2\) by10/7 at79/40. Reflect for x<=-sigma.

Lemma1.1 of `FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md` proves that every
actual normal between circle-touching bodies in positive circular order
has strictly positive origin moment, for all contact means. Apply it
to the actual boundary edges3--1 and4--2. The genuine degree-two
endpoint torque equations give
\[
                      \det(P_3,n_3)>0,
                      \det(P_2,n_2)<0.
 \tag{9}
\]
Combining (7)--(9) gives h>0 and the strict endpoint signs
\[
 b_3h>a_3(\sigma-x),\qquad
 b_2h>a_2(\sigma+x).
 \tag{10}
\]

All the own-frame conclusions in Sections4 and6 of that source now
apply separately to the two true degree-two endpoints. For precision,
write the left one as
\[
 X=\sigma-x>0,\quad P=(-X,h),\quad
 n=(-b,a),\quad k=Jn=(-a,-b),
 \quad a=\sin\phi,\ b=\cos\phi,
\]
\[
 S=P+[0,1]n+[-\rho,1-\rho]k,\qquad0<\rho<1.
\]
Its proper radial concurrence is \(q=P+\ell n\), \(\ell\ge0\),
because its other positive neighbor touches the circle. Put
\(N=P\cdot n>0\), \(K=-P\cdot k>0\), and \(Z=K+\rho\).
The complete one-/two-circle-corner analysis gives
\[
 Z\ge\frac12,\quad R^2=(N+1)^2+Z^2,\quad
 c_S=(N+\tfrac12)n-(Z-\tfrac12)k,\quad X\ge bN-aZ.
 \tag{11}
\]
The radial physical mask is exactly Z=1/2 and remains included with
unequal or zero individual circle weights. The center is in the closed
upper-left quadrant, with strictly negative horizontal coordinate and
zero vertical coordinate retained. The concurrence is strictly in the
upper-left quadrant. The right endpoint is the reflected chart. No
internal body receives this concurrence argument.

## 4. The full scalar contradiction

Write the endpoint center angles above the left/right horizontal rays
as \(\delta_3,\delta_2\ge0\). The actual three-contact boundary path
runs along the complementary lower arc. With
\[
 \theta=\arccos(9/25),\qquad\alpha=3\theta-\pi,
\]
the contact center bounds give
\[
 \delta_3+\delta_2<\alpha<\frac\pi6,
 \qquad\cos\alpha=\frac{13959}{15625}>\frac{89}{100},
 \qquad\sin\alpha<\frac9{20}.
 \tag{12}
\]
The complete frame-uniform calculation in the fan source, Section6,
uses only the endpoint chart (11). It gives, for each endpoint,
\[
 X_i\ge d\cos\delta_i-\frac35\sin\delta_i,
 \qquad d=\sqrt{R^2-\tfrac14}-1>\frac9{10}.
 \tag{13}
\]
No hub degree or additional spoke enters that calculation. Its only
angular premise is \(0\le\delta_i<\pi/6\), supplied by (12).

The positive decreasing concave function
\(g(t)=d\cos t-(3/5)\sin t\) has its minimum two-argument sum
at the endpoints of a fixed-sum interval. Equations (12)--(13) give
\[
 \begin{split}
 \sqrt2=X_3+X_2
 &\ge g(\delta_3)+g(\delta_2)>g(0)+g(\alpha)\\
 &>\frac9{10}\left(1+\frac{89}{100}\right)
                       -\frac35\frac9{20}
   =\frac{1431}{1000}>\frac{10}{7}>\sqrt2.
 \end{split}
 \tag{14}
\]
This contradiction excludes the entire stated house owner family.

## 5. Exact remaining scope

At least one endpoint contact H--3 or H--2 in any surviving four-load
house must be outside the two-tip-owned singleton family. It may be
hub-owned, including a positive shared side, or genuinely free
vertex/vertex. Those cases and the whole four-load house are not closed
here. The cone identity was used only for the geometric bound (4);
every torque, concurrence and force statement used the unmodified
original certificate. All four extra squares, all independent frames
and every actual contact mean remain. No numerical proof premise,
Lean compilation or CI is used.
