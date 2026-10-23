# The sharp radius as a five-corner model

The sharp eight-square radius can be defined by five points in a disk
and five projected distances. No numerical radius bracket, approximate
root, or list of admissible decimal coordinates is part of the definition.

The points are the outward corners of the five fixed exterior squares.
The two intervening exterior squares contribute their widths to the
projected distances; their translation freedoms do not enter this model.

## 1. The geometric definition

Fix an orthonormal frame and write
\[
 e_t=(\cos t,\sin t),\qquad f_t=(-\sin t,\cos t),
 \qquad 0\le t\le\frac\pi4.
\tag{1}
\]
For five points \(P_1,P_2,P_3,P_4,P_5\), impose the following
five conditions.

| Projected distance | Required span |
| --- | --- |
| \((P_2-P_1)_y\) | \(\ge2\) |
| \((P_2-P_3)_x\) | \(\ge3\) |
| \((P_3-P_4)_y\) | \(\ge2\) |
| \(f_t\cdot(P_4-P_5)\) | \(\ge1+\sin t\) |
| \(e_t\cdot(P_1-P_5)\) | \(\ge2+\cos t\) |

Define
\[
 \boxed{
 R_\star=
 \min\left\{\max_{1\le i\le5}\|P_i\|:
       0\le t\le\frac\pi4,\quad
       P_1,\ldots,P_5\text{ satisfy the five spans above}\right\}.
 }
\tag{2}
\]
Thus one asks for the smallest centered circle accommodating this
projected contact chain. A common change of orthonormal coordinates
does not change the problem.

The minimum is attained. Its angle and five points are unique in the
chosen frame, and
\[
                         R_\star^2=q_*.
\tag{3}
\]
Here \(q_*\) is the exact stationary value in the existing sharp
theorem. The companion
[selection proof](HAND_FIVE_CORNER_MODEL_SELECTION.md) proves these
statements over the entire domain in (2), without the historical
five-interval enclosure. The
[unrestricted eight-square theorem](HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md)
then identifies (2) with the least enclosing radius for eight unit
squares. Numerical radius estimates are consequences of (3), rather
than a rule for selecting the constant.

## 2. Why the spans have these values

The points correspond, in order, to the outward corners of the
exterior anchors A, B, D, E and H. Four squares use the fixed frame;
H uses the frame \((e_t,f_t)\). Their centers are
\[
\begin{aligned}
 A&=P_1+(-\tfrac12,\tfrac12),&
 B&=P_2+(-\tfrac12,-\tfrac12),\\
 D&=P_3+(\tfrac12,-\tfrac12),&
 E&=P_4+(\tfrac12,\tfrac12),\\
 H&=P_5+\tfrac12(e_t+f_t).
\end{aligned}
\tag{4}
\]
The A/B and D/E contacts give the two vertical spans of two.
The intervening square T gives the horizontal span of three from
the B corner to the D corner. The intervening square G and the
mixed-frame contacts give the last two spans. Their cosine and sine
terms are the exact projections of unit-square sides.

At the minimum, all five inequalities are equalities and all five
points lie on the circle. The model therefore has a literal
circle-contact interpretation, not only an optimization interpretation.
Section 5 of the selection proof establishes this rigidity.

## 3. The symmetric circle equations

The relevant radius is below two. For any \(R<2\), the five-point
feasibility problem has an equivalent description using nonnegative
coordinates
\[
 u,v,r,w,U,V\ge0,\qquad u,v\le R.
\]
Put the first four points on the circle in the form
\[
 P_1=(r,-u),\quad P_2=(U,2-u),\quad
 P_3=(-V,2-v),\quad P_4=(-w,-v).
\tag{5}
\]
Their exact circle and span equations are
\[
\boxed{
\begin{aligned}
 r^2+u^2&=R^2,& U^2+(2-u)^2&=R^2,\\
 w^2+v^2&=R^2,& V^2+(2-v)^2&=R^2,\\
                         U+V&=3.
\end{aligned}}
\tag{6}
\]
Write \(c=\cos t\), \(s=\sin t\), and set
\[
 K_1=2-c(r-1)+su,\qquad
 K_2=1+cv-s(w-1).
\tag{7}
\]
The fifth point is
\[
                         P_5=-K_1e_t-K_2f_t,
\tag{8}
\]
and its containment condition is simply
\[
                         K_1^2+K_2^2\le R^2.
\tag{9}
\]
Equations (5)--(8) make every projected span an equality. All sign
choices in (6) have a geometric meaning: the first and fourth corners
are below the horizontal axis, the second and third are above it,
and their horizontal coordinates point outwards.

Conversely, any five feasible points with \(R<2\) can be replaced by
points of the form (5)--(8) in the same disk. One moves the first
corner to the right circular arc, sets the upper right corner at the
first vertical span, uses the horizontal span to locate the upper
left arc, and then sets the lower left corner at the second vertical
span. Each operation improves the relevant remaining projection.
The exact monotonic argument is given in Section 2 of the companion;
it does not assume that the original contacts were equalities.

Solving (6) successively gives the earlier radical formulas with
\(q=R^2\):
\[
 r=\sqrt{q-u^2},\quad U=\sqrt{q-(2-u)^2},\quad V=3-U,
 \quad v=2-\sqrt{q-V^2},\quad w=\sqrt{q-v^2}.
\tag{10}
\]
Thus (6)--(9) are the geometric source of those radicals. Their
admissible domain consists of the nonnegative circle coordinates
just stated; no approximate coordinate window defines it.

## 4. Eliminate the radius from the four-circle chain

There is also a useful exact reduction that avoids the nested upper
circle roots. Subtract the two upper circle equations in (6):
\[
 (U-V)(U+V)=(u-v)(4-u-v).
\]
Using \(U+V=3\) gives
\[
 U=\frac{9+(u-v)(4-u-v)}6,\qquad
 V=\frac{9-(u-v)(4-u-v)}6.
\tag{11}
\]
Consequently the squared radius is the explicit polynomial
\[
 \boxed{
 q(u,v)=\frac{\bigl(9+(u-v)^2\bigr)
                    \bigl(9+(4-u-v)^2\bigr)}{36}.
 }
\tag{12}
\]
Only the two lower-circle roots remain:
\[
             r=\sqrt{q(u,v)-u^2},\qquad
             w=\sqrt{q(u,v)-v^2}.
\tag{13}
\]
On the natural domain
\[
 0\le u,v\le\sqrt{q(u,v)}<2,
 \qquad 0\le t\le\pi/4,
\tag{14}
\]
(11) automatically gives positive \(U,V\). Indeed their circle
identities give \(|U|,|V|<2\), whereas their sum is three. Thus
(12)--(14), together with (7) and (9), give an equivalent
two-height version of the model below radius two.

Formula (12) is also a chord formula. The upper corners have horizontal
separation three and vertical separation \(u-v\); their midpoint is
orthogonal to their connecting chord. Its distance from the origin,
combined with half the chord length, gives exactly (12).

## 5. What stationarity means

At the minimum, the contact equations are exact and the parameters are
interior. If
\[
                   F(q,u,t)=K_1^2+K_2^2-q,
\]
then they satisfy
\[
                          F=F_u=F_t=0.
\tag{15}
\]
These equations characterize the selected minimum after its global
optimality has been proved. They need not be used as a numerical-root
definition.

The position equation has a direct mechanical interpretation: positive
weights on the five projected contacts balance positive radial forces
at the five circular corners. The tilt equation is the remaining
rotational balance. Section 5 of the companion gives the weights and
proves their exact equivalence to (15). Their positivity also proves
uniqueness of the five points at the minimizing angle.

The selection proof establishes uniqueness of the global minimum and
of the stationary zero in the already proved analytic strip. It does
not assert that every stationary point at arbitrary larger radii is
the same point.

## 6. Recovering the square family

Use (4) at the unique minimizing chain. The two remaining exterior
centers have the form
\[
                  T=(U-\tfrac32,z),\qquad
                  G=H+e_{t_*}+\eta f_{t_*}.
\tag{16}
\]
Their two translation parameters, together with the central square's
two center coordinates and orientation, give the five freedoms in the
equality family. The
[geometric equality model](EIGHT_SQUARE_GEOMETRIC_EQUALITY_MODEL.md)
states the complete admissible domain using disk containment, the two
sliding segments, and the central square's actual separating axes.
Its comparison with the earlier coordinate domain and all pair
separations is supported by
[the equality-family theorem](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md).
The original-center pullback in the unrestricted theorem proves that
every equality packing is obtained in this way.

The five-corner minimum specifies the rigid geometric data. The family
conditions specify the allowed motion of the other three squares.
