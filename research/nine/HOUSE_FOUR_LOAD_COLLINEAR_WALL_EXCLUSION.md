# The entire collinear-hub-wall four-load house is excluded

**Status: complete hand whole-wall exclusion; root and separate independent full
hand audits passed.** Work in

\[
                  \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}
\tag{1}
\]

with the exact positive house and labels

\[
        H=5,\quad A=3,\quad B=1,\quad C=4,\quad D=2.
\]

The loaded boundary path is A--B--C--D. The physically clear hub H
has exactly the three positive spokes HA,HB,HD; HC is absent. The
two endpoint bodies A,D have degree two, B has degree three, and C
has degree two. All actual physical masks, shared means and four
arbitrary completion squares remain.

**Theorem.** The full collinear-wall domain of
HOUSE_FOUR_LOAD_ENDPOINT_OWNER_REDUCTION.md is impossible. In
particular, the two endpoint contacts cannot both be H-owned.

The proof uses the original three-force hub equation and genuine
endpoint equations. The origin estimate uses a positive geometric
reweighting of physical circle corners, not a replacement stress.

## 1. The complete wall and actual transverse means

The complete owner reduction gives

\[
                       n_A=n_B=-n_D,
                    \qquad\mu_D=\mu_A+\mu_B,
\tag{2}
\]

where every mu is strictly positive. Normalize H=[0,1]^2 and
n_A=n_B=e_y, n_D=-e_y. Write the actual applications as

\[
                  P_A=(x_A,1),\quad P_B=(x_B,1),
                       \quad P_D=(x_D,0).
\tag{3}
\]

All three coordinates belong to[0,1]; an application can be any
actual mean on a positive-length shared side. The true hub torque is

\[
                 \mu_Dx_D=\mu_Ax_A+\mu_Bx_B.
\tag{4}
\]

The complete four-boundary-path separation theorem gives
|P_A-P_D|>1, so x_A!=x_D. Equations (2),(4) therefore make x_A!=x_B
and put x_D strictly between x_A and x_B. Reflect horizontally to get

\[
                            x_A<x_D<x_B.
\tag{5}
\]

This does not replace an actual side mean by an interior point or a
midpoint. Both endpoint contact sets remain fully retained.

The actual boundary path is clockwise in these coordinates. Indeed A
and B occupy the exterior of H's top support line. Their actual H
contact sets are ordered left to right by (5): they cannot overlap in
a relative interval or place a vertex in the other's side interior,
since the two inward tangent sectors above that support would then
overlap. A possible common endpoint preserves this order. D occupies
the exterior of the bottom support line. Thus the H port order A,B,D
is clockwise. The selected house outer face H,A,B,C,D,H, extended
through the actual boundary bodies to their circle corners, preserves
that order. There is no HC force or port.

Let O=(X,Y) be the true disk origin in this normalized hub frame.
Circle resultants throughout are vectors weighted from O.

## 2. Both endpoint resultant horizontal components are negative

Let g_AB point from A to B, and g_CD from C to D, at their actual
boundary-contact applications Q_AB,Q_CD. The complete directed
boundary-moment sign theorem, with the clockwise order just proved,
gives

\[
 M_{AB}:=\det(Q_{AB}-O,g_{AB})<0,
 \qquad
 M_{CD}:=\det(Q_{CD}-O,g_{CD})<0.
\tag{6}
\]

Arbitrary shared-boundary means are included in this sign theorem.
The genuine endpoint force and origin-torque equations are

\[
 F_A=\mu_Ae_y-\gamma_{AB}g_{AB},
       \qquad \mu_A(x_A-X)=\gamma_{AB}M_{AB}<0,
\tag{7}
\]

\[
 F_D=-\mu_De_y+\gamma_{CD}g_{CD},
       \qquad \mu_D(x_D-X)=\gamma_{CD}M_{CD}<0.
\tag{8}
\]

Hence X>x_D>x_A. Proper concurrence applies only to the two true
degree-two endpoints, each with a physical boundary neighbor. Its
positive radial points, relative to O, are

\[
 q_A=(x_A-X,1-Y)+\ell_A e_y,
 \qquad
 q_D=(x_D-X,-Y)-\ell_D e_y,
                    \qquad\ell_A,\ell_D\ge0.
\tag{9}
\]

Each q_i is a positive multiple of its actual nonzero F_i, including
every physical two-corner weight split. Therefore

\[
                           (F_A)_x<0,\qquad(F_D)_x<0.
\tag{10}
\]

The endpoint resultant minor angle is greater than120 degrees by the
whole-path theorem. If (F_A)_y<=0, (9) would imply Y>=1 and then
(F_D)_y<0. If (F_D)_y>=0, it would imply Y<=0 and then (F_A)_y>0.
Each case puts both resultants in one closed90-degree quadrant and
is impossible. Thus

\[
                            (F_A)_y>0>(F_D)_y.
\tag{11}
\]

No equation of the internal degree-three body B has been shortened.

## 3. The actual endpoint centers are northwest and southwest

The genuine path B--C--D gives F_C=uF_B+vF_D, u,v>0, by
THREE_BOUNDARY_PATH_RESULTANT_CONE.md. Full component balance becomes
F_A+(1+u)F_B+(1+v)F_D=0. Its normalized positive physical-corner
combination gives the geometric origin estimate

\[
 R^2+|O-(1/2,1/2)|^2\le\frac92,
          \qquad -\frac3{10}<Y<\frac{13}{10}.
\tag{12}
\]

The last inequalities use 9/2-R^2<3/5<16/25. No original multiplier
or torque is changed by this geometric reweighting.

Every point of A has height at least1, so its center height relative
to O is at least3/2-Y>0. Every point of D has height at most0, so
its relative center height is at most-1/2-Y<0.

For clarity, here is the full own-frame check of the horizontal
center sign; it is not inferred merely from the resultant's sign.
Consider a square with minimum-y actual support point P=(x,y)
relative to O, with x<0, y>-1/2 and a circle resultant of negative
horizontal component. In the aligned frame a strictly positive
center horizontal coordinate would make every far circle corner
have strictly positive horizontal coordinate. Its center coordinate
must therefore be nonpositive, retaining the two-corner transition.

For an oblique frame, P is its unique bottom vertex. Its inward axes
are u=(c,s),v=(-s,c), with c,s>0 and c^2+s^2=1. If the relative
center horizontal coordinate x+(c-s)/2 were nonnegative, then c>s
and x>=-(c-s)/2. The center's own projections would satisfy

\[
 \begin{split}
 cx+sy+\tfrac12&\ge s\bigl(y+(c+s)/2\bigr)>0,\\
 -sx+cy+\tfrac12&>\tfrac12(1-c)>0.
 \end{split}
\tag{13}
\]

Its unique physical far corner is consequently P+u+v, whose first
coordinate is at least(c-s)/2>0. That contradicts the negative
horizontal resultant. Thus the oblique center is strictly to the left.

Apply this check to A using (7),(10),(12). Apply it to D after
reflection across the horizontal axis: its reflected support point
has relative coordinates(x_D-X,Y), with Y>-3/10>-1/2, and its
horizontal resultant is still negative. Both masks and all shared
means are covered. Write the actual centers as

\[
 c_A-O=(-r_A\sin\delta_A,r_A\cos\delta_A),
 \quad
 c_D-O=(-r_D\sin\delta_D,-r_D\cos\delta_D),
\tag{14}
\]

where 0<=delta_A,delta_D<pi/2.

## 4. The real three-contact path fixes the coupled angle domain

The clockwise path established in Section1 runs from the northwest
center in (14), through B,C, to the southwest center along the
complementary right arc. Its total angle is pi+delta_A+delta_D.
Each of its three actual boundary contacts spans less than
theta=acos(9/25). Therefore

\[
         \delta_A+\delta_D<\alpha:=3\theta-\pi<\pi/6.
\tag{15}
\]

This is an actual path-order statement, not a choice of the shorter
endpoint arc. Every endpoint frame lies inside the full interval of
the support-height theorem.

## 5. The two actual support heights exceed the available unit gap

Apply BOUNDARY_UNIT_SUPPORT_HEIGHT.md in the upward direction to A
and in the downward direction to D. Their actual minimum support
heights from O are exactly1-Y and Y, respectively, by (3). Thus

\[
                       1-Y\ge f_R(\delta_A),
                         \qquad Y\ge f_R(\delta_D),
\tag{16}
\]

where

\[
       f_R(t)=(R-\sqrt2)\cos t-\frac9{40}\frac{\sin^2t}{\cos t}.
\]

The complete coupled-angle inequality of that source, using (15),
gives

\[
 1=(1-Y)+Y\ge f_R(\delta_A)+f_R(\delta_D)
                >f_R(0)+f_R(\alpha)>\frac{2241}{2225}>1.
\tag{17}
\]

This contradiction closes the entire collinear-wall domain. The
strict margin holds at both radius endpoints. No parallel frame is
imposed on A,B,C,D, and every physical corner mask and actual shared
application remains.

Together with HOUSE_FOUR_LOAD_ENDPOINT_OWNER_REDUCTION.md, the only
remaining four-load house domain is the specified physically unique
free endpoint D with a positive-length shared DC side and arbitrary
other endpoint owner. That remaining domain is not excluded here.
The house's other two load orbits and the full nine-square theorem
remain separate obligations. No secondary minimizer, numerical
parameter cover, Lean compilation or CI is used.
