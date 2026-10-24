# Every four-load fan needs a hub-owned endpoint contact

**Status: complete hand implication at the stated full physical scope;
root and separate independent full hand audits passed.** Work in the declared window
\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The positive component is the four-load fan
\[
 Hu_i\ (1\le i\le4),\qquad u_1u_2,\ u_2u_3,\ u_3u_4,
\tag{2}
\]
with H unloaded and all four path bodies loaded. The endpoints have
exact positive degree2; the internal path bodies retain degree3.

**Theorem.** At least one of the two actual endpoint normals Hu_1,Hu_4
must be a side axis of H. Equivalently, the entire family in which
neither endpoint is H-owned is impossible. This covers arbitrary free
endpoint normals, all physical circle-corner masks, every shared
boundary-side mean and all four completion squares.

The pre-certificate fixed-tip selection already used elsewhere is
retained. No additional normal is selected in this proof.

## 1. The exhaustive endpoint cover

If an endpoint normal is not an H side axis, its H support is a single
vertex. Thus in the family to be excluded both hub endpoint applications
are fixed vertices. `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md` makes
them opposite vertices, since every actual endpoint pair has distance
strictly greater than1.

Each endpoint contact is therefore one of the following:

* a singleton in the relative interior of a side of its boundary tip;
* a free point-only vertex/vertex contact, strict in both vertex cones.

This uses the existing strict point-only vertex/vertex normal
convention: an axis endpoint of such a cone is not retained as an
owned singleton at a tip vertex. No new choice is being imposed here.

At a free endpoint with exactly one physical circle corner, its other
physical pair intersection is either a singleton or a genuine shared
side. In the singleton case the already compatible
`GENERAL_FIXED_TIP_NORMAL_SELECTION.md` removes the free normal. Its
coincident radial-D exception is impossible here because the other
neighbor touches the circle: a shared boundary point has norm strictly
greater than R-sqrt(2), whereas a radial-D inner vertex has exactly
that norm. Thus every still-relevant unique-corner free endpoint must
have a positive-length shared side with its path neighbor.

A physical two-circle-corner free endpoint remains separate, with both
corner weights and their zero endpoints retained. Sections2--4 handle
these two full free-contact alternatives.

We also use that nonconsecutive path bodies are closed-disjoint. For
example, an extra physical u_1u_3 contact would make u_3 touch every
loaded body, contradicting the connected loaded noncontact theorem.
An extra u_1u_4 contact would make a physical loaded four-cycle, also
excluded by that theorem. The other missing pair is reflected. These
are physical noncontacts, not assumptions obtained by omitting graph
edges.

## 2. A free unique endpoint opposite a shared boundary side is impossible

Suppose u_1 has one physical circle corner, Hu_1 is free, and u_1u_2
shares a positive-length side. Write Q for the Hu_1 vertex. The
owned-normal triangle theorem applied at u_1 shows that Q is incident
to that shared side: its outward normal toward H is strict in the
u_1 vertex cone, so its dot product with the shared-side axis is
strictly positive.

Choose an oriented orthonormal frame along the two inward sides of
u_1 at Q, so that, in coordinates relative to the true circle origin,
\[
 \begin{split}
 Q&=(X,Y),\\
 u_1&=Q+[0,1]e_x+[0,1]e_y,\\
 u_2&=Q+[t,t+1]e_x+[-1,0]e_y,\qquad -1<t<1,\\
 n&=(a,b),\qquad a,b>0,
 \end{split}
\tag{3}
\]
where n points from H into u_1. Reflections of the frame are harmless:
all force and torque equations below are written in that same frame.
The two listed positive pair magnitudes at u_1 will be mu for Hu_1
and gamma for u_1u_2. Its actual shared-side mean is
\(Q+\tau e_x\), in the actual overlap interval.

The circle force at u_1 is
\[
                         F_1=\mu(a,b)+\gamma e_y.
\tag{4}
\]
Both components are positive, so its unique physical circle corner is
\[
                  z=Q+e_x+e_y=(X+1,Y+1),
                        \qquad X,Y>-1/2.
\tag{5}
\]
Write \(F_1=\lambda z\), \(\lambda>0\), absorbing the irrelevant
common circle factor2.

### 2.1. Every coincidence and shared-mean endpoint is retained

If -1<t<0, Q is in the relative interior of a u_2 side. The tangent
sectors of u_2, u_1 and H at Q then have sizes180,90,90 degrees and
must fill the whole turn. The two latter quadrants must share a
positive boundary ray. Their actual unit sides therefore share a
positive segment, contradicting the point-only Hu_1 premise.

If t=0, the two parallel boundary units share a full unit side. Their
farthest horizontal corner contribution to the squared radius is the
same. Equality of their containing-circle radii forces Y=0: compare
\(\max(Y^2,(Y+1)^2)\) and \(\max(Y^2,(Y-1)^2)\).
Equation(5) then gives X+1=sqrt(R^2-1)>1, so X>0.
But the exact u_1 torque about Q is
\[
                         \lambda(Y-X)=\gamma\tau,
                    \qquad 0\le\tau\le1.
\tag{6}
\]
Its left side is negative and its right side nonnegative. This is
impossible even at the actual mean tau=0. Consequently
\[
                         0<t<1,\qquad t\le\tau\le1.
\tag{7}
\]
In particular Q does not belong to u_2. The nonconsecutive physical
noncontact from Section1 also keeps u_3 away from Q.

### 2.2. The endpoint's complete force and torque fix the normal slope

The two coordinates of (4) and (6) give
\[
 \lambda(X+1)=\mu a,\qquad
 \lambda(Y+1)=\mu b+\gamma,\qquad
                    \lambda(Y-X)=\gamma\tau.
\tag{8}
\]
Thus Y>X and, because tau<=1,
\[
 \frac ba
  =\frac{Y+1-(Y-X)/\tau}{X+1}\le1.
\tag{9}
\]
Every actual mean, including tau=1, remains. Therefore a>=b>0.

### 2.3. The full hub torque has the wrong sign

H has Q as a strict support vertex for n. It physically touches u_2,
whose minimum first coordinate is X+t>X. Thus one inward H side axis
at Q has positive first coordinate. Strict support by n and
orthogonality force its two inward axes to have exactly the form
\[
                 w=(c,-d),\qquad v=(-d,-c),
            \qquad c,d>0,\quad c^2+d^2=1.
\tag{10}
\]
The other choice for the orthogonal axis would have both coordinates
positive and would violate strict inward support. Moreover
\(ac-bd<0\), and (9) implies c<d.

The other endpoint vertex of H is
\[
                              Q_4=Q+w+v.
\tag{11}
\]
The H arc Q--(Q+v)--Q_4 has first coordinate at most X, since c<d.
It cannot contain an H contact with u_2. That contact is therefore
on the other arc Q--(Q+w)--Q_4. The physical fan port order puts the
u_3 spoke on this same arc. Coincidence of that spoke with Q_4 is
allowed; its moment about Q_4 is zero. An inner side mean stays on
its actual side of the arc. The port-order justification is exactly
that of `FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md`, Section2: the outer
face contains all four boundary vertices, and the two chords are on
the same side between the endpoint spokes. No third body is needed
at Q, which was excluded in Section2.1.

For every point P on this arc and every actual outward H normal m
there,
\[
                         \det(P-Q_4,m)\le0.
\tag{12}
\]
On Q+s w with outward normal -v the value is s-1. On
Q+w+s v with outward normal w it is again s-1. At Q+w, its whole
normal cone consists of positive combinations of w and -v and gives
the same weak sign. At Q_4 the determinant is zero. Positive side
means preserve these inequalities.

In contrast, the u_1 force at Q has strictly negative moment:
\[
 \det(Q-Q_4,n)
       =b(d-c)-a(d+c)
       \le-2bc<0.
\tag{13}
\]
The u_4 force at Q_4 has zero moment. Thus all four positive hub
forces have nonpositive moment about Q_4, and the u_1 contribution
is strict. This contradicts the full unloaded hub force/torque
balance. Section2 excludes the entire unique-free/shared-side
alternative, independently of the other endpoint's physical mask.

## 3. A physical radial free endpoint has two distinct inner-vertex contacts

The remaining free endpoint has two physical circle corners. Put
\[
                          d=\sqrt{R^2-1/4}-1>9/10.
\tag{14}
\]
Its square, in an outward radial frame (e,f=Je), is
\[
                     [d,d+1]e+[-1/2,1/2]f.
\]
A free Hu_1 vertex is one of its two inner vertices. The exact local
routing argument of `BOWTIE_RADIAL_FREE_INTERFACE_PRESSURE.md`,
Section1, applies unchanged: it uses only this radial endpoint's
two positive forces, the physical triangle H,u_1,u_2, and the fact
that u_2 touches the circle. It uses no degree-two equation at u_2.
It shows that u_1u_2 is a singleton at the other inner vertex, and
that its genuine normal is strict in that vertex cone. In particular
there is no shared u_1u_2 mean in this radial-free case.

Thus u_2 cannot contain the H endpoint vertex. Nor can the other
inner body, by the nonconsecutive physical noncontact in Section1.
Together with the elementary tangent-sector fact for a tip-owned
side-interior endpoint, this proves that **after Section2 every inner
hub application is distinct from both opposite endpoint vertices**.

## 4. The radial-free adapter to the complete endpoint metric inequality

All remaining endpoints are either tip-owned side-interior singletons
or the radial-free vertices from Section3. The geometric hub order,
torque signs and true-origin arguments of
`FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md`, Sections2--3, now apply with
the same scope: their only ownership input in those sections was that
no inner hub application equals an endpoint, just proved for both
remaining types.

Consequently, in the true-circle coordinates, write
\[
 \begin{gathered}
 P_1=(x-\sigma,h)=(-X_1,h),\quad
 P_4=(x+\sigma,h)=(X_4,h),\quad \sigma=1/\sqrt2,\\
 X_1,X_4>0,\qquad X_1+X_4=\sqrt2,\qquad h>0,\\
 n_1=(-\cos\phi_1,\sin\phi_1),\quad
 n_4=(\cos\phi_4,\sin\phi_4),\quad0\le\phi_i\le\pi/4.
 \end{gathered}
\tag{15}
\]
The actual path order is counterclockwise along the lower hub arc.
The positive boundary-edge moment sign and the genuine endpoint torque
remain valid for both types.

For a tip-owned endpoint, Sections4--6 of that source already give
an upper-side center angle delta, \(0\le\phi\le\delta<\pi/2\),
and, once delta<alpha below, the uniform estimate
\[
                          X\ge d\cos\delta-\frac35\sin\delta.
\tag{16}
\]
This is a one-endpoint calculation and imposes no owner condition on
the other endpoint.

We supply the full radial-free calculation. Consider the left endpoint.
Its counterclockwise outgoing boundary-edge moment is positive. In the
radial frame, the local routing of Section3 therefore places its H
contact and next contact at
\[
               P_1=d e-\tfrac12 f,\qquad
               T=d e+\tfrac12 f,\qquad f=Je.
\tag{17}
\]
Indeed, reversing these signs gives an outgoing normal
\(-A e-B f\), A,B>0, at \(d e-f/2\), with strictly negative origin
moment \(-dB-A/2\). The displayed order instead has positive moment.
The strict inward normal at P_1 consequently has the form
\[
                    n_1=\cos\eta\,e+\sin\eta\,f,
                              0<\eta<\pi/2.
\tag{18}
\]
Combine this with (15), and put \(\delta=\phi_1+\eta\). Then
\(e=(-\cos\delta,\sin\delta)\), initially with
\(0<\delta<3\pi/4\). Since \((P_1)_x<0\), equation(17) forces
\(d\cos\delta>(1/2)\sin\delta\), so in fact
\(0<\delta<\pi/2\). The center is a positive radial multiple of e,
strictly upper-left, and the exact contact coordinates are
\[
                      X_1=d\cos\delta-\tfrac12\sin\delta,
                  \qquad h=d\sin\delta+\tfrac12\cos\delta.
\tag{19}
\]
This is stronger than (16). The right endpoint is its reflected
calculation. All circle-weight splits are retained: (17)--(19) use the
physical radial frame, not an assumption of equal corner weights.

The proper concurrence at either radial-free endpoint is
\(q=P+\ell n\), \(\ell\ge0\), and is a positive multiple of its
actual resultant. Equations(15),(19) therefore put that resultant in
the same strict upper quadrant as its center. No claim that a radial
concurrence lies inside its square is made.

## 5. The joint contradiction covers both remaining endpoint types

Both endpoint centers are now in the closed upper quadrants, and their
resultants are in the strict upper quadrants.
Their actual boundary path follows the complementary lower circle arc,
by the port order. As in the complete two-tip-owned proof, put
\[
 \theta=\arccos(9/25),\qquad\alpha=3\theta-\pi,
 \qquad0<\alpha<\pi/6.
\]
The three boundary contacts give
\[
                       \delta_1+\delta_4<\alpha.
\tag{20}
\]
Thus (16) is valid for every tip-owned endpoint, while (19) gives the
same bound for every radial-free endpoint. The concavity argument from
Section7 of `FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md` yields
\[
 \begin{split}
 \sqrt2=X_1+X_4
 &\ge \sum_{i=1,4}\left(d\cos\delta_i-\frac35\sin\delta_i\right)\\
 &>d(1+\cos\alpha)-\frac35\sin\alpha\\
 &>\frac{1431}{1000}>\sqrt2.
 \end{split}
\tag{21}
\]
This contradiction covers the two tip-owned endpoints, the mixed
tip-owned/radial-free pair, and two radial-free endpoints.

## 6. Complete implication and remaining fan obligation

The selected endpoint cover in Section1 is exhaustive when neither
normal is H-owned. Its unique-free singleton cases are removed by the
existing fixed-tip selection; its unique-free shared-side cases are
excluded by Section2; all remaining physical masks are covered jointly
by Sections3--5. Thus this entire non-H-owned endpoint family is closed.

A surviving fan must have at least one H-owned endpoint contact,
including any genuinely shared H/tip side. That remaining family still
requires a complete owner/mean argument or a joint capacity at most3.
No force on a degree-three internal body was split, no shared mean was
frozen, and no one-/two-circle-corner transition was discarded. All
four arbitrary completion squares remain. No numerical diagnostic,
Lean compilation, CI or post-certificate normal change is used.
