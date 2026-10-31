# The entire selected nonparallel D-leaf articulation branch is impossible

**Status: complete hand argument; two independent hand audits passed.** In the
declared radius window, the nonparallel alternative of
`D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md` is impossible after the
legitimate finite normal selections described below. This covers both
possible owners of the B--C contact axis, every circle-corner mask, and
the full articulation-height range. No symmetry of B and C is assumed.

The arbitrary-normal D stress control in
`D_LEAF_GENERIC_CONTACT_SELECTION.md` is not contradicted: its
point-only vertex/vertex reactions are removed by pre-multiplier normal
selection. The parallel-left alternative is separate and is not closed
by this manuscript.

## 1. Exact input and the remaining free-normal selection

Use the notation

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 s=1+\sqrt2-R,\qquad
 A=[-s,1-s]\times[h-1,h],\qquad0<h<1.                 \tag{1}
\]

The radial D leaf applies a positive horizontal bridge force to A at
\((1-s,0)\). The other two positive reactions of A are nonparallel.
By the complete left-contact localization, after naming the upper
neighbor B and the lower neighbor C, they have the form

\[
\begin{aligned}
 P&=(-s,h),& n&=(-b,a),& a&=\sin\phi,&b&=\cos\phi,\\
 Q&=(-s,h-1),&m&=(-d,-c),&c&=\sin\psi,&d&=\cos\psi,
\end{aligned}                                                     \tag{2}
\]

where \(0<\phi,\psi<\pi/2\). These normals point from A to its
neighbors. The normal selection in
`D_LEAF_GENERIC_CONTACT_SELECTION.md` removes vertex/vertex A contacts.
Consequently P and Q lie in the **relative interiors** of sides of B
and C, respectively. Thus n and m are actual side-axis directions of
their respective neighboring squares.

All selections in this section are imposed simultaneously before the
physical multiplier theorem. They do not alter an already obtained
stress. There are only finitely many candidate bodies, physical contact
points, circle corners, and contact stars in a fixed minimizing packing.

### 1.1. At least one of B,C has a unique physical circle corner

The bounds needed here and below are

\[
 0<s<\frac9{20},\qquad
 D:=\sqrt{R^2-\tfrac14}-1>\frac9{10}.                    \tag{3}
\]

The first is proved in the localization manuscript. For the second,
\((79/40)^2>193/50=(19/10)^2+1/4\).

The origin is in the open interior of A. Therefore
\(P\cdot n>0\) and \(Q\cdot m>0\). Each facing side of B,C
is thus at positive distance from the origin in its inward normal
direction. If either such body has two physical circle corners, its
center is on that normal axis: its farthest side has normal coordinate
\(\sqrt{R^2-1/4}\), and its facing side has coordinate D. Every
point of that facing side consequently has norm at least D.

One of P,Q has vertical absolute value at most \(1/2\), and hence
norm at most

\[
                   \sqrt{s^2+\frac14}
                   <\frac{\sqrt{181}}{20}<\frac9{10}.      \tag{4}
\]

Its neighboring body therefore cannot have two circle corners. At least
one of B,C has a unique physical circle corner.

### 1.2. Remove a point-only vertex/vertex B--C contact

Suppose BC is a point-only vertex/vertex contact at T. Choose one of
B,C, call it U, having the unique circle corner z just proved to exist.
Its contact with A is at the relative interior point p of a U side, and
its A-contact force has the fixed perpendicular side-axis direction u.
The other force acts at the vertex T with a freely selectable strictly
exposing common normal.

If u and z are nonparallel, their two force lines
\(p+\mathbb R u\) and \(\mathbb R z\) meet at a fixed point q.
Force and torque balance for the three positive forces on U require the
third force line also to pass through q. But q cannot equal T: no vertex
of a square lies on the perpendicular line through a relative-interior
point of one of its sides. Thus only finitely many unit normal directions
at T can give the required third line.

If u and z are parallel, force balance itself requires the third normal
to be parallel to them, again excluding all but finitely many normal
directions. This case is retained explicitly rather than treating a
possibly degenerate wrench determinant as nonzero.

Choose the strictly exposing BC normal outside these finite exceptions.
This can be done for every candidate U and star simultaneously. The BC
junction is distinct from P and Q, because T is a vertex of each body
whereas P,Q are relative side-interior points in their respective bodies.
At a four-square junction the matched conjugate normals used for planar
uncrossing still vary through an open one-parameter interval; excluding
finitely many additional directions is compatible with that construction.
The other strict, nonradial, and finite generic conditions are retained.

The physical multiplier theorem with these preassigned choices therefore
cannot give a positive BC vertex/vertex edge in this nonparallel chart.
Every remaining BC contact has a side-axis owner. A positive-length
shared side has both owners and is included.

Reflect across the horizontal axis and interchange B,C if necessary so
that B is an owner. This exchanges h with \(1-h\), which is why both
height cases will be treated below.

## 2. The B--C normal has one forced sign

Put

\[
 v=Jn=(-a,-b),\qquad k=Jm=(c,-d),
\]
\[
 K=ad+bc=\sin(\phi+\psi)>0,
 \qquad L=bd-ac=\cos(\phi+\psi).
                                                               \tag{5}
\]

The changes between the two actual square frames are

\[
                    m=L n+K v,\qquad k=-K n+L v.          \tag{6}
\]

The origin force and torque equations at A give the exact height
identity

\[
                     h=\frac{ad}{K},
                     1-h=\frac{bc}{K}.                  \tag{7}
\]

### 2.1. A B--C normal parallel to a facing axis is impossible

This observation applies to either loaded body. Suppose its facing side
has inward normal u and the force on its other edge is also parallel to
u. Its circle-load vector must then be parallel to u. The positive
distance of its facing side from the origin makes the center's
u-coordinate positive. A zero transverse circle-load coordinate forces
the center's transverse coordinate to vanish; otherwise every farthest
circle corner has one fixed nonzero transverse sign. The body is
therefore a radial S square in that frame, with outer face at
\(\sqrt{R^2-1/4}\) and inner face at D from (3).

An outward contact on its outer face is impossible: the neighboring unit
square has width at least one in that direction, so would reach beyond
the containing disk. An outward contact with the inner-face normal
cannot have a circle-touching neighbor, by the horizontal-inner-face
part of `C7_FORCE_POLYGON.md`, Lemma 2.1. That lemma applies to every
application point on the full inner side, including shared-side means.
Both B,C are circle-touching. Thus parallel facing/BC normals are
excluded for either body.

Since B owns the BC axis, its normal from B to C is now either v or
\(-v\).

### 2.2. The sign \(-v\) is impossible by a support projection

If the normal were \(-v\), its application point T would minimize
v on B. Since P is on B's minimum-n side, we could write

\[
                     T-P=j n-u v,\qquad0\le j,u\le1.     \tag{8}
\]

The outward normal of C toward B would be v. Since \(v\cdot m=K>0\),
T would maximize the m-coordinate on C. Q minimizes that coordinate,
so \(m\cdot(T-Q)=1\). Therefore

\[
                         m\cdot(T-P)=1+c>1.             \tag{9}
\]

But (6) and (8) give
\(m\cdot(T-P)=Lj-Ku\le\max(L,0)\le1\), a contradiction.
Hence the BC normal is exactly v.

### 2.3. The sign of L and the full contact chart

The point T now maximizes v on B and minimizes m on C, since
\((-v)\cdot m=-K<0\). If L were zero, the two C force normals
would be parallel, already excluded in Section 2.1. If \(L<0\),
the C support point would be the upper endpoint in its k-coordinate.
Since Q is strictly inside that facing side, one would have
\(T=Q+r k\), \(0<r<1\). Then

\[
                         n\cdot(T-P)=-a-Kr<0,
\]

contradicting that P minimizes n on B. Thus \(L>0\), so
\(\phi+\psi<\pi/2\), and instead

\[
                          T=Q-r k,\qquad0<r<1.            \tag{10}
\]

Projecting \(T-P=-e_y-rk\) into B's frame gives

\[
                  j:=n\cdot(T-P)=Kr-a\in[0,1],
 \qquad
                  w:=v\cdot(T-P)=b-Lr\in(0,1).           \tag{11}
\]

The strict bounds on w follow because P is side-interior. Define

\[
                    U=1-w=1-b+Lr\in(0,1).
                                                               \tag{12}
\]

Equations (7) and (11) also give

\[
                              r\ge\frac aK=\frac hd.      \tag{13}
\]

This chart includes every remaining BC axis owner, including all possible
side-contact endpoint degeneracies. No small-angle condition beyond the
proved \(L>0\) has yet been used.

## 3. Actual circle corners, including both two-corner masks

Let \(\gamma>0\) be the BC force magnitude and let
\(\mu_B,\mu_C>0\) be the two A-contact magnitudes. Body force
balance says

\[
                     2m_B=\mu_B n-\gamma v,
 \qquad
                     2m_C=\mu_C m+\gamma v.               \tag{14}
\]

The first load has positive n-coordinate and negative v-coordinate.
The positive n-location of B's facing side makes its farthest
n-coordinate the upper endpoint. Its center's v-coordinate is negative
or zero; otherwise its circle-load v-coordinate could not be negative.
Consequently the following is an actual circle corner, with positive
weight even in the two-circle-corner case:

\[
                            z_B=P+n-Uv.                   \tag{15}
\]

Similarly, (6) and (14) give positive m- and k-coordinates for the load
of C. Its center's k-coordinate is positive or zero, and its opposite
corner from T is an actual positive-weight circle corner:

\[
                   z_C=T+m+k=Q+m+(1-r)k.                 \tag{16}
\]

In the respective square side frames, write these corners as
\((X,Z)\) with the transverse sign made positive. Explicitly,

\[
\begin{aligned}
 X_B&=1+sb+ah,&
 Z_B(r)&=1-b+bh-sa+Lr\ge\tfrac12,\\
 X_C&=1+sd+c(1-h),&
 Z_C(r)&=1+d(1-h)-sc-r\ge\tfrac12.
\end{aligned}                                                     \tag{17}
\]

Thus

\[
              X_B^2+Z_B(r)^2=R^2=X_C^2+Z_C(r)^2.         \tag{18}
\]

At fixed s, angles and h, B's squared corner norm is increasing in r
where \(Z_B>0\), and C's is decreasing where \(Z_C>0\). In world
coordinates the same two corners are

\[
\begin{aligned}
 z_B&=(-s-b+aU,\quad h+a+bU),\\
 z_C&=(-s-d+c(1-r),\quad h-1-c-d(1-r)).
\end{aligned}                                                     \tag{19}
\]

Their horizontal coordinates are negative, since every positive circle
corner of B,C is strictly westward, as proved in the localization
manuscript. Their displayed vertical coordinates are respectively
positive and negative.

The following strict radius budget will yield every contradiction:

\[
\begin{aligned}
 R^2-(s+1)^2
  &=(2+\sqrt2)\bigl(2R-2-\sqrt2\bigr)\\
  &\ge\frac{19}{10}-\frac{\sqrt2}{20}
   >\frac95.
\end{aligned}                                                     \tag{20}
\]

The middle equality at the lower radius endpoint is exact, and the
expression increases with R. No decimal comparison is used.

## 4. If C has two circle corners, B cannot reach the circle

Suppose first that C has two physical circle corners, regardless of
which ones receive positive weight. Its facing side has normal
coordinate D from (3), so \(|Q|\ge D>9/10\). Hence

\[
 (1-h)^2=|Q|^2-s^2
       >\frac{81}{100}-\frac{81}{400}
        =\frac{243}{400}>\frac9{16}.
\]

Therefore \(h<1/4\). By (7),

\[
                         \tan\psi>3\tan\phi.             \tag{21}
\]

Since \(\phi+\psi<\pi/2\), this implies
\(\tan^2\phi<1/3\), so

\[
                   0<a<\frac12,
                   b>\frac{\sqrt3}{2}>\frac56.          \tag{22}
\]

For fixed \(\phi\), cosine decreases with \(\psi\) in this
range. Equation (21) therefore gives

\[
 L\le\cos\bigl(\phi+\arctan(3\tan\phi)\bigr)
   =\frac{1-4a^2}{\sqrt{1+8a^2}}
   \le1-4a^2.                                           \tag{23}
\]

Using \(r<1\), (12), and (19),

\[
\begin{aligned}
 (z_B)_y
 &<\frac14+a+b(1-b+L)\\
 &\le\frac14+a+2b-b^2-4a^2b\\
 &\le\frac54+a-\frac{10}{3}a^2
 \le\frac54+\frac3{40}=\frac{53}{40}.
\end{aligned}                                                     \tag{24}
\]

For the penultimate line, use \(b^2=1-a^2\),
\(2b\le2-a^2\), and \(b>5/6\). The final bound is the exact
quadratic maximum \(a-(10/3)a^2\le3/40\).
Also \(|(z_B)_x|=s+b-aU\le s+1\). Consequently

\[
 R^2=|z_B|^2
   <(s+1)^2+\left(\frac{53}{40}\right)^2
   <(s+1)^2+\frac95,
\]

contradicting (20). This disposes of the entire two-circle-corner C
case, not merely an equal-weight or symmetric subcase.

## 5. If C has one circle corner, torque forces an acute frame sum

Suppose now that C has the unique physical circle corner (16). Its
circle-load vector is a positive multiple of \(z_C\). The A-contact
normal line is \(Q+\mathbb R m\); the BC-contact normal line is
\(T+\mathbb R v\). By (6) and (10), their intersection is exactly

\[
                           q_C=Q+\frac{rK}{L}m.           \tag{25}
\]

Taking torque about that intersection shows
\(q_C=\tau z_C\) for a real scalar \(\tau\). Its
m-coordinate is positive, since \(Q\cdot m>0\),
\(r,K,L>0\); hence \(\tau>0\). Its k-coordinate is
\(Q\cdot k\), whereas
\(z_C\cdot k=Q\cdot k+1-r>Q\cdot k\), and the former
circle coordinate is positive. Thus

\[
                               0<\tau<1.                 \tag{26}
\]

The line through T in direction v has constant n-coordinate, so
\(q_C\cdot n=T\cdot n=P\cdot n+j>0\). Therefore
\(z_C\cdot n>0\). Finally (16), (6), and (26) give

\[
 L-K=(z_C-T)\cdot n
      =(1-\tau)(z_C\cdot n)>0.                          \tag{27}
\]

Consequently

\[
                   0<K<L,
             \qquad0<\phi+\psi<\frac\pi4.               \tag{28}
\]

This conclusion uses the full loaded-body torque equation. It was not
assumed as an orientation normalization.

## 6. Exclude all heights when C has one circle corner

### 6.1. The upper contact has height at least one half

If \(h\ge1/2\), (7) implies \(\phi\ge\psi\), and (28)
gives \(\psi<\pi/8\). From (13),

\[
\begin{aligned}
 |(z_C)_y|
 &=1-h+c+d(1-r)\\
 &\le1+c+d-2h\le c+d.
\end{aligned}                                                     \tag{29}
\]

Also \(|(z_C)_x|\le s+d\le s+1\). Since

\[
                 (c+d)^2=1+\sin2\psi
                      \le1+\frac1{\sqrt2}<\frac95,
\]

equations (29) and (20) contradict \(|z_C|=R\).

### 6.2. The upper contact has height at most one half

If \(h\le1/2\), then \(\phi\le\psi\), so
\(\phi<\pi/8\). Put

\[
                              r_0=\frac{1-h}{d}>0.         \tag{30}
\]

We use the explicit corner formulas at this auxiliary parameter even if
\(r_0>1\); no physical square at \(r_0\) is assumed.

First suppose \(r\le r_0\). Since \(L>0\) and
\(Z_B(r)\ge1/2\), (17) gives

\[
                           |z_B(r)|^2\le|z_B(r_0)|^2.     \tag{31}
\]

Write \(U_0=1-b+Lr_0\). The relations (5), (7), and (30) give

\[
 0<U_0\le1-b+\frac Ld=1-\frac{ac}{d}<1.                 \tag{32}
\]

Since \(b>a\), this shows \((z_B(r_0))_x<0\) and
\(|(z_B(r_0))_x|\le s+1\). Direct substitution, or the fact that
\(T(r_0)\) has height zero, gives

\[
 (z_B(r_0))_y
     =a+b+a\left(a-\frac{bc}{d}\right)
     \le a+b.                                            \tag{33}
\]

The inequality uses \(ad\le bc\), equivalent to \(h\le1/2\).
The height is positive by its original expression
\(h+a+bU_0\). Since
\((a+b)^2\le1+1/\sqrt2<9/5\), equations (31)--(33) again
contradict (20).

It remains that \(r\ge r_0\). In this case
\(0<r_0\le r<1\). The decreasing C coordinate in (17) gives

\[
                            |z_C(r)|^2\le|z_C(r_0)|^2.    \tag{34}
\]

At the auxiliary parameter,

\[
 (z_C(r_0))_y=-(c+d),
 \qquad
 (z_C(r_0))_x=-s-d+c(1-r_0)<0,
                                                               \tag{35}
\]

where the last sign follows from \(\psi<\pi/4\), hence \(d>c\).
Its horizontal absolute value is at most \(s+d\). Therefore

\[
\begin{aligned}
 |z_C(r_0)|^2
 &\le(s+d)^2+(c+d)^2\\
 &=s^2+2sd+1+d^2+2cd\\
 &\le(s+1)^2+\frac53
  <(s+1)^2+\frac95.
\end{aligned}                                                     \tag{36}
\]

For the penultimate inequality use \(d\le1\) and

\[
 2cd\le\frac23d^2+\frac32c^2,
 \qquad
 d^2+2cd\le\frac53d^2+\frac32c^2\le\frac53.
\]

The first is a completed-square inequality. Equations (34)--(36)
contradict (20), completing every remaining height and orientation.

## 7. Complete selected nonparallel-branch conclusion

Every nonparallel D articulation has the opposite-left-corner form
(2). Finite pre-multiplier choices first remove its A vertex/vertex
contacts, then its BC vertex/vertex contact as in Section 1. Every
remaining BC contact has a side-axis owner. Sections 2--3 exhaust all
four signs of that owner's axes, derive the actual contact chart, and
identify genuine positive-weight circle corners. Section 4 excludes
every two-circle-corner C body. Sections 5--6 exclude every unique-corner
C body for the entire height interval \(0<h<1\). Reflection covers
the other choice of BC owner.

**Theorem 7.1.** The selected physical certificate can be chosen so that
no D-leaf triangle-plus-leaf component has nonparallel articulation
reactions. This excludes the whole nonparallel alternative; it does not
assert that arbitrary choices of vertex/vertex normals admit no such
positive stress core.

Only the parallel-left articulation alternative remains under this
selection. Its shared-side means and all its physical circle masks must
be handled separately before the parent D gate or C1.3.b1 is declared
closed. No completion square has been removed or approximated in this
core exclusion.
