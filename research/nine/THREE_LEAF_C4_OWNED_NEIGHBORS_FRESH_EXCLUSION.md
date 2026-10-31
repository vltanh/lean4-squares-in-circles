# Three genuine S leaves on C4: both outer neighbors own their middle contacts

Date: October 27, 2026.

**Status: complete fresh hand proof of the entire stated original interface,
saved for full independent and root review.** No unavailable earlier source
is used. The parallel-middle interfaces with a tilted outer neighbor are
not claimed here.

Keep the original nine-square packing and selected positive certificate,
with the actual component

    A--B--C--D--A,  A--L_A, B--L_B, C--L_C,
    A3, B3, C3, D2, L_A1, L_B1, L_C1.

The three leaves are genuine S leaves. All three root forces, both D
forces, the original circle load, every actual contact mean and every
physical circle mask remain. The other two physical squares remain
arbitrary and present. Work in the strict-high range

\[
 R^2=(d+1)^2+1/4\le Q_*:=1105/256,
 \qquad d=1+\varepsilon,
 \qquad 0<\varepsilon<1/60.
\tag{1}
\]

Each actual genuine root contains its real point of the closed epsilon
disk. The complete middle-root theorem
`GENUINE_S_THREE_FORCE_ROOT_TWO_NEAR_NEIGHBORS_FRESH_DOMAIN.md`
(`5dba416ea7bfd8500daf6f33bcecd56521dd7013f2357b9442964d2c49edb480`)
has full independent acceptance in
`REVIEW_GENUINE_S_THREE_FORCE_TWO_NEAR_FRESH_DOMAIN_HEXAGON_2026_10_27.md`
(`2595b9050f97e3af62ef950f1c214a9f2f94fc0de8f0c4c26356f61d1587d1e5`).
Its actual B3 reduction gives a parallel pair or two strict left B vertices.

**Theorem.** If A and C each own the actual normal of their contact with
B, the entire original interface is impossible. Consequently this closes
all of the nonparallel-middle case, and the parallel-middle case in which
both outer roots own the actual West normal. No A--C edge is assumed.

## 1. Complete common chart and angular bounds

Normalize the genuine B leaf to East. In the nonparallel case write

\[
 P_A=(\varepsilon,a),\quad n_{BA}=(-c,s),\qquad
 P_C=(\varepsilon,-b),\quad n_{BC}=(-\bar c,-\bar s),
\tag{2}
\]

where a,b,c,s,bar c,bar s are positive, a+b=1, and both normals are unit.
The full B3 moment and vertical force equations give

\[
 u=ac/s=b\bar c/\bar s>0.
\tag{3}
\]

The unchanged near-neighbor supports imply

\[
 \frac{a^2-\varepsilon u}{\sqrt{u^2+a^2}}\le\varepsilon,
 \qquad
 \frac{b^2-\varepsilon u}{\sqrt{u^2+b^2}}\le\varepsilon,
\]
and hence
\[
 a^2,b^2\le2\varepsilon u+\varepsilon^2.
\tag{4}
\]

If a numerator is nonpositive its corresponding inequality (4) is
immediate; otherwise squaring gives (4) without changing its direction.
With m=max(a,b)>=1/2, (4) gives

\[
 \frac a u,\frac b u
 \le\frac{2\varepsilon m}{m^2-\varepsilon^2}
 <\frac{60}{899}<\frac1{14}.
\tag{5}
\]

The function of m in (5) decreases for m>epsilon. Thus
s/c,bar s/bar c<1/14 and c,bar c>99/100. The exact squared reserve for
the latter assertion is 196/197-(99/100)^2=29203/1970000.

In the parallel case the same notation means c=bar c=1, s=bar s=0,
with a,b>0 and a+b<=1 the two original opposite-sign contact heights.
The strict signs and this full original interval are supplied by the
common theorem's Section 5, not by a choice of side midpoint.

Since A owns its contact axis, introduce its actual orthonormal axes

\[
 f=(-c,s),\qquad j=(-s,-c).
\]

Its actual rectangle and incoming point are

\[
 A:\quad f\in[H,U],\quad j\in[-T,1-T],\qquad
 U=1+H,
\tag{6}
\]
\[
 H=-\varepsilon c+as\in[-\varepsilon,\varepsilon],
 \qquad K=P_A\cdot j=-\varepsilon s-ac<0.
\tag{7}
\]

In (6), T>0 because K<0 belongs to its actual unit j interval.
The lower root has the reflected chart with

    f_C=(-bar c,-bar s), j_C=(-bar s,bar c),
    H_C=-epsilon*bar c+b*bar s,
    K_C=-epsilon*bar s-b*bar c<0.

All following statements reflect to C with these actual axes. The actual
AB force at A is -mu f, mu>0, at (H,K).

D has a nonzero actual circle load. Otherwise its true degree-two force
balance makes its two normals antiparallel. The actual A,C would then
lie beyond opposite parallel supporting lines of D, separated by its
directional width, which is at least one. Their two actual epsilon-disk
points have projected separation at most 2epsilon<1, a contradiction.
In particular D is physically boundary. No two-force equation is assigned
to either genuine root.

## 2. Every genuine outer leaf is vertical-near or far-left

We enumerate all four actual sides and four vertices in (6). A genuine
S application has norm d, and its radial direction is an actual support
normal at that unchanged point.

The -f owned side cannot supply height d, since H>=-epsilon. The +j
owned side would require 1-T=d and hence T<0. A strict upper-near
vertex (H,1-T) with positive j coordinate has squared norm less than
epsilon^2+1<d^2. These exclude the corresponding owned endpoints as
well. Every remaining possible genuine leaf is exactly one of:

* **Near-vertical:** the strict lower-near vertex (H,-T), with H<0 and
  T=sqrt(d^2-H^2)>1; or the owned -j side, with radial point (0,-d),
  T=d and H<=0.
* **Far-left:** the owned +f side, with H=epsilon and radial point (d,0);
  or a strict far-f vertex (U,V), where
  \[
  U=1+H>59/60,\quad 0<|V|<2\sqrt\varepsilon<13/50,
  \quad U^2+V^2=d^2.
  \tag{8}
  \]
  If V<0 its actual j interval is [V,V+1]; if V>0 it is [V-1,V].

An axis at a vertex is counted as an owned side with its original radial
application, so V=0 belongs to the owned +f case. This exhausts the actual
support-feature cover. The term near-vertical refers to the direction in
the original plane: at A, -j points almost North; at C it points almost
South.

## 3. A far-left owned leaf is impossible

For A this requires H=epsilon. It is absent in the parallel case because
then H=-epsilon. In the nonparallel case equality in the first support
bound gives a^2=2epsilon*u+epsilon^2. Equation (4) then gives a>=b,
so a>=1/2 and

\[
 K<-99/200.
\tag{9}
\]

The full A3 force equation has its real leaf along +f and its AB force
along -f. Its remaining AD force is therefore an axis force. It cannot
be +f: D would lie beyond support d, and the sharp contained-unit support
equality in `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 1, would
make D the very same physical radial S unit as L_A. These are distinct
actual squares. Thus AD is -f, with positive magnitude nu.

Its unchanged point has coordinates (epsilon,Y). Full origin torque is

\[
 \mu K+\nu Y=0,
\]

so Y>0. Apply only the force-free Section 1 of
`ADJACENT_S_LEAF_C4_PARALLEL_ROOT_LEAF_REDUCTION.md`
(`702eba704af93e67b85b9101a947ae5b3fe9134e194de64d87e5820e9fcc379b`)
in the rotated (-f,j) coordinates. D lies beyond coordinate -epsilon
and contains its actual point (-epsilon,Y). Since D is physically
boundary, that local theorem gives Y>4/5, with no D owner or mask premise.
But both K and Y belong to the same actual unit side of A, contradicting
Y-K>4/5+99/200>1. The original mean endpoints are included.

## 4. Two strict far-left leaves are physically incompatible

Each actual direction in (8) lies within

\[
 \arctan(1/14)+\arctan(78/295)
 =\arctan(1387/4052)<\arctan(12/35)
\tag{10}
\]

of West. The exact last cross-product reserve is
12*4052-35*1387=79. The two real radial S leaf centers have the same
radius d+1/2<91/60. If both roots had these leaves, their actual center
distance would be strictly less than

\[
 2\frac{91}{60}\sin\arctan(12/35)
 =2\frac{91}{60}\frac{12}{37}
 =\frac{182}{185}<1.
\tag{11}
\]

Their open inscribed half-unit disks would overlap. This is a physical
contradiction using the two real leaves; no circle-order or boundary-path
statement is imported.

## 5. A strict far-left leaf cannot coexist with the other vertical-near root

Assume A has (8), while C is near-vertical. Put eta_C=T_C-1. Then

    -epsilon<=H_C<=0,  1-epsilon<=U_C<=1,
    0<eta_C<=epsilon,  1<T_C<=d.

The actual C rectangle gives the world-coordinate bounds

\[
 \max_C y\le\varepsilon\bar s,
 \qquad \max_C x\le\varepsilon\bar c+d\bar s.
\]

Consequently, in the actual A direction -j=(s,c),

\[
 h_C(-j)<\varepsilon(s+\bar s)+d s\bar s
 <\frac1{420}+\frac{61}{11760}
 =\frac{89}{11760}<\frac1{100}.
\tag{12}
\]

Every C point also has norm at most epsilon+sqrt(2)<3/2, because C
contains its actual epsilon-disk point and has diameter sqrt(2).

The fixed point q=(-1/2,-1/10) is in the open interior of C. Indeed

    q.f_C=bar c/2+bar s/10 lies strictly between H_C and U_C,
    q.j_C=bar s/2-bar c/10 lies strictly between -T_C and -eta_C.

For the upper endpoint of the second interval, use
1/28-99/1000<-1/60<=-eta_C; all other inequalities follow directly
from c,bar c>99/100 and s,bar s<1/14. At A, q.f=c/2-s/10 lies
strictly inside [H,U], while

\[
 99/1000<q\cdot j=s/2+c/10<19/140<1/7.
\tag{13}
\]

If V<0, q also lies strictly inside [V,V+1], so A overlaps C.
If V>0, q lies above V-1; physical nonoverlap therefore forces

\[
 0<V\le q\cdot j<1/7.
\tag{14}
\]

The actual A corner (U,V-1), expressed in the orthonormal (f,-j) frame,
has coordinates (U,1-V). A occupies its Southwest unit quadrant. Any
other unit containing this corner without overlapping A contains a full
unit segment in a closed Northeast direction. This is the actual
vertex/side-interior tangent-sector argument of Section 1 of
`SHORT_ARM_THREE_FORCE_TRIANGLE_PARENT_NEAR_ROOT_FRESH_EXCLUSION.md`;
its geometric argument gives the general lower bound

\[
 |Z|^2\ge U^2+(1-V)^2+1+2\min(U,1-V).
\]

Here U>59/60 and 1-V>6/7, so the lower bound exceeds Q_* by

\[
 (59/60)^2+(6/7)^2+1+12/7-Q_*
 =280879/2822400>0.
\tag{15}
\]

Thus no actual D contact can occur at that corner. This use is purely
geometric and does not import the triangle hypothesis of the later
sections of that source.

Retain the full A3 equation. Let alpha>0 be its leaf magnitude and put
lambda=mu*d/alpha>0. The actual AD vector is a positive multiple of

\[
 (\lambda-U,-V)
\tag{16}
\]

in the f,j frame. Its second component is strictly negative. The complete
remaining support cover of (16) has only the forbidden far corner,
the owned -j side, or the near corner (H,V-1).

On the owned -j side, every D point has -j projection at least
1-V>6/7. Equation (12) makes actual C--D contact impossible, for every
original point of that side.

At the near corner, lambda<U. The full origin moment, including the
actual AB value K, is

\[
 \lambda(1-V+K)=U-V.
\tag{17}
\]

The denominator in (17) is positive. Comparing lambda<U in (17) gives
VH<UK<0, hence H<0. Write

\[
 r=\frac{U-\lambda}{V}
   =\frac{UK-VH}{V(1-V+K)}>0.
\]

The numerator is less than -VH<=epsilon V, while

\[
 1-V+K=\frac{U-V}{\lambda}>
 1-\frac VU>\frac{353}{413}.
\]

Thus

\[
 r<\frac{413}{21180}<\frac1{50}.
\tag{18}
\]

The actual AD direction is a positive multiple of -r f-j. Its support
at (H,V-1) is -rH+1-V>6/7. In contrast every actual C point has that
projection at most r|C|+h_C(-j)<3/100+1/100=1/25. Actual C--D contact
is again impossible. This exhausts (16), with every side endpoint.
Reflection treats a far-left C and a near-vertical A.

Sections 3--5 therefore leave both outer roots in the near-vertical
features, without an external equation or an altered force at either.

## 6. Both near-vertical roots give actual close D ports

For A, let its genuine point be (xi,-T), where xi=H for a strict leaf
and xi=0 for an owned leaf. Thus

\[
 -\varepsilon\le H\le\xi\le0,\qquad
 T=1+\eta,\quad 0<\eta\le\varepsilon,\qquad
 \xi^2+T^2=d^2.
\tag{19}
\]

With lambda=mu*d/alpha>0, the full AD vector has coordinates
(lambda-xi,T), both strictly positive. Its unchanged actual application
is consequently the unique far-upper A corner

\[
 Q_A=U f-\eta j.
\tag{20}
\]

Full origin torque gives

\[
 \lambda(-K-\eta)=UT-\eta\xi.
\tag{21}
\]

In particular -K-eta>0. Define the actual positive component ratio

\[
 r=\frac{T}{\lambda-\xi}
   =\frac{T(-K-\eta)}{UT+\xi K}
   \le\frac{-K-\eta}{U}
   <\frac{a+\varepsilon/14}{1-\varepsilon}.
\tag{22}
\]

Here xi*K>=0; no leaf moment or AB endpoint has been discarded.
Reflection gives Q_C and ratio bar r with the same bound using b.
Since a+b<=1,

\[
 r+\bar r<\frac{1+\varepsilon/7}{1-\varepsilon}
 <\frac{421}{413},\qquad
 r\bar r<(421/826)^2<1.
\tag{23}
\]

The actual **outward D** normals, up to their positive normalizations,
are

\[
 m_A=(c+rs,rc-s),\qquad
 m_C=(\bar c+\bar r\bar s,\bar s-\bar r\bar c).
\tag{24}
\]

They both have positive horizontal component. Put theta=atan(s/c),
bar theta=atan(bar s/bar c), alpha=atan r and bar alpha=atan bar r.
Their angles are alpha-theta and bar theta-bar alpha. Equation (23)
gives alpha+bar alpha<pi/2, while theta+bar theta<2atan(1/14)<pi/2.
Their angle difference is therefore strictly between -pi/2 and pi/2:
the two original D normals have positive scalar product.

The actual ports satisfy

\[
 \begin{split}
 Q_{A,x}&=-Uc+\eta s,
 &Q_{A,y}&=Us+\eta c>0,\\
 Q_{C,x}&=-U_C\bar c+\eta_C\bar s,
 &Q_{C,y}&=-U_C\bar s-\eta_C\bar c<0.
 \end{split}
\tag{25}
\]

Each x coordinate is at least -1 and is strictly less than -29/30,
since

\[
 (59/60)(99/100)-1/840-29/30=79/14000>0.
\]

Each absolute y coordinate is less than 1/14+1/60<1/10. Hence

\[
 |Q_A-Q_C|^2<(1/30)^2+(1/5)^2=37/900<1.
\tag{26}
\]

Moreover (24) supplies a direction n_0 in the closed cone generated
by the two actual normals, whose angle from East has absolute value less
than atan(1/14). Indeed if the normals straddle East use East; if both
are above it, use m_C, whose angle is less than bar theta; if both are
below it, use m_A, whose angle is greater than -theta. A zero angle is
included. This inference does not assert opposite strict y signs.

## 7. Distinct D normals force an actual corner beyond the circle

First suppose m_A and m_C are distinct unit directions. The complete
actual-feature cover of Section 1 of
`CLOSE_SUPPORT_PORTS_STRADDLING_NORMALS_FRESH_EXCLUSION.md`
applies with the following literal replacement: distinct normals exclude
the common-face case, while (23)--(26) exclude two vertices, two adjacent
side interiors, opposite faces, and a nonincident vertex/side pair.
Thus both actual normals belong to the outward cone of one actual vertex
Z among Q_A,Q_C. The original port bounds therefore hold at Z. No
force-line intersection or concurrence is used.

Let v_1,v_2 be the two orthonormal inward side vectors at Z, and S=v_1+v_2.
Since the actual cone contains n_0, each v_i.n_0<=0. Hence

    S.n_0<=-1,     |S.Jn_0|<=1,     |S|=sqrt(2).

Write delta for the angle of n_0 from East. The bounds
cos(delta)>99/100 and |sin(delta)|<1/14 give

\[
 S_x<-99/100+1/14=-643/700,
 \qquad |S_y|\le\sqrt2<3/2.
\tag{27}
\]

The actual opposite corner Z+S has squared norm strictly greater than

\[
 (29/30)^2+2+2(29/30)(643/700)-3/10
 =Q_*+189389/2016000>R^2.
\tag{28}
\]

This contradicts physical containment. This slightly wider cone estimate
was derived here; no strengthened conclusion is attributed to the frozen
straddling theorem. Its proof uses the stronger actual |Z_y|<1/10 bound.

## 8. Equal D normals contradict the complete D load

If the two actual normals agree, their two distinct ports (25) lie on
one actual D face. Thus D owns that common normal m. Its full true D2
force equation makes its nonzero circle resultant a positive multiple
of e=-m. We justify the resulting physical frame without prescribing a
circle mask or its weights.

Use e and a perpendicular own axis as D coordinates. If D's center had
nonzero transverse coordinate, every physically farthest vertex would
have the same strict transverse sign; any nonzero positive combination
of its actual circle vectors would have that sign. The transverse
component of the genuine circle resultant is zero. Therefore the center
has transverse coordinate zero. Its longitudinal coordinate is positive,
since the circle resultant is a positive multiple of e; a negative
coordinate would give the opposite sign at all farthest vertices. Both
coordinates zero would put its corners at radius sqrt(1/2), outside the
present radius domain.

It follows that D's two physical circle corners are on its far e face,
at transverse coordinates +/-1/2. If h is its near e face, actual radius
equality gives

    (h+1)^2+1/4=R^2,   h+1>0,   hence h=d.

This also forces equal nonzero circle weights, though that conclusion is
not needed. The unchanged two original ports on that near face must each
have norm at least d. But (19)--(20) give

\[
 |Q_A|^2=U^2+\eta^2\le1+\varepsilon^2<d^2,
\]

a contradiction. This is the full two-contact D equation with its actual
load, not a substituted leaf equation.

## 9. Exact original join and remaining interfaces

The complete common middle-B3 theorem makes both outer endpoints actual
axis owners throughout the nonparallel case, so Sections 1--8 exclude
that whole case. They also exclude every parallel-middle configuration
where both A and C own the original West contact axis, retaining both
entire original mean intervals and their positive opposite signs.

Only parallel B with at least one outer root not owning that axis lies
outside this source. No conclusion is asserted for that remaining
interface here. Every use of an outer force equation was the full A3 or
C3 equation; none is exported to a degree-four diamond hub. The physical
near-East vertex-cone argument of Section 7 is degree-free at its stated
port and normal bounds.

All statements preserve the original nine squares, original positive
graph, actual forces, means, masks and selected directions. No normal is
reselected after extraction, no physical contact is added, and no numeric
pose, sampling, computational certificate or external-moment deletion is
a premise.
