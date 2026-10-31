# The tilted S-leaf three-load C5 channel cannot have a unique far circle corner

Date: October 27, 2026.

**Status: complete original-domain mask exclusion, submitted for root
and separate independent review.** This closes the entire physical
unique-corner C alternative in
S_LEAF_C5_THREE_LOAD_TILTED_CHANNEL_DOMAIN.md. The physical radial-C
mask and the aligned high root remain outside this source.

## 1. Original component, actual coordinates, and the narrow mask

Keep precisely the original positive component

    A--B--M--C--U--A, A--L,

with the same nine physical units. B,M,C have their positive total
circle loads and true degree two; U is the true unloaded degree-two
side transmitter; A keeps its full degree three, including its genuine
S leaf L. No force at M is deleted. Every actual normal, side mean,
physical mask, zero individual circle weight, and additional physical
contact remains.

Use the complete accepted necessary-domain source
S_LEAF_C5_THREE_LOAD_TILTED_CHANNEL_DOMAIN.md, SHA
8cadc80c6de3a86c44f120f4a309a50af7361aec072341cb27297e47401943f2,
and its full independent review
REVIEW_S123_FAR_SUPPORT_AND_TILTED_CHANNEL_HEXAGON_2026_10_27.md.
Its notation gives

    0<epsilon=d-1<1/60,   d=sqrt(R^2-1/4)-1,
    A=p0+[0,1]f1+[0,1]f2, p0=(d,0),
    f1=(-a,-b), f2=(-b,a), a>b>0, a^2+b^2=1,
    n=x f1-t f2, x>0,t>=0,x^2+t^2=1,
    f=t f1+x f2,
    q_A=(q,0), 0<q<=d, k=d-q>=0.

All coordinates below are actual orthonormal projections; the
orientation reversal of f1,f2 has no effect on distances or supports.
Put

    U0=da, V0=db, A0=1-U0, F0=1-V0.

The direct actual A--B point and root normal m satisfy

    P_B=(Z-U0,F0) in the f1,f2 frame,
    0<=Z<=1,
    P_B-q_A is a positive multiple of m,
    P_B-q_A has own components (Z-ka,1-kb).             (1)

Thus Z=0 for m_1<0, Z=1 for m_1>0, and the entire original
side mean survives when m_1=0.

Assume for contradiction that C has exactly one physical circle
corner. Its original channel axis is genuinely C-owned. In the
n,f frame its entire actual box and the actual U mean are

    C=[X,X+1] times [-D0,1-D0],
    X=1+h, -epsilon<=h<=epsilon,
    p_CU=(X,-T),
    59/238<T<13/50,
    D0=sqrt(R^2-(X+1)^2)>1/2,
    q_C=(T(X+1)/D0,-T) in C.                           (2)

The proper incoming length is nonnegative. The necessary-domain
source already proves

    1/66<epsilon<1/60.                                 (3)

In particular R^2>43/10: at epsilon=1/66 its squared-radius excess
over 43/10 is 59/5445.

The physical radial C mask, including a zero individual corner
weight, is not included in this assumption.

## 2. The original root concurrence is close to its real leaf point

The actual channel point has transverse component -T, and its
norm is at most the norm of the actual root vertex with projections
(A0,-V0). Therefore

    T^2<=A0^2+V0^2=d^2-1+2A0.

Using T>59/238 and d<61/60 gives

    A0>1/72,                                           (4)

since the exact reserve after subtracting 1/72 is
3319/101959200. In particular A0>0. The channel equations now imply

    59/238<V0<13/50,
    37/50<F0<179/238<113/150,
    1/72<A0<1/60.                                     (5)

Indeed for t>0, T=V0*x-A0*t<=V0; for t=0, T=V0-Y<=V0.
The upper V0 bound follows from V0^2<=4epsilon<1/15.
The last displayed comparison in the F0 interval has reserve11/8925.

For t>0, the unchanged support is

    h=A0*x+V0*t<=epsilon.

First t<119/1770 and hence x>99/100. Then (4) sharpens it to

    t<833/70800<1/80,
    k=t/(b*x+a*t)<1/20.                               (6)

For the last comparison use
b> (59/238)(60/61); the exact reserve between 1/20 and the
resulting upper bound is 31279/24812568.

For t=0, the original mean gives k=d(1-T/V0), so

    k<(61/60)(1-(59/238)/(13/50))
      =366/7735<1/20,                                 (7)

with reserve83/30940. Thus both actual mean cases satisfy

    0<=k<1/20, q>19/20.                                (8)

No root mean has been chosen to obtain (8).

## 3. Every actual C-to-M contact lies in one small rectangle

Properness in (2) gives

    D0<=T(X+1)/X<1573/2950<8/15,                       (9)
    rho_C:=T(X+1)/D0-X in [0,49/750),
    ell_C:=1-D0+T>3/5.

The first final reserve is 1/8850. The upper bound on rho_C
uses X>59/60 and T(X+1)/D0<1573/1500<21/20.

Let g be the original unit normal from C toward M and Q its
original actual application. The full true C2 force equation
makes g_f>0, because its circle force has negative f component
and the U force has zero f component.

If g_n>0, its actual point is the far upper corner
Q=(X+1,1-D0). Properness makes its direction proportional to

    (1-rho_C,ell_C).

Here 1-rho_C>701/750>19/25>ell_C. Hence g_n>1/sqrt(2), and

    h_C(g)>(X+1)/sqrt(2)>119/(60 sqrt(2))>5/4>d.

This is impossible for a contained neighboring unit: its minimum
support cannot exceed d, by the sharp center/half-width bound.

If g_n<0, its actual point is the inner upper corner and

    Q=(X,1-D0),
    g=(-rho_C,ell_C)/sqrt(rho_C^2+ell_C^2).

In particular -g_n/g_f<49/450<1/9. If g_n=0, the actual
owned upper-face mean is

    Q=(T(X+1)/D0,1-D0), g=f.

These alternatives exhaust every actual C feature and every
side-mean endpoint. Consequently, in the actual n,f frame,

    59/60<Q_n<21/20,
    7/15<Q_f<1/2,
    g=(-alpha,beta), alpha>=0,beta>0,
    alpha/beta<1/9.                                   (10)

## 4. A full loaded-neighbor lemma at the rectangle (10)

We prove that the actual M satisfies

    every point of M has n coordinate >1/15.           (11)

The only force facts used here are the original true M2 proper
radial concurrence, and its boundedness inside M when M has a
unique physical circle corner. These hold because M has the
actual physical boundary neighbors B,C. They are the full local
facts used in Section2 of
D_LEAF_C5_THREE_CONSECUTIVE_LOADS_EXCLUSION.md.

### 4.1. The whole physical two-corner mask

Suppose M is radial. If M owns its incoming normal g, its possible
minimum supports in an own-axis direction are d, -(d+1), and -1/2.
But (10) gives

    1/3<Q.g<1/2,

so none is possible.

Otherwise Q is a strict M vertex. It is not an unshareable circle
vertex, hence it is an inner vertex d e +/- (1/2)Je of the actual
radial M. Write e=(e_n,e_f). The bound Q_n>59/60 first gives
e_n>0, since e_n<=0 would give Q_n<=1/2.

If Q=d e+(1/2)Je and e_f>=0, then min_M n=Q_n.
If this same vertex has e_f<0, Q_f>7/15 gives
e_f>-1/(30d)>-1/30, and

    min_M n=Q_n+e_f>19/20.

If Q=d e-(1/2)Je, then Q_f>0 forces e_f>0. Also e_f<4/5:
otherwise e_n<=3/5 and
Q_f=d e_f-e_n/2>4/5-3/10=1/2.
Therefore

    min_M n=Q_n-e_f>11/60.

All these lower bounds are greater than 1/15. This uses no
inside-unit concurrence for a radial M and retains both original
corner weights, including zero endpoints.

### 4.2. Unique M owning g

Let j=(beta,alpha), H=Q.g and K=Q.j. Then

    1/3<H<1/2, K>0.

Since H>0, M's physical circle corner is on its far g face.
Its positive original radial concurrence has j coordinate K>0,
so that corner is on the positive j side. The whole box is

    M=[H,H+1]g+[W-1,W]j,
    W=sqrt(R^2-(H+1)^2)>7/5.

The last inequality follows from R^2>43/10 and H+1<3/2.
Consequently every point of M has n coordinate at least

    -alpha(H+1)+beta(W-1)
      >beta(2/5-1/6)=7beta/30>1/15.

All original incoming and outgoing means remain arbitrary.

### 4.3. Unique M not owning g

Now Q is a strict minimum-g vertex of M. Let its inward unit
axes be u,v. Suppose contrary to (11) that min_M n<=1/15.

If both inward axes have nonpositive n components, orthogonality
makes their f components of opposite signs. Every vertex then lies
in the rectangle

    -31/60<n<21/20,  -8/15<f<3/2.

Its squared norm is at most 1341/400<43/10, so M would be
circle-clear. If both n components are nonnegative, its minimum n
coordinate is Q_n>59/60, also impossible.

Thus one inward n component is positive and the other negative.
Write the latter axis as v=(-c,s), c>0. The strict inequalities
g.u>0,g.v>0 force the other axis to be u=(s,c), with s>0:
the alternative (-s,-c), s<0, would have negative g scalar product.
The assumed minimum gives

    c>=Q_n-1/15>11/12,
    0<s<2/5.                                         (12)

The squared comparison in the second inequality has reserve1/3600.

The original unique-corner concurrence q_M belongs to M and is on
Q+[0,infinity)g. Hence |q_M-Q|<=sqrt(2), and

    (q_M)_n>59/60-sqrt(2)/9>49/60.

Its unique circle corner Z_M is on the same positive ray, with
q_M a scalar multiple between zero and one. Thus
(Z_M)_n>49/60. This excludes Q+v and Q+u+v as the circle corner:
their n coordinates are at most 1/15 and less than7/15,
respectively. Q itself is a shared point and cannot be on the circle.

The only remaining corner is Q+u. Equations (10),(12) give

    |Q+u|^2
      <(21/20)^2+(1/2)^2+1
          +2[(21/20)(2/5)+(1/2)]
      =1677/400<43/10<R^2.

The exact reserve is43/400. This final contradiction proves (11)
in every actual M feature and physical mask.

## 5. The entire nonpositive first component at the direct root is impossible

Suppose the original direct m has m_1<=0 in the f1,f2 frame.
The exact root features in (1) give Z=0 or Z=ka<1/20.
Therefore

    (P_B)_1<-14/15,
    (P_B)_2=F0>37/50,
    m=(-p,s), p>=0,s>0, p/s<1/19.                      (13)

The ratio follows from
p/s<=ka/(1-kb), k<1/20 and b<13/50.

The actual supporting unit B satisfies, purely geometrically,

    every B point has f1 coordinate <1/15,
    every B point has f2 coordinate >0.               (14)

Here are the full owner cases. If B owns m, write a point of B
relative to the original mean P_B as r m+z(s,p), where
0<=r<=1 and -1<=z<=1. Its first coordinate is at most
(P_B)_1+s<(P_B)_1+1<1/15, and its second is at least
F0-p>F0-1/19>0.

If B does not own m, P_B is its strict minimum-m vertex.
At most one inward axis has positive first component, and its
first component is at most one. Indeed two positive first
components would put one orthogonal axis in the lower-right
quadrant, with negative scalar product with m. Thus the same
first-coordinate bound holds. Any inward axis with negative
second component must have absolute second component below p/s;
there is at most one such axis. This gives the same strict
positive lower bound F0-1/19 for the second coordinate.

Since n=x f1-t f2, x<=1,t>=0, (14) implies

    every B point has n coordinate <1/15.

This contradicts the whole-M lower bound (11), because B and M
have an actual physical contact. No B equation or B physical mask
was specialized in (14).

## 6. The only other direct root feature is its opposite vertex

We are left with m_1>0. The actual root port is now

    P_B=(A0,F0),

and the positive proper direction is

    m=(r,s)/sqrt(r^2+s^2),
    r=1-ka, s=1-kb,
    19/20<r<=s<=1.                                    (15)

Its norm is less than4/5 by (5). Every point of a physical radial
unit has norm at least d>1. Thus B is physically unique, and its
proper concurrence belongs to B.

We separate its complete actual owner alternatives.

### 6.1. A strict B vertex makes the boundary path too short

If B does not own m, P_B is a strict B vertex. Its unique circle
corner Z_B must be opposite that vertex: a circle vertex at an
adjacent vertex would have distance one from P_B, whereas
R-|P_B|>1. Both coordinates of Z_B are positive, since
q_B=P_B+rho_B m is on its positive radial ray.

Use |Z_B-P_B|^2=2. Since A0(Z_B)_1>0,

    (Z_B)_2
      < F0/2 + [R^2+A0^2-2]/(2F0)
      <97/50.                                        (16)

For the second inequality, the expression on the right decreases
with F0 over (5), so use F0=37/50, R^2=1105/256 and
A0=1/60. The remaining exact reserve is9959/2131200.
Since R^2>43/10 and (Z_B)_1>0, (16) then gives

    (Z_B)_1>73/100,

with squared reserve7/2000. The actual B center is
(P_B+Z_B)/2, so its f1,f2 center angle lies in

    0<theta_B<arctan(4).                               (17)

For example its second coordinate is below27/20 and its first
above73/200, whose ratio is below4.

In the same actual frame, the C center is

    (X+1/2)n+(1/2-D0)f.

Its angle is strictly between -1/25 and zero. Indeed (6) gives
atan(t/x)<1/75, while (9) gives

    (D0-1/2)/(X+1/2)<2/89,
    1/75+2/89<1/25.                                   (18)

This also retains t=0. Thus the actual minor center gap from
C to B is less than arctan(4)+1/25<4pi/9.
For the last exact angular comparison use

    arctan(1/4)>=1/4-(1/4)^3/3=47/192
       > pi/18+1/25,

where pi<22/7 leaves reserve3043/100800.

But B--M--C is an actual three-body boundary path. Each actual
boundary contact is consecutive in the physical circular order;
each gap is greater than2pi/9, and the two-gap span is less than
pi. Its endpoint minor center gap is therefore greater than4pi/9.
This is the same complete path consequence used in Section2 of
FAR_SUPPORT_THREE_BOUNDARY_PATH_EXCLUSION.md. It contradicts
(17)--(18), with the full middle unit M retained.

### 6.2. Every actual B-owned mean forces a forbidden M contact

Suppose B owns m. Put j=(-m_2,m_1) and

    H=P_B.m, z=P_B.j.

Equations (5),(15) give the uniform strict bounds

    1/2<H<3/5, 0<z<8/15.                              (19)

For clarity m_1>17/25, m_1<=1/sqrt(2), and
1/sqrt(2)<=m_2<11/15. These bounds prove both sides of (19);
the squared reserve for
(179/238)/sqrt(2)<8/15 is41207/25489800.

Since H>0, the unique circle corner is on the far m face.
Its original positive radial concurrence has j coordinate z>0.
Therefore the full B box, circle corner, and concurrence are

    B=[H,H+1]m+[W-1,W]j,
    Z_B=(H+1)m+Wj,
    W=sqrt(R^2-(H+1)^2),
    q_B=Q_m m+zj,
    Q_m=z(H+1)/W.

In particular

    13/10<W<29/20,
    Q_m<128/195,
    0<=rho_B:=Q_m-H<61/390.                           (20)

The upper W bound follows even from W<23/16, since
1105/256-(3/2)^2=529/256. Every original incoming mean is
retained in these equations.

Let k_B be the actual outward B-to-M normal. The full B2 force
equation has strictly negative j component at k_B, because its
circle resultant has positive j component and the A force is
parallel to m. Thus only the following features are possible.

If (k_B)_m<0, its actual point is (H,W-1).
If (k_B)_m=0, its actual lower-side mean is (Q_m,W-1).
In either case that actual point has norm less than4/5:
the larger uniform square bound is

    (128/195)^2+(9/20)^2<16/25,

with reserve4031/608400. But an actual contact between the two
physical boundary units B,M has norm strictly greater than4/5
by BOUNDARY_PAIR_CONTACT_SHARP_INNER_RADIUS.md at d>1.
This full force-free theorem, independently accepted in
REVIEW_SHARP_BOUNDARY_PAIR_CONTACT_RADIUS_TRIANGLE_BRIDGES_2026_10_27.md,
retains every side mean and endpoint.

Finally, if (k_B)_m>0, its actual point is the far lower corner
(H+1,W-1). Its proper direction is proportional to

    (1-rho_B,-eta), eta=z-W+1>0.

Equations (19)--(20) imply

    eta<7/30,
    1-rho_B>329/390,
    eta/(1-rho_B)<91/329<2/7.

The support of B in this actual direction is consequently greater
than

    [3/2-(2/7)(9/20)]/sqrt(1+(2/7)^2)
       =48/(5sqrt(53))>5/4>d.

No contained M can lie beyond this support. The strict final
comparison follows from192^2>25^2*53. This exhausts the actual
B-owned lower face and both of its vertices.

## 7. Exact conclusion and retained obligation

Section5 excludes the whole m_1<=0 direct feature with every
actual mean. Section6 excludes both owner classes in the only
remaining m_1>0 feature. These alternatives are exhaustive for
the complete tilted original S123 root domain.

Hence the far endpoint C cannot have one physical circle corner.
It must retain the full physical radial mask from the accepted
necessary-domain source:

    C=[d,d+1]n+[-1/2,1/2]f,
    h_A(n)=epsilon,
    p_CU=d n-T f, 0<T<13/50.

No individual radial weight is fixed or discarded. The entire
radial-C completion and the aligned high root still need their
whole exits before M6.B5L.C5.L123.S can be declared closed.

The proof uses the true original degrees throughout. In particular
M remains a positively loaded degree-two boundary body in the
proper-neighbor lemma, the angular path, the contact-radius
contradiction and the final support contradiction. No new finite
pose sample, numerical premise, normal reselection, shared metadata
edit, remote action, compilation or CI is used.

