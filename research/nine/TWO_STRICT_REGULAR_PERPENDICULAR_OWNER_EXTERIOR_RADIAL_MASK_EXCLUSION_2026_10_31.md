# The regular perpendicular owner-side exterior endpoint has one physical circle corner

Date: October 31, 2026 UTC. Author: regular-perpendicular continuation.

**Status: complete hand feature exclusion, submitted for separate review.**
In the full regular two-strict, both-hub-owned roof chart, the exterior
endpoint on the AD-owning hub's side cannot have two physical circle
corners. This excludes its entire physical radial mask simultaneously,
including either individual zero circle coefficient. It uses the full
original A3, D3 and V2 equations, but no force equation at B, C or N.
Consequently it applies with loaded or unloaded N and with arbitrary
true degrees at the exterior endpoints, under the inherited physical
owner conclusions. It does not close the whole regular side feature.

The main geometric lemma is independent of a radius window or force
equations. A short bound from the unchanged V torque excludes the other
possible radial own-axis choice before that lemma is applied.

## 1. Entire original regular chart and retained equations

Retain the same actual contained unit squares, all original contacts,
positive forces, application points, physical circle corners and
individual nonnegative circle coefficients. Work in the original window

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1.

The complete original V2 has two physical circle corners and its actual
radial position is

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-1/2).

The two strict V applications are P and Q. Both roofs are genuinely
owned by their unloaded true3 hubs A and D. Keep their actual axes

    h=(c,-s), e=(s,c), k=(C,S), v=(-S,C),
    c,s,C,S>0, c^2+s^2=C^2+S^2=1,
    c=cos(alpha), s=sin(alpha),
    C=cos(beta), S=sin(beta).

Here the unchanged AD singleton is A-owned, with normal -e. The full
original regular reduction gives

    H=s*C+c*S, J=c*C-s*S, F=J-H,
    0<alpha+beta<pi/4, 0<H<J, F>0,
    0<rho<1,
    x=1+s-H*rho in (0,1),
    y=1-c+J*rho in (0,1),
    m=x/y>0, n=F/(1-rho)>0.                         (1)

In particular y>J*rho. The original exterior applications and unit
directions are

    K=P-h+y*e,
    L=Q-k+(rho-1)*v,
    p=sqrt(m^2+1), q=sqrt((n+H)^2+J^2),
    b=(-m*h+e)/p,
    a=((n+H)*k+J*v)/q=(n*k+e)/q,
    w=Jrot(b), z=Jrot(a).                           (2)

The inherited three-distinct-singleton owner conclusion makes K a
genuine relative-interior point of B's minimum-b side and L a genuine
relative-interior point of C's maximum-a side. It follows from the
actual hub supports and the already selected certificate; it is not a
new normal selection. Thus (b,w) and (a,z) are actual own frames of B
and C, respectively. The original means have not been moved.

The complete unchanged V torque, after dividing all original pair
magnitudes by the same positive AD magnitude, is

    m*(d*s+c/2)=n*(d*S+C/2).                        (3)

Both individual V circle coefficients remain in their original closed
nonnegative interval. Equation (3) does not require them to be equal.
No B/C/N term is used or deleted here. All other actual units remain.

The main theorem is:

**Theorem 1.1.** Under this complete chart, a physically boundary B
has exactly one physical circle corner. In particular the actual loaded
B of either original D02.L135 or D02.L1345 cannot have two physical
circle corners. Any physical two-corner C, if present, is radial along
its exterior incoming axis -a; no transverse radial frame survives.

For the reflected chart in which D owns the perpendicular AD normal,
the same conclusion holds with the entire data A,D and B,C exchanged.

## 2. A geometric radial-port obstruction

The following lemma needs no circle equation, force, other neighbor or
radius bound.

**Lemma 2.1.** Let d be any real number. Let

    P=(d,1/2),
    h=(cos(alpha),-sin(alpha)), e=Jrot(h),
    0<=alpha<pi/2,
    m>0, 0<y<1, x=m*y,
    x+y>=1,
    p=sqrt(m^2+1), b=(-m*h+e)/p, w=Jrot(b),
    K=P-h+y*e.

If K.b=d, then K.w<-1/2. Consequently K cannot belong to the
minimum-b side of the radial square

    [d,d+1]*b+[-1/2,1/2]*w.                         (4)

The conclusion excludes even the two endpoints of that side.

*Proof.* Put

    gamma=arctan(m)-alpha.

Then -pi/2<gamma<pi/2 and the actual vectors are

    b=(-sin(gamma),cos(gamma)),
    w=(-cos(gamma),-sin(gamma)).

In particular cos(gamma)>0 and 1+sin(gamma)>0. Taking the two
unchanged projections of K gives

    K.b=-d*sin(gamma)+cos(gamma)/2+(m+y)/p,
    -K.w=d*cos(gamma)+sin(gamma)/2-(1-x)/p.

The assumed first equality K.b=d eliminates d without a sign
ambiguity. Substitution into the second identity yields exactly

    -K.w=1/2+[(m+y)*t_gamma-(1-x)]/p,
    t_gamma=cos(gamma)/(1+sin(gamma))
           =tan(pi/4-gamma/2).                    (5)

Since gamma<=arctan(m), monotonicity of the last tangent on its
actual interval gives

    t_gamma>=tan(pi/4-arctan(m)/2)=p-m>0.

The bracket in (5) consequently obeys

    (m+y)*t_gamma-(1-x)
       >=(m+y)*(p-m)-1+m*y
        =p*(m+y-p).                               (6)

All terms are actual scalar expressions, and the equality in (6)
uses p^2=m^2+1. Finally

    (m+y)^2-p^2=2*m*y+y^2-1=2*x+y^2-1
       >=(1-y)^2>0,

where x+y>=1 and y<1 give the last two steps. Since m+y and p
are positive, m+y>p. Thus the bracket in (5) is strictly positive.
This proves -K.w>1/2 and the claim. QED.

## 3. Both actual exterior supports are strictly outward

The following estimates use the entire original V torque (3). They
do not rely on a boundary mask or force equation at B or C.

First the original radius interval gives

    9/10<d<61/60.                                  (7)

For the lower bound, d>9/10 is equivalent to
R^2-1/4>(19/10)^2, and the lower endpoint has the positive reserve
5841/1600-5776/1600=65/1600. For the upper bound, the comparison

    (121/60)^2-1041/256=31/57600>0

gives d<61/60 at the upper endpoint. Both comparisons are strict
even at the original closed endpoints.

Write only for this calculation

    B0=d*s+c/2, D0=d*S+C/2,
    A0=d*c-s/2, E0=d*C-S/2.

Because d>1/2 and all four trigonometric components are positive,

    B0>(c+s)/2>1/2,
    D0>(C+S)/2>1/2.

Cauchy and (7) give

    B0,D0 <=sqrt(d^2+1/4)<5/4.

Indeed d^2+1/4<4621/3600<25/16. Therefore both positive ratios
B0/D0 and D0/B0 are less than 5/2. Also J>1/sqrt(2)>2/3 and
0<F<1. Using x<1, y>J*rho and the complete torque (3),

    m*rho=x*rho/y<1/J<3/2,
    m*(1-rho)=F*D0/B0<5/2,
    m<4.                                           (8)

The same exact torque gives

    n*rho=m*rho*B0/D0<15/4,
    n*(1-rho)=F<1,
    n<19/4<5.                                      (9)

Since A0,E0<d<61/60, the original point K satisfies

    p*(K.b)=m*(1-A0)+B0+y
       >-m/60+1/2>13/30>0.                        (10)

In the actual (k,v) frame, L has coordinates
(E0-1,-D0-(1-rho)), so similarly

    q*(-L.a)
       =(n+H)*(1-E0)+J*(D0+1-rho)
       >-(n+H)/60+1/3
       >-6/60+1/3=7/30>0.                         (11)

Here H<1 and n<5 give the strict penultimate bound. Consequently

    K.b>0, L.a<0.                                  (12)

Every interval and force ratio in this calculation was retained.
These are elementary continuous inequalities, with no finite pose
sample or computed certificate.

## 4. The physical two-corner axes and the complete B exclusion

Consider any actual contained boundary square with own axes b,w.
If its center is r*b+t*w, its four squared corner radii maximize
the b and w coordinates independently. Two physical circle corners
are therefore adjacent and require exactly one of r,t to be zero.
If both vanish, all four corners have radius 1/sqrt(2), outside the
original window. This is a statement about the entire physical mask;
a zero individual coefficient at a physical corner does not change it.

For the actual B, K is on its minimum-b side. Equation (12) gives

    center(B).b=K.b+1/2>0.

Thus a two-corner B cannot have its radial direction transverse to b.
It would necessarily have center(B).w=0 and positive radial direction
b. Its actual far support is sqrt(R^2-1/4)=d+1, hence its whole
position would be exactly (4). In particular K.b=d and
-1/2<K.w<1/2, with the strict inequalities furnished by the original
genuine side-interior contact.

But the original regular variables give the strict identity and bound

    x+y=2+s-c+(J-H)*rho>1.                         (13)

Indeed c<1, s>0 and (J-H)*rho>0. All premises of Lemma 2.1 are
therefore supplied by the unchanged physical chart (1)--(2).
That lemma yields K.w<-1/2, contradicting even membership of K in
the proposed radial side. The entire two-physical-circle B mask is
excluded. Since B is physically on the circle and four physical
corners are impossible, it has exactly one physical circle corner.

For C, its actual center satisfies

    center(C).a=L.a-1/2<0.

The same complete corner classification shows that a physical
two-corner C can only have its radial direction -a, with entire
position

    C=[-d-1,-d]*a+[-1/2,1/2]*z.                  (14)

This proves Theorem 1.1. No C radial exclusion beyond this axis
identification has been presumed.

## 5. A closed additional C-radial exclusion

The same geometric lemma also excludes (14) throughout the whole
closed parameter range

    rho<=J/(J+H).                                  (15)

To see this, reflect the entire coordinate chart across the horizontal
axis. The unchanged points and vectors become

    Q -> P'=(d,1/2),
    k -> h'=(C,-S), v -> -e',
    L -> K'=P'-h'+y'*e',
    y'=1-rho,
    m'=(n+H)/J,
    -a -> b'=(-m'*h'+e')/sqrt((m')^2+1).

The reflected incoming axis b' is precisely the positive radial
direction of the hypothesized C in (14). Put x'=m'*y'. The full
original D torque in (1) gives exactly

    x'=[F+H*(1-rho)]/J=1-H*rho/J,
    0<x'<1,
    x'+y'=2-rho*(1+H/J).

Condition (15) is therefore x'+y'>=1. Lemma 2.1 applies in this
whole-data reflected frame, with alpha'=beta>0. It contradicts
membership of the same actual L in C's radial inner side.

Consequently any remaining physical two-corner C must satisfy the
strict original constraint

    rho>J/(J+H).                                   (16)

The equality in (15) is excluded by the strict final reserve
(1-y')^2>0 in Lemma 2.1. No original side endpoint or circle weight
was omitted at that equality.

## 6. Scope and literal consequences

The main B exclusion used the complete original hub and V equations,
the actual exterior owner interiors and the original radius window.
It imposed no equation at an exterior endpoint, no channel direction,
no status at N, and no condition on the three completing squares.
It therefore covers every original regular chart with these premises,
including both D02.L135 and D02.L1345 and higher exterior degrees
when the same actual owner conclusion is available.

For an A-owned perpendicular AD singleton, B is physically unique;
the reflected D-owned chart makes C physically unique. In either
orientation the entire both-radial exterior mask is impossible.
Within the stated A-owned orientation, a physical two-corner C can
remain only in (14) and the strict domain (16).

The separate complete diagonal-N exclusion remains unchanged. In
the unloaded side-N remainder, the original B2/C2/N2 equations and
all physical positions remain to be used. This source does not
assert closure of that whole side feature, the loaded-N feature,
either original D02 row or the nine-square theorem.

The direct original-chart input is
`TWO_STRICT_PERPENDICULAR_AD_REGULAR_ANGLE_TORQUE_REDUCTION_2026_10_30.md`.
The exterior owner premise is the already inherited conclusion of
`PHYSICAL_TWO_CORNER_TRIANGLE_TIP_FIVE_DISTINCT_APPLICATIONS_AND_HUB_SINGLETON_OWNER_COVER_2026_10_29.md`
at its unchanged common-selection scope. The physical-mask convention
and full force/torque convention are those of
`PHYSICAL_CONTACT_STRESS.md`.

This proof contains no numerical pose search, computed exclusion
certificate, normal reselection, replacement mean, shortened star,
physical-mask relabeling, omitted body, Lean/Lake invocation or CI.
