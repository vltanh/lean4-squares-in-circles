# Every boundary neighbor of a shallow tilted S root lies on one strict circle side

Date: October 27, 2026.

**Status: complete force-free hand theorem, reconstructed after the
workspace snapshot reset and submitted for full independent reread.**
The full earlier scope is retained, including origin-interior roots,
arbitrary degrees, all original means and every physical circle mask.
No root or neighbor force equation is used.

## 1. Complete actual physical hypotheses

Keep the original contained, interior-disjoint unit squares with

    sqrt(17)/2<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<=epsilon<1/60,
    r=R-sqrt(2),       r^2>419/1000.

Suppose A is an actual genuine S-leaf root in its own orthonormal
coordinates

    A=[U-1,U] times [V-1,V],
    U^2+V^2=d^2,
    1-epsilon<=U<=d,       V>0.

Its real leaf application and directions are

    P=(U,V),       e=(U,V)/d,       f=(-V,U)/d,
    L=P+[0,1]e+[-1/2,1/2]f.

The actual leaf L is retained throughout. Write a=U-1 and b=V-1.
The complete hypotheses imply

    |a|<=epsilon<1/60,
    59/60<U<61/60,
    V^2<=4epsilon<1/15,
    0<V<4/15,       -1<b<-11/15.                      (1)

The lower metric bound follows from
r^2>=25/4-sqrt(34)>419/1000. Every point of any physical boundary
unit has norm at least r, by comparison with its actual radius-R
corner and its diameter sqrt(2).

**Theorem.** For every physical boundary unit T other than L which
physically touches A, every actual circle corner Z of T satisfies

    f dot Z<0.                                          (2)

The proof covers every actual supporting normal and application mean
of that contact. In particular it retains U=1, U<1, all side
endpoints, both physical circle masks and zero individual weights.

## 2. No positive-vertical boundary contact survives the actual leaf

The upper-left A vertex (a,V) has squared norm at most

    epsilon^2+4epsilon<241/3600<r^2.

It cannot belong to a physical boundary unit.

No third unit can contain P either. A occupies the Southwest
right-angle tangent sector at P; the real leaf L occupies its
half-plane directed along the strictly Northeast e. The two remaining
connected angular gaps are each strictly smaller than a right angle.
A third unit's connected tangent sector has angle at least a right
angle and cannot fit. This includes coincident means and side endpoints.

Therefore a positive-vertical boundary normal could only be the
North own axis, at its unchanged actual point

    Q=(q,V),       a<=q<=U.

The boundary-point bound gives

    q^2>=r^2-V^2>419/1000-16/225>(7/12)^2.

Since q>=a>=-epsilon, this forces q>7/12.

### 2.1. A side-owned minimum of T

If T owns its minimum-y support, its actual rectangle is

    T=[z,z+1] times [V,V+1],       q-1<=z<=q.

Physical avoidance of the real L forces z+1<=U. Otherwise at
height V+eta for small positive eta the inner leaf edge is at
x=U-(V/U)eta, and its open section extends to the right of U.
That open section intersects T's actual open horizontal interval.

Thus every T corner has absolute horizontal coordinate below 61/60
and vertical coordinate below 19/15. All four squared norms are
strictly below 17/4, contradicting physical boundary contact.

### 2.2. A tilted minimum vertex of T

Otherwise Q is T's actual unique bottom vertex, and the whole
actual frame is

    T=Q+[0,1](c,s)+[0,1](-s,c),
    c,s>0,       c^2+s^2=1.

Put g=U-q>=0 and eta=V/U. The right upward edge crosses the
actual inner supporting line of L at parameter

    t_*=g/(c+eta*s).

If g>=c+eta*s, then q+c<=U. Every corner has absolute horizontal
coordinate below 61/60 and vertical coordinate below

    4/15+sqrt(2)<101/60.

Hence every squared norm is below

    (61^2+101^2)/3600=13922/3600<17/4.

In the remaining case 0<=t_*<1, the actual tangential coordinate
on L's inner line at that crossing is

    f dot (Q+t_*(c,s)-P)=g*d*s/(U*c+V*s)>=0.

If this were less than 1/2, the edge would enter int(L) immediately
after crossing. Therefore nonoverlap, including the real endpoint
equality, gives

    g*s>=(U*c+V*s)/(2*d),
    q<=U-V/(2*d)-(U/(2*d))*(c/s).                     (3)

Put t=U/(2*d)>59/122>3/8. The q bound yields

    c/s<(61/60-7/12)/(59/122)=793/885<1.               (4)

The actual opposite corner Q+(c-s,c+s) consequently has absolute
horizontal coordinate below 61/60 and vertical coordinate below
101/60, so the preceding squared-norm bound applies. The left
adjacent corner and Q have the stronger vertical bound 19/15.

For the right adjacent corner, (3) gives

    q+c<61/60+c*(1-t/s)<61/60+3/8=167/120.

The last scalar bound holds throughout 0<s<=1. On the positive
part, the maximum of sqrt(1-s^2)*(1-t/s) occurs at s^3=t and
equals (1-t^(2/3))^(3/2). Since t>3/8,
t^(2/3)>1/2, and the maximum is below 1/(2sqrt(2))<3/8.
The nonpositive part is immediate. Its vertical coordinate is
V+s<19/15, so this corner also has squared norm below

    (167/120)^2+(19/15)^2<17/4.

All four actual T corners are strictly inside the circle. This
contradicts T's physical boundary status. Thus every positive-vertical
normal has been excluded, with all original owner and mean endpoints.

## 3. The East own normal is physically impossible

Suppose another actual unit T touches A with the East normal, at
any actual mean on its right side. Then T is contained in x>=U.
Its center satisfies

    (c_T)_x>=U+1/2>89/60.

Every contained unit center has norm below 91/60, from the exact
bound |c_T|^2+|c_T|+1/2<=1105/256. Consequently

    |(c_T)_y|<1/3.

The real leaf center is c_L=(d+1/2)e. The original bounds give

    7/5<(c_L)_x<91/60,
    0<(c_L)_y<2/5.

For the first lower bound one may use
U*(1+1/(2*d))>(59/60)*(91/61)>7/5.
Therefore

    |c_T-c_L|^2
      <(7/60)^2+(11/15)^2<1.

The actual radius-1/2 incircles of distinct unit squares have
disjoint open interiors, so their centers are at distance at least
one. This contradiction excludes every East-normal contact, even
without assuming T itself touches the outer circle.

## 4. Every remaining actual boundary corner is on the negative f side

The complete actual normal cover is now West, South, strict Southwest
at (a,b), or strict Southeast at (U,b). We check all of them.

### 4.1. The whole West side and its Southwest endpoint

An actual West or Southwest contact point has the form
p=(a,y), b<=y<=V. Since it belongs to a physical boundary unit,

    y^2>=r^2-a^2>419/1000-1/3600>(647/1000)^2.

The positive endpoint V<4/15 excludes positive y, so y<-647/1000.
In the original radial frame (e,f),

    p_f=(-V*a+U*y)/d<0,
    |p_e|=|U*a+V*y|/d<epsilon+V<17/60.

The first strict sign follows, for example, from
V*epsilon<1/225 and U*(-y)>(59/60)*(647/1000).
If an actual circle corner Z of this neighbor had f dot Z>=0,
then p dot Z<=R*|p_e| and

    |Z-p|^2>=(R-|p_e|)^2
             >(2-17/60)^2=(103/60)^2>2.

This contradicts the actual unit diameter. Every such Z therefore
satisfies (2). The entire original West-side mean is retained.

### 4.2. Every South-side mean, including both endpoints

For an actual South normal, the entire neighboring unit lies in
y<=V-1. Thus any actual radius-R corner Z satisfies Z_y<=V-1
and |Z_x|<=R. Since R<25/12,

    d*(f dot Z)
       =-V*Z_x+U*Z_y
       <=V*R-U*(1-V)
       <(4/15)*(25/12)-(59/60)*(11/15)
       =-149/900<0.

This treats every point on the actual South side at once and does
not impose a midpoint or endpoint mean.

### 4.3. The strict Southeast vertex

Its actual application is q=(U,V-1). In the original radial frame,

    q_e=d-V/d>0,
    q_f=-U/d<0.

If a radius-R corner Z of its actual neighbor had f dot Z>=0,
then q dot Z<=R*q_e. Hence

    |Z-q|^2
      >=(R-q_e)^2+q_f^2
       =(R-d)^2+1+2*V*(R/d-1)>2.

Here R-d>1 and R/d>1. This again contradicts the actual unit
diameter. The full Southeast normal cone and all physical corner
masks are included.

These three arguments exhaust the surviving physical features and
prove (2) for every boundary neighbor.

## 5. Exact retained scope

The entire proof is force-free. A and all its actual neighbors may
have arbitrary degrees, additional forces and circle weights. The
only root hypothesis is its real shallow tilted S-leaf chart with
U>=1-epsilon; no origin-exterior premise is added. Every physical
corner, including a corner with zero individual multiplier, obeys
the conclusion.

This source can therefore replace the pre-reset source with the same
name in all callers that used precisely this physical theorem. It
does not import the degree-three torque classification from the older
OFF_ORIGIN_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md.

No normal or actual mean is changed, no original force is deleted,
and no numerical pose, compilation, CI, remote action or shared
metadata edit is used.
