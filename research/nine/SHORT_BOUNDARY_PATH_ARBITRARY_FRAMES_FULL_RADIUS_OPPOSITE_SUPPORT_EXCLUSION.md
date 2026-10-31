# Opposite supports exclude every short boundary path throughout the full radius window

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: new complete proposed strengthening, frozen for separate
independent and root review.** The endpoint frames are arbitrary and
their horizontal support directions need not be owned side normals.
The theorem applies for every R>=79/40, with no upper radius bound.
It preserves the preceding frozen R>=2 theorem at its original bytes.

## 1. Complete actual statement

Keep the containing-circle origin O. Let two through four distinct
actual unit squares, with disjoint open interiors, form a physically
touching path inside the closed radius-R disk, where

    R>=79/40.

Every path unit physically touches the circle. Its actual center
directions have a strictly increasing counterclockwise lift along the
path, of total advance less than 2*pi, with every successive advance
less than pi. Let L and K be its first and last units.

In an oriented orthonormal chart about the unchanged circle origin,
suppose the original endpoint support points satisfy

    P_L=(-X_L,h_L) in L,       L subset {x<=-X_L},
    P_K=(X_K,h_K) in K,        K subset {x>=X_K},
    X_L,X_K>-1/2,             h_L,h_K>=0,
    X_L+X_K<=1.                                         (1)

The two heights are independent. The points can be tilted vertices,
arbitrary aligned side points, or original shared-side means including
either closed endpoint. There is no endpoint side-ownership premise.

Let F_L,F_K be nonzero nonnegative combinations of their respective
actual physical circle-corner position vectors. Assume

    (F_L)_y>=0,              (F_K)_y>=0.                 (2)

Retain both physical corners of a two-corner mask and every possible
zero individual coefficient. **Theorem: this entire configuration is
impossible.** No endpoint or path force equation is a premise.

## 2. Complete center-quadrant proof at arbitrary actual support frames

We print the physical center lemma, including the aligned mean case.
For a right endpoint with minimum-x point P=(X,h), X>-1/2 and h>=0,
suppose its actual center had negative y coordinate.

If the unit is tilted, its full pose is

    P+[0,1](c,s)+[0,1](s,-c),
    c,s>0, c^2+s^2=1.                                  (3)

The center height h+(s-c)/2<0 forces c>s and
0<=h<(c-s)/2. Its lower adjacent and opposite vertices then both
have strictly negative y coordinates. The upper adjacent vertex has
squared norm greater than P's by

    1+2Xc+2hs>0.

The opposite vertex has squared norm greater than that upper vertex by

    1+2Xs-2hc
      >1+2Xs-c(c-s)
       =s(2X+s+c)>0.                                  (4)

The strict signs use 2X>-1 and c+s>1. Hence neither nonnegative-height
vertex can be a physical circle corner. Every physical circle corner
has negative y coordinate, contradicting the nonnegative y component
of the full nonzero resultant in (2).

If the unit is aligned, write it as [X,X+1] times [B,B+1], retaining
its original P on the full left side. Since X>-1/2, its far normal
side is x=X+1. A negative center height B+1/2 would make B the only
farthest tangent coordinate, again giving only negative-y circle
corners and contradicting (2).

Thus the actual center has nonnegative y coordinate in both complete
frame cases. Its x coordinate is X+w/2>0, because its actual horizontal
width w is at least one. Reflecting the left unit in the vertical axis
gives the same conclusion there: its actual center has negative x
coordinate and nonnegative y coordinate. Write the actual center angles

    alpha_L=pi-delta_L, alpha_K=delta_K,
    0<=delta_L,delta_K<pi/2.                             (5)

Both exact zero-height endpoints remain permitted.

## 3. The complete path angle interval

Every boundary center has radius at least R-1/sqrt(2)>5/4, including
at R=79/40. Every contacting pair of centers has distance at most
sqrt(2). The cosine law therefore gives its minor gap

    gamma<theta:=acos(9/25).

By the actual lift premise, all successive path advances are these
minor gaps. Equations (5) and the strictly increasing lift of total
advance less than 2*pi give the exact total

    pi+delta_L+delta_K.

At most three contacts consequently imply

    delta_L+delta_K<alpha:=3theta-pi.                   (6)

The elementary exact three-angle identities give

    cos(alpha)=13959/15625>89/100,
    sin(alpha)=1204 sqrt(34)/15625<9/20,
    0<alpha<pi/6.                                      (7)

Indeed pi/3<theta<pi/2 first gives 0<alpha<pi/2. The cosine formula
and 4*13959^2>3*15625^2 then give the upper bound pi/6. All radical
and rational comparisons in (7) compare positive quantities. If there
are at most two contacts, their total advance is less than 2theta<pi,
already impossible. The following argument covers the three-contact
case and retains either or both deltas equal to zero.

## 4. A sharp enough abscissa bound for every endpoint orientation

Consider either endpoint after reflecting the left one. Let its actual
center be r(cos(delta),sin(delta)), where 0<=delta<=alpha, and let X
be its minimum horizontal coordinate. Put

    sigma=1/sqrt(2), C=cos(delta), S=sin(delta).

The complete actual frame can be written with axes

    u=(cos(psi),sin(psi)),
    v=(sin(psi),-cos(psi)),       0<=psi<=pi/2.           (8)

The endpoints in (8) are the actual aligned side cases. No actual
contact point is selected or replaced in this frame description.
For all these frames the original horizontal support coordinate is

    X=r*C-(cos(psi)+sin(psi))/2.                         (9)

Every actual farthest corner is on the circle. Choosing either farthest
corner at an own-coordinate tie is legitimate for the radius identity;
it imposes no condition on the original physical mask or its weights.

The following uniform radical estimate will be used throughout:

    sqrt(R^2-(1/2)t^2)>=R-(2/15)t^2,    |t|<=1.          (10)

To see this, rationalize the difference from R. Its coefficient is
at most 1/[2(R+sqrt(R^2-1/2))]. In the full stated radius range,
sqrt(R^2-1/2)>9/5 and R>=79/40, so

    R+sqrt(R^2-1/2)>151/40>15/4.

This proves (10), including t=0. It uses no upper radius bound.

### 4.1. The full far-corner case psi>=delta

The center's two own-coordinate signs permit the far corner offset
(u+v)/2, of length sigma and direction

    beta=psi-pi/4.

At psi=delta the v coordinate is zero and both choices are physical;
the displayed one remains valid. At psi=pi/2,delta=0 the u coordinate
is zero and the same radius identity remains valid. Put

    theta_0=delta-beta, t=sin(theta_0).

Then delta-pi/4<=theta_0<=pi/4, so its cosine is nonnegative. The
actual radius identity and (9) give exactly

    r=sqrt(R^2-sigma^2*t^2)-sigma*cos(theta_0),
    X=C*sqrt(R^2-sigma^2*t^2)
        -sigma*(2C*cos(theta_0)+S*t).                   (11)

Use (10) and cos(theta_0)=sqrt(1-t^2)<=1-t^2/2. Then

    X>=(R-2sigma)C-sigma*S*t+(sigma-2/15)C*t^2.

The quadratic expression in t is bounded below by completing its
square. Since sigma>7/10, one has sigma-2/15>17/30, and therefore

    sigma*S*t-(sigma-2/15)C*t^2
      <=sigma^2*S^2/[4(sigma-2/15)C]
      <=(15/68)*S^2/C.

This inequality also holds at S=0, when its right side is zero.
Thus the whole case, including every tied or aligned endpoint, gives

    X>=g(delta):=(R-sqrt(2))*cos(delta)
                  -(15/68)*sin(delta)^2/cos(delta).    (12)

### 4.2. The full complementary far-corner case psi<delta

Now the center's u coordinate is positive and its v coordinate is
negative. The actual farthest corner offset is (u-v)/2, of length
sigma and direction beta=psi+pi/4. Put theta_0=beta-delta. Formula
(9) gives exactly

    X=C*sqrt(R^2-(1/2)sin(theta_0)^2)
        -sigma*((C+S)cos(theta_0)+C*sin(theta_0)).       (13)

Let T=S/C=tan(delta). The full interval (7) gives

    0<=T<45/89,
    sqrt(2+2T+T^2)<181/100.                            (14)

For the final inequality, its squared value is less than
25877/7921, which is less than (181/100)^2 by cross multiplication.
Cauchy--Schwarz bounds the second bracket in (13) by
C*sqrt(2+2T+T^2). The exact positive comparisons

    sigma<99/140,
    (99/140)*(181/100)=17919/14000
      <1921/1500<sqrt(2)-2/15                          (15)

complete the estimate. The middle gap in (15) is 31/42000>0; the
last comparison uses sqrt(2)>707/500. Both radical bounds follow by
squaring positive quantities.

Apply (10), now enlarged to sqrt(R^2-(1/2)sin(theta_0)^2)>=R-2/15.
Equations (13)--(15) give

    X>(R-sqrt(2))*C>=g(delta).

This case includes the aligned psi=0 endpoint whenever delta>0.
Together Sections 4.1--4.2 exhaust every actual frame and every
farthest-corner sign, so (12) is a uniform whole-orientation bound.

## 5. Entire continuous sum bound and the exact positive reserve

Write A=R-sqrt(2)>0 and k=15/68. The function in (12) is exactly

    g(delta)=(A+k)cos(delta)-k sec(delta).

It is strictly decreasing on [0,alpha]: its derivative is negative
for delta>0 and vanishes only at the left endpoint. Its second
derivative is

    -(A+k)cos(delta)-k(sec(delta)*tan(delta)^2+sec(delta)^3)<0.

Thus it is strictly concave on the entire interval. For x,y>=0 with
x+y<alpha, concavity on [0,x+y] gives

    g(x)+g(y)>=g(0)+g(x+y)>g(0)+g(alpha).                (16)

When x+y=0, the first inequality is directly equality; the second
remains strict by alpha>0 and strict decrease. No zero-angle endpoint
or collapsed interval is lost.

By (6), (12), and (16), the actual original endpoint coordinates satisfy

    X_L+X_K
      >(R-sqrt(2))*(1+cos(alpha))
         -(15/68)*sin(alpha)^2/cos(alpha).

Use R>=79/40, sqrt(2)<99/70, and (7). All denominators are positive,
and R-sqrt(2)>157/280. The entire expression is consequently greater
than

    (157/280)*(189/100)
      -(15/68)*(81/400)*(100/89)
      =1+57857/6052000>1.                              (17)

This contradicts the original support span in (1). The positive
rational reserve (17) applies to the full continuous orientation and
radius domain, including the lower radius 79/40. It is not a sampled
or numerically minimized bound.

## 6. Exact relation to the preceding sources and caller limits

The earlier arbitrary-frame source proves the same physical statement
for R>=2 with a coarser width estimate. The present new source retains
its full center lemma and strengthens the continuous abscissa estimate
to the whole R>=79/40 domain. Both preceding frozen manuscripts remain
unchanged:

| Preceding source | SHA-256 |
| --- | --- |
| SHORT_BOUNDARY_PATH_OPPOSITE_SUPPORTS_WITHOUT_SIDE_OWNERSHIP.md | 699995c7434d2b448c16831f874bc2b36a2df356532bbd1c085cc8c15c9b96d9 |
| FOUR_BOUNDARY_PATH_OWNED_ENDPOINT_TANGENT_SIGN_OBSTRUCTION.md | 5e8cba82367da03c15710cd6060c3a009323413465a78acaf965f4b07ff29536 |

The full proof used here is printed in Sections 2--5. The new theorem
has no force-balance, concurrence, true-degree or upper-radius premise.
Every original physical side mean, actual circle mask and individual
zero coefficient remains. A caller still must prove the actual center
traversal, both original-origin support heights, both resultant signs,
and the support span. An abstract graph order or a translated local
coordinate chart does not supply those requirements.

No whole original graph/load family is closed by this generic source
alone. No new fine label, geometric sampling, numerical optimization,
force deletion, mean change, Lean compilation, CI, workflow, shared
metadata change, commit or publication is used. This new strengthening
requires its own complete independent and root reviews.
