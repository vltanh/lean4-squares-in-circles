# Short boundary paths: independent endpoint heights and all horizontal-axis endpoints

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed strengthening, submitted for a separate full
independent review.** It preserves the frozen preceding theorem and
removes two restrictions from its geometric hypothesis. The actual
endpoint heights need not agree, and either or both inward normals may
be exactly horizontal. There is no upper-radius or degree bound.

## 1. Complete physical statement

Keep the original circle origin. Let R>=79/40 and let two through four
distinct actual unit squares form a physically touching path, all
contained in the radius-R disk and physically touching its circle.
Their open interiors are pairwise disjoint. Its first and last units
are L and K. Assume their actual center directions have a strictly
increasing counterclockwise lift along the path, with total advance
less than 2*pi and each successive advance less than pi.

In an oriented orthonormal chart about the unchanged circle origin,
assume the actual endpoint points and owned inward side normals are

    P_L=(-X_L,h_L),       P_K=(X_K,h_K),
    X_L,X_K>0,           h_L,h_K>=0,
    X_L+X_K<=sqrt(2),
    n_L=(-b_L,a_L),      n_K=(b_K,a_K),
    0<=a_i<b_i,          a_i^2+b_i^2=1.                 (1)

The points may be anywhere on their full closed actual sides. Put
j_i=J n_i for the positive quarter-turn J. Let F_i be any nonzero
nonnegative combination of the actual physical circle-corner position
vectors of that endpoint. Retain both individual coefficients when two
corners are physical. Suppose

    F_L dot j_L<=0,       F_K dot j_K>=0.                (2)

**Theorem.** This entire physical configuration is impossible.

There is no force balance or concurrence premise on the path. All
additional units and forces remain. A caller must establish the actual
center traversal, original-origin coordinates, owned sides and the
two signs; neither a graph drawing nor a translated local chart
supplies these hypotheses automatically.

## 2. Endpoint centers, including the exact axis endpoints

For the right endpoint, write its whole actual pose as

    K=P+[0,1]n+[-rho,1-rho]j, 0<=rho<=1,
    P=(X,h), n=(b,a), j=(-a,b).

Its minimum normal coordinate is N=b*X+a*h>0. Its center is

    c=(N+1/2)n+tau*j,
    tau=P dot j+1/2-rho.

Every physical circle corner is on its far normal side: replacing
N by N+1 at a fixed tangent coordinate increases squared norm by
2*N+1>0. If tau<0, every farthest tangent coordinate is tau-1/2<0,
contradicting F dot j>=0. Hence tau>=0, including both physical
corners and either zero coefficient when tau=0.

The center coordinates consequently satisfy

    c_e=X+b/2-a*(1/2-rho)>=X+(b-a)/2>0,
    c_f=(N+1/2)*a+tau*b>=0.

Thus the actual center angle and normal angle obey

    0<=phi=atan(a/b)<=delta<pi/2,
    v=delta-phi>=0.                                    (3)

When a=0 and tau=0, delta=phi=0 is deliberately retained. Reflecting
the left endpoint across the f axis reverses its oriented tangent,
so (2) gives the identical result there. Its actual center is in the
closed upper left quadrant, with angle pi-delta_L. These conclusions
used h_L and h_K separately; their equality was never required.

## 3. The entire angular interval remains small

Every boundary unit center has norm at least R-1/sqrt(2)>5/4.
Touching unit centers have distance at most sqrt(2). The cosine law
therefore bounds each actual minor contact angle by

    gamma<theta:=acos(9/25).

The actual path lift and (3) give its total advance exactly

    pi+delta_L+delta_K,

including the value pi when both deltas vanish. There are at most
three contacts. Consequently

    delta_L+delta_K<alpha:=3*theta-pi.

The exact triple-angle identities and positive comparisons are

    cos(alpha)=13959/15625>89/100,
    sin(alpha)=1204*sqrt(34)/15625<9/20,
    0<alpha<pi/6.

For the last upper bound use 4*13959^2>3*15625^2 and alpha in(0,pi/2).
With at most two contacts the path advance is already impossible,
because it is at least pi whereas 2*theta<pi. The three-contact
case is covered by the remaining argument.

## 4. A uniform lower bound on the two original abscissae

For either reflected right endpoint let r=|c| and put

    d=sqrt(R^2-1/4)-1>9/10,       r_0=d+1/2.

The strict bound on d follows from
(79/40)^2-1/4-(19/10)^2=13/320>0. Its actual farthest corner has
own coordinates (r*cos(v)+1/2,r*sin(v)+1/2), including v=0.
Thus

    R^2=r^2+r*(cos(v)+sin(v))+1/2,
    (r_0-r)*(r_0+r+1)=r*(cos(v)+sin(v)-1).

Since 0<=v<=delta<pi/6, this implies

    r_0>=r>=r_0-sin(v)/2.

Every original side parameter gives

    X>=r*cos(delta)-(cos(phi)+sin(phi))/2.

Set c=cos(delta), s=sin(delta). Cauchy--Schwarz and direct expansion
give, including phi=0 and delta=0,

    cos(phi)+sin(phi)+c*sin(delta-phi)
      =(1+c*s)*cos(phi)+s^2*sin(phi)
      <=sqrt(1+2*c*s+s^2)<=c+(6/5)*s.

Indeed the squared excess in the final inequality is
(2/25)*s*(5*c-7*s)>=0 on this entire interval. Substitution proves

    X>=g(delta):=d*cos(delta)-(3/5)*sin(delta).            (4)

This proves (4) for each endpoint separately, without a common
height and without excluding the zero normal-angle endpoint.

The function g is positive, decreasing and strictly concave on
[0,alpha]. Positivity follows already from
(9/10)*(89/100)-(3/5)*(9/20)>0; then g''=-g<0.
If x,y>=0 and x+y<alpha, concavity gives

    g(x)+g(y)>=g(0)+g(x+y)>g(0)+g(alpha).                (5)

For x+y=0 the first relation in (5) is equality directly, so no
division by a degenerate interval is needed. The strict final
inequality still holds since alpha>0 and g is strictly decreasing.

Apply (4)--(5) to the two actual deltas. Their original abscissae obey

    X_L+X_K
      >d*(1+cos(alpha))-(3/5)*sin(alpha)
      >(9/10)*(1+89/100)-(3/5)*(9/20)
       =1431/1000>10/7>sqrt(2),

contradicting (1). This proves every independent-height and axis
endpoint of the complete statement.

## 5. Relation to the preceding theorem and preservation

This strengthening independently prints every additional endpoint
step. It uses the same continuous scalar argument as the complete
preceding source, whose original strict/common-height scope is an
immediate subcase:

| Preceding complete source | SHA-256 |
| --- | --- |
| FOUR_BOUNDARY_PATH_OWNED_ENDPOINT_TANGENT_SIGN_OBSTRUCTION.md | 5e8cba82367da03c15710cd6060c3a009323413465a78acaf965f4b07ff29536 |

No circle resultant is replaced by a center, no original side mean
is selected anew, and no two-corner physical mask or zero coefficient
is lost. The theorem has no upper containing-radius bound. It gives
no new whole original family credit until a caller proves its full
hypotheses and its complete original feature union. No Lean, CI,
numerical pose search, force deletion or metadata change is used.
