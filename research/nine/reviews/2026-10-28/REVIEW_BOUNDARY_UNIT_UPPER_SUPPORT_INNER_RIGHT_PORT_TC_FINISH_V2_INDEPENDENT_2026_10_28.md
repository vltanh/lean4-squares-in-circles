# Independent full review: upper boundary unit with an inner right port

Date: October 28, 2026 UTC. Reviewer: tc_finish_v2.

**Verdict: PASS for the exact complete local theorem and the precise export
boundary stated below.** I independently read every line of the frozen source,
verified its actual-frame hypotheses and every corner estimate, and checked the
closed frame and side-position endpoints. This review is separate from the
construction. The source was not modified during review.

## 1. Exact source pin, complete reads, and dependency scope

The full 218-line source reviewed is:

- `BOUNDARY_UNIT_UPPER_SUPPORT_WITH_INNER_RIGHT_PORT_HEIGHT_BOUND.md`
- SHA256 `450a64e84fe1b55a8102eee744757b8d8d47d8c04339c8b62d812b54487bd1eb`.

The complete source was read in two consecutive ranges, lines 1--115 and
116--218, without truncation. The source hash was checked before review.

There is no operative imported theorem or external direct-input document in
this source. The proof uses the elementary description of a unit square,
convexity of squared Euclidean norm and of scalar quadratics, the Pythagorean
identity, and the displayed exact inequalities. Accordingly there is no
unread operative dependency to infer from a filename or synopsis.

This is a force-free theorem about one actual physical boundary unit. No
original graph, force degree, resultant, selected pair normal, circle weight,
load grouping, application mean, or physical circle mask is part of its
hypotheses. The review does not supply a graph caller or any packing exclusion.

## 2. Literal statement and whole domain retained

The unchanged circle has radius satisfying

    R^2 = (2 + epsilon)^2 + 1/4, epsilon >= 0.

The actual square is

    A = (h + x, g) + [0,1](-q,p) + [0,1](p,q),
    |h| <= epsilon, p,q >= 0, p^2 + q^2 = 1.

It is contained in that disk and physically touches its circle. Its original
side point is

    Q = (h+x,g) + rho(p,q), 0 <= rho <= 1,
    x <= 0, x + rho*p >= 0, 0 <= Q_y <= 1.

The proposed conclusion is exactly `g > 4/7`. Because both vertical components
of the unit frame are nonnegative, `g` is its actual minimum height. The theorem
retains both signs of `h`, all nonnegative `epsilon`, both aligned frame
endpoints, all four side-point endpoints or inequalities at equality, and the
whole horizontal interval `-rho*p <= x <= 0`.

In particular, there is no hidden upper bound on epsilon and no premise that
any force line goes through an interior point. The proof does not shift the
origin of the containing circle: it subtracts `h` only in scalar corner
bookkeeping, then restores its complete effect.

## 3. Actual corners and horizontal shift estimate

The four scalar corner pairs used in the source are exactly

    U0=(x,g), U1=(x-q,g+p),
    U2=(x+p,g+q), U3=(x+p-q,g+p+q).

For `-rho*p <= x <= 0`, each of their horizontal absolute values is at most
`p+q <= sqrt(2)`. For example, `x-q` lies between `-rho*p-q` and `-q`, while
`x+p` lies in `[0,p]`; the remaining two intervals also satisfy the same bound.
The actual corner is `(h+Ui_x,Ui_y)`, and hence

    |actual corner|^2 <= |Ui|^2 + 2*sqrt(2)*epsilon + epsilon^2.

This estimate holds for either sign of `h` and for epsilon zero.

If `g <= 0`, the original lower port-height bound gives
`g >= -rho*q >= -1`. All corner heights then lie in `[-1,sqrt(2)]`.
Their squared scalar norms are at most four. The full actual norm is thus at
most `4 + 2*sqrt(2)*epsilon + epsilon^2`, strictly less than
`17/4 + 4*epsilon + epsilon^2 = R^2`. The strict reserve includes epsilon zero.
The entire nonpositive-height case is correctly excluded.

## 4. Positive low-height reduction and first two corners

Write `G=4/7` and `t=1-G=3/7`, and assume `0<g<=G`.

When `q=0`, necessarily `p=1` and `-1<=x<=0`. Every scalar corner norm is at
most `1+(1+G)^2=170/49<17/4`. This handles the complete first axis endpoint
before division by q. The other axis endpoint `p=0,q=1` remains in the later
closed ranges and requires no division by p.

For `q>0`, the first and third scalar corners obey

    |U0|^2 <= 65/49,
    |U2|^2 <= p^2+(G+q)^2
             = 1+G^2+2Gq <= 121/49.

The second estimate legitimately uses `0<=x+p<=p`. The actual port bound
also gives the full allowed side-position interval

    0 <= rho <= min(1,(1-g)/q).

No endpoint or sign of the actual horizontal displacement is discarded.

## 5. Complete upper-left adjacent-corner estimate

The source bounds the remaining adjacent corner by

    |U1|^2 <= (rho*p+q)^2 + (g+p)^2.

For `q<=t`, `p+q` increases up to q=t, where its value is
`(sqrt(40)+3)/7 < 4/3`; the latter strict comparison follows from
`sqrt(40)<19/3`. Therefore

    |U1|^2 < (4/3)^2+(11/7)^2
             = 1873/441 = 17/4 - 5/1764.

This strict reserve includes q=t.

For `q>=t` and `g<=1-q`, increasing rho to one and g to `1-q` gives

    (p+q)^2+(1-q+p)^2 = 3+2(p-q)
       <= (15+2*sqrt(40))/7 < 83/21 < 17/4.

The monotonicity of `p-q` on the closed q interval justifies the maximum at t.
For `g>=1-q`, substitution of the actual maximal allowed rho gives a convex
quadratic in g. Its maximum on `[1-q,G]` occurs at an endpoint. The lower
endpoint is the preceding bound, and the upper endpoint expands exactly to

    2G+2p+t^2/q^2 = 8/7+2p+9/(49q^2).

Both q-dependent terms decrease on `[t,1]`; continuity covers p=0 at q=1.
Its value at t is the same already bounded expression. This checks the whole
adjacent-corner domain, including q=t and g=1-q.

## 6. Complete opposite-corner estimate

For fixed p,q,g,rho, the squared norm of U3 is convex in x, so the entire
horizontal interval is covered by its two endpoints. At x=0 the identity is

    |U3|^2 = 2+g^2+2g(p+q)
             < 2+16/49+(8/7)(99/70)
             = 138/35 < 17/4,

where `sqrt(2)<99/70` supplies a strict bound.
At x=-rho*p the resulting norm is convex in rho. Its endpoint rho=0 is already
covered, and the other endpoint is `min(1,(1-g)/q)`.

For `q<=t` that endpoint is one. The exact corner has horizontal coordinate
`-q`, giving

    |U3|^2 < 9/49+(4/7+4/3)^2 = 1681/441 < 17/4.

For `q>=t`, `g<=1-q`, the same rho=1 expression increases with g and is at most

    q^2+(1+p)^2 = 2+2p <= 2+2*sqrt(40)/7 < 80/21.

In the remaining closed range `q>=t`, `g>=1-q`, the full expression is

    F(g,q)=[p-q-(1-g)*p/q]^2+(g+p+q)^2.

Its g derivative is exactly

    2[1+1/q-(1-g)/q^2] >= 2,

because `1-g<=q`. Thus replacing g by G is valid. Direct expansion gives

    F(G,q)=15/7+2(p+q)-6/(7q)+9/(49q^2).

The derivative of its last two terms is `(42q-18)/(49q^3)`, nonnegative on
`[t,1]`. For `t<=q<=9/10`, their value is bounded above by `-320/441`.
Using `p+q<99/70` yields

    F(G,q)<9362/2205 = 17/4 - 37/8820.

For `9/10<=q<=1`, `p+q` is decreasing and is at most
`(9+sqrt(19))/10<27/20`. The last two terms are at most their value
`-33/49` at one. Consequently

    F(G,q)<2043/490 = 17/4 - 79/980.

Both intervals include q=9/10, and the latter includes the p=0 axis endpoint.
Every strict rational reserve and every displayed identity in this section
has been checked independently.

## 7. Boundary contradiction and precise passing export

The preceding estimates place every scalar corner strictly inside squared
radius `17/4` whenever `0<g<=4/7`. Restoring h places every actual corner at
squared norm strictly below

    17/4+2*sqrt(2)*epsilon+epsilon^2
       <=17/4+4*epsilon+epsilon^2=R^2.

Strictness again holds at epsilon zero. Convexity of squared norm on the
actual square puts the entire square strictly inside the circle, contradicting
its physical boundary contact. Together with Section 3, this proves g>4/7 on
the complete stated domain.

I find no missing frame endpoint, side endpoint, positive-height subinterval,
or actual corner. The proof passes as a radius-parametric, degree-independent,
load-independent, single-unit physical height theorem. A future graph caller
must still prove its literal actual frame and original point hypotheses; this
review supplies neither those hypotheses nor a whole-fan exclusion.

No graph edge, selected normal, application mean, force, load, or original body
has been removed or substituted. No sampled geometric certificate, numerical
pose, Lean/Lake run, CI/workflow execution, metadata edit, staging, commit, or
remote write was used in this review. Adoption remains a separate root action.
