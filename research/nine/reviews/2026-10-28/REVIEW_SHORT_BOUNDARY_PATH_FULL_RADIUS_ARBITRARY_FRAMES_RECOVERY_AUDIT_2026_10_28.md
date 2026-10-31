# Independent review of the full-radius arbitrary-frame short boundary path exclusion

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Verdict: PASS for the complete statement at the exact frozen bytes below.**
This is a fresh independent mathematical review of the new strengthening,
including the full physical center lemma, both far-corner sign cases, the
continuous orientation bound, and the radius endpoint. It does not transfer
approval from either preceding path theorem.

## 1. Exact object, scope, and direct identities

The reviewed source is
`SHORT_BOUNDARY_PATH_ARBITRARY_FRAMES_FULL_RADIUS_OPPOSITE_SUPPORT_EXCLUSION.md`:

- Bytes: 11,659.
- SHA-256: `34c9a02388146c9e085f66831eb3be49bd577cf1ec47ff7948f7306c0f4c24f1`.
- Git blob: `7acffbf54f622b53d310168207ca9ba6d28164f1`.

I read the complete source and independently rederived its proof. Its two
displayed preceding-source pins match the current checkout exactly:

| Preceding source | Current SHA-256 |
| --- | --- |
| SHORT_BOUNDARY_PATH_OPPOSITE_SUPPORTS_WITHOUT_SIDE_OWNERSHIP.md | 699995c7434d2b448c16831f874bc2b36a2df356532bbd1c085cc8c15c9b96d9 |
| FOUR_BOUNDARY_PATH_OWNED_ENDPOINT_TANGENT_SIGN_OBSTRUCTION.md | 5e8cba82367da03c15710cd6060c3a009323413465a78acaf965f4b07ff29536 |

The new proof is printed in full and does not require an unprinted
strengthening of either input. I had also independently reviewed both
preceding sources at those exact bytes. They remain unchanged.

The domain is two through four actual boundary units inside the original
radius-R disk, R >= 79/40, with the actual counterclockwise center lift
specified in the statement. The endpoint supports are at (-X_L,h_L) and
(X_K,h_K), with their whole units on the respective outer horizontal
half-planes, X_L,X_K > -1/2, independent h_L,h_K >= 0, and X_L+X_K <= 1.
Both full nonzero circle-corner resultants have nonnegative vertical
component. The endpoint directions need not be owned axes. No force
equation, true-degree restriction, upper radius bound, or relation between
the two heights is used.

## 2. Physical center quadrants, including all far-corner ties

For a tilted right unit with minimum-x vertex P=(X,h), I independently
used its full pose with inward axes (c,s),(s,-c), c,s>0. A negative
center height gives c>s and 0 <= h < (c-s)/2. The lower adjacent and
opposite vertices then both have strictly negative height. The upper
vertex has larger squared norm than P by 1+2Xc+2hs>0. The opposite
vertex in turn has larger squared norm than the upper vertex because

    1+2Xs-2hc > s(2X+s+c) > 0.

The last strict inequality uses exactly 2X>-1 and c+s>1; it does not
assume X is positive. Thus every actual farthest corner has negative
height. Every physical circle corner is a farthest corner, so a nonzero
nonnegative combination of all physical circle-corner vectors has
negative vertical component. This contradicts the given full resultant.
An individual zero coefficient cannot remove this contradiction.

In the aligned case [X,X+1] times [B,B+1], X>-1/2 makes the right side
strictly farther in the horizontal coordinate. A negative center height
makes B the strictly farther vertical coordinate. The only farthest
height is negative, giving the same contradiction. This argument leaves
the original minimum-side point or mean unchanged, including its closed
endpoints. Center height zero is retained rather than excluded.

Therefore the right center has nonnegative height and strictly positive
x coordinate: its horizontal width is at least one, so X+width/2>0.
Reflection gives a strictly negative x coordinate and nonnegative height
for the left center. Their actual arguments are pi-delta_L and delta_K,
with both deltas in [0,pi/2). No selected circle weight determines these
center positions.

## 3. The actual path angle, rather than an abstract graph order

Every boundary center has radius at least R-1/sqrt(2)>5/4 throughout
the stated range, including R=79/40. Touching unit centers are at
distance at most sqrt(2). The cosine law therefore gives, for each
minor center gap gamma,

    cos(gamma) = (r_1^2+r_2^2-D^2)/(2r_1r_2) > 9/25.

One can check the strict lower bound directly from
cos(gamma) >= 1-D^2/(2r_1r_2) and r_1r_2>25/16. The statement's
successive advances are less than pi, so they are these actual minor
gaps. Its increasing lift of total advance less than 2*pi is essential:
the endpoint quadrants force that total to be pi+delta_L+delta_K.

With at most three contacts, delta_L+delta_K < alpha=3acos(9/25)-pi.
The exact identities in the source give

    cos(alpha)=13959/15625 > 89/100,
    sin(alpha)=1204 sqrt(34)/15625 < 9/20,
    0 < alpha < pi/6.

The sine, cosine, and quadrant comparisons are valid with positive
quantities. In particular, pi/3<acos(9/25)<pi/2 fixes alpha's quadrant
before using its cosine. A path with fewer than three contacts already
has total advance below pi and is impossible; retaining it in the common
proof does not add a missing equality case.

## 4. Uniform bound over the entire actual endpoint frame

Write a reflected or right endpoint center as r(C,S), C=cos(delta)>0,
S=sin(delta)>=0. Every actual frame is covered by inward axes

    u=(cos(psi),sin(psi)), v=(sin(psi),-cos(psi)),
    0 <= psi <= pi/2.

The original minimum horizontal coordinate is exactly
X=rC-(cos(psi)+sin(psi))/2. This identity uses the actual square's
support and does not replace an application point. The aligned frames
psi=0 and psi=pi/2 are included.

I checked the uniform radical estimate by rationalization:

    sqrt(R^2-t^2/2) >= R-(2/15)t^2, |t|<=1.

Indeed its loss coefficient is at most
1/[2(R+sqrt(R^2-1/2))]<2/15, since R>=79/40 and
sqrt(R^2-1/2)>9/5. This proof has no upper-radius premise and is valid
at t=0.

### 4.1. Nonnegative second own-center coordinate: psi>=delta

The actual farthest offset can be (u+v)/2. It has length
sigma=1/sqrt(2) and argument beta=psi-pi/4. At psi=delta the second
own-center coordinate is zero; at psi=pi/2,delta=0 the first is zero.
The chosen corner is still an actual farthest corner in both ties. Its
use for the radius identity imposes no positivity condition on its
physical coefficient.

With theta_0=delta-beta and t=sin(theta_0), its cosine is nonnegative.
Solving the radius equation for the actual positive center radius and
using the exact horizontal width gives

    X=C sqrt(R^2-t^2/2)-sigma(2C cos(theta_0)+S t).

The estimate cos(theta_0)<=1-t^2/2 and the radical bound give

    X >= (R-sqrt(2))C - sigma S t + (sigma-2/15)C t^2.

Completing this quadratic square is valid because C>0 and
sigma-2/15>17/30>0. Its possible loss is at most

    sigma^2 S^2/[4(sigma-2/15)C] <= (15/68)S^2/C.

This also treats S=0 without division by S. Thus the full first case
gives X>=g(delta), with the g printed in the source.

### 4.2. Negative second own-center coordinate: psi<delta

The actual farthest offset is now (u-v)/2, of argument beta=psi+pi/4.
The radius and width identities instead give exactly

    X=C sqrt(R^2-sin(theta_0)^2/2)
        -sigma((C+S)cos(theta_0)+C sin(theta_0)).

This is a different far corner; carrying over the preceding corner
formula would be invalid. The source correctly changes it. Setting
T=S/C yields 0<=T<45/89. Cauchy--Schwarz bounds the bracket by
C sqrt(2+2T+T^2). I checked the exact positive comparisons

    (181/100)^2-25877/7921 = 729881/79210000 > 0,
    1921/1500-17919/14000 = 31/42000 > 0.

Together with sigma<99/140 and sqrt(2)>707/500, these prove that the
whole bracket loss is strictly below C(sqrt(2)-2/15). The radical
bound enlarged to R-2/15 therefore gives
X>(R-sqrt(2))C>=g(delta). This second case includes the aligned
psi=0 frame whenever delta>0. For delta=0 it is empty. The two cases
exhaust all orientations, signs, and aligned endpoints.

## 5. Continuous sum, exact reserve, and closed endpoints

Let A=R-sqrt(2)>0 and k=15/68. The complete orientation bound is

    g(delta)=(A+k)cos(delta)-k sec(delta).

Its derivative is negative for delta>0, zero only at delta=0. Its
second derivative is strictly negative throughout [0,alpha]. For
x,y>=0 with x+y<alpha, concavity applied with x and y as complementary
points of [0,x+y] gives

    g(x)+g(y) >= g(0)+g(x+y) > g(0)+g(alpha).

When x+y=0, the first equality is checked directly and the second
inequality remains strict. Thus no zero-height or zero-angle endpoint
is silently removed.

Combining this with the actual angle sum gives

    X_L+X_K > (R-sqrt(2))(1+cos(alpha))
                  -(15/68)sin(alpha)^2/cos(alpha).

All substitutions have the correct direction: R-sqrt(2)>157/280,
1+cos(alpha)>189/100, and the subtracted quotient is below
(81/400)(100/89). Exact rational arithmetic gives

    (157/280)(189/100)-(15/68)(81/400)(100/89)
      = 1+57857/6052000 > 1.

This contradicts the original support span. It is a uniform proof
over the continuous frame interval and every R>=79/40, not a sample,
numerical optimizer, or unproved extremum claim.

## 6. Approval limits and preserved data

The source proves its entire force-free statement. It retains both
physical circle corners, zero individual weights, independent endpoint
heights, aligned side points and original closed means, arbitrary true
degrees, and the original circle origin. No owner selection is needed.
A caller must still establish the actual counterclockwise lift, every
physical boundary status, both full resultant signs, and the original
support heights and span. This review gives no abstract graph order
the status of an actual physical traversal.

The generic source alone closes no whole original family identifier.
All nine actual units and the original 2513/58 inventory are unchanged.
I made no source edit, force deletion, mean replacement, radius-window
restriction, metadata change, Lean compilation, CI run, commit, push,
or publication. The only computation used in this review checks byte
identities and exact rational arithmetic printed above. Root adoption
and any original-interface caller remain separate actions.
