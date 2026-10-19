# Gate 3B.2 / M5: global support surplus and quantitative two-frame stability

Recovered from the preceding uncommitted handoff and reviewed in the current
continuation. Repository baseline: f6d1647bf42688327f2507c5837e7e8c41ff2ece.
Research only. The full M5 exclusion and unrestricted sharp radius are OPEN.

## Definitions

Put T=pi/2 and h=pi/4. A square frame is an angle theta modulo T.
M5 means that the maximum number of frames in a CLOSED clockwise h-window,
counting multiplicity, is five. It does not mean merely a chosen 5/3 split.
For the eight actual frames define

    S = sum_i exp(4 i theta_i),
    w_ij = (1+|cos(theta_j-theta_i)|+|sin(theta_j-theta_i)|)/2,
    W = sum_{i<j} w_ij,
    c = (sqrt(2)-1)/2,
    W0 = 28+15c = (41+15sqrt(2))/2,
    E = W-W0.

For two actual unit squares, w_ij is their combined projected half-width
in every signed side-normal of either square. W has no center or owner
variables. No disk-dependent upper bound on W is assumed.

## 1. Global harmonic bound

For maximum closed-window count m,

    |S| <= 2m-8.

In particular M5 implies |S|<=2 and

    sum_{i<j} sin^2(2(theta_i-theta_j)) = (64-|S|^2)/4 >= 15.

Proof. Set alpha_i=4theta_i modulo 2pi and let N(phi) count the points
alpha_i in the closed semicircle centered at phi. Except at finitely many
endpoints, complementary semicircles partition the eight points, hence
8-m<=N(phi)<=m. For any beta, direct integration of each indicator gives

    integral N(phi) cos(phi-beta) dphi = 2 sum_i cos(alpha_i-beta).

The constant four has zero cosine integral. Since |N-4|<=m-4 almost
everywhere and integral |cos(phi-beta)| dphi=4, the real part of
exp(-i beta)S is at most 2m-8. Choose beta in the direction of S.
Expansion of |S|^2 proves the pair identity. Coincident frames and closed
endpoint ties cause no issue for the almost-everywhere integral. QED.

The converse is not asserted: five frames at zero and three at h have
|S|=2 but all eight lie in a single closed h-window.

## 2. Sharp pair-support infimum on M5

Every M5 frame multiset satisfies W>=W0.

For one pair set t=|sin(2(theta_i-theta_j))| in [0,1]. Then

    w_ij-1 = (sqrt(1+t)-1)/2 >= c t >= c t^2.

The first inequality is the chord inequality for the concave square root.
Sum and apply Section 1. In a generic folded M5 word, letting all folded
positions tend to zero gives five frames tending to zero and three to h,
and W tends to W0. This is an infimum of frame data, not an attained
M5 packing or a radius theorem.

## 3. Strong concavity on both complete folded M5 charts

Use either closed chart proved in GATE3B_M5_TWO_FOLDED_TYPES.md; the proof
also applies to all eight bounded-walk words before re-anchoring. Write

    0=x_0<=x_1<=...<=x_7<=h,
    theta_i=x_i+h*1_{word_i=H}.

These labels are folded-position labels. Define

    lambda_k=(x_k-x_{k-1})/h, 1<=k<=7,
    lambda_8=(h-x_7)/h,
    Lambda4=lambda_1+lambda_3+lambda_5+lambda_7.

The weights are nonnegative and sum to one. Throughout every such closed
chart,

    E >= c Lambda4
          + (1/4) sum_{i<j}(x_j-x_i)(h-x_j+x_i).       (SC)

Proof. Vertex k of the simplex has x_i=0 for i<k and x_i=h for i>=k.
The point x is their convex combination with weights lambda_k. At odd k
the two frame counts are 4+4; at even k they are 3+5 or 5+3. This follows
from the bounded occupancy walk: after an odd step its height is four,
and after an even step it is three or five. Consequently the vertex
values of W are W0+c at odd k and W0 at even k.

For each fixed pair the folded chart keeps its angle difference in one
closed interval on which the signs in its support width are fixed.
Within that interval

    w''(delta)=-(|cos delta|+|sin delta|)/2 <= -1/2.

Thus w(delta)+delta^2/4 is concave. Its Jensen inequality yields

    w(mean delta)>=sum_k lambda_k w(delta_k)+Var(delta_k)/4.

For i<j the vertex differences have two values separated by h. The
variance is (x_j-x_i)(h-x_j+x_i). Summing gives (SC), with endpoint
validity supplied by the same concave functions or continuity. QED.

## 4. Quantitative 3+5 clustering

If E<=3/1000 for an actual M5 frame multiset, then after one common
rotation three chosen frames are within 1/200 radian of the standard
frame, and the other five are within 1/200 of a frame at 45 degrees,
modulo quarter-turns. The grouping need not be the initial L/H grouping.

Proof. For distinct simplex vertices with indices j,k put d=|j-k|.
The sum over pairs of the squared change in their angle differences is
h^2 d(8-d)>=7h^2. The sum of the variances in (SC) therefore implies

    E >= (7h^2/8)(1-sum_k lambda_k^2).

Choose k with maximal lambda_k. Since sum lambda_j^2<=lambda_k,

    1-lambda_k <= 8E/(7h^2).

Every folded coordinate is within h(1-lambda_k) of vertex k. With h>3/4
and E<=3/1000,

    1-lambda_k < 16/2625 < 1/100,
    max_i |theta_i-theta_i^(k)| <= 8E/(7h) < 4/875 < 1/200.

The vertex cannot be odd, because then (SC) gives
E>=c lambda_k>(1/5)(99/100), contradicting E<=3/1000. It is therefore a
3+5 vertex. Rotate by an additional 45 degrees if needed so that the
three-label reference class is standard. QED.

## Scope and audit

These theorems hold for the full M5 frame domain independently of all
centers and owner choices. The companion GATE3B_M5_SURPLUS_CIRCLE_SPLIT.md
uses them to obtain an exact two-frame disk problem in LOW. HIGH remains.
No proof that disk containment forces low surplus is claimed.

The handoff's Fraction-only verify_m5_global_support_surplus.py was rerun
in this continuation. Its eight-word identities, 160 exact M5 frame tests,
32 outward-interval concavity regressions, host-square inclusions, true
vertex/pair checks, and non-M5 negative control passed. Those finite
regressions audit implementation; the continuous proofs are above.
