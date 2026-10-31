# Root review: occupied side-cap proximity and the complete simple C6

Date: October 26, 2026.

**Verdict: ACCEPT the complete whole-channel proximity theorem, both
original four-load completion joins, and the full simple-C6 assembly.**
This is a full source and original-domain review, not an acceptance from
the arithmetic reserves alone. The positive-chord six-body families and
coarse C1.6.b0 remain open.

## 1. Exact reviewed source and retained domain

I read all 469 lines of
FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md, SHA-256

    d7a1b864c2e7c1b3a00998b80e157a822e224aba4478fb3ed7e2df93371e2afb.

The source keeps an original entire simple positive cycle with at least
three positive circle loads, an actual unloaded degree-two side channel,
all physical endpoint masks, individual zero weights, genuine side means,
transverse sliders, the whole actual exterior pocket and arbitrary extra
orientation. Its radius interval is the full 2<=R<=sqrt(1105)/16.

The proof concludes that an occupied side cap forces the unchanged
transmitter's outward side to have height at most
D=sqrt(R^2-1/4)-1, and therefore dist(O,U)<1/60. It does not infer whole
vertical separation of the extra and transmitter. That distinction is
essential: the center-cover proof includes extras whose lowest point
could lie outside the channel strip.

I checked the original channel hypotheses in
GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md, including the precise
unique-mask proper-concurrence use. I also checked the port and angular
lemmas in SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md,
the actual ring and central-extra hypotheses in
SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md, the complete pair
join in FOUR_C6_LOADED_INTERMEDIATE_SIDE_PATH_DIAMETER.md, and the
six-orbit cover in SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md. The cited
previously accepted diagonal and five-load assemblies retain their full
original scopes; the new source does not remove their force hypotheses.

## 2. The radial point is inside the original extra

The sharp center bound is |c_E|<=M=D+1/2. Since the whole actual cap is
in y>=h, its center height is at least h+1/2>4/5. For any

    D<rho<min(v+1,41/40),

the point rho*c_E/|c_E| differs radially from c_E by less than 1/2 in
both directions. The lower-side estimate uses M-rho<1/2; the upper-side
estimate uses rho-|c_E|<9/40. Thus it is in E's open incircle, including
the extremal case |c_E|=M. No radial boundary endpoint is silently treated
as an interior point.

The point's height is strictly above h and below v+1, so it lies strictly
between the transmitter's horizontal sides. A point of E's open interior
cannot lie even on either vertical side of U: its neighborhood would
meet U's open interior. It is therefore strictly left or strictly right
of the full transmitter strip. The sign of the fixed center determines
one consistent alternative for every sufficiently small rho-D.

Taking the scalar limit rho down to D gives exactly x/|c_E|>=a/D.
It does not move any original square or contact. Positivity of the extra
height makes a<D strict and converts that angular inequality into the
closed convex sector in Section 3.

## 3. Complete original endpoint-mask cover

For an endpoint owning the channel side axis, the full mean interval is
retained. The outer vertical side lies beyond radius41/40, and

    B^2-(D^2-a^2)=2(D-a)+1/4>0.

Thus the same radial point, for rho sufficiently close to D, is strictly
inside the endpoint as well as E. Both the upper and lower horizontal
sides are checked, including a mean at a side endpoint.

For an oblique endpoint I reconstructed the four actual vertices and
the own coordinates k=-ac+ht, j=at+hc. Since j>0, the physical farthest
corner is exactly the adjacent corner for k>=1/2 or the opposite one
for k<=1/2. The physical radial tie k=1/2 is assigned to the adjacent
case. Its exact circle equation yields j<=D and

    |p|^2>=D^2+1/4.

The candidate radial point is strictly farther horizontally and
vertically than p, which contradicts this inequality as rho decreases
to D. This treats the radial mask without an inside-body concurrence.

Only the physically unique opposite corner remains. Its genuine
degree-two proper concurrence lies inside the endpoint on the positive
ray of its actual circle corner, at height h. Its ray factor is at most
one by circle containment. Hence the farthest corner has height at least
h, giving c>=t. The actual endpoint center consequently has exactly the
form (a+w0,B0), with 1/2<=w0<=1/sqrt(2), h<=B0<=h+1/2 and norm at least
R-1/sqrt(2). No physical radial tie or higher-degree endpoint is assigned
this unique-tip equation.

## 4. The continuous center cover

The candidate center set is the compact convex intersection of the
radius-M disk, the upper half-plane y>=H and the angular half-plane
x>=ay/sqrt(D^2-a^2). Its boundary is precisely the two straight segments
and one first-quadrant circle arc between the three displayed points.
Squared distance is convex on the segments and strictly convex in the
arc angle, since the endpoint center has both coordinates positive.
Convexity also bounds all interior points by the boundary. Thus the
three-point reduction covers the entire region, including degeneracies.

At the cone endpoint, the actual horizontal and vertical gaps are
nonnegative. Replacing w0 by 1/sqrt(2) and lowering B0 to the displayed
norm-constrained value therefore increases the distance. This lower
height is indeed no larger than the actual B0, because increasing the
horizontal coordinate relaxes the lower norm constraint.

On the initial a interval, the relaxed endpoint has fixed norm r0 while
the candidate has fixed norm M>r0. Their angular difference is positive.
Its derivative has the sign of

    D^2-r0^2+1/2+2a/sqrt(2),

which is strictly increasing. It has at most one change from negative
to positive, so the angular difference and distance reach their maxima
at the two stated endpoints. On the remaining a interval, both positive
coordinate gaps decrease. This establishes the full continuous reduction;
it is not a choice of diagnostic poses.

I independently expanded the two squared radical inequalities G_k and
checked the adverse signs of each substitution. G_k decreases with s and
T, and its derivative in R is greater than1183/1200 on both complete
radius bands. The thresholds z>7/12 and z>3/5 are therefore uniform, with
strict reserves at the lower radius endpoints. The low-band and high-band
distance bounds are below one by17111/1440000 and1/45000, respectively.
The a=0 comparison has the claimed strict reserve as well.

For the horizontal arc endpoint, the horizontal gap is below4/5 in both
orders and the vertical gap is at most1/2. For the lower sector corner,
H>=A gives squared distance at most3/4; H<A gives horizontal gap below
17/20 and squared distance below389/400. These cases cover both boundary
orders and the common equality H=A. Therefore every actual candidate
center lies strictly inside the radius-one disk about the actual endpoint
center, contradicting disjoint open unit incircles.

## 5. Exact arithmetic independently reconstructed

A fresh standard-library Fraction calculation verified the following
21 positive quantities from the saved source and its immediate join:

| Quantity | Exact positive value |
| --- | --- |
| Center-radius comparison | 31/57600 |
| D>9/10 squared reserve | 7/50 |
| T>19/10 squared reserve | 7/50 |
| R<21/10 squared reserve | 599/6400 |
| Lower M-r0 bound | 53/390 |
| Initial endpoint square comparison | 2753/25200 |
| G_k derivative floor | 1183/1200 |
| sqrt(15)/2<31/16 squared reserve | 1/256 |
| T(51/25)<989/500 squared reserve | 221/250000 |
| Low-band M<37/25 comparison | 11/1250 |
| sqrt(95)/12<13/16 squared reserve | 1/2304 |
| Low-band cone gap | 17111/1440000 |
| High-band cone gap | 1/45000 |
| Horizontal arc endpoint x bound | 107/3600 |
| Horizontal arc distance bound | 11/100 |
| Lower-corner a bound | 3/400 |
| Lower-corner horizontal gap | 49/7320 |
| Lower-corner distance bound | 11/400 |
| Central-extra proximity comparison | 1/1008 |
| G_(7/12)(2) lower value | 241/57600 |
| G_(3/5)(51/25) lower value | 1571/250000 |

All passed. These fixed arithmetic checks substantiate the displayed
analytic proof; they do not supply geometric coverage or a numerical
replacement for any physical premise.

## 6. Full four-load and simple-C6 assembly

The nine original physical squares give R>2 by the already accepted
measure theorem. Its finite certificate remains an inherited dependency;
this review does not declare it retired. The uniform center-diameter
theorems give central capacity one in each entire four-load orbit and
each original width pattern. Side caps have capacity one and diagonal
caps are empty. The only remaining three-extra allocation is therefore
one central and one in each of two side caps.

The new channel theorem places both actual transmitters within1/60 of
the origin. Their original horizontal port margins put every vertex
beyond7/100. The unchanged central extra is within1/40 of the origin
and has every vertex beyond19/300. Thus the three actual pairwise
interior-disjoint units meet D_(1/40) with every vertex outside D_(3/50).
The previously independently reviewed angular-measure lemma excludes
three such units. It covers all locations of O relative to each square,
so this join introduces no implicit origin-interior assumption.

Finally I checked the exact original six load representatives in the
no-chord row of the exhaustive cover. The three-load long-channel and
four-load adjacent-zero cases have their complete core exits. The full
alternating width/mask partition is exhaustive, with physical radial
masks determined by actual corners and individual zero weights retained.
The earlier five-load central-plus-cap join is complete. The two new
four-load joins fill exactly the remaining alternatives. Every actual
six-body component in this simple-cycle branch is therefore excluded
with its same three physical extras.

Exactly the two FOUR CAPS labels, the two FOUR parents, and M6.B6.C6.ALL
can close after separate independent acceptance. No fine label needs to
be invented. Positive chords retain extra forces and different genuine
degrees, so none of their families or coarse C1.6.b0 closes by this source.
The unrestricted theorem, every original equality packing and the older
full dependency audit remain separate obligations.

No Lean compilation, CI, workflow dispatch or merge was run.
