# Independent review: one-sign radial roof pocket is empty

Date: October 29, 2026 UTC. Reviewer: block_forests.

**Verdict: PASS, unchanged, for the complete frozen one-sign theorem.**
I am not a contributor to its target strategy or its proof. I read all
378 lines, all 405 lines of its operative capacity-one source, and the
full quantitative arc, physical support and original graph inputs used
below. I reconstructed the continuous physical proof and every entry,
mask, endpoint and whole-unit routing join. No repair or added premise
is requested.

Primary reviewed source:

    RADIAL_ROOF_STACK_ONE_SIGN_HUB_POCKET_EMPTY_2026_10_29.md
    SHA256 fbae486a8a481dffb3fee77d41712607d5ca57fb44fe4e3f728d7b14dec62eff
    14991 bytes, 378 lines.

Complete operative capacity source, also independently reconstructed:

    SHARED_TRIANGLE_HUBS_PARALLEL_ROOF_BOTH_EXTERIOR_POCKETS_CAPACITY_ONE_2026_10_29.md
    SHA256 ccc05fb4a7a8a633b9ba3abf5ad8712f71c50e2f754b75c1b5847297e5e5b1e5
    18880 bytes, 405 lines.

The primary conclusion is that the actual upper pocket is empty for
h>=0, and its reflected lower pocket is empty for h<=0. Together with
the complete individual capacity-one result, the two shared-hub pockets
have combined capacity at most one. The stated original application
is the positive-length shared A--D, parallel-roof feature in D02.L135
and D02.L1345. This review does not itself supply the further central
and B--N--C allocation theorem or close either original full load row.

## 1. Complete physical statement and original-data preservation

Both physical theorems use actual interior-disjoint closed unit squares
in the unchanged disk with 2<=R<=sqrt(1105)/16. Put

    d=sqrt(R^2-1/4)-1, a=d-1,
    V=[d,d+1] times [-1/2,1/2],
    A=[a,d] times [h,h+1], -1/2<h<1/2,
    H=h+1, S=(a,H).

The actual B is physically on the containing circle, contains S,
intersects A only there, and satisfies min_B y>h and max_B x<d.
Its true positive degree, forces, circle coefficient mask and any
other contacts are unrestricted by the new force-free geometry.

The pocket is the actual upper bounded side of the occupied crosscut
from a V circle corner through (d,1/2), (d,H), S, to an actual B
circle corner, closed by its actual upper circle arc. A whole extra
means its connected open interior occupies that side and its entire
closed square stays in the closure. This is the correct object for a
packing-capacity result. No center-only assignment is substituted.

All extra contacts may be weak, no extra is assumed circle-loaded or
physically boundary, and every original application mean is retained.
Auxiliary separating axes used in the geometric proof do not alter
any original stress normal. In the D02 application all six original
component units and three original extras remain present.

## 2. Independent check of the operative capacity-one source

The fixed whole-B half-plane is valid at the entire radius and seam
interval. Its actual center c has

    |c_x|<31/40, c_y>31/30,

from S in B, its half diagonal, min_B y>h, and actual circle contact.
The estimate

    5x+14y>1271/120-sqrt(221/2)>0

holds at every actual B point, not merely at the contact or center.
Every B circle corner has positive height greater than sqrt(7)/2,
because every B point has |x|<3/2 and positive y and R>=2.

I checked that either original V corner and every B corner determine
the stated simple occupied crosscut. V and B are closed-disjoint;
the A/B intersection is exactly S. The top and right A segments
retain positive lengths because the seam interval is strict. Both
circle endpoints lie in the fixed open positive semicircle for
(5,14), and the B endpoint follows the V endpoint in its unambiguous
upper angular lift. Thus the complete loop lies in that half-plane.

Every loop point has norm strictly greater than 1/2: A's pieces have
x=d>9/10 or y=H>1/2, and points of either actual boundary unit are
at least R-sqrt(2)>1/2 from the origin. The negative half-plane ray
puts O on the unbounded side. The connected closed half disk is
disjoint from the loop and lies on the same side. Consequently the
whole bounded pocket has strict half-disk clearance. This applies
to the entire extra, including any boundary contacts by closure.

The sharp arc theorem applies to every such actual extra at radius
5/4, whether physically boundary or clear. Its full angular measure
is at least Lambda, and the separate exact estimate gives Lambda>4/5.
B has the same clearance and bound. Two hypothetical extras and B
would therefore contribute more than 12/5 inside one fixed open
semicircle. The actual radial V contributes the explicit clipped
interval of length asin(2/5)+atan(5/14)>3/4 in that same semicircle.
The four actual open-square circle sets are disjoint. Their total
would exceed 63/20>22/7>pi, which is impossible.

This is a whole-arc measure sum; it makes no unsupported inference
from center angles to arc endpoints. I read the full sharp theorem,
including its outer-face and weak-clearance residue, and the exact
Lambda>4/5 proof. The latter constant is independent of physical
boundary status, as required for the arbitrary extras. Thus both
individual pocket capacities are available at the stated scope.

## 3. Every B circle corner is higher than S when h>=0

Now H>=1. The complete bounds -1/15<a<1/60 and
14/15<d<61/60 are valid at both radius endpoints. The same center
estimate makes every B point have positive height. If an actual B
circle corner z had z_y<=H<3/2, then R>=2 forces

    z=(-A0,b), A0>sqrt(7)/2, 0<b<=H.

The alternative positive x is excluded by max_B x<d. Its actual
horizontal displacement to S is A0+a>5/4.

At the physical circle corner, both inward orthonormal B axes have
dot product with z at most -1/2, from containment of the adjacent
corners. Write S=z+alpha*u+beta*v with alpha,beta in [0,1]. If both
axes have nonpositive vertical component, the nonnegative vertical
displacement to S can use only a horizontal edge, so horizontal
displacement is at most one. This includes the horizontal endpoint.

Otherwise an upward inward axis must have positive horizontal
component, by the circle inequality. It is u=(C,s), C,s>0, and
the other permitted axis is necessarily v=(s,-C). The other choice
(-s,C) has positive dot product with z. Actual membership then gives

    alpha*s-beta*C>=0,
    A0+a=alpha*C+beta*s<=alpha/C<=1/C.

But S.u=z.u+alpha<=1/2 and a>-1/15, H>=1 imply
s<17/30 and C>4/5. Thus A0+a<5/4, a contradiction. Every side
or corner placement of S is included by alpha,beta. This proves
z_y>H for every physical B circle corner; no positive corner-weight
choice is made.

## 4. Complete whole-pocket routing and separating-axis cover

With the upper V corner, every occupied loop piece of height below
H has x>=d. The B segment lies at or above H by the preceding
corner theorem. The same conclusion holds for the upper circle
arc: below H it is on the right side and has
x>sqrt(R^2-H^2)>sqrt(7)/2>d. Hence the loop misses the open quadrant

    x<d, y<H.

Every point of that quadrant reaches infinity horizontally to the
left without crossing the loop. It is wholly on the unbounded side,
so the whole bounded pocket and every actual extra avoid it.

For the original lower V circle corner, the difference of the two
bounded regions consists, outside the occupied V, of the outer
circular cap at x>d+1. Its horizontal width R-(d+1)<1 cannot
contain a unit. The open interior of an extra cannot pass between
this cap and the upper free component through the occupied V or a
circle corner. Connectedness therefore places its full interior
in one component, and closure retains its full square there. Both
original V-corner choices consequently give the same necessary
quadrant avoidance for an actual extra.

I checked the finite-axis separation argument carefully. Separating
the actual square E from expanding rectangles [-M,d] times [-M,H]
uses only the two rectangle axes and the two E axes, with signs.
One axis occurs on an unbounded subsequence. Any negative component
would make the rectangle's maximum projection unbounded, so the
retained direction n=(c,s) has nonnegative components and satisfies

    min_E n.z>=d*c+H*s.

Weak side and vertex separations are included. No limit of changing
square frames or selected stress normals is taken.

The universal support cap is rederived correctly: the farthest actual
corner gives R^2>=|c_E|^2+|c_E|+1/2, hence |c_E|<=d+1/2.
The half-width in any unit direction is at least 1/2, so every
minimum support is at most d. Equality in direction n forces the
unique actual radial S square in that direction. Thus East would
make E equal the occupied V and is impossible; North gives
min_E y>=H directly.

For the remaining strictly positive E-own-axis direction, H>=d is
impossible. If H<d, the exact separation inequality gives

    c<=(d^2-H^2)/(d^2+H^2)<121/7321<1/60,
    min_E n.z>H>=1.

Its two actual far-side vertices have n coordinate at least two,
so the entire transverse interval has absolute value at most 9/16.
This makes max_E x<1073/1800<3/5<d. Quadrant avoidance now forces
the entire E above y=H in this final orientation case also.

The resulting necessary conditions are E subset {y>=H}, H<=d.
For d<1 they are already impossible. The remaining interval includes
the exact endpoint d=H=1: the argument did not assume d>1 or h>0.

## 5. Actual far-wall geometry forces a fixed rectangle inside E

For E above H>=1, let its unsigned vertical own-axis projections
be C>=s>=0. Its center height and the center cap give

    1<=C+s<31/30.

The complete monotone bound yields s<1/10, then
s<61/1782<7/200 and C>999/1000. This includes s=0 and both
actual tilt signs. The upper almost-horizontal edge has two corners
of heights at least 1+C>1999/1000. Each has horizontal absolute
value less than 567/1000 by actual disk containment. Their separation
is C; hence their midpoint and then the actual center give

    |(c_E)_x|<17/200,
    H+1/2<=(c_E)_y<=d+1/2.

For every point of the closed rectangle

    K=[-7/20,7/20] times [H+3/50,H+47/50],

the horizontal and vertical displacements from that same center are
less than 87/200 and 137/300. Projecting onto both actual E axes
gives strict own-coordinate bounds below 1/2. Thus the whole closed
K lies in int E, including both horizontal endpoints and both
vertical edges. This is a genuine interior rectangle of the actual
unit, not a substitute pose or an assumed orientation.

## 6. Complete B/E separation contradicts B's physical boundary contact

Any two actual convex units with disjoint open interiors admit a
weak separator g, oriented so max_B g.z<=min_E g.z. Since S is
in B and the compact K lies strictly inside E,

    g.S<=min_E g.z<min_K g.z.

The strict second inequality remains valid even if the actual B/E
separation is a side contact or a vertex contact. If g_y<=0,
the explicit rectangle minimum gives a nonpositive, in fact strictly
negative, difference from g.S. Therefore g_y>0. Its bottom side
then forces

    (7/20-a)*|g_x|<(3/50)*g_y,
    |g_x|/g_y<9/50, 1/g_y<51/50.

The actual E support cap gives max_B g.z<=d. Every actual B point
has |x|<=a+sqrt(2)<43/30, since S belongs to that same B, and
y>h>=0. Consequently every B point has y<259/200 and

    |z|^2<(43/30)^2+(259/200)^2<4.

This excludes B's actual circle contact for every R>=2. It covers
the entire physical B, independently of its true degree, selected
normals or circle load. The hypothetical E is therefore impossible.

## 7. Full original shared-hub entry and reflection

I independently reconstructed the complete entry in the capacity
source. At loaded true V2, the equal roof normals make its full
circle resultant a positive multiple of that direction. A unique
physical corner, or a physical two-corner mask with unequal weights,
makes the minimum support a unique V vertex. This includes either
individual zero coefficient. Both roof applications would coincide.

The positive-length A/D shared side gives identical frames. If the
roof direction were not their own axis, their coincident maximum
vertices would force identical centers. If it is their own axis,
their two maximum sides can meet only at a common endpoint without
interior overlap. The alleged singleton V contact would then use
an axis endpoint at an actual A or D vertex, contradicting the
unchanged strict point-only certificate convention. Thus the entire
common-application mask alternative is excluded before the actual
radial S roof and equal positive circle weights are derived.

For the radial roof, a nonaxial identical-frame A/D stack would put
their distinct roof vertices at distance sqrt(1+delta^2)>1 on V's
unit inner side. Hence the shared pair has exactly the aligned
stack chart. The seam endpoints h=+/-1/2 are excluded by the same
original singleton convention. All original roof and shared-side
means remain in their full closed intervals, including permitted
coincident roof means in the radial mask.

The full unloaded A3 and D3 force equations give the strict outward
return vectors (-mu,gamma) and (-nu,-gamma). Their actual vertices
are S_B=(a,h+1), S_C=(a,h-1). The complete strict support-span
lemma gives max_B x<d, min_B y>h and the reflected C bounds.
This uses actual support geometry and does not delete any B or C
force. Both actual return units are physically boundary in the two
original D02 load rows.

Reflection y to -y exchanges the two real hubs and sends the lower
pocket seam h to the upper pocket seam -h. Thus h>=0 empties the
upper pocket, h<=0 empties the lower pocket, and h=0 empties both.
The other pocket, when present, has capacity at most one by the
complete input checked above. The combined bound is therefore one.

The original substitution A=0, D=2, V=1, B=5, C=3, N=4 has the
required actual degrees and loads in both L135 and L1345. In the
latter N is genuinely loaded and is never used as a transmitter.
The exterior-loop correspondence retains physical circle corners
and all zero-stress contacts. Other AD features and nonparallel roof
forces remain outside the present theorem, exactly as stated.

## 8. Exact checks, pins and review boundary

I independently recomputed all displayed new reserves and the operative
capacity constants with exact fractions. Selected checks are:

| Comparison | Exact value |
| --- | --- |
| low radius bound for d | 11/900 |
| high radius bound for d | 31/57600 |
| circle-corner displacement comparison | 59/3600 |
| 1/60-121/7321 | 61/439260 |
| 3/5-1073/1800 | 7/1800 |
| 7/200-61/1782 | 137/178200 |
| 1-(7/200)^2-(999/1000)^2 | 387/500000 |
| far-edge corner radius comparison | 867/800000 |
| first rectangle own-coordinate reserve | 2941/60000 |
| second rectangle own-coordinate reserve | 3373/120000 |
| (51/50)^2-[1+(9/50)^2] | 1/125 |
| whole-B radius-two reserve | 96671/360000 |
| prior fixed-half-plane comparison | 24241/14400 |
| prior V-arc x-bound | 251/900 |
| prior clipped V arc above 3/4 | 2701/1029000 |
| prior 63/20-22/7 | 1/140 |

All operative pins match the current exact source bytes:

| Complete input | SHA256 |
| --- | --- |
| SHARP_QUARTER_CLEAR_RADIUS_FIVE_QUARTERS_ARC_AND_INTERVAL_CAPACITY.md | bca528af5320cc8314839eb0d53cf6f15ec381ac42d5bd353f62a27a47101f67 |
| BOUNDARY_UNIT_CENTERED_RADIUS_FIVE_QUARTERS_ARC.md | a431e5073be53ccc82dfc0e9924ca55db2cd51f53cbef1dad52fd90d890116e1 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |

This is a full noncontributor mathematical PASS for the new one-sign
emptiness theorem and its operative individual-capacity joins. No
source bytes were changed. No pose sample, orientation grid, numerical
packing certificate, original normal reselection, mean movement, force
deletion, unit contraction, Lean/Lake invocation, CI, ledger mutation,
commit, remote action or merge was performed. Root adoption and any
further original-region allocation assembly remain separate steps.
