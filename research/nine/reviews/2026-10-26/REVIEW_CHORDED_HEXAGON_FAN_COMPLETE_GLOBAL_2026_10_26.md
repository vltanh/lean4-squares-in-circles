# Full independent review: the complete positive-chord hexagon fan

Reviewer: global_closure, separately from the author and root audit.
Date: October 26, 2026.

**Verdict: ACCEPT the complete original FAN.L12345 and FAN.ALL domains.**
No correction is required. The other chorded-hexagon graphs and coarse
C1.6.b0 are not closed by this source or review.

## 1. Exact source pins and original-parent contract

Read the complete source

    CHORDED_HEXAGON_FAN_COMPLETE_EXCLUSION.md

at SHA-256

    4a84373008fd18935cf67669033e2414e66133501ae1f4ffb7446ada7362bbeb.

Its whole both-axis dependency was separately read and accepted in
REVIEW_FAN_HUB_OWNED_ENDPOINTS_GLOBAL_2026_10_26.md, pinning

    CHORDED_HEXAGON_FAN_HUB_OWNED_ENDPOINTS_EXCLUSION.md
    26005cd9ccc9c71746200a33cae9ba0c0fd2cb8a7c9ca27c7a239fd0ede6e8aa.

I also read the actual original load cover
SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md, including its complete
fan row and Section 4.7, and the original LOAD_CONTRACT, FAN.COVER,
FAN.L12345 and FAN.ALL entries. The source concerns exactly the
exterior hexagon with all rim edges and positive chords {02,03,04}.
Vertex 0 is H. All five B_i are forced genuinely loaded: the endpoints
are true degree-two triangle tips and every internal degree-three
body has a neighbor touching both of its other neighbors. H is
physically clear because it touches five actual boundary bodies.

There is exactly one necessary load orbit, 12345, including all
graph-preserving dihedral images. The present proof retains all nine
positive edges, H's degree five, the three internal degrees three,
all physical masks and individual corner-weight endpoints, all
actual means, and the same three completion squares. Its owner
cover is exhaustive for that full original contract.

## 2. Actual normal order and full force equations

All five hub forces and all five complete circle resultants occur
in the displayed equations. Moving the moment center retains the
whole hub force and torque equations. The global resultant identity
comes from summing the original six-body component equations.

Every nonconsecutive boundary pair is physically closed-disjoint,
because an extra physical edge would close the existing five-body
path to a forbidden boundary cycle. In particular the two endpoint
contact sets are disjoint. At a hub point there can be only two
boundary neighbors, and any two there must be consecutive.

The actual outer face gives the hub spoke order and its two boundary
arcs. I checked the source's extension of monotone support-normal
order to coincident applications: each unchanged normal lies in
the neighboring square's inward tangent sector, whose interior is
disjoint from the other physical sectors. At a square vertex this
sector is precisely the inward right-angle cone, including weak
endpoints. Therefore those directions cannot reverse their actual
sector order. A corner-valued shared-side mean does not permit an
internal normal from the other arc to be inserted into the path's
ordered interval. This is the needed full coincidence treatment.

The complete corner/resultant-to-center bound and boundary center
separation also give strict circle-resultant order. Their positive
sum is zero, so every consecutive gap, including the closing one,
is strictly below pi. Endpoint proper concurrence is used only at
the true degree-two B_1,B_5 with their actual boundary neighbors.
The physical radial masks are retained and exterior concurrences
are never asserted to lie in their squares.

## 3. The whole hub-pocket lemma

Every point of any actual boundary unit has distance at least
r=R-sqrt(2)>=2-sqrt(2)>1/4 from O. The pocket lemma assumes a
single open half-plane containing both endpoint resultants and
the whole actual outer H arc, and a strict quarter-disk margin
for that arc.

For its actual geometric boundary, contact extremes are chosen only
within the unchanged physical H-endpoint contact sets, toward the
outer arc. They do not replace any force mean. Paths through the
open interiors of the two physically disjoint endpoints to their
gap-facing circle corners join that outer H subarc to give a simple
occupied crosscut. It and the actual closing circle arc form the
Jordan boundary of the hub pocket in the original exterior-face
order. Every piece misses the closed quarter disk: the H arc by
hypothesis, the endpoint paths by their actual boundary-body distance,
and the containing-circle arc by the original radius. Weak contact
subdivisions cannot enlarge its free region through occupied paths.

The separate auxiliary homotopy only has to avoid O. Every endpoint
square and its positive concurrence lie in the strict F_i half-plane,
since each physical corner z satisfies z.x>=R^2-R sqrt(2)>0 on that
whole square. The corner endpoint can move to R F_i/|F_i| within
the same own angular interval. Those disjoint ordered intervals
preserve the original closing-arc lift and add no winding.

The resulting loop lies entirely in the assumed strict v half-plane:
its H subarc, actual contact extremes, positive concurrence and
resultant points, their connecting segments, and the unique closing
minor resultant arc all satisfy v.x>0. The actual Jordan boundary
therefore has winding zero about O. Since the boundary itself already
misses the entire connected quarter disk, winding is zero on that
whole disk. Compactness gives a positive separation margin, so a
slightly larger disk also remains outside the bounded pocket.
Every whole pocket extra thus has distance strictly greater than
1/4. No concurrence-containment or convex-free-pocket assumption is
used, and the homotopy is not a physical motion of any square.

## 4. Exactly one hub-axis endpoint

After path reversal and one coordinate reflection, the other endpoint
is either the top-left or bottom-left H vertex. In both cases the
short hub arc confines every normal to a closed half-plane with a
strict endpoint contribution. Full positive hub balance excludes it,
including corner-valued means and coincident internal applications.
Thus the path follows the long clockwise arc.

The general boundary-edge moment lemma in
FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md Section 1 is genuinely degree-free
at the boundary pair; I read its full support-width proof. Clockwise
order gives a negative first-edge moment. The true B_1 torque equation
then gives p<0 for its top-side mean. Endpoint properness yields both
complete endpoint resultants strictly in the left half-plane, and the
whole outer hub arc has x<=p<0.

For a top-left endpoint, the outer arc's distance is minimized at
the original top mean and is at least r. For a bottom-left endpoint,
the top segment has the same property. If its vertical segment does
not cross height zero, its closest endpoint also has norm at least r.
If it crosses zero and |L|<=1/4, the two actual boundary contact radii
would force both h>1/2 and 1-h>1/2. The exact strict reserve comes
from (2-sqrt(2))^2-1/16>1/4. Thus |L|>1/4 in that last case. The
entire actual outer H arc has a strict quarter-disk margin, and the
hub-pocket lemma applies uniformly to this whole mixed owner family.

## 5. Both endpoint hub normals oblique

Their actual H vertices are distinct, because the endpoint boundary
bodies are physically closed-disjoint. Adjacent and opposite vertices
are therefore the complete geometric split. The source does not
import the different four-boundary-path endpoint-distance theorem.

The hub center bound is obtained from the full five-load equation:
normalize the original circle-corner weights to sum one, keep their
zero weighted vector sum, and use the actual contact/diameter bound
|z-c_H|<=3/sqrt(2). This gives

    R^2+|c_H|^2<=9/2, hence |c_H|<=1/sqrt(2).

It is valid for all internal degrees and all physical corner masks.

For adjacent endpoint vertices the short top arc is excluded by
full hub balance. One endpoint has horizontal coordinate of absolute
value at most 1/2 by the center bound. Its actual boundary radius
forces |h|>3/10. The negative sign would give |(c_H)_y|>4/5,
contradicting the same center bound. Hence the actual outer top arc
lies in y>3/10, and properness gives both endpoint resultants in y>0.
The pocket lemma applies.

For opposite vertices the source groups every original coincident
endpoint spoke before taking moment. I checked the diamond-side
determinants on both lower sides and the full lower-vertex normal
cone: they are weakly negative about p_1 and weakly positive about
p_5. The two complete moment equations make both endpoint-group
vertical sums nonnegative. Actual normal order then makes the first
left endpoint normal and last right endpoint normal have nonnegative
vertical components. This step does not discard a force at a
coincident port or pretend it is another degree-two endpoint force.

The center bound and actual port radii give strict positive horizontal
distances X,Y from O to the opposite ports. The lower H arc has the
same counterclockwise order as the physical boundary path. The
positive first boundary-edge moment and the true B_1 torque force
h>0. Properness places the two endpoint resultants in the strict
upper-left and upper-right quadrants. The outer arc through the top
H vertex therefore lies in y>0. Its two actual positive support
heights are at least r/sqrt(2)>=sqrt(2)-1>1/4, so every point of
the arc has the required strict distance margin. This completes
all oblique endpoint owners, including free, tip-owned, physical
radial, shared-neighbor and coincident-port cases.

## 6. Both axes and the complete physical routing of all extras

The separate fully reviewed owner source covers both-axis endpoints
with unrestricted internal normals. Its equal and opposite cases
are excluded; its adjacent case gives an actual pocket support above
2/5. This joins exactly with the one-axis and no-axis cases above.
No endpoint normal or side mean is changed during the join.

The actual fan has four triangular bounded faces, so the accepted
positive-chord central-capacity theorem gives zero central capacity
for the whole bounded free union. The four directly touching
boundary pairs have empty exterior unit pockets by the complete
occupied-crosscut and dilation theorem. The source explicitly
constructs the complete face cover by occupied paths through the
five original boundary bodies to their actual circle corners.
Those paths, the four triangular faces and four pair pockets leave
exactly the closing hub pocket. Every extra has connected open
interior disjoint from all occupied paths. Fixing a compact inner
square first gives the same face label at weak junctions; closure
routes the whole extra. Moving the auxiliary access path inside its
actual boundary body avoids every extra interior and does not
change its label. No positive chord is deleted.

All three original completion units are therefore in the hub pocket,
at strict distance greater than 1/4, and so are the five original
boundary units. For each unchanged convex square, its nearest-point
supporting line supplies the half-plane cap premise of
GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md Section 1 with height equal
to that strict distance. Each of these eight squares contributes
an open-interior radius-5/4 arc longer than pi/4. Disjoint square
interiors make those eight arcs disjoint, contradicting their total
length exceeding 2pi. The complete nine-square contradiction follows.

## 7. Exact comparisons and original gate conclusion

I independently checked the elementary rational/radical reserves:

    91^2-2*64^2=89>0,
    283^2-2*200^2=89>0,
    23/4-283/50=9/100,
    (4/5)^2-1/2=7/50>0,
    2-(7/5)^2=1/25>0,
    49-48=1>0,
    9/2-2^2=1/2.

The equality 23/4-283/50=9/100 is used only after the strict radical
bound sqrt(2)<283/200, so it gives the needed strict h^2>9/100.
The source's lower-radius join retains the already accepted global
nine-square radius-two exclusion; the current proof does not try to
derive R>=2 from this six-body component alone.

The exact original parent join is now valid:

| Original gate | Full domain supplied by the reviewed source |
| --- | --- |
| M6.B6.HEXAGON.FAN.L12345 | Every original graph-preserving pose, radius, endpoint owner, physical circle mask, zero individual corner weight, actual mean, internal degree-three force and three-extra placement for chords {02,03,04} and positive load set 12345. |
| M6.B6.HEXAGON.FAN.ALL | The original full load cover has only 12345; the three endpoint-owner counts 2,1,0 and their full geometric transitions are exhausted by the two reviewed manuscripts. |

This is a complete proof for those two existing original obligations.
It does not close any other positive-chord graph, exterior-pentagon
embedding, coarse C1.6.b0 row or unrestricted nine-square theorem.
No ledger or original identifier was changed by this review. No
Lean compilation, CI, numerical feasibility claim or remote mutation
was used.
