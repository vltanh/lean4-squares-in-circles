# Root review: two-channel capacity, enlarged junction margin and the actual force-line barrier

Date: October 30, 2026 UTC.

**Verdict: PASS for all three complete frozen sources, with the distinct
geometric, translational and angular scopes kept separate.** Root read
the entire manuscripts and reconstructed the proofs described below.
The main two-path proof is stronger than a stress theorem: its hypothesis
is an actual pair of vertex-disjoint common-normal contact paths.

## Frozen sources

| Source | SHA256 |
| --- | --- |
| TWO_LONG_CHANNELS_FORCE_CAPACITY_EIGHT_AND_FOUR_LOAD_CYCLE_REDUCTION_2026_10_30.md | `e05fa0520279d957659f694fdaa5b08be750a848d5117f3792df4399476354f5` |
| FOUR_SQUARE_JUNCTION_CAPACITY_EIGHT_WITH_ONE_FIFTEENTH_MARGIN_2026_10_30.md | `df237a44886f100d3fa901981c6c747b0dfa827d61ef4c1f046b476df1c1ada4` |
| LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md | `dd1d91f8e49f4a5f507a70b53a75a30b299757f9f04a0976da3e674674ae7b05` |

The endpoint covering and protected-ray inputs have the complete root
reviews in the preceding e88e848 checkpoint. The enlarged capacity proof
is self-contained, and is reconstructed here rather than inferred from
the earlier smaller coordinate margin. Independent current-source reviews
by agents other than the respective authors are recorded separately.

## 1. The two-path geometric theorem and its force-only caller

Support telescoping along a common-normal four-square actual path gives
endpoint center projection at least three. Consequently the endpoints
have signed projections beyond +/-89/60, and their halfwidths are each
less than 8/15. No assertion about the transverse positions of the three
means is made. In the stress caller only translational balance at the two
true unloaded degree-two internals is needed to supply the common normal.

I checked the complete distinct-body join. A long-path endpoint cannot
also be an unloaded degree-two body: extending through its other neighbor
would give either a three-internal path of center span at least four, or
a closed positive-width telescoping path. Both contradict the center
bound. The old endpoint-matching theorem makes different long endpoint
pairs disjoint. Their internals cannot be endpoints of the other path;
sharing an internal would propagate through its two true neighbors and
identify the same whole path. Thus different long endpoint pairs really
give eight distinct physical bodies. Parallel paths on the same pair
remain outside this conclusion.

All four endpoint radii lie between 89/60 and 91/60. The long-pair angular
separation exceeds 150 degrees, because its contrary would give squared
distance below 8281/960<9. Any two of the four endpoints are separated
by more than thirty degrees: the contrary bound is 8291/9000<1. If two
long pairs did not alternate, placing the other pair in an arc of length
less than 210 degrees and subtracting its two endpoint gaps greater than
thirty would give a long-pair gap below 150, a contradiction.

The protected outward rays are free of every other closed unit. Their
polar direction moves by less than fifteen degrees, so the four disjoint
angular intervals preserve the alternating endpoint order. Using an
auxiliary circle of radius three is a sound way to make all physical
contacts strictly interior without assuming any endpoint touches the
containing circle.

## 2. The topological crossing is an actual four-square contact

The route through successive centers and original actual means has
strictly increasing projection in its channel direction. Appending the
two outward spokes preserves that monotonicity, yielding a simple proper
arc of the auxiliary disk. The two proper arcs with alternating boundary
ends must intersect, by Jordan separation.

Neither an exterior spoke nor a non-mean point of a physical route can
be an intersection. A protected spoke misses all squares of the other
path and the other spokes. Every route point other than a mean is in an
open square interior, which cannot meet any other closed square. Thus
the intersection is an actual contact mean on each path and belongs to
four distinct actual squares. The local-angle argument makes these four
units one exact two-by-two block.

This checks the key boundary issue: the proof uses center-to-mean routes,
not a straight force line that could lie on an occupied boundary. It also
does not rely on an abstract planar drawing of the body graph.

Every four-square junction in the containing disk has norm below 19/20,
because its block's farthest corner would otherwise have squared norm
at least 1921/400>Q. Each outer path contact instead has signed normal
projection of magnitude greater than 19/20, from the endpoint and
halfwidth bounds. The common junction is therefore the middle contact
of both paths; its four units are precisely their four internals.

## 3. Near-axis inversion and the capacity contradiction

At that junction the two internal widths in either path agree, since
all four square frames agree. Writing m=|n_x|+|n_y|, the full support
identity gives 1+2m<91/30 and m<61/60. If a is the larger absolute normal
coordinate and b the smaller, the exact inequality a>=1-b/2 on
0<=b<=1/sqrt(2) gives b<1/30 and a>899/900.

If both channel normals were near the same block axis, their two distinct
positive-side endpoints would each have that coordinate greater than
79411/54000>22/15. The transverse bound in the normal frame, less than
one third, is used here; substituting the looser full center radius would
not justify the same comparison. The corresponding cap has squared
diameter at most 719/1200<1, contradicting physical center separation.
The two normals must therefore be near different block axes.

The actual middle support point obeys |p.n|<1/60 for each normal, by
retaining both internal widths and endpoint halfwidths. Taking the normal
near the coordinate where |p| has its largest coordinate gives

    max(|p_x|,|p_y|)<15/869<1/30.

This is a bound in the actual common square frame, without moving any
body or using torque to make a normal exactly axial. It supplies the
precise premise of the enlarged junction-capacity theorem.

That theorem works even for |p_x|,|p_y|<=1/15. Any extra center has
distance at least one half from the actual two-by-two block. A center
outside both coordinate intervals would exceed the center-radius bound
by at least 2251/3600 in squared norm. Every remaining center is in one
of four caps beyond 43/30, each with squared diameter at most
713/720<1. Thus the entire packing has capacity eight, including any
unstressed ninth square. At the sharper coordinate threshold 1/30,
the diagonal reserve is 2827/3600 and the cap bound is 719/1200.

I checked the eight-unit witness at squared radius 17/4. It supports
the stated sharp count and explains why an eight-body crossing alone
is not an exclusion. The main theorem retains the ninth physical unit
in exactly the step where it is needed.

## 4. The separate plane-selection statement is conditional on its embedding

The source's second theorem explicitly assumes the compatible local
center/mean embedding construction. With that premise its junction disks
and strand tubes can be chosen to avoid all four protected spokes, and
the same alternating-exit argument contradicts disjoint embedded paths.
This is a valid separate conditional result without a ninth-body premise.
It does not equate independently selected translational and angular
certificates or resolve their complete downstream compatibility audit.

The main geometric theorem and force-only corollary have no such embedding
premise. For four-load simple cycles, two long runs are excluded in all
placements by the force-only corollary. The author correctly retains the
remaining eight-body patterns (2,1,1,0) and (1,1,1,1), and the nine-body
pattern (2,1,1,1). Any later angular-budget closure needs its own order
hypothesis and current-source review.

## 5. The outer-strip and straight-line barrier proofs

The prior expanded-endpoint proof supplies the actual coupled height
bound |y_A|+|y_B|<=1/8 for any gap-two pair. If a different square met
the closed outer strip x<=-119/60, its center would have x<-191/150
and |y|<5/6. Its coordinate differences from A would be less than
one quarter and 23/24, so its squared distance from A would be below
565/576<1. Reflection gives the other strip. The calculation includes
closed contacts and uses no load or further-contact premise.

For the straight-line conclusion the source explicitly adds angular
balance at the two actual unloaded degree-two internals. Together with
translational balance this makes the original contact differences parallel
to the common normal. I checked the own-frame classification: the width
is one for an axis normal, or sqrt(2) when the opposite support vertices
have a difference parallel to the normal. A diagonal internal would make
the center projection at least 2+sqrt(2)>91/30. Both internals are
therefore side-normal and the three means are one unit apart on the
same original line.

The inward-normal chord lemma is valid at an arbitrary support point,
including a vertex. In each own coordinate subtraction by t*n, with
0<=t<=1, moves an exposed coordinate inward by at most one and leaves
a zero-normal coordinate fixed. The four actual units consequently cover
the line segment from q_1-2n to q_1+2n. Their middle-contact projection
has absolute value below 1/60, so this segment bridges both excluded
outer strips.

An extra square's open interior cannot cross that entire line. Inside
the strips it is excluded geometrically, and between them the line is
covered by the other actual squares. Convexity therefore puts the extra
wholly in one of the closed half-planes, with its interior in the
corresponding open half-plane. Boundary-only contact with the force line
is retained. This reasoning does not require the line to pass through
the interior of a channel square.

The actual covered endpoints give the sharp relation

    (2+|s|)^2+t^2<=R^2<=Q, hence |t|<=9/16.

I checked the stated local equality witness and the distinction between
its valid internal force/moment balance and any unasserted full endpoint
balance. Five actual extras split across the two half-planes, so one
side has at least three. A sharp triple-cap floor is not supplied by
this fact; the source correctly leaves that caller obligation open.

## 6. Verification and exact limits

All displayed rational margins and source identities were recomputed.
No pose sample, numerical mesh, Lean build or CI result is a premise.
The proofs cover complete continuous orientation and contact domains.
They do not close an original coarse parent, unrestricted optimality,
equality classification or G4.2.c. Parallel channels sharing one endpoint
pair and flexible internal heights are preserved; neither is replaced
by a solid four-square row.
