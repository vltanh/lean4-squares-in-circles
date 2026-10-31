# Independent review: two parallel roots with outer radial leaves

Date: October 27, 2026.

Reviewer: triangle_bridges, independently of author hexagon.

**Verdict: ACCEPTED in full.** I read the complete physical capacity
source and its complete forty-degree arc prerequisite, including the
restored one-eighth outer-face calculation. I found no mathematical
gap, mask restriction, missing side endpoint or original-domain
substitution. No correction was requested.

## 1. Exact reviewed texts

| Source | SHA256 |
| --- | --- |
| TWO_PARALLEL_ROOTS_OUTER_RADIAL_LEAVES_CAPACITY.md | be87f34b2c973138703e1ea63fb4d33221e530057f7446babcd1917467c4769e |
| FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md | 5c0da36441613ccf2e3ce75a669ca1b212589788442e56b007a33a32d5131517 |
| NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md | 4930d66aaeb88b786bd010469636f5e25684d0e266f9af90ccc0fbe694d81366 |
| ADJACENT_S_LEAF_C4_PARALLEL_ROOT_LEAF_REDUCTION.md, exact strict/strict caller | 702eba704af93e67b85b9101a947ae5b3fe9134e194de64d87e5820e9fcc379b |

The first source is the new theorem under review. The two arc sources
were read in full to check the actual connected-arc scope rather than
assuming it from an abstract. The final source was read in full, and
its strict/strict chart is exactly the physical caller used here; this
review does not independently replace a separate review of every
other reduction in that source.

## 2. Full original physical statement and clearance

The theorem uses four actual squares: two adjacent parallel roots
and their two actual radial S leaves. The root charts are the
unchanged actual rectangles, with common support h and genuine
outer lower points of the same norm d. The new premise is precisely
min(v,w)>1/8. It imposes no orientation or force condition on any
additional square, in particular on the original C,D.

I checked that their union contains the entire rectangle
[-X,Y] times [-min(v,w),1-max(v,w)], which contains the closed disk
of radius min(v,w). The upper clearance exceeds that radius since
max(v,w)<4/15 and min(v,w)<4/15; both horizontal margins exceed
59/60. This is a statement about the actual two tiles.

The argument for a closed point of another unit inside that disk
is valid, including a point on the common A/B seam. Every
neighborhood in the disk contains interior points of at least one
tile. An interior point of the other unit arbitrarily close to the
proposed closed point therefore gives a genuine open-interior
overlap. Hence every additional unit has distance at least
min(v,w), strictly larger than 1/8. No unsupported equality case
of the connected-arc theorem is imported.

## 3. Independent check of the full forty-degree arc prerequisite

The prerequisite uses only signs and order of actual own axes,
keeping the original circle origin. Its coordinates a>=b>=1/2
and a^2+b^2<=1105/256 cover every orientation and center.

For a>9/8 I checked the fixed-q convex expansion
A^2+B^2+2*sin(delta)*A*B. Enlarging the parameter interval to
b=1/2 and a=b is valid. The complete endpoint bounds are respectively
97/144 and 72897/100000; both lie below 29241/40000.
The smaller exact reserve is 411/200000. The sign of the
negative cross term at b=1/2 is correct because A>1/8 and
sin(delta)>3/5.

The resulting squared inequality gives alpha-beta>delta without
assuming A+sin(delta)B positive. I checked beta+delta belongs to
(0,pi/2) before cosine inversion. The other three endpoint
differences follow from the actual half-angle and unit-strip
bounds, including b=9/8 and b>9/8. Thus the full open intersection,
not an arbitrarily chosen subarc, has length greater than delta.

For a<=9/8 the strict distance hypothesis forces both inner
coordinates positive and a>13/12. I checked all four endpoint
differences in the actual first-quadrant interval. The two outer
faces use the exact sine lower bound 59/81>sin(delta), and the
difference is within the stated monotonicity interval
[-pi/2,pi/2]. The a=9/8 and b=9/8 boundaries remain covered.
No extra component is hidden at either outer face.

Finally the actual incircle argument places the center-direction
radius-9/8 point in the open interior, using
5/8<|c_E|<91/60. The exact farthest-corner reserve at 91/60 is
31/57600. The strict threshold is retained; the source explicitly
does not extend connectedness to distance exactly 1/8.

This supplies the full force-free, arbitrary-orientation connected
arc of length greater than 40 degrees required by the caller.

## 4. The complete occupied root and leaf arcs

I independently recovered the root intervals
[pi-eta_A,pi-theta_A] and [theta_B,eta_B] from all four actual
sides. A negative-y circle point is impossible because

    (9/8)^2-(61/60)^2-(4/15)^2=2317/14400>0.

The wrong-sign x quadrants also have norm below 9/8. On the
remaining quadrants the shallow inner sides are inactive, and the
outer vertical and upper horizontal sides give precisely the
stated endpoints. The positive lengths follow from the actual
upper outer corners; no occupied part is omitted. I checked the
strict theta<30 degrees and eta>30 degrees comparisons.

The two equal genuine radial identities imply
d^2>65/64 from v,w>1/8. Therefore the actual leaf transverse
sides are strictly inactive on the entire radius-9/8 circle
intersection. Its complete closed leaf arc is exactly the
half-width-alpha interval in the real leaf direction. The outer
normal side is also inactive. This is the actual leaf square,
not a force resultant or a selected subarc.

I checked phi_A,phi_B<alpha via rho*X,rho*Y>d^2; the precise
rational reserve is 523/7200. The bounds on phi and alpha
also fix the circular order and include all possible weak
root/leaf junctions.

## 5. All complementary gaps and the exact bottom estimate

The four displayed gap lengths are the complete circular
complement of the four actual occupied arcs. In particular,
the right leaf arc wraps across angle zero; its upper endpoint
alpha-phi_B gives the stated right gap. The left side has
the reflected expression. Actual disjointness supplies the
nonnegative gap ordering, so a zero or absent gap creates no
additional available region.

The side gaps are strictly below 30 degrees and therefore cannot
contain a required arc longer than 40 degrees. The top gap is
strictly below 120 degrees.

For each bottom endpoint I checked the full bound

    cos(phi+alpha)
       <122/135-16/305
        =1402/1647<6/7<sqrt(3)/2.

The transverse radical lower bound has exact squared reserve
581/360000. The difference 6/7-1402/1647 is 68/11529.
The relevant sums belong to (0,pi/2), so the cosine inversion
is justified. Each sum exceeds 30 degrees, giving the complete
bottom gap length strictly below 120 degrees.

## 6. The capacity count and exact adjacent-C4 scope

The interior arc of any additional actual unit cannot cross a
closed occupied arc, even at an endpoint: its open neighborhood
would meet the other square's actual open interior. Because its
complete radius-9/8 intersection is connected, it lies in a
single one of the four actual gaps.

Neither side gap can hold one such unit. Each top/bottom gap
can hold at most two, since three disjoint open arcs longer
than 40 degrees exceed the entire gap. Thus there are at most
four additional actual units.

For the original adjacent-C4 strict/strict caller, the four
specified units are A,B,L,M and five further original units
remain, including C,D and all three completion squares.
The theorem therefore excludes the whole declared
min(v,w)>1/8 domain without assigning any degree, mask or
orientation to C or D and without using their mutual edge.

The source correctly retains min(v,w)<=1/8 and horizontal
genuine-leaf charts as separate domains. It makes no premature
whole high-LCD.SS or coarse-cell claim. This complete physical
capacity result and its exact original caller are independently
accepted.
