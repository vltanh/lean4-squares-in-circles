# The original C5 S124 root: exact moment transport and the remaining small domain

Date: October 27, 2026.

**Status: complete hand domain reduction, submitted for full root and
separate independent review.** This does not claim the whole original
gate closed. Its exact surviving aligned and tilted domains are
listed in Section 6. No positive edge or unloaded transmitter is
removed.

## 1. The entire original graph and all its actual data

Retain the same nine physical unit squares and their common compatible
selected certificate, with

    79/40<=R<=sqrt(1105)/16.

The complete positive component is the original simple cycle and leaf

    0--1--2--3--4--0,       0--L,

with genuine S leaf `L`, positive block loads at exactly `1,2,4`,
and true degrees

    0=3, 1=2, 2=2, 3=2, 4=2, L=1.

Body `3` remains its actual unloaded two-force transmitter, with its
actual width, normal, two applications and slider. The other three
physical units remain arbitrary and present. Every physical circle
mask, zero individual circle weight, actual shared-side mean,
selected positive force and zero-weight physical contact is retained.

Use the accepted same-nine `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md`
to reduce to `R>2`. Put

    d=sqrt(R^2−1/4)−1,       r=R−sqrt(2),
    14/15<d<61/60.

The actual genuine leaf has inner midpoint `d e`, outward radial
axis `e`, equal positive circle weights and positive circle resultant
parallel to `e`. Its root is physically circle-clear. Its full root
force and origin moment are retained throughout.

## 2. Exterior access and the original nonzero cycle moment

The actual cycle has the original positive plane embedding. Use its
center/contact strands with the compatible arbitrarily small routing
neighborhoods at weak junctions. The proof of
`D_LEAF_BOUNDARY_ROOTS_CYCLE_EDGE_EXCLUSION.md`, Section 2, uses
only this physical cycle and exterior access strands, not the D-leaf
force or its rectangular chart. The same routing proof therefore
applies to the present real S leaf and every actual boundary body.

For clarity, append an occupied interior strand from each chosen
physical boundary body to any chosen actual circle corner, and the
actual root--leaf strand to a leaf circle corner. Such a strand
cannot terminate in the bounded face of a loop contained in the
circle. Its open interior cannot cross another occupied strand, so
it is exterior access. Cutting along the real leaf access gives the
same linear order on the cycle and the remaining circle boundary.
Compact interior strands followed by the original arbitrarily small
routing neighborhoods preserve this conclusion at every weak
junction. No circle access is assigned to body `3`.

Orient the actual cycle consistently with the counterclockwise root
arc cut at the leaf. Its actual boundary edge `1--2` has positive
directed moment in the corresponding minor circle order, by the
degree-free boundary-pair moment theorem in
`FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md`, Lemma 1.1. The other circle
arc contains the real leaf; the actual boundary edge cannot skip
that boundary access. This is precisely the physical orientation
step in the cited cycle theorem.

If `M_i` denotes the magnitude times origin moment of the directed
force on cycle edge `i`, the original torque at every degree-two
cycle body gives

    M_i=M_(i−1).

At a loaded body all its actual circle atoms have zero origin
moment. At the actual unloaded body `3` the same equality is its
unchanged two-force torque equation. The genuine root leaf also
has zero origin moment. Thus there is one unchanged common value

    M>0.                                                (1)

For the first and last root ports in the actual counterclockwise
occupied-arc order, with original normals `n_1,n_2`, applications
`p_1,p_2` and positive magnitudes `mu_1,mu_2`, this gives

    det(p_1,n_1)>0,       det(p_2,n_2)<0,                (2)
    alpha e+mu_1 n_1+mu_2 n_2=0,
    mu_1 det(p_1,n_1)+mu_2 det(p_2,n_2)=0,
    alpha,mu_1,mu_2>0.                                  (3)

This does not turn `2--3--4` into a physical edge. The entire
original torque chain, including the actual means at body `3`,
supplies (1).

## 3. Every tilted high-coordinate root is excluded

For a tilted genuine root, choose its actual own axes and reflect
the entire chart if necessary so that

    H=[U−1,U] times [V−1,V],
    U>=V>0,       U^2+V^2=d^2,
    e=(U,V)/d.                                          (4)

The real leaf midpoint is `(U,V)`. Its root southwest quadrant
and the real leaf's northeast-facing half-plane leave only two
tangent gaps strictly smaller than a right angle. No third unit
can contain that point. It is therefore a legitimate cut of the
actual occupied root boundary.

The normals follow the usual counterclockwise convex-boundary
order. With `theta=arg(e)`, their actual lifts satisfy

    theta<arg(n_1)<=arg(n_2)<theta+2pi.                  (5)

The positive leaf-direction normal cannot be another contact:
the actual support point is the unshareable leaf midpoint.
Equations (2), (3), (5) are exactly the original ordered-moment
hypotheses of
`S_LEAF_ROOT_HIGH_COORDINATE_NORTH_SCREEN_EXCLUSION.md`, Section 5,
at its complete tilted-root scope. Its force-free physical screen
and its full true-S3 argument therefore exclude every

    U>4/5.                                              (6)

This includes origin-interior, origin-boundary and off-origin
tilted roots. No neighbor degree, force or circle mask is changed.

## 4. Exact central-capacity joins, including equality

Apply the two complete force-free theorems in
`SMALLER_CENTRAL_DISKS_NINE_UNIT_CAPACITY.md` to the actual root
in (4). They imply:

* `U<=77/100` is impossible throughout the original radius window.
* When `d<=1`, equivalently `R^2<=17/4`, every `U<=4/5`
  is impossible as well.

The hypotheses are literal inclusions of the corresponding closed
central disks in the actual root. The proof counts all eight other
original units. It retains the weak side-distance endpoints, and
does not assume their inner-circle intersections are connected.
In combination with (6), every tilted root at `d<=1` is excluded.

Consequently every surviving tilted root satisfies

    1<d<61/60,
    77/100<U<=4/5,
    3/5<V<2/3.                                          (7)

For the lower `V` bound use `V^2=d^2−U^2>1−16/25`.
For the upper bound use

    V^2<(61/60)^2−(77/100)^2<4/9.

Thus this is a genuinely origin-interior root, with every own
margin explicit. These comparisons do not replace the actual
radius relation in (4).

## 5. The complete root features and physical endpoint masks in (7)

The real root southwest vertex is ineligible as a boundary port:

    |(U−1,V−1)|^2<(23/100)^2+(2/5)^2
                         =2129/10000<r^2.              (8)

Here the high-radius floor gives
`r^2>=25/4−sqrt(34)>419/1000`. The strict northeast leaf
vertex remains unshareable.

The two root normals are nonparallel. A positive leaf-direction
normal is impossible; the parallel negative direction would put
both applications at the southwest vertex, already excluded by
(8). Projecting (3) onto `f=(-V,U)/d`, and using (5), therefore
gives

    f dot n_1>0,       f dot n_2<0.

The full root torque gives a common radial concurrence `q e`.
By the first actual moment in (2),

    det(p_1,n_1)=q(f dot n_1)>0,       q>0.              (9)

In fact `q<=d`. If `q>d`, it lies strictly above and right of
the actual root rectangle in both own coordinates. A direct
normal-cone check leaves only its northeast and southwest
vertices as possible actual applications of a normal line
through that point; no side-interior line can pass through it.
The former is unshareable and the latter is ineligible by (8).
This proves the upper bound without altering either mean.

The first root normal has positive `f` component. Northeast and
southwest have been excluded, and East, South and strict Southeast
have negative `f` component. If the first normal were North,
the full two components of (3) would force the second normal
strictly Southwest, contrary to (8). Thus the first normal is

    West, at (U−1,qV/d),
    or strict Northwest, at (U−1,V).                    (10)

The last normal has negative `f` component. West, North and
strict Northwest have positive component; the two other vertices
were excluded. East is also impossible: (10) has nonnegative
ordinary vertical component, so the full vertical equation in
(3), including the positive genuine-leaf component, cannot be
balanced by an East last force. Therefore the last normal is

    South, at (qU/d,V−1),
    or strict Southeast, at (U,V−1).                    (11)

All means in (10), (11) remain their original values. In
particular neither side has been replaced by its endpoint.

The first actual boundary port has norm no larger than the
northwest vertex. Its boundary-point lower bound therefore gives
the additional exact necessary inequality

    U<=(d^2+1−r^2)/2=:u_0.                              (12)

Equality is retained. The established full threshold computation
in `FOUR_CYCLE_TILTED_S_ARTICULATION_EXCLUSION.md`, Section 2,
has `3/4<u_0<4/5` and `d^2−u_0^2>1/4`; its proof is purely
the displayed radius relation and applies here unchanged.

Both actual root neighbors have exactly one physical circle
corner. Indeed `U,V>1/2` makes all three other root corners
strictly nearer the origin than its real leaf midpoint:

    |(U−1,V)|^2=d^2+1−2U<d^2,
    |(U,V−1)|^2=d^2+1−2V<d^2,
    |(U−1,V−1)|^2=d^2+2−2(U+V)<d^2.

Strict convexity of squared norm shows that the real leaf
midpoint is the only root point with norm `d`; every other
root point has norm strictly less than `d`. A unit with two
physical circle corners is an actual radial S rectangle, whose
every point has norm at least `d`. It could therefore touch
the root only at the unshareable real leaf midpoint. This is
impossible. The conclusion is about physical masks and retains
every individual circle-weight endpoint.

The names “first” and “last” describe the actual root arc, not a
new assignment of which endpoint has a boundary successor. The
original reflection of load124 is load134. Exactly one of those
root endpoints is adjacent along the cycle to the actual unloaded
body, and that true adjacency is retained in either orientation.

## 6. Exhaustive current original remainder

If the real S-leaf axis is an own root side axis, normalize it
East. The actual root is

    H=[d−1,d] times [h−1,h],       0<=h<=1.

For `d>=1`, the entire aligned root is already excluded by
`ALIGNED_S_LEAF_ROOT_TWO_BOUNDARY_NEIGHBORS_EXCLUSION.md`.
Its true degree-three and both actual boundary-neighbor premises
hold literally here, and it uses no force equation at those
neighbors. The entire remaining aligned domain is therefore

    sqrt(15)/2−1<d<1,       0<=h<=1,                    (13)

with its original full equations and all five cycle bodies.

For a tilted root, the only remaining domain is exactly (7),
refined by (9)–(12), the complete features (10), (11), and the
two physically unique root-neighbor masks. The middle loaded
body's physical mask is not restricted here. The actual unloaded
body's width, orientation and both original applications are
not changed or discarded.

This manuscript consequently does **not** close
`M6.B5L.C5.L124.S`. It closes complete original root domains
and records a much smaller exhaustive remainder. The nonzero
cycle moment and positive-concurrence consequences are available
for that remainder with their exact original hypotheses.

No ledger, roadmap, remote state, original atom or actual mean
is modified. No numerical pose, Lean compilation or CI result
is a premise of the proof.
