# Root review: occupied arcs and true gaps give the uniform cycle bound seven

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete frozen source, the force-free metric theorem,
the compatible cycle theorem and the stated full-force callers.**

The source was read in full and every step reconstructed:

`OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md`

- Size: 18,761 bytes.
- SHA256: `369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403`.
- Git blob: `19f068ec0c046073e04d461b6f9e57937c4155d1`.

The full occupied-arc input was independently read before the new source:
`CYCLIC_GLOBAL_CONTINUATION.md`, SHA256
`e319e541254f50aceff0d72775386187f1505a5edf817d7f3e5b10ce27bc4984`.
The input's Sections 2--4 are completely reconstructed in the new source;
its misleading word "inward" for axes is correctly replaced by "outward"
without changing the actual coordinate convention or any geometry.

## 1. The whole inner-circle intersection is one genuine occupied arc

For a square with an actual containing-circle corner, choose outward
own axes so the square is [a-1,a] x [b-1,b], with a>=b>=1/2 and
a^2+b^2=R^2. Comparing the two adjacent corners justifies the lower
bounds on both coordinates. The source retains the original disk
origin and does not translate the containing circle.

All loose rational bounds follow over the full stated radius window:
a>11/8, a<81/40, b<3/2, R<25/12. Thus the radius-5/4 intersection is
in the own right halfplane and is exactly

    [max(-alpha,beta), min(alpha,gamma)].

The positive-square bound (a-1)^2+(b-1)^2<2081/1600<25/16 makes
beta>-alpha. The full closed intersection is therefore one interval
[beta,min(alpha,gamma)], and its relative interior satisfies all
four original side inequalities strictly. Its endpoints are allowed
on actual square sides; no false endpoint-interiority claim is used.

At fixed q, the expression

    E=(a-1)^2+(b-1)^2+sqrt(2)(a-1)(b-1)

is convex in a+b. The source's two endpoint configurations exhaust
the allowed interval. At b=1/2 the increasing quadratic comparison
has upper value 933/1600<25/32. At a=b, the exact upper expression
(626-287 sqrt(2))/288 is below 25/32 because
401^2=160801<164738=2*287^2. Every squaring has positive sides.
The resulting strict inequality yields alpha-beta>pi/4.

The parallel-strip difference is nondecreasing for b>=1/2. Its minimum
is 2 asin(2/5)>pi/4; the b>=5/4 endpoint case is covered separately.
Hence the entire actual intersection has angular length greater than
pi/4, with no orientation mesh or optimization premise.

## 2. Actual corner order, compact trimming and the metric sum

Every actual outer-circle corner z has its radial point (5/(4R))z
strictly in the original square. In its own frame each inward
coordinate displacement is positive and at most R-5/4<5/6<1.
Thus the corner direction lies strictly inside the connected arc.

Likewise the center radius satisfies 5/4<|c|<91/60, so its radial
inner-circle point is within 4/15<1/2 of c and is in the open
incircle. This gives center order without importing a centered-arc
estimate or assuming that an arc is centered on the body direction.

One can trim arbitrarily small positive amounts from the two ends
of each full intersection, preserving length greater than pi/4 and
the designated corner and center directions in its relative interior.
The resulting compact arcs lie entirely in their original open square
interiors. They are disjoint, so their circular order agrees with the
chosen corner directions. All other corners of a square remain in the
same connected full arc, whose relative interior cannot intersect an
other square's interior arc; changing the chosen corner cannot change
the order. The argument includes squares with two physical circle
corners and zero selected weights.

For t selected boundary bodies, these trimmed arcs and the intervening
positive directed gaps partition the same inner circle. The gap's two
endpoints lie in the actual endpoint squares, so their chord is at least
the true set distance D_i. The directed circular arc length is at least
this chord even for a gap greater than pi. Consequently

    sum D_i <= (5/4) sum delta_i
              < (5*pi/16)(8-t).

The strict inequality comes from the genuine occupied lengths. Other
packing squares may meet the intervening intervals; the source does
not incorrectly call them empty physical regions. Theorem 1 is a
force-free metric theorem for any selected boundary units in their
actual circular order, whether or not consecutive units touch.

The exact elementary integral for pi<22/7 is valid, and therefore
5*pi/16<55/56<1. The proof requires no decimal angle approximation.

## 3. The compatible physical order is proved at its stated scope

The complete source again supplies the necessary cycle-order join.
Circle points have unique physical owners: sufficiently short radial
inward segments lie in the open square at any containing-circle corner.
The center-to-corner spokes are thus distinct and disjoint.

Each spoke meets the actual center-to-contact drawing only at its own
center. A coincident direction would meet the square boundary at the
same unique point and would make a contact occupy a uniquely owned
circle corner, which is impossible. The stipulated compatible local
resolutions can therefore preserve every marked spoke, including at
marked vertices with additional incident positive edges.

The selected simple cycle is a Jordan curve inside the disk. Each spoke
reaches the containing circle without another cycle intersection, so
its open part is in the cycle exterior. Disjoint annular spokes preserve
their cyclic order by cutting along one spoke and applying Jordan
separation. This proves cycle order equals actual boundary-corner order,
including the two-mark case. The proof assumes neither an origin inside
the cycle nor a convex force polygon.

This is an explicit compatible physical-embedding premise. Abstract
planarity alone is not substituted for it, and an independently chosen
planar translational stress is not identified with a torque-balanced
certificate.

## 4. Every genuine internal body pays a true set-gap cost

Common signed actual support normals telescope to

    n.(c_next-c_prev)=h_prev+h_next+sum_internal 2h_U.

For every pair of actual endpoint points x,y, their projection gap is
at least W_i=sum_internal 2h_U>=j_i. Thus the true set distance D_i
is at least W_i, not merely the endpoint center distance. No collinearity
of actual application means or restriction to side/diagonal normals is
needed.

Since m=t+sum j_i, the complete metric sum gives

    sum W_i < (5*pi/16)(8-t),
    m-t <= sum W_i < 8-t,
    m<=7.

First the nonnegative left side forces t<8, which justifies multiplying
8-t by a factor below one. There is no missing t>=8 sign case. No run
length bound is needed, making the theorem uniform across all load
counts, internal orientations and run placements.

## 5. Full-force callers, whole-family scope and limits

The only stress premise supplying the common normal is the complete
two-force equation at every genuinely unloaded true-degree-two internal
body of the same full retained graph. Extra marked chords and attachments
remain in their actual stars. A vertex with degree two only on a drawn
cycle cannot be used as a transmitter if it has another positive edge.

An entire positive simple component has at least two circle-loaded bodies.
The center-dotted force sum makes some circle weight positive; the full
force sum is zero; circle corners from a single physical boundary square
all have strictly positive dot product with its center. Thus a single
loaded body cannot support that sum. Marking the positive-load bodies
supplies the precise theorem caller.

For a displayed cycle with all physical boundary vertices marked, zero
or one mark is impossible if every remaining vertex truly has degree two:
common-normal telescoping around the closed run would give positive total
width and zero displacement. The broader marked chorded-cycle corollary
is therefore complete as stated.

This closes all compatible simple C8 and C9 components at once and every
such cycle with extra edges only at its boundary marks. A surviving C8
or C9 cycle must have a physically circle-clear branching vertex. The
source explicitly retains arbitrary chorded blocks, blocks with interior
vertices and repeated outer-face walks beyond this scope.

The seven-body record orbit has four marks and internal reserve three;
its required inequality is 3<5*pi/4 and is preserved. Every actual extra
square remains. No sharp seven-body completion bound or unrestricted
nine-square theorem follows from this cycle estimate alone.

No original inventory flag, common-selection gate or equality assertion
is changed by this review. The verification is a complete hand-proof
reconstruction with exact arithmetic, without Lean compilation, CI,
finite orientation search or a packing certificate.
