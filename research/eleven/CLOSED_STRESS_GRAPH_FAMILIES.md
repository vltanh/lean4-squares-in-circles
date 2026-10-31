# Stress stars and four-cycles are impossible below the eleven-square optimum

Use the sparse minimizer stress theorem and the independently certified
universal bound `q>9/2`. A retained connected stress core has the original
disk as its unique minimum enclosing disk: its normalized loaded corners
have weighted mean zero and weighted squared norm q. The following geometric
enclosing disks therefore exclude whole stress graph families.

The contact edges used here need only be physical contacts among the core's
actual squares; they need not all have positive stress weights.

## Any core with a spanning contact star

Suppose one core square touches every other core square. Let z be the hub's
center. For a leaf square choose a shared point P with the hub. Then
`|P-z|<=sqrt(2)/2`. Every point x of that leaf has
`|x-P|<=sqrt(2)`, the unit-square diameter. Hence

    |x-z| <= 3sqrt(2)/2.

The hub itself lies in the smaller radius-`sqrt(2)/2` disk about z. The entire
core consequently has an enclosing disk of squared radius `9/2`, contrary
to its minimum-disk identity and the universal strict lower bound. This
argument applies to a spanning star of any retained core size.

## A four-square core with a spanning contact cycle

Let A,B,C,D be the four center vectors in cyclic contact order. Adjacent
centers have distance at most sqrt(2): a shared point is within sqrt(2)/2
of each center. All distinct centers have distance at least one, by their
disjoint open inscribed radius-1/2 disks.

Put `L=|A-C|`, `M=|B-D|`, and `z=(A+C)/2`. The quadrilateral identity gives

    L^2+M^2 <= |A-B|^2+|B-C|^2+|C-D|^2+|D-A|^2 <= 8.

Since L,M>=1, it follows that `1<=L^2<=7`. The two opposite centers A,C
have squared distance `L^2/4<=7/4` from z. The parallelogram identity gives

    |B-z|^2 = (|B-A|^2+|B-C|^2)/2-L^2/4
             <= 2-L^2/4 <= 7/4,

and the same bound holds for D. Every square point is within sqrt(2)/2 of
its center. Thus the whole core lies in the disk about z of radius
`(sqrt(7)+sqrt(2))/2`, with squared radius

    (9+2sqrt(14))/4 < 17/4 < 9/2.

This again contradicts the retained core's minimum-disk identity.

## Exact remaining four-vertex graph case

A connected graph on four vertices either has a spanning star, has a
spanning four-cycle, or is exactly a four-vertex path. Indeed a vertex of
degree three supplies a star. With maximum degree two, a connected graph
is a path or cycle, and a connected four-vertex cycle is the four-cycle.

Therefore a four-square retained core can only have a path as its physical
contact graph. `FOUR_PATH_ANGULAR_CLASSIFICATION.md` further excludes the
full-angle path stress when only its endpoints have positive circle weights:
that classification forces `q=17/4`, contradicting `q>9/2`.

The path argument alone cannot assume its internal vertices are unloaded.
The additional theorem in `LEAF_NEIGHBOR_UNLOADED.md` proves precisely that
missing fact for a full-angle stress at q>9/2: every neighbor of a leaf is
strictly inside the containing disk. It applies to both internal vertices
of a four-vertex path. Consequently all four-square **full-angle** stress
cores are excluded. Every retained connected full-angle core has at least
five vertices. This strengthening does not apply after angular stationarity
has been discarded, and it does not establish the sharp eleven-square bound.
