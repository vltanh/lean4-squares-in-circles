# The complete force-polygon and completion domain of a positive five-cycle

**Status: complete necessary-domain reduction; root and separate independent full
hand audits passed.** This source covers both positive-load orbits of
C5 in C1.5.b0. It does not yet prove their completion bound. Every
physical corner mask, actual side mean, zero-weight physical contact
and all four additional squares remain.

Work throughout
\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]
Use the existing selected physical planar certificate, including strict
point normals and the compatible diagonal avoidance. The complete
five-body graph/load reduction leaves exactly these C5 load orbits:

* Three loads: `T-U-B-C-V-T`, with T,B,C loaded and U,V unloaded.
* Four loads: `A-B-C-D-U-A`, with A,B,C,D loaded and U unloaded.

An unloaded body can still physically touch the circle unless a stated
geometric argument excludes that physical state.

## 1. A nonparallel two-force loaded body has a proper radial concurrence

The following is the nonparallel part of the existing rectangle
normal-line calculation, without its boundary-neighbor premise.

**Lemma 1.1.** Suppose a loaded unit has exactly two positive pair
forces, and their actual force lines are nonparallel. Then the lines
meet at a point q which is a positive multiple of its circle-resultant
vector m. For every actual application p and outward unit normal n,
\[
                          p-q=\alpha n,\qquad\alpha\ge0.
 \tag{2}
\]
For one physical circle corner q belongs to the unit. With two physical
circle corners it need not belong to the unit; (2) is the conclusion
used below. No neighboring body need touch the containing circle.

*Proof.* Torque about the intersection gives `q parallel m`, since
`m` is nonzero. If the two applications coincide, their intersection
is that same point p and (2) is immediate. Positivity follows because,
for each positive circle corner z of the unit,
\[
 p\cdot z=\frac{|p|^2+R^2-|p-z|^2}{2}
              \ge\frac{R^2-2}{2}>0.
\]
Thus `p dot m>0`, fixing the positive radial sign.

For distinct applications use the exact normal-line calculation in
`C7_FORCE_POLYGON.md`, Sections 4--5, as isolated in the proof of
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1. Its one-corner
part places q inside `[a-1,a] x [b-1,b]`. Every outside alternative
is excluded by actual distinct contacts, impossibility of sharing a
containing-circle point, or the unit-neighbor support-width bound.
None of these steps assumes a boundary neighbor. This gives the
positive radial factor and (2) by the supporting half-planes.

For two physical corners the same calculation writes
`q=tau(T,eta)`, `|eta|<=1/2`, for the radial unit
`[T-1,T] x [-1/2,1/2]`. It excludes `tau<(T-1)/T`.
For `(T-1)/T<=tau<=1`, q is inside the unit. For `tau>1`, the
remaining possible non-circle contacts are on its inner face or its
endpoints; the outer face is excluded by width. Each surviving normal
line then points outward from q to its actual application, as in (2).
These steps likewise require no boundary neighbor. The boundary-neighbor
premise of the earlier lemma was needed only to rule out parallel
forces, which are expressly excluded here. `square`

In the three-load C5, `FIVE_CYCLE_THREE_LOAD_PARALLEL_EXCLUSION.md`
already excludes parallel forces at T. Thus Lemma 1.1 applies to T,
even though both its neighbors are unloaded. B and C have each other
as boundary neighbors, so the full earlier two-force theorem applies
to them. In the four-load orbit every loaded body has a boundary
neighbor and therefore has nonparallel pair forces and (2).

## 2. Exact contraction of every unloaded transmitter

At an unloaded degree-two body the two forces have equal magnitude,
opposite directions and a common actual line. The full transmission
classification gives reserve
\[
                         w\in\{1,\sqrt2\}.
 \tag{3}
\]
For a side-normal transmitter its applications on opposite sides have
exact displacement `w n=n`; their common transverse coordinate is an
arbitrary actual mean. For a diagonal transmitter they are opposite
vertices and the displacement is `sqrt(2) n`.

Suppose the directed channel goes from loaded X through the transmitter
to loaded Y. Write its actual endpoint applications as p_X,p_Y and
its unit direction as n. Formula (2) at the loaded endpoints gives
\[
 p_X=q_X+\alpha_X n,\qquad
 p_Y=p_X+w n,\qquad
 q_Y=p_Y+\alpha_Y n,
 \qquad\alpha_X,\alpha_Y\ge0.
\]
Consequently
\[
             q_Y-q_X=(\alpha_X+w+\alpha_Y)n.
 \tag{4}
\]
The coefficient is strictly positive and at least w. A direct edge
between loaded bodies has the analogous formula with w=0 and a
strictly positive coefficient: equality would identify their positive
radial directions, which lie in disjoint physical boundary-corner
intervals.

Thus the three-load orbit has a triangle of loaded concurrence points,
with reserve w_U on TB, zero on BC, and w_V on CT. The four-load orbit
has a quadrilateral, with zero reserves on AB, BC, CD and reserve w_U
on DA. These are exact contact equations. They do not replace the
transmitter body by a segment in the physical completion problem.

## 3. The contracted force polygon is strictly convex and contains zero

Orient the cycle and let `mu_i n_i` be its directed force, with
`mu_i>0`. Each physical body has zero origin moment from its radial
circle forces. Its torque balance therefore gives one common value
\[
                           \det(p_i,\mu_i n_i)=H
 \tag{5}
\]
on every original edge. Equal force magnitudes and collinear actual
applications carry this same value across each transmitter.

There is a direct boundary-to-boundary edge in both load orbits.
Orient that edge so its consecutive positive radial concurrence
vectors have positive determinant. Their physical corner intervals
are disjoint, and the boundary-contact acuteness theorem makes this
determinant nonzero. Formula (4) then shows its actual moment is
positive. Hence choose the cycle orientation so that
\[
                                  H>0.
 \tag{6}
\]

List the loaded concurrences in cycle order, with three or four
vertices as appropriate. Write their positive edge lengths from (4)
as `L_i`. Equations (4)--(6) imply
\[
 \det(q_i,n_i)=\frac{H}{\mu_i}>0,
 \qquad
 \det(q_i,q_{i+1})=\frac{L_iH}{\mu_i}>0.
 \tag{7}
\]
The positive angular increment between successive radial vectors is
strictly between zero and pi. Their sum is a positive multiple of
`2pi` and is less than `4pi`, because there are at most four edges.
Thus the sum is exactly `2pi`. Each straight edge lies within its
successive angular sector; these sectors have disjoint interiors.
The polygon is simple and winds once about zero.

Write `2m_i=kappa_i q_i` with `kappa_i>0`. Actual force balance at
each loaded body reads
\[
        \kappa_i q_i+\mu_i n_i-\mu_{i-1}n_{i-1}=0.
 \tag{8}
\]
Taking the determinant with `n_{i-1}` and using (7) gives
\[
        \mu_i\det(n_{i-1},n_i)
             =\frac{\kappa_iH}{\mu_{i-1}}>0.
 \tag{9}
\]
Every local turn is strictly left. The simple triangle or quadrilateral
is therefore strictly convex. Formula (7) also puts zero strictly on
the left of every directed edge. Consequently zero lies in its open
interior.

**Theorem 3.1.** Every surviving three-load C5 has a strictly convex
proper concurrence triangle containing zero, with exact reserves
`(w_U,0,w_V)`. Every four-load C5 has a strictly convex proper
concurrence quadrilateral containing zero, with exact reserves
`(0,0,0,w_U)`. Each reserve is retained as a full physical transmitter
and every side-mean parameter remains actual.

A concurrence of a radial two-corner body can lie outside its square
and outside the containing disk. No disk bound on the force polygon,
or inclusion of the physical central hole in that polygon, is inferred
here. Such conclusions would require additional geometry.

## 4. Complete remaining width and physical-boundary cover

For three loads, `FIVE_CYCLE_THREE_LOAD_PARALLEL_EXCLUSION.md`
excludes the entire parallel alternative at T, and
`FIVE_CYCLE_THREE_LOAD_DOUBLE_DIAGONAL_EXCLUSION.md` excludes
`w_U=w_V=sqrt(2)`. The exact remaining width cover is therefore
\[
            (w_U,w_V)=(1,1)
                 \quad\hbox{or}\quad(1,\sqrt2),
 \tag{10}
\]
up to reflection. Every physical circle mask of T,B,C is still
included. At a diagonal transmitter, each vertex endpoint lies in the
relative interior of a neighboring side by the compatible diagonal
avoidance; its two loaded endpoint bodies share that channel axis.
No corresponding common frame is imposed on a side-normal transmitter's
loaded endpoints.

For four loads the complete single-transmitter cover is
\[
                         w_U=1\quad\hbox{or}\quad\sqrt2.
 \tag{11}
\]
If diagonal, its two loaded endpoints share the channel as a side axis.
The other two loaded bodies still have independent frames.

The four-load transmitter U is physically circle-clear: otherwise all
five physical bodies would form a boundary contact C5, excluded by
`CIRCLE_CONTACT_ANGULAR_ORDER.md`. In the three-load family at least
one of U,V is physically circle-clear for the same reason. Either
individual transmitter can otherwise retain a physical circle contact
with zero multiplier. Formula (10) does not erase that physical label.

## 5. Exact completion-region accounting

The selected physical five-cycle has the arbitrarily small planar
center/contact embedding of `PHYSICAL_BODY_GRAPH_UNCROSSING.md`.
Its boundary circle vertices can all be attached by exterior spokes.
Choose one circle port on each loaded body. These noncrossing spokes
subdivide the exterior of the cycle, inside the containing circle,
according to the loaded cyclic order. Additional physical circle
contacts and zero-weight contacts may subdivide these regions further;
they do not allow a connected extra-square interior to cross a core
body or a chosen spoke inside that body.

Use the weak contact-boundary convention of `CONTACT_RING_HOLE_AREA.md`
when applications coincide. Its k=5 area theorem gives
\[
            \operatorname{area}(\text{central free region})
                  \le\frac54\cot(\pi/5)<2.
 \tag{12}
\]
The smaller contact-polygon degeneracies satisfy the corresponding
smaller bounds. Hence the entire bounded five-ring region contains at
most one further unit square. All applications of this statement keep
the original extra-square interiors; an arbitrarily small embedding
perturbation can be chosen after taking compact inner portions of
those finitely many interiors.

For every consecutive boundary pair which physically touches, the
complete exterior-pair-pocket theorem in
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, Sections 2--4, excludes
any additional unit in that exterior pocket. It retains every other
square while moving the hypothetical pocket occupants and does not
assume that the touching pair's circle multipliers are positive.
Possible additional caps between two circle corners of one body only
subdivide these regions.

Thus the precise residual completion cover is:

| Load orbit | Empty exterior pockets | Remaining locations of four extras |
| --- | --- | --- |
| Three loads `T-U-B-C-V-T` | The exterior BC pocket | At most one in the bounded five-ring region; every other extra lies in one of the two exterior channel regions `T-U-B` and `C-V-T`, including any subdivisions by zero-weight contacts. |
| Four loads `A-B-C-D-U-A` | The exterior AB, BC and CD pockets | At most one in the bounded five-ring region; every other extra lies in the single exterior channel region `D-U-A`, including its physical subdivisions. |

Consequently a nine-square completion in the three-load orbit requires
at least three extras in the union of its two exterior channel regions,
and at least two in one of them. In the four-load orbit it requires
at least three extras in its one exterior channel region. These are
necessary routing conclusions, not capacity estimates for those regions.

## 6. Later full-family exits and exact scope

The routing in Section5 remains a proved necessary-domain statement.
FIVE_CYCLE_THREE_LOAD_EXCLUSION.md and FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md
now exclude both entire load orbits directly, without needing a separate
transmitter-pocket capacity estimate. FIVE_CYCLE_POSITIVE_COMPONENT_EXCLUSION.md
assembles the whole C5 graph branch. Both reserve widths, every actual
mean, every physical circle mask and all four extras remain.

The geometric C7 capacity theorem is not a premise of this exit. No
force polygon is substituted for an actual boundary cycle, and a radial
two-corner concurrence is not assumed to lie inside its body or disk.
House, four-load fan and larger components retain their additional
forces and require separate arguments. A C5 subgraph with extra positive
edges is outside the exact degree-two component scope. No numerical
diagnosis, post-stress normal change, Lean compilation or CI is used.
