# All three-hub multicycle modules and the exact type of parallel transmitters

Date: October 31, 2026. Separate hand-proof addendum; independent review
pending. The earlier frozen manuscripts and their status are unchanged.

## 1. Parallel genuine transmitters must be side-type

This first theorem is radius-free. Retain actual closed interior-disjoint
unit squares and one unchanged physical force-and-torque certificate.
Let A,B,U,V be four DISTINCT actual squares with positive original paths

\[
A-U-B,\qquad A-V-B,
\]

where U,V are unloaded and have exactly the two displayed original
positive neighbors. Endpoints A,B have arbitrary complete original
degrees, circle loads and additional physical contacts. All original
applications or shared-side means remain.

**Theorem 1.** Both U and V are side-normal transmitters. Their common
signed original normal n is an actual own-side axis of both U,V, and

\[
\operatorname{dist}(A,B)=1.
\]

In particular the diagonal-transmitter alternative is impossible for
ANY genuine parallel pair, independently of the number of other squares
or the containing radius.

### Complete proof

At a genuine unloaded degree-two square, the two original forces are
equal and opposite. Its full torque equation makes the displacement
between its two actual applications parallel to that force. Consequently
it has either side-normal width one, with equal transverse application
coordinates, or diagonal-normal width sqrt(2), with the two opposite
vertices as applications. This is the full original two-force theorem
in `PHYSICAL_CONTACT_STRESS.md`, Section 5.

For one path the terminal applications satisfy

\[
p_B-p_A=w n,
\qquad w\in\{1,\sqrt2\}.
\]

The actual support gap from A to B in n is exactly w. Every actual
displacement b-a has projection at least w, while the displayed
displacement attains length w. Thus dist(A,B)=w. The minimum-distance
DISPLACEMENT between two disjoint compact convex sets is unique: if
two distinct displacement vectors both minimized the norm, their
midpoint would lie in the convex difference B-A and have strictly
smaller squared norm. Applying this to both paths gives the SAME
signed n and SAME width w for U,V. No original normal is reselected.

Their minimum and maximum n supports agree with the same A and B
supports. Thus their longitudinal centers agree. Their orientations
agree modulo square symmetry, because the side or diagonal direction
and the width type determine the square frame. In coordinates (n,t),
where t is perpendicular to n, their open center slices have length
w. Nonoverlap therefore gives

\[
|t\cdot(c_U-c_V)|\ge w.                         \tag{1}
\]

Suppose w=sqrt(2). The two A-side applications are the unique left
diagonal vertices of U and V. Their longitudinal coordinates agree,
and their transverse difference equals that of the centers. Equation
(1) makes their distance at least sqrt(2). But both are maximum-n
support points of the ONE actual endpoint square A. A support face
of a unit square is either a vertex or a unit side, of diameter at
most one. This is a contradiction. The same contradiction could be
read at B. Therefore w=1, proving the theorem.

### Additional exact geometry, with no changed applications

Order the two side-type transmitter centers so that their transverse
difference is Delta>0. Then

\[
1\le\Delta\le2.                                \tag{2}
\]

Indeed the lower bound is (1). Each original A-side application lies
in its transmitter's transverse interval of length one. Their ordered
transverse difference is at least Delta-1. Both applications lie in
A's one support face, so this difference is at most one. Hence
Delta<=2.

If either terminal has a UNIQUE n-support vertex, its two path
applications must coincide there. The two transmitter side intervals
then intersect, so Delta<=1. Equation (2) forces Delta=1, and both
applications occur at their common side endpoints. The same statement
holds at the opposite endpoint B with its minimum-n support.

Conversely, if Delta>1, each endpoint has two distinct applications
on its corresponding support face. That face must be an entire own
side. Thus n is an own-side axis of A and B as well; all four square
frames then agree modulo square symmetry. This is only a necessary
geometric classification, not a claim that every allowed Delta is
realizable with the rest of an original packing.

## 2. All three-hub multicycle three-port modules are excluded

Now retain the same original nine-square model at
\(R^2\le1105/256\), with the compatible selected physical certificate
required by the previously accepted literal embedded K23 exclusion.
Let K be a connected entirely unloaded set, with exactly three FULL
original positive cut edges, internal cycle rank b>=2, and exactly
THREE original full-degree-at-least-three hubs. External endpoint
squares may repeat. All actual transmitters, forces, applications,
outside stars and all nine squares remain.

**Theorem 2. No such K exists, at any cycle rank b>=2.** Thus the
arbitrary-degree higher-rank remainder begins with at least four hubs.

### Complete proof

The previously proved distinct-exit theorem
`THREE_PORT_CYCLIC_DISTINCT_EXITS_AND_FORCE_CONCENTRATION_2026_10_31.md`
puts the three reduced exits at three distinct hubs. Here these are
ALL hubs. Suppress only genuine full-degree-two paths. Each internal
link or exit arm contains zero or one actual transmitter, and there
are no returning links. A direct link cannot coexist with another
channel between the same endpoints, because it gives set distance
zero while any transmitted channel gives positive set distance.

The complete force concentration inequality guarantees at least one
DIRECT original contact among the three hubs. Section 3 of
`THREE_PORT_RANK_TWO_AND_ALL_SUBCUBIC_MULTICYCLE_EXCLUSION_2026_10_31.md`
excludes the entire alternative with exactly one direct hub pair,
without using b=2 or a degree upper bound. Its complete original
dominant-pair and point-terminal cut arguments therefore apply here.

If all three hub pairs are direct, no pair can have an additional
transmitted channel. There are no further hubs. The reduced internal
graph is precisely a triangle and has cycle rank one, contrary to
b>=2.

The only remaining direct graph is a path A-B-C. The two direct
pairs AB and BC admit no further parallel channel. Every other
internal reduced edge must join A and C, since there are only three
hubs and no loops. Write k for its multiplicity. The reduced graph
has 2+k edges and three vertices, so

\[
b=(2+k)-3+1=k.
\]

Thus k>=2. These A-C channels are all transmitted. Select any two,
with distinct actual internal transmitters U,V. The FIVE original
squares A,C,B,U,V then contain the LITERAL physical positive K23
with parts

\[
\{A,C\}\quad\hbox{and}\quad\{B,U,V\}.
\]

All six required positive edges are actual original contacts; no
transmitted edge has been promoted to a direct one. The previously
accepted physical embedded K23/occupied-cross theorem in
`GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md`, Section 7, excludes
this literal subgraph in the same nine-square packing. Every extra
positive edge and every completion square remains. This contradiction
finishes the theorem for all b>=2 at once.

Theorem 1 separately shows that U,V in this last branch are side-type,
but that strengthening is not needed for the existing K23 exit.

## 3. Exact boundary

Theorem 1 is an unrestricted local physical statement with actual
genuine full-degree-two transmitters and arbitrary endpoint degrees.
It does not assert that a selected path inside a higher-degree body
transmits through that body. Theorem 2 uses the existing compatible
physical K23 theorem, as well as the frozen distinct-exit and
unique-direct-pair results, at their stated unchanged scopes.

Neither result excludes the remaining four-or-more-hub,
arbitrary-degree, higher-rank modules whose direct exit-hub graph is
a two-edge path and whose residual full cuts have at least four
edges. No whole original canonical parent or equality result is
declared closed here.

Every new step is printed hand geometry or graph counting. No
mathematical script, numerical pose evaluation, graph enumeration,
Lean, Lake or CI was used. No frozen prior proof, ledger, or remote
branch was changed by this addendum.
