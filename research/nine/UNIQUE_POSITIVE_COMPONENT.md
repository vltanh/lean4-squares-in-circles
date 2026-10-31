# The selected planar physical stress has exactly one positive component

**Status: complete hand deduction from the planar-certificate theorem;
two separate hand audits passed.** A normalized physical stress selected as in
`PHYSICAL_BODY_GRAPH_UNCROSSING.md` has exactly one component carrying
positive contact or circle weights. All other packing bodies have zero
stress. This conclusion does not require excluding the four-body
triangle-plus-leaf class and does not use a lower bound on component
size.

The point is a planar boundary-order argument. Every component has zero
total circle-force vector. Two disjoint connected plane graphs cannot
both have boundary ports whose positive weighted sum is the disk center.

## 1. All positive circle atoms can be attached at once

Use the selected plane drawing of the positive body-pair graph from
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`. For every actual circle corner
\(z\) carrying a positive circle weight on body \(i\), add the spoke

\[
                         [c_i,z].                         \tag{1}
\]

All these spokes can be retained simultaneously in the construction of
that drawing, not just one spoke per circle-touching body.

Indeed, except for its circle endpoint, a spoke is in its square's open
interior. A center-to-contact segment of that square cannot meet it away
from the center: two distinct rays from an interior point do not meet,
and a contact endpoint on the spoke ray would have to be the same
boundary point \(z\). But a circle point cannot belong to two packing
squares. Spokes in different square interiors are disjoint, and spokes
of the same square meet only at that square's center.

There are finitely many spokes. Every contact junction has positive
distance from their union. Choose all junction neighborhoods and tube
perturbations in the planar-drawing construction small enough to avoid
these spokes away from their incident centers. At a center the finitely
many distinct spoke and contact rays can also be kept in their distinct
angular sectors. This gives a plane graph with all positive circle atoms
attached as degree-one ports on the containing circle. Distinct ports
have distinct geometric circle points, after weights at the same corner
are combined. No edge of the graph other than these terminal endpoints
meets the circle.

In particular, distinct components of this augmented graph are disjoint
connected subsets of the closed disk. Each pair of ports in one component
can be joined by a simple graph path whose open part is in the open disk:
the other circle ports have degree one, so none is an interior point of
such a simple path.

## 2. A boundary-order lemma

**Lemma 2.1.** Let two disjoint connected finite plane graphs lie in a
closed disk, with their only boundary points being distinct degree-one
ports. Their port sets cannot alternate around the boundary circle.

*Proof.* Suppose that four ports occur in the cyclic order

\[
                        a,b,a',b',                         \tag{2}
\]

with \(a,a'\) in the first component and \(b,b'\) in the second.
A simple path from \(a\) to \(a'\) in the first graph is a crosscut
of the disk: its open part lies in the open disk. The two boundary arcs
between its endpoints lie on the two sides of this crosscut. The ports
\(b,b'\) lie on different sides by (2), so every path between them
in the disk must meet the crosscut. This contradicts the disjointness of
the two components. \(\square\)

**Corollary 2.2.** If the first component has at least two ports, then
all ports of the second component lie in one open gap between consecutive
ports of the first.

*Proof.* No port is shared. If two ports \(b,b'\) of the second
component lie in different such gaps, each of the two open boundary arcs
between \(b,b'\) contains a port of the first component. Choosing one
from each arc gives the forbidden alternating order in Lemma 2.1. Thus
all second-component ports lie in a single gap. The conclusion is also
immediate when the second component has only one port. \(\square\)

## 3. Force balance leaves no room for a second component

Let \(K\) be any component. Summing all its body force equations
cancels its positive body-pair forces in equal and opposite pairs.
Therefore its circle ports satisfy

\[
                  \sum_{z\in Z_K}\lambda_z z=0,
                  \qquad \lambda_z>0.                    \tag{3}
\]

Here \(Z_K\) contains exactly the actual circle corners with positive
weights in that component, combining weights at a repeated corner.
Any component with a circle weight has at least two distinct ports,
since no circle point is the origin.

For such a component, every circular gap between consecutive ports has
angular length at most \(\pi\). If one gap were longer than
\(\pi\), all its ports would be contained in the complementary
closed arc of length strictly less than \(\pi\). A vector toward
the midpoint of that arc would have strictly positive dot product with
every port, contradicting (3).

Now suppose that two distinct components \(K,L\) both carry circle
weights. By Corollary 2.2, all ports of \(L\) lie in one open gap
between consecutive ports of \(K\). The preceding paragraph bounds
that gap's length by \(\pi\). The midpoint direction of the gap
therefore has strictly positive dot product with every port of \(L\):
the endpoints are excluded even if the gap has length exactly
\(\pi\). This contradicts (3) for \(L\).

Consequently at most one component carries positive circle weights.
The argument includes the degenerate case in which the first component
has only two antipodal ports. Its two gaps are open semicircles, and the
same strict dot-product contradiction applies to every second component.

## 4. A component with positive contacts must carry circle weight

For completeness, a component with a positive body-pair edge cannot be
entirely unloaded. Let \(n_{ij}\) be the unit normal of an oriented
positive edge \(i\to j\), directed from square \(i\) to square
\(j\), and let \(\mu_{ij}>0\) be its aggregate magnitude. At its
actual shared support point,

\[
 n_{ij}\cdot(c_j-c_i)
       =H_i(n_{ij})+H_j(n_{ij})\ge1,                     \tag{4}
\]

where \(H_i\) is the centered support halfwidth of square \(i\).

If the component had no circle weights, multiply each body's force
equation by its center and sum. Every oriented edge contributes

\[
 \mu_{ij} n_{ij}\cdot(c_i-c_j)
       =-\mu_{ij}\bigl(H_i(n_{ij})+H_j(n_{ij})\bigr)<0.  \tag{5}
\]

The sum would have to be zero, which is impossible when there is a
positive edge. Thus every nontrivial positive contact component carries
positive circle weight. An isolated body with a positive circle weight
would itself already be a circle-loaded component, covered by Section 3.

Finally, normalization gives \(\sum_z\lambda_z=1\), so at least
one component carries circle weight. Combining this with Sections 3--4
proves the claimed uniqueness.

**Theorem 4.1.** For a selected planar normalized physical certificate,
all positive body-pair contacts and all positive circle atoms belong to
one connected component of the body-pair graph, including any loaded
isolated vertex in the definition of a component. Every other body has
zero contact and circle stress.

## 5. Consequence in the nine-square radius window

In the window used by the nine-square argument, an isolated loaded body
is impossible because its circle resultant is nonzero; see
`ACUTE_LOADED_CONTACT_GRAPH.md`. The complete tree and two-load
completion theorems then make the unique component cyclic with three to
seven noncollinear circle resultants. The previously closed triangle and
four-body biconnected cells do **not** exclude the four-body
triangle-plus-leaf cell. Accordingly the size range that follows from
the current results is

\[
                         4\le m\le9.                     \tag{6}
\]

There are exactly \(9-m\) zero-stress bodies outside this selected
component. They remain physical completion squares and must be retained
in every capacity argument. This theorem establishes uniqueness of the
selected positive component; it does not exclude its remaining mixed
cyclic geometries or prove the unrestricted sharp radius bound.
