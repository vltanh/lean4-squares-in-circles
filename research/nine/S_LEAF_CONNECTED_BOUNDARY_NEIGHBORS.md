# Connected boundary neighbors cannot balance a radial S leaf

**Status: complete hand necessary-condition theorem; independent full hand
audit passed.** In the declared radius window, suppose a positive component
has a radial S leaf L with articulation A. If every other loaded body
belongs to one connected physical-contact graph of circle-touching
neighbors of A other than L, then the component is impossible.

The connected graph may contain physically circle-touching bodies with
zero circle multiplier. Its edges need only be physical contacts. The
theorem retains all contact normals, all square orientations, and every
circle-corner weight mask.

In particular, it excludes the whole S-leaf branch of the diamond with
the leaf at a hub whenever the other hub physically touches the circle.
The clear-hub alternative and the D-leaf cases are not excluded here.

## 1. Two separated arcs contain every possible boundary neighbor

Use

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,
 \qquad L=[d,d+1]\times[-1/2,1/2].
 \tag{1}
\]

The leaf's two positive circle weights are equal, so its resultant is
a nonzero positive horizontal vector. Its center direction is zero.
The articulation A is physically circle-clear by the radial-bridge
endpoint theorem, and its right support contains (d,0).

After reflection across the horizontal axis if necessary, the entire aligned or tilted A family
satisfies the hypotheses of Section3 of
S_LEAF_TRIANGLE_EXCLUSION.md. That section is a geometric neighbor
lemma, independent of the triangle graph and its load allocation. Put

\[
 \vartheta=\arctan\frac37.
\]

Every physical circle corner of every square touching A avoids the
closed angular arc

\[
            I=[\pi-\vartheta,\;3\pi/2-\vartheta].
 \tag{2}
\]

This arc has length exactly pi/2 and contains the negative horizontal
direction.

Independently, the center directions of distinct circle-touching
squares have circular separation strictly greater than 2pi/9, by
CENTERED_INNER_ARC.md. Every circle corner differs from its own center
direction by strictly less than pi/9, by
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Lemma2.1. Since L's center
direction is zero, every circle corner of any other circle-touching
body has circular distance strictly greater than pi/9 from zero.

Combining this fact with (2), the circle corners of every boundary
neighbor of A other than L belong to

\[
 J_+=(\pi/9,\;\pi-\vartheta),\qquad
 J_-=(3\pi/2-\vartheta,\;2\pi-\pi/9).
 \tag{3}
\]

All directions in J_+ have positive second coordinate; all directions
in J_- have negative second coordinate.

Every one body's physical circle corners lie in the same one of these
two intervals. Indeed any two of its corners are each within pi/9
of its center direction, so their circular separation is strictly
less than 2pi/9. In contrast, two directions in different intervals
in (3) have separation strictly greater than 2pi/9: the gap through I
is pi/2, and the gap through the positive horizontal direction is
2pi/9. Thus a body cannot have one circle corner in each interval.

## 2. A boundary contact cannot join the two intervals

Let X,Y be physically touching circle-boundary neighbors of A,
different from L. Choose one circle corner on each. Their vectors
have positive dot product, by ACUTE_LOADED_CONTACT_GRAPH.md,
TheoremA.2; the proof of that theorem uses physical circle contact,
not positivity of the corresponding circle multipliers. Hence the
minor angular arc between the two chosen corners is shorter than
pi/2.

Suppose the corners belonged to different intervals in (3). The arc
between them through I has length strictly greater than pi/2, so it
cannot be their minor arc. Their minor arc must instead pass through
the positive horizontal direction. That arc contains every angle in
(-pi/9,pi/9), and therefore contains a circle corner of L: such a
corner differs from L's center direction by less than pi/9.

But the circle-corner ordering theorem in
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Section2, says that the
chosen corners of a touching boundary pair are consecutive along their
corresponding minor arc among any selection of one corner per boundary
body. Choosing that corner of L contradicts consecutiveness.

Thus every physical edge between boundary neighbors of A preserves
the J_+/J_- assignment. Consequently every connected graph of such
neighbors lies entirely in one of the two assignments.

## 3. The force-balance obstruction

Suppose all loaded bodies other than L belong to one such connected
graph K, and K does not include L. By Section2, all positive circle
atoms outside L have strictly the same sign of second coordinate.
There is at least one such positive atom, since the positive component
cannot have only one loaded body.

Summing all physical body force equations in the component cancels
the internal pair forces. The sum of its circle-load vectors must be
zero. The S leaf contributes zero second coordinate, whereas the sum
of all other positive circle atoms has a strictly positive or strictly
negative second coordinate. This is impossible.

**Theorem3.1.** Under the hypotheses stated above, no such positive
component exists. No assertion that its loaded corner vectors are
pairwise acute was used; acuteness was needed only along each physical
boundary-contact edge.

## 4. The complete S/boundary-hub diamond consequence

Let the diamond have hubs A,U and degree-two tips B,C, with its
pendant radial S leaf L joined to A. Its positive block edges are

\[
                         AU,\ AB,\ AC,\ UB,\ UC.
\]

Both B,C are loaded: an unloaded degree-two triangle tip would
transmit through its two physically touching neighbors, which is
impossible. A is physically circle-clear by its leaf bridge. If U
physically touches the circle, then B--U--C is a connected graph of
boundary neighbors of A. It contains every possible loaded body of
the component except L, whether U has positive or zero circle weight.
Theorem3.1 excludes this entire case.

Hence the S-leaf diamond-hub branch, if it survives, has a physically
circle-clear second hub U and exactly the three loaded bodies L,B,C.
All four completion squares remain in that residual problem. This
does not close either full diamond attachment branch or C1.4.b1.

No Lean compilation, CI, numerical angle grid, or unproved generic
normal choice is used.
