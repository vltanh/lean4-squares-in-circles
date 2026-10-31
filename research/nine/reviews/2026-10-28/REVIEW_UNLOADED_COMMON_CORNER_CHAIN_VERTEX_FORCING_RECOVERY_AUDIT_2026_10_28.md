# Independent review: arbitrary-degree common-corner force balance and the physical neighbor chain

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

## 1. Exact source and verdict

**PASS.** I read the entire frozen source
`UNLOADED_COMMON_CORNER_STAR_CONTACT_CHAIN_OPPOSITE_VERTEX_FORCING.md`
and independently rederived its strict support-span input, the entire
physical chain sign cover, both full-star consequences, and the
closed owned-axis alternative. Its exact source is 8,005 bytes,
SHA-256

`d1c6f5fe17b89a0660fcea7c67446ecd845b6bf45b582fd35be263536c68a277`,

Git blob `9f7167387e108f056c40c27fddc164cbd35de93f`.
The sole direct pin matches the current checkout. No source was changed.

The geometric chain lemma has no force, circle, radius or degree
premise. Its full-star consequences use the complete force balance
at a genuinely unloaded actual square of arbitrary positive degree.
All neighbor degrees, loads, physical contact features and original
means remain. In particular an own-axis force in a closed normal cone
can have its original application elsewhere on the same support side;
the theorem does not move that application to a common vertex.

## 2. Exact operative input and independent geometric derivation

| Input | SHA-256 | Exact use |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Full strict unit support span and nonobtuse owned-axis physical triangle, including all actual means |

I freshly reread this entire input. Both geometric tools used in
the new source also have complete short derivations, so no graph
or force assertion is hidden in their application.

Let an actual unit square K have a minimum-n support point P and
let e be a unit direction with n.e<0. At a vertex write
K=P+[0,1]r+[0,1]s with orthonormal inward axes. The support condition
gives n.r,n.s>=0. Since n.e<0, at least one of e.r,e.s is negative.
The positive projection of K-P in direction e is therefore at most
the other positive component. It is strictly below one: a component
equal to one forces e to equal that inward axis and hence n.e>=0.
At a side-interior point, the inward normal axis has negative
e projection, while the entire remaining actual tangent interval has
length at most one and tangent projection strictly below one. Side
endpoints are covered by the vertex calculation. Thus

    max_{Z in K} e.(Z-P)<1.

The strictness is independent of K's frame and of the original
support point within a side. No load or stress magnitude is involved.

For U=[0,1]^2, a neighbor with a strict Southwest U-to-neighbor
normal has its U support at (0,0), and the span estimate puts the
whole neighbor in x<1,y<1. A strict Northeast neighbor has its
support at (1,1), and the same estimate in the negative directions
puts it in x>0,y>0. Any common point would lie in int U. A distinct
full closed square cannot contain a point in int U while retaining
disjoint open interiors: its own interior points approach every
boundary point, giving overlap with that open neighborhood. Hence
these two opposite strict-corner neighbors cannot touch. Reflection
gives the Northwest/Southeast alternative.

For an owned East U-to-neighbor normal, the whole neighbor lies
in x>=1. A second U-to-neighbor normal with negative x component
supports U on x=0. The strict span bound makes that entire second
neighbor lie in x<1. They are closed-disjoint, contradicting a
physical triangle. This proves the owned-axis nonnegative dot-product
condition with every side mean retained. Equality of the dot product
is allowed, as required by the subsequent closed-axis case.

## 3. Complete physical A-B-C chain sign cover

Use only distinct actual U,A,B,C with physical UA,UB,UC,AB,BC.
The fixed U frame is [0,1]^2. The original A normal has
n_A,x<0<n_A,y, so its actual U support is (0,1). The original C
normal has n_C,x<=0 and n_C,y<0. It is either strict Southwest
at (0,0) or the U-owned South axis with its unchanged actual side
mean. There are no other C features under these exact premises.

Assume n_B,x>0. Its complete vertical sign cover is as follows.

| Original B feature | Actual contradiction |
| --- | --- |
| n_B,y<0, strict Southeast at (1,0) | B and A are at opposite strict U vertices, contradicting the actual AB contact |
| n_B,y=0, U-owned East with any original mean | Its dot product with n_A is negative, contradicting the actual U-A-B owned-axis triangle |
| n_B,y>0, strict Northeast, while n_C,x<0 | B and C are at opposite strict U vertices, contradicting the actual BC contact |
| n_B,y>0, strict Northeast, while n_C,x=0 | The actual C normal is U-owned South and has negative dot product with n_B, contradicting the actual U-B-C triangle |

These cases include all three B vertical signs and the complete
closed C horizontal endpoint. Thus necessarily n_B,x<=0. This
conclusion is about the original actual normal; it does not assume
that either AB or BC carries a positive force. It uses neither
torque balance nor the positive degree of any of these four units.

## 4. Full-star contradiction with all additional original neighbors

For Theorem 1, U is genuinely unloaded. Keep every original
positive vector F_J=mu_J n_J in its entire star, including every
neighbor besides A,B,C. The premises give

    F_A,x<0, F_C,x<=0,
    F_J,x<=0 for every other original J except B.

The full original x force equation therefore forces F_B,x>0.
Since its original magnitude is positive, this means n_B,x>0,
contradicting the physical chain conclusion. No upper degree
bound, hidden three-force reduction or omission of an extra
neighbor is involved.

The C-owned-by-U South case has F_C,x=0 but F_C is a positive
nonzero pair force. Its vertical component and its original torque
remain in the original system. The contradiction simply needs
only the horizontal component of the complete force balance.
Every possible original shared-side mean is allowed, including
both endpoints. No assertion about its torque at (0,0) is used.

## 5. Complete opposite-vertex forcing at arbitrary degree

For Theorem 2 normalize the strictly exposed C vertex to P=(0,0).
Its original force has two strictly negative own components. Every
other original force except A,B,C lies in the closed Southwest
normal cone, so has both components nonpositive. These cone
conditions are all that the force argument needs; they do not
imply, and the proof does not claim, that a side-axis application
has been moved to P.

The original A normal is not an own axis. It therefore strictly
exposes exactly one of the four actual U vertices Q.

If Q=P, both A components are also strictly negative. The full
two-component force balance makes both B components strictly
positive. Its actual U support is consequently the strict opposite
vertex (1,1), which cannot have a neighbor touching the strict C
neighbor at P. This contradicts the actual BC incidence.

If Q is adjacent to P, exchange the two actual own coordinates
when necessary so Q=(0,1). This transforms the entire chart and
all its original vectors; it is not a normal change. The signs
are precisely those of Theorem 1, and all additional original
forces retain nonpositive horizontal components. That theorem
excludes either adjacent vertex.

P, its two adjacent vertices and its opposite vertex exhaust the
actual U vertices. Thus Q must be opposite P. The proof makes no
assumption that original application points are distinct. It permits
arbitrarily many positive pair forces in the same closed corner cone,
as well as genuine endpoint-valued or interior-valued means on its
axis support faces.

## 6. Literal caller boundary and preservation

At a true unloaded H4 with neighbors A,B,C,D, actual AB and BC,
strict HC and HD both at the same H vertex P, and non-H-owned HA,
Theorem 2 applies with U=H and the additional original neighbor D.
It forces the HA vertex opposite P. The loaded C3 is not assigned
a C2 equation; HC and HD are not replaced by one force on an
invented neighbor; no H3 equation appears. If HC is an actual
South own axis instead, Theorem 1 supplies the stated complete
horizontal force contradiction, with its full side mean.

Both are necessary local tools. An entire original family still
needs the appropriate physical incidence and feature premises to
be verified separately. The generic source claims no original-row
closure by itself and introduces no selected-normal perturbation.

All nine actual units and the original 2,513 fine and 58 coarse
identifiers are preserved. This review changes no source, force,
normal, application, mean, physical circle mask, individual zero
coefficient, metadata, flag or count. It creates only this review.
No numerical pose sampling, angular mesh, Lean compilation, CI,
workflow, git commit or remote operation was used.
