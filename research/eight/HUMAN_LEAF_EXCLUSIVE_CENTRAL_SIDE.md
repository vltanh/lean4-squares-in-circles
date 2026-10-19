# An actual leaf monopolizes its central side; in side-stressed B2 it must be perpendicular

**2026-10-12. Global structural consequence of the exact
leaf theorem and full-orientation one-square cap geometry.**
This argument is independent of the number of outer centers
and is not a cap-constant optimization.

## Theorem (exclusive leaf side)

Choose an attained radius-minimizing eight-square packing
with the **fewest actual contacts**, at
\(R^2\le9789/2500\), and let C be the
unique origin-containing unit square.

If a square T has **exactly one actual
square-square contact**, then:

1. That contact is with C, not another exterior square;
2. The genuine frames of T and C are parallel,
   the center \(p_T\) is radial along one of
   the **four signed side normals** m of C,
   and T has two true vertices on the
   containing circle;
3. The *actual whole-square cap*
   \[
   H_m:=\{x:m\cdot x\ge b\},\qquad
   b=\sqrt{R^2-1/4}-1>4/5,
   \]
   contains T but **cannot contain any other
   different packed unit square**:
   \[
   \boxed{S\ne T\Longrightarrow
          S\not\subseteq H_m.}                \tag{1}
   \]
4. If C has **exactly two positive-stress
   contact neighbor pairs** along opposite
   C **side** normals ±n, every actual
   leaf T attached to C must use one of
   the *two perpendicular* C side normals
   \[
   \boxed{m=\pm Jn.}                            \tag{2}
   \]

The conclusion is about an actual *whole*
C-owned central-side cap, not just the sign
of an exterior center.

## Proof

The exact actual-leaf theorem
HUMAN_STRESS_GRAPH.md section 1 proves
that any one-contact square T in a
minimum-contact radius minimizer:
has C as its sole neighbor, is parallel
to C, has center along a common side
normal m, and touches the containing
circle at two outer vertices.

That theorem also identifies the
shared whole-side contact line
\(m\cdot x=b\) with
\(b=\sqrt{R^2-1/4}-1\) and
puts the **entire leaf T** in
\(H_m=\{m\cdot x\ge b\}\).

The established sharp radius lower bound
\(R>\sqrt2+1/2\) implies
\[
R^2-1/4>2+\sqrt2>
2+31/25=(9/5)^2,
\]
so \(b>4/5\).
The high-cap two-square capacity lemma
proved with exact rational center
separation in
HUMAN_M6_PERPENDICULAR_SPECTATOR_LEAF.md
states that **no two different**
disjoint-interior unit squares can both
be wholly in a cap \(h\ge4/5\)
under the n=8 disk ceiling.
Its strict squared-center separation
upper bound is
\[
(2/3)^2+(23/200)^2
=164761/360000<1.
\]
As T already occupies \(H_m\),
no other square can wholly occupy it.
This proves the exclusive cap property (1).

Now suppose C has two positive-stress
neighbor squares A,B with opposite
C side normals n,-n.
Both *actual whole* A and B squares
lie beyond C's corresponding opposite
side supporting lines.
Since T is a leaf, its normal m is
one of the four C side normals
\(\pm n,\pm Jn\).

If m=n, the positive neighbor of C
on its +n side also lies wholly beyond
the very same C support line \(m\cdot x=b\)
that T occupies. This contradicts
the exclusive cap theorem.
The same argument excludes m=-n
using the other positive C neighbor.
Thus m must equal +Jn or -Jn,
proving (2). QED.

## Role in the global proof roots

This removes leaf placement along
positively stressed central **side**
directions for **every** B2 side-mode
minimum-contact representative,
not merely for m=6.

It is particularly useful in the
**k=7, m=6 spectator-spoke mode S**:
if the unique spectator T is a
C-leaf, then it is a *radial,
frame-parallel, circle-contact*
square on one of the perpendicular
C faces. This is the precise
orthogonal scaffold recorded in
HUMAN_M6_PERPENDICULAR_SPECTATOR_LEAF.md.

The theorem is not applicable when
C's two positive force directions
are diagonal unless new geometry
is supplied. Diagonal mode instead
requires the two additional
tangentially opposing zero-stress
C contacts from
HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md.

Nothing here excludes the legitimate
seven-outer actual-contact ring
equality packing. Root A, the remaining
B2/B3/X structural modes, k<=6 and the
unrestricted \(R_8\ge\widehat R\)
remain OPEN.
