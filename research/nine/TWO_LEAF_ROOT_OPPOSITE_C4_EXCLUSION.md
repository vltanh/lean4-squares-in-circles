# Two genuine leaves at a C4 root exclude the entire opposite block-load orbit

**Status: complete whole load/leaf-family hand exclusion; root full hand
audit and separate independent full hand audit passed.**
Choose the common canonical nine-square radius/Phi minimizer in
\[
                   \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The exact positive component is
\[
                  H-A-U-C-H,\qquad H-L_1,\ H-L_2,
\tag{2}
\]
where L_1,L_2 are genuine leaves. The positive block-load set is
exactly A,C. The true positive degrees are four at H, two at A,U,C,
and one at each L_i. The three remaining physical squares are
arbitrary and retained.

**Theorem.** The entire opposite block-load orbit in (2) is impossible
at the canonical minimizer. It includes every S/S, S/D and D/D
genuine leaf pair, every relative leaf pose, every A/C physical
circle mask, each individual zero radial corner weight and all
original shared-side means.

In the labels of FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md, this is
the complete C4 two-leaves-at-A family with block loads BD. It closes
all three full leaf-type alternatives of that graph/load orbit.
The BCD block-load family and the whole attachment layout remain open.

## 1. Every genuine leaf gives positive pressure at its actual root

Let L be either genuine leaf, with actual positive circle resultant
F_L. Its actual root is H and keeps all other positive forces.
The full leaf reduction supplies one of the two physical types:

* In type S, L has two physical circle corners. The complete
  RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md theorem gives
  \[
                           c_H\cdot F_L>0.
  \tag{3}
  \]
  This uses the original nonnegative circle weights and their
  positive total, without changing their distribution or the
  actual shared H/L application.
* In type D, write its unique circle corner as R e. The actual
  inward contact is at \((R-\sqrt2)e\). The selected nonradial
  point-normal convention forces this contact into the relative
  interior of an actual H side with outward normal e.
  Thus
  \[
      h_H(e)=R-\sqrt2,\qquad
      c_H\cdot e=R-\sqrt2-\frac12
          \ge\frac{79}{40}-\sqrt2-\frac12
          >\frac{17}{280}>0 .
  \tag{4}
  \]
  The final exact comparison uses \(\sqrt2<99/70\).
  Since the genuine leaf's circle force is a positive multiple
  of e, (3) follows in this type too.

The D argument is exactly the existing physical D leaf/root
domain from RADIAL_BRIDGE_AND_LEAF_REDUCTION.md. It uses the true
leaf degree one only at L, never at H. The two actual S/D types
exhaust the leaf classification, and no hypothesis on the other
root neighbors has been introduced.

For the actual two leaves in (2), put
\[
                              M=F_{L_1}+F_{L_2}.
\]
Equation (3) gives the complete strict pressure inequality
\[
                              c_H\cdot M>0.
\tag{5}
\]
The leaf directions may be unequal, and M is not assumed to be
a side axis, a radial leaf force, or a force applied at a single point.

## 2. The real block and every outside body satisfy the uniform theorem

Each genuine leaf is loaded. The leaf-root theorem makes H physically
circle-clear, with all four original pair forces retained. The chosen
block-load orbit gives the true unloaded degree-two U, the genuine
loaded degree-two A,C, and no other circle load in the positive
component apart from L_1,L_2. Summing every real component force
equation gives
\[
                              M+F_A+F_C=0.
\tag{6}
\]

Thus the entire physical core (2), with actual M defined above,
satisfies every premise of
POSITIVE_ROOT_PRESSURE_OPPOSITE_C4_EXCLUSION.md:
the true degrees at A,U,C, the clear H, the complete balance (6)
and strict pressure (5). That uniform theorem retains arbitrary
additional H forces and all five physical squares outside the
four-cycle. Here those five squares are precisely the two genuine
leaves and the three arbitrary completion squares.

Its complete physical mask and canonical-contact proof therefore
excludes the entire orbit (2). No end-triangle theorem is applied
to a leaf, no leaf is replaced by an aggregate force body, and no
positive force at H is deleted. The canonical packing is chosen
once; a hypothetical gap only contradicts its existing secondary
minimum and does not modify the packing or certificate.

## 3. Exact leaf cover and parent consequence

Exchanging L_1,L_2 is an actual automorphism fixing the entire block
and its load set. The complete genuine leaf-type representatives
are therefore S/S,S/D,D/D. Equations (3)--(6) hold on all three
entire domains, with their full relative orientations and actual
means. No extra normal choice depends on a leaf direction or
weight; the uniform theorem's local finite preselection can be
imposed simultaneously with the original leaf conventions.

This closes one entire block-load orbit and all three of its
whole leaf-type alternatives. It does not close the two-leaves-at-
one-C4-root layout, because its BCD block-load family still remains.
The four-body-block/two-bridge cell C1.4.b2 and the unrestricted
nine-square sharpness/equality obligations stay open. The result
keeps its canonical lower-bound premise and does not classify
original equality configurations.

All three completion units remain throughout. No numerical
parameter search, Lean compilation or CI is used.
