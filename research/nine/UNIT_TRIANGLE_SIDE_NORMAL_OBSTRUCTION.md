# Side-owned contacts in a triangle have nonobtuse normals

**Status: complete geometric hand implication; independent full hand audit passed.**
Let A,B,C be interior-disjoint unit squares, with all three physical
pair contacts nonempty. Choose actual separating unit normals n from
A to B and m from A to C. If n is a side axis of A, then

\[
                              n\cdot m\ge0.
\tag{1}
\]

There is no containing-circle, stress, generic-normal or frame-alignment
premise. Every actual contact point and every shared-side mean is
allowed. In particular this result applies to every owned AB edge
in the remaining distinct-S/S triangle family.

## 1. The support-span fact

If a unit square T has a minimum-m support point p and u is a unit
vector with m dot u<0, then

\[
                        \max_{x\in T}u\cdot(x-p)<1.
\tag{2}
\]

This is the complete support-span lemma in
TRIANGLE_DISTINCT_MIXED_LEAVES_EXCLUSION.md, Lemma3.1. Here is its
short geometry, to make the radius-free implication self-contained.

At a vertex p, write T=p+[0,1]v+[0,1]w with orthonormal inward axes.
The minimum-support condition gives m dot v,m dot w>=0. Since
m dot u<0, at least one of u dot v,u dot w is negative. The positive
u-span is therefore at most the other positive component. It is
strictly below1, since a unit component equal to1 would make the
other component zero and would make m dot u nonnegative.

At a side-interior p, one inward axis is parallel to m and has a
negative u-component. Only the tangential interval contributes a
positive span. Its length is at most1 and its projected unit
component is strictly below1 because u has a nonzero component
along m. Side endpoints are already included in the vertex case.
This proves (2) for every actual support feature.

## 2. The whole triangle implication

Suppose, for a contradiction, n dot m<0. Write H=h_A(n). Since n
is a side axis of the unit square A, its width in direction n is1.

Choose any actual AC application p. The negative n-component of m
forces every maximum-m support point of A onto its minimum-n side.
Consequently

\[
                              n\cdot p=H-1.
\tag{3}
\]

The same p is a minimum-m support point of C. Apply (2), with u=n:

\[
                          \max_{x\in C}n\cdot x<H.
\tag{4}
\]

But every point of B has n-projection at least H by the actual AB
separation. Equations (3)--(4) make B and C closed-disjoint,
contrary to their physical contact. This proves (1).

The case n dot m=0 is retained. A pair of mutually perpendicular
side normals can occur at a triangle junction, so replacing the
conclusion by a strict inequality would be unjustified.

## 3. Consequence for a radial-leaf articulation

Suppose A is a circle-clear triangle articulation with a radial leaf
direction e and positive equilibrium

\[
                      \alpha e+\mu n+\nu m=0,
                    \qquad\alpha,\mu,\nu>0.
\tag{5}
\]

Whenever A owns its AB normal n, (1) and (5) give

\[
                 \alpha(e\cdot n)=-\mu-\nu(n\cdot m)<0.
\tag{6}
\]

Thus the leaf direction has strictly negative projection on every
cycle normal owned by that articulation.

For an S leaf, let its actual radial application be p_L=d e, with
d=sqrt(R^2-1/4)-1. The application is a maximum-e support point of
A. By (6), its n-coordinate is on the opposite n-face from AB:

\[
                     n\cdot p_L=h_A(n)-1.
\tag{7}
\]

Write h=h_A(n). In the distinct-S/S domain both articulations meet
D_delta, where delta=d-1<1/60. The two AB supporting-half-plane
conditions therefore give |h|<=delta. Equation (7) yields the exact
leaf-component relation

\[
 e\cdot n=\frac{h-1}{d},\qquad
 |p_L\cdot Jn|=\sqrt{d^2-(1-h)^2}.
\tag{8}
\]

This covers both a tilted articulation support vertex and an aligned
side mean. If the square root vanishes, e=-n and h=1-d; this
parallel endpoint is retained. In particular the theorem does not
remove the parallel-articulation or variable-mean charts of the
exact surviving S/S control.

## 4. Scope

The theorem restricts a complete geometric owner class. It does not
prove that an arbitrary edge has a side owner, does not choose a new
normal after stress extraction, and does not bound the completion
capacity of a surviving core. Any such use still requires its own
legitimate pre-certificate selection and whole-family capacity proof.

No Lean compilation, CI, numerical pose sample or angle subdivision
is used.

