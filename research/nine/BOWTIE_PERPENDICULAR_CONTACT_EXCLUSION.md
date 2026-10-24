# Perpendicular articulation-owned contacts cannot support two loaded tips

**Status: complete hand implication; root and separate independent full hand audits passed.**
Let A,B,C be interior-disjoint closed unit squares with all three
physical pair contacts. Suppose B and C are positive degree-two
circle-loaded tips: their only positive pair edges are AB, BC and
AC. The square A may have additional positive edges. All squares
lie in a disk centered at zero with

\[
                              R^2>2+\sqrt3.
\tag{1}
\]

**Theorem.** The two actual outward normals from A to B and C
cannot be perpendicular side axes of A.

The assertion retains arbitrary contact means on positive-length
shared sides, singleton contacts at side endpoints, every physical
circle-corner mask and every nonnegative split of its positive total
circle load. It uses no generic selection of the BC normal.

## 1. A support-point fact for unit squares

If p minimizes u dot x over a unit square S, where u is a unit
vector, then

\[
                         p+\varepsilon u\in S
\tag{2}
\]

for every sufficiently small positive epsilon.

To see this at a vertex, use the orthonormal inward side axes v,w.
The minimum-support condition gives u dot v,u dot w nonnegative,
and u=(u dot v)v+(u dot w)w. A sufficiently short segment therefore
stays in the square. At a side-interior point u is the inward side
normal, so the assertion is immediate. Side endpoints are included
in the vertex argument. No strict exposure is required.

## 2. The entire BC normal cone is forced northwest

For this geometric step only, translate the intersection of the two
supporting A faces to zero and rotate their outward normals to e_x
and e_y. Then

\[
 A=[-1,0]^2,\qquad
 B\subseteq\{x\ge0\},\qquad C\subseteq\{y\ge0\}.
\tag{3}
\]

Their actual AB and AC applications have the forms

\[
                   P=(0,p),\quad Q=(q,0),
                  \qquad -1\le p,q\le0.
\tag{4}
\]

These are actual application means when a contact is a segment.
Choose any physical BC point T and let g=(g_x,g_y) be the actual
unit separating normal from B toward C. The two supporting
half-planes give

\[
                g\cdot P\le g\cdot T\le g\cdot Q,
                     \qquad T_x,T_y\ge0.
\tag{5}
\]

We claim

\[
                             g_x\le0,\qquad g_y\ge0.
\tag{6}
\]

First suppose g_x>0. If g_y<=0, then g dot P>=0 and g dot Q<=0.
Every term in (5) is zero. Thus P maximizes g on B. But P
minimizes e_x on B, so (2) gives P+epsilon e_x in B, with larger
g-projection. This is impossible. If g_y>0, then g dot T>=0 and
g dot Q<=0. Therefore T=0. This point minimizes e_x on B and
maximizes g on B, giving the same contradiction by (2). Hence
g_x<=0.

If g_y<0 as well, then g dot T<=0 and g dot P>=0, so both are
zero. When g_x<0 this forces T=0; when g_x=0 it still forces
T_y=0. In either case T minimizes e_y on C and minimizes g on C.
Equation (2) applied to C gives T+epsilon e_y in C, whose
g-projection is strictly smaller. This contradiction proves (6).

The proof covers a common triple junction P=Q=T, both endpoints
of every shared side, and arbitrary positions of T on the BC
contact. No assumption of three distinct applications was made.

## 3. The two circle-load vectors have negative scalar product

Return to the original origin for the circle. The translation in
Section2 only established the direction restriction (6); no
translated circle vector will be used. Let mu,nu,gamma>0 be the
AB,AC,BC force magnitudes and write

\[
 F_B=2\sum_{z\text{ on }B}\lambda_z z,
       \qquad
 F_C=2\sum_{z\text{ on }C}\lambda_z z.
\tag{7}
\]

Each sum has positive total weight. The exact tip force equations
are

\[
                F_B=\mu e_x-\gamma g,
                \qquad F_C=\nu e_y+\gamma g.
\tag{8}
\]

Consequently (6), the unit length of g and positivity of gamma
give

\[
 F_B\cdot F_C
       =\mu\gamma g_x-\nu\gamma g_y-\gamma^2<0.
\tag{9}
\]

On the other hand B and C physically touch. By
ACUTE_LOADED_CONTACT_GRAPH.md, TheoremA.2, every physical circle
corner of B has positive scalar product with every physical circle
corner of C under (1). Summing with their nonnegative circle
weights, each total positive, yields F_B dot F_C>0. This contradicts
(9) and proves the theorem.

## 4. Consequence for the remaining bowtie owner cover

If both articulation contacts have A-side owners, their normals are
axes of the same square. Opposite axes are excluded by
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md. Perpendicular axes are
excluded here. The only remaining alternative is a common
parallel direction, for which BOWTIE_PARALLEL_PRESSURE.md proves
c_A dot M>0 in the declared research window.

This does not yet close the acute nonparallel owner class in which
only one articulation contact has an A-side owner, nor any free
point-normal transition not removed by a separate valid selection.
No completion square has been omitted, and no Lean compilation,
CI, sampled pose or circle-mask restriction is used.
