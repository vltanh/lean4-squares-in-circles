# Two unloaded house hubs cannot share a side-axis contact

**Status: complete radius-free hand exclusion; root and separate independent full
hand audits passed.** The geometric argument was first identified
by the house-orbit analysis and is recorded here with every actual contact
mean retained.

Let A,D,T,B,C be five interior-disjoint unit squares with physical
contacts
\[
                 AD,\quad AT,\quad DT,\quad AB,\quad BC,\quad CD.
\tag{1}
\]
Suppose A and D have zero circle load and their entire positive
neighborhoods are exactly {D,T,B} and {A,T,C}, respectively. Every
one of the six listed edges has a strictly positive magnitude.
There may be additional zero-weight physical contacts.

**Theorem.** The AD normal cannot be a side axis of both A and D.
In particular a positive-length shared AD side is impossible. This
covers the complete shared-hub-contact alternative of the house middle
triple {2,3,4}, under the labeling A=1,D=5,T=3,B=4,C=2.

No force, load, circle-corner or degree condition is imposed on T,B,C
beyond (1). Thus the conclusion keeps all circle masks and every
completion square, and it requires no containing-radius bound or new
normal selection.

## 1. The roof triangle fixes the two horizontal signs

Rotate and translate so that the AD normal from A toward D is e_x,
with supporting line x=H. Since both bodies own this side axis,
\[
 A\subset\{H-1\le x\le H\},\qquad
 D\subset\{H\le x\le H+1\}.
\tag{2}
\]
Their frames are parallel to the displayed axes; their vertical
positions need not agree. The aggregate AD application is any actual
mean in their intersection. Its height will not be fixed or used.

Let a,b,d,c denote the actual outward unit normals from A to T,
from A to B, from D to T, and from D to C, respectively. Apply
`UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` to the physical triangle
A-T-D at A, using its owned AD axis e_x. Apply it again at D, using
its owned DA axis -e_x. The conclusions are
\[
                               a_x\ge0,
                    \qquad     d_x\le0.
\tag{3}
\]
Both zero cases are retained; the side-normal triangle theorem is
non-strict.

Write gamma>0 for the AD magnitude. The complete unloaded balances
at A,D are
\[
 \gamma e_x+\mu_T a+\mu_B b=0,
 \qquad
 -\gamma e_x+\nu_T d+\nu_C c=0,
\tag{4}
\]
where all four additional magnitudes are positive. Their horizontal
coordinates and (3) give the strict signs
\[
                               b_x<0<c_x.
\tag{5}
\]
These are the actual aggregate force normals; no application point or
shared mean was changed in obtaining them.

## 2. The lower pair is strictly separated by the hub interface

Choose the actual AB application p. The negative horizontal component
b_x in (5), together with A's aligned frame, forces
\[
                                p_x=H-1.
\tag{6}
\]
The point p is a minimum-b support point of B. The full support-span
lemma in `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md`, Section1,
with u=e_x and b dot u<0, yields
\[
                   \max_{z\in B}e_x\cdot(z-p)<1.
\]
Combining with (6),
\[
                                \max_{z\in B}z_x<H.
\tag{7}
\]
The support-span statement includes a vertex, a side-interior point
and every endpoint or weighted mean of a genuine shared segment.

Similarly the positive horizontal component c_x forces the actual
DC application q to have q_x=H+1. It is a minimum-c support point
of C. Use the same span lemma with u=-e_x to obtain
\[
                                \min_{z\in C}z_x>H.
\tag{8}
\]
The strict inequalities (7)--(8) make B and C closed-disjoint. This
contradicts the physical BC contact in (1) and proves the theorem.

## 3. Scope in the middle-triple house

The full middle-triple orbit has both hubs unloaded, so its entire
positive-length shared AD alternative is excluded by this theorem.
The argument also excludes any other actual AD force whose direction
is a side axis of both hubs. Under the retained strict point-normal
convention, an axis at a point-only vertex/vertex contact would already
be inadmissible, but that convention was not needed for this proof.

A singleton AD contact with an axis owned by only one hub, or with a
strict free vertex/vertex normal, is not covered by (2) and remains a
separate part of the complete middle-triple problem. No conclusion
about its full core or exterior completion capacity is inferred from
the present shared-hub exclusion. No numerical diagnosis, Lean
compilation or CI is used.
