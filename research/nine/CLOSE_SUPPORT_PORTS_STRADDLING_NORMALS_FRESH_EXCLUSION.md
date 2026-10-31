# Two close left ports with straddling outward normals cannot belong to a unit

**Status: complete fresh force-free geometric theorem, saved for full
independent review.** Hexagon supplied and re-derived the geometric argument;
triangle_bridges checked it and records the complete actual-feature proof.
No unavailable older source is used as a premise.

Let D be an actual unit square contained in the circle centered at O=0 with

\[
 R^2\le Q_*:=1105/256.
\]

Suppose two actual points P,Q of D have actual **outward** supporting unit
normals n,m, respectively, and satisfy

\[
 |P-Q|<1,\qquad P_x,Q_x<-29/30,\qquad
 |P_y|,|Q_y|<1/4,
\tag{1}
\]
\[
 n_x,m_x>0,\qquad n_y m_y<0,\qquad n\cdot m>0.
\tag{2}
\]

**Theorem.** These hypotheses are impossible. D has no prescribed force,
load, degree, physical circle mask, neighbor adjacency, or concurrence.
P,Q can be the original means of actual shared segments, including any
endpoints. No supporting normal or application is changed.

## 1. The complete two-port feature cover

We prove that both normals belong to the outward normal cone of one
actual vertex V among P,Q.

If P=Q, this point cannot be in a side interior, whose unique outward
normal would give n=m, contrary to the opposite strict vertical signs.
It is a vertex, and the conclusion follows.

Suppose P and Q are distinct. They cannot be two vertices: distinct
vertices of a unit square have distance at least one. If both are in
relative side interiors, their normals are the corresponding side axes.
The same face would give n=m; different adjacent faces would give
\(n\cdot m=0\); and opposite faces are distance at least one apart.
All possibilities contradict (1) or (2).

Thus one point, say P, is a vertex and Q lies in a side interior.
A nonincident side is distance at least one from that vertex, so Q is
on an incident side. Its actual outward normal m is one of the two
generators of P's outward normal cone, and n is in that same closed
cone by the support condition at P. This gives the asserted vertex V.

This argument also covers an axis normal chosen at a vertex: that point
is still treated as a vertex, not silently moved into a side interior.

## 2. The opposite actual corner exceeds the radius bound

Because n,m have positive horizontal components and opposite strict
vertical components, a positive linear combination is a positive
multiple of East. Their common vertex normal cone consequently contains
East. Let u,v be D's two orthogonal inward unit side vectors at V.
The dual supporting inequalities give

\[
 u_x\le0,\qquad v_x\le0.
\]

Since u,v are orthonormal, \(u_x^2+v_x^2=1\). Therefore

\[
 u_x+v_x\le-1.
\tag{3}
\]

Their vertical components have opposite weak signs. It follows that

\[
 |u_y+v_y|\le1.
\tag{4}
\]

The actual opposite corner V+u+v belongs to D. Using the port bounds
at this actual vertex and (3)--(4),

\[
\begin{split}
 |V+u+v|^2
 &=|V|^2+2+2V_x(u_x+v_x)+2V_y(u_y+v_y)\\
 &>\left(\frac{29}{30}\right)^2+2
       +2\frac{29}{30}-\frac12\\
 &=\frac{3931}{900}>\frac{1105}{256}\ge R^2.
\end{split}
\tag{5}
\]

The exact final reserve is

\[
 \frac{3931}{900}-\frac{1105}{256}
   =\frac{2959}{57600}>0.
\]

This contradicts actual containment. All feature limits permitted by
(1)--(2) were included; the strict numerical reserve comes from the
stated original port bounds. In particular the proof never identifies
support-line intersections with force-line concurrence.

## 3. Scope for subsequent callers

A caller must establish both original D ports, the two original outward
normals, their strict opposite vertical signs, and their positive dot
product. If its normals point **into** D, their signs must both be reversed
before applying (2). Merely having two nearby contacts or a small angle
between force lines is insufficient.

The argument is independent of any circle weights or normal-selection
theorem. It preserves all other actual squares and does not make any
whole graph or completion claim by itself.
