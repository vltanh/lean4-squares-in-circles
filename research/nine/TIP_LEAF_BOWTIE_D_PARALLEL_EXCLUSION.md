# A D leaf at a bowtie tip: the entire parallel articulation is impossible

**Status: complete whole-interface hand argument; root and separate
independent full audits passed.** Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 D=\sqrt{R^2-\frac14}-1,\qquad s=1+\sqrt2-R.
\tag{1}
\]
The exact positive graph is \(H-A-B-H\), \(H-C-E-H\), and the
leaf \(A-L\). The leaf L is radial D. A has exact degree three,
H has degree four, and B,C,E have degree two. All three remaining
physical units remain present.

**Theorem.** The two triangle reactions at A cannot be parallel.
Together with TIP_LEAF_BOWTIE_D_NONPARALLEL_EXCLUSION.md, this
excludes the entire D-leaf alternative of the tip-attached
bowtie-leaf layout. No S-leaf alternative is asserted.

## 1. The full wall and actual mean cover

The radial-D leaf puts
\[
 A=[-s,1-s]\times[h-1,h],\qquad0<h<1,
\tag{2}
\]
with its positive eastward force applied at \((1-s,0)\).
Its two other positive normals, if parallel, cannot be opposite:
the two neighboring squares would then be beyond opposite supports
of A and could not physically touch. Their positive sum balances
the eastward leaf force, so both normals are \(-e_x\).

Let their positive magnitudes be \(\mu,\nu\), and their actual
applications be
\[
                 P=(-s,y)\in A\cap B,\qquad Q=(-s,z)\in A\cap H.
\tag{3}
\]
These are the true weighted means when the contact has a shared side.
The whole units B,H lie in \(x\le-s\) and each attains \(x=-s\).
A's exact torque is
\[
                              \mu y+\nu z=0.
\tag{4}
\]

The degree-two triangle bodies B,C,E are loaded. The usual
unit-transmitter argument proves this without assuming their masks.
H is physically circle-clear, since H,C,E cannot be a physical
triangle of boundary bodies. A is physically clear by its radial leaf.

The exact radius window gives
\[
                 \frac13<s<\frac49,\qquad D<\frac{61}{60}.
\tag{5}
\]
Every point of a boundary unit has norm at least
\(R-\sqrt2=1-s\). Therefore
\[
                      s^2+y^2\ge(1-s)^2,\qquad |y|>\frac13.
\tag{6}
\]
Reflect vertically so \(y>0\). Equation (4) then gives \(z<0\).

Let g be the B-to-H unit normal, T its actual application, and
\(\gamma>0\) its magnitude. It cannot be horizontal. If \(g=e_x\),
the B-to-H separation puts H in \(x\ge-s\), contrary to its
positive width and its containment in \(x\le-s\).
If \(g=-e_x\), then H's maximum x is at most B's minimum x,
which is strictly less than \(-s\), contrary to (3).
Thus
\[
                                  g_y\ne0.
\tag{7}
\]
This includes every mutual owner, free normal and side mean.

## 2. The loaded tip determines the vertical force sign

We use the nonparallel part of the proper-concurrence calculation
in TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1.
That source's boundary-neighbor premise is used only to rule out
parallel forces in the first paragraph. Its subsequent
normal-line calculation proves the following conditional statement
for arbitrary neighboring units:

> If the two positive pair forces of a loaded square are nonparallel,
> their lines meet at a positive multiple of its circle resultant,
> behind both actual outward applications.

For a physical unique corner, that intersection lies in the unit;
for a two-corner mask it may lie outside, but the positive radial
coefficient and the behind-contact conclusion still hold. Individual
zero corner weights and coincident applications are included in
that calculation. We have independently supplied nonparallelism
in (7), so no boundary-neighbor premise is being imported for B.

B's true force equation is
\[
                         F_B=-\mu e_x-\gamma g.
\tag{8}
\]
Its AB normal line is horizontal through P. Its proper concurrence
therefore has height y. Since \(y>0\) and the radial coefficient is
positive, \((F_B)_y>0\). Equation (8) gives
\[
                                  g_y<0.
\tag{9}
\]

## 3. The true opposite-petal resultant lies in one controlled sector

Let M be the sum of the circle resultants of the exact degree-two
tips C,E. Keep their complete physical triangle with H. The
degree-four H equation and the two tip torque equations give
\[
 \begin{split}
                   M&=-\nu e_x+\gamma g,\\
             -\nu\det(Q,e_x)+\gamma\det(T,g)&=0.
 \end{split}
\tag{10}
\]
The end-triangle theorem gives
\[
                         M\ne0,\qquad h_H(M/|M|)<D.
\tag{11}
\]

The H-to-A normal is \(e_x\), and the H-to-B normal is \(-g\).
The purely geometric behind-ports statement in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 2, applies
to the physical unit triangle H,A,B, with no force equation or
boundary condition at its root. Since these normals are nonparallel,
their lines intersect at q and
\[
                       Q=q+\alpha e_x,\qquad\alpha\ge0.
\tag{12}
\]
Thus \(q_x\le-s<0\) and \(q_y=z<0\).
Equation (10) says \(\det(q,M)=0\).
Also \(M_y=\gamma g_y<0\), so q is a positive multiple of M.

Put \(w=-z>0\). For some angle \(\theta\),
\[
             \frac M{|M|}=(-\cos\theta,-\sin\theta),\qquad
                        0<\theta\le\arctan(w/s).
\tag{13}
\]
This controls the true whole-petal direction. Neither its magnitude
nor its two individual circle forces has been replaced by a leaf.

## 4. A whole-frame support estimate from a right support point

Let any unit square S lie in \(x\le-s\) and contain the right
support point \(Q=(-s,-w)\), where \(s,w>0\).
For \(e=(-\cos\theta,-\sin\theta)\), \(0\le\theta\le\pi/2\), we claim
\[
                         h_S(e)\ge Q\cdot e+\cos\theta.
\tag{14}
\]

If Q belongs to a vertical support side, the actual point
\(Q-e_x\) belongs to S, proving (14), including every endpoint
and interior mean. Otherwise Q is its unique rightmost vertex.
Its inward orthonormal side vectors are
\[
                  u=(-\cos\beta,\sin\beta),\qquad
                  v=(-\sin\beta,-\cos\beta),
                   \qquad0<\beta<\pi/2.
\]
The support increment from Q is exactly
\[
                   \max(\cos(\beta+\theta),0)+\sin(\beta+\theta).
\tag{15}
\]
If \(\beta+\theta\le\pi/2\), this is at least1 and hence at least
\(\cos\theta\). Otherwise sine decreases on the interval
\([\pi/2,\pi/2+\theta]\), so (15) is at least
\(\sin(\pi/2+\theta)=\cos\theta\). This proves (14) for every
frame and every actual Q.

Apply it to H and the sector (13):
\[
                     h_H(M/|M|)\ge(s+1)\cos\theta+w\sin\theta.
\tag{16}
\]
The right side is concave on
\([0,\arctan(w/s)]\), so its minimum is at an endpoint.
The endpoint values are
\[
                   1+s,\qquad
          \sqrt{s^2+w^2}+\frac{s}{\sqrt{s^2+w^2}}.
\tag{17}
\]
Both are at least \(2\sqrt s\). Consequently
\[
             h_H(M/|M|)\ge2\sqrt s>
                   \frac2{\sqrt3}>\frac{61}{60}>D,
\tag{18}
\]
contradicting (11).

## 5. Whole D-leaf conclusion and scope

This proof has retained every actual AB,AH,BH application mean,
both physical B circle masks, every mutual-contact owner and
every free normal. The nonparallel B concurrence was obtained from
the actual common-wall geometry, not from a fictitious boundary
neighbor. The only equation at H is its genuine degree-four
equation with the whole C,E petal.

The parallel and nonparallel D articulation cases are exhaustive.
The present source and
TIP_LEAF_BOWTIE_D_NONPARALLEL_EXCLUSION.md therefore exclude the
entire D-leaf type of this six-body tip-attached bowtie-leaf layout
in the common selected certificate. All three extras remain fixed.

The S-leaf type and therefore the parent C2.33.b1 cell remain open
until separately closed. No sampled pose, angle subdivision,
completion motion, Lean compilation or CI is used.

