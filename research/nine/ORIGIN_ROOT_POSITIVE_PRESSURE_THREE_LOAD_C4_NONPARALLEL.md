# Positive outside pressure and an origin-containing C4 root exclude parallel three-load ports

**Status: complete uniform hand implication; root and separate
independent full hand audits passed.**

Work in the original nine-square packing, with
\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Suppose the selected positive graph contains the actual cycle
\[
                              H-A-B-C-H.
\tag{2}
\]
H is physically circle-clear. A,B,C are positively circle-loaded
of true positive degree two. H may have arbitrary additional
positive neighbors, and every other original square remains.
Let
\[
                         S=F_A+F_B+F_C
\]
be the three actual circle resultants. Assume that the unchanged
rest of the physical certificate supplies a resultant M satisfying
\[
                          S+M=0,\qquad c_H\cdot M>0,
                          \qquad O\in H.
\tag{3}
\]
The origin-containment premise is closed containment; the origin
may initially be on a side or vertex. M is an actual resultant,
not a replacement physical body or a newly imposed force at H.

Use the compatible strict and fixed-application normal selections
already made before extraction of the physical multiplier certificate.

**Theorem.** The actual H-to-A and H-to-C normals are nonparallel.
No degree-two equation is imposed at H, and no outside force is
deleted. The theorem applies to every original endpoint mean,
physical B mask and individual zero corner weight.

## 1. Full opposite/equal normal cover at the actual block

Write n,m for the two actual root-to-tip unit normals,
\(\mu,\nu>0\) for their magnitudes and \(P_A,P_C\) for their
unchanged applications. Sum only the true A,B,C force and
origin-moment equations. Every internal pair force cancels at
its actual common application and every circle force has zero
origin moment. Thus
\[
 S=\mu n+\nu m,\qquad
 \mu\det(P_A,n)+\nu\det(P_C,m)=0.
\tag{4}
\]
No equation at H has been truncated. By (3), S is nonzero.

The complete boundary-path cone theorem gives
\[
                    F_B=\lambda F_A+\eta F_C,\qquad
                         \lambda,\eta>0,
\tag{5}
\]
and the endpoint force directions have a strict angular
difference between zero and pi. This is the unchanged physical
A-B-C path; no outside degree enters that theorem.

Both actual endpoint stars have a physical boundary neighbor B.
The full proper-concurrence input used in
TRIANGLE_C4_THREE_LOAD_PARALLEL_DOMAIN.md, Section 1, therefore
gives positive radial concurrence points
\[
                 q_A=P_A+t_A n,\qquad q_C=P_C+t_Cm,
                           \qquad t_A,t_C\ge0.
\tag{6}
\]
Each point is a positive multiple of its original endpoint
circle resultant, with all physical one-/two-corner masks
retained. The input uses only these actual degree-two endpoint
equations and B's physical boundary status.

If \(m=-n\), use (n,Jn) coordinates. Equation (4) makes the
transverse application coordinates satisfy
\(\mu y_A=\nu y_C\). If nonzero, they have the same strict sign.
Equations (5),(6) then give that sign to all three transverse
circle resultants, contradicting S parallel to n. If both
coordinates vanish, both endpoint circle resultants lie on the
n axis, contradicting their strict nonparallel force-cone order.
This excludes the whole opposite-normal alternative.

Suppose henceforth \(m=n\). The moment equation gives
\(\mu y_A+\nu y_C=0\); neither height can vanish, by the same
strict force-cone argument. They have opposite signs. H must
own the actual common side axis n: otherwise its support is a
single vertex and the two transverse coordinates coincide.
Rotate n to \(-e_x\), reflect or exchange A,C as necessary, and
write
\[
 \begin{gathered}
 H=[-s,1-s]\times[l,l+1],\\
 P_A=(-s,y),\quad P_C=(-s,-w),\qquad
 y,w>0,\quad y+w\le1.
 \end{gathered}
\tag{7}
\]
Both heights are the original contact means.

## 2. The origin and genuine pressure supply the whole needed wall range

The actual common support is \(s=h_H(-e_x)\). From (4),
\(S=-(\mu+\nu)e_x\), so (3) gives \(c_H\cdot(-e_x)<0\).
Since H has width one in that actual side direction,
\[
                             s-\frac12<0.
\tag{8}
\]
Closed origin containment gives \(s\ge0\). Put \(r=R-\sqrt2\).
Every point of a physical boundary square has norm at least r,
so the two actual applications satisfy
\[
                         y,w\ge\sqrt{r^2-s^2}.
\tag{9}
\]
The radius window gives \(r^2>5/16\). Since \(s<1/2\), the
radicand in (9) is positive. Combining (9) with (7) gives
\[
                  r^2-s^2\le\frac14,\qquad
                  s\ge\sqrt{r^2-\frac14}>\frac14.
\tag{10}
\]
In particular the possible s=0 origin-boundary alternative is
excluded by these exact inequalities. The complete actual range is
\[
                           \frac14<s<\frac12.
\tag{11}
\]

For either P in (7), its opposite endpoint height and (9) yield
\[
 \begin{split}
 |P|^2
 &\le s^2+\left(1-\sqrt{r^2-s^2}\right)^2\\
 &=1+r^2-2\sqrt{r^2-s^2}\\
 &<1+r^2-2\sqrt{r^2-\frac14}<\frac{13}{16}.
 \end{split}
\tag{12}
\]
The last comparison is the complete decreasing-function bound on
\(5/16<r^2<49/100\), with endpoint value13/16. Meanwhile
\[
       d=\sqrt{R^2-\frac14}-1>\frac{91}{100},\qquad
              d^2>\frac{13}{16}.
\tag{13}
\]
Every point of a physical two-circle-corner unit has norm at least d.
Thus both A and C are physically unique, including all initially
allowed individual zero weights. No circle weight has been reset.

Equations (7),(10)--(13) give exactly the full wall hypotheses used
by the two endpoint scalar theorems. The end-triangle support bound
from the earlier exact HXY component is not used here; its role
in obtaining a positive s is replaced by the actual premise O in H.

## 3. Endpoint theorems have precisely these local wall hypotheses

The aligned endpoint description and the complete tilted frame
follow from the actual unique corner and proper concurrence, as
in Section 5 of TRIANGLE_C4_THREE_LOAD_PARALLEL_DOMAIN.md:
\[
 \begin{split}
 &A=[-s-1,-s]\times[Y-1,Y],
                \quad Y=\sqrt{R^2-(s+1)^2}
                &&\text{in the aligned case},\\
 &A=P_A+[0,1](-a,b)+[0,1](-b,-a),\quad
             0<a\le b,\quad a^2+b^2=1
                &&\text{in the tilted case}.
 \end{split}
\tag{14}
\]
The original aligned mean ranges over its true side interval.
The lower endpoint has the reflected description.

For explicit dependency scope, the full proof of
TRIANGLE_C4_ALIGNED_WALL_TIP_SIGN.md uses only (1),(7),(11)--(14),
the actual degree-two endpoint equations and containment of its
boundary neighbor. Its strict support bound excludes a westward
outgoing normal at every aligned endpoint. It uses no H, X or Y
force equation once those wall hypotheses are supplied.

Likewise the full proof of
TRIANGLE_C4_TILTED_WALL_OUTER_FACE_EXCLUSION.md uses only the same
wall hypotheses, the true endpoint concurrence and actual B
containment. Its whole rectangle, original application identity
and exact positive polynomial apply unchanged. Hence a westward
tilted endpoint cannot use its outer lower face, for every actual
shared mean and both endpoints.

These are applications of the scalar proofs to their explicit
geometric premises, not applications of an exact smaller-component
theorem after deleting an outside force.

## 4. Complete all-mask force assembly without an outside degree assumption

The actual B force equation remains
\[
                         F_B=\gamma_Ag_A+\gamma_Cg_C,
                             \qquad\gamma_A,\gamma_C>0.
\tag{15}
\]
Its physical circle corners are acute to the northwest A corner
and southwest C corner, so each has negative first coordinate.
The endpoint equations give \((g_A)_y<0<(g_C)_y\). Thus at
least one outgoing normal is westward.

Section 3 makes such an endpoint tilted. Its complete feature
cover leaves its actual lower vertex. Both its contacts are
distinct physical singletons. The prior simultaneous fixed-tip
selection removes its free normal, and the strict physical
convention makes that contact B-owned. Write
\(g_A=(-c,-d_1)\), where \(c,d_1>0\) and \(c^2+d_1^2=1\).
Its whole cone gives
\[
                         f_A=cb_A+d_1a_A\ge c.
\tag{16}
\]
This is exactly the local calculation in Section 2 of
TRIANGLE_C4_THREE_LOAD_PARALLEL_EXCLUSION.md.

If both endpoints are westward, their B-owned axes are orthogonal.
The original B minimum supports give an actual corner with first
coordinate at most
\[
                         -s-\frac12-\sqrt2<-R.
\]
If only A is westward, the complete nonwest C feature domain retains
every side mean and the possible coincident application, and gives
\[
                         (T_C)_x\ge-s-1,\qquad
                         (T_C)_y\ge-w.
\]
The actual width-one identity of B then gives
\[
                           f_A+1-c\le d_1(y+w)\le d_1<1,
\]
contrary to (16). These are the exhaustive two force alternatives,
proved in Sections 3--4 of the full wall assembly. Only true
equations at A,B,C enter them. There is no distinct-application
or concurrence assumption at B.

This contradicts the equal-normal case and proves the theorem.

## 5. Entire genuine two-leaf corollary and its exact nonclaim

Suppose the actual positive component is
\[
                       H-A-B-C-H,\qquad H-L_1,\ H-L_2,
\tag{17}
\]
with both L_i genuine degree-one leaves and A,B,C positively loaded
of true degree two. H has true degree four. The two genuine leaves
supply the complete S/S,S/D,D/D alternatives.

The physical central-disk theorem used in
TWO_LEAF_ROOT_NO_UNLOADED_TRANSMITTER.md, Section 1, gives
\(O\in H\) over every alternative: for d<1 or d>1 it lies in
the open interior, while at d=1 the exceptional actual root has
O at a vertex. The closed premise needed above includes that
entire exception.

Each genuine leaf gives strictly positive actual root pressure:
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md covers S, and for D
\[
                  c_H\cdot e=R-\sqrt2-\frac12>0.
\]
This full S/D argument is written in
TWO_LEAF_ROOT_OPPOSITE_C4_EXCLUSION.md, Section 1, and assumes
nothing about the other H neighbors. Consequently
\(M=F_{L_1}+F_{L_2}\) satisfies (3), by summing all original
component force equations. Every individual S corner weight and
original H/leaf mean remains.

The theorem therefore excludes the entire parallel-root part of
the three-block-load C4/two-leaf orbit, for all S/S,S/D,D/D pairs,
with three arbitrary physical completion squares retained. In
the labels A-B-C-D-A of
FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md, this is the BCD
block-load orbit's complete parallel-at-root subfamily.

The nonparallel BCD family remains open. This corollary does not
close that whole load orbit, the same-root attachment layout or
C1.4.b2. It uses no canonical minimizer and makes no claim about
all original equality packings.

## 6. Six complete same-root parallel attachment families

The same implication applies to a positive component consisting of
the actual three-loaded C4 (2), k genuine leaves at H and t intact
end triangles at H, where
\[
                         k\ge2,\qquad k+2t\le5.
\tag{18}
\]
Every triangle has two actual positively loaded degree-two tips.
Each core tip A,B,C keeps true degree two; H has its real degree
\(2+k+2t\). The component has \(4+k+2t\) bodies and every one of
the \(5-k-2t\) remaining physical squares stays in the packing.

Any two genuine leaves give the same closed origin-containment
premise at H, with arbitrary other H forces allowed. Each actual
leaf has positive root pressure by Section 5. Every intact triangle
has positive root pressure by the complete uniform theorem in
BOWTIE_CELL_CLOSED.md, Section 2; that theorem explicitly allows
arbitrary additional positive neighbors at its articulation.
Sum these genuine inequalities, and sum all actual component
force equations, to obtain exactly (3).

Thus the whole parallel-root domain is excluded in all six
integer attachment families:
\[
\begin{array}{c|c|c|c|c}
 k&t&\text{component bodies}&\deg(H)&\text{arbitrary extras}\\ \hline
 2&0&6&4&3\\
 3&0&7&5&2\\
 4&0&8&6&1\\
 5&0&9&7&0\\
 2&1&8&6&1\\
 3&1&9&7&0
\end{array}
\tag{19}
\]
Every genuine S/D assignment, relative attachment pose, physical
tip mask and original mean is included. The proof uses no root
permutation or load-set symmetry. It does not delete an attached
triangle's forces or replace its two physical bodies by one leaf.

The nonparallel part of each family remains open. These are six
whole parallel attachment/load subfamilies within larger open
coarse cells, not six coarse-cell closures.

More generally, the uniform theorem is available wherever its
actual origin-containment, positive outside pressure and true
degree-two A/B/C hypotheses are proved. It does not manufacture
those premises in a different attachment. All nine squares,
outside forces, original contact means and physical masks stay
in the problem. No Lean compilation or CI is used.
