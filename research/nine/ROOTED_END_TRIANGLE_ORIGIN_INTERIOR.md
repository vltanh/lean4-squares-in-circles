# Every intact loaded end triangle has its root strictly around the origin

Date: October 26, 2026.

**Status: complete uniform hand theorem, accepted after the full-source reviews
REVIEW_END_TRIANGLE_ORIGIN_INTERIOR_ROOT_2026_10_26.md and
REVIEW_END_TRIANGLE_ORIGIN_INTERIOR_GLOBAL_2026_10_26.md.**
No original checklist label is changed by this source.

Work in the common compatible selected physical certificate in

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]

Let the three actual interior-disjoint unit squares H,T1,T2 have all
three positive triangle edges. The tips T1,T2 have their exact positive
degree two and positive circle load. H may have arbitrary additional
positive forces and arbitrary true positive degree. Every other physical
square, additional zero-weight physical contact, actual common application
mean, physical circle mask and individual zero corner weight remains.

**Theorem.** The original containing-circle origin O belongs to the open
interior of H.

Consequently, two intact loaded end triangles in the same selected packing
cannot have distinct roots. This conclusion concerns their actual root
squares, not an identification or a replacement of either end triangle by
a leaf or a radial contact.

The proof uses only the genuine degree-two equations at T1,T2 and the
accepted whole end-triangle pressure and common-side theorems. In particular
it does not infer their pressure from a truncated force equation at H.
H is in fact physically circle-clear: if it physically touched the circle,
H,T1,T2 would be a forbidden triangle of physical boundary squares by
CIRCLE_CONTACT_ANGULAR_ORDER.md. Thus its actual circle load is zero for a
geometric reason, independently of the number or directions of its other
forces. No positive root circle force is removed by a choice of stress.

## 1. Exact retained inputs and a lower bound at every boundary contact

Write n1,n2 for the actual outward H-to-Ti unit normals, mu1,mu2>0
for their magnitudes, and p1,p2 for their actual common applications.
For a shared side, pi is the original aggregate mean in the actual closed
intersection segment. Put

\[
 F_i=2\sum_{z\text{ on }T_i}\lambda_z z,
 \qquad M=F_1+F_2=\mu_1 n_1+\mu_2 n_2.
\tag{2}
\]

Summing the two true tip origin-moment equations cancels their mutual
contact at its actual common application and gives

\[
             \mu_1\det(p_1,n_1)+\mu_2\det(p_2,n_2)=0.
\tag{3}
\]

The complete end-triangle pressure theorem, BOWTIE_CELL_CLOSED.md,
Section 2, gives

\[
                          c_H\cdot M>0.
\tag{4}
\]

END_TRIANGLE_COMMON_SIDE.md gives an actual side of H, with outward
unit side axis N, which contains both p1,p2 and satisfies

\[
                       M\cdot N>0,
               \qquad P:=h_H(N)<\frac{39}{40}<1.
\tag{5}
\]

Its proof already includes parallel normals, shared-mean endpoints,
all root/tip/free owners and every physical circle mask. The common side
is the side supplied by the actual features; it is not chosen afresh to
favor a later estimate.

If n1,n2 are nonparallel, END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md,
Sections 2--3, gives their genuine intersection q with

\[
 q=-tM,\quad t>0,\qquad
 p_i=q+a_i n_i,\quad a_i\ge0.
\tag{6}
\]

At either loaded tip the two original force lines are nonparallel: that
tip has the other tip as a physical boundary neighbor. The full proper
concurrence lemma, TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1,
gives a positive radial concurrence q_i and

\[
             q_i=\tau_i F_i,\quad\tau_i>0,
             \qquad q_i=p_i+\ell_i n_i,\quad\ell_i\ge0.
\tag{7}
\]

Only the tip equations are used in (6)--(7). There is no fictitious
degree-two equation at H, and no assertion that a two-corner tip's
concurrence is inside that tip.

The two actual circle resultants F1,F2 cannot have the same direction.
One direct justification, retaining zero individual corner weights, is
that distinct physical boundary-center directions differ by more than
pi/5, from CIRCLE_CONTACT_ANGULAR_ORDER.md, Lemma 2.1, while each nonzero
nonnegative weighted circle resultant is within pi/12 of its own center
direction, from FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md, Section 1.
Coincident resultant directions would put the center directions less
than pi/6 apart, a contradiction. The latter local angle estimate does
not require a four-body path or its force balance.

Finally every actual point p belonging to a circle-touching unit obeys

\[
                       |p|\ge R-\sqrt2>\frac{67}{120}.
\tag{8}
\]

Indeed choose one of that unit's actual circle corners z. Its diameter
gives |z-p|<=sqrt(2), so |p|>=R-sqrt(2). The strict last comparison
follows from R>=79/40 and sqrt(2)<17/12. This argument concerns physical
circle contact and does not require that the chosen corner's weight be
positive.

## 2. A common-side normal-line fact with all endpoint cases

Rotate and, later when useful, reflect the common-side frame of (5), so

\[
 H=[P-1,P]\times[Y-\tfrac12,Y+\tfrac12],\qquad N=e_x,
 \qquad M_x>0,
 \qquad p_i=(P,y_i).
\tag{9}
\]

Every actual outward normal at that side has (n_i)_x>=0. Its transverse
component is positive only at the upper endpoint of that side, negative
only at the lower endpoint, and zero only in the direction e_x.
This is the exact normal cone of the closed square; it includes the
tangential side axes at the endpoints and every possible shared mean.

Suppose n1,n2 are nonparallel and take q from (6). Then

\[
 q_x\le P,
 \qquad
 \min(y_1,y_2)\le q_y\le\max(y_1,y_2).
\tag{10}
\]

The first assertion follows separately from
P-q_x=a_i(n_i)_x>=0. Here is a full proof of the second.
If p1=p2, the two nonparallel lines meet there, so q=p1=p2.
Otherwise their transverse normal components cannot both be strictly
positive or both be strictly negative: that would place both actual
points at the same upper or lower endpoint. If either transverse normal
component is zero, its equation in (6) gives q_y equal to that actual
application's height. In the remaining case the components have opposite
signs. The positive one belongs to the upper endpoint and gives q_y no
larger than that height; the negative one belongs to the lower endpoint
and gives q_y no smaller than that height. This proves (10), including
zero proper lengths and tangential normal endpoints.

The genuine origin moment (3), in the same frame, is exactly

\[
                 P M_y=\sum_{i=1}^2\mu_i y_i(n_i)_x.
\tag{11}
\]

No port is replaced by a side midpoint in (9)--(11).

## 3. Nonparallel root forces: the common side has positive height

Write (6) in the form

\[
 q=-s(1,k),\qquad s=tM_x>0,
 \qquad k=M_y/M_x.
\tag{12}
\]

Suppose for contradiction that P<=0 and put p=-P>=0. The strictly
positive pressure (4), divided by M_x, is

\[
                    -p-\frac12+Yk>0.
\tag{13}
\]

Thus Y and k are both nonzero and have the same sign. Reflect the
transverse coordinate if necessary so that Y>0 and k>0. Relation (10)
and the actual side interval in (9) give

\[
       s\ge p,\qquad -sk=q_y\ge Y-\frac12,
       \qquad 0<Y<\frac12,
       \qquad sk\le\frac12-Y.
\tag{14}
\]

Combining (13)--(14), using p>=0 and treating p=0 by the same weak
inequality, gives

\[
 p\left(p+\frac12\right)
 \le pYk
 \le Y\left(\frac12-Y\right)
 \le\frac1{16}.
\tag{15}
\]

If p>=1/8, the left side is at least5/64>1/16. Consequently

\[
                              0\le p<\frac18.
\tag{16}
\]

By (10) and q_y=-sk<0, at least one actual application has y_i<0.
Its membership in the original side interval and Y>0 imply

\[
                   -\frac12<Y-\frac12\le y_i<0.
\tag{17}
\]

That actual point therefore satisfies

\[
 |p_i|^2=p^2+y_i^2<\frac1{64}+\frac14=\frac{17}{64}.
\tag{18}
\]

But

\[
       \left(\frac{67}{120}\right)^2-\frac{17}{64}
                         =\frac{83}{1800}>0.
\tag{19}
\]

Equations (18)--(19) contradict (8), since p_i belongs to the original
circle-touching tip Ti. Thus

\[
                                  P>0.
\tag{20}
\]

This part uses the strictly positive whole end-triangle pressure, its
proper negative concurrence and an actual physical boundary contact.
It uses neither the full force equation at H nor any lower bound R>2.

## 4. Nonparallel root forces: the actual side ports straddle height zero

Since q_x=-s<0<P, equation P-q_x=a_i(n_i)_x implies

\[
                           a_i>0,\qquad (n_i)_x>0
                           \quad(i=1,2).
\tag{21}
\]

Suppose first that y1,y2>=0. Relation (10) makes q_y>=0, so (12)
gives M_y<=0. The right side of (11) is nonnegative, while P>0,
so (11) gives M_y>=0. Hence M_y=0. Because mu_i>0 and both
(n_i)_x are strictly positive, (11) then forces y1=y2=0.
The two actual ports coincide at (P,0), so their two nonparallel lines
have q=(P,0), contradicting q_x<0<P.

The alternative y1,y2<=0 is excluded by reflecting the same argument:
(10) gives M_y>=0, (11) gives M_y<=0, and again both ports would
coincide at (P,0). Therefore the two actual heights satisfy

\[
                          \min(y_1,y_2)<0<\max(y_1,y_2).
\tag{22}
\]

In particular Y-1/2<0<Y+1/2. Equations (5),(20) give
P-1<0<P. Both coordinate inequalities are strict, proving

\[
                                 O\in\operatorname{int}H
\tag{23}
\]

in the entire nonparallel root domain.

## 5. The full parallel root domain

Two parallel outward root normals cannot be opposite: the two tips
would lie beyond opposite supports of H, separated by its positive
width, and could not physically touch. Thus

\[
             n_1=n_2=e=\frac M{|M|},\qquad e\cdot N>0.
\tag{24}
\]

### 5.1. A common strict vertex direction is impossible

If e is not the common-side axis N, then in the frame (9) it has a
nonzero transverse component and strictly positive x-component. It
strictly exposes one vertex of H. Both actual root applications are
therefore the same vertex p. Equation (3) gives det(p,e)=0.
The pressure (4) gives c_H·e>0, and, since p maximizes e on H,

\[
 p\cdot e=c_H\cdot e+\frac{|e_x|+|e_y|}{2}>0.
\tag{25}
\]

Consequently p=r e with r>0. The two genuine loaded-tip concurrences
in (7) now satisfy

\[
                     q_i=(r+\ell_i)e,\qquad r+\ell_i>0.
\tag{26}
\]

Both actual circle resultants Fi would have the same direction e,
contrary to Section 1. This excludes the complete strict-vertex
parallel alternative, including coincident original means.
A transverse root side axis has e·N=0 and is already incompatible
with (24); it is not a missing endpoint of this case.

### 5.2. A common root side axis gives strict origin containment

The remaining possibility is e=N=e_x. The actual common side in
(9) is the maximizing side for both original normals. Equation (4)
then gives

\[
                           P-\frac12>0.
\tag{27}
\]

The original moment equation (11) is

\[
                              \mu_1y_1+\mu_2y_2=0.
\tag{28}
\]

Its two strictly positive coefficients imply that either the heights
have strictly opposite signs or both are zero. In the latter case,
(7) and (27) give q_i=(P+ell_i,0) with P+ell_i>0, so the two actual
circle resultants would again have the same direction e_x. That is
impossible. Hence the heights have strictly opposite signs.

Together with 1/2<P<39/40<1, this proves all four strict inequalities
placing O inside the original rectangle (9). Thus (23) also holds
throughout the parallel domain.

Sections 3--5 exhaust every root interface and prove the theorem.

## 6. Uniform consequence for distinct end-triangle roots

Suppose two intact loaded end triangles in one original packing have
distinct actual root squares H and K. Apply the theorem separately
to their true degree-two tips. Both H and K contain O in their open
interiors, contradicting the original pairwise interior disjointness.

The two end triangles may be joined by bridges, further cyclic blocks,
or arbitrary other positive connections. Those connections and their
forces are not deleted. The consequence needs only the two true loaded
tip pairs at their respective roots; it does not require a degree bound
at either root, a statement about the graph between them, or a
support-minimizing certificate beyond the common selection already used
by the pressure and common-side inputs.

This is stronger than excluding a particular orientation or force mask
of the three-triangle chain. An exact coarse-cell assembly can apply it
to the two different roots of that original chain, while the same-root
bouquet uses the unchanged positive-pressure sum. No such assembly or
ledger update is implicitly asserted by merely saving this source.

The theorem retains all actual squares and all force weights, including
individual zero circle weights. It uses no sampled pose, new normal
selection after extraction, physical displacement, numerical certificate,
Lean compilation or CI.
