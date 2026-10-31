# The complete parallel-bypass end-triple house is excluded

**Status: complete hand subfamily exclusion; root and separate independent full
hand audits passed.** Work in
\[
                 R_*:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Use the existing selected physical certificate, with its strict
point-only vertex/vertex normals. No new normal is selected here.

The house labels are those of FIVE_BODY_BICONNECTED_REDUCTION.md.
For the end-triple load mask \(\{1,2,3\}\), write
\[
 N=1,\qquad B=2,\qquad T=3,\qquad U=4,\qquad H=5.
\]
Thus the exact positive edges are
\[
                UN,\quad UB,\quad HN,\quad HB,\quad HT,\quad NT.
\tag{2}
\]
The bodies N,B,T have positive circle load, and U,H have zero load.
All four additional squares and all zero-weight physical contacts remain.

By UNIT_BYPASS_NORMAL_CHANNEL.md, U is a side-normal transmitter of
reserve1, and H is wholly on one transverse side of U. The theorem here
excludes **every** realization in which H has the same square frame as U.
It retains arbitrary actual shared-side means and both physical circle
masks at B. The tilted-bypass domain and the full house branch remain open.

## 1. The entire parallel-bypass geometric domain

Rotate, reflect and translate the coordinates so that
\[
 U=[0,1]\times[0,1],\qquad
 B\subset\{y\le0\},\qquad N\subset\{y\ge1\},
\tag{3}
\]
and H is to the right of U. The actual two U applications have the
same first coordinate. Since H touches both endpoints, its vertical
projection contains [0,1]. Its frame is assumed parallel to U and its
vertical width is one. Therefore
\[
                       H=[a,a+1]\times[0,1],\qquad a\ge1.
\tag{4}
\]
The disk center in these translated coordinates will be written
\(O=(X,Y)\); circle-load vectors always mean the actual vectors \(z-O\).

Both B and N must also be parallel to this frame. Indeed, if B were
oblique, its maximum-y support would be its unique vertex P. The UB
application and every HB contact must then equal P, since both occur
on y=0. Their first coordinates belong to both [0,1] and [a,a+1],
forcing a=1 and P=(1,0). But UB would then be a point-only
vertex/vertex contact carrying U's vertical side-axis normal. That
normal is not strictly exposing at the U vertex, contrary to the retained
point-normal convention. The reflected argument treats N.

Consequently the full domain is
\[
 B=[b,b+1]\times[-1,0],\qquad
 N=[n,n+1]\times[1,2],\qquad
                  a-1\le b,n<1,
\tag{5}
\]
with \(1\le a<2\). The lower bounds express physical contact with H.
The strict upper bounds follow because UB and UN have their prescribed
vertical transmitter normals: an endpoint value b=1 or n=1 would again
make that actual force a forbidden point-only axis endpoint. Positive
length side contacts, including endpoint-valued aggregate means, remain.

There are precisely two HB contact types: a shared horizontal segment
when b>a-1, or the point (a,0) when b=a-1. Likewise HN is a shared
horizontal segment when n>a-1, or the point (a,1) when n=a-1. The
point cases have the strict open quadrant normal cones of their two
diagonally adjoining aligned squares.

## 2. B cannot have two physical circle corners

The disk contains a top vertex of N at height2, so
\[
                         Y\ge2-R>-\frac12.
\tag{6}
\]
Thus every farthest corner of B is on its bottom side y=-1. Its only
possible two-corner mask has X=b+1/2. Put
\[
                       L=\sqrt{R^2-\frac14}.
\]
In that mask the circle equation gives Y=L-1. The window supplies
\[
                         \frac{19}{10}<L<\frac52.
\tag{7}
\]
For every corner of N, (5) gives the horizontal bound
\[
                 |x-X|\le |n-b|+\frac12\le\frac32.
\tag{8}
\]
Its vertical coordinates relative to O are 2-L and 3-L. By (7),
their absolute values are at most 3-L<11/10. Therefore every N
corner has squared distance from O strictly less than
\[
                   \frac94+\frac{121}{100}
                     =\frac{173}{50}<R_*^2.
\tag{9}
\]
This contradicts N's physical circle contact. Hence B has one physical
circle corner. This argument did not restrict either individual circle
weight in the two-corner alternative.

If HB were a shared segment, both positive B pair normals would be
vertical upward. B's resultant circle force would be vertical downward.
A unique physical circle corner of the aligned square B has a nonzero
horizontal coordinate relative to O, of absolute value greater than1/2.
It cannot supply that vertical resultant. Thus the complete remaining
HB geometry is
\[
                    b=a-1,\qquad P=(a,0),
\tag{10}
\]
and its actual outward normal from B toward H is (c,d), with
\[
                         c,d>0,\qquad c^2+d^2=1.
\tag{11}
\]

## 3. B's exact force and torque require d<=c

Let mu>0 be the UB magnitude and nu>0 the HB magnitude. Let lambda>0
be B's circle magnitude, with the common factor2 absorbed. Because the
two pair normals are e_y and (c,d), its circle force points strictly
southwest. Its unique physical circle corner is therefore
\[
 z=(a-1,-1),\qquad z-O=(-s,-t),\qquad s>\frac12,\ t>0.
\tag{12}
\]
Write the actual UB mean as (xi,0). It is allowed to be either
endpoint of the true shared segment. Equations (5),(10) give
\[
                a-1\le\xi\le1,\qquad k:=a-\xi\in[0,1].
\tag{13}
\]
The two force components and the torque about the actual HB point P
are exactly
\[
 \lambda s=\nu c,\qquad
 \lambda t=\mu+\nu d,\qquad
 \lambda(t-s)=\mu k.
\tag{14}
\]
For the last identity, the UB moment is -mu k and
\(z-P=(-1,-1)\), whose determinant with \(\lambda(-s,-t)\)
is lambda(t-s). Thus t>=s.

Put r=d/c. Eliminating the magnitudes in (14) yields
\[
                         t-s=k(t-sr).
\tag{15}
\]
If k=0, then t=s and the positive force mu in (14) gives r<1.
If k>0, then k<=1 and t>=s imply
\[
                  kr=1-\frac ts(1-k)\le k.
\tag{16}
\]
In every allowed mean and endpoint case,
\[
                                  d\le c.
\tag{17}
\]
No circle-center normalization or reflected-load replacement entered
this calculation.

## 4. A shared HN segment requires the opposite strict inequality

Suppose n>a-1. The HN force from H is alpha e_y, alpha>0,
at its actual mean Q=(zeta,1), where
\[
                         a\le\zeta\le n+1<a+1.
\tag{18}
\]
Write the HT magnitude as beta>0 and its outward normal from H as m.
Horizontal force balance at H gives beta m_x=nu c>0.

In fact m_y>0. If m_y<0, the actual HT application is H's bottom-right
vertex (a+1,0). Apply the strict unit support-span lemma
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, Section1, to T at this
minimum-m support point and u=e_y. Every point of T then has y<1,
so T cannot physically touch N. If m_y=0, T lies in x>=a+1,
whereas N has maximum first coordinate n+1<a+1. That also prevents NT.

Thus the actual HT application is the top-right vertex
\[
                              Q_T=(a+1,1).
\tag{19}
\]
Take the H torque equation about Q_T. The HB contribution is
nu(d-c), the HN contribution is -alpha(a+1-zeta), and the HT
contribution vanishes. Hence
\[
                   \nu(d-c)=\alpha(a+1-\zeta)>0.
\tag{20}
\]
This contradicts (17). Every actual HN mean, including both endpoints
of its positive-length shared segment, was retained in (18).

## 5. The point HN alternative is geometrically impossible

It remains that n=a-1, so HN is the point (a,1). Its normal from H
is strictly northwest, say (-u,v) with u,v>0. The horizontal H force
equation again gives m_x>0 for its roof neighbor T, because both
HB and HN have strictly negative first components from H.

Exactly as in Section4, m_y<0 would put all T below y=1, and m_y=0
would put all T in x>=a+1; neither permits contact with N. Therefore
m_y>0, and the HT application is again (a+1,1).

Apply the same support-span lemma now with u=-e_x. Since m_x>0,
every point of T has
\[
                                  x>a.
\tag{21}
\]
But n=a-1 gives max_x N=a. The closed squares N,T cannot touch,
contrary to the positive NT edge. This excludes the entire point-HN
case, without any assumption on the normal owner at NT or HT.

## 6. Exact conclusion and remaining house work

Sections2--5 cover both HB types and both HN types, the unique and
two-physical-corner masks at B, all transmitter means and all other
contact owners. Hence no end-triple house in (1) has its clear bypass
parallel to its side-normal transmitter. The reflected end-triple orbit
has the same exclusion.

Every surviving end-triple house must therefore have a genuinely tilted
bypass H. Its full pose, the independently oriented boundary bodies,
all zero-weight physical contacts and all four exterior completion
squares remain. This manuscript does not close that tilted family,
the middle-triple or four-load house, or C1.5.b0.

No numerical sampling, Lean compilation, CI, secondary motion of the
packing or post-certificate normal change is used.
