# A positive five-cycle cannot have four loaded bodies

**Status: complete hand exclusion; root and separate independent full hand audits
passed.** This theorem covers the entire four-load orbit of
C5 in C1.5.b0. It keeps both transmitter widths, every physical circle
mask, all actual shared-side means and all four completion squares.

Work in
\[
 R_*=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Suppose a selected positive component is exactly
\[
                         A-B-C-D-U-A,
\tag{2}
\]
where A,B,C,D have positive total circle load and U has zero load.
Use the existing strict point-normal and compatible diagonal-avoidance
convention. No new normal choices are made in this proof.

**Theorem.** The component (2) is impossible. This is a selected-core
exclusion, independent of the positions and orientations of the four
remaining physical squares. It uses no secondary replacement of the
packing and asserts no exclusion of a five-cycle subgraph whose vertices
have additional positive edges.

## 1. The actual transmitter line and the loaded circular order

The full domain theorem `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md`, Sections
1--3, gives proper positive radial concurrences q_A,q_B,q_C,q_D. They
form a strictly convex quadrilateral containing the origin. The channel
through U contracts to its side q_D q_A, with exact physical reserve
\[
                              w=1\quad\hbox{or}\quad\sqrt2.
\tag{3}
\]
The actual endpoint applications P_A,P_D obey
\[
 P_D-P_A=w e_x
\tag{4}
\]
after rotating the channel horizontally and labeling A as the left
endpoint. Orient the vertical axis toward the side of this line away
from the origin. The proper concurrences and actual applications are
then on one line
\[
 P_A=(l,h),\quad P_D=(l+w,h),\qquad h>0.
\tag{5}
\]
Indeed q_A,P_A,P_D,q_D occur in this order along the horizontal line,
with possibly zero endpoint reserves, and the origin is strictly on the
inward side of the force-polygon edge. Both endpoint circle-resultant
vectors therefore have strictly positive vertical components.

Write the endpoint centers as c_A=(x_A,y_A), c_D=(x_D,y_D). The actual
horizontal support inequalities at (5) give
\[
 x_D-x_A=w+H_A(e_x)+H_D(e_x)\ge w+1\ge2,
\tag{6}
\]
where H denotes a square's projection halfwidth. This remains exact for
any genuine shared-side application means.

Every circle-touching unit has center radius r satisfying
\[
                  \frac54<r< M:=\frac{91}{60}.
\tag{7}
\]
For the lower bound use r>=R-1/sqrt(2), R>=79/40 and
sqrt(2)<29/20. For the upper bound, a farthest corner gives
r^2+r+1/2<=R^2, whereas
\[
 M^2+M+\tfrac12=\frac{15541}{3600}
             =\frac{1105}{256}+\frac{31}{57600}.
\]
Since M<2, (6) now forces
\[
                           x_A<0<x_D.
\tag{8}
\]

For clarity, the concurrence quadrilateral and the physical centers
have the same cyclic order. Each physical circle corner is within
20 degrees of its center direction, and distinct boundary centers are
more than40 degrees apart, by
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, Section2. A positive
circle resultant lies between its body's physical circle corners.
Thus the four positive radial concurrence directions lie in disjoint
center intervals and inherit exactly their circular order. In the
orientation (5), that order is A,B,C,D around the lower side of the
channel and then D,A along the upper side. Section2 below identifies
which center arc is the upper one without a corner-mask assumption.

## 2. Both channel-endpoint centers are in the closed upper half-plane

We prove
\[
                              y_A,y_D\ge0.
\tag{9}
\]
This step retains a radial two-corner endpoint whose concurrence lies
outside its body.

Consider A, whose center has negative horizontal coordinate by (8).
If its frame is aligned with the displayed axes and y_A<0, all of its
farthest corners have negative vertical coordinate. In particular every
physical circle corner does, contradicting the strictly positive
vertical component of its circle resultant from (5). Therefore y_A>=0
in the aligned case. The endpoint y_A=0 is deliberately retained;
it may have two physical circle corners with unequal positive weights.

If A is oblique, its rightmost support is the single actual vertex
P_A. Write its inward orthonormal side vectors as
\[
 u=(-a,b),\quad v=(-b,-a),\qquad a,b>0,\quad a^2+b^2=1.
\tag{10}
\]
Then
\[
                       y_A=h+\frac{b-a}{2}.
\]
Assume y_A<=0. Since h>0, this implies a>b and
h<=(a-b)/2. Moreover
\[
                     c_A\cdot v=-b x_A-a y_A>0.
\]
Every farthest corner of A must therefore include the inward step v:
it is either P_A+v or P_A+u+v. Their vertical coordinates satisfy
\[
 h-a<0,\qquad h+b-a\le-\frac{a-b}{2}<0.
\tag{11}
\]
Every physical circle corner is a farthest corner. Thus again every
positive circle atom has negative vertical coordinate, a contradiction.
In the oblique case y_A is in fact strictly positive.

Reflection across the vertical axis gives the identical argument for D,
using x_D>0 and its leftmost support P_D. This proves (9), including
all physical one-corner and two-corner masks and all shared means.

Put
\[
 \delta_A=\arctan\frac{y_A}{-x_A},\qquad
 \delta_D=\arctan\frac{y_D}{x_D},\qquad
 0\le\delta_A,\delta_D<\frac\pi2.
\tag{12}
\]
The upper center arc from D to A has length
\[
                     \gamma=\pi-\delta_A-\delta_D\le\pi.
\tag{13}
\]
It is positive: their two center directions are distinct and in the
opposite horizontal half-planes. Their order agrees with the force
quadrilateral order established in Section1. Consequently the actual
boundary path A-B-C-D follows the complementary center arc, of length
2pi-gamma. No completion square, and no zero-weight physical boundary
contact, is removed in identifying this order.

## 3. Three boundary contacts force an almost-horizontal endpoint pair

Set
\[
                 \theta=\arccos\frac9{25},\qquad
                 \alpha=3\theta-\pi.
\tag{14}
\]
The minor center-angle gap at any physical contact of two boundary
squares is strictly less than theta. Indeed their center distance is
at most sqrt(2), and both radii exceed5/4 by (7), so
\[
 \cos(\text{minor gap})
 =1-\frac{|c_i-c_j|^2-(r_i-r_j)^2}{2r_ir_j}
 >1-\frac{16}{25}=\frac9{25}.
\tag{15}
\]
By the angular-neighbor contact rule, each of AB,BC,CD follows its
consecutive minor center arc. These are precisely the three arcs of
the ordered lower path in Section2. Hence
\[
                  2\pi-\gamma<3\theta,
 \qquad
                  \delta_A+\delta_D<\alpha.
\tag{16}
\]
The exact triple-angle identity gives
\[
                \cos\alpha=\frac{13959}{15625}=:c_0.
\tag{17}
\]
Here 0<alpha<pi/4. We will use the elementary strict bounds
\[
 \frac{89}{100}<c_0<\frac9{10},\qquad
 \sin\alpha<\frac9{20},\qquad
 \cos(\alpha/2)>\frac{97}{100}.
\tag{18}
\]
The sine bound follows by squaring from
c_0^2>319/400; the integer numerator difference is60613025 over
the positive common denominator400*15625^2. The half-angle bound
follows from c_0>89/100. These also give
\[
 \begin{split}
 \cos t+\sin t&<\frac{27}{20} &&(0\le t\le\alpha),\\
 \cos t+\sin t&<\frac{121}{100} &&(0\le t\le\alpha/2).
 \end{split}
\tag{19}
\]
For the first use monotonicity on [0,pi/4] and (18). For the second,
its square is1+sin(2t)<29/20<(121/100)^2.

## 4. The complete side-normal transmitter alternative is impossible

Suppose w=1. Each actual endpoint application is at distance at most
1/sqrt(2) from its own square's center, whether a vertex or a shared
mean. Equation (4) therefore gives
\[
                         |c_D-c_A|\le1+\sqrt2.
\tag{20}
\]
On the other hand (16) says gamma>pi-alpha. Using (7),(17),
\[
 \begin{split}
 |c_D-c_A|^2
 &=(r_D-r_A)^2+2r_Ar_D(1-\cos\gamma)\\
 &>\frac{25}{8}(1+c_0)
   =\frac{3698}{625}.
 \end{split}
\tag{21}
\]
This contradicts (20), since
\[
                 (1+\sqrt2)^2=3+2\sqrt2
                     <\frac{41}{7}<\frac{3698}{625}.
\tag{22}
\]
The first strict comparison uses sqrt(2)<10/7. All possible endpoint
frames and all transverse transmitter means were retained.

## 5. The complete diagonal transmitter alternative is impossible

Suppose w=sqrt(2). The compatible diagonal-avoidance convention at
point-only vertex contacts forces each transmitter endpoint to lie in
the relative interior of a side of its loaded neighbor. Both loaded
endpoint bodies therefore own the horizontal channel normal and have
frames parallel to the displayed axes. This is the exact diagonal
transmission conclusion in `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md`,
Section4; it is not an owner assumption on B or C.

Their horizontal center displacement is now exactly
\[
                        x_D-x_A=1+\sqrt2.
\tag{23}
\]
For either endpoint center, put r=|c| and let delta be its angle above
its own horizontal half-axis, as in (12). Its actual farthest-corner
circle equation is
\[
                 R^2=r^2+r(\cos\delta+\sin\delta)+\frac12.
\tag{24}
\]
This also holds at delta=0, when there are two physical circle corners.
It makes no assumption on their separate weights.

By (16), one of delta_A,delta_D is less than alpha/2 and both are
less than alpha. Denote the smaller-angle endpoint by index s and
its other endpoint by index b. Equations (19),(24) imply
\[
                             r_s>\frac43,
                  \qquad    r_b>\frac97.
\tag{25}
\]
For an exact check, if r_s<=4/3 the right side of (24) is less than
or equal to
\[
 \frac{16}{9}+\frac{121}{75}+\frac12
      =\frac{1751}{450}<\frac{6241}{1600}=R_*^2;
\]
the difference is137/14400. If r_b<=9/7 it is less than or equal to
\[
 \frac{81}{49}+\frac{243}{140}+\frac12
      =\frac{3811}{980}<\frac{6241}{1600};
\]
the difference is929/78400. Both contradict (1).

Together with (18), these radius bounds force
\[
 \begin{split}
 x_D-x_A
 &=r_A\cos\delta_A+r_D\cos\delta_D\\
 &>\frac43\frac{97}{100}+\frac97\frac{89}{100}
   =\frac{5119}{2100}
   >\frac{17}{7}>1+\sqrt2.
 \end{split}
\tag{26}
\]
Here the middle rational margin is19/2100, and the last strict
comparison again uses sqrt(2)<10/7. This contradicts the exact
horizontal displacement (23).

## 6. Full orbit conclusion and remaining scope

The transmission classification (3) is exhaustive, and Sections4--5
exclude both widths. The endpoint half-plane proof retained physical
one-corner and two-corner bodies, zero individual circle weights,
nonparallel and parallel endpoint frames, singleton applications and
all genuine shared-side means. B and C were used only as actual loaded
boundary neighbors with their original independently oriented frames.
Every completion square was left fixed throughout.

Consequently the entire four-load C5 orbit is excluded as a selected
positive component in (1). Combined with the existing complete load
cover, the C5 part of C1.5.b0 now retains only the three-load orbit
T-U-B-C-V-T, with nonparallel T and reserve pair(1,1) or(1,sqrt(2)),
up to reflection. Its whole completion bound remains a separate open
obligation. No numerical optimization, Lean compilation, CI, optional
contact deletion or post-certificate normal change is used here.
