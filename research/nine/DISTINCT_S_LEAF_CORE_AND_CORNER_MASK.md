# The remaining S/S triangle has one C corner, but its positive cores exist

**Status: two complete hand implications; root and independent full hand audits passed.**
This source concerns the entire remaining C1.3.b2 layout: a triangle
A,B,C with radial S leaves at the two distinct articulations A,B,
in the high-radius domain

\[
          \frac{\sqrt{17}}2<R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]

First, C necessarily has exactly one physical circle corner, not
merely one positive corner weight. Second, an explicit positive
five-body core exists strictly inside (1), with fixed side normals
and strictly interior shared-side application means. Thus a blanket
core exclusion for this whole S/S family is false. Its required
universal exit is a completion capacity of at most three further
unit squares, or a complete classification with that capacity for
every family. No such capacity is asserted here.

## 1. A uniform support bound behind a radial outward support

**Lemma 1.1.** Suppose p=d e is an outward support point of a unit
square A in the unit direction e, with d>=1. For every unit u with
e dot u<=0,

\[
                             h_A(u)\le1.
\tag{2}
\]

*Proof.* If p is a vertex, write
\(A=p+[0,1]v+[0,1]w\) with orthonormal inward axes and
\(e=-a v-b w\), a,b>=0, a^2+b^2=1. Put
\(u=xv+yw\). The hypothesis is ax+by>=0, and

\[
 h_A(u)=-d(ax+by)+\max(x,0)+\max(y,0)
       \le-ax-by+\max(x,0)+\max(y,0).
\tag{3}
\]

If x,y>=0, the last expression is at most
\(\sqrt{(1-a)^2+(1-b)^2}=\sqrt{3-2(a+b)}\le1\).
If x,y<=0 it is nonpositive. In the mixed case x>=0>=y, write
x=cos theta, -y=sin theta. The constraint gives
\(0\le\theta\le\arctan(a/b)\), with zero-component endpoints
handled directly. The function
\((1-a)\cos\theta+b\sin\theta\) increases up to the right
endpoint of this interval: its unconstrained maximum has tangent
\(b/(1-a)=(1+a)/b>a/b\). Its endpoint value is b<=1.
The other mixed case is symmetric.

If p is side-interior, use the inward axis -e and a tangential axis.
For c=e dot u<=0, the inward normal span is -c and the tangential
span is at most sqrt(1-c^2). Thus
\(h_A(u)\le(d-1)c+\sqrt{1-c^2}\le1\). This includes the full
range of side means and finishes the proof. \(\square\)

## 2. Every physical two-circle-corner mask of C is excluded

Put d=sqrt(R^2-1/4)-1>1. If C had two physical circle corners,
it would be a radial S square in some unit direction u, and every
point of C would have u-projection at least d. Since C touches both
A and B, Lemma 1.1 forces

\[
                        e_A\cdot u>0,\qquad e_B\cdot u>0.
\]

Every circle corner of C has u-projection d+1>0, so its nonzero
circle resultant m_C does also, regardless of whether one or both
corner multipliers are positive. But global force balance is

\[
                    \alpha e_A+\beta e_B+m_C=0,
                    \qquad\alpha,\beta>0.
\]

Its projection on u is strictly positive, a contradiction. Thus C
has exactly one physical circle corner. In particular its two pair
forces cannot be parallel: the radial S alternative has just been
excluded, and radial D parallel forces have zero triangle moment,
already excluded by `TRIANGLE_DISTINCT_LEAVES_DOMAIN.md`.

## 3. An exact surviving positive core

Let

\[
 x=\frac{\sqrt{70}-8}{4},\qquad \delta=x^2,\qquad d=1+\delta,
 \qquad R^2=(d+1)^2+\frac14.
\tag{4}
\]

Then

\[
 \frac9{100}<x<\frac1{10},\qquad
                  8x+2x^2=\frac34.
\tag{5}
\]

For the bounds, square 209/25<sqrt(70)<42/5. In particular
\(R^2>17/4\), while

\[
 R^2<\left(\frac{201}{100}\right)^2+\frac14
       =\frac{42901}{10000}<\frac{1105}{256}.
\tag{6}
\]

The last exact comparison is 10982656<11050000. Thus the core lies
strictly inside the remaining radius interval, not at an excluded
endpoint.

Take the three central squares

\[
 \begin{aligned}
 A&=[\delta,\delta+1]\times[x-1,x],\\
 B&=[\delta-1,\delta]\times[2x-1,2x],\\
 C&=[\delta-1,\delta]\times[2x-2,2x-1].
 \end{aligned}
\tag{7}
\]

The first leaf is

\[
                        L_A=[d,d+1]\times[-1/2,1/2].
\tag{8}
\]

For the other, put

\[
 p=(\delta-1,2x),\qquad n=p/d,
 \qquad L_B=\{p+u n+v Jn:0\le u\le1,\ |v|\le1/2\}.
\tag{9}
\]

Since \(|p|^2=(1-x^2)^2+4x^2=(1+x^2)^2=d^2\), n is
unit. Both leaves are precisely radial S squares with equal-radius
outer corner pairs.

### 3.1. Exact containment

The outer corners of each leaf have squared norm
\((d+1)^2+1/4=R^2\); its other corners have smaller norm.
The unique farthest corner of C is

\[
                        z_C=(\delta-1,2x-2).
\]

Its squared norm is

\[
 |z_C|^2=5+2x^2+x^4-8x
        =\frac{17}{4}+4x^2+x^4=R^2,
\tag{10}
\]

using (5). Its two coordinate intervals have unique far endpoints,
so it has only this one physical circle corner.

For A, its maximum squared corner norm is
\(d^2+(1-x)^2<(101/100)^2+1<17/4\). For B it is
\((1-\delta)^2+(1-2x)^2<2<17/4\). Thus both articulations
are strictly circle-clear, as required.

### 3.2. Every pair is physically nonoverlapping

The three squares in (7) have disjoint open interiors. Their actual
shared segments are

\[
 \begin{array}{ll}
 AB:&\{\delta\}\times[2x-1,x],\\
 AC:&\{\delta\}\times[x-1,2x-1],\\
 BC:&[\delta-1,\delta]\times\{2x-1\}.
 \end{array}
\tag{11}
\]

All have positive length. L_A is separated from A by x=d, and
from B,C by a strict horizontal gap. Its common side with A is
\(\{d\}\times[-1/2,x]\).

The vector n has negative first and positive second components.
B's unique maximum-n support point is p, and L_B starts at its
minimum-n side through p. Thus their interiors are disjoint, with
the actual vertex/side contact p. For L_B's other pairs,

\[
 \max_{L_B}X=\delta-1+\frac{x}{d}<\delta,
\]

which strictly separates it from A and L_A. Also

\[
 \min_{L_B}Y=2x-\frac{1-\delta}{2d}>2x-1=max_CY,
\]

which strictly separates it from C. This verifies all ten physical
pairs, including the nonneighbor pairs of the positive graph.

## 4. A strictly positive physical force-and-torque certificate

Use outward pair normals in the convention
\(\sum\mu n+2\sum\lambda z=0\). Define positive magnitudes

\[
 u=1-\delta,\qquad v=2(1-x),\qquad
 w=\frac{u(1-x)}x,
 \qquad \alpha=\frac ux,
 \qquad \beta=\frac{d(1-x)}x.
\tag{12}
\]

Assign AC magnitude u, BC magnitude v, AB magnitude w, and the
two leaf edges magnitudes alpha and beta. Their actual means are

\[
 \begin{aligned}
 P_{AB}&=(\delta,x(1-x)),\\
 P_{AC}&=(\delta,-(1-x)^2),\\
 P_{BC}&=(-u(1-x)/2,2x-1),\\
 P_{A L_A}&=(d,0),\qquad P_{B L_B}=p.
 \end{aligned}
\tag{13}
\]

All three triangle means are strictly inside their physical segments
(11). For AB, 0<x(1-x)<x and 2x-1<0. For AC, the differences
from its lower and upper endpoints are respectively x(1-x)>0
and x^2>0. For BC,
\(-u<-u(1-x)/2<0<\delta\). The A-leaf mean (d,0) is also
strictly inside its common side. The B-leaf mean is the midpoint of
that leaf's inner side and the strictly supported upper-left vertex
of B.

Set the C circle multiplier to 1/2. At each outer corner of L_A
use multiplier \(\alpha/[4(d+1)]\), and at each outer corner
of L_B use \(\beta/[4(d+1)]\). These are all strictly positive;
there are no other circle atoms.

The two leaf circle-force sums are alpha e_x and beta n, and

\[
                      \beta n=(-w,v),\qquad z_C=(-u,-v).
\tag{14}
\]

Thus the three central body force sums are, respectively,

\[
 \begin{array}{ll}
 A:&(\alpha,0)+(-w,0)+(-u,0)=0,\\
 B:&(w,0)+(0,-v)+(-w,v)=0,\\
 C:&(u,0)+(0,v)+(-u,-v)=0.
 \end{array}
\tag{15}
\]

The leaf pair forces are the negatives of their circle sums, so each
leaf balances too. Every bridge and circle force has zero origin
moment. The three directed triangle moments A to B to C to A are
exactly equal to

\[
                    H=u(1-x)^2>0:
\]

\[
 w(P_{AB})_y=H,\qquad
 -v(P_{BC})_x=H,\qquad
 -u(P_{AC})_y=H.
\tag{16}
\]

Therefore all five body torque equations also hold. A's two cycle
forces are parallel, a genuine retained alternative of the port
orientation theorem.

Every positive pair normal is an actual side axis. In particular,
there is no free vertex/vertex normal whose generic selection could
remove this core. Rescaling all weights gives any desired positive
normalization of the same certificate.

## 5. Exact implication for the unfinished theorem

The support lemma closes every physical two-circle-corner mask of C
for the entire S/S family. The exact construction proves that the
remaining unique-corner family has realizable positive cores strictly
inside (1), including the parallel-articulation chart and strict
shared means. It is not a nine-square counterexample and makes no
claim about how many further squares fit.

The subsequent full reduction and classification are now completed in
DISTINCT_S_LEAVES_PARALLEL_ARTICULATION_REDUCTION.md and
DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md. The upper/lower capacity sources
prove that every member of the entire exact slider family admits at most
three additional arbitrary unit squares. TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md
assembles the whole cell. This positive control remains valid and is
accounted for by that capacity theorem. No numerical optimization,
Lean compilation or CI is a premise of either result here.
