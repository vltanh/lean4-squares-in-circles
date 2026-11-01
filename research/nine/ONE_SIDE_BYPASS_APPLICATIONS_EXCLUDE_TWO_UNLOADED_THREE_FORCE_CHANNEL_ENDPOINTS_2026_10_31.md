# Two unloaded channel endpoints cannot use one side of their unit bypass

Date: October 31, 2026. Author: four_chain continuation.

**Status: complete new hand proof, frozen for independent review.**
Root suggested the acute-normal common-side test. The full equality
geometry and endpoint torque exclusion below are the new construction
of this author. No earlier source or original status is changed.

## 1. Exact actual-star theorem

Let A,B,C,U be four distinct actual closed unit squares with disjoint
open interiors. All units of the original packing lie in one closed
disk of radius R, where

\[
2R<3+\sqrt2.                                      \tag{1}
\]

In particular (1) holds throughout R^2<=1105/256. Retain the original
physical force-and-torque certificate and its existing strict singleton
vertex/vertex convention: a positive singleton vertex/vertex pair
cannot have a normal on a side-axis endpoint of either square's common
normal cone. No new normal is selected in this proof.

The full positive stars of A,C,U are exactly

\[
A:\{B,U,Z_A\},\qquad C:\{B,U,Z_C\},\qquad U:\{A,C\}.
                                                               \tag{2}
\]

A and C have true full degree three: each displayed three-element
neighbor set consists of different actual squares.

All three A,C,U are unloaded in the original selected-circle sense.
The outside neighbors Z_A,Z_C are actual squares and may coincide with
each other. B has arbitrary full degree, circle load and physical mask.
Every original contact application or full shared mean remains fixed.

Let p and q be the original AB and BC applications, regarded as actual
support points of B. Suppose p and q lie on one closed side of B.

**Theorem. These hypotheses are impossible.**

The result is a full physical-star implication. B is not assigned a
three-force equation. The third A/C forces are not required to be
genuine leaf forces, radial forces or already loaded terminal forces.

## 2. The normal channel makes the common-side case exact

The original U2 equations propagate one signed normal n and magnitude
mu>0 from A to C. Full torque makes its endpoint applications differ
by w n, where w is the actual transmitter width, one or sqrt(2).
The unit-bypass theorem `UNIT_BYPASS_NORMAL_CHANNEL.md`, Sections 1--2,
applies with the actual B touching both endpoints. It gives w=1 and
side-normal U. Its hypotheses place no restriction on B's degree.

Consequently

\[
\operatorname{dist}(A,C)=1.
\]

Indeed every A-to-C displacement has projection at least one on n,
and the original U application displacement attains that distance.
Since p is in A, q is in C, and their common B side has length one,

\[
1\le |q-p|\le1.
\]

Thus p,q are the two endpoints of that side and q-p=n. The latter
identity follows either from equality in the support projection or
from uniqueness of the minimizing displacement in the convex set C-A.

After one orthogonal change of the entire physical datum, take

\[
B=[0,1]\times[0,1],\quad
p=(0,1),\quad q=(1,1),\quad n=(1,0).
\]

Then A lies in x<=0, C lies in x>=1, and the actual side transmitter is

\[
U=[0,1]\times[v,v+1].
\]

Disjoint open interiors of B,U give v>=1 or v<=-1. The two unchanged
U applications have the form (0,t),(1,t), with t in [v,v+1].

## 3. Actual endpoint frames and all original mean endpoints

Both p=(0,1) and (0,t) belong to the maximum-x support face of A.
If that face were one vertex, these points would coincide. This would
give t=1, v=1 and the lower-left vertex of U. The actual positive AU
contact would be singleton vertex/vertex, with its horizontal channel
normal an own-side axis of U. That contradicts the unchanged strict
singleton convention. Hence A owns a vertical support side. The same
argument at C gives a vertical minimum-x side.

Therefore, for some real a,c,

\[
A=[-1,0]\times[a,a+1],\qquad
C=[1,2]\times[c,c+1],
\]

and both intervals contain 1 and t.

If v<=-1, then t<=0. A unit interval containing 1 and t must have
t=0 and equal [0,1]; the same holds at C. Also v=-1. But then AU
is only the singleton aligned vertex pair (0,0), with its horizontal
side-axis normal, again forbidden. Thus v>=1 and t>=1.

Because A,U are aligned, a zero-length physical intersection would
again be a singleton vertex/vertex pair with forbidden channel-axis
normal. Their actual intersection on x=0 has positive length; its
original weighted mean is still allowed to be either endpoint. Hence
a+1>v>=1. Since a<=1, this gives 0<a<=1. Similarly 0<c<=1. We obtain

\[
1\le t\le2.                                       \tag{3}
\]

No midpoint or strict-interior assumption has been made about t.

## 4. Complete endpoint torque forces both exits predominantly horizontal

Write the original outward normals from B as

\[
n_{BA}=(-\alpha,\beta),\quad
n_{BC}=(\gamma,\delta),\qquad
\alpha,\beta,\gamma,\delta\ge0,
\]

with alpha^2+beta^2=gamma^2+delta^2=1. These signs follow from the two
actual B support vertices p,q. Let their positive magnitudes be
lambda_A,lambda_C. The channel magnitude is the same mu>0 at A,C.

The full translation at A makes its third force vector

\[
f_A=(-\lambda_A\alpha-\mu,\ \lambda_A\beta).
                                                               \tag{4}
\]

If beta=0, this vector is horizontal to the left. Its actual
application has x=-1, and the immediate neighbor Z_A contains a
point with x=-2 by the unit inward-support-segment fact.

If beta>0, the AB contact p minimizes n_BA on A. Its y coordinate
therefore equals A's lower side a, giving a=1. The third force in
(4) has strictly negative x and positive y components, so its
original application is exactly the opposite vertex

\[
Q_A=(-1,2).
\]

Take moments of the COMPLETE A equation about p=(0,1). The AB term
vanishes; the U term is -mu(t-1); and the third term is
lambda_A(alpha-beta)+mu. Thus

\[
\lambda_A(\beta-\alpha)=\mu(2-t).
                                                               \tag{5}
\]

It follows from (3)--(5) that the absolute horizontal component of f_A
is at least its vertical component:

\[
(\lambda_A\alpha+\mu)-\lambda_A\beta=\mu(t-1)\ge0.
\]

The normalized third force u_A therefore satisfies
-(u_A)_x>=1/sqrt(2). The actual terminal Z_A contains Q_A+u_A, hence
has a point with

\[
x\le-1-1/\sqrt2.                                 \tag{6}
\]

The beta=0 case satisfies (6) as well.

The full C equation is the reflected calculation, without a change
of any mean. Its third force vector is

\[
f_C=(\lambda_C\gamma+\mu,\ \lambda_C\delta).
\]

If delta=0 its actual neighbor contains a point with x=3. If delta>0,
then c=1, its third application is Q_C=(2,2), and full torque about
q=(1,1) gives

\[
\lambda_C(\delta-\gamma)=\mu(2-t).
\]

Thus its normalized third force u_C has (u_C)_x>=1/sqrt(2), and the
actual Z_C contains Q_C+u_C. In either case Z_C has a point with

\[
x\ge2+1/\sqrt2.                                  \tag{7}
\]

The elementary support fact used here is valid for every application:
if Q is a minimum-u support point of an actual unit square, then
Q+u belongs to it. In own coordinates the nonzero signed components
of u are each at most one, and the unit step goes into the coordinate
intervals. It includes a shared side and its mean endpoints.

The two actual points supplied by (6)--(7) are in the original disk.
Their horizontal separation is at least 3+sqrt(2), contrary to (1).
This proves the theorem. It does not matter whether Z_A and Z_C are
different squares: both actual points must lie in that same disk.

For the target radius, R<25/12 and sqrt(2)>4/3 give

\[
2R<25/6<13/3<3+\sqrt2,
\]

so the contradiction includes the closed R^2=1105/256 endpoint.

## 5. Acute bypass normals and the remaining unicyclic row

For any two original support normals n_1,n_2 of a unit square, if
n_1.n_2>0 then their actual support applications lie on one closed
side. To check this elementary normal-fan statement, if one normal
is an own axis, positive dot product forces the other support vertex
or side onto that same side. If neither is an own axis, both support
applications are vertices. They cannot be opposite vertices because
the two normal-coordinate products would both be negative. Identical
or adjacent vertices belong to a common closed side. This includes
arbitrary means on an owned support side.

Therefore the theorem excludes every original instance of (2) with

\[
n_{BA}\cdot n_{BC}>0.
\]

More generally it excludes the whole common-side application feature,
including any nonacute normal pair whose actual applications share
one side. It does not rely on the B force or torque equation.

In the remaining three-port unicyclic (t,s)=(1,0) row, take U to be
its one true transmitter and B the opposite hub. Its other two hubs
A,C have precisely the complete stars (2), with their direct exits.
Every literal original hypothesis is then supplied by the row, under
the existing strict singleton convention of the selected certificate.
Thus every surviving such row has nonpositive bypass-normal dot
product and applications on different closed sides of B.

This does not yet exclude that remaining obtuse/orthogonal feature,
the direct-triangle (0,0) row, or a whole coarse nine-square parent.
It also does not transfer a conclusion from a three-force endpoint
to an endpoint with an additional positive force.

All calculations above are hand calculations. No mathematical script,
pose search, sampled angle, Lean, build or CI was used. Independent
source-level review is required before adoption.
