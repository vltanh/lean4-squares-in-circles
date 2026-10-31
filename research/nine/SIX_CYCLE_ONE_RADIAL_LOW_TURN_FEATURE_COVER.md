# Complete actual feature cover at a nonobtuse unique turn in the one-radial C6

Date: October 26, 2026.

**Status: accepted complete analytic original-domain cover**, after
full review in REVIEW_C6_RADIAL_LOW_TURN_FEATURE_COVER_ROOT_2026_10_26.md. This source identifies the remaining low-turn domain without
replacing a mean, normal or physical mask. It excludes every outer-axis
owner at once and supplies a stronger local near-corner angle bound for
\(R\ge2\). It does not yet exclude all rows of the remaining cover.

Retain the original alternating all-side C6 with one physically radial
loaded unit S, two physically unique loaded units, and three true unloaded
degree-two side-normal transmitters. Keep both individual circle weights
at S, all positive channel forces, all original side means and their
endpoints, all three transmitter sliders and all nine physical squares.
The original radius window is \(79/40\le R\le\sqrt{1105}/16\);
when all nine squares are used, NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md
supplies \(R>2\).
The zero-individual-radial-weight endpoints already have their separate
accepted exclusion; they are not converted to physical-unique masks here.

The complete local unique-turn theorem is Section 1 of
SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md. Its local calculation has
no diagonal or all-unique premise. The positive concurrence triangle
and strict positive turns come from the accepted full all-mask
simple-cycle force-polygon prerequisites.

## 1. Precisely one unique turn can be at most a right angle

Write the turns as \(\theta_S,\theta_B,\theta_C\). The complete
local theorem gives
\[
 0<\theta_B,\theta_C\le3\pi/4,\qquad 0<\theta_S<\pi,\qquad
                     \theta_S+\theta_B+\theta_C=2\pi.
\tag{1}
\]
If both unique turns were at most \(\pi/2\), their sum with
\(\theta_S<\pi\) would be less than \(2\pi\). Thus in the
remaining domain there is exactly one unique unit L with
\[
 0<\theta_L\le\pi/2,
\]
while the other unique unit T satisfies
\[
 \pi/2<\theta_T\le3\pi/4,\qquad 3\pi/4\le\theta_S<\pi.
\tag{2}
\]
In particular the radial right-turn family is not part of this residue.

The T endpoint has the already accepted complete strict-turn
A/M/O/T feature cover. The purpose of the following sections is
to give a complete actual cover at L, including all original
axis means and their coincidences.

## 2. A whole-channel support bound excludes every outer side axis

This fact is local to any actual reserve-one channel from a unit Q
to a contained unit W. Let n be its unchanged direction out of Q
and let \(h_Q(n)\) be its original support. The true channel equation
and the minimum directional halfwidth of a unit give
\[
 h_Q(n)+1+\frac12\le n\cdot c_W\le |c_W|\le d+\frac12,
 \qquad d=\sqrt{R^2-\frac14}-1.
\]
Consequently
\[
                              h_Q(n)\le d-1=:\delta.
\tag{3}
\]
Throughout the original radius window, \(\delta<1/60\).
No degree or circle-weight equation at the far endpoint is used.

At a physically unique unit, choose positively oriented actual
own axes so its circle corner is \(z=(a,b)\), with
\(a,b>1/2\). The unit is
\[
                         [a-1,a]\times[b-1,b].
\tag{4}
\]
Its outer-axis supports are a and b. Since each incident original
channel has reserve one, (3) excludes either positive outer axis
as an actual normal. This removes both outer-axis possibilities
from the complete local unique-turn proof, uniformly in every
actual mean and force ratio.

The two remaining axis supports also give useful exact bounds:
an incoming bottom-axis owner has \(b\ge1-\delta>59/60\);
an outgoing left-axis owner has \(a\ge1-\delta>59/60\).
If both occur, both bounds hold. They are necessary bounds on the
original unit, not replacements of its coordinates.

## 3. Exact own-coordinate parameters and every remaining row

At L its two pair lines have a genuine proper concurrence
\[
 q=\tau z,\qquad 0<\tau\le1,\qquad q\in L.
\]
Put
\[
 t=1-\tau,\qquad X=1-ta,\qquad Y=1-tb,\qquad
                 0\le X,Y\le1,\quad 0\le t<1.
\tag{5}
\]
Use coordinates relative to the actual opposite vertex
\(P_{00}=(a-1,b-1)\), so the other non-circle vertices are
\[
 P_{10}=P_{00}+(1,0),\qquad P_{01}=P_{00}+(0,1).
\]
The point \(P_{11}=z\) is unshareable.

Orient the original force polygon counterclockwise. The incoming
and outgoing directed channel normals are \(n_-,n_+\);
their actual outward normals at L are \(-n_-,n_+\).
The origin-moment signs permit only incoming outer-right or
inner-bottom axes and outgoing outer-top or inner-left axes.
Section 2 removes the two outer axes. A remaining owned axis is
an actual genuine shared interface: opposing parallel unit faces
have positive overlap, because a singleton vertex/vertex contact
with the selected side-axis normal is prohibited by the original
strict point-normal convention.

The complete remaining low-turn cover is the following table.
Every displayed coordinate is relative to \(P_{00}\).
A vector in the direction columns is proportional to the actual
directed unit normal by a strictly positive factor.

| Actual owner pattern | Incoming application \(p_-\) | Outgoing application \(p_+\) | Directed incoming/outgoing vectors | Exact additional low-turn restrictions |
| --- | --- | --- | --- | --- |
| No owner; two adjacent-to-circle vertices | \((1,0)\) | \((0,1)\) | \((X-1,Y)\), \((-X,1-Y)\) | \(0<t<1/(a+b)\); the turn is strictly less than \(\pi/2\). |
| No owner; same inner left side | \((0,0)\) | \((0,1)\) | \((X,Y)\), \((-X,1-Y)\) | \(a>b,\ 0<X,Y<1,\ t>0,\ 1-t(2a+b)+t^2R^2\le0\). |
| No owner; same inner bottom side | \((1,0)\) | \((0,0)\) | \((X-1,Y)\), \((-X,-Y)\) | \(b>a,\ 0<X,Y<1,\ t>0,\ 1-t(a+2b)+t^2R^2\le0\). |
| Incoming bottom axis only | \((X,0)\) | \((0,1)\) | \((0,1)\), \((-X,1-Y)\) | \(t>0,\ 0<X<1,\ 0\le Y<1,\ b\ge1-\delta\); the turn is strictly acute. |
| Outgoing left axis only | \((1,0)\) | \((0,Y)\) | \((X-1,Y)\), \((-1,0)\) | \(t>0,\ 0<Y<1,\ 0\le X<1,\ a\ge1-\delta\); the turn is strictly acute. |
| Both inner axes | \((X,0)\) | \((0,Y)\) | \((0,1)\), \((-1,0)\) | Full (5), \(a,b\ge1-\delta\), and \(\theta_L=\pi/2\); all mean endpoints and any coincidence remain. |

Here \(a^2+b^2=R^2\) everywhere. The parameters X,Y are linked
by the same original t in (5); the table does not introduce
independent slider choices for them. All original contact
restrictions and pairwise nonoverlap remain additional premises.

### 3.1 Why the non-owner rows are exhaustive

If neither actual normal is an L side axis, the complete local
proof shows that the two applications are distinct vertices and
neither can equal q. Its argument uses only this unique unit
and its two actual true side transmitters, so applies unchanged
in the present physical-radial mask at the third load.

The origin moments leave precisely the three vertex pairs in
the first three rows. For example the moment of the opposite
vertex normal has the sign of \(a-b\) on the incoming channel
and the opposite sign on the outgoing one. The zero-vector
alternative would place q at \(P_{00}\) with \(a=b\); a distinct
adjacent application would then have an L side-axis normal,
outside the non-owner case.

In the first row, strict vertex support gives \(t>0,\ X,Y>0\).
The determinant of the two displayed vectors is
\(1-t(a+b)\). The original positive force-polygon turn makes it
strictly positive, giving the displayed bound on t. Their dot
product is
\[
                       taX+tbY>0,
\]
so the turn is acute. The determinant bound also guarantees
\(X,Y>0\); it is not a relaxed replacement for the original
force equations.

In the second row the determinant is \(X>0\), while the dot
product is \(Y(1-Y)-X^2\). Thus a turn at most \(\pi/2\) is
equivalent to
\[
 X^2-Y(1-Y)=1-t(2a+b)+t^2R^2\le0.
\tag{6}
\]
The third row is symmetric, with determinant Y and dot product
\(X(1-X)-Y^2\), giving its displayed quadratic. Equality in
these two quadratics retains the original right-turn endpoints.

### 3.2 Why the owner rows retain every genuine mean

An incoming bottom-axis application's own transverse coordinate
is fixed by its original normal line to be \(\tau a\). Relative
to \(P_{00}\) this is exactly X; its point is therefore
\((X,0)\), including the original mean endpoints initially.
Similarly an outgoing left-axis application is exactly \((0,Y)\).

With only the incoming axis, the complete moment cover permits
an outgoing upper-left adjacent vertex or an opposite vertex
when \(b>a\). The latter would have directed vector \((-X,-Y)\).
A turn at most \(\pi/2\) would force \(Y=0\), making its actual
normal a side axis, contrary to the one-owner premise. If its
vector vanished, q would be \(P_{00}\), and the original strict
opposite-vertex normal paired with the bottom axis would have
turn strictly greater than \(\pi/2\). Thus only the fourth row
remains. Its strict upper-left vertex normal forces \(X>0\)
and \(1-Y=tb>0\); hence \(0<X<1\), and the shared mean is
strictly inside its original bottom side. The case \(Y=0\)
remains allowed.

The outgoing-axis case is the reflected statement and gives
the fifth row. With both actual axes, the turn is exactly
\(\pi/2\) and the complete original means are precisely those
of the last row. In particular \(X=Y=0\), when compatible
with the remaining physical constraints, is retained as a
coincident-application boundary case. No strict-turn overlap
argument is incorrectly applied to that right-turn row.

These arguments exhaust every axis/non-axis combination in
the original full local support cover.

## 4. Placement relative to the radial unit and a stronger near-corner angle

The original S-incident channel at L can be either its incoming
or outgoing channel. This is retained as part of the physical
label, rather than identifying two means by a new symmetry.

In the first row both choices use an actual adjacent-to-circle
vertex. In the second and third rows, one choice uses the
opposite vertex and the other the adjacent vertex. In either
single-owner row, one choice uses its actual strict interior
shared mean and the other its adjacent vertex. In the
two-owner row the original S channel uses one of its two
actual full means, possibly at an endpoint.

For completeness, a useful uniform strengthening of the accepted
near-corner lemma holds on \(R\ge2\). In the actual radial frame
at the upper S port,
\[
 P=(d,1/2),\qquad g=(-\cos\alpha,\sin\alpha),\qquad
 Q=P+g,\quad0<\alpha<\pi/2.
\]
If the next unit's actual circle corner z satisfies
\(|z-Q|\le1\), then
\[
                              \alpha>\frac12.
\tag{7}
\]
Indeed \(|Q|\ge R-1\), whereas the exact difference is
\[
 |Q|^2-(R-1)^2
       =2R-1+\sin\alpha-2d(R)(1+\cos\alpha).
\]
It decreases strictly with R. At \(R=2\),
\(d>187/200\), with squared reserve \(231/40000\).
If \(0\le\alpha\le1/2\), the complete elementary estimates
\(\sin\alpha\le\alpha,\ \cos\alpha\ge1-\alpha^2/2\) give
\[
 \begin{split}
 |Q|^2-(R-1)^2
 &<3+\alpha-\frac{187}{100}\left(2-\frac{\alpha^2}{2}\right)\\
 &\le\frac72-\frac{187}{100}\frac{15}{8}
   =-\frac1{160}<0,
 \end{split}
\]
a contradiction. The quadratic increases on the indicated
nonnegative interval. This proves (7) for any actual
near-corner channel, without a turn or owner assumption at its
other endpoint.

At S itself, its two actual side channels have angles
\(\alpha,\beta>0\) in the strict radial inner-vertex charts, with
\[
                 \theta_S=\pi-\alpha-\beta.
\]
Equation (2) therefore gives the exact whole low-turn condition
\[
                           \alpha+\beta\le\pi/4.
\tag{8}
\]
If the S-incident application at L is an adjacent vertex,
(7) forces the angle at the other radial port to satisfy
\[
             0<\beta<\pi/4-1/2<2/7.
\tag{9}
\]
The last strict inequality uses \(\pi<22/7\).
The strict partner T cannot then be type A, since its own
actual adjacent port would also give a radial angle greater
than \(1/2\). In that situation its entire remaining strict
feature cover is M/O/T.

If L's actual S-incident application is an interior mean or an
opposite vertex, premise (7) is not supplied merely by its label.
Such a mean is not replaced by an adjacent vertex. The full
strict partner cover A/M/O/T remains until an additional
physical inequality is proved. If an original endpoint mean
itself satisfies the distance premise, (7)--(9) apply to that
actual endpoint without relabeling its contact.

## 5. Exact remaining scope

The table is a necessary exhaustive original feature/mean cover
at the unique nonobtuse load. It makes no assertion that every
listed scalar tuple is a realizable packing or equilibrium.
Every original positive force equation, full channel equation,
physical containment and pairwise nonoverlap constraint remains.

The accepted zero-radial-weight and radial right-turn exclusions
remain separate. The complete strict-turn A/M/O/T pair family
has its separate proofs, including the A/O high-radius join.
This source supplies the complementary domain where one unique
turn is at most \(\pi/2\); it does not silently infer a same-side
port chord for the first, fourth, fifth or sixth rows.

No original gate is closed here. The new unconditional progress
is the whole-channel outer-axis exclusion, the exact full
low-turn table with mean endpoints retained, and the uniform
high-radius near-corner estimate (7). No computational
certificate, angle grid, numerical pose, Lean compilation or
CI is used.

