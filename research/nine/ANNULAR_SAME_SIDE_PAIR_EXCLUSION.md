# An annular pair on the same side cannot have separated horizontal centers

Put
\[
D=\{x^2+y^2\le17/4\},\quad
E=[1,2]\times[-1/2,1/2],\quad W=-E.
\]

**Theorem.** There are no physically interior-disjoint unit squares A,B,
both contained in \(D\cap\{y\ge0\}\) and avoiding E,W, whose centers
satisfy
\[
0\le x_A<x_B<1,\qquad x_B-x_A>1/2,\qquad
|c_A|\ge1/\sqrt2,\quad |c_B|\ge1/\sqrt2.              \tag{1}
\]
In fact the displayed annulus condition for B is automatic from the
other hypotheses. Both square orientations are arbitrary, and all
physical boundary contacts are allowed.

The strict horizontal-gap condition matters. At gap 1/2, the north
square and the aligned square \([0,1]^2\) form an allowed annular pair.

## 1. Two complete local inputs

We use these proved statements, each with a full all-orientation proof.

**Open-disk intersection.** Every upper-half-disk square B avoiding E,W
with \(1/2<x_B<1\) meets
\[
K=\{p:|p-(0,3/2)|<1/2\}.                             \tag{2}
\]
For \(y_B<1\), this is LOW_OUTER_SQUARE_MEETS_N_DISK.md, a finite
convex-center-polygon proof that does not require disk containment.
For \(y_B\ge1\), HIGH_OUTER_SQUARE_MEETS_N_DISK.md proves the stronger
statement that \((3/7,5/4)\) lies in B's open interior; that point lies
in K since \(193/784<1/4\).

**Positive terminal-cap exclusion.** If \(T\subset D\cap\{y\ge0\}\)
avoids E and \(1/2<c_x<1\), then for every unit direction
\(n=(b,a)\) with \(0\le a\le b\),
\[
\min_{p\in T}n\cdot p<\frac12+\frac a{\sqrt2}.        \tag{3}
\]
This is the cap consequence in WEDGE_135_CAPACITY_ONE.md, Section 4.
Its proof uses only the stated single-terminal hypotheses: it routes all
physical separating axes against E to
POSITIVE_NORMAL_CAP_FLOOR_EXCLUSION.md or
OWNED_AXIS_TERMINAL_CAP_EXCLUSION.md. No second angled terminal, wedge
containment, shared orientation, or pair-order assumption occurs in (3).

For any square T in D and any unit vector n, write H_T(n) for its support
halfwidth. The standard corner and support facts give
\[
|c_T|\le3/2,\qquad H_T(n)\ge1/2.                     \tag{4}
\]

## 2. Downward normals are all excluded by the open disk

By (1), \(x_B>1/2\). For any unit vector \(n=(b,-a)\), with
\(a,b\ge0\), equations (4) and \(x_A\ge0\) imply
\[
\max_A n\cdot p
=b x_A-a y_A+H_A(n)
\ge\frac12-\frac32a
=\sup_{p\in K}n\cdot p.                             \tag{5}
\]
But B contains a point of the open disk K by (2), so
\[
\min_B n\cdot p<\frac12-\frac32a.
\]
Thus no downward-right normal separates A from B in this order. This
argument covers shallow and steep directions, either possible owner,
and zero-coordinate boundaries. It does not require annularity.

## 3. Upward normals are excluded by support and the terminal cap

First let \(n=(b,a)\), \(0\le a\le b\), be a unit direction. Since
A lies wholly above zero, its center has \(y_A\ge0\). Thus the annulus
condition gives the elementary support bound
\[
\begin{aligned}
\max_A n\cdot p
&\ge b x_A+a y_A+1/2\\
&\ge a(x_A+y_A)+1/2
 \ge a|c_A|+1/2
 \ge\frac12+\frac a{\sqrt2}.
\end{aligned}                                       \tag{6}
\]
Equation (3) for B contradicts separation in this direction.

Now suppose \(n=(b,a)\) with \(0<b<a\). Whole upper containment gives
\(y_A\ge H_A(e_y)\). Therefore
\[
\max_A n\cdot p\ge a H_A(e_y)+H_A(n).
\]
The two-direction support minimum from
HALF_DISK_CLOSE_CENTER_RIGIDITY.md, equation (7), gives
\[
aH_A(e_y)+H_A(n)
\ge\min\left\{a+b/2,\ \frac{1+a(a+b)}2\right\}>1.    \tag{7}
\]
The first entry exceeds one because \(0<b<1/\sqrt2<4/5\) implies
\(a^2-(1-b/2)^2=b(1-5b/4)>0\). The second exceeds one because
\(a(a+b)=1+b(a-b)>1\).
On the other hand (4) gives
\(\min_B n\cdot p\le|c_B|-H_B(n)\le1\). Again separation is
impossible. Thus every up-right normal with positive horizontal
component is excluded.

## 4. Leftward and vertical normals are too short

Both center heights lie in \([1/2,3/2]\). In fact
\[
1/2<y_B<3/2.
\]
The upper strictness follows from \(x_B>1/2\) and (4). Equality
\(y_B=1/2\) would force vertical halfwidth 1/2 and hence axis alignment;
such a square with \(x_B>1/2\) overlaps E. Consequently, with
\(d_x=x_B-x_A\), \(d_y=y_B-y_A\),
\[
0<d_x<1,\qquad |d_y|<1.                              \tag{8}
\]
If a unit normal n has \(n_x\le0\), then
\[
n\cdot(c_B-c_A)=n_xd_x+n_yd_y<1,
\]
including \(n_x=0\) by the strict vertical-gap bound. Such a normal
cannot separate the squares, because a separating axis must satisfy
\[
n\cdot(c_B-c_A)\ge H_A(n)+H_B(n)\ge1.
\]

Every unit normal has now been excluded. In particular, no separating
axis owned by either square exists, contradicting their physical
interior-disjointness. This proves the theorem.

**Useful consequence.** In any pair satisfying the geometric hypotheses
in (1) except annularity, the left square has \(|c_A|<1/\sqrt2\).
Indeed \(x_B>1/2\) and \(y_B\ge1/2\) imply
\(|c_B|^2>1/2\), so the theorem leaves only the displayed alternative
for A.
