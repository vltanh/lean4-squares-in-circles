# P.ALL: every four-square path cage has total capacity at most eight

**Status:** complete all-parameter hand proof. The additional squares have
independent arbitrary orientations and arbitrary physical separating axes.
The quantitative proof below does not assume the stronger standalone
HALF.3 rigidity statement, now proved separately in
HALF_POCKET_TRIPLE_RIGIDITY.md. It uses no numerical search, parameter table, or interval
certificate as a premise. Lean compilation and CI have not been run.

Put
\[
D=\{(x,y):x^2+y^2\le17/4\},\quad
E=[1,2]\times[-1/2,1/2],\quad W=-E.
\]
For arbitrary parameters \(t_L,t_R\in[-1/2,1/2]\), include the aligned
middle squares
\[
L=[-1,0]\times[t_L-1/2,t_L+1/2],\qquad
R=[0,1]\times[t_R-1/2,t_R+1/2].                       \tag{1}
\]

**Theorem P.ALL.** At most four other physical unit squares can be placed
in D with pairwise disjoint open interiors, also avoiding E,W,L,R.
Consequently every packing containing the four-square cage (1) has at
most eight squares. This holds simultaneously for the entire closed
parameter square \([-1/2,1/2]^2\), including all boundary cases.

The established local inputs, all with full hand proofs, are:

1. The corner bound \(|c_T|\le3/2\), and \(-1<(c_T)_x<1\) for any
   square avoiding E,W, from DIAGONAL_CENTER_EXCLUSION.md. The radial
   terminal outer-face screen gives \(-2<x<2\) at every point of such
   a square; see RADIAL_SECTOR_POCKET_CAPACITY.md, Lemma P1.1.
2. The upper-half-pocket capacity-three theorem in
   P_HALF_POCKET_SECTION_PROOF.md, and the close-center triple
   classification in HALF_DISK_CLOSE_CENTER_RIGIDITY.md, Corollary 3.
3. ANNULAR_SAME_SIDE_PAIR_EXCLUSION.md, with its strict open-disk
   intersection inputs LOW_OUTER_SQUARE_MEETS_N_DISK.md and
   HIGH_OUTER_SQUARE_MEETS_N_DISK.md.
4. The exact single-square inequality in
   TERMINAL_CAP_SECTION_EXCLUSION.md, with constant \(d_0=19/120\).
5. HIGH_CENTER_COMMON_POINT.md: any square in D with center height
   greater than \(3/\sqrt5\) contains \((0,\sqrt5/2)\) strictly;
   reflection gives the corresponding statement below the origin.

For a square T let \(H_T(v)\) denote its support halfwidth in direction v.
Every unit direction satisfies \(H_T(v)\ge1/2\), and a wholly upper
square satisfies \((c_T)_y\ge H_T(e_y)\ge1/2\).

## 1. All extras route into two half-pockets, each of capacity three

The four fixed squares cover the horizontal segment
\([-2,2]\times\{0\}\), since both slider intervals contain zero.
The open interior of an additional square cannot meet this closed fixed
union: an interior ball about a point of a fixed square would meet that
fixed square's open interior. Every point of an extra has \(-2<x<2\)
by the outer-face screen. Its connected interior therefore lies wholly
above or wholly below y=0, and the whole closed square lies in the
corresponding closed half-plane.

The upper-half-pocket section theorem gives capacity three in each
half-plane. To recall its exact content, every upper extra is either
\[
N=[-1/2,1/2]\times[1,2],
\]
an aligned bottom square with center \((z,1/2)\), \(|z|\le1/2\), or has
an open section at y=1 of length greater than 1/2, with left endpoint
below 1/2 and right endpoint above -1/2. The three points
\((-1/2,1),(0,1),(1/2,1)\) pierce every nonexceptional square strictly.
The exceptional cases are handled in that theorem and cannot increase
the capacity above three.

If five extras existed, reflection in y=0 would let us assume there are
three upper extras and at least two lower extras. We show that every
possible upper triple leaves room for at most one lower square.

## 2. The canonical upper triple already leaves only one lower square

If any two upper centers differ horizontally by at most 1/2, the
close-center theorem classifies the entire triple as
\[
U_L=[-1,0]\times[0,1],\quad
U_R=[0,1]\times[0,1],\quad N.                        \tag{2}
\]
Avoidance of U_L and U_R by the middle squares in (1) forces
\(t_L=t_R=-1/2\). Indeed their upper faces must be at or below zero,
and the allowed slider range leaves only those values.

Every lower extra has center horizontal coordinate in \((-1,1)\).
Its open inscribed disk must avoid the middle column containing that
coordinate, whose vertical interval is now \([-1,0]\). Thus its center
height is at most \(-3/2\). The universal center-radius bound forces
that center to equal \((0,-3/2)\). Two distinct extras cannot have the
same center, since their open inscribed disks would overlap. Hence there
is at most one lower extra in this case.

## 3. Every other upper triple contains a small inner square

Order the center horizontal coordinates of a noncanonical upper triple
as \(x_1<x_2<x_3\). The close-center theorem gives
\[
x_2-x_1>1/2,\qquad x_3-x_2>1/2,
\qquad -1<x_1<x_2<x_3<1.                            \tag{3}
\]
There is a pair on the same weak side of the vertical axis. If
\(x_2\ge0\), take the middle and right squares. If \(x_2<0\), reflect
horizontally and take the reflected middle and left squares. Denote the
resulting inner and outer members by A and B. Thus
\[
0\le x_A<x_B<1,\qquad x_B-x_A>1/2.                  \tag{4}
\]
This includes the boundary case \(x_A=0\).

The outer square has \(x_B>1/2\) and \(y_B\ge1/2\), so
\(|c_B|^2>1/2\). The annular same-side pair exclusion therefore forces
\[
|c_A|^2<1/2.                                        \tag{5}
\]
We next prove a quantitative consequence of (4)--(5) that constrains
both P slider heights at once.

## 4. The lower vertical-axis section controls every shallow support

Write \(c_A=(x,y)\). Since A is wholly upper, \(y\ge1/2\), and
\[
|c_A-(0,1/2)|^2=|c_A|^2-y+1/4<3/4-y\le1/4.
\]
Thus \((0,1/2)\) lies in A's open inscribed disk and hence in its open
interior. Let \(\delta\) be the lower endpoint of its vertical-axis
section. Then
\[
0\le\delta<1/2.                                    \tag{6}
\]

**Support claim.** For every unit direction \(n=(a,b)\) with
\(0\le b\le a\),
\[
\max_{p\in A}n\cdot p\ge
\frac12+b\delta+\frac b{2a}.                         \tag{7}
\]

Choose an inward normal \(m=(s,t)\) of a square side at the lower section
endpoint. It may be chosen with \(t>0\); this also handles a vertex
endpoint by selecting a side with positive vertical inward component.
Then
\[
s^2+t^2=1,\qquad sx+ty=1/2+t\delta,\qquad
y\ge(|s|+t)/2.                                     \tag{8}
\]

The case \(s\ge t\ge0\) is impossible. In that case
\(x=(1/2+t\delta-ty)/s\), and its resulting squared center radius,
as a function of \(y\ge(s+t)/2\), is strictly increasing: its derivative
has the sign of
\[
y-t(1/2+t\delta)\ge s/2-t^2\delta>0.
\]
At the smallest allowed height, (8) gives
\(x=(s-t)/2+t\delta/s\ge(s-t)/2\), so the squared radius is at least
\((s+t)^2/4+(s-t)^2/4=1/2\), contradicting (5).

Therefore either \(s<0\) or \(0\le s<t\). In both cases
\(a-bs/t\ge0\). Solving (8) for y and using \(x\ge0\) yields
\[
n\cdot c_A\ge b\delta+\frac b{2t}.
\]
Set \(Z=|n\cdot m|+|n\cdot Jm|\ge1\). The coordinates of e_y in
the \((n,Jn)\) frame are \((b,a)\), so \(t\le aZ\). Also
\(H_A(n)=Z/2\). Consequently
\[
\begin{aligned}
\max_A n\cdot p
&\ge b\delta+\frac12\left(Z+\frac bt\right)\\
&\ge b\delta+\frac12\left(Z+\frac{b/a}{Z}\right)
 \ge b\delta+\frac12\left(1+\frac ba\right).
\end{aligned}
\]
The last step is the exact identity
\[
Z+\frac{b/a}{Z}-1-\frac ba
=\frac{(Z-1)(Z-b/a)}Z\ge0.
\]
This proves (7) for all square orientations.

## 5. The terminal-cap theorem forces delta below 19/120

Physical separation supplies a unit axis n oriented from A toward B.
We first specify all its possible directions without imposing ownership.

The outer square has \(1/2<y_B<3/2\): the upper strictness follows
from \(x_B>1/2\) and the center bound, while equality at the lower end
would force axis alignment and overlap with E. Hence the absolute
vertical center gap is strictly below one. All normals with nonpositive
horizontal component have center projection gap less than one and
cannot separate.

For a downward-right direction \(n=(a,-b)\), \(a,b\ge0\), the open
disk intersection theorem puts a point of B in
\(K=B((0,3/2),1/2)\). But
\[
\max_A n\cdot p\ge1/2-3b/2=\sup_K n\cdot p
>\min_B n\cdot p,
\]
so these normals are also impossible, including the horizontal boundary.

For an upward-right direction \(n=(a,b)\) with \(b>a>0\), whole upper
containment and the two-direction support minimum give
\[
\max_A n\cdot p\ge
\min\left\{b+a/2,\ \frac{1+b(a+b)}2\right\}>1,
\]
whereas \(\min_B n\cdot p\le1\). At \(a=b=1/\sqrt2\), the same
lower bound is at least one. Equality in the bound for B would require
\(c_B=(3/2)n\), whose horizontal coordinate is \(3/(2\sqrt2)>1\),
again impossible. This covers the 45-degree boundary exactly.

Thus every actual separating axis has the form
\[
n=(a,b),\qquad 0<b<a,\qquad a^2+b^2=1.
\]
Combining separation with (7) gives
\[
\min_B n\cdot p\ge\max_A n\cdot p
\ge\frac12+b\left(\delta+\frac1{2a}\right).           \tag{9}
\]
The theorem TERMINAL_CAP_SECTION_EXCLUSION.md excludes (9) whenever
\(\delta\ge d_0=19/120\), because B is an upper square avoiding E with
\(1/2<x_B<1\). Therefore
\[
\delta<\frac{19}{120}.                              \tag{10}
\]

## 6. Both slider heights fall together, leaving one lower square

For either middle square in (1), its bottom is at or below zero. A's
open vertical-axis section contains every point immediately above
\(\delta\). If either middle square's upper face exceeded \(\delta\),
there would be an interior point of A on x=0 within that middle square's
vertical interior, and an open ball about that point would overlap its
interior on the appropriate side. Hence avoidance forces both bounds
\[
t_L+1/2\le\delta,\qquad t_R+1/2\le\delta.             \tag{11}
\]
These inequalities are simultaneous and do not assume equal sliders.

Now take any lower extra C. Its center has \(-1<x_C<1\). Choose the
middle column containing its horizontal coordinate, with either column
allowed at x=0. Its radius-1/2 open inscribed disk must avoid that aligned
column. Therefore its center height satisfies one of
\[
y_C\le t_i-1\quad\text{or}\quad y_C\ge t_i+1.
\]
The latter is impossible for a lower square, since \(t_i+1\ge1/2\).
Equations (10)--(11) thus give
\[
y_C\le t_i-1\le\delta-3/2
<-\frac{161}{120}<-\frac3{\sqrt5}.                   \tag{12}
\]
The last exact comparison is
\(5\cdot161^2>9\cdot120^2\), equivalently \(25921>25920\).
By HIGH_CENTER_COMMON_POINT.md, every such C contains
\((0,-\sqrt5/2)\) in its open interior. There can be at most one lower
extra.

Every upper triple, canonical or otherwise, therefore leaves lower
capacity at most one. This contradicts the three-plus-two split forced
by five extras. Reflection covers the opposite split. The asserted
total capacity of eight follows for every pair of slider parameters.
\(\square\)

## Scope of the result

This closes the complete geometric P.ALL family, not only selected
slider values or selected contact separators. Together with the existing
six-body capacity theorem and FIVE_BODY_TWO_LOAD_REDUCTION.md, it also
closes physical completion of every selected positive component with
exactly two circle-loaded bodies in the declared radius window, including
cyclic components.
This quantitative proof excludes a putative noncanonical upper triple
through its effect on both sliders and the opposite half-pocket. The
separate HALF_POCKET_TRIPLE_RIGIDITY.md now proves that every upper E/W
triple is canonical. It gives a shorter independent assembly: each
half-pocket has capacity three; a five-extra packing has a three-plus-two
split; the triple is canonical and Section 2 leaves capacity at most one
on the opposite side. The full argument above preserves the independent
quantitative route and its stronger two-square slider implication.
