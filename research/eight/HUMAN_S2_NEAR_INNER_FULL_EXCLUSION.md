# The entire S2 nearer-inner two-cap branch is impossible

Research continuation, 2026-10-12. This **eliminates an entire
continuous inner/outer-center subbranch** previously narrowed
to \(k=4\) and \(h_R<1/20\):
in exclusive S2=(3+0,2+2), the two squares on the *nearer*
2+2 cap **cannot both have center norm less than one**.

All square orientations are independent. The argument uses only
the published arbitrary-frame cap/angle lemmas, actual
center separation, and a short **hand convexity reduction** with
exact rational endpoint margins. It is not a generated
interval-box classifier or a proof of unrestricted n=8 optimality.

## Theorem

Let eight pairwise interior-disjoint unit squares fit in
a disk centered at zero with squared radius
\[
R^2\le9789/2500.
\]
Let C be the unique open origin-containing square.
Suppose every exterior square has exactly one central-owned
whole-side separator, with exclusive S2 populations
\[
R:3,\quad L:0,\quad U:2,\quad D:2
\]
after reflections/axis exchange, and U is the *nearer*
of the two opposite 2+2 caps:
\[
7/24<h_U=1/2+b\le1/2,\quad h_D=1-h_U\ge1/2.
\]

**Conclusion:** the U cap **must contain a square whose
center norm is at least one**. Equivalently,
\[
\boxed{\text{exclusive S2}\Longrightarrow
\#\{\text{outer U centers}\}\ge1.}              \tag{1}
\]
Thus **every** S2/k=4 case with both U centers inner is
impossible (regardless of h_R), not just the previous
interval \(h_R\ge1/20\). The result is stronger still:
it excludes the both-U-inner subbranch for every k.

The statement is not that S2 itself is impossible:
S2 configurations with one or two outer U centers
still require a sharp global argument.

## 1. Exact pre-existing geometric consequences if both U centers were inner

Assume contrary to (1) that both U centers have
radial norm strictly less than one.

By
[HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md](HUMAN_S2_NEAR_INNER_OUTER_POLARITY.md)
and
[HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md](HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md),
the far D cap has two outer centers and the R triple
has **exactly two outer centers and one inner**:
one outer R would create the forbidden six-square
two-R-inner/two-U-inner/two-D-outer pattern, while
three outer R rays cannot fit between the two
D outer rays and the U+ inner ray.
All seven labels are distinct because statuses are
exclusive one-side. In particular **k=4**.

Let the two outer R center-ray angles be
\(\psi_1<\psi_2\), and the unique inner R center
angle be \(\theta\). The previously established
arbitrary-frame outer-ray polarity bounds are
\[
-\pi/6-1/250<\psi_1<-\pi/18+1/500<0,
\]
\[
0<67/500<\psi_2<7\pi/36.                        \tag{2}
\]
For the two outer D centers, order their southern
angles as \(\phi_1<\phi_2\). The strengthened
far-cap elevation and outer-outer angular
separation imply
\[
-5\pi/12-1/500<\phi_2<-\pi/3.                  \tag{3}
\]
For the two inner U centers, the sharp transverse
placement result
[HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md](HUMAN_S2_K4_TRANSVERSE_CENTER_ANCHORS.md)
gives a positive-x U center \(u=(u_x,u_y)\) with
\[
u_x>9/25,\quad u_y>19/24,\quad |u|<1.
\]
It follows, with rational square comparisons, that
\[
\boxed{9/25<u_x<31/50,\qquad
79/100<u_y<47/50.}                              \tag{4}
\]
The same two-inner U angular analysis places
its center ray angle \(\eta\) in
\[
\pi/4<\eta<5\pi/12.                              \tag{5}
\]

The unique inner R square lies in the whole
positive right cap, with center x-coordinate
\(>1/2\) and norm \(<1\). Hence
\[
-\pi/3<\theta<\pi/3.                             \tag{6}
\]

## 2. Exact mixed inner/outer angular gap at least 12/25

**Elementary center-angle lemma.**
If two distinct interior-disjoint unit-square
centers have norms \(1/2<r<1\) and
\(1\le s<283/200\) within the stated disk, then
their smaller angular separation is
\[
\boxed{\delta>12/25\ {\rm radians}.}             \tag{7}
\]

The universal upper center norm \(283/200\)
follows from
\(s^2+s+1/2\le9789/2500\), with strict
margin \(65/40000>0\) at that rational ceiling.
Put \(z=12/25\). The alternating cosine Taylor
lower bound gives
\[
\cos z\ge1-z^2/2+z^4/24-z^6/720>177/200.
\]
If \(\delta\le z\), the center squared distance is
\[
r^2+s^2-2rs\cos\delta
<r^2+s^2-(177/100)rs.
\]
The last expression is separately convex in
\(r\) and s. Its four rational corner values
on \([1/2,1]\times[1,283/200]\) are
\[
73/200,\quad19999/20000,\quad
23/100,\quad19907/40000,
\]
all strictly less than one. Distinct packed
unit squares have center distance at least one,
contradiction. This proves (7).

We also need the stronger analogue for
\(5/8<r<1\). The same cosine-law argument
with angle \(33/50\) radians and
\(\cos(33/50)>789/1000\) gives a mixed
angular gap
\[
\boxed{\delta>33/50.}                            \tag{8}
\]
Indeed the four corresponding rational
corner bounds on
\([5/8,1]\times[1,283/200]\) are
\[
647/1600,\quad159569/160000,\quad
211/500,\quad153871/200000,
\]
again all below one. Each cosine comparison
uses the standard alternating Taylor inequality;
the explicit strict rational margins are in
[verify_s2_near_inner_full_exclusion.py](verify_s2_near_inner_full_exclusion.py).

## 3. The inner R ray must lie between the two outer R rays

We exclude the other possible angular positions
of \(\theta\).

**Suppose first \(\theta<\psi_1\).**
Since the inner R center radius is \(>1/2\),
(7) and (2) yield
\[
\theta<\psi_1-12/25
<-\pi/18-239/500<-13/20.
\]
The final strict comparison follows from
\(\pi>157/50\) and
\(157/900+239/500-13/20=11/4500>0\).

Since its x center coordinate exceeds \(1/2\),
the inner R radius is \(>5/8\):
\[
r\cos|\theta|>1/2,\qquad
\cos|\theta|<\cos(13/20)<4/5,
\]
where the last inequality follows from
\(1-z^2/2+z^4/24<4/5\) at \(z=13/20\).

The D ray \(\phi_2\) lies **below** \(-\pi/3\),
whereas \(\theta>-\pi/3\). Equations
(2)–(3) give
\[
0<\theta-\phi_2
<13\pi/36-119/250
<33/50,
\]
because with \(\pi<22/7\) the upper bound
is \(5189/7875=33/50-17/15750\).
This contradicts the stronger mixed
center-angle lemma (8), applied to the
inner R and outer D square. Thus
\[
\theta\not<\psi_1.                               \tag{9}
\]

**Suppose instead \(\theta>\psi_2\).**
By (7) and the exact lower bound on \(\psi_2\),
\[
\theta>\psi_2+12/25>67/500+12/25
=307/500>\pi/12.
\]
The U+ inner ray \(\eta\) belongs to
\((\pi/4,5\pi/12)\) by (5).
Since \(\theta\in(\pi/12,\pi/3)\),
its **ordinary angular gap from \(\eta\)**
is strictly less than \(\pi/3\):
if \(\theta\le\eta\), use
\(5\pi/12-\pi/12=\pi/3\);
if \(\theta>\eta\), use
\(\pi/3-\pi/4=\pi/12\).
But the two **distinct inner square** centers
have radius \(<1\) and mutual distance \(\ge1\),
which forces an angular gap **strictly greater**
than \(\pi/3\), by the inscribed-disk cosine-law
theorem. Contradiction, so
\[
\theta\not>\psi_2.                               \tag{10}
\]

Equality with either outer ray is ruled out
by the positive mixed gap (7). Therefore
\[
\boxed{\psi_1<\theta<\psi_2.}                     \tag{11}
\]
Using (7) on both successive inner/outer
pairs and (2),
\[
\psi_2>\psi_1+24/25
>-\pi/6-1/250+24/25
=-\pi/6+239/250.
\]
By \(\pi<22/7\),
\[
-\pi/6+239/250>239/250-11/21
=2269/5250>43/100.                              \tag{12}
\]
The old upper bound in (2) gives
\(7\pi/36<31/50\), again by
\(\pi<22/7\). Hence the positive outer R ray
satisfies the strict *narrow polar interval*
\[
\boxed{43/100<\psi_2<31/50.}                     \tag{13}
\]

## 4. The positive outer R and positive-x inner U centers must overlap

Let q be the positive-y **outer** R-square center,
with polar angle \(\psi_2\) in (13) and radial
norm \(1\le s<283/200\).
Let u be the **distinct** positive-x **inner**
U-square center, with coordinates in (4).

We prove analytically from these bounds alone
that
\[
\boxed{|q-u|^2<4923651/5000000<1.}              \tag{14}
\]
This is a small convexity endpoint proof, not a
numerical test of infinitely many orientations.

Write q in polar form
\[
q=(s\cos\psi_2,s\sin\psi_2).
\]
On \((43/100,31/50)\), the x coordinate q_x is
**strictly greater than \(31/50\)**:
since \(s\ge1\) and
\[
\cos(31/50)\ge1-(31/50)^2/2
=4039/5000>31/50.
\]
Thus \(q_x>u_x\). For any fixed q, the
squared distance
\[
(q_x-u_x)^2+(q_y-u_y)^2
\]
strictly decreases with increasing \(u_x\)
in the permitted interval
\(9/25<u_x<31/50\). It is separately
convex in \(u_y\in(79/100,47/50)\),
so its maximum over the containing rectangle
is **no greater** than the larger of its values
at \(u_x=9/25\) and
\[
u_y=y\in\{79/100,\;47/50\}.                       \tag{15}
\]
The corners need not be geometrically realizable:
using a larger rectangle is a valid upper bound.

For such a fixed rational corner y, write
\[
f_y(\psi)=(9/25)\cos\psi+y\sin\psi.
\]
Since both components are positive,
\(f_y''=-f_y<0\) on the entire interval
\([43/100,31/50]\). A concave function
attains its minimum at an endpoint.
The elementary Taylor bounds give
\[
\begin{array}{c|cc}
z & \cos z \text{ is greater than} &
    \sin z \text{ is greater than}\\
43/100 &907/1000&416/1000\\
31/50&807/1000&58/100
\end{array}
\]
(the bounds follow from
\(\cos z\ge1-z^2/2\) and
\(\sin z\ge z-z^3/6\); strict margins hold).
For both \(y=79/100\) and \(47/50\),
\[
(9/25)(807/1000)+y(58/100)>
(9/25)(907/1000)+y(416/1000)
\]
because the difference is
\(-9/250+ (164/1000)y>0\).
Hence concavity yields the uniform strict
**rational lower bound**
\[
f_y(\psi)>
f_{0,y}:=(9/25)(907/1000)+y(416/1000).        \tag{16}
\]

The squared center distance at the relaxed
corner is
\[
s^2+(9/25)^2+y^2-2s f_y(\psi)
<
s^2+(9/25)^2+y^2-2s f_{0,y}.                   \tag{17}
\]
The right side is a **convex quadratic in
s∈[1,283/200]**, so its maximum is at an
endpoint. Its only four endpoint values are
\[
\begin{array}{c|cc}
y&s=1&s=283/200\\
79/100&22169/50000&4509111/5000000\\
47/50&3613/6250&4923651/5000000
\end{array}
\]
and **each is strictly below one**.
The greatest is \(4923651/5000000
=1-76349/5000000\).
This proves (14) over the *full continuous*
range of centers and square frames. QED.

But q and u are **distinct** packed square labels:
one is R-only and the other is U-only.
Their open inscribed radius-1/2 disks must be
disjoint, requiring \(|q-u|\ge1\).
Inequality (14) contradicts this requirement.

The original assumption that both nearer
U-cap centers were inner is false. The theorem
is proved. QED.

## Current S2 center-count queue and scope

This supersedes the previously recorded
"near-U both inner ⇒ k=4 and h_R<1/20"
necessary conditions: that whole antecedent
is **now impossible**.

Every still-unexcluded exclusive S2 packing
must have **at least one outer** center on
the nearer U side. Since the farther D
side has two outer centers and the
perpendicular R triple has at least one
outer, **k≥4** is retained automatically.

* For **S2/k=4**, exactly one nearer U member
  and exactly one R-triple member can be outer.
* For **S2/k=5,6**, the near U pair and R triple
  must be allocated outer labels consistent
  with their totals, side offsets and actual
  square geometry.

These are **necessary status/center-count
conditions**, not new existence assertions.
No full S2 class is rejected, no S4 equality
configuration is removed, and the sharp global
bound \(R_8\ge\widehat R\) remains **OPEN**.

[verify_s2_near_inner_full_exclusion.py](verify_s2_near_inner_full_exclusion.py)
checks the exact displayed rational endpoints.
The continuous proof is the hand convexity
argument above; the script is not an
interval-box search, a Lean theorem, or a
substitute for the written proof.
