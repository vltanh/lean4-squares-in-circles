# Entire seven-outer m=3 centrally stressed cycle is impossible: positive circle forces fit in a semicircle

**2026-10-13. Complete all-frame global physical-stress macro-case exclusion.**
This eliminates **EVERY** seven-outer, no-full-actual-ring,
central-positive-degree-two configuration whose unique
positive stress component is
\[
C-S_1-S_2-S_3-C.
\]
It does **not** assume C has only two *actual*
neighbors, does not assume a parallel frame,
and does not rely on any local cap-offset optimization.

The proof is a single sharp **semicircle force-balance contradiction**
coupled with the already-proved strict outer-center angular separation.

## Theorem

Let eight pairwise interior-disjoint genuine unit squares
attain the global least containing-disk radius R, where
\[
\sqrt2+1/2<R\le\sqrt{9789/2500}<2.
\]
Let C be the unique unit square containing the disk
origin in its open interior, and assume exactly **seven
exterior square centers are outer**, i.e. norm at least one.

Suppose the induced *actual outer square contact graph*
is a **proper** subgraph of the seven-ray center-cycle,
and that a normalized physical stress has **exactly two
positive C-neighbor pairs**. By the established
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
its unique nontrivial positive-stress component
is a C-rooted cycle of m consecutive outer labels.

**Then m cannot equal three:**
\[
\boxed{\text{k=7, B2, outer actual forest}
\Longrightarrow m\ne3.}                     \tag{1}
\]
This holds for **any number of additional zero-positive-stress
actual C contacts**, zero-weight outer contact edges,
arbitrary independent frames and full square positions.

Combined with the previously proved complete **m=7**
exclusion, the only not-yet-excluded stress-cycle lengths
in this structural root are
\[
\boxed{m\in\{4,5,6\}.}                          \tag{2}
\]
There are **seven cyclic labeled positive-stress supports per
length**, or **21 remaining graph supports** before geometric
feasibility checks.

The genuine sharp equality construction with a **full
seven-outer actual contact ring** lies in a *different*
structural root and is deliberately preserved.

## 1. Every circle vertex is within a uniform narrow angle of its square center

Let \(x\) be any **actual true square vertex on the
containing circle**, so \(|x|=R\), belonging to a
unit square with center p. The distance
from p to any of its true vertices is exactly
\[
a:=\sqrt2/2.
\]
Let \(\eta_x\in[0,\pi]\) be the ordinary smaller
angle between the rays through p and x.

Because \(|x-p|=a<R\),
\[
x\cdot p=(R^2+|p|^2-a^2)/2>0,
\]
so \(\eta_x<\pi/2\).
The perpendicular distance from x to the
ray \(\{tp:t\ge0\}\) is \(R\sin\eta_x\)
and is at most \(|x-p|=a\).
Therefore
\[
\sin\eta_x\le a/R,\qquad
\eta_x\le\arcsin(a/R).                         \tag{3}
\]

The established radius lower bound
\(R>\sqrt2+1/2\) and the exact rational
square comparisons
\[
\sqrt2>141/100,\qquad
\sqrt2<99/70
\]
give
\[
R>191/100,\qquad
a<99/140,
\quad
\frac aR<\frac{495}{1337}.                   \tag{4}
\]

We now prove the strict convenient
**uniform circle-ray shadow bound**
\[
\boxed{\eta_x<31/80\ \text{radians}.}         \tag{5}
\]
Indeed \(31/80\in(0,\pi/2)\) and
the elementary alternating sine lower bound gives
\[
\sin(31/80)>
31/80-(31/80)^3/6
=\frac{1160609}{3072000}.
\]
The exact rational difference is
\[
\frac{1160609}{3072000}-\frac{495}{1337}
=\frac{31094233}{4107264000}>0.
\]
Combine with (3)--(4) and monotonicity
of sine on \([0,\pi/2]\) to obtain (5).

Thus **every true containing-circle vertex**
of any unit square lies in an angular
arc of half-width \(<31/80\) about
its actual center ray. This does
not imply the *entire square* lies in
that arc; only the true circle-vertex
directions are needed for physical stress.

## 2. Three consecutive outer-center directions leave a strict semicircle for their circle vertices

Assume toward contradiction m=3.
Name the three positive-stress outer squares
\(S_1,S_2,S_3\) in their **consecutive
outer-center ray order** among all
seven exterior outer labels. Let their
ordinary positive angular separations
along this three-label arc be
\(\delta_1,\delta_2>0\).

The remaining **five** successive
center-ray angular gaps on the complementary
arc from S3 back to S1 include all
four exterior spectator center rays.
The exact arbitrary-frame theorem
[HUMAN_STABLE_OUTER_ANGLE.md](HUMAN_STABLE_OUTER_ANGLE.md)
proves that **every** pair of
distinct outer centers in the
search disk has smaller polar angular
gap
\[
>\delta_0:=\pi/4-1/500.
\]
In particular every *circularly successive*
ordinary gap is strictly greater
than \(\delta_0\) (if an ordinary gap
exceeded \(\pi\), this weaker inequality
would still hold).

Therefore the complementary five-gap
arc consumes strictly more than
\[
5\delta_0=5\pi/4-1/100,
\]
leaving the arc containing exactly
S1,S2,S3 with strict total length
\[
\boxed{\delta_1+\delta_2
       <2\pi-5\delta_0
       =3\pi/4+1/100.}                         \tag{6}
\]

By (5), every actual **circle vertex**
on S1, S2 or S3 has a ray direction
within strictly less than \(31/80\)
of its own square's center ray.
Hence **all** possible true
containing-circle vertex directions
of these three squares lie in one
single angular arc of total width
strictly less than
\[
\begin{aligned}
(\delta_1+\delta_2)+2(31/80)
&<3\pi/4+1/100+31/40\\
&=3\pi/4+157/200\\
&<\pi.                                            \tag{7}
\end{aligned}
\]
The last strict inequality is simply
\(\pi>157/50\), so
\(\pi/4>157/200\).

This is a **genuine strict angular
semicircle enclosure**, not a sampled
angular grid. Even if an individual
square has two or more active
circle vertices, all such vertices
lie in that same **open semicircle**.

## 3. The positive physical circle forces cannot balance

The global physical stress equations
in [HUMAN_CONTACT_EQUILIBRIUM.md](HUMAN_CONTACT_EQUILIBRIUM.md),
section 4, are
\[
F_i=2\sum_\alpha \mu_{i,\alpha}x_{i,\alpha},
\qquad \mu_{i,\alpha}\ge0,\qquad
\sum_{i,\alpha}\mu_{i,\alpha}=1,
\]
where each \(x_{i,\alpha}\) with
\(\mu_{i,\alpha}>0\) is a true vertex
on the disk circle. Pairwise physical
contact forces cancel in the total sum,
so
\[
\boxed{\sum_{i,\alpha}
       \mu_{i,\alpha}x_{i,\alpha}=0.}           \tag{8}
\]

The circle-free central C has **zero**
circle multipliers.
Every square outside the unique
nontrivial positive-stress component
has **no positive contact forces**.
The exact stationarity result
\(F_i=0\iff\sum_\alpha\mu_{i,\alpha}=0\)
proved in HUMAN_CONTACT_COMPONENTS.md
then gives **zero circle multipliers
on all four exterior spectator
labels**, even if some of their true
vertices happen to lie on the disk
circle or they have extra
zero-weight actual contacts.

Thus **every term with positive
circle multiplier** in (8)
belongs to one of
\(S_1,S_2,S_3\).

But section 2 proved all their
potential positive circle vertices
lie in an angular arc of width
strictly less than \(\pi\).
There therefore exists a unit
vector w pointing toward the
midpoint of this arc such that
\[
w\cdot x_{i,\alpha}>0
\quad\text{for every }\mu_{i,\alpha}>0.
\]
Since the normalized multipliers
are nonnegative and sum to one,
\[
w\cdot\sum_{i,\alpha}
\mu_{i,\alpha}x_{i,\alpha}>0,
\]
contradicting (8).

No such m=3 positive-stress
cycle can exist. This proves
the entire macro-case exclusion
(1), and together with the
previous m=7 exclusion proves
the current list (2). QED.

## Scope and structural consequences

**Crucially, C's actual degree is NOT assumed two.**
The contradiction uses only the
normalized positive-stress support
and the angular ordering of the
**seven actual outer-center rays**.
Thus it excludes m=3 even if
C has additional true but
zero-stress contact chords
or the spectator squares have
zero-weight actual contacts.

This theorem **supersedes**
the earlier, weaker pure-central-
actual-degree-two m3 parallel-scaffold
exclusion: the present argument
removes the entire m3 positive
stress support regardless of
the middle square's actual circle
status, square frame, contact
degree or positive circle weight.

It does not eliminate m=4,5,6,
the B3 central-positive-degree>=3
branch, exterior root X,
any k<=6 cases, or the
genuine full seven-outer
actual-contact-cycle equality
configuration in root A.
All 7−m exterior spectators
remain physically present for
the remaining graph lengths and
must not be discarded from
future full-packing inequalities.

A separate exact arithmetic script
[verify_seven_outer_m3_semicircle.py](verify_seven_outer_m3_semicircle.py)
checks every rational trigonometric
margin and the strict final
semicircle width comparison.
It does not replace the full
true-square/stress-force argument
above. The unrestricted
\(R_8\ge\widehat R\)
and Lean 4 formalization remain OPEN.
