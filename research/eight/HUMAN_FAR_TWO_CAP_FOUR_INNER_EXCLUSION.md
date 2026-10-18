# Outer-pair angular crowding forbids four perpendicular inner centers

Research continuation, 2026-10-12. This is a **new complete
macro-case elimination** in the previously open n=8
status-by-outer-count table: exclusive S2/k=3 and S4/k=3
are impossible. The proof uses exact hand angular inequalities
and the previously proved outer-outer angular gap,
without a chosen contact graph, numerical mesh, or common square frame.

## Theorem: a six-square forbidden cap configuration

Suppose at least six **distinct** pairwise interior-disjoint unit
squares lie in the disk \(D_R\) with
\[
R^2\le q_{\rm plus}=9789/2500.
\]
Suppose their six labels split into three populations:

* **R inner pair:** two whole unit squares lie in \(x\ge h_R\)
  for some \(h_R\ge0\), and **both centers have norm \(<1\)**.
* **U inner pair:** two *other* whole unit squares lie in
  \(y\ge h_U\), with \(h_U>7/24\), and **both centers have
  norm \(<1\)**.
* **D opposite pair:** two further whole unit squares lie in
  \(y\le-(1-h_U)\), each with center norm \(\ge1\).

Then such six squares **cannot coexist**.

No assumption of mutual square-frame alignment or any actual
square-square contact is made. The two U and two D caps are
opposite signed sides of a hypothetical central unit square,
so their offsets add to exactly one.

## 1. Four inner rays force a near-outer right-lower witness

The sharp two-inner cap theorem
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md)
gives
\[
h_U< H_*:=(\sqrt3-1)/2.
\]
Write
\[
\alpha:=\arcsin(19/24)\quad
(\pi/6<\alpha<\pi/3).
\]
Since \(h_U>7/24\), the two U-inner centers have
positive y coordinate \(>h_U+1/2>19/24\).
Their center angles lie strictly within
\((\alpha,\pi-\alpha)\), on opposite sides of \(\pi/2\).

The two R-inner centers have center x \(>1/2\), hence
ray angles in \((-\pi/3,\pi/3)\), one negative and one
positive by the same cap theorem.
Exactly as in
[HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md](HUMAN_PERPENDICULAR_FOUR_INNER_CAP_BOUND.md),
the four labels are distinct, so their successive
center-ray gaps exceed \(\pi/3\). The upper U ray,
the lower U ray, and the positive R ray imply the
negative R-center angle obeys
\[
-\pi/3<\theta_{R_-}<-\alpha.                 \tag{1}
\]
Indeed the U pair has angular difference \(>\pi/3\),
so its positive-x member has angle
\(<2\pi/3-\alpha\); this member is more than
\(\pi/3\) above the positive-y R member; that
R member is more than \(\pi/3\) above \(R_-\).

Put \(r=|p_{R_-}|<1\). From \(p_{R_-}.x\ge1/2\)
and (1),
\[
p_{R_-}.x=r\cos|\theta_{R_-}|
<r\cos\alpha
=r\frac{\sqrt{215}}{24}
<r\frac58.
\]
The last inequality is exactly \(\sqrt{215}<15\).
Therefore
\[
\boxed{4/5<r<1.}                               \tag{2}
\]
This near-outer inner-center witness is forced *without*
assuming the R-side offset is bounded below beyond \(h_R\ge0\).

## 2. Two far D rays occupy one narrow southern arc

The D whole-cap condition gives each D center
\[
p_D.y\le -(1-h_U+1/2)=-(3/2-h_U)
<-(2-\sqrt3/2).
\]
Every square center in \(D_R\) has radial norm
\[
|p|<r_0:=283/200,                              \tag{3}
\]
because \(|p|^2+|p|+1/2\le R^2\le9789/2500\)
and the left-hand side at \(r_0\) equals
\(156689/40000>9789/2500=156624/40000\).

It follows that each D center satisfies
\[
\frac{-p_D.y}{|p_D|}
>\frac{2-\sqrt3/2}{283/200}>\frac45.
\]
For the final inequality it suffices that
\(\sqrt3<217/125\), because
\(2-\sqrt3/2>283/250\);
the rational square check is
\(3\cdot125^2=46875<217^2=47089\).

Set \(\beta=\arcsin(4/5)=\arctan(4/3)\).
Represent all D polar angles in \((-\pi,0)\).
Both D rays lie in the **single nonwrapping arc**
\[
-\pi+\beta<\theta_D<-\beta,\quad
\beta>\pi/4.                                     \tag{4}
\]
The existing arbitrary-frame
[HUMAN_STABLE_OUTER_ANGLE.md](HUMAN_STABLE_OUTER_ANGLE.md)
gives for these two **distinct outer centers**
\[
\boxed{\text{their smaller angular gap}>
\delta_0:=\pi/4-1/500}.                         \tag{5}
\]

## 3. An inner radius above 4/5 repels all far D rays

We prove an elementary mixed inner/outer angular fact
under (2)–(3).

**Claim.** If one center has \(4/5<r<1\),
another has \(1\le s<283/200\), and they
are distance at least one apart, their smaller
angular separation must exceed
\[
\delta_1:=\pi/6+1/100.                          \tag{6}
\]

For \(0\le\delta\le\delta_1\), use
\(\cos\delta\ge\cos\delta_1>43/50\).
To verify the latter without numerical evaluation,
use \(\sqrt3>433/250\),
\(\cos(1/100)>1-1/20000\), and
\(\sin(1/100)<1/100\):
\[
\cos(\pi/6+1/100)
>\frac{433}{500}\Big(1-\frac1{20000}\Big)
-\frac1{200}
>\frac{43}{50}.
\]
The last positive difference is \(9567/10000000\);
the first square comparison is
\(3\cdot250^2=187500>433^2=187489\).

The cosine law then yields
\[
\begin{aligned}
|p-q|^2
&=(s-r)^2+2rs(1-\cos\delta)\\
&< (123/200)^2+(283/100)(7/50)\\
&=30977/40000<1,
\end{aligned}
\]
contradicting disjoint unit inscribed disks.
This proves (6).

Apply it to \(R_-\) and **each D center**. Both
angles lie in \((-\pi,0)\), and their ordinary
angle difference is \(<\pi\), so the smaller
angular gap is their absolute difference.
By (1), \(\theta_{R_-}>-\pi/3\), while
(4) gives \(\theta_D<-\beta\). A D ray
**above** \(R_-\) could differ by at most
\(\pi/3-\beta<\pi/12<\delta_1\), contradicting
(6). Thus every D ray is **below**
\(R_-\), and (6) forces
\[
\theta_D<\theta_{R_-}-\delta_1
<-\alpha-\delta_1.                              \tag{7}
\]

## 4. The available D arc is too short for two outer rays

Combining (4) and (7), **both** D rays belong to
the same linear interval
\[
-\pi+\beta<\theta_D<-\alpha-\delta_1.
\]
Its width is
\[
W=\pi-\alpha-\beta-\delta_1.
\]

We prove exactly that
\[
\alpha+\beta>\frac{7\pi}{12}.                    \tag{8}
\]
Indeed,
\(\tan\alpha=19/\sqrt{215}>9/7\), since
\(133^2=17689>81\cdot215=17415\).
The arctangent sum formula then gives
\[
\alpha+\beta>
\arctan(9/7)+\arctan(4/3)
=\pi/2+\arctan(3/11).
\]
And \(\arctan(3/11)>\pi/12\), because
\(\tan(\pi/12)=2-\sqrt3<3/11\),
equivalent to \(\sqrt3>19/11\);
the last comparison is \(3\cdot11^2=363>19^2=361\).
Thus (8) is an exact hand inequality.

With \(\delta_1=\pi/6+1/100\), (8) implies
\[
W<\pi-7\pi/12-(\pi/6+1/100)
=\pi/4-1/100
<\pi/4-1/500=\delta_0.                         \tag{9}
\]

But the two distinct D centers are both outer,
so their angular separation must exceed \(\delta_0\)
by (5). Two rays in one interval of width
strictly smaller than \(\delta_0\) cannot do that.
Contradiction. The six-square theorem is proved. QED.

## First complete new macro-branch eliminations

### Exclusive S2=(3+0,2+2), k=3: impossible

Normalize the triple side to R and the nearer two-square
side of the opposite 2+2 axis to U. The farther D side
contains **two outer centers** because its offset is
at least 1/2. The R triple must contribute an outer center.
If \(k=3\) exactly, no other square is outer: the
other two R squares and both U squares are **inner**.
The U offset obeys \(h_U>7/24\) by the 2+2 cap theorem.
All six witnesses have different labels because S2
statuses are single-side. Apply the six-square theorem.
Contradiction. Therefore
\[
\boxed{\text{Every exclusive S2 packing has }k\ge4.}  \tag{10}
\]

### Exclusive S4=(2+1,2+2), k=3: impossible

Normalize its two-member 2+1 cap to R and the
nearer 2+2 cap to U, farther cap to D.
The farther D pair provides two outer centers.
If the R two-member cap offset were \(\ge1/2\),
both R centers would be outer, contradicting k=3.
Thus its offset \(h_R<1/2\), making the opposite
L singleton's cap offset \(1-h_R>1/2\), so L
is outer. If k=3, all remaining R and near U
centers are **inner**. The six-square theorem
applies again and yields a contradiction.
Consequently
\[
\boxed{\text{Every exclusive S4 packing has }k\ge4.}  \tag{11}
\]
This keeps all genuine S4/k=7 **sharp candidate
equality** realizations: it rules out only k=3.

### Stronger general implication

In either S2 or S4, if **both** nearer-2+2 cap
squares happen to have inner centers, then
it is impossible to have **two distinct inner centers**
in a perpendicular whole-square cap. Thus every
such perpendicular two- or three-square cap
must contain **at least one additional outer center**.
This is a *joint center/status restriction*
not encoded in the previous 3,995,040 symbolic
12-status words.

## Status

A written analytic proof, relying only on the existing
hand outer-outer angle gap and elementary inscribed-center
distance bounds. It uses no interval grid, optimization
output, generated classifier, or alignment of arbitrary
square frames. No Lean formalization has yet been done.

This eliminates S2/k=3 and S4/k=3, **not S2 or S4
in full**. D0 with corner-only squares, D1/D2, the
surviving S1/S3 cases, and the global \(R_8\ge\widehat R\)
remain open.
