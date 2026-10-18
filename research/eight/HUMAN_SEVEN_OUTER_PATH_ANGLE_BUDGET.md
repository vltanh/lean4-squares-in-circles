# Full seven-outer stressed path: an exact near-right-angle angular bottleneck

**2026-10-12 research continuation.** This is a global contact/stress
structural **necessary inequality**, not an exclusion of the branch.
It is an example of moving from computer-enumerated stress supports
to an exact *hand-proved whole-configuration* requirement.

## Theorem

Let an attained minimum-radius packing of eight disjoint-interior
unit squares lie in \(D_R\) with
\[
R^2\le9789/2500.
\]
Assume there are **seven outer-center** exterior squares and the
outer-induced *actual-contact* graph is **not** the full seven-cycle.
Choose a normalized physical stress whose central square C has
**exactly two distinct positive-stress neighbors**.

By
[HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md](HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md),
the entire nontrivial positive-stress graph is a single
C-rooted cycle \(C-S_1-\cdots-S_m-C\),
\(3\le m\le7\), and successive \(S_i\) are angularly
consecutive outer-center square labels.

Suppose specifically the stressed cycle uses **all seven**
outer squares, \(m=7\). Let
\(\delta_1,\ldots,\delta_6\) denote the ordinary
positive angular gaps between the center rays of
its six successive *contacting outer pairs*
\(S_i,S_{i+1}\), and let \(\gamma\) denote the
seventh circular gap from \(S_7\) back to \(S_1\),
across which **the two outer labels do not contact**.

Then the missing angular gap obeys the stringent
**exact rational two-sided bound**
\[
\boxed{\frac{\pi}{2}-\frac1{800}
       <\gamma<
       \frac{\pi}{2}+\frac3{250}.}                 \tag{1}
\]

Furthermore, **each of the six contacting outer
center-ray gaps** belongs to the narrow interval
\[
\boxed{\frac{\pi}{4}-\frac1{500}
       <\delta_i<
       \frac{\pi}{4}+\frac9{800}
       \qquad(i=1,\ldots,6).}                     \tag{2}
\]
Their total positive "excess" above the
universal outer-pair separation baseline is
\[
\boxed{0<
  \sum_{i=1}^{6}\left(
     \delta_i-\frac{\pi}{4}+\frac1{500}
  \right)
  <\frac{53}{4000}.}                              \tag{3}
\]

Thus a seven-outer path connected to exactly
two opposite central stressed spokes cannot
have arbitrary angular contact gaps: **six
actual outer contacts must almost realize
the critical \(45^\circ\) sector angle,
and the single omitted outer edge must
occupy an almost \(90^\circ\) angular hole**.

No common square orientation or contact-frame
alignment is assumed. The real candidate's
**full seven-outer actual-contact cycle**
is a *different* branch and is preserved.

## 1. Opposite central force normals give center distance >=2

By the physical-stress force equilibrium at
the strictly circle-free central square,
its two positive contact forces have
opposite unit normals \(n,-n\) and equal
magnitudes.

Write A and B for the two outer neighbor
square labels \(S_1,S_7\).
The two tight C--A and C--B support
conditions yield the projection inequality
(see the complete calculation in
HUMAN_SEVEN_OUTER_STRESS_CYCLE_NORMAL_FORM.md)
\[
n\cdot(p_A-p_B)
\ge h_A(n)+h_B(n)+2h_C(n).
\]
Every unit square has projected half-width
at least \(1/2\) in any unit normal.
Therefore
\[
\boxed{|p_A-p_B|\ge
  n\cdot(p_A-p_B)\ge2.}                          \tag{4}
\]

Both A and B are **outer centers**, so their
radii \(r,s\) satisfy
\[
1\le r,s<r_0:=283/200
\]
by the universal true-square farthest-vertex
bound \(r^2+r+1/2\le9789/2500\).
The upper endpoint r_0 is strict because its
left-hand side exceeds the ceiling.

Let \(\Delta\in[0,\pi]\) be the **smaller**
polar angle between A and B.
The cosine law and (4) give
\[
\cos\Delta\le
\frac{r^2+s^2-4}{2rs}.                           \tag{5}
\]
The right-hand side is **strictly increasing**
in each variable on \([1,r_0]\):
its r derivative equals
\((r^2-s^2+4)/(2r^2s)>0\), because
\(r^2\ge1\) and \(s^2<r_0^2<4\);
the s derivative is symmetric.
Hence
\[
\cos\Delta<
\frac{2r_0^2-4}{2r_0^2}
=1-\frac2{r_0^2}
=\frac{89}{80089}.                               \tag{6}
\]

The elementary sine Taylor lower bound gives
\[
\sin(1/800)>
\frac1{800}-\frac1{6\cdot800^3}
>\frac1{850}>\frac{89}{80089}.
\]
Both final comparisons have strict **positive
exact rational differences**
\[
\frac1{800}-\frac1{6\cdot800^3}-\frac1{850}
=\frac{3839983}{52224000000}>0,
\quad
\frac1{850}-\frac{89}{80089}
=\frac{4439}{68075650}>0.
\]
If \(\Delta\le\pi/2-1/800\), cosine monotonicity
would yield
\(\cos\Delta\ge\sin(1/800)>89/80089\),
contradicting (6).
Thus
\[
\boxed{\Delta>\pi/2-1/800.}                      \tag{7}
\]

This angular separation is a consequence of
**opposite central stress forces and true square
support**, not the weaker generic
two-outer-center angular theorem.

## 2. Six successive outer angular gaps consume almost 3/2 turns

The independent arbitrary-frame theorem
[HUMAN_STABLE_OUTER_ANGLE.md](HUMAN_STABLE_OUTER_ANGLE.md)
proves for *every distinct pair of outer
centers* at this disk ceiling the **smaller**
angular gap \(>\delta_0\), where
\[
\delta_0:=\pi/4-1/500.
\]
Therefore each of the six **ordinary circular
successive gaps** satisfies
\(\delta_i>\delta_0\) (even if a gap were
greater than pi, this weaker statement
would still hold).

Since
\[
\sum_{i=1}^6\delta_i>6\delta_0
=3\pi/2-6/500>\pi,
\]
the complementary seventh gap satisfies
\[
0<\gamma=2\pi-\sum_{i=1}^6\delta_i
<\pi/2+6/500<\pi.
\]
Thus \(\gamma\) is exactly the **smaller**
center-ray angle between the stressed
C-neighbors A and B:
\[
\Delta=\gamma.
\]
Apply (7) to get the lower half of (1).
The preceding generic outer-gap bound gives
the upper half of (1), since
\(6/500=3/250\). QED for (1).

## 3. Each contacting outer gap is within a tiny rational margin of pi/4

Define
\[
\varepsilon_i:=\delta_i-\delta_0>0.
\]
From the angular sum and lower half of (1),
\[
\begin{aligned}
\sum_{i=1}^6\varepsilon_i
&=2\pi-\gamma-
  6(\pi/4-1/500)\\
&= \pi/2-\gamma+6/500\\
&<\frac1{800}+\frac6{500}
=\frac{53}{4000}.                                \tag{8}
\end{aligned}
\]
Because every epsilon_i is positive,
each epsilon_i is strictly below
\(53/4000\), so
\[
\delta_0<\delta_i<
\delta_0+\frac{53}{4000}
=\pi/4+\frac9{800}.
\]
This proves (2),(3). QED.

## The next decisive computer-to-hand inequality

A fully global result for this **particular
structural root** would follow from the
following explicitly identified target:

> **Six-edge outer-contact chain rigidity goal.**
> Prove that seven distinct outer-center
> unit squares in \(D_{\sqrt{q_+}}\),
> connected by **six successive actual contacts**
> whose rays each satisfy (2), and accommodating
> a central unit C with two opposite stressed
> spokes as above, cannot form a full eight-square
> packing with radius below \(\widehat R\).
> A stronger *configuration-free* angular
> obstruction \(\sum_i\varepsilon_i\ge53/4000\)
> would eliminate this entire m=7
> positive-stress-path case outright,
> but is **not yet known**.

Computer assistance can now focus on **true
square-frame SAT contact equations for the
six successive actual outer pairs**, circle
vertex constraints and central whole-square
support—not on enumerating millions of
independent central side-status words.
A numerical support candidate does not
prove the six-edge inequality. Any
computer-discovered inequality must be
converted to a hand proof for the complete
frame/position domain.

The other C-rooted stressed cycle lengths
m=3,4,5,6, the central branching stress
case, the exterior inner-witness case and
the **equality-bearing actual seven-outer
contact ring** remain open. The unrestricted
\(R_8\ge\widehat R\) is not proved.
