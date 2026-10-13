# Mixed inner/outer two-square cap: a strict three-quarter-radian angular gap

Research continuation, 2026-10-12. This is a new **arbitrary-frame,
all-center-position** geometric lemma applicable directly to the
remaining exclusive S2/k=4 case (one inner and one outer center on
the nearer 2+2 side). It does not assume a contact graph, frame
alignment, or a selected separating axis between the two squares.

## Theorem

Let two distinct unit squares with disjoint open interiors fit
inside a disk centered at zero with
\[
R^2\le q_+=9789/2500.
\]
Let both *whole* squares lie in the outward cap
\[
\{y\ge h\},\qquad h\ge7/24.
\]
Suppose their centers \(p\) and \(q\) satisfy
\[
|p|<1,\qquad |q|\ge1.
\]

Write \(\theta_p,\theta_q\in(0,\pi)\) for their ordinary
polar angles measured from the positive x axis. Then
\[
\boxed{|\theta_p-\theta_q|>3/4\ {\rm radians}.}     \tag{1}
\]

**Same-transverse-sign refinement.** If the two center x
coordinates have the *same strict sign*, then
\[
\boxed{|p_x|<1/4,\qquad |q_x|>7/10}.               \tag{2}
\]
Moreover the **outer** center lies farther from the
positive y diameter in angular order: for both centers in
the positive-x half-plane,
\[
\theta_q<\theta_p-3/4,
\]
and for both in the negative-x half-plane,
\[
\theta_q>\theta_p+3/4.
\]
This is a theorem about center coordinates, **not**
whole-square quadrant membership.

## 1. Strict radial bounds and a cap polar interval

For any unit square of any frame with center z and
containing disk radius squared at most q_+, the actual
farthest-vertex formula gives
\[
|z|^2+|z|+1/2\le q_+.
\]
It follows that
\[
|z|<r_0:=283/200,
\]
since at r_0 the left side exceeds q_+ by
\(65/40000>0\).

For any unit square wholly in \(y\ge h\),
its projected vertical half-width is at least \(1/2\).
Thus both centers satisfy
\[
p_y,q_y\ge h+1/2\ge19/24.
\]
In particular the **inner** center has radius
\[
19/24\le|p|<1,
\]
and the **outer** center has radius
\(1\le|q|<283/200\).

Set
\[
\alpha:=\arcsin(19/24),\qquad
\beta:=\arcsin(475/849).
\]
The polar angles satisfy
\[
\theta_p\in(\alpha,\pi-\alpha),\qquad
\theta_q\in(\beta,\pi-\beta),                   \tag{3}
\]
because
\[
\frac{q_y}{|q|}>
\frac{19/24}{283/200}=\frac{475}{849}.
\]
We will use the two strict elementary bounds
\[
\alpha>17/20,\qquad \beta>29/50.                \tag{4}
\]
To check them without decimals, use the alternating
sine Taylor upper bound \( \sin x\le x-x^3/6+x^5/120 \)
on these positive angles:
\[
\frac{19}{24}
-\left(\frac{17}{20}-\frac{(17/20)^3}{6}
       +\frac{(17/20)^5}{120}\right)
=\frac{5161381}{128000000}>0,
\]
\[
\frac{475}{849}
-\left(\frac{29}{50}-\frac{(29/50)^3}{6}
       +\frac{(29/50)^5}{120}\right)
=\frac{121549694833}{10612500000000}>0.
\]
Monotonicity of sine on \((0,\pi/2)\) gives (4).

## 2. Mixed-center angular separation

Two interior-disjoint unit squares contain disjoint
open inscribed radius-\(1/2\) disks, so their
centers have mutual distance at least one.

Suppose contrary to (1) that the ordinary angle gap
\(\delta=|\theta_p-\theta_q|\le3/4\).
Both angles belong to \((0,\pi)\), so \(\delta<\pi\)
and is the smaller angular separation.

The alternating cosine Taylor lower bound yields
\[
\cos\delta\ge\cos(3/4)
\ge 1-\frac{(3/4)^2}{2}
+\frac{(3/4)^4}{24}
-\frac{(3/4)^6}{720}
=\frac{239759}{327680}>\frac{73}{100},
\]
where the final exact positive margin is
\[
\frac{239759}{327680}-\frac{73}{100}
=\frac{2763}{1638400}>0.
\]

For radial norms \(r=|p|\in[19/24,1]\) and
\(s=|q|\in[1,283/200]\), the cosine law gives
\[
|p-q|^2=r^2+s^2-2rs\cos\delta
<r^2+s^2-\frac{73}{50}rs.
\]
This quadratic is convex in r for each fixed s,
and in s for each fixed r. Its maximum over the
closed rectangle therefore occurs at one of the
four endpoint pairs. Their exact values, in order
\((19/24,1),(19/24,283/200),(1,1),(1,283/200)\),
are
\[
\frac{6781}{14400},\quad
\frac{715289}{720000},\quad
\frac{27}{50},\quad
\frac{37453}{40000}.
\]
Each is **strictly below one**; the greatest equals
\(1-4711/720000\).

Thus \(|p-q|^2<1\), a contradiction. This proves
the full orientation-independent gap (1).

## 3. Same-transverse-sign polarity and displacement

First suppose **both center x coordinates are positive**,
so both angles lie in \((0,\pi/2)\).
By (3)–(4),
\[
\theta_p>\alpha>17/20.
\]
If \(\theta_q\ge\theta_p\), their gap is
\[
\theta_q-\theta_p<\pi/2-17/20
<11/7-17/20=101/140<3/4,
\]
contrary to (1). Here only \(\pi<22/7\)
and the exact positive margin
\(3/4-101/140=1/35\) are used.

Hence necessarily
\[
\theta_q<\theta_p-3/4.
\]
Since \(\theta_q>\beta>29/50\),
\[
\theta_p>\frac{29}{50}+\frac34
=\frac{133}{100}.
\]
For the inner center,
\[
0<p_x=|p|\cos\theta_p
<\cos(133/100)
\le1-\frac{(133/100)^2}{2}
+\frac{(133/100)^4}{24}
=\frac{590220721}{2400000000}<\frac14.
\]
The final margin is \(9779279/2400000000>0\).

For the outer center,
\[
0<\theta_q<\pi/2-3/4,\qquad
q_x=q_y\tan(\pi/2-\theta_q)
>(19/24)\tan(3/4).
\]
A direct derivative/integration argument gives
\(\tan x>x+x^3/3+2x^5/15\) for \(0<x<\pi/2\):
successively use \(\tan'>1\), then
\(\tan'>1+x^2\), then
\(\tan'>1+x^2+2x^4/3\).
At \(x=3/4\) the lower polynomial is
\(2361/2560=9/10+57/2560>9/10\).
Therefore
\[
q_x>(19/24)(9/10)=171/240>7/10.
\]
This proves (2) for positive transverse signs.

If both center x coordinates are negative,
reflect the entire configuration across the y axis.
All hypotheses are preserved, and the same proof
applies to \(-p_x,-q_x\); its angular-order
statement becomes
\(\theta_q>\theta_p+3/4\).
QED.

## Consequences for the remaining eight-square status queue

In the **exclusive S2=(3+0,2+2)** case,
the already established
[HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md](HUMAN_S2_NEAR_INNER_FULL_EXCLUSION.md)
shows that the nearer 2+2 cap cannot have
**two** inner-center members. The existing S2/k=7
exclusion and the two far-cap outer centers imply:

* S2/k=4 has **exactly one inner** and **exactly
  one outer** center on the nearer two-member side,
  alongside the two far-side outer centers and one
  outer R-triple center.
* The two nearer-side center rays must be separated
  by **more than 3/4 radian**.
* If their transverse center coordinates have the
  **same strict sign**, the inner is trapped in
  \(|x|<1/4\) and the outer in \(|x|>7/10\),
  with their forced angular order given above.

These are new exact **continuous positional constraints**,
not a full S2/k=4 rejection. In particular, they
cannot be applied as same-sign statements when the
near-side centers lie on opposite sides of the
origin diameter, or when a D1/D2 status overlap
prevents selection of distinct labels.

The entire S2, S3, S4 and D1/D2 global sharp
lower-bound problem remains open. The actual
S4/k=7 equality configuration is not affected.

[verify_mixed_near_cap_polarity.py](verify_mixed_near_cap_polarity.py)
audits the exact rational margins but does not
replace the hand proof or constitute a Lean theorem.
