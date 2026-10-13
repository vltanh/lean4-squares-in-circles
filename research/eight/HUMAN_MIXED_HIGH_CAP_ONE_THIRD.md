# New full-frame mixed-cap opposite-sign theorem at h>=1/3

**Status: analytical hand exclusion with exact rational margins.**
Research continuation 2026-10-12. This improves
HUMAN_MIXED_HIGH_CAP_37_100.md from h>=37/100 to **h>=1/3**,
using the new sharp one-square envelope
[HUMAN_CAP_ENVELOPE_ONE_THIRD.md](HUMAN_CAP_ENVELOPE_ONE_THIRD.md).

## Theorem

Let two **distinct, interior-disjoint genuine unit squares**
with arbitrary independent orientations lie in a disk with
\(R^2\le q_+:=9789/2500\), both wholly beyond the same
outward side line \(y=h\) with
\[
\boxed{h\ge1/3}.
\]
Let p be the **inner** square center (\(|p|<1\)),
and q the **outer** center (\(|q|\ge1\)).
Then their transverse center x coordinates have
**strictly opposite signs**:
\[
\boxed{p_xq_x<0.}
\]
The boundary p_x=0 is also excluded, not just equal
nonzero signs. This result is about centers, not
whole-square quadrant membership.

### Full proof

If h>=1/2, the inner center cannot exist, because
whole-cap containment forces \(p_y\ge h+1/2\ge1\).
So consider 1/3<=h<1/2. Assume to the contrary
\(p_xq_x\ge0\).

The previously proved *all-frame mixed near-cap polarity*
HUMAN_MIXED_NEAR_CAP_POLARITY.md applies since
h>=1/3>7/24. Its strict angular proof includes
the weak same-sign boundary case and forces:
\(q_x\ne0\); after reflecting x if necessary,
\[
0\le p_x<1/4,\qquad q_x>7/10.                \tag{1}
\]

Apply the **new full-frame one-square cap envelope**
to the outer square Q at h>=1/3:
\[
(1+h)^2+(q_x+1/2)^2\le q_+.
\]
Since h>=1/3 and the rational comparison
\[
(4/3)^2+(97/100+1/2)^2-q_+
=2077/90000>0,
\]
we have
\[
\boxed{7/10<q_x<97/100.}                      \tag{2}
\]

The whole-cap center projections and |p|<1 give
\[
a:=5/6\le p_y<1,\qquad q_y\ge a.
\]
The universal true-square farthest-vertex norm
bound gives
\[
|q|<r_0:=283/200.
\]
Therefore
\[
q_y<\sqrt{r_0^2-q_x^2}.
\]
Crucially, we keep the correlation between
the outer center's x and y coordinates:
from q_x<97/100 and
\[
r_0^2-(97/100)^2-(103/100)^2
=17/40000>0,
\]
it follows that
\[
\boxed{\sqrt{r_0^2-q_x^2}>103/100.}           \tag{3}
\]

Now (1) implies \(0<q_x-p_x<q_x\).
There are only **two** possible signed y orders.

**Case q_y>=p_y.** Since \(p_y\ge a\),
\[
\begin{aligned}
|q-p|^2
&=(q_x-p_x)^2+(q_y-p_y)^2\\
&<q_x^2+\left(\sqrt{r_0^2-q_x^2}-a\right)^2\\
&=r_0^2+a^2-2a\sqrt{r_0^2-q_x^2}\\
&<r_0^2+a^2-2a(103/100)\\
&=\frac{352801}{360000}
=1-\frac{7199}{360000}<1.
\end{aligned}
\]
This is an **exact full-interval argument**:
the dependence between the outer center
coordinates has not been replaced by
independent worst-case bounds.

**Case q_y<p_y.** Since \(q_y\ge a\)
and \(p_y<1\), we have
\[
|q_y-p_y|<1-a=1/6.
\]
Combined with (1),(2),
\[
|q-p|^2<(97/100)^2+(1/6)^2
=\frac{87181}{90000}
=1-\frac{2819}{90000}<1.
\]

Both cases contradict \(|q-p|\ge1\), required
because every genuine unit square contains
an open inscribed disk of radius 1/2,
and the two such disks are disjoint.
This contradiction proves \(p_xq_x<0\). QED.

## Exact S2/k4 application and honest limits

In the surviving **exclusive S2=(3+0,2+2),
k=4** class, normalize U as the nearer
two-square cap. Its two distinct U members
are precisely one inner and one outer center,
by the already completed S2-near-both-inner
and k=3 exclusions. The offset satisfies
\(7/24<h_U<97/200\).

The theorem excludes **every weak same-sign
near-U pair** with \(h_U\ge1/3\). Hence
the latest necessary three-cell decomposition is:

| Cell | Near-U cap offset | Center signs |
| --- | --- | --- |
| A | \(1/3\le h_U<97/200\) | Strictly opposite |
| B | \(7/24<h_U<1/3\) | Strictly opposite |
| C | \(7/24<h_U<1/3\) | Weak same sign; retain previously proven center, quadrant and frame-defect conditions |

This improves the previous cell-C upper cutoff
from 37/100 to **1/3** and deletes its entire
closed intermediate band [1/3,37/100).
None of these three residual cells has been
proved empty as a whole.

The counterexample in
RATIONAL_DIAGONAL_CAP_ENVELOPE_COUNTEREXAMPLE.md
shows the **one-square** envelope itself is
false already at h=293/1000>7/24.
Therefore applying the new one-square inequality
below 1/3 without additional proof would be
invalid. The remaining low-offset **two-square**
cell C may still admit a different sharp
pairwise SAT obstruction; no counterexample
to its mixed inner/outer impossibility has been
claimed.

The exact-fraction audit
[verify_mixed_high_cap_one_third.py](verify_mixed_high_cap_one_third.py)
checks the final positive rational margins.
The analytic proof, not any numerical solver,
establishes the continuous implication.
The unrestricted \(R_8\ge\widehat R\)
and full equality/Lean program remain OPEN.
