# Mixed inner/outer cap squares must have opposite transverse center signs from h>=8/25

**Status: all-orientation hand theorem with exact positive rational margins.**
Research continuation 2026-10-12. This strengthens
HUMAN_MIXED_HIGH_CAP_ONE_THIRD.md by lowering the
offset cutoff from 1/3 to **8/25** using the new
[HUMAN_CAP_ENVELOPE_8_25.md](HUMAN_CAP_ENVELOPE_8_25.md).

## Theorem

Let two genuine unit squares of arbitrary independent frames
have disjoint open interiors in a disk of squared radius
\(R^2\le9789/2500\). Suppose both **entire squares**
lie beyond the same outward cap line y=h, for
\[
\boxed{h\ge8/25}.
\]
Let p be the **inner** center (norm <1) and q
the **outer** center (norm >=1). Then
\[
\boxed{p_xq_x<0.}
\]
This rules out even the zero-sign boundary, not merely
strictly equal transverse signs. This is a center-sign,
not whole-quadrant-membership, conclusion.

## Full exact hand proof

For h>=1/2 the proposed inner center cannot exist:
whole-cap projection forces p_y>=h+1/2>=1.
Thus assume 8/25<=h<1/2.

Suppose contrary to the theorem that p_xq_x>=0.
The previously proved full-frame mixed-cap polar
lemma HUMAN_MIXED_NEAR_CAP_POLARITY.md is applicable
since h>=8/25>7/24. It handles the zero-coordinate
boundaries and forces q_x!=0; reflecting the x axis
if needed gives the **strict inequalities**
\[
0\le p_x<1/4,\qquad q_x>7/10.                     \tag{1}
\]

The **new arbitrarily rotated one-square envelope**
at h>=8/25, proved with true vertex geometry and a
noncircular exact Bernstein certificate, gives for
the whole outer square Q:
\[
(1+h)^2+(q_x+1/2)^2\le q_+:=9789/2500.
\]
At h>=8/25 the exact rational comparison
\[
(33/25)^2+(39/40+1/2)^2-q_+
=\boxed{97/40000>0}
\]
therefore yields
\[
\boxed{7/10<q_x<39/40.}                         \tag{2}
\]

Whole-cap projection, and inner radial norm <1, give
\[
a:=41/50\le p_y<1,\qquad q_y\ge a.
\]
Every genuine square center in the search disk has norm
\[
|q|<r_0:=283/200,
\]
by the true farthest-vertex radius inequality.
Hence, retaining the **coupled radial constraint**,
\[
q_y<\sqrt{r_0^2-q_x^2}.
\]
Since q_x<39/40 and
\[
r_0^2-(39/40)^2-(41/40)^2
=\boxed{39/40000>0},
\]
we know
\[
\boxed{\sqrt{r_0^2-q_x^2}>41/40.}               \tag{3}
\]

Because q_x>7/10>p_x>=0, we have
\(0<q_x-p_x\le q_x\). The two possible
signed center-height orders are exhaustive:

**If q_y>=p_y**, then q_y-p_y<
\(\sqrt{r_0^2-q_x^2}-a\). By the cosine-free
radial identity,
\[
\begin{aligned}
|q-p|^2
&<q_x^2+\left(\sqrt{r_0^2-q_x^2}-a\right)^2\\
&=r_0^2+a^2-2a\sqrt{r_0^2-q_x^2}\\
&<r_0^2+a^2-2a(41/40)
=\boxed{7949/8000<1}.
\end{aligned}
\]

**If q_y<p_y**, then p_y-q_y<1-a=9/50,
so
\[
|q-p|^2<(39/40)^2+(9/50)^2
=\boxed{39321/40000<1}.
\]

Both contradictions are **strict over the
whole continuum**, require no common square
frame, and use only exact rational margins
51/8000 and 679/40000 respectively.
The two different square centers must be
at distance at least one, because their
open inscribed half-unit disks are disjoint.
Therefore the same-weak-sign assumption is
impossible, proving \(p_xq_x<0\). QED.

## New S2/k4 cell classification

In exclusive S2=(3+0,2+2), k=4,
the nearer U whole cap holds exactly one
inner-center and one outer-center square;
its offset is in \(7/24<h_U<97/200\).

The new theorem **excludes every same-weak-sign
mixed near-U pair for h_U>=8/25**, lowering the
previous 1/3 cutoff to **8/25**. Thus the
latest necessary exhaustive 3-cell queue is:

| Cell | h_U | Mixed near-U transverse center signs |
| --- | --- | --- |
| A | \(8/25\le h_U<97/200\) | Strictly opposite |
| B | \(7/24<h_U<8/25\) | Strictly opposite |
| C | \(7/24<h_U<8/25\) | Weak same sign, retaining the forced outer whole-quadrant owner and near-axis frame defect |

The prior C interval [8/25,1/3) has
been completely excluded, for all frames.
**None of A, B, or C has yet been
eliminated as an entire branch.**

The genuine exact rotated single-square
counterexample at h=3/10 below this threshold
does **not** contradict the mixed two-square
theorem, because it contains only one square
and no inner/outer pair. It warns against
unjustified extension of the same
one-square envelope into the residual cell C.

[verify_mixed_high_cap_8_25.py](verify_mixed_high_cap_8_25.py)
audits the exact coupled radial endpoint
margins with Fractions. This is not a
numerical sampling claim, unrestricted
\(R_8\ge\widehat R\) proof, global equality
classification or Lean formalization.
