# Mixed same-sign cap pairs cannot occur at offset h>=37/100

**Status: full-domain, arbitrary-orientation hand exclusion at the n=8
disk ceiling**, derived from the computer-guided strengthened sharp
single-square cap envelope
[HUMAN_CAP_ENVELOPE_37_100.md](HUMAN_CAP_ENVELOPE_37_100.md).
This improves the previous threshold \(h\ge2/5\) from
[HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md](HUMAN_MIXED_HIGH_CAP_SIGN_SPLIT.md).

## Theorem

Let two distinct unit squares of independent arbitrary frames
have disjoint open interiors in a disk of squared radius
\[
R^2\le q_+:=9789/2500.
\]
Suppose both **whole** squares lie beyond \(y=h\),
with
\[
h\ge37/100.
\]
If one center \(p\) has norm \(<1\) and the other center q
has norm \(\ge1\), then their transverse center coordinates
must have **strictly opposite signs**:
\[
\boxed{p_xq_x<0.}                               \tag{1}
\]
The entire same-weak-sign case, including the p_x=0 boundary,
is impossible for every square orientation.

### Hand proof with a strict rational center-distance margin

If \(h\ge1/2\), the hypothesized inner center is already
impossible because its y normal projection is at least
\(h+1/2\ge1\). Assume \(37/100\le h<1/2\).

Suppose \(p_xq_x\ge0\). By the existing full-orientation
[HUMAN_MIXED_NEAR_CAP_POLARITY.md](HUMAN_MIXED_NEAR_CAP_POLARITY.md)
for h>=7/24 (the hypotheses are met because 37/100>7/24),
the outer x coordinate cannot vanish. Reflect x if necessary:
\[
0\le p_x<1/4,\qquad q_x>7/10.                  \tag{2}
\]
(The weak case p_x=0 is covered by that lemma's exact
zero-center boundary argument.)

Apply the **new full-domain cap envelope** to the outer square q:
\[
(h+1)^2+(q_x+1/2)^2\le R^2\le q_+.
\]
Since h>=37/100, and
\[
(143/100)^2-\Big[q_+-(137/100)^2\Big]
=31/5000>0,
\]
we get the strict upper bound
\[
\boxed{7/10<q_x<93/100.}                      \tag{3}
\]

The inscribed-center farthest-vertex bound gives every
center radius \(<283/200\). Together with \(q_x>7/10\),
\[
q_y^2<(283/200)^2-(7/10)^2
=\frac{60489}{40000}<(123/100)^2.
\]
The last squared rational margin equals \(27/40000>0\).
Whole-cap membership also gives
\(p_y,q_y\ge h+1/2\ge87/100\),
and the inner center has \(p_y<1\).
Therefore
\[
\boxed{87/100\le p_y<1,\qquad
87/100\le q_y<123/100.}                         \tag{4}
\]

Equations (2)--(4), with q_x>p_x, imply the **strict
coordinate distance bounds**
\[
|q_x-p_x|<93/100,\qquad
|q_y-p_y|<123/100-87/100=9/25.
\]
Thus
\[
\begin{aligned}
|q-p|^2
&<(93/100)^2+(9/25)^2\\
&=\frac{1989}{2000}
=1-\frac{11}{2000}<1.                          \tag{5}
\end{aligned}
\]
But each packed unit square contains an open inscribed
radius-1/2 disk. Distinct interior-disjoint unit squares
must have their centers separated by at least one.
Inequality (5) contradicts this. QED.

## Exact S2/k=4 branch pruning

Use the exclusive S2=(3+0,2+2) classification
normalized as R:3,L:0,U:2,D:2, with U the **nearer**
2+2 side. By the already proved S2 near-both-inner
exclusion, in the k=4 branch the two actual near-U
centers consist of *one inner and one outer*.
Their offset h_U is restricted to
\[
7/24<h_U<97/200.
\]

The new theorem excludes **all same-weak-sign** near-U
center pairs whenever \(h_U\ge37/100\).
Consequently the exact remaining three-way
S2/k4 case queue becomes:

| Cell | Offset | Near-U transverse centers |
| --- | --- | --- |
| A (now enlarged) | \(37/100\le h_U<97/200\) | Strictly opposite signs |
| B | \(7/24<h_U<37/100\) | Strictly opposite signs |
| C (shrunk) | \(7/24<h_U<37/100\) | Weak same signs, inner \(|x|<1/4\), outer \(|x|>7/10\), at least one square frame tilted \(>1/2600\) radians |

In the same-sign cell C, the outer U square is also
a genuine **whole NE or NW quadrant owner** with
signed x-clearance \(>1/50\), by
[HUMAN_MIXED_CAP_WHOLE_QUADRANT_OWNER.md](HUMAN_MIXED_CAP_WHOLE_QUADRANT_OWNER.md).
No same-sign branch with offset \(h\ge37/100\)
survives, regardless of frames.

This is genuine **continuous-region pruning**, not a
complete S2/k4 exclusion. In particular the exact
standalone rotated two-square same-sign counterexample
in [RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md](RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md)
contains **two outer centers** and thus does not contradict
the present *mixed inner/outer* theorem.

The actual S4/k7 equality construction, other status
cases, the global lower bound \(R_8\ge\widehat R\),
global equality classification and Lean 4 formalization
remain untouched and OPEN.

[verify_mixed_high_cap_37_100.py](verify_mixed_high_cap_37_100.py)
audits the exact inequalities and endpoint margins only.
