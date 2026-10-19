# Complete hand proof of exterior-frame concentration

**Theorem.** Let eight unit squares with pairwise disjoint open interiors
lie in a disk centered at the origin with squared radius
\(q\le Q=9789/2500\). The seven exterior square frames, considered modulo
\(\pi/2\), admit real lifts in an interval of length strictly less than
\(7/10\). This theorem has no retained computational coverage premise.

## 1. The geometric hand inputs

The hand central-core theorem gives a unique central square whose open
interior contains the closed radius-\(1/12\) disk. The other seven squares
are exterior. Order their centers by polar angle. The hand common-point
lemma gives each adjacent center gap \(\delta_i>19/25\), with
\(\sum_i\delta_i=2\pi\).

The fixed-axis radial-boundary reduction translates each exterior center
to the core boundary or the containing-disk boundary. It preserves all
seven actual square frames, their cyclic order, and one initially selected
true separating axis on each neighboring pair. Its use here relaxes
nonneighbor constraints. Every resulting neighbor still has disjoint
open interiors, so the common-point and retained-axis lemmas continue to
apply. In particular every gap is below \(2\pi-114/25<3\pi/4\).

No orientation window has been assumed at this stage.

## 2. The complete continuous pair table

Split the outer radial boundary at \(b/a=1/4,3/7\) into types L, M, H,
and retain the whole core curve as C. With \(a_0=\sqrt{Q-1/4}-1/2\)
and \(c_0=\sqrt{Q/2}-1/2\), use the positive-half labels

\[
\begin{aligned}
L_C&=7.506931(7/12-a)+1.077372b,\\
L_L&=.403875(a-a_0)+1.089065b,\\
L_M&=-2.143075+1.489593a+1.580219b,\\
L_H&=\pi/4-.569472(a-c_0)+.390886(b-c_0).
\end{aligned}
\]

For a state \(\alpha=\sigma\arctan(b/a)\), set
\(\psi=\alpha-\sigma L\). At a type endpoint or nearest-axis tie,
choose one representative once for each vertex and use it on both
incident edges. The lifted-state telescoping lemma requires no continuity
or matching of two alternative representative values.

Put

\[
h(\phi)=\frac{|\sin\phi|+|\cos\phi|-1}{2},\qquad\beta=9/50.
\]

The ten whole-pair hand proofs and their independent audits establish

\[
\delta_i-\beta h(\phi_i)+\psi_{i+1}-\psi_i
>\Gamma_{t_i t_{i+1}},
\qquad
\Gamma=\begin{pmatrix}
.92&.91&.9005&.8833\\
.91&.91&.9005&.8833\\
.9005&.9005&.8912&.8926\\
.8833&.8833&.8926&.9099
\end{pmatrix}.
\tag{1}
\]

All decimals are exact rational numbers. The
[coverage inventory](FOUR_TYPE_HAND_COVERAGE_INVENTORY.md) binds every
entry to its full continuous proof and review. There are 128 ordered
source-axis branches; reflected reversal covers the retained target axes.
The last entry, C/M, passes its
[independent audit](CORE_MID_WHOLE_PAIR_INDEPENDENT_AUDIT.md).
Every entry is proved before frame concentration, for all admissible
angles, all signs, and every point on its stated side or arc.

## 3. The seven-walk budget

Subtract \(a=.8833\) from every edge of (1). All residuals are nonnegative.
Every triangle has residual sum at least \(p=.0265\): the four unordered
triangle sums are \(.0611,.0267,.0265,.0265\).

Every loop except M has residual at least \(p\). The M loop has residual
\(.0079\), and every off-diagonal edge incident to M has residual at least
\(.0093\). Thus a closed walk containing that loop and any other vertex
has residual at least

\[
.0079+2(.0093)=p.
\]

The constant seven-step M walk has residual \(7(.0079)>p\).
Every other odd closed walk contains an odd simple cycle; on four vertices
this is a loop or triangle. Deleting the other nonnegative residual edges
proves

\[
\sum_{i=0}^{6}\Gamma_{t_i t_{i+1}}
\ge7a+p=\frac{3881}{625}.
\tag{2}
\]

This is a finite graph argument, without a word search.

Let \(U=\sum_i h(\phi_i)\). Since the potentials telescope and the physical
center gaps sum to \(2\pi\), (1)--(2) give

\[
2\pi-\frac9{50}U>\frac{3881}{625},
\qquad
U<\frac{710/113-3881/625}{9/50}
=\frac{10394}{25425}.
\tag{3}
\]

Here the hand Machin bound \(\pi<355/113\) supplies the strict rational
upper bound. The radial deformation preserved the actual frames, so (3)
holds for the original packing's physical orientation tour.

## 4. Lift the orientation tour

Write \(T=\pi/2\), \(H=T/2\), and

\[
g(d)=\frac{\cos d+\sin d-1}{2},\qquad 0\le d\le H.
\]

This function is increasing and concave, \(g(0)=0\), and
\(g(H)=(\sqrt2-1)/2\). If \(x_i\in[-H,H]\) is a signed shortest
orientation-circle increment between the two adjacent frames, then
\(h(\phi_i)=g(|x_i|)\). Concavity gives

\[
g(d)\ge\frac{g(H)}H d.
\tag{4}
\]

At \(z=7/10<H\), the lower sine and cosine Taylor polynomials give

\[
2g(z)>
\frac{2945220061}{7200000000}
>\frac{10394}{25425},
\tag{5}
\]

and the exact difference in the second comparison is
\(201866893/813600000000>0\). Since \(g\) is increasing and \(z<H\),
(3)--(5) also give \(U<2g(H)=\sqrt2-1\).
Therefore (4) implies

\[
\sum_i|x_i|\le\frac H{g(H)}U<2H=T.
\]

The sum of the signed increments is an integer multiple of \(T\); its
absolute value is less than \(T\), so that sum is zero. They consequently
define a closed real lift of the seven-frame tour. Let \(D\) be the range
of its lifted values. Every closed real walk has total variation at least
twice its range, hence \(D<H\).

The function \(g\) of shorter orientation-circle distance is a metric.
For two distances whose sum is at most \(H\), its triangle inequality
follows from concavity and \(g(0)=0\). If their sum exceeds \(H\), (4)
bounds the sum of the two costs below by \(g(H)\), which bounds every
direct cost above. Apply this triangle inequality separately to the two
parts of the cyclic tour between an extreme low and extreme high lift.
Their direct circle distance is \(D\), since \(D<H\). Thus

\[
U\ge2g(D)=\cos D+\sin D-1.
\]

Together with (3)--(5) and strict monotonicity of \(g\) on \([0,H]\),
this forces \(D<7/10\), proving the theorem.

## 5. Consequences for the remaining hand problem

The seven exterior frames fit in one open 45-degree interval, so the
former M5 and M6 branches are entirely excluded. The central square's
orientation remains free.

The frame premise of [the seven quarter-word reduction](SEVEN_QUARTER_WORDS.md)
and [the common hand table](COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md)
is now proved. The latter table rules out the four words containing a 2,
since their corrected edge costs sum to more than

\[
4(.9775)+2(.785)+.815=6.295>44/7>2\pi.
\]

Only \(0010111\), \(0011011\), and \(0101011\) remain. The first two need
their separate word exclusions. The candidate word needs the global hand
capture that supplies the hypotheses of the already proved sharp terminal.
Those subsequent gates are not asserted by this frame theorem.
