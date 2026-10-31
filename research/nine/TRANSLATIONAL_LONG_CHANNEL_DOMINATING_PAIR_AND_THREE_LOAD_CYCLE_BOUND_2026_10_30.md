# Long-gap domination and the six-body bound for three-load cycles need only translational stress

**Date:** October 30, 2026 UTC. **Status:** complete new corollary and
full scope derivation, awaiting separate current-source review and adoption.
This source does not change the original inventories by itself.

The geometric input is the complete
[two-endpoint expanded-square cover](TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md),
Theorem 1. All other arguments below are elementary and are repeated here.
No angular equilibrium, torque-preserving planarization, circle-mask
classification or common contact-mean selection is needed for this source.

## 1. Physical long-gap domination

Put \(Q=1105/256\), \(M=91/60\). Let finitely many actual unit squares,
with pairwise disjoint open interiors, lie in the disk \(D_{\sqrt Q}\).
Let A and B be two of these squares. For a unit direction d, write
\(h_S(d)\) for the original square's support halfwidth.

Assume

\[
d\cdot(c_B-c_A)\ge2+h_A(d)+h_B(d).                       \tag{1}
\]

**Theorem 1 (physical dominating pair).** Every other actual unit square C
satisfies

\[
\boxed{\quad \operatorname{dist}(C,A)<1
\quad\hbox{or}\quad \operatorname{dist}(C,B)<1.\quad}      \tag{2}
\]

Thus the open distance-one neighborhoods of A and B meet every other
physical square. This concerns all squares, whether stressed, loaded,
unstressed, or unrelated to the contact graph.

*Proof.* The exact corner bound gives \(\|c_C\|<M\), and the expanded
square theorem gives \(d_C:=\operatorname{dist}(c_C,A)<3/2\), or the
same statement for B. In the first case choose p in A attaining d_C.
If d_C<=1/2, then p lies in C's closed inscribed radius-1/2 disk, so
\(\operatorname{dist}(C,A)=0\). Otherwise put

\[
q=c_C+\frac{p-c_C}{2d_C}.
\]

This point belongs to that same inscribed disk and hence to C, while
\(\|p-q\|=d_C-1/2<1\). This proves (2); use B for the other alternative.

The hypothesis (1) is equivalent to \(\operatorname{dist}(A,B)\ge2\).
Only the support-gap formulation is needed below. For completeness, the
reverse implication follows by taking nearest points a in A,b in B:
the direction \(d=(b-a)/\|b-a\|\) maximizes on A at a and minimizes on B
at b. The two supporting hyperplanes have gap \(\|b-a\|\). The forward
implication is immediate by projection. No arbitrary axis is imposed on
the third square.

## 2. The precise translational stress assumptions

Consider a finite positive body-pair support graph on some of the actual
squares. Each positive pair edge ij carries a magnitude \(\mu_{ij}>0\)
and a signed unit separator normal \(n_{ij}\), from i to j. Require the
actual tight support equality

\[
n_{ij}\cdot(c_j-c_i)=h_i(n_{ij})+h_j(n_{ij}).              \tag{3}
\]

At every body there is translational force balance. A body is called
unloaded here precisely when its whole circle-load vector is zero by
having zero circle coefficients; at such a body the sum of its incident
pair-force vectors is zero. A loaded body has positive total circle
weight. The standard normalized translational minimizer stress of
[SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md) has these properties,
as does its separately constructed planar translational variant.

Only the true positive pair degree is used. No positive edge may be
deleted in order to call a body an unloaded degree-two transmitter.
The proof neither assumes nor creates angular balance.

## 3. Full translational path identity without discrete orientations

Let a path connect retained endpoint bodies U,V and have k internal
bodies, all genuinely unloaded of true positive degree two. At each
internal body its two nonzero forces cancel, so their magnitudes agree
and their normals are opposite relative to that body. Orienting the path
from U to V therefore gives one common signed unit direction n and one
positive magnitude on every path edge.

Add the unchanged actual support equalities (3). The intermediate center
coordinates telescope, giving

\[
n\cdot(c_V-c_U)
=h_U(n)+h_V(n)+2\sum_{i\text{ internal}}h_i(n)
\ge h_U(n)+h_V(n)+k.                                    \tag{4}
\]

This uses the actual, possibly tilted square width \(2h_i(n)\ge1\).
There is no claim that it is either 1 or sqrt(2); that stronger discrete
classification requires torque and is deliberately unnecessary here.

Every center has norm below M, so the left side of (4) is below 2M.
Since \(h_U+h_V\ge1\), a path with k>=3 would require a projected
center gap at least four, contradicting \(2M=91/30<4\). Therefore

\[
\boxed{k\in\{0,1,2\}.}                                 \tag{5}
\]

A closed path returning to the same endpoint is likewise impossible:
the telescoped left side would be zero and the summed positive widths
strictly positive. Distinct paths with the same two endpoints remain
possible; this source does not discard parallel retained edges.

## 4. Two long partners at one actual unit are impossible

The following is the purely geometric matching theorem from
[LONG_CHANNEL_ENDPOINT_MATCHING.md](LONG_CHANNEL_ENDPOINT_MATCHING.md),
Theorem 1.1. Its full short proof is included to isolate the dependencies.

Suppose an actual center b has two distinct other actual centers a,c at
distance at least three. Rotate so b=(r,0). The universal bound gives
\(0<r<M\). For either a or c, its horizontal coordinate x satisfies

\[
x<\frac{M^2+r^2-9}{2r}.
\]

The right side increases with r>0, because its derivative is
\(1/2+(9-M^2)/(2r^2)>0\). Hence

\[
x<M-\frac9{2M}=-\frac{7919}{5460}<-\frac{29}{20}.
\]

Both a and c lie in the open disk centered at (-29/20,0) with squared
radius

\[
M^2-(29/20)^2=\frac{89}{450}.
\]

Their mutual squared distance is therefore below \(178/225<1\),
contrary to the disjoint open inscribed radius-1/2 disks of the two
actual unit squares. Thus no center has two distinct partners at
distance at least three.

A k=2 path in (4) gives endpoint-center distance at least three. It
follows that the distinct endpoint pairs of all such paths form a
matching. Again, multiple paths on the same endpoint pair are retained.
This conclusion needs no endpoint load or degree restriction.

## 5. A forbidden triangle in every translationally suppressed graph

**Theorem 2 (translational 2/1/1 triangle obstruction).** Suppose three
distinct actual retained bodies A,B,C are pairwise linked by paths of
the type in Section 3, with at least two internal bodies on AB and at
least one on each of AC and BC. Such a configuration is impossible.

Indeed (4) gives (1) for AB and gives

\[
\begin{aligned}
n_{AC}\cdot(c_C-c_A)&\ge1+h_A(n_{AC})+h_C(n_{AC}),\\
n_{BC}\cdot(c_C-c_B)&\ge1+h_B(n_{BC})+h_C(n_{BC}).
\end{aligned}
\]

The latter inequalities imply \(\operatorname{dist}(A,C)\ge1\) and
\(\operatorname{dist}(B,C)\ge1\), contradicting Theorem 1. Equivalently
one can apply the geometric input's three-square gap corollary directly.

The retained endpoints can have any original loads and arbitrary further
positive edges. This is therefore a block- and component-independent
restriction. Suppressing genuine unloaded degree-two vertices is just a
notation for (4); the actual squares are still present and counted.

## 6. Every three-load positive simple cycle has at most six bodies

**Theorem 3.** If an entire positive translational-stress component is a
simple cycle with exactly three loaded bodies, then it contains at most
six bodies in total.

*Proof.* The three loaded bodies split the cycle into exactly three
maximal unloaded runs. Their endpoint pairs are distinct. Let their
internal body counts be k_1,k_2,k_3. Every internal body is genuinely
unloaded and has true degree two in the entire positive component, so
(5) gives \(0\le k_j\le2\).

Two runs with k_j=2 would share a loaded endpoint and have distinct
other loaded endpoints. Section 4 rules this out. Consequently at most
one run has two bodies, and

\[
k_1+k_2+k_3\le2+1+1=4.
\]

If the cycle had at least seven bodies, equality would be necessary:
it would have exactly seven bodies and run pattern (2,1,1). The three
loaded bodies and the three original runs then satisfy Theorem 2, a
contradiction. Thus the cycle has at most six bodies.

This excludes every seven-, eight-, and nine-body simple three-load
component in the n=9 research window with one common argument. The
eight- and nine-body exclusions were already obtained by the geometric
matching theorem; the new expanded-square cover supplies the complete
seven-body (2,1,1) exit. No existing independent six-cycle closure is
changed. No loaded run is treated as an unloaded transmitter.

## 7. Logical scope and sharpness

Theorems 1--3 apply before any torque, chosen shared-side application
means, physical one-/two-corner classification or common angular-normal
selection audit. If a translational stress happens to be planar, that
additional property is not used. The result therefore does not combine
the separate planar and angular certificates or assume they coincide.

The exact record's seven-square stressed core is retained: its retained
loaded/branching graph is not the forbidden three-load simple cycle.
A long pair may have other squares at physical distance below one from
one endpoint, as Theorem 1 requires. The statements use weak gap/radius
hypotheses and strict covering conclusions, so equality at q=Q is fully
included without a false exclusion of the known record.

No theorem here asserts that every open large-block row contains the
forbidden triangle. No coarse parent, full sharp-radius theorem,
equality classification or Lean integration is declared closed by this
source. The unchanged original caller identities and the complete
downstream prerequisites still need their stated audit.

No pose search, numerical packing certificate, Lean compilation or CI
is used. The only new imported geometric result is the independently
reviewable expanded-square cover linked at the start.
