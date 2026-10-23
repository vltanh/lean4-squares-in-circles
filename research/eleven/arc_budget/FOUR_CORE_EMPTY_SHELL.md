# Four core centers force an empty radial shell

Suppose eleven unit squares with disjoint interiors lie in a disk centered
at the origin with squared radius at most \(U=49013/10000\). If four square
centers have distance at most \(41/40\), then every other center has distance
strictly greater than \(11/10\). Orientations are unrestricted.

The previously proved `WEIGHTED_ARC_EXCLUSION.md` rules out five or more
centers at radius at most \(41/40\), so the hypothesis gives exactly four
such centers. The new conclusion excludes the whole closed shell
\([41/40,11/10]\) for the other seven. It does not exclude the four-core
case itself.

Let \(L_r(S)\) denote the angular measure of the square's intersection with
the circle of radius \(r\) about the disk center. Use the six-circle weight

\[
\begin{split}
W(S)={}&\frac1{10}L_{2/5}(S)+\frac{27}{100}L_{13/20}(S)
       +\frac{73}{1000}L_{9/10}(S)\\
      &+\frac{199}{1000}L_{6/5}(S)
       +\frac{179}{1000}L_{5/4}(S)
       +\frac{179}{1000}L_{7/5}(S).
\end{split}
\]

The positive weights sum to one. Three exact single-square covers prove

| Center and containment condition | Certified lower bound |
| --- | --- |
| \(\lVert p\rVert\le41/40\) | \(W(S)\ge33/40\) |
| \(41/40\le\lVert p\rVert\le11/10\) | \(W(S)\ge149/200\) |
| \(\lVert p\rVert\ge41/40\) and \(S\subseteq\overline B_{\sqrt U}\) | \(W(S)\ge3/8\) |

If one of the seven noncore centers belonged to the middle shell, summing
the four core bounds, its middle bound, and six ring bounds would give

\[
\sum_S W(S)\ge4\frac{33}{40}+\frac{149}{200}+6\frac38
=\frac{1259}{200}>\frac{44}{7}>2\pi.
\]

The rational gap \(1259/200-44/7\) is \(13/1400\). This contradicts
\(\sum_S W(S)\le2\pi\), because disjoint square interiors have disjoint
circle-intersection interiors up to finitely many boundary points.

## Exact closed covers

As in `WEIGHTED_ARC_EXCLUSION.md`, express the center in its own square frame
and use coordinate signs and exchange to put \(a\ge b\ge0\). Initial
closed boxes are \([0,41/40]^2\) for core poses, \([0,11/10]^2\) for middle
poses, and \([0,7/4]^2\) for ring poses. The last box contains all feasible
ring poses because \(U<81/16\).

For a box \([a,A]\times[b,B]\), the exact discard predicates are:

- every domain: \(A<b\);
- core: \(a^2+b^2>(41/40)^2\);
- middle or ring: \(A^2+B^2<(41/40)^2\);
- middle: \(a^2+b^2>(11/10)^2\);
- ring: \((a+1/2)^2+(b+1/2)^2>U\).

All predicates are strict. Every remaining terminal box evaluates the
six-circle weighted measure of the contained rectangle
\([A-1/2,a+1/2]\times[B-1/2,b+1/2]\), using the already audited outward
rational arc bounds in `exact_arcs.py`. A nonterminal box is the union of
its two recorded closed midpoint children. No numerical optimization is
part of the proof.

| Certificate | Nodes | Arc leaves | Discard leaves | Maximum depth |
| --- | ---: | ---: | ---: | ---: |
| `SHELL_CORE_COVER.json` | 5,649 | 2,548 | 277 | 21 |
| `SHELL_MIDDLE_COVER.json` | 327 | 118 | 46 | 16 |
| `SHELL_RING_COVER.json` | 1,077 | 270 | 269 | 22 |

Run `python generate_four_core_shell.py` to regenerate the three full trees
and `python check_four_core_shell.py` to replay them. The replay does not
import the generator; it recomputes every cover split, domain discard, and
one of the 2,936 accepted arc bounds. Both inherit the assertion-mode guard
from `exact_arcs.py`; the replay also has its own guard.
