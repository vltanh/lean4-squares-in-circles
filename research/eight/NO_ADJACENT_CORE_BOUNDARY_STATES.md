# A hand core-pair bound and the global five-word reduction

This note proves a stronger core-to-core pair entry directly. Its final seven-cycle consequence uses the other entries of the completed [four-type pair certificate](FOUR_TYPE_BOUNDARY_PAIR_CERTIFICATE.md). No majority-class assumption is used.

Use \(Q=9789/2500\), core radius \(\rho=1/12\), the four-type rational potential from `verify_fourtype_pairs.cpp`, and \(\beta=9/50\). In particular, the core potential is the odd extension of the piecewise affine function with values

\[
\frac1{10^8}(0,4963699,8978948,12327199,14841828,8212593,-5496777,-2591030,0)
\]

at \(t=0,1/8,\ldots,1\). Every affine segment lies between its endpoint values, so

\[
|\psi_0(t)|<3/20.
\]

## 1. Two core-boundary states have gap greater than 4/3

A core-boundary center lies on the Minkowski sum of a centered unit square and the closed radius-\(1/12\) disk. Therefore its norm satisfies

\[
r\le\frac{\sqrt2}{2}+\frac1{12}<\frac45.
\]

The general exterior lower bound also gives \(r\ge7/12\). For two disjoint unit squares, their inscribed open radius-\(1/2\) disks are disjoint, hence their centers are at distance at least 1. If their positive smaller center-angle gap is \(\delta\in(0,\pi)\), then

\[
\cos\delta\le F(r,s):=\frac{r^2+s^2-1}{2rs}.
\]

On \([7/12,4/5]^2\), the derivative

\[
\frac{\partial F}{\partial r}=\frac{r^2-s^2+1}{2r^2s}>0
\]

is positive, as is the derivative with respect to \(s\). Consequently

\[
\cos\delta\le F(4/5,4/5)=7/32.
\]

The alternating cosine series gives

\[
\cos(4/3)\ge1-\frac{(4/3)^2}{2}+\frac{(4/3)^4}{24}-\frac{(4/3)^6}{720}
=\frac{7709}{32805}>\frac7{32}.
\]

Since cosine decreases on \([0,\pi]\), it follows that \(\delta>4/3\).

## 2. Hand pair-cost bound

Every pair has width excess

\[
0\le u\le\frac{\sqrt2-1}{2}<\frac{21}{100}.
\]

For two core-boundary states, the preceding gap estimate and the potential bound imply

\[
\begin{aligned}
\delta-\frac9{50}u+\psi_b-\psi_a
&>\frac43-\frac9{50}\frac{21}{100}-\frac3{10}\\
&=\frac{14933}{15000}\\
&>\frac{99}{100}.
\end{aligned}
\]

Thus the core-to-core entry of the current cost matrix can be replaced by \(99/100\) using only this hand proof, with no interval verifier needed for the stronger entry.

## 3. Global exclusion of adjacent core boundary states

All remaining entries of the completed four-type pair certificate have common lower bound

\[
a=883146/10^6.
\]

In any actual closed seven-center cycle the gaps sum to \(2\pi\), so its total potential-corrected cost is

\[
\sum_i\left(\delta_i-\frac9{50}u_i+\psi_{i+1}-\psi_i\right)
=2\pi-\frac9{50}\sum_i u_i\le2\pi.
\]

If two consecutive states are both core-boundary states, their edge has cost greater than \(99/100\), while the other six edges have cost at least \(a\). This forces total cost greater than

\[
\frac{99}{100}+6\frac{883146}{10^6}
=\frac{1572219}{250000}
>\frac{710}{113}>2\pi,
\]

a contradiction. The displayed comparison is exact: its difference from \(710/113\) is \(160747/28250000>0\).

Hence **every boundary representative of an actual admissible seven-cycle has no adjacent core states**.

This conclusion is independent of M5, M6, the omitted central frame, and the width-excess baseline. It applies to the ordinary exact-holonomy boundary reduction of any actual packing.

## 4. Only five cyclic radial words remain

Use `C` for a core-boundary state and `O` for an outer-boundary state. A cyclic seven-letter binary word with no adjacent `C` has at most three `C` letters. Up to cyclic rotation, the five possibilities are

| Number of core states | Representative word |
|---|---|
| 0 | `OOOOOOO` |
| 1 | `COOOOOO` |
| 2, circular separation 2 | `COCOOOO` |
| 2, circular separation 3 | `COOCOOO` |
| 3 | `COCOCOO` |

For two core states, their shorter separation is 2 or 3. For three core states, the three intervening positive runs of outer states have lengths 1, 1, 2, uniquely up to rotation. This proves completeness of the table, including every boundary tie after assigning each square one boundary type.

The five-word reduction is not an exclusion of M7 or M8, and it does not yet prove the sharp radius lower bound. Its use is to give the next global capture gate an exact finite radial cover substantially smaller than the original 20 necklaces.
