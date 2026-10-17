# The first complete hand mismatch bound for the candidate word

## 1. The closed gate

Use the roles \((H,G,A,B,T,D,E)\), quarter word
\(k=(0,1,0,1,0,1,1)\), and exact squared radius
\(Q=3915534138/10^9\). Write

\[
\phi_i=k_i\pi/2+d_i,\qquad d_i=\theta_{i+1}-\theta_i,
\qquad I=\{0,2,3,4,5\},\qquad S=\sum_{i\in I}|d_i|.
\tag{1}
\]

The physical frame lifts \(\theta_i\) come from the complete hand frame
theorem, so \(|d_i|<7/10\). The boundary reduction supplies the center
gaps \(\delta_i>19/25\), their sum \(2\pi\), and an actual feasible
retained SAT separator on each edge. Every boundary state may
independently have core or outer radial kind.

Assume only the previously proved normalized G/T tangent bounds:

\[
u_G\in[-4/5,-1/20],\qquad u_T\in[1/20,4/5],\qquad
u_E\in[-1,0].                                      \tag{2}
\]

**Theorem.** Every such candidate cycle satisfies

\[
\boxed{S<2/5.}                                     \tag{3}
\]

In particular, each of the five charged frame differences has magnitude
less than \(2/5\). No H/D cut, smaller mismatch assumption, or desired
contact owner is used to prove (3).

## 2. The full-domain charged pair inequalities

Put

\[
\gamma=\frac{89727}{100000},\qquad
\beta=\frac{99}{5000},\qquad
h(x)=\frac{|\sin x|+|\cos x|-1}{2},\qquad
\beta_i=\begin{cases}\beta&i\in I,\\0&i\notin I.\end{cases}
\tag{4}
\]

The fixed rational table is
`CANDIDATE_COARSE_MISMATCH_HAND_DATA.json`. Its **462 closed state
arcs** cover all **22 nonempty role/kind/sign domains** allowed by (2).
Each arc has rational endpoints and a rational affine label \(L=c+pa+qb\).
The unsigned coordinates and signs have the usual conventions:
the own-frame center is \((a,-\sigma b)\), \(u=\sigma b/a\), and
\(\alpha=\sigma\arctan(b/a)\). The two boundary kinds are

\[
\begin{array}{ll}
O:&(a+1/2)^2+(b+1/2)^2=Q,\\
C:&a=7/12\quad(0\le b/a\le6/7),\\
 &(a-1/2)^2+(b-1/2)^2=1/144\quad(6/7\le b/a\le1).
\end{array}                                        \tag{5}
\]

Every core arc stays on its side or corner, including the exact common
endpoint 6/7. At any shared endpoint choose one containing arc once for
the vertex and use the same label on its two incident edges.

**Pair bound.** Every actual feasible retained separator on edge i satisfies

\[
\phi_i-\beta_i h(\phi_i)+L_i-L_{i+1}>\gamma.
\tag{6}
\]

All four original axes are included. The input's seven declared signed
frame ranges are exactly \([-7/10,7/10]\); they introduce no extra
capture premise. The proof of (6) is the independently reviewed
affine-arc hand kernel, now including the explicitly declared width charge.
Its complete source/target support argument is
`AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md`; the conditional interface has the
separate independent review
`CONDITIONAL_AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md`.

For completeness, the retained margins, with
\(W=(1+|\sin\phi|+|\cos\phi|)/2\), are

\[
\begin{aligned}
M_1&=\sigma b+A\sin\phi-\tau B\cos\phi-W,\\
M_2&=A-a\cos\phi+\sigma b\sin\phi-W,\\
M_3&=a\sin\phi+\sigma b\cos\phi-\tau B-W,\\
M_4&=a-A\cos\phi-\tau B\sin\phi-W.
\end{aligned}                                      \tag{7}
\]

Each row fixes a rational \(\lambda\ge0\) and proves

\[
\phi-\beta_i h(\phi)+L_s-L_t-\gamma-\lambda M_j>0.
\tag{8}
\]

The charge depends only on the original directed edge and its angle.
It stays unchanged when axes 2 and 3 are normalized by reflection and
reversal. The two coordinate minima are eliminated by endpoint support,
the derivative signs of \(Y-Xr\) along a circular arc, or the whole-circle
lower support. The latter radical is bounded by the global identity

\[
\frac{5t+15V/t-5V^2/t^3+V^3/t^5}{16}-\sqrt V
=\frac{(\sqrt V-t)^4(V+4t\sqrt V+5t^2)}{16t^5}\ge0
\quad(t>0,V\ge0).                                \tag{9}
\]

On the row's fixed angle interval \(\phi=k\pi/2+r x\),
\(0\le x\le7/10\), the charge is exactly
\(\beta_i(\sin x+\cos x-1)/2\). Alternating Taylor inequalities
give rational lower coefficient polynomials for (8) and for all support
premises. Their exact Bernstein coefficients on the declared rational
interval are nonnegative for premises and strictly positive for costs.

The complete accepted input has **129,031 fixed rows**,
**354,720 premise and cost polynomials**, and **2,961,120 coefficient
bounds**. Every cost is strict; the least printed strict cost coefficient is

\[
\frac{642432521}{100000000000000}>0.                \tag{10}
\]

The physical center-gap enclosure and outward arctangent/pi brackets give
the same complete necessary angle domain as in the uncharged hand kernel.
All **121,808 original-axis angle chains** are covered, with zero coverage
errors. Thus (6) holds for every currently possible separator before any
owner is eliminated. The table is a fixed mathematical input. Its
discovery fits and refinements are not premises of the proof.

## 3. A strict cyclic contraction

On \([0,7/10]\),
\(h(x)=(\sin x+\cos x-1)/2\) is concave, vanishes at zero, and
satisfies

\[
h(7/10)>\frac{29}{100}\frac7{10}.
\]

The displayed Taylor comparison is one of the fixed exact comparisons
in the independently reviewed
`HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md`. Its endpoint chord proves

\[
h(x)\ge\frac{29}{100}x\qquad(0\le x\le7/10).
\tag{11}
\]

The function h is even and has period \(\pi/2\), so
\(h(\phi_i)=h(|d_i|)\). Sum (6) using one consistent label per
vertex. The labels cancel and \(\sum_i\phi_i=\sum_i\delta_i=2\pi\).
Consequently

\[
2\pi>7\gamma+\beta\sum_{i\in I}h(|d_i|)
\ge7\gamma+\beta\frac{29}{100}S.                  \tag{12}
\]

But the following exact rational reserve is positive:

\[
7\frac{89727}{100000}
+\frac{99}{5000}\frac{29}{100}\frac25
-\frac{710}{113}
=\frac{271}{282500000}>0.                          \tag{13}
\]

If \(S\ge2/5\), (12)--(13) would give
\(2\pi>710/113>2\pi\), a contradiction. This proves (3).

## 4. Immediate owner consequence and remaining premises

The same independently reviewed bootstrap theorem now applies to each
zero-quarter edge \(H\to G\), \(A\to B\), and \(T\to D\).
Its containment/core bounds imply that either primary margin 2 or 4 is
at most

\[
.915-1.05875\cos x+.05875\sin x
\le-\frac{711}{20000}<0\qquad(|x|\le2/5).
\]

Thus those three edges must use original axes 1 or 3. This consequence
is obtained after the full four-axis proof of (6), so there is no circular
owner assumption. Stronger tangent signs for A/B, smaller mismatch,
the quarter-edge owners and the terminal tilt interval are subsequent
gates.

## 5. Frozen reconstruction

`CANDIDATE_COARSE_MISMATCH_HAND_COMPACT_REPORT.json` retains every
polynomial degree and an exact lower bound for every Bernstein coefficient.
`python replay_candidate_coarse_mismatch_hand.py` reconstructs the full
coefficient output and compares every compact record and frozen hash.
The full-output SHA-256 is

```
9e44e1fe7a0df8c7f2f4e7203a2c5f5f154fd07322852574539ccddb6df19b11
```

The verifier is the independently reviewed conditional kernel with hash
`6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697`.
The separate candidate-specific independent review and manifest bind the
full state/angle union, the charge convention and the strict contraction.
