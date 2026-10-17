# Candidate word: exclusion of the lower G tangent domain

## Theorem and exact input

Let

\[
Q=\frac{3915534138}{10^9},\qquad
\gamma=\frac{8977}{10000},\qquad
(H,G,A,B,T,D,E)=(0,1,2,3,4,5,6).
\]

There is no boundary seven-cycle with quarter word
\(k=(0,1,0,1,0,1,1)\), the established center-order and frame hypotheses

\[
\sum_i\delta_i=2\pi,\quad \delta_i>19/25,\quad
\phi_i=\delta_i+\alpha_{i+1}-\alpha_i
\in k_i\pi/2+[-7/10,7/10],
\tag{1}
\]

adjacent-square separation, and

\[
u_G=\tan\alpha_G\in[-1,-4/5],\qquad u_E\in[-1,0].
\tag{2}
\]

Both radial kinds are included independently at every vertex. No contact
owner or additional sign restriction is assumed. The input radius is Q.
The usual outer-radius monotonicity interface permits the global proof to
use this exclusion at lower radii. The statement concerns a boundary
representative; it does not assert that the deformation preserves an
original center or its individual ray.

Together with `G_UPPER_AFFINE_HAND_EXCLUSION.md`, this theorem proves

\[
                 -4/5<u_G<-1/20
\tag{3}
\]

for every surviving candidate boundary cycle in the normalization
\(u_E\le0\). The reflection and reversal fixing E justify that normalization
in `CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md`.

## 1. Boundary geometry and piecewise affine labels

In a square's canonical frame its center is \((a,-\sigma b)\), where
\(0\le b\le a\), \(v=b/a\in[0,1]\), and \(\sigma\in\{-1,1\}\).
Thus \(\alpha=\sigma\arctan v\) and \(u=\sigma v\). The radial boundaries
are

\[
\begin{array}{ll}
O:&(a+1/2)^2+(b+1/2)^2=Q,\\
C:&a=7/12\quad(0\le v\le6/7),\\
  &(a-1/2)^2+(b-1/2)^2=1/144\quad(6/7\le v\le1).
\end{array}
\tag{4}
\]

The rational input `G_LOWER_AFFINE_HAND_DATA.json` declares 114 closed
subarcs of (4) covering all 24 nonempty role/kind/sign domains in (2).
Every core arc lies entirely on the straight side or entirely on its
circular corner. The exact transition is \(v=6/7\).

Each arc carries the rational affine label

\[
                       L=c+pa+qb.
\tag{5}
\]

The input's `arcs` array specifies its role, kind, sign, rational endpoints,
and the coefficients in (5). At a shared endpoint choose any containing
arc once for that vertex. Use its chosen label on both incident edges.
Every combination of containing source and target arcs is included in the
pair table, so labels telescope without requiring continuity across an
arc boundary.

## 2. Continuous support elimination

For a source \((a,-\sigma b)\) and target
\(R_\phi(A,-\tau B)\), put
\(W=(1+|\sin\phi|+|\cos\phi|)/2\). The four retained SAT margins are

\[
\begin{aligned}
M_1&=\sigma b+A\sin\phi-\tau B\cos\phi-W,\\
M_2&=A-a\cos\phi+\sigma b\sin\phi-W,\\
M_3&=a\sin\phi+\sigma b\cos\phi-\tau B-W,\\
M_4&=a-A\cos\phi-\tau B\sin\phi-W.
\end{aligned}
\tag{6}
\]

The common-point axis-elimination theorem ensures that separation supplies
at least one nonnegative margin in (6). For each original axis, the fixed
table supplies a rational \(\lambda\ge0\). Consequently

\[
\phi+L_s-L_t-\gamma
\ge \phi+L_s-L_t-\gamma-\lambda M_j
\quad\text{when }M_j\ge0.
\tag{7}
\]

The right side separates into a source affine function, a target affine
function, and a function of \(\phi\). Reflection and reversal reduce axes
2 and 3 to axes 4 and 1 by swapping the vertices, negating their signs,
and replacing the labels by \((-L_t,-L_s)\). Both the angle and the
quantity in (7) are preserved.

For the normalized axes 1 and 4, write the target label as
\(C+PA+TB\). The affine coefficients after subtracting \(\lambda M_j\)
are

| Axis | Source a | Source b | Target A | Target B |
|---|---|---|---|---|
| 1 | \(p\) | \(q-\lambda\sigma\) | \(-P-\lambda\sin\phi\) | \(-T+\lambda\tau\cos\phi\) |
| 4 | \(p-\lambda\) | \(q\) | \(-P+\lambda\cos\phi\) | \(-T+\lambda\tau\sin\phi\) |

All coordinate minima are removed by the following elementary facts. On
a circular arc write

\[
a=h_0+\sqrt{R_0^2-(b-h_0)^2},\quad
r(b)=\frac{b-h_0}{a-h_0},\quad a'(b)=-r(b),\quad r'(b)>0.
\]

For \(Xa+Yb\), if \(X\ge0\), concavity gives its minimum at one of the
two endpoints. A straight side has the same endpoint rule. If
\(Y-Xr\ge0\) at both endpoints, it is nonnegative throughout, so the
lower endpoint is a minimum; the reversed inequality gives the upper
endpoint. Finally, enlargement to the whole circle always gives

\[
Xa+Yb\ge h_0(X+Y)-R_0\sqrt{X^2+Y^2}.
\tag{8}
\]

The source coefficients are constant. A table row specifies one of these
four modes for the target, and proves every needed sign premise throughout
its angle interval. A straight core side is never replaced by a circle.

The only remaining radical in (8) is removed by the global identity, valid
for every \(V\ge0\) and rational \(h>0\),

\[
T_h(V)=\frac{5h+15V/h-5V^2/h^3+V^3/h^5}{16},\qquad
T_h(V)-\sqrt V=
\frac{(\sqrt V-h)^4(V+4h\sqrt V+5h^2)}{16h^5}\ge0.
\tag{9}
\]

Here \(V=X_t^2+Y_t^2\), so its nonnegativity is automatic. The positive
rational h is supplied in each circle row. After (8)–(9), only a function
of one real angle remains. These reductions apply to the entire declared
state arcs, including every interior point.

## 3. Fixed exact polynomial checks

Every row writes \(\phi=k\pi/2+r x\), with \(r\in\{-1,1\}\) and
\(0\le x\le7/10\). On this range use the alternating Taylor bounds

\[
\sin x=x-x^3/6+x^5/120-x^7/5040+\eta x^9/9!,\quad0\le\eta\le1,
\]
\[
\cos x=1-x^2/2+x^4/24-x^6/720+x^8/40320-\zeta x^{10}/10!,
\quad0\le\zeta\le1.
\tag{10}
\]

Rational interval arithmetic encloses each power coefficient after this
substitution. Since x is nonnegative, taking every coefficient's lower
endpoint yields a pointwise lower polynomial. No differentiation of a
Taylor remainder is used. On each fixed rational interval \([l,h]\), set
\(x=l+(h-l)t\) and express the polynomial as

\[
\sum_{j=0}^n B_j\binom nj t^j(1-t)^{n-j},\qquad0\le t\le1.
\tag{11}
\]

The coefficients \(B_j\) are exact rationals. Nonnegative coefficients
prove each support premise; strictly positive coefficients prove the
strict lower bound in (7). The frozen verifier performs only these
declared arithmetic operations and fixed interval unions. It performs no
search or adaptive subdivision.

All **9,087** declared rows pass. Their **25,221** premise and cost
polynomials contain **184,288** coefficient bounds. Every premise bound
is nonnegative and every cost bound is strictly positive. The least
printed strict cost coefficient is

\[
                 \frac{309500239}{10^{14}}>0.
\tag{12}
\]

`G_LOWER_AFFINE_HAND_COMPACT_REPORT.json` records each polynomial's degree
and a lower bound for every Bernstein coefficient, in input-row order.
The full coefficient lists are reproducible from the rational input and
the frozen verifier; their SHA-256 is

```
ae78b786aa819f912897937708cfe7fd299d20a701e56041357ba8411bf0dc79
```

This is a large finite one-angle polynomial table, with the continuous
coordinate eliminations proved above. Neither discovery fits nor failed
proposal tables are assumptions of the proof.

## 4. Exhaustive coverage and contradiction

From (1), every physical gap also satisfies
\(\delta_i<710/113-114/25\). If a source arc has
\(\alpha_s\in[s_-,s_+]\) and a target arc has
\(\alpha_t\in[t_-,t_+]\), every relevant angle belongs to

\[
\left[19/25-s_++t_-,\;710/113-114/25-s_-+t_+\right]
\cap\left(k\pi/2+[-7/10,7/10]\right).
\tag{13}
\]

The fixed verifier encloses each arctangent endpoint using the identity
\(\arctan v=2\arctan(v/(1+\sqrt{1+v^2}))\), rational square-root
brackets and alternating series. It encloses pi by Machin's formula and
alternating series. The resulting rational outer bounds make every
required union in (13) explicit.

There are **8,240** nonempty source-arc/target-arc/original-axis/angle-half
chains. Every one is covered by closed declared intervals. Together with
the complete state unions, this includes every original separating axis
and every state allowed by (2).

For a hypothetical seven-cycle, choose its containing arcs once and an
actual separating axis on each edge. The corresponding row gives
\(\phi_i+L_i-L_{i+1}>\gamma\). Summing yields

\[
2\pi=\sum_i(\phi_i+L_i-L_{i+1})
>7\gamma=\frac{62839}{10000}.
\]

But

\[
\frac{62839}{10000}-\frac{710}{113}
=\frac{807}{1130000}>0,\qquad 2\pi<\frac{710}{113},
\]

a contradiction. This proves the lower exclusion and, together with the
upper exclusion, the strict G bounds (3).

## Reproduction and review status

Run `python replay_G_lower_hand.py` beside the committed input and frozen
verifier. It regenerates the entire coefficient output, checks its hash,
and compares every compact record. The optional `--save-full` flag writes
the full output. The full report is a reproducible output, not a second
proof input.

The exact author replay and complete-domain verifier pass. The independent
audit in `G_LOWER_AFFINE_HAND_INDEPENDENT_AUDIT.md` also passes: it
reconstructs every state and angle union with independent rational
arctangent bounds and checks the input scope, hashes and cyclic reserve.
Its checker is `audit_G_lower_hand_assembly_independently.py`.
The continuous kernel is exactly the independently reviewed frozen kernel
used for the upper exclusion. The manifest
`G_LOWER_AFFINE_HAND_MANIFEST.json` binds these proof and audit files.
