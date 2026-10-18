# Candidate word: exclusion of the lower H tangent domain

## 1. The theorem and its prerequisites

Let

\[
Q=\frac{3915534138}{10^9},\qquad
\gamma=\frac{8977}{10000},\qquad
k=(0,1,0,1,0,1,1).
\]

Use the cyclic roles \((H,G,A,B,T,D,E)\). Consider any boundary
seven-cycle at squared radius Q, with each state independently on the
outer-circle boundary or the radius-1/12 core-avoidance boundary. Assume
the proved physical center-gap and frame hypotheses

\[
\sum_i\delta_i=2\pi,\qquad \delta_i>19/25,\qquad
\phi_i=\delta_i+\alpha_{i+1}-\alpha_i
\in k_i\pi/2+[-7/10,7/10],
\]

and an actually feasible retained SAT separator on every adjacent pair.

**Theorem.** No such cycle satisfies

\[
u_H\in[-1,1/2],\quad u_G\in[-4/5,-1/20],\quad
u_T\in[1/20,4/5],\quad u_E\in[-1,0].                 \tag{1}
\]

The reflection normalization and the four independently reviewed G/T
tangent theorems supply the last three conditions for every surviving
candidate. Consequently every such normalized candidate has

\[
u_H>1/2.                                             \tag{2}
\]

This proof assumes no D bound, smaller frame mismatch, or selected contact
owners. Its conclusion concerns a boundary representative. Its use for
arbitrary original squares retains the established fixed-frame boundary
reduction and outer-radius monotonicity interfaces.

## 2. State curves and affine labels

An unsigned state has coordinates \((a,b)\), \(0\le b\le a\),
and tangent \(v=b/a\in[0,1]\). With sign \(\sigma\), its actual
own-frame center is \((a,-\sigma b)\), so
\(u=\sigma v\) and \(\alpha=\sigma\arctan v\). The curves are

\[
\begin{array}{ll}
O:&(a+1/2)^2+(b+1/2)^2=Q,\\
C:&a=7/12\quad(0\le v\le6/7),\\
 &(a-1/2)^2+(b-1/2)^2=1/144\quad(6/7\le v\le1).
\end{array}                                         \tag{3}
\]

`H_LOWER_AFFINE_HAND_DATA.json` contains **279 closed state arcs**.
Their exact rational endpoints cover all **22 nonempty role/kind/sign
domains** under (1). A core arc stays on its side or corner; the exact
junction 6/7 is included from both sides.

Every arc declares a rational affine label \(L=c+pa+qb\).
Its sign is encoded in the arc and its coefficients; there is no further
sign multiplier on L. At a shared endpoint choose one containing arc
once for that vertex and use its same label on both adjacent edges.
The proof covers every such choice, so discontinuous label values at an
arc endpoint do not disturb the final telescoping sum.

## 3. The complete continuous pair bound

For source \((a,-\sigma b)\), target \(R_\phi(A,-\tau B)\), put
\(W=(1+|\sin\phi|+|\cos\phi|)/2\). The four retained margins are

\[
\begin{aligned}
M_1&=\sigma b+A\sin\phi-\tau B\cos\phi-W,\\
M_2&=A-a\cos\phi+\sigma b\sin\phi-W,\\
M_3&=a\sin\phi+\sigma b\cos\phi-\tau B-W,\\
M_4&=a-A\cos\phi-\tau B\sin\phi-W.
\end{aligned}                                       \tag{4}
\]

Every fixed row declares an original edge and axis, its two complete
state arcs, a rational angle interval, and a rational \(\lambda\ge0\).
It proves on that whole domain that

\[
\phi+L_s-L_t-\gamma-\lambda M_j>0.                  \tag{5}
\]

Whenever that separator is feasible, (5) gives
\(\phi+L_s-L_t>\gamma\).

Here is the continuous argument behind every row. The complete proof and
its independent review are `AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md` and
`AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md`.

Subtracting \(\lambda M_j\) separates the source and target coordinate
functions. Reflection and reversal normalize axes 2 and 3 to axes 4 and 1,
with label pair \((-L_t,-L_s)\), leaving the angle and cost unchanged.
The normalized source coefficients are constant in the angle.

An affine function on a straight core side is minimized at an endpoint.
On a circular arc write its derivative as \(Y-Xr\), where
\(r=(b-h_0)/(a-h_0)\) increases along the arc. Its endpoint signs prove
the declared monotone support rules. When \(X\ge0\), concavity gives
an endpoint minimum. An unconditional remaining lower support is

\[
Xa+Yb\ge h_0(X+Y)-R_0\sqrt{X^2+Y^2}.               \tag{6}
\]

This enlargement is used only for circular arcs. A declared positive
rational h eliminates the target radical by

\[
\frac{5h+15V/h-5V^2/h^3+V^3/h^5}{16}-\sqrt V
=\frac{(\sqrt V-h)^4(V+4h\sqrt V+5h^2)}{16h^5}\ge0.
                                                               \tag{7}
\]

Write \(\phi=k\pi/2+r x\), with \(r=\pm1\) and
\(0\le x\le7/10\). Alternating Taylor bounds
\(S_7(x)\le\sin x\le S_9(x)\) and
\(C_{10}(x)\le\cos x\le C_8(x)\) give rational coefficient
intervals in (5)--(7). Lower coefficient endpoints give a pointwise lower
polynomial, since x is nonnegative. The exact power-to-Bernstein identity
on the row's fixed interval proves each support premise by nonnegative
coefficients and each cost by strictly positive coefficients.

All **48,050 fixed rows** pass. Their **126,530 premise and cost
polynomials** have **860,259 coefficient bounds**. The least printed
strict cost coefficient is

\[
\frac{1122836547}{100000000000000}>0.                 \tag{8}
\]

The verifier contains no search or adaptive subdivision. Proposed rows
were refined during discovery; only the frozen fixed table is a premise.

## 4. Complete angle unions and contradiction

The other six positive center gaps give
\(\delta_i<710/113-114/25\). For arc angle ranges
\([s_-,s_+]\) and \([t_-,t_+]\), every necessary pair angle is in

\[
[19/25-s_++t_-,\;710/113-114/25-s_-+t_+]
\cap(k\pi/2+[-7/10,7/10]).                           \tag{9}
\]

The exact arctangent and pi brackets, followed by rational interval-union
checks, prove that all **45,560 nonempty original angle chains** are
covered. This includes every radial kind, sign, original axis, both
angle halves, and all endpoints. Thus one row supplies (5) for an actual
separator on each edge of a hypothetical cycle.

The labels cancel, and the angles telescope with the center gaps. Hence

\[
2\pi=\sum_i(\phi_i+L_i-L_{i+1})
>7\gamma=\frac{62839}{10000}
=\frac{710}{113}+\frac{807}{1130000}>2\pi,
\]

which is impossible. This proves (1) cannot occur and establishes (2).

## 5. Frozen evidence and review

`H_LOWER_AFFINE_HAND_COMPACT_REPORT.json` retains each polynomial's degree
and an exact rational lower bound for every Bernstein coefficient.
`python replay_H_lower_hand.py` reconstructs the full coefficients and
checks every compact record and every frozen hash. The full output hash is

```
de4a7e204de32faba3420dd85c57c90af1e847a36348cbd40a9c3bc9d83a4847
```

The kernel is byte identical to the independently reviewed source
`1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee`.
The independent review `H_LOWER_AFFINE_HAND_INDEPENDENT_AUDIT.md`
passes; it reconstructs every state and angle union and checks the complete
continuous implication. `H_LOWER_AFFINE_HAND_MANIFEST.json` binds the
fixed data, exact replay, compact records and completed review. Mismatch, D capture, contact owners and tilt remain
separate candidate gates.
