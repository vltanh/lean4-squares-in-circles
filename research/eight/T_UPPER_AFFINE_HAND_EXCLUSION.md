# Candidate word: exclusion of the upper T tangent domain

## Theorem

Put

\[
Q=\frac{3915534138}{10^9},\qquad
\gamma=\frac{8977}{10000}.
\]

Consider a boundary seven-cycle with roles \((H,G,A,B,T,D,E)\),
quarter word \(k=(0,1,0,1,0,1,1)\), and the established hand hypotheses

\[
\sum_i\delta_i=2\pi,\quad \delta_i>19/25,\quad
\phi_i=\delta_i+\alpha_{i+1}-\alpha_i
\in k_i\pi/2+[-7/10,7/10].
\tag{1}
\]

Every adjacent pair has a retained nonnegative signed SAT margin. Each
vertex may independently be on the outer-circle boundary or the
radius-1/12 core-avoidance boundary.

There is no such cycle with

\[
u_G\in[-4/5,-1/20],\qquad u_T\in[4/5,1],\qquad u_E\in[-1,0].
\tag{2}
\]

The already proved lower and upper G exclusions supply the first
restriction for every surviving candidate cycle after the normalization
\(u_E\le0\). Thus this theorem proves the strict conclusion

\[
                              u_T<4/5.
\tag{3}
\]

The theorem does not assume a lower bound on T, the desired contact
owners, or a tighter frame bound. It concerns a boundary representative.
The frame-preserving boundary theorem and the outer-radius monotonicity
interface are retained when it is used in the unrestricted proof.

## 1. Explicit state and scalar inputs

Write a canonical state as \((a,-\sigma b)\), with
\(v=b/a\in[0,1]\), \(\sigma\in\{-1,1\}\), and
\(u=\sigma v\), \(\alpha=\sigma\arctan v\). The two curves are

\[
\begin{array}{ll}
O:&(a+1/2)^2+(b+1/2)^2=Q,\\
C:&a=7/12\quad(0\le v\le6/7),\\
  &(a-1/2)^2+(b-1/2)^2=1/144\quad(6/7\le v\le1).
\end{array}
\tag{4}
\]

`T_UPPER_AFFINE_HAND_DATA.json` declares **102 closed arcs**, with exact
rational endpoints and rational affine labels \(L=c+pa+qb\). They cover
all **22 nonempty role/kind/sign domains** allowed by (2). Every core arc
is confined to its side or corner, with the exact junction 6/7 retained.

The same input contains **7,078 fixed scalar rows**. Each declares its
original edge, source arc, target arc, one of all four retained signed
axes, angle half \(\phi=k\pi/2+r x\), rational interval
\(x\in[l,h]\subset[0,7/10]\), nonnegative rational SAT multiplier,
and an explicit source/target support rule. Circle-support rows also
declare their positive rational radical-majorant parameter.

The table is an immutable mathematical input. Its discovery fits and
provisional versions are not premises.

## 2. Continuous reduction to the fixed polynomial inequalities

Apply the hand theorem in `AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md`, whose
complete continuous argument and exact kernel have the independent review
`AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md`. Its relevant steps are recalled
here to specify the implication being invoked.

For source \((a,-\sigma b)\), target \(R_\phi(A,-\tau B)\), and
\(W=(1+|\sin\phi|+|\cos\phi|)/2\), the margins are

\[
\begin{aligned}
M_1&=\sigma b+A\sin\phi-\tau B\cos\phi-W,\\
M_2&=A-a\cos\phi+\sigma b\sin\phi-W,\\
M_3&=a\sin\phi+\sigma b\cos\phi-\tau B-W,\\
M_4&=a-A\cos\phi-\tau B\sin\phi-W.
\end{aligned}
\tag{5}
\]

If \(M_j\ge0\), the row's \(\lambda\ge0\) gives

\[
\phi+L_s-L_t-\gamma
\ge\phi+L_s-L_t-\gamma-\lambda M_j.
\tag{6}
\]

The right side separates into affine functions of the two state
coordinates and a function of the angle. Reflection and reversal
normalize axes 2 and 3 to source axes 4 and 1 without changing the angle
or cost. The source coordinate coefficients are then constant.

An affine function on a straight side has its minimum at an endpoint.
On a circular arc \(a=h_0+\sqrt{R_0^2-(b-h_0)^2}\), its derivative
is \(Y-Xr\), where \(r=(b-h_0)/(a-h_0)\) increases. Its two endpoint
signs justify the declared monotone support rules. If \(X\ge0\),
concavity supplies an endpoint minimum. Otherwise enlargement to the
whole circle gives the unconditional lower support

\[
              h_0(X+Y)-R_0\sqrt{X^2+Y^2}.
\tag{7}
\]

Every needed derivative sign is proved by that row's premise
polynomials. A straight side is never enlarged to a circular corner.
For \(V=X^2+Y^2\), the last radical is removed by

\[
\frac{5h+15V/h-5V^2/h^3+V^3/h^5}{16}-\sqrt V
=\frac{(\sqrt V-h)^4(V+4h\sqrt V+5h^2)}{16h^5}\ge0.
\tag{8}
\]

The familiar alternating bounds \(S_7\le\sin x\le S_9\) and
\(C_{10}\le\cos x\le C_8\), on \([0,7/10]\), give rational
coefficient intervals for the result. Taking lower coefficient endpoints
gives a pointwise lower polynomial because x is nonnegative. Its
Bernstein coefficients on the fixed interval \([l,h]\) are nonnegative
for every support premise and strictly positive for every cost.

All **19,711** premise and cost polynomials pass, comprising **147,771**
coefficient bounds. The least printed strict cost coefficient is

\[
                       \frac{768927349}{50000000000000}>0.
\tag{9}
\]

Thus each declared row proves \(\phi+L_s-L_t>\gamma\) on its entire
state/angle domain, whenever its selected original separator is feasible.
No optimizer or adaptive verification process is used in this implication.

## 3. Complete domain unions and the cyclic contradiction

The physical center gaps also satisfy
\(\delta_i<710/113-114/25\). For source and target arc angle ranges
\([s_-,s_+]\) and \([t_-,t_+]\), respectively, every relevant \(\phi\)
lies in

\[
\left[19/25-s_++t_-,\;710/113-114/25-s_-+t_+\right]
\cap\left(k\pi/2+[-7/10,7/10]\right).
\tag{10}
\]

The frozen verifier encloses the endpoint arctangents by the half-angle
identity and alternating sums, encloses pi by Machin's formula, and
checks every closed interval union. All **6,452** nonempty original
source-arc/target-arc/axis/angle-half chains are covered. Both radial kinds,
every allowed sign, every arc endpoint, and all original axes are included.

Choose one containing arc once for each vertex of a hypothetical cycle.
Use the chosen label on both incident edges. This convention handles any
piecewise label jump without changing the telescoping sum. On each edge
choose an actual nonnegative margin from (5). By the complete table,

\[
2\pi=\sum_i(\phi_i+L_i-L_{i+1})
>7\gamma=\frac{62839}{10000}
=\frac{710}{113}+\frac{807}{1130000}>2\pi.
\]

The contradiction proves (2) impossible and establishes (3).

## 4. Reproduction and audit binding

`T_UPPER_AFFINE_HAND_COMPACT_REPORT.json` records each polynomial degree
and a lower bound for every one of its Bernstein coefficients. The full
coefficient output is reconstructed by `python replay_T_upper_hand.py`.
Its SHA-256 is

```
f43ecf10d0543acb7417c881dd4068b850caa2399de40397082265f00f3ac186
```

The replay checks the input and frozen-kernel hashes, the full output hash,
and every compact record. The optional `--save-full` flag writes the full
output. The kernel source is exactly the independently reviewed
`1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee`.

The author replay and full domain verifier pass. The independent review
`T_UPPER_AFFINE_HAND_INDEPENDENT_AUDIT.md` also passes. Its checker
`audit_T_upper_hand_assembly_independently.py` reconstructs all 22 state
unions and 6,452 angle chains with independent rational arctangent bounds,
checks the exact scope and hashes, and verifies the cyclic contradiction.
The manifest `T_UPPER_AFFINE_HAND_MANIFEST.json` binds these files.
This theorem alone does not supply T's lower bound or the remaining
mismatch, owner and tilt capture.
