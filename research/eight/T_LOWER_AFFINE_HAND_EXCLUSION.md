# Candidate word: exclusion of the lower T tangent domain

## 1. The closed gate

Put

\[
 Q=3.915534138=\frac{3915534138}{10^9},
 \qquad \gamma=.8976=\frac{561}{625}.
\]

Use the cyclic roles and quarter word

\[
 (H,G,A,B,T,D,E),\qquad k=(0,1,0,1,0,1,1).
\]

Every vertex may independently be a core or outer boundary state. Assume
the established center-order and frame-concentration hypotheses

\[
 \sum_i\delta_i=2\pi,\qquad \delta_i>19/25,\qquad
 \phi_i=\delta_i+\alpha_{i+1}-\alpha_i
       \in k_i\pi/2+[-7/10,7/10],                         \tag{1}
\]

and actual adjacent-square separation. Set \(u_i=\tan\alpha_i\),
with \(-1\le u_i\le1\).

**Theorem.** No such boundary cycle satisfies all three closed restrictions

\[
 -\frac45\le u_G\le-\frac1{20},\qquad
 -1\le u_T\le\frac1{20},\qquad -1\le u_E\le0.           \tag{2}
\]

The already proved two G exclusions and the reflection normalization
give the first and third restrictions for a surviving candidate cycle.
Consequently this theorem gives the next necessary bound
\(u_T>1/20\). It does not require the separate T-upper exclusion.

All \(2^7\) radial-kind choices and all retained SAT owners are included.
The conclusion is about the boundary representative. Application to an
original packing uses the previously proved boundary-reduction and
outer-radius monotonicity interfaces; no preservation of a center's
tangent during the initial boundary deformation is assumed here.

## 2. Exact state arcs and markers

Write each own-frame center as \((a,-\sigma b)\), where
\(0\le b\le a\), \(v=b/a\in[0,1]\), and
\(\sigma\in\{-1,1\}\). Then \(u=\sigma v\) and
\(\alpha=\sigma\arctan v\). The two boundary types are

\[
\begin{array}{ll}
 O:&(a+1/2)^2+(b+1/2)^2=Q,\\
 C:&a=7/12\quad(0\le v\le6/7),\\
   &(a-1/2)^2+(b-1/2)^2=1/144\quad(6/7\le v\le1).
\end{array}                                                     \tag{3}
\]

`T_LOWER_AFFINE_HAND_DATA.json` is the complete rational table. Its
303 closed arcs cover the 24 nonempty role/kind/sign domains under (2).
Each arc records its role, kind, sign, two rational tangent endpoints
and three rational coefficients \((c,p,q)\). Its marker is

\[
                         L=c+pa+qb.                              \tag{4}
\]

The sign is already reflected in the choice of the arc's coefficients;
there is no additional sign multiplying (4). Every core arc is wholly
on a side or wholly on a corner. In particular the exact transition
\(6/7\) is retained. There is no gap between consecutive closed arcs.

At a shared endpoint the two formulas may differ. Choose one containing
arc for each vertex once, and use that marker on both incident edges.
The pair table includes every choice of containing source and target
arc. Thus the markers telescope without needing continuity at a cut.

## 3. The continuous pair inequalities

For source \((a,-\sigma b)\), target
\(R_\phi(A,-\tau B)\), and
\(W=(1+|\sin\phi|+|\cos\phi|)/2\), the four retained SAT margins are

\[
\begin{array}{ll}
 M_1=\sigma b+A\sin\phi-\tau B\cos\phi-W,&
 M_2=A-a\cos\phi+\sigma b\sin\phi-W,\\
 M_3=a\sin\phi+\sigma b\cos\phi-\tau B-W,&
 M_4=a-A\cos\phi-\tau B\sin\phi-W.
\end{array}                                                     \tag{5}
\]

The common-point axis-elimination theorem supplies a nonnegative margin
from this list for every separated adjacent pair in the present scope.
Each fixed table row supplies a nonnegative rational multiplier
\(\lambda\) and proves

\[
 \phi+L_s-L_t-\gamma-\lambda M_j>0                 \tag{6}
\]

for the complete source arc, complete target arc, and declared angle
interval. Since \(M_j\ge0\), this implies
\(\phi+L_s-L_t>\gamma\).

The elementary proof of (6) is the shared affine-arc support kernel.
Subtracting \(\lambda M_j\) separates the two state coordinates.
Reflection and reversal reduce axes 2 and 3 to axes 4 and 1 by replacing
the marker pair with \((-L_t,-L_s)\) and reversing both signs.
The angle and pair cost are preserved.

For either normalized axis, each state minimum is the support of a
linear function \(Xa+Yb\) on one arc of (3). The following four rules
exhaust the modes used by the table:

- A straight core side has its minimum at an endpoint.
- On a circular arc, \(X\ge0\) makes the function concave, so its
  minimum is at an endpoint.
- With \(a'=-r\) and \(r\) increasing, the derivative \(Y-Xr\)
  has one sign throughout if it has that sign at both endpoints.
  This gives the lower or upper endpoint rule.
- Enlarging a circular arc with center \((h_0,h_0)\) and radius
  \(R_0\) to its full circle gives
  \[
  Xa+Yb\ge h_0(X+Y)-R_0\sqrt{X^2+Y^2}.              \tag{7}
  \]

The source coefficients in (6) are constant in the angle; its lower
support is computed exactly. The target mode is declared in the row,
and the endpoint or derivative premises are proved on the entire angle
interval. A straight core side is never treated as a circular corner.

For a target-circle row the input gives a positive rational \(h\).
The identity

\[
 \begin{split}
 T_h(V)&=\frac{5h+15V/h-5V^2/h^3+V^3/h^5}{16},\\
 T_h(V)-\sqrt V
 &=\frac{(\sqrt V-h)^4(V+4h\sqrt V+5h^2)}{16h^5}\ge0
 \end{split}                                                    \tag{8}
\]

is global for \(V\ge0\). Here \(V=X^2+Y^2\). Substituting (8)
into the lower support leaves an explicit polynomial expression in
\(\phi,\sin\phi,\cos\phi\). No remaining minimization over either
state coordinate is assumed.

## 4. Fixed rational polynomial evidence

Write each row's angle as \(\phi=k\pi/2+r x\), with \(r=\pm1\)
and a fixed rational interval inside \(0\le x\le.7\).
The alternating Taylor bounds are

\[
\begin{split}
 \sin x&=x-x^3/6+x^5/120-x^7/5040+\eta x^9/9!,\\
 \cos x&=1-x^2/2+x^4/24-x^6/720+x^8/40320-\zeta x^{10}/10!,
 \qquad0\le\eta,\zeta\le1.
\end{split}                                                     \tag{9}
\]

Rational interval arithmetic on coefficients yields a pointwise lower
polynomial because \(x\ge0\). The error parameters may vary with
\(x\); no derivative of a Taylor remainder is taken. On each fixed
interval, the ordinary change of variable to \([0,1]\) and the exact
power-to-Bernstein identity give rational Bernstein coefficients.
Nonnegative coefficients prove each premise; strictly positive
coefficients prove (6).

The complete fixed table has:

| Object | Count |
|---|---:|
| Closed state arcs | 303 |
| Nonempty required angle chains | 47,168 |
| Fixed one-angle rows | 49,971 |
| Premise and cost polynomials | 132,139 |
| Nonnegative coefficient lower bounds | 857,343 |

Every cost polynomial has a strictly positive coefficient lower bound.
The smallest printed cost lower bound is

\[
                   \frac{1649411}{3125000000000}>0.              \tag{10}
\]

`T_LOWER_AFFINE_HAND_COMPACT_REPORT.json` records each row's premise
and cost polynomial degrees and a lower bound for all their coefficients.
The full coefficient lists are uniquely reproduced from the rational
input and frozen verifier. The full output is bound by SHA-256

```
955d268b626f278059698cbe6c08ec90076c0260bd6b696925b1fff71349cd74
```

This is a large finite polynomial table. Its proof mechanism is the
continuous support calculation (6)--(8) followed by the elementary
polynomial argument (9). The verification contains no numerical
optimizer and no adaptive subdivision process.

## 5. Complete angle cover and the cyclic contradiction

Since the other six center gaps exceed \(19/25\), every edge satisfies

\[
 \frac{19}{25}<\delta_i<\frac{710}{113}-\frac{114}{25}.           \tag{11}
\]

If a source arc has \(\alpha_s\in[s_-,s_+]\) and a target arc has
\(\alpha_t\in[t_-,t_+]\), its full required angle range is contained in

\[
 \left[\frac{19}{25}-s_++t_-,\,
       \frac{710}{113}-\frac{114}{25}-s_-+t_+\right]
 \cap \left(k\pi/2+[-.7,.7]\right).                            \tag{12}
\]

Directed rational bounds for the endpoint arctangents and \(\pi\)
give explicit outward intervals on both half-angle branches. All 47,168
original source-arc/target-arc/axis/half chains have complete closed
interval covers. Every original axis is checked before normalization.
The separate Python assembly audit recomputes the arctangent intervals
using a different rational root mesh and verifies these unions again.

Choose containing arcs once for the seven vertices. For each adjacent
pair choose an axis with \(M_j\ge0\). Its row gives the strict pair
bound. Summing and using both telescoping identities yields

\[
 2\pi=\sum_i\phi_i=\sum_i(\phi_i+L_i-L_{i+1})
      >7\gamma=\frac{3927}{625}.                               \tag{13}
\]

But

\[
 \frac{3927}{625}-\frac{710}{113}=\frac1{70625}>0,
 \qquad 2\pi<\frac{710}{113}.                                  \tag{14}
\]

This contradiction proves the theorem and closes the lower-T domain.

## 6. Reproduction and immutable inputs

The frozen verifier is byte-identical to the independently reviewed
affine-arc kernel, with SHA-256

```
1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee
```

From this directory, run

```sh
python replay_T_lower_hand.py
python audit_T_lower_hand_assembly.py
python audit_T_lower_hand_assembly_independently.py
```

The first command reconstructs the complete arithmetic output and checks
its recorded hash and every compact record. Add `--save-full` to retain
the optional full coefficient report. The second independently checks
the rational state and angle unions, scope, data bindings and cyclic
reserve. It works with the compact report alone. The third command is the
separate reviewer's domain reconstruction. Its complete independent
continuous and assembly review is recorded as PASS in
`T_LOWER_AFFINE_HAND_INDEPENDENT_AUDIT.md`.

`T_LOWER_AFFINE_HAND_MANIFEST.json` binds the immutable proof files.
No discovery fit, failed proposal or intermediate refinement is a
theorem premise or part of that manifest.
