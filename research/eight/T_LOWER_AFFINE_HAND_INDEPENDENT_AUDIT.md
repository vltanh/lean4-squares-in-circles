# Independent audit of the lower T hand exclusion

**Result: PASS.** The complete fixed table excludes
\(u_T\le1/20\) under the previously proved G bounds and the normalization
\(u_E\le0\). This review independently checks its state and angle domains,
the exact cyclic contradiction, and the binding to the approved continuous
support kernel. It does not use the discovery optimizer.

## 1. Exact scope and inputs

The squared radius is \(Q=3915534138/10^9\), and the quarter word is
\((0,1,0,1,0,1,1)\), with roles \((H,G,A,B,T,D,E)\). The excluded closed
domain is

\[
u_G\in[-4/5,-1/20],\qquad u_T\in[-1,1/20],\qquad u_E\in[-1,0].
\]

Every other role ranges through its full canonical tangent interval.
Both the outer-circle and core-avoidance boundary kinds are included at
every role. The **303 declared closed arcs** cover all **24 nonempty
role/kind/sign domains**. Core side and corner intervals meet at the exact
junction \(6/7\); no side is treated as a circular corner. At a zero
tangent one containing sign representation is chosen consistently on both
incident edges.

The fixed data hash is

```
d09d5eed09b0297139d13be0506fd108df3b34f27048670fd7f10b916d6b6dd3
```

All seven thresholds are the exact rational \(\gamma=561/625=.8976\).
There is no mismatch charge or additional frame or owner restriction.
The physical hypotheses remain the established center gaps
\(\delta_i>19/25\), total gap \(2\pi\), and
\(|\phi_i-k_i\pi/2|<7/10\).

## 2. Independent reconstruction of the domain cover

`audit_T_lower_hand_assembly_independently.py` imports neither the
JavaScript verifier nor any discovery routine. It recomputes the closed
state unions using fractions. It brackets every endpoint arctangent by
an independent rational half-angle calculation and alternating sums, and
brackets pi by Machin's identity. On each ordered pair of arcs it forms

\[
[19/25-\alpha_s^{\max}+\alpha_t^{\min},\;
710/113-114/25-\alpha_s^{\min}+\alpha_t^{\max}],
\]

then intersects this physical angle enclosure with both closed halves of
\(k_i\pi/2+[-7/10,7/10]\). All four **original directed axes** are
enumerated separately. The independent closed-union check passes for
all **47,168 required angle chains**, including endpoints and shared arc
boundaries.

The checker also validates all source/target role indices, quarter
increments, half-angle signs, nonnegative SAT multipliers, rational
labels, positive radical-majorant parameters, and each declared support
rule. Every row threshold is at least the corresponding cyclic threshold.

## 3. Continuous inequalities and exact arithmetic

The frozen verifier is byte identical to the independently reviewed kernel

```
1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee
```

The complete support argument and its independent review are
`AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md` and
`AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md`. For an actual feasible separator,
subtracting its nonnegative margin times the declared nonnegative
multiplier gives a lower bound for \(\phi+L_s-L_t-\gamma\). Endpoint,
monotonicity, and circular support rules eliminate both state variables.
The displayed sixth-degree radical majorant and Taylor inequalities then
reduce each row to fixed rational polynomial coefficients. Positivity of
the Bernstein coefficients proves the whole scalar interval, rather than
only its sample points.

All **49,971 rows** pass. Their **132,139 premise and cost polynomials**
contain **857,343 coefficient bounds**. Every premise bound is nonnegative,
and every cost bound is strictly positive. The smallest printed strict
cost coefficient is

\[
\frac{1649411}{3125000000000}>0.
\]

The independent assembly recomputes these record counts and signs and
checks the frozen source and full-output hashes. The full coefficient
output has SHA-256

```
955d268b626f278059698cbe6c08ec90076c0260bd6b696925b1fff71349cd74
```

The compact report and deterministic replay retain every polynomial's
degree and a rational lower bound for all its Bernstein coefficients.

## 4. The cyclic contradiction and its consequence

Choose a containing arc once at each vertex, and use its same affine label
on both incident edges. For each edge choose any actually feasible
retained separator. The complete cover and strict scalar inequalities give

\[
2\pi=\sum_i(\phi_i+L_i-L_{i+1})
>7\gamma=\frac{3927}{625}
=\frac{710}{113}+\frac1{70625}>2\pi.
\]

This contradiction proves the claimed lower T exclusion. Together with
the independently reviewed upper T theorem it gives
\(1/20<u_T<4/5\) on every normalized surviving boundary candidate.
The result is a tangent statement about that boundary representative;
the existing frame-preserving and radius-monotonicity interfaces govern
its later use. No original-center tangent preservation is assumed.

The exact independent audit output is
`T_LOWER_AFFINE_HAND_INDEPENDENT_ASSEMBLY.json`. Candidate mismatch,
contact-owner and tilt capture are separate remaining gates.
