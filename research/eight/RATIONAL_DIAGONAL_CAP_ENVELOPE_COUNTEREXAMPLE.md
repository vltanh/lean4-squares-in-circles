# Exact diagonal-square obstruction to extending the sharp cap envelope down to 7/24

Research continuation 2026-10-12. **This is a genuine single-square
counterexample**, not an eight-square packing.

The arbitrary-frame sharp whole-cap center envelope
\[
R^2\ge(1+h)^2+(|y|+1/2)^2
\]
proved previously for \(h\ge37/100\) at
\(R^2\le q_+=9789/2500\), **cannot simply be extended to all**
\(h\ge7/24\). The actual failed hypotheses are below.

## Rational offset, exact diagonal frame, and true vertices

Let
\[
h=\frac{293}{1000}=\frac7{24}+\frac1{750},\quad
u=\frac{\sqrt2}{2},\quad
p=(h+u,1).
\]
Use the genuinely orthonormal unit-square frame
\[
e=(u,u),\qquad f=(u,-u).
\]
The square \(S=\{p+(se+tf)/2:|s|,|t|\le1\}\)
has four actual vertices
\[
(h,1),\quad(h+\sqrt2,1),\quad
(h+u,1+u),\quad(h+u,1-u).
\]
Every vertex satisfies \(x\ge h>7/24\), so the
**whole genuine rotated unit square** lies in
the stated outward cap.

The maximum squared true-vertex norm is at most
the maximum of
\[
q_{\rm right}=h^2+3+2h\sqrt2,\qquad
q_{\rm top}=h^2+2+(h+1)\sqrt2.
\]
The left/bottom vertices have still smaller norms.
The elementary rational radical bound
\[
\sqrt2<99/70,\qquad (99/70)^2>2,
\]
gives **strict exact disk margins**
\[
q_+-q_{\rm right}>
\frac{6857}{7000000}>0,\qquad
q_+-q_{\rm top}>
\frac{7557}{7000000}>0.
\]
Thus all four actual true-square vertices fit inside
\(D_{\sqrt{q_+}}\) with positive slack.

However, the **axis-parallel candidate envelope** at
the same whole-cap offset and *actual* y-center \(y=1\)
would require
\[
R^2\ge(1+h)^2+(1+1/2)^2
=\frac{3921849}{1000000}
=q_++\frac{6249}{1000000}>q_+.
\]
This is false for the valid rotated square above.

Every displayed statement has a **rational arithmetic
certificate**, including the radical comparisons, in
[verify_diagonal_cap_envelope_counterexample.py](verify_diagonal_cap_envelope_counterexample.py).

## What this establishes (and does not establish)

The sharp one-square envelope is **false at the exact offset
293/1000**, which is itself strictly above \(7/24\).
Consequently a proof of the S2/k4 low-offset cell C **cannot**
blindly extend the one-square envelope to \(h=7/24\).

The example's square center has norm \(>1\), so this does
**not** invalidate a hypothetical *two-square* mixed
inner/outer cap obstruction, and certainly does not furnish
an eight-square counterexample. It does not challenge
the already-proved \(h\ge37/100\) theorem.

The next constructive task is to seek an **intermediate
provable lower threshold** using the full disk radius ceiling,
then separately tackle \(7/24<h\) below it with genuine
two-square separating-axis constraints and its inner-center
hypothesis. No unrestricted \(R_8\ge\widehat R\) result
is claimed here.
