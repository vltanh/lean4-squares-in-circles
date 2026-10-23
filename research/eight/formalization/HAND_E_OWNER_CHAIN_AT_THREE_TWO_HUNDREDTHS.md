# All feasible E owners are 0 or 1 already at S <= 3/200

## 1. Statement and dependency boundary

Assume the candidate frame with roles H,G,A,B,T,D,E, signed coordinates
`(+, -, +, -, +, -, -)` (the E sign may be weak), the G/T tangent cuts,
the H cut `b_H >= a_H/2`, the zero-owner restrictions, and the intended
BT/DE quarter-owner sets. Assume core avoidance and actual corner
containment at `q <= Q = 9789/2500`. Put A's physical frame at zero,
G's frame at t, and

\[
 S=|\theta_H-t|+|\theta_B|+|\theta_T-\theta_B|
       +|\theta_D-\theta_T|+|\theta_E-\theta_D|\le3/200.
\]

**Theorem.** Every originally feasible E-axis belongs to `{0,1}` in the
zero-based forward-axis numbering. This holds independently of which
original G-axis is feasible, including all separating ties.

This is a complete replacement, at the larger mismatch threshold, for
the E2/E3 exclusion in `HAND_MIXED_OWNER_CHAIN_BOUNDS.md`. It uses neither
mixed-owner capture nor a tilt window nor the old `S <= 1/1000`
contraction. It does not supply the earlier tangent cuts, quarter owners,
or mismatch contractions.

All terminating decimals below denote exact rationals. There is no state
or angle partition in this proof. Its eight alternatives are precisely
the four original G witnesses paired with each of the two forbidden E
witnesses.

## 2. Nominal inequalities and the one error budget

Write the unsigned canonical coordinates as `a_i >= b_i >= 0`, and set

\[
 c=\cos t,\quad s=\sin t,\quad W=(1+c+|s|)/2,
\]
\[
 L=447/800,\quad U=283/200,\quad U_G=349/250,
 \quad V=29/25,\quad k=251/250.
\]

The existing geometric coordinate bounds give

\[
 L<a_i<U,\quad b_i<9/10,\quad |p_i|<3/2,
 \qquad 7/12\le a_G,a_T<U_G.
\tag{1}
\]

The H cone and its corner disk imply `a_H < V`, because
`(V+1/2)^2+(V/2+1/2)^2 = 3.922 > Q`.
The frame chart gives `c >= 3/4`, `|s| <= 7/10`, and

\[
                         1-c\le(4/7)s^2.             \tag{2}
\]

Let `e_H,e_A,e_B,e_T,e_D` be the five actual absolute aligned errors;
their sum is S. A projection rotates by at most `3e/2`, while its width
is at least `1+e/2-e^2/4-e^3/12`. Since
`e/4+e^2/12 < 1/250` for `0 <= e <= 3/200`, each original allowed aligned
owner gives

\[
\begin{aligned}
 b_H+b_G&\ge1-ke_H,\qquad b_A+b_B\ge1-ke_A,\\
 a_B-b_T&\ge1-ke_B,\qquad b_T+b_D\ge1-ke_T,\\
 a_D+b_E&\ge1-ke_D.                                  \tag{3}
\end{aligned}
\]

The four nominal G and E projections are

\[
\begin{array}{ll}
 G_0=ca_A-sb_A-b_G,& E_0=ca_H+sb_H-b_E,\\
 G_1=a_A-sa_G-cb_G,& E_1=a_H+sa_E-cb_E,\\
 G_2=ca_G-sb_G-b_A,& E_2=ca_E+sb_E-b_H,\\
 G_3=a_G-sa_A-cb_A,& E_3=a_E+sa_H-cb_H.
\end{array}                                         \tag{4}
\]

An actually feasible G witness satisfies `G_j >= W` exactly. The actual
E angle differs from t by at most S. The projection and width Lipschitz
bounds therefore give `E_j >= W-2S` for each actually feasible E witness.

A sum with HG weight h and E weight e loses at most
`hk e_H+2eS`. In particular, if `h,e <= 1`, its loss is at most

\[
             \ell=(k+2)S\le2253/50000.                \tag{5}
\]

Only one shared aligned-error sum is used here.

## 3. A sharper quarter chain, retaining the shared error allocation

We first prove the uniform bounds

\[
                 \boxed{b_A>79/250,\qquad a_A<1303/1000.}       \tag{6}
\]

The diagonal corner bound gives `b_D < 8993/10000`, because

\[
 2(8993/10000+1/2)^2-Q=24049/50000000>0.
\]

Adding BT and TD in (3), and using `e_B+e_T <= S-e_A`, gives

\[
 a_B+1/2>C+z,\qquad
 C=5/2-8993/10000-kS,\quad z=ke_A\in[0,kS].
\]

Containment at B and the AB inequality imply

\[
 b_A> f(z):=3/2-z-\sqrt{Q-(C+z)^2}.
\]

The radicand is positive throughout this interval, and `(C+z)^2>Q/2`.
Consequently

\[
 f'(z)=-1+(C+z)/\sqrt{Q-(C+z)^2}>0.
\]

Thus the weakest bound occurs at `z=0`, not by independently spending S
in AB and in BT+TD. At the largest allowed S, `C >= 39641/25000`, and

\[
 (39641/25000)^2+(3/2-79/250)^2-Q
                     =318881/625000000>0.
\]

This proves the first assertion of (6). The second follows from

\[
 (1303/1000+1/2)^2+(79/250+1/2)^2-Q=213/200000>0.
\]

Write `A_*=1303/1000` and `b_*=79/250` in the remaining bounds.

## 4. Forced arcs from actual witnesses

For `s >= 0`, feasible G0, G1, G2, G3 force, respectively,

\[
             s<27/100,\qquad s<13/50,
             \qquad s<3/20,\qquad s<3/25.             \tag{7}
\]

Here are direct derivations. Add HG to G0, using (1), (3), (6), and
`b_H < .9`; this gives `-.203+.816s <= kS`, excluding `s >= .27`.
Add c times HG to G1. The necessary inequality is
`-.803+.6c+(13/12)s <= kS`. Equation (2) and `s <= .7` bound its left
side below by `-.203+(253/300)s`, excluding `s >= .26`.

For G2, the G cone `b_G >= a_G/20` gives

\[
 (1/2+U_G/20)s\le U_G-1/2-b_*=2/25,
\]

which excludes `s >= .15`. For G3, (4) and (6) imply

\[
 -.08+(1/2+L)s-(4/7)(1/2+b_*)s^2\le0.
\]

On `s <= .7` its left side is at least `-.08+.73235s`, excluding
`s >= .12`. All four endpoint comparisons are strict rational ones.

For `s=-r <= 0`, a feasible E2 forces

\[
                    r<27/100,\qquad c>24/25.          \tag{8}
\]

Indeed `E2 <= Uc-L/2`, by the H cone. Thus
`1/2+L/2-2S+r/2 <= (U-1/2)c`. Using `c <= 1-r^2/2`, the two sides
already contradict each other at `r=.27` by
`10907/4000000`; the left increases and the right decreases thereafter.
The cosine assertion follows from `.96^2+.27^2<1`.

A feasible E3 similarly forces

\[
                    r<9/50,\qquad c>49/50.            \tag{9}
\]

Use `E3 <= U-L(r+c/2)`. Feasibility requires

\[
 (1/2+L/2)\sqrt{1-r^2}+(1/2+L)r\le U-1/2+2S.
\]

The left side is strictly increasing on `[0,.7]`: in its derivative,
`r/sqrt(1-r^2) <= 1`, so the derivative is at least `L/2>0`.
At `r=.18`, its cosine is greater than `.98`; even replacing it by
`.98` violates the displayed inequality by `749/80000>0`.
This proves (9). These negative arcs were derived from the putative
E witness at the present threshold, not borrowed from an earlier
small-mismatch theorem.

## 5. Exclude E2 for all four G witnesses

Throughout, a circle with positive mass m supplies the exact bound

\[
 xa_i+yb_i\le mq+(x^2+y^2)/(4m)-(x+y)/2.               \tag{10}
\]

It follows by completing the two squares of the shifted corner. No
maximizing center or radial-contact equality is presumed.

### G0/E2

Sum HG, G0, E2 with unit weights. Demand is `D=1+2W` and the coordinate
sum is `F=c(a_A+a_E)+s(b_E-b_A)`. Equations (1), (6) give

\[
 D-F\ge2-(A_*+U-1)c+|s|/10\ge141/500>\ell.
\]

### G1/E2

Sum c times HG, G1, and c times E2. Then

\[
 D=c+(1+c)W,\qquad
 F=a_A-sa_G+c^2a_E+csb_E.
\]

For nonnegative s the gap is bounded below by

\[
 -.803+2c-.915c^2+(13/12-(2/5)c)s.
\]

The sine coefficient is positive, and the c polynomial increases on
`[.75,1]`. Its minimum is `2917/16000`.
For negative s use (8), `a_G <= U_G`, and discard the nonpositive
`csb_E` term in F. The gap is at least

\[
 -.803+2c-.915c^2+\{(1+c)/2-U_G\}r
 \ge20177/125000.
\]

Both lower bounds exceed the loss (5).

### G2/E2

The unit-weight sum HG+G2+E2 has coordinate sum
`ca_G+(1-s)b_G+ca_E+sb_E-b_A`. Apply (10) only to G with `m=3/8`:

\[
 ca_G+(1-s)b_G\le3q/8+5/6-c/2-5s/6.
\]

Its demand-minus-bound gap is therefore at least

\[
 7/6+b_*+(17/200)c-3q/8
          +|s|+5s/6-(9/10)\max(s,0).
\]

The sine part is nonnegative. Equations (7), (8) give `c >= .96`
for either sign, so the gap is at least `1151/12000 > ell`.

### G3/E2, nonnegative s

The unit-weight sum has coordinate sum
`a_G+b_G+ca_E+sb_E-sa_A-cb_A`.
The corner disk gives `a_G+b_G < 9/5`, since `2Q < (14/5)^2`.
It follows that the gap is at least

\[
 1/5-(99/1000)c+(1/10+L)s\ge101/1000>\ell.
\]

### G3/E2, nonpositive s

Use the fixed weights `4/5,1,4/5` on HG,G3,E2. Their coordinate sum is

\[
 a_G+(4/5)b_G+(4/5)ca_E-(4/5)rb_E+ra_A-cb_A.
\]

Complete the G circle with `m=13/40`, and bound the other terms using
(1), (6). The resulting gap is at least

\[
 13/5-(13/40)q-82/65+(21/250)c-(403/1000)r
                 \ge24519/650000,
\]

by (8). Its shared loss is at most `(4/5)ell`. The exact reserve is

\[
 \boxed{24519/650000-(4/5)(2253/50000)
                         =5439/3250000>0.}           \tag{11}
\]

This excludes the entire negative arc, not just an endpoint. The single
fixed stress in this paragraph replaces the inadequate unit-weight
three-edge estimate near the end of that arc.

## 6. Exclude E3 for all four G witnesses

The same nominal loss bound (5) applies in each case.

### G0/E3

Use weights c,c,1 on HG,G0,E3. The demand is `c+(1+c)W`, and
`F=c^2a_A-csb_A+a_E+sa_H`.
For nonnegative s the gap is at least

\[
 -.915+2c-.803c^2+(.816c-.66)s.
\]

By (7), `c>.96`; both the sine coefficient and the derivative of the
c polynomial are positive. The polynomial at `.96` exceeds `1/4`.
For `s=-r`, use `b_A<.9` and `a_H>L` instead; the lower bound becomes

\[
 -.915+2c-.803c^2+(1/2-(2/5)c+L)r>1/4,
\]

by (9). Thus both signs contradict (5).

### G1/E3

Use weights c,1,1. Now `D=c+2W` and
`F=a_A+a_E+s(a_H-a_G)`.
For nonnegative s the gap is at least

\[
 .282-(8/7)s^2+(127/300)s\ge.282,
\]

using (2) and (7). For negative s it is at least

\[
 .282-(8/7)r^2+(1-U_G+L)r>6/25,
\]

using (9). Both exceed (5).

### G2/E3 and G3/E3

Use weights c,1,1 in each case and apply (10) to G with `m=3/8`.
Put

\[
 B_0=8/3-U+b_*-3Q/8=5959/60000.                       \tag{12}
\]

For G2/E3 the c polynomial is `3c-(2/3)c^2`; its loss from c=1 is at
most `2(1-c)`. The remaining sine contribution is at least
`(1/2+(4/3)c-V)s` for s>=0, and `(1/6+L)r` for s=-r.
On the positive arc (7), `c>.98` and `s<.15`; hence the first contribution
dominates `(8/7)s^2`. On the negative arc (9), the second dominates
`(8/7)r^2`. The complete gap is consequently at least B0.

For G3/E3 the c polynomial is `(5/2+b_*)c-(2/3)c^2`, again with loss at
most `2(1-c)`. The positive sine contribution is at least `(1-V+L)s`,
and the negative one at least `(1+L-A_*)r`. They dominate the respective
quadratic losses because

\[
 1-V+L>(8/7)(3/25),\qquad
 1+L-A_*>(8/7)(9/50).
\]

Thus this gap is also at least B0. Finally,

\[
                     B_0-2253/50000=16277/300000>0,
\]

so both cases are excluded.

## 7. All original witnesses, and the remaining problem

If E2 or E3 were an originally feasible witness, choose any actually
feasible G witness. Section 5 or 6 gives a strict contradiction for
that very pair of witnesses. Thus **every** feasible E witness is 0
or 1. A forbidden axis tied with an allowed one is excluded in exactly
the same way; no witness has been replaced by a preferred owner.

The proof preserves all actual centers and all five shared frame errors.
Its only calculations are circle support, monotonicity, the eight actual
mixed-witness alternatives, and the displayed rational comparisons.
No numerical cover, generated owner row, sampled minimum, or external
verification assertion is a premise. No Lean source was changed or
compiled, and no CI was run.

What remains for mixed-owner capture at this threshold is to exclude the
bad pairs with E0/E1. The complete positive G1/E1 exclusion at this
threshold is already in `HAND_MIXED_PRIMARY_AT_THREE_TWO_HUNDREDTHS.md`.
The remaining E0/E1 alternatives, tilt capture, and the earlier global
cuts/contractions are not claimed here.
