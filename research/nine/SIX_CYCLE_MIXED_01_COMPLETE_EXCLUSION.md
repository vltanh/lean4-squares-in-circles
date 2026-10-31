# Complete assembly for the mixed two-share C6 orbit with shares 0 and 1

Date: October 26, 2026.

**Status: complete analytic whole-orbit exclusion, accepted after
independent full-source and physical-scope review.** The complete
boundary proof is independently reviewed in
`REVIEW_C6_MIXED_01_BOUNDARY_MONOTONICITY_C6_2026_10_26.md`;
the coordinate and force lemmas are independently reviewed in
`REVIEW_C6_MIXED_01_GAP_MONOTONICITIES_C6_2026_10_26.md`.
The fixed endpoint source and the full physical join passed root
independent review in
`REVIEW_C6_MIXED_01_COMPLETE_JOIN_ROOT_2026_10_26.md`.
No conditional scalar premise remains.

Retain all nine original physical squares, the common selected positive
certificate, every original force, actual application mean and genuine
shared-mean endpoint, the unique physical circle masks, the true
degree-two equations of the three alternating unloaded side-normal
transmitters, every actual transmitter position, all three extra
squares, and the entire interval

\[
                    \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]

The contact type is the full mixed-corner orbit

\[
 (\chi_0,\chi_1,\chi_2)=(1,1,0),\qquad
        S_0W_0\text{ and }S_1W_1\text{ genuinely shared}.
\tag{2}
\]

The three extra squares remain arbitrary. The contradiction being
assembled occurs already among necessary equations of the original
six cycle bodies. No replacement force system or packing is created.

## 1. The exact whole-domain inputs

Use the physical normal form and exhaustive orbit cover in
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md`. Normalize
only the positive force scale to `(mu_0,mu_1,mu_2)=(1,p,q)`.
Put

\[
 \alpha_i=\theta_i-\pi/2\in(0,\pi/4],\qquad
 \sum_i\alpha_i=\pi/2,\qquad
 c_i=\sin\alpha_i,\quad s_i=\cos\alpha_i,
\]
\[
 t_i=s_i-c_i,\quad h_i=s_i+c_i,
 \qquad r=1/\sqrt2,\quad P=1+r,\quad Q=9/4,\quad K=79/40.
\tag{3}
\]

The exact mean-preserving closure arguments in
`SIX_CYCLE_MIXED_01_CLOSURE_REDUCTION.md` prove, over every
original positive force ratio,

\[
 p>P,\qquad
 p(1-c_0-c_1)\ge s_1(s_1-c_1),
 \qquad c_0+c_1\le1,
\]
\[
 h_1>(1+r)s_0-rc_0.
\tag{4}
\]

The last inequality implies `c_0>3/10`, as proved in
`SIX_CYCLE_MIXED_01_GAP_MONOTONICITIES.md`. Thus, with
`a=c_0` and `b=c_1`, every actual packing lies in the simple
necessary domain

\[
 p>P,\quad \frac3{10}<a\le r,\quad 0<b\le r,
 \quad a+b\le1,
 \quad\arcsin a+\arcsin b\ge\pi/4.
\tag{5}
\]

No positive-force limit or endpoint mean was deleted to obtain (4).
In particular the force bound is the full concavity/Cauchy lemma of
the closure source, not a diagnostic lower estimate.

## 2. The exact scalar gap and its reviewed monotonicities

Write

\[
 s=\sqrt{1-a^2},\quad t=\sqrt{1-b^2},
 \quad c_2=st-ab,\quad s_2=sb+at,
\]
\[
 D=\sqrt{1+p^2+2pb},\quad
 w=1+\sqrt2+a+s,\quad v=\sqrt{4K^2-w^2}>0,
\]
\[
 G(p,a,b)=KD-2-b-t-3p
                   +\frac w2(a+pc_2)+\frac v2(s+ps_2).
\tag{6}
\]

The unchanged physical virial identity is `R sum_i D_i=N`, with
`D_i=|f_(i-1)-f_i|>0`. The pointwise Cauchy elimination in
`SIX_CYCLE_MIXED_01_CAUCHY_AND_ENDPOINTS.md` proves

\[
                     K\sum_iD_i-N\ge G(p,a,b)
\tag{7}
\]

for every original positive `q`; no value of `q` is selected.

The independently reviewed source
`SIX_CYCLE_MIXED_01_GAP_MONOTONICITIES.md` proves that `G`
is strictly increasing in `p` whenever `p>=P` and `a+b<=1`,
and strictly decreasing in the second angle `alpha_1` whenever
`p>=P` and `a>3/10`. Since sine is strictly increasing on
`[0,pi/4]`, the latter is also strict decrease in `b` while
`a,p` are fixed and the angle path remains in the original closed
angle triangle. The source additionally proves decrease in the first
angle; the join below does not need to increase both angles at once.

The independently reviewed separate boundary source proves the
following full-interval statement, with all denominators positive:

\[
 a\longmapsto G(p,a,1-a)\text{ is strictly decreasing on }
 [3/10,r]\quad\text{for every }p\ge P.
\tag{8}
\]

This is the exact statement used from
`SIX_CYCLE_MIXED_01_BOUNDARY_MONOTONICITY.md`. It is not inferred
from the two coordinate monotonicities. The fixed scalar source proves
unconditionally that

\[
 G(P,5/9,4/9)>1/40,
 \qquad G(Q,r,1-r)>1/40.
\tag{9}
\]

Both signs in (9) have complete rational square-bound proofs and
positive reserves in the cited source.

## 3. Every angular path in the join is valid

For any original `a` in (5), increase `b` to `1-a` while
holding `a,p` fixed. This stays inside the permissible individual
angle interval because

\[
 1-a<7/10<r,\qquad b\le1-a.
\tag{10}
\]

The lower condition `alpha_0+alpha_1>=pi/4` is preserved by
increasing `b`. At the final point, both sines are positive and
sum to one. Therefore their squared sum is less than one, so
`arcsin(a)+arcsin(1-a)<pi/2`. The same strict upper bound
holds throughout the increasing path. Thus the third angle remains
between zero and `pi/4`. All arguments of the reviewed angular
derivative stay in its stated domain.

It follows that

\[
                    G(p,a,b)\ge G(p,a,1-a).
\tag{11}
\]

Every point on the boundary interval in (8) also lies in this closed
angle triangle. Both sines lie in `(0,r]`, and their sum is one;
the angle sum is at least `pi/4` because the sine of that sum is
at least either positive sine and, more directly, the sum is at least
`pi/3`: for a fixed angle sum, concavity of sine gives
`a+(1-a)<=2 sin((alpha_0+alpha_1)/2)`. Its upper bound is the
strict `pi/2` bound just proved. Thus (8) will not be applied to
an artificial angular extension outside its own hypotheses.

## 4. Two exhaustive force ranges and their endpoints

First suppose `p>=Q=9/4`. The force derivative, (11), the
boundary lemma (8), and the second endpoint in (9) give

\[
 \begin{aligned}
 G(p,a,b)&\ge G(Q,a,b)\ge G(Q,a,1-a)\\
        &\ge G(Q,r,1-r)>1/40.
 \end{aligned}
\tag{12}
\]

All angle-dependent quantities stay fixed during the force decrease,
so `a+b<=1` remains valid. The force parameter ends at `Q>P`,
within the full monotonicity range. Equality `p=Q` is included here.

Now suppose `P<p<Q`. The exact first projection in (4) gives

\[
 p(1-a-b)\ge s_1(s_1-b)=1-bh_1,
\]

and hence

\[
 a\le1-\frac1p-b\left(1-\frac{h_1}{p}\right)
                <1-\frac1p<\frac59.
\tag{13}
\]

Here `h_1<=sqrt(2)<P<p`, and `b>0`, so the displayed
strict inequalities have their claimed signs. This keeps the original
projection until it yields the correct upper endpoint for `a`;
replacing it merely by `a+b<=1` would lose (13).

Decrease the scalar force `p` to the permitted comparison value
`P`, apply (11), and then use (8) and the first endpoint in (9):

\[
 \begin{aligned}
 G(p,a,b)&>G(P,a,b)\ge G(P,a,1-a)\\
        &\ge G(P,5/9,4/9)>1/40.
 \end{aligned}
\tag{14}
\]

These are estimates of one scalar function on its proved enlarged
domain. They do not modify a positive physical force in the original
certificate. No claim is made that a comparison point itself is a
packing. The two force ranges are exhaustive and leave no equality
boundary uncovered.

## 5. The full original physical contradiction

Equations (12)--(14) give `G>1/40` on the entire original mixed-01
domain.
Restore the force scale `mu_0`: (7) then yields

\[
                  K\sum_iD_i-N>\frac{\mu_0}{40}>0.
\tag{15}
\]

Substituting the unchanged physical identity `N=R sum_i D_i`
contradicts `R>=K`, since `sum_i D_i>0`. This is the entire
orbit (2), with every physical square and every actual shared mean
still present. No bound on an extra-square position or a transmitter
slider was imposed.

The logical join here does not use a numerical optimization, interval
grid, coefficient packet, Lean compilation, or CI action. The global
sharp inequality, equality classification, the remaining one-share
completion problem, the obtuse one-radial branch, and the earlier
prerequisite audit remain separate obligations.
