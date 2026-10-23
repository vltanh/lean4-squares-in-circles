# An exact obstruction to extending the fixed stationary scalar to S = 1/10

## 1. Scope

This note identifies a negative direction of the **eliminated scalar**
used by the conditional owner-frame terminal. It is not a packing,
a feasible-center construction, or a counterexample to the proposed
middle contraction. Its purpose is to identify which information a
larger-range proof must retain: the original center constraints, a
different stress, or both. Improving the Taylor remainder of this same
scalar cannot prove a nonnegative correction on the whole larger range.

Use the exact identity (6) in
`HAND_OWNER_GAUGE_POSITIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md`, with the
stationary weights from
`HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md`.
Fix a stationary comparison point at `q=q_*` and

\[
                  \frac1{10}\le\tau\le\frac4{25}.
\]

All statements below concern evaluation of that explicit scalar. They
do not apply its conditional geometric theorem outside its hypotheses.
Write `c=cos(tau)`, `s=sin(tau)`, and use the stationary positive
radicals `v,w` and positive edge weights `delta,epsilon` from those notes.

## 2. One exact error direction

Retain the D-owned ED alternative, so its owner indicator is `j=0`.
Set

\[
 x_1=x_2=x_3=h=0,\qquad x_4=x>0.
\tag{1}
\]

Here h denotes the HG error. The other four owner indicators can be
chosen arbitrarily. Every norm term, the mixed GA term, and both free
slider terms in the exact identity are unchanged. Its only changing
terms are the ED support and the mixed HE sine. Consequently

\[
\begin{aligned}
 \Delta\Phi(x)
 &=\delta(\cos x-1+\sin x)
       +\epsilon\{\sin(\tau-x)-\sin\tau\}\\
 &=(\delta+\epsilon s)(\cos x-1)
       +(\delta-\epsilon c)\sin x.
\end{aligned}
\tag{2}
\]

This is an identity, with no Taylor loss. For `0<=x<=1/10`, both
mixed-angle width branches used to obtain it are nonnegative because
`tau-x>=0`; the endpoint `tau=x=1/10` follows by continuity.

Stationarity gives

\[
 \delta-\epsilon c=\epsilon s\frac vw.
\tag{3}
\]

Since `(1-cos x)/sin x=tan(x/2)` for `0<x<=1/10`, (2) yields the
exact criterion

\[
 \boxed{\Delta\Phi(x)<0
 \quad\Longleftrightarrow\quad
 \tan\frac x2>
 \frac{z\eta}{1+z(1+\eta)},\qquad
 z=\tan\tau,\quad\eta=v/w.}
\tag{4}
\]

## 3. A negative value throughout the stationary tilt interval

The already proved stationary rectangle gives

\[
 0<z<\frac{41}{250},\qquad
 0<\eta<\frac{562}{1897}<\frac3{10}.
\]

The positive rational function on the right of (4) increases in both
variables. Therefore

\[
 \frac{z\eta}{1+z(1+\eta)}
 <\frac{(41/250)(3/10)}{1+(41/250)(13/10)}
 =\frac{41}{1011}<\frac1{20}.
\tag{5}
\]

At `x=1/10`, elementary strict monotonicity of `tan x-x` on the
positive interval gives `tan(1/20)>1/20`. Equations (4)--(5) prove

\[
                 \boxed{\Delta\Phi(1/10)<0}
\tag{6}
\]

for every stationary comparison tilt in the stated interval. More
explicitly, the correction is less than

\[
 -\frac{191}{20220}(\delta+\epsilon s)\sin(1/10)<0.
\]

In particular this holds at the unique stationary minimum `tau=t_*`,
where the zero-error eliminated scalar has value zero. Thus the same
scalar evaluated at (1) has negative value at `S=1/10`.

The completed center squares, disk slacks, and remaining primal
constraints were discarded in forming that scalar. A negative value
of a necessary scalar expression does not supply centers satisfying
those constraints. The result rules out only a proposed proof of
nonnegativity of this unchanged scalar throughout `S<=1/10`; it does
not rule out the desired geometric contraction. No numerical sample,
angle subdivision, generated certificate, Lean compilation, or CI run
is used in this calculation.
