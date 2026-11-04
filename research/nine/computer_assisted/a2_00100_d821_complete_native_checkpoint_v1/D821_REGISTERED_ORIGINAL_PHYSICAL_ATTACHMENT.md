# D821: exact original-path attachment

This attachment records the unchanged original domain for
`positive-821c9a2debeed0aa`, positive baseline frontier index 26. It adds no
exclusion by itself. The complete-original conclusion still requires the
five complementary domains and every continuation to pass exact replay.

## Registered path and literal halfspaces

The frozen original path is

```json
[["angle",3,1],["angle_cut",[0,"0"],1],
 ["alternate_four_escape",[1,7],[3]]]
```

Indices 0 through 8 are the original squares A through I. The frame slope
is `t_i=beta_i/alpha_i`, with `alpha_i>0`; it is not an angle in radians.
The two slope branches retain `t_D in [0,1]` and `t_A in [0,1]`, including
their shared zero faces.

The frozen `alternate_chain((1,7))` is `(A,B,H,D)`. The literal selected
escape is branch 3; each earlier escape is retained with its sign reversed
as a closed predecessor complement. Thus the four additional center
inequalities are exactly

\[
\begin{aligned}
x_H-x_B+y_H-y_B&\le0,\\
x_A-x_B+y_B-y_A&\le0,\\
x_A-x_B+y_A-y_B&\le0,\\
x_B-x_H+y_H-y_B&\le0.
\end{aligned}
\]

The first is the selected branch. The next three are the complements of
branches 0, 1 and 2 in that order. Every equality is retained. In particular,
no strict predecessor face is silently deleted and no alternative physical
label order is substituted. The accompanying literal audit evaluates only
the two frozen row-definition functions and checks every coefficient and
right-hand side against these four displayed expressions.

## Full physical caller

Each of the nine originals is a unit square with center `(x_i,y_i)` and
orthonormal frame determined by `(alpha_i,beta_i)`, where
`alpha_i^2+beta_i^2=1`. Its original corners are

\[
\left(x_i+\frac{\epsilon\alpha_i-\tau\beta_i}{2},
      y_i+\frac{\epsilon\beta_i+\tau\alpha_i}{2}\right),
\qquad \epsilon,\tau\in\{-1,1\}.
\]

All 36 corners lie in the closed disk of squared radius `1105/256`.
All 36 original pair interiors are disjoint. The exact `001/00` caller
retains actual AB, BC, EF and FG, strictly weak CD, and all five original
center-cone comparisons. The accepted normalization retains its original
large D/C height gap, both original sign roots and the H/I label order;
this registered path selects only its stated positive sign root and
subsequent clauses. All other inherited physical conditions remain active.

`fresh_root_bound4.json` starts from this literal registered domain. Its
initializer independently reconstructs the whole path before checking any
of the four bound rounds. The resulting D/G corridor, horizontal order
and height inequalities are proved consequences of the original domain.
They are not additional caller restrictions. The full mathematical use of
those consequences, the actual-AB theorem, its closed equality blocker and
the five closed complementary domains is given in
`D821_COMPLETE_ASSEMBLY_HAND_PROOF.md`.

The frozen original-definition source and the current status register have
the same 231 ID/sign/baseline-index/path tuples. Their status fields serve
different dates; proof attachment uses the immutable definitions. The
literal audit rechecks this exact equality and the root's original-source
hash. It neither repeats weighted arithmetic nor changes a closure ledger.
