# First actual LP use of the fresh strict-011 representative root

Root observed session 14074 finish with exit 0 using the frozen real-LP
protocol and the `threads=1` v2 driver. The output is a complete four-way
AB inset-proxy cover: five nodes, one excluded child, three OPEN children.
The independent fresh subprocess reports the whole mask OPEN.

The LP selected four nonzero weights. Each exact weight is
`274877906944 / 2^40 = 1/4`. The printed physical rows are the unit-width
inset tangents for A and B, the actual AB mask row, and the negative-x AB
proxy row. Writing `d=x_B-x_A` and `h=(alpha+|beta|)/2`, they are

| Physical row | Inequality |
|---|---|
| A inset tangent at width sum 1 | `-g_A-h_A <= -1` |
| B inset tangent at width sum 1 | `-g_B-h_B <= -1` |
| Actual AB projection comparison | `-d+h_A+h_B <= 0` |
| AB negative-x inset alternative | `d+g_A+g_B <= 0` |

The tangent is a necessary physical inequality: with width sum `s=2h`
and `g=1/(2s)`, its slack is `(s-1)^2/(2s)>=0`. The mask has actual AB,
and the last row is exactly the selected member of the complete four-way
physical inset union. Every other original square, corner, and pair stays
in the caller.

Summing the four rows with weights 1/4 cancels every one of the 54 original
variable coefficients and gives `0 <= -1/2`. The exact reserve is `1/2`.
The actual floating-point proposal therefore produced an exactly dyadic
dual: the independently recomputed residual vector is zero and its
absolute-bound payment is zero. This gate does not claim a nonzero
numerical residual was exercised. The generic residual-payment path is
source-reviewed and will be separately recorded when a later numerical
bound actually uses it.

The companion audit rehashes the actual output, reconstructs the same
normalized caller, reconstructs all four expected child states, and
freshly checks all five records with the frozen independent arithmetic.
It also rebuilds the four displayed rows directly from their physical
formulas and recomputes every weighted coefficient, RHS, and reserve.
It uses no optimizer and imports no numerical package.

This is the required first actual numerical weighted-use gate for this
fresh driver. It grants no new original-cell or mask credit. The separate
bounded whole-root run remains subject to root scheduling and preserves
all unfinished domains explicitly.
