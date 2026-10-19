# Independent audit of the compact terminal and sharp-ceiling proofs

The independently reviewed files are

- `HUMAN_BROAD_TERMINAL_ARITHMETIC.md`;
- `verify_hand_terminal_tables.py`;
- `HUMAN_SHARP_CEILING_BRACKET.md`;
- `verify_hand_sharp_ceiling_bracket.py`.

**Result: the mathematical enclosure and terminal arguments pass.** Both
fixed-arithmetic transcription checkers also complete successfully. The
new proofs supply a conditional arbitrary-center terminal theorem and the
exact rational ceiling comparison; they do not establish the global
contact, owner, or angle-budget hypotheses.

## 1. Arithmetic and stationary-graph enclosure

The terminal checker's integer intervals round outward under every sum,
product, reciprocal, and square root, including reciprocals of negative
intervals. All divisions exclude zero. Its derivative pairs apply the
ordinary product, quotient, and square-root rules. In particular,
`z_t=(1+z*z)/2` correctly differentiates with respect to the angle t, not
with respect to the half-angle parameter z. The q coordinate is held fixed.

The nine printed position brackets cover all nine stated z values
uniformly in q. The full-box signs `F_yy>6` and `F_yt<0` justify the
continuum between those values: the lower y value at the first endpoint
has negative `F_y` at every later t, and the upper y value at the last
endpoint has positive `F_y` at every earlier t. There is exactly one
stationary position in that fixed box. It is the globally minimizing
position from the analytic family theorem and satisfies
`Y_t=-F_yt/F_yy>0`.

Therefore each of the four fixed rectangles contains the entire
stationary graph between its two endpoint brackets. Every midpoint
bracket is a valid anchor for the mean-value estimate on that graph.
The derivative operator used in the owner table is precisely
`partial_t-(F_yt/F_yy)partial_y`. Half the z width is 31/8000; since
`dt/dz<=2`, its t distance is at most 31/4000, as printed.

All nine lower-reserve computations and the curvature, weight, norm,
and endpoint bounds in the Markdown match the checker. There is no
additional adaptive domain used by the checker.

The actual tilt interval lies in the rational chart. An elementary
explicit check, which can be appended for clarity, is

\[
\tan(1/20)>1/20,\qquad
\tan(2/25)
\le\frac{2/25}{1-(2/25)^2/2}
=\frac{50}{623}<\frac{81}{1000}.
\]

## 2. Independent derivation of all owner alternatives

Use the names and positive weights of the terminal note. The exact force
identities reduce the smooth single-frame coefficients to

\[
v_B=(\alpha-\beta)/2,\quad
v_D=(\beta-\delta)/2,\quad
v_E=\delta/2-\epsilon c,\quad
v_T=0,\quad
v_H=-\omega/2+N.
\]

For H, the mixed HE transverse coordinate gives

\[
(c-s)/2-Y_{HE}=-1/2-h_1-h_{2t}.
\]

Together with `mu_H h_1=-omega/2` and
`mu_H h_2=-epsilon/2`, this yields the displayed formula for `v_H`.

Choosing the owner of an aligned edge subtracts its weight times its
reference transverse coordinate from that owner's smooth coefficient.
The five transverse coordinates are, in the note's order,

\[
x_1-x_2,\quad y+3/2-Z,\quad Z-y_3+1/2,
\quad x_4-x_3,\quad\eta.
\]

The ED cut contains E. Adding D, then T, and then taking the negative
of the B/T/D/E cut gives the DT, TB, and AB coefficients. Every other
aligned edge has both its endpoints on one side of the cut. Hence its
contribution is independent of that edge's owner. This reproduces
exactly the two coefficients in every row of the terminal note's table.
The H cut gives the two HG alternatives directly.

The simplification uses the exact identities

\[
K=\epsilon c+\delta(x_4-x_3),\qquad
L=\delta-\epsilon c,
\]

whose second equality follows from `F_y=0`, rather than from a numerical
stationarity residual.

The nine-scalar implication is valid at the endpoints as well as the
interior of the slider rectangle:

- AB needs `X` and `alpha(1-Y)-X`.
- The varying TB/DT owner needs the two extrema
  `beta(-9/10-J)` and `beta(27/25+J)`.
- The other DT owner needs `K` and `beta-K`.
- The other TB owner needs `X` and `beta-X`; the latter exceeds the
  second AB reserve because `beta>alpha` and `0<Y<1`.
- ED is covered by `K` and `L`, using `K<epsilon c`.
- The two HG alternatives over `eta in[-1/2,37/100]` are covered by
  `N-(37/100)omega` and `omega/2-N`.

This is an analytic cover of all 32 assignments, with no numerical
enumeration needed for the reduction.

## 3. Coarse and sharp radius enclosures

The new family coordinates agree exactly with the existing global family
theorem: `y=-u`, `x_1=r`, `x_2=U`, `x_3=-V`, `y_4=-v`, `x_4=-w`, and
`(h_1,h_2)=(-k_1,-k_2)`. The new q interval lies inside that theorem's
radius strip.

At every q in the new interval the stationary envelope has reduced
curvature greater than 3/4 throughout the four rectangles. The two
endpoint signs give a critical point in the chart; global family
uniqueness identifies it as the minimum in the entire relevant strip.

For a fixed test point, strong convexity in y gives the precise loss
`F_y^2/(2*6)=F_y^2/12`. The mean-value theorem, with `|F_yt|<6`, bounds
the change in `F_t` by `|F_y|`. Strong convexity of the stationary
envelope gives the second loss
`(|F_t|+|F_y|)^2/(2*(3/4))=(2/3)(|F_t|+|F_y|)^2`.
All position segments and angle intervals used here remain inside the
proved chart. Thus the coarse lower bound `5981/48000000>0` is global
within the family, rather than a local positive defect test.

The eight sharp-pose radical brackets are stated as rational inputs and
checked by strict squaring against the complete preceding radicand
intervals. In particular the signs of `x_2-3` and `y_3-2` give the
correct lower and upper radicands at both nested square roots. The
printed integers, widths, radius choices, and fixed y/z test coordinates
match the checker.

The same two-stage convexity bound at q_- is strictly positive, because

\[
\frac7{10^{16}}-\frac{11}{4\cdot10^{28}}>0.
\]

At Q_sharp the negative test value bounds the minimum from above.
Continuity, strict radius monotonicity, and global uniqueness therefore
give `q_-<q_*<Q_sharp`. This argument does not assume the decimal test
coordinates are the exact minimizing coordinates.

## 4. Nonlinear remainder and scope

The reference selected vertices have norm below 2. For the H vertex,
the positive reduced curvature makes its squared norm convex along the
stationary graph, so the two endpoint bounds suffice. The reference
neighbor vectors and both slider centers satisfy the stated stronger
norm bounds on the full parameter box and every slider value; convexity
justifies reducing the affine slider rectangle to its four corners.

The pure angular loss `12 S^2` accounts for the five disk terms, all
reference-normal projection terms, the true aligned support cusps,
and the mixed HE width. GA has no mismatch dependence because its
actual frame defines the comparison tilt.

The printed Young sum below 110 absorbs arbitrary anchored-center
displacements at cost `110 S^2`, retaining half their positive squares.
Choosing the two sliders by their actual projections makes their
displacements exactly parallel to their reference incident normals.
Both displacement norms are below 4. The identity
`(R(a)n-n) dot (xi n)=xi(cos a-1)` therefore makes the slider loss at
most `8 S^2`, including the deliberately overestimated zero GA term.

The total loss is `130 S^2`, and the final positive coefficient is

\[
\frac9{500}-130\frac1{10000}=\frac1{200}.
\]

No center-neighborhood assumption has entered this argument. The
remaining premises are exactly the named signed owners, the frame
lifts and common tilt, the small aligned-angle total, and the two
projected-slider intervals. Those are global capture premises and
must continue to be proved separately.
