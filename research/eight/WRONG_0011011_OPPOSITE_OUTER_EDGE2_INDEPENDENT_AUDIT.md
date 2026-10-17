# Independent audit: the whole opposite-sign outer edge-2 quarter row

**PASS.** The reviewed theorem covers all four retained axes on both halves
of the complete angle interval. It proves the strict bound `.89777`, hence
the declared pair target `17953/20000`, for edge 2 with signs `(-,+)` and
its reflected edge-6 partner. No discovery or sampled optimizer premise is
used in the continuous proof.

The companion's 106 fixed exact comparisons were replayed byte for byte.
The separate `audit_wrong_0011011_opposite_outer_edge2.py` imports none of
the companion's routines: it binds the two exact label rows from the
declared rational label table, evaluates circle derivatives by the chain
rule, uses different Taylor truncations and square-root brackets, and
reconstructs all twenty displayed curvature/ratio rows. Together with the
decisive reference values and coarse direction comparisons it passes 37
independent strict checks. Its JSON records hashes of the reviewed
manuscript, companion source and arithmetic output.

## Continuous identities and initial bounds

I rederived the four signed projections directly from the source and target
frames. The cost is exactly `phi-P(b)-R(B)`: the reflected role-2 negative
label is `-P`, and role 3 supplies `+R`. The circle derivative formulas,
all stated monotonicities of `P` and `R`, and both changes from transverse
to primary coordinates are correct. In particular, expanding
`M(a)=-P(b(a))` gives

`M = constant + .02363*u^2 + (.11055*u-.961795)*sqrt(Q-u^2)-.055275*u`,

which differentiates to the stated formulas. For `N(A)=-R(B(A))`, the
logarithmic derivative follows from `B'=-1/r_B`; both its terms are
positive. The two distinct aligned contact sets are complete because the
labels increase. Their curvature/monotonicity arguments have the correct
directions.

## The two boundary curves

The rotation formulas for the common lower-half axial curve solve its
contact equation on the correct branch. Direct differentiation gives
`U'=V*f`, `V'=-U*f` and the printed expression for `f'`. Its sign and the
decrease of `-f'` follow from the stated numerator monotonicity. Each of
the three axial curvature rows uses a positive upper bound for `z''`;
this additional sign was checked independently, so using the upper bound
for `R'` in the negative term is valid. The strong-convexity completion
at `.15017` and the subsequent strictly increasing tail cover the whole
curve through its zero-coordinate exit.

For the upper-half zero-coordinate exit, separate concavity in its two
variables and the four endpoint values exclude the full rectangle
`x in [.4,.7]`. On the remaining strip the denominator of the implicit
derivative is positive and below `.4`, whereas its numerator exceeds `.4`.
Thus `x_z>1` holds on the whole exit, and both possible label costs increase
toward the aligned endpoint. There is no assumption that a root occurs at
a sampled point.

## Coverage of the eight half-axis regimes

The axis-1 lower contact flow maximizes the source coordinate and then
increases the angle parameter until that coordinate reaches zero. The
negative angle derivative follows from the decreasing product
`P'(b)*sqrt(Q-(b+1.5)^2)`; its endpoint is the first common boundary curve.
The upper half has positive angle derivative, its nonnegative contact set
is an interval by concavity, and it ends at alignment or the second
boundary curve. Its contact remains below the diagonal throughout, so no
unmentioned clamped interval is present.

For axis 2 on the lower half, the least target primary coordinate is
always active and at least `1+b`. Interior source stationarity, the target
axial endpoint and the remaining source axial endpoint all have the
claimed decreasing-angle direction. The source diagonal is impossible.
The bound on `N''/N'` uses the correct endpoint denominators. On the upper
half, an inactive target diagonal is reduced to contact by increasing the
source coordinate. The five `P' v/k` rows cover every source coordinate.
They supply the same strict direction at interior stationary points,
one-sided source endpoint minima and either target endpoint. The axial
source is separately covered, so the compact-minimum reduction is complete.

For axis 3 on the lower half, the source second derivative is positive on
the `.01` strip, while the first derivative at its upper feasible endpoint
is negative. Thus the entire source minimum is on the zero target; the
boundary cost increases from alignment. The remaining angle tail uses
valid upper chords for the increasing labels, the full-circle support,
and seven strictly negative second-derivative rows. The two endpoint
comparisons therefore close the entire tail. The upper half reduces to
alignment or the already proved upper zero-coordinate exit.

Axis 4 on the lower half has an active source coordinate and a strictly
positive angle derivative. Its upper half includes the possible inactive
source diagonal, both source endpoints, the target diagonal and the axial
target. The inactive part moves to contact by increasing the target
coordinate. I rederived the decisive ratio identity: solving the rotated
contact equations at source primary `a=d` yields exactly

`k/K = (Q-u)/(u*q) + v*z/(u*q*K)`.

The comparison contact exists before `pi/2`; allowing it beyond `.7` only
enlarges the speed ratio used as an upper bound. Differentiating the last
display gives the printed formula (25), and the five fixed positive rows
prove its strict separation from `R'`. This controls every stationary or
boundary contact. The last axial target uses `M''>.979>.67`; the weaker
`.67` in its product estimate is legitimate. Its endpoint product is
strictly below one. Thus the final compact-minimum argument includes all
boundary components and the upper angle endpoint.

No correction is required. The proof and its exact arithmetic support the
full stated row, without any inference to a different sign, radial kind or
word except the explicitly justified reflected-reversal partner.
