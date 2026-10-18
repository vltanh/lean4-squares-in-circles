# Long two-core terminal: exact role, owner, and angle interfaces

This note identifies the hypotheses passed from the finite boundary-state
certificates to the seven-square local dual. The finite domain cover is now
complete, with all32 ordinary exclusion inputs matched to audited exact
manifests. The charged angular budget and its independently checked owner
complement are also complete. Their exact composition gives the angular and
owner conclusions below. The broad center-free local dual, stationary graph,
and projected-slider interfaces are now also proved. Section8 gives the
completed contradiction for this boundary word.

## 1. Boundary word and terminal role box

The counterclockwise word is `(C0,O1,O2,C3,O4,O5,O6)`, with the selected named
branch equal to the reflection of `(T,B,A,G,H,E,D)`. The exact terminal box is

| Role | Named square | Signed tangent interval |
|---|---|---|
| 0 | T | [-9/32,-17/64] |
| 1 | B | [31/64,33/64] |
| 2 | A | [-23/64,-21/64] |
| 3 | G | [13/64,15/64] |
| 4 | H | [-61/64,-59/64] |
| 5 | E | [1/64,3/64] |
| 6 | D | [55/64,57/64] |

The exact rational cover audit `audit_long_two_core_cover.py` verifies every
domain inclusion and complement cover leading to this box. Its latest output
matches all32 pair inputs to complete exact manifests, with no pending input. The
reflection and maximum-core selection are explicit in that audit and in the
capture ledger.

## 2. The residual budget and the five aligned frame differences

Let `h(d)=(cos d+sin d-1)/2`, where `d` is the distance between square frames
modulo `pi/2`. The budget has penalty `1/50` on edges0,1,3,5,6 and zero on
edges2,4. Define each directed pair residual by

\[
e_i=\delta_i-\beta_i h(d_i)+\psi_{i+1}(t_{i+1})-\psi_i(t_i)-\gamma_i.
\]

The exact pair theorem gives `e_i>=0`. Physical holonomy and the exact rational
sum of constants give

\[
\sum_i e_i+\frac1{50}\sum_{i\in\{0,1,3,5,6\}}h(d_i)
=2\pi-\sum_i\gamma_i<\frac7{10^7}.
\]

Therefore each residual is below `7/10^7`. The elementary concavity and Taylor
bounds detailed in the ledger give

\[
S=d_0+d_1+d_3+d_5+d_6\le\frac1{14000}<\frac1{10000}.
\]

## 3. Exact canonical quarter turns

Write `alpha_i=atan(t_i)`. The relative canonical frame angle across edge `i`
is

\[
\varphi_i=\delta_i+\alpha_{i+1}-\alpha_i.
\]

Since `0<=h<1/4` and `0<=e_i<7/10^7`, the budget bounds this expression using
only the separate one-variable ranges of `psi_i(t)-atan(t)`. The exact
Fraction-only script `verify_long_terminal_angle_lift.py` proves

\[
|\varphi_0-\pi/2|<1/4,\quad |\varphi_1|<1/4,
\quad |\varphi_3|<1/4,\quad
|\varphi_5-\pi/2|<1/4,\quad |\varphi_6|<1/4.
\]

Together with the small frame-distance budget, these fix the signed lifts:
the deviations from the displayed multiples of `pi/2` are the actual small
frame differences, with absolute values `d_i`. There is no hidden choice of a
different quarter-turn branch.

Normalize A's square frame to angle0 and then undo the reflection of the named
ring. All standard frames A,B,T,D,E are consequently within `S` of angle0.
Take G's actual tilted angle as the common angle `t`; H's frame differs from
that angle by at most `d_3`. The sum of the five actual aligned edge mismatches
is exactly `S`, the quantity used by the local dual.

## 4. Exact nominal SAT owners

In the order `(source e, source f, target e, target f, then their negatives)`,
the independently completed masked certificate permits only the following
signed axes:

| Directed boundary edge | Allowed indices | Named local-dual contact |
|---|---|---|
| T to B | 1,2 | Horizontal T/B; either owner |
| B to A | 1,3 | Vertical A/B; either owner |
| A to G | 3 | G-owned tilted axis for G/A |
| G to H | 1,3 | Tilted H/G; either owner |
| H to E | 4 | H-owned transverse axis for H/E |
| E to D | 1,2 | Vertical E/D; either owner |
| D to T | 1,3 | Horizontal D/T; either owner |

The canonical quarter turns in Section3 are what identify these signed axes
with the named directions. The five two-owner choices give the32 cases of the
local dual. The two mixed-frame contacts have their required owner fixed.

The mask theorem itself states that every wrong-axis separated pair has cost
at least `gamma_i+7/10^7`. It is independently valid per pair. Thus one may
combine it with target-cost checks on just the allowed axes to establish the
full pair budget, without circular reasoning. Once the full budget is summed,
its residual bound makes every wrong axis impossible in the physical ring.

The selected-axis budget passed all7 times576 initial pieces, using24558
exact interval nodes. Its audited manifest is
`m5_agent/long_local_selected_budget_v1_charged_piece_logs_checked/manifest.json`,
with SHA256
`4db897f1ad7382dc258cf368bd4ce9aed57e97aa7c781880372062dde2d37369`.
The composition audit independently rechecks the completed owner complement,
whose manifest SHA256 is
`ead804b9221b9cee0970365ce998616ab6002c3efbc6849ceef125cc7d79effa`.
Thus the full-SAT pair theorem, its cyclic residual budget, and the owner
conclusion are established on the exact terminal role box.

## 5. A broad exact common-tilt interval

For mixed edge2 the penalty is zero. Hence

\[
t=\frac\pi2-\delta_2-\arctan(t_3)+\arctan(t_2)
\]

is enclosed using the two separate piecewise-linear-plus-arctangent functions.
The exact scalar audit proves the rational bound

\[
\boxed{\frac1{10}<t<\frac4{25}.}
\]

The outward interval printed in decimals is approximately
`[.1028967634869,.1503772470899]`; only its exact Fraction endpoints and the
rational outer bound are used in the argument. The arctangent enclosure uses
20 terms of the alternating series, and the pi enclosure is supplied by the
independent Machin-series audit. This is a broad chart, not a claim that the
tilt already lies in the earlier tiny fixed-root neighborhood.

## 6. Projected sliders in the center-free comparison

The two core tangents lie strictly within `|t_i|<6/7`, so both C-states have
canonical longitudinal coordinate exactly `a=7/12`.

After the normalization above, let `a_T` be T's small frame error relative to
the horizontal family. Its actual height is

\[
z_T=\frac7{12}(\cos a_T-t_0\sin a_T),\qquad |a_T|\le S.
\]

Consequently

\[
\frac7{12}\left(1-\frac{S^2}{2}-\frac9{32}S\right)
\le z_T\le
\frac7{12}\left(1+\frac9{32}S\right).
\]

At `S<=1/14000` this lies strictly inside `[29/50,7/5]`. The lower endpoint
reserve matters: the exact projected height need not be at least `7/12` when
T's frame is slightly rotated.

Because `t` is G's actual frame angle, its transverse projection is exactly

\[
G\cdot f_t=-\frac7{12}.
\]

For the stationary comparison center `H^0(t)`, write
`H^0(t)·f_t=h_2(q_*,y(t),t)+1/2`. The slider chosen to match G's actual
transverse coordinate is therefore

\[
\eta=(G-H^0(t)-e_t)\cdot f_t
=-\frac{13}{12}-h_2(q_*,y(t),t).
\]

The exact512-cell broad stationary-graph audit now proves
`-29/20<h2<-7/5` throughout this tilt chart. Therefore the displayed eta
lies in `(19/60,11/30)`, strictly inside `[-1/2,37/100]`. See
`BROAD_STATIONARY_GRAPH_AND_CURVATURE.md`; its graph and scalar bounds
have independent exact replays.

With these slider choices, the comparison displacement of T is parallel to
the horizontal normal and that of G is parallel to its own tilted normal.
The corresponding angle/center cross terms are quadratic in the frame error,
which is the mechanism of the center-free local theorem. The theorem itself,
including its exact broad-chart arithmetic and nonlinear remainder, is owned
by the separate local-dual proof.

## 7. Transfer back below the sharp ceiling

The sharp pair certificates concern the expanded boundary ring at `Qsharp`.
The local contradiction is applied to the ring before that expansion, at
`qtilde<q_*`. The outer-radius monotonicity bridge changes each O center by at
most `10^-16` and preserves every frame and center ray; the C centers are fixed.
Thus all canonical angle lifts and actual frame mismatches are unchanged.
Any wrong owner at the lower radius would remain a valid wrong separating axis
after expansion, contradicting the sharp owner capture. The two core slider
identities above are unchanged exactly.

This transfer is essential: applying the local lower bound only to the ring at
`Qsharp>q_*` would not give a contradiction.

## 8. Completed broad local invocation

The broad stationary graph and its reduced curvature are now proved in
`BROAD_STATIONARY_GRAPH_AND_CURVATURE.md`. The independent exact broad
coefficient audit covers all327680 owner comparisons on the full slider
rectangle, with reserve above9/500 and anchored Young constant below100.
The analytic projection-aligned remainder is proved in
`m5_agent/CENTER_FREE_PROJECTED_SLIDER_REMAINDER.md`.

These results give, for the original-radius boundary ring before expansion,

\[
\widetilde q\ge q_*+\frac{\mu_H}{2}(t-t_*)^2
 +\frac12\sum_{i=A,B,D,E,H}\mu_i|d_i|^2+\frac{13}{2500}S
\ge q_*.
\]

Since that ring was constructed at `qtilde<q_*`, this closes the long-word
contradiction. The only pair conditions used by the local theorem are the
captured seven SAT witnesses; nonneighbor overlaps in the boundary
relaxation do not affect its applicability.
