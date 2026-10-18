# One-core terminal interfaces for the broad local dual

This note states the consequences of the two captured one-core domains and
their frozen angular/owner pair certificates. Both terminal budget/owner
compositions are now exactly validated on their declared domains. The finite
domain implications have an exact46-case rational audit, with all46 ordinary
pair manifests and all46 independent binding/coverage audits matched. Thus
the angular, owner, and actual boundary-state consequences below now apply
to every one-core ring after the explicit sign normalization and phase split.
The broad stationary graph, h2 range, owner-coefficient arithmetic, and
projection-aligned nonlinear remainder have all passed their separate
audits as well. The final invocation is made explicitly in Section5.

## 1. Residual budgets and actual aligned frame mismatch

For each endpoint phase define

\[
e_i=\delta_i-\beta_i h(d_i)
    +\psi_{i+1}(t_{i+1})-\psi_i(t_i)-\gamma_i,
\qquad h(d)=\frac{\cos d+\sin d-1}{2}.
\]

Here `d_i` is the square-frame distance modulo `pi/2`. The coefficient is
`1/50` on the five aligned edges, and zero on the two mixed edges:

| Phase | Counterclockwise named roles | Aligned edge indices |
|---|---|---|
| T core | reflected(T,B,A,G,H,E,D) | 0,1,3,5,6 |
| G core | (G,A,B,T,D,E,H) | 1,2,3,4,6 |

The exact pair theorem gives `e_i>=0`. Physical holonomy `sum delta_i=2pi`
and the rational sum of constants yield

\[
\sum_i e_i+\frac1{50}\sum_{\text{aligned }i}h(d_i)
<\frac9{10^7}.
\]

Thus each pair residual is below `9/10^7`. Concavity gives `h(d)>=d/4`
on the full frame interval, first proving the aligned sum `S<9/50000`.
The elementary Taylor bounds then give `h(d)>49d/100`, so

\[
\boxed{S<\frac9{98000}<\frac1{10000}.}
\]

## 2. Canonical quarter lifts and the common tilted frame

Write `alpha_i=atan(t_i)` and
`phi_i=delta_i+alpha_(i+1)-alpha_i`. The exact scalar audit, using rational
piecewise-linear ranges and alternating arctangent enclosures, places every
aligned `phi_i` within `1/4` of its displayed multiple of `pi/2`:

| Phase | Quarter indices on edges0 through6 | Mixed edge defining the tilt |
|---|---|---|
| T core | (1,0,mixed,0,mixed,1,0) | edge2 |
| G core | (mixed,0,1,0,1,mixed,0) | edge0 |

The small metric mismatch from Section1 therefore fixes the actual signed
differences from those quarter turns. Normalize A's named frame to angle0;
in the T phase undo the naming reflection. The standard frames A,B,T,D,E
then have exactly the five aligned mismatch terms used in the local dual.
Take G's actual frame as the tilted reference angle `t`. H differs from it
by its captured aligned edge mismatch. The sum is the same `S` above.

The absolute canonical sectors can also be tracked explicitly. Set A's
canonical frame angle to0. In the T phase, before undoing the reflection,
the canonical angles on roles0 through6 are respectively near
`(-pi/2,0,0,pi/2-t,pi/2-t,pi,3pi/2)`. In the G phase they are near
`(t-pi/2,0,0,pi/2,pi/2,pi,t+3pi/2)`. Entries containing G's own angle
are exact; each other discrepancy is bounded by the appropriate path sum
of aligned mismatches. The last roles use the physical lifted closure
`theta7=theta0+2pi`, which follows from `sum delta=2pi` and the periodic
alpha values. These sectors determine the positive signed axes and the
positive T height used below. In particular a reflected f-axis changes
sign relative to the f-axis of the reflected canonical frame; the owner
table keeps the original certificate indices and applies that sign change.

In both phases the named tilt is `t=pi/2-phi_mixed`. The mixed penalty is zero,
so its pair residual directly bounds `phi_mixed` through two separate
one-variable functions `psi_i(t_i)-atan(t_i)`. The exact scripts prove

\[
\boxed{\frac1{10}<t<\frac4{25}.}
\]

The audits are `one_core_t_aligned_budget_v1_angle_audit.json` and
`one_core_g_aligned_budget_v1_angle_audit.json`. The T audit uses the actually
captured role2 lower bound `-11/32`, which is stronger than the unchanged
budget input's lower bound `-23/64`.

## 3. Exactly the local dual's32 owner assignments

Use signed SAT-axis indices0 through7 in the order
`(source e, source f, target e, target f, then their negatives)`.
The frozen owner complements leave the following allowed sets:

| Edge | T-core named contact | T-core allowed | G-core named contact | G-core allowed |
|---|---|---|---|---|
| 0 | T to B | 1,2 | G to A | 1 |
| 1 | B to A | 1,3 | A to B | 1,3 |
| 2 | A to G | 3 | B to T | 3,4 |
| 3 | G to H | 1,3 | T to D | 1,3 |
| 4 | H to E | 4 | D to E | 3,4 |
| 5 | E to D | 1,2 | E to H | 2 |
| 6 | D to T | 1,3 | H to G | 1,3 |

After the canonical quarter lifts above, these sets give exactly the seven
named directions of the local dual: five aligned contacts have either owner,
G/A uses G's tilted normal, and H/E uses H's transverse normal. Hence there
are exactly32 allowed owner assignments covered by that theorem.

The owner complement is the independent pair statement that a wrong-axis
separated pair has cost at least `gamma_i+9/10^7`. It can be combined with
target-cost checks on just the allowed axes to prove the full-SAT baseline
bound. Summing that completed baseline around the physical ring gives the
strict residual cap from Section1, which makes every wrong owner impossible.
This composition avoids any circular use of the owner conclusion to assume
the pair budget. It has been exactly checked for both phases: T selected
manifest SHA256
`63b85cf8b9b0e4597e26807fba8509893984dfdfe890d3dc9c421816de360a0b`
and G selected manifest SHA256
`3e42cc4e5b0a98b1a67220e58204e66b2e0c6c6207bb6a6006f731ce7799d7ea`.
Each complete7168-piece cover independently reaudits its full wrong-axis
complement and verifies the rational deficit below9/10^7.

## 4. Projected sliders require no center proximity

Let the stationary comparison at actual tilt `t` be the one used by the broad
local dual. Choose its free sliders to match actual transverse projections:

\[
z_T=T_y,\qquad
\eta=(G-H^0(t)-e_t)\cdot f_t.
\]

Then the comparison displacement of T is parallel to the horizontal contact
normal, and that of G is parallel to its own tilted normal. The corresponding
angle/center products are quadratic in frame error; this is the hypothesis
used by the center-free local proof.

For a boundary state with signed tangent `u`, its canonical longitudinal
coordinate `a=r/sqrt(1+u^2)` satisfies

\[
(1+u^2)a^2+(1+|u|)a+1/2=q
\]

on O, while `a=7/12` on C whenever `|u|<6/7`.
The captured quarter sectors give `G dot f_t=-a_G` exactly in both phases.
Since `H^0 dot f_t=h2+1/2`,

\[
\boxed{\eta=-a_G-h2-1/2.}
\]

For T, if its small named frame error has magnitude at most `S`, the exact
sign of the transverse term is unnecessary:

\[
a_T(1-S^2/2-|u_T|S)\le T_y\le a_T(1+|u_T|S).
\]

The Fraction-only audit `verify_one_core_projected_sliders.py` proves all
outer-root substitutions uniformly for
`q in[Qsharp-3/10^16,Qsharp]`:

| Phase | T longitudinal coordinate | G longitudinal coordinate |
|---|---|---|
| T core | 7/12 | (27/20,7/5) |
| G core | (27/20,69/50) | 7/12 |

It follows that `T_y` lies in `[29/50,7/5]` in both phases. The core T lower
bound has a small reserve below `7/12`; a slightly rotated core square need
not have projected height at least `7/12` itself.

The broad-chart inequality

\[
-29/20<h2(q_*,y(t),t)<-7/5
\]

then yields eta in `(-1/2,-2/5)` for the T-core phase and eta in
`(19/60,11/30)` for the G-core phase. Both are inside the common comparison
rectangle `[-1/2,37/100]`. This h2 statement is now proved by the exact512-cell
broad stationary-graph audit in `BROAD_STATIONARY_GRAPH_AND_CURVATURE.md`.
It was independently replayed, and discharges the explicit h2 premise of
the separate slider audit.

## 5. Applying the contradiction below the candidate radius

For an original hypothetical `q<q_*`, replace q by
`qtilde=max(q,q0)<q_*`, with the rational `q0` supplied by the root isolating
interval and `Qsharp-q0<=3/10^16`. Apply radial boundary reduction at qtilde,
then expand O radii to Qsharp for the exact finite capture.

The outer-radius monotonicity theorem preserves every feasible SAT axis,
all canonical tangents, center rays, and frames. Thus all angle and owner
conclusions established at Qsharp hold for the boundary ring before
expansion as well. In particular a wrong axis below Qsharp would remain a
wrong feasible separator after expansion, a contradiction. The change in
each outer center is at most `1/10^16`; the root substitutions in Section4
already cover the entire lower-radius interval directly.

The broad center-free local dual is finally applied at qtilde, using the
captured owners, `S<1/10000`, actual tilt in `[1/10,4/25]`, and the two
projected sliders in their proved rectangle. Its now-audited bound is

\[
\widetilde q\ge q_*+\frac{\mu_H}{2}(t-t_*)^2
 +\frac12\sum_{i=A,B,D,E,H}\mu_i|d_i|^2+\frac{13}{2500}S
\ge q_*.
\]

The exact broad coefficient check is
`audit_capture/verify_broad_dual_coefficients_independently.py`; the full
nonlinear remainder derivation is
`m5_agent/CENTER_FREE_PROJECTED_SLIDER_REMAINDER.md`. It uses12S^2 of pure
angular loss,100S^2 from anchored Young absorption, and16S^2 from the two
projection-aligned sliders. The latter terms are quadratic because
`(R(a)n-n) dot(d n)=d(cos a-1)`. No small anchored-center neighborhood is
assumed. The displayed lower bound contradicts the chosen qtilde.
Applying that bound only to the expanded Qsharp ring would not establish
the contradiction.
