# Finite all-outer capture and sharpness interface

This component handles the remaining boundary word `OOOOOOO`. It is part of
the unrestricted seven-exterior reduction for the eight-square problem.
The ordinary domain cover has exactly45 rational exclusion inputs. The
terminal domain has a separate width budget, complementary owner checks,
and scalar geometric deductions. A sampled optimization is never counted
as one of the required pair proofs.

## Canonical choice

Let the seven centers be ordered counterclockwise, and let
\(t_i=\tan\alpha_i\in[-1,1]\) be each square's fundamental frame offset from
its center ray. Choose a label attaining the maximum of \(|t_i|\), and make
it role0. If necessary, reflect the plane and reverse the cyclic order. This
negates every fundamental tangent and preserves the all-outer word, the
physical gap sum, containment, and the pair inequalities. Thus one may assume

\[
 -1\le t_0\le0,\qquad |t_i|\le-t_0\quad(0\le i\le6).
\]

No uniqueness of the maximum is needed. On a role0 interval \([l,h]\) with
\(h\le0\), every other role can safely be restricted to \([l,-l]\).
This correlated maximum condition is essential in the upper anchor cuts;
omitting it would retain a different cyclic labeling of the same optimum.

## Gates and exact finite cover

`audit_all_outer_capture_cover.py` uses Fraction arithmetic to verify every
closed interval cover and every input-domain inclusion. For each input, it
matches the full rational geometric/potential data against the completed
manifest registry. It separately records whether our independent manifest
audit matches. Its JSON output is the current authoritative status table for
this cover; missing manifests remain explicitly pending.

| Gate | Required ordinary inputs | Retained domain or purpose |
|---|---:|---|
| Maximum offset |2|Canonical \(t_0\in[-1,-3/4]\).|
| Coarse ordered roles |14|Fix the seven role sectors; the first2 are the already proved role1 exclusions.|
| H anchor |2|\(t_0\in[-97/100,-9/10]\); apply the canonical maximum cap.|
| Near ordered roles |12|Enter the seven intervals in `all_outer_near_prefix_plan.json`.|
| Terminal ordered roles |15|Enter the exact terminal box below.|

Each ordered-prefix step restricts earlier roles to their retained intervals,
excludes the displayed closed intervals of the current role, and leaves later
roles in their preceding domains. The excluded intervals together with the
retained interval cover the entire old interval. Shared endpoints are covered
twice, so there is no endpoint gap. Canonical caps are applied only through
the proved maximum condition above.

The complete input plans are
`all_outer_coarse_prefix_v2_plan.json`,
`all_outer_anchor_low_checked_candidate.json`,
`all_outer_anchor_high_checked_candidate.json`,
`all_outer_near_prefix_plan.json`, and
`all_outer_terminal_prefix_plan.json`.
The first two maximum-offset inputs are the bound data files
`m5_agent/all_outer_far0_pair_data.json` and
`m5_agent/all_outer_far1_pair_data.json`.

All45 ordinary exclusions now have complete exact manifests and independent
binding/coverage audits. The cover checker reports45/45 exact and45/45
independent, with no pending input. The final29 certificates contain236544
genuine initial piece rectangles across231 signed branches. Their independent
audit is `all_outer_final29_independent_manifest_audits.json`; the complete
three-word ledger is `all123_ordinary_capture_independent_ledger.json`.

## Terminal box and labels

The table assigns each canonical role its name in the reflected sharp-chain
coordinates. Its tangent entries remain the canonical variables used by the
certificate, before that final geometric reflection; reflection negates the
fundamental offsets. The common named tilt below is measured after reflection.

| Role | Name | Fundamental tangent interval |
|---|---|---|
|0|H|\([-19/20,-23/25]\)|
|1|E|\([3/200,1/20]\)|
|2|D|\([173/200,9/10]\)|
|3|T|\([-61/500,-109/1000]\)|
|4|B|\([12/25,13/25]\)|
|5|A|\([-71/200,-159/500]\)|
|6|G|\([9/100,13/125]\)|

The terminal budget input is `all_outer_terminal_budget_v1.json`. Its
piecewise affine potentials have32 pieces on each declared one-sided domain,
and its denominator is \(10^{12}\). The five aligned edges1,2,3,4,6 have
charge \(\beta=1/50\); the two mixed edges0 and5 have zero charge.
Its exact cyclic lower sum is

\[
 \sum_i\gamma_i=\frac{628318482237}{10^{11}},
 \qquad \sum_i\gamma_i+\frac7{10^7}>2\pi.
\]

The last inequality uses the separately hand-derived33-place Machin upper
bound. Exact all-domain pair validation is complete for every declared edge,
including the independently checked selected/complementary composition.

## Budget and signed owners

Write \(h_i=(|\cos\phi_i|+|\sin\phi_i|-1)/2\), where
\(\phi_i=\delta_i+\arctan t_{i+1}-\arctan t_i\). Full pair bounds give

\[
 e_i=\delta_i-\beta_i h_i+\psi_{i+1}-\psi_i-\gamma_i\ge0.
\]

At physical holonomy \(\sum\delta_i=2\pi\), telescoping yields both
\(\sum_i\beta_i h_i<7/10^7\) and \(\sum_i e_i<7/10^7\).
The complementary owner input increases each threshold by exactly
\(7/10^7\) and checks every axis outside the following sets:

| Directed role edge | Allowed kernel axes | Named reference normal after reflection and, where needed, reversal |
|---|---|---|
|H→E|4|H's \(f_t\)|
|E→D|1,2|E's or D's \(f_0\)|
|D→T|1,3|D's or T's \(e_0\)|
|T→B|1,2|T's or B's \(e_0\)|
|B→A|1,3|For A→B, A's or B's \(f_0\)|
|A→G|3|For G→A, G's \(e_t\)|
|G→H|1,3|For H→G, H's or G's \(e_t\)|

The kernel numbers its positive source e/f and target e/f axes as0,1,2,3,
and their negatives as4,5,6,7. A complementary separating axis would imply
\(e_i\ge7/10^7\), contradicting the strict total residual bound.
The actual owner axis is the corresponding rotated axis of that square;
the displayed \(e_0,f_0,e_t,f_t\) are its comparison directions. Its small
rotation is retained in the sharp dual estimate.

The full-SAT budget can be assembled without circularity: certify selected
axes at \(\gamma_i\), and all complementary axes independently at the
stronger \(\gamma_i+7/10^7\). Their union proves the full pair bound before
using the physical cyclic sum. The owner implication is used only afterward.

This composition has been executed and independently audited. The selected
manifest SHA256 is
`ba4ba022bc1ca7ed8a3c89431545bc39532493790d82087269cc14dc5e407573`,
and its complementary owner manifest is
`714a000d12caca8279d2966f3667ef706ce3adb272188ec705d37b7db5498341`.
Both contain the full7168-piece cover. The independent report is
`all_outer_terminal_v1_selected_budget_independent_composition_audit.json`.

## Frame mismatch and common tilt

Let \(d_i\in[0,\pi/4]\) be the distance to the nearest quarter-turn on an
aligned edge. Concavity gives \(h_i\ge d_i/4\). Therefore the mismatch sum
\(S\) of the five aligned edges is below \(7/50000<1/1000\). On this smaller
interval, elementary sine/cosine Taylor bounds give \(h_i\ge49d_i/100\),
so in fact

\[
 S<\frac1{14000}<\frac1{10000}.
\]

`verify_all_outer_terminal_angle_lift.py` is a separate exact Fraction audit
of the potential/atan ranges. Conditional on the budget, it fixes the aligned
quarter counts on edges1,2,3,4,6 to1,0,1,0,0. The mixed edge5 then gives

\[
 t=\frac\pi2-
   \bigl(\delta_5+\arctan t_6-\arctan t_5\bigr)
   \in(1/10,4/25).
\]

Its sharper rational enclosure has decimal endpoints approximately
0.101532829186 and0.146247877713. The decimals are only display values; the
saved audit contains the exact fractions.

The already proved frame-concentration theorem and the coarse box also give
the complete sector word, independently of a small-mismatch assumption; see
`ALL_OUTER_QUARTER_WORD.md`. With A's named actual frame normalized to zero,
the canonical-frame quarter indices before the final reflection are
\((1,2,3,3,0,0,1)\) modulo4. This determines every signed normal in the table.

## The two slider coordinates

Let \(a_i=r_i/\sqrt{1+t_i^2}\). The T center, in its named frame, is
\((-a_3t_3,a_3)\), with frame deviation from A at most \(S\). Hence

\[
 |T_y-a_3|<\tfrac32 S.
\]

At the exact fixed sharp ceiling, monotonicity of the outer boundary and
rational substitutions in
\((a+1/2)^2+(|t|a+1/2)^2=Q\) give
\(1.3632<a_3<1.3693\). Thus \(T_y\) lies safely inside
\([7/12,11/8]\).

G's actual frame is the named tilt \(t\). Its center in that frame is exactly
\((a_6t_6,-a_6)\), so its reference slider projection is

\[
 \eta_G=-a_6-(h_2+1/2),
 \qquad 1.3715<a_6<1.3779.
\]

The broad stationary-reference chart supplies
\(-29/20<h_2<-7/5\). Conditional on that analytic interval bound,
`verify_all_outer_terminal_sliders.py` proves by exact rational root
substitutions that

\[
1.3630928571<T_y<1.3694071429,\qquad
-0.4779000001<\eta_G<-0.4214999999.
\]

These displayed decimal bounds are conservative rationals; the saved JSON
also records the sharper exact fractions. The estimates include a
\(10^{-16}\) allowance for the radius transfer and lie strictly inside the
common comparison rectangle
\([29/50,7/5]\times[-1/2,37/100]\).
The required \(h_2\) statement is an explicit external premise of this scalar
checker. It is now proved by the broad stationary-graph arithmetic audit,
whose512-cell independent replay is
`broad_stationary_h2_independent_replay.json`.

These scalar ranges, signed owners, and mismatch/tilt bounds are all proved.
The complete broad coefficient and nonlinear audit is
`BROAD_CENTER_FREE_SHARPNESS_INDEPENDENT_AUDIT.md`. The center-free
sharpness theorem therefore applies without capture of all center
coordinates. The fixed-Q radius-transfer lemma returns its conclusion to
any hypothetical packing below the isolated sharp value.
