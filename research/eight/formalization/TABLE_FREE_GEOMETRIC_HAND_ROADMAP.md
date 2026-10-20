# Table-free hand proof: the hard class is sharp; global capture remains

**PR #10:** `formalize/eight-uncompiled-draft`.
**Mode:** hand mathematics only; no Lean changes, compilation, or CI.
**Target:** the unrestricted sharp eight-unit-square radius theorem and
its complete five-parameter equality family, without a numerical lookup
table in the mathematical dependency chain.

## 1. Current mathematical status — 19–20 October 2026 UTC

The unrestricted table-free proof is **not complete**. Its remaining
substantive work is global candidate capture. After G0--G2 and the E-sign
normalization, `S<=3/200` suffices for one complete downstream chain.
All six tangent cuts follow from that bound without any prior cut or
preferred mixed owner. A second route now closes the entire aligned
hard-quarter class, without any mismatch hypothesis, by explicit
radius-preserving reductions. Its signed three-zero bridge also closes
the original ordered class with HG2/TD0 and the stated remaining owners.
The full ordered outer-error extension now admits all signs of
both outer errors and all four outer owner combinations, and
no longer assumes the G/T transverse signs. Its frame order
and specified hard/mixed owners remain explicit. It retains
the complete original-center equality conclusion. For the already aligned
three-zero class, every frame-order assumption has now been
removed: the H/D span is necessarily positive, a common A/B
frame outside D--H clamps to the nearer endpoint with strict
circle loss, and the E-frame reduction retains that loss.
The missing global step must supply either complete route's entry
hypotheses; neither is asserted for arbitrary candidates.

The old final contraction `S<=3/200 => S<1/1000` is now **unnecessary**.
Mixed-owner rigidity, both tilt signs, the complete positive tilt tails,
the sharp terminal, and the equality classification have a forward hand
chain at `S<=3/200`. The new tilt and terminal use the same actual
ED-owner/H frame; no unjustified conversion to the old A/G tilt is used.

| Gate | Hand-proof status | Exact boundary |
|---|---|---|
| G0 | Closed on paper | Central core, physical gaps, fixed-axis boundary reduction and documented radius transfer. |
| G1 | Closed on paper | Complete four-type frame concentration; real frame spread below 7/10. |
| G2 | Closed on paper | All six wrong words excluded; only 0101011 survives. Reflection gives the weak E sign. |
| G3 | All six cuts closed conditionally at S<=3/200 | Cut-free quarter owners first give four cuts at S<=1/32; complete H-low exclusions then give H>1/2, followed by G>-4/5. No tangent cut is an independent missing input after small mismatch. |
| G4 | Global capture open; ordered AB alignment covers all outer errors and G/T signs | The original ordered HG2/TD0 class reduces to five anchors with strict loss off zero. AB alignment now covers every outer-owner/error pattern, including both wrong intermediate signs simultaneously, under the retained H/A/B/D signs and frame order. Coarse mismatch bounds S<2/5 and S<13/50 remain open. |
| G5 | Entire ordered hard-owner class sharp without G/T sign assumptions | Both outer errors and both intermediate transverse coordinates may have either sign. Wrong intermediate signs reach a zero endpoint with strict middle-circle loss; the existing complete reduction then applies. The already aligned-three-zero class needs no frame-order hypothesis. Global owner capture and alignment without frame order remain open. |
| G6 | DE closed globally; forbidden BT has a global three-edge return bound | Every original DE witness is in {2,3}. A feasible BT0/1 forces A positive; its complete E--H--G--A return now has linear-A charge greater than 103/40, covering every return owner and radial kind. The complementary four-edge lower bound remains open. |
| G7 | Closed conditionally at S<=3/200; old contraction retired | Every original mixed owner is G0/E1, without an S<=1/1000 premise. |
| G8 | Closed conditionally at S<=3/200 | t>S and 1/10<tau<4/25, where tau is the actual ED-owner/H frame difference. |
| G9 | Closed conditionally at S<=3/200 | Sharp owner-frame inequality with S/5000, all five completed anchors, and the full equality family. |
| G10 | Open pending global entry into a completed route | The original-center transfer at S<=3/200, the ordered hard-owner class without G/T sign assumptions, and the aligned-three-zero class without frame order are proved, including equality. Arbitrary candidates are not yet captured by a completed route. |

These are mathematical hand-proof statuses, not Lean verification claims.
Historical certificate files and the uncompiled Lean draft remain unchanged.
Removing a mathematical dependency does not claim that its old Lean import
has already been removed or that compilation time has been measured.

## 2. Exact remaining global problem

Use cyclic roles `(H,G,A,B,T,D,E)` and the surviving quarter word

\[
 k=(0,1,0,1,0,1,1),\qquad m=(0,0,1,1,2,2,3).
\]

An own-frame center is `(a_i,-sigma_i b_i)`, with `a_i>=b_i>=0` and
signed tangent `u_i=sigma_i b_i/a_i`. Let d_i be its real frame increment
after subtracting the prescribed quarter turn. The entry theorems give

\[
 \sum_i d_i=0,\quad |d_i|<7/10,
\]
\[
 g_i=k_i\pi/2+d_i+\sigma_i\arctan(b_i/a_i)
                  -\sigma_{i+1}\arctan(b_{i+1}/a_{i+1})>19/25,
 \qquad\sum_i g_i=2\pi.
\]

The mismatch is

\[
 I=\{H,A,B,T,D\},\qquad S=\sum_{i\in I}|d_i|.
\]

The two remaining errors belong to the same closed frame tour. They
cannot be assigned independent angular budgets. Every actual edge has
at least one feasible original signed SAT witness; only the already
proved zero-primary exclusion can restrict owners before later gates.

### G3: all six tangent cuts follow after small mismatch

The reflection alone proves `u_E<=0`. The additional bound `S<=3/200`
now supplies all six cuts

\[
 -4/5<u_G<-1/20,\qquad 1/20<u_T<4/5,
 \qquad u_H>1/2,\qquad u_D<-1/2.
\]

This is a forward reordering of the historical route. The small-mismatch
proofs below cannot be used to assume cuts while proving that same bound
on S. Existing fitted arc values are not hand premises.

[The original-center norm theorem](HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md)
now gives `|p|<283/200` and the all-original-axis nominal inequality
`P_nominal>=1-|d|` for `|d|<=3/10`. It also excludes GA axis 0 on the
full high-G tail and forces that tail to have negative A/G tilt once
the earlier A sign is available. The remaining negative-tilt tail is
not excluded by those implications.

[The global DE cyclic-marker theorem](HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md)
now proves every original DE owner belongs to `{2,3}` and `u_D<0`
from G0--G2 and `u_E<=0`, with no mismatch bound, tangent cut,
zero-owner input or preferred mixed owner. Each forbidden axis forces
a common-marker edge charge greater than one on the entire frame
interval. The six-edge G1 return path then exceeds the full cyclic
angular budget. The same estimates exclude both intended axes when
D has nonnegative sign. The witness-preserving boundary transfer
keeps the conclusion valid for original centers and tied axes.

[The global zero-owner sign theorem](HAND_G3_GLOBAL_ZERO_OWNER_SIGN_RIGIDITY.md)
also proves `axis0=>y_source>0` and `axis2=>y_target<0` on every
original zero edge. It needs no mismatch bound, tangent cut, E
normalization, or quarter/mixed owner input. A putative offending
sign forces a positive increment in `(29/100,7/10)`; one actual
circle support and one strictly concave scalar give a boosted common
marker charge above one on that entire interval. The six-edge
return path excludes it. If both transverse owners are feasible,
both signs follow. A single owner supplies only its stated one-sided
sign; the full six-sign tuple has not been proved globally.

Section 11 of the global DE note now makes the generic quarter
consequences explicit: every original quarter axis 0 or 1 forces
its target sign positive, and every original quarter axis 2 or 3
forces its source sign negative. The local reflected reversal maps
the original indices `0<->2`, `1<->3` and preserves the actual
marker charge and error. Together with the zero-owner theorem,
these implications supply all six signs for the hard original
HG2/GA0/AB0-or-2/BT2/TD0/DE3/EH1 class before any mismatch
bound. Its six signs are therefore no longer separate entry
assumptions once those original owners are supplied.

[The global zero--quarter propagation theorem](HAND_G3_GLOBAL_A_SIGN_UNDER_FORBIDDEN_B_OWNER.md)
now also proves that an original BT0/1 witness forces `y_A>0`,
without a mismatch, E sign, tangent cut, or other quarter owner.
Under the contrary weak A sign, the actual AB2 and BT path has
common-marker charge greater than `19/10`; the original five-edge
return exceeds the full cyclic budget. Its BT1 positive-error case
retains both the B and T circles and reduces a complete angle
triangle to one harmonic boundary. Generically, a zero edge
followed by a quarter axis 0/1 forces both outer endpoints
positive; the reflected quarter axis 2/3 followed by a zero edge
forces both outer endpoints negative. The A-positive forbidden-BT
branch itself remains open globally.

[The whole-chart marker and negative-AB comparison](HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md)
supplies the global bounds `F>=.86b` and
`F_O<=3(a-a_0)/8+1.091b`. Its exact negative-AB dual comparison
also retains a positive reserve under the stated source-weight
and complementary-charge hypotheses. These are analytic helpers
for that remaining branch, not an assertion that it is excluded.

[The global linear-A return theorem](HAND_G3_GLOBAL_RETURN_WITH_LINEAR_A_CHARGE.md)
now proves `pi+r+v+t-(49/50)b_A-F_E>103/40` on E--H--G--A,
using only the weak E-negative and A-positive endpoint signs.
It includes every original quarter owner, both zero owners,
all intermediate signs and both radial kinds. When the three
absolute errors total at most `.3`, their actual nominal
projections give `b_A<=4c_0-3+R`; the unchanged G1 charge
retains a gain in R. One strongly convex high-chart scalar
and one rational reference point give the full return bound.
Thus a complementary AB--BT--TD--DE charge at least
`16761/4520` would close the remaining forbidden-BT branch.
That complementary inequality is still an explicit open task.

[The earlier DE-owner theorem at S<=1/32](HAND_G3_D_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md)
remains valid and is used in the already completed conditional
downstream proofs, but its mismatch input is no longer needed for
the DE conclusion itself. The new global result does not supply
the bound on S, the other quarter owner, or the stronger D tangent
cut `u_D<-1/2`.

[The complete BT-owner theorem without tangent cuts](HAND_G3_B_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md)
now supplies the other quarter edge from exactly those same inputs,
using DE first. It covers every original GA/EH witness and both tilt
signs with explicit circle stresses. Thus the whole G6 owner conclusion
is available before any G3 tangent cut once `S<=1/32` is known.

[The four-cut theorem](HAND_G3_FOUR_CUTS_AT_ONE_THIRTY_SECOND.md) then
proves, in forward order, `u_G<-1/20`, `1/20<u_T<4/5`, and `u_D<-1/2`
at `S<=1/32`, without any earlier cut. The first three conclusions use
the original zero edges and AB--BT path; D uses the newly proved BT
owner.

At `S<=3/200`, [the complete H-low high-index stresses](HAND_G3_H_LOW_HIGH_INDEX_STRESSES_AT_THREE_TWO_HUNDREDTHS.md)
exclude GA0 and GA2 on their entire arcs, all nonnegative GA tilts,
and five of the remaining negative-tilt GA/EH pairs under `u_H<=1/2`.
[The three primary-pair stresses](HAND_G3_H_LOW_PRIMARY_BRANCHES_AT_THREE_TWO_HUNDREDTHS.md)
exclude the other three pairs. They retain the same original centers,
the exact shared EH error sum, and both owners on every aligned edge.
The last three four-circle cases use continuous rational weights,
explicit polynomial positivity, signed first-order cancellation, and a
single shared Taylor remainder. Together the two notes prove `u_H>1/2`
without an earlier H or G cut.

[The high-G theorem from the H cone](HAND_G3_HIGH_G_CUT_FROM_H_CONE_AT_THREE_TWO_HUNDREDTHS.md)
then proves `u_G>-4/5`, using only the now-established weak H cone as its
extra tangent input. [The all-cuts assembly](HAND_G3_ALL_CUTS_AT_THREE_TWO_HUNDREDTHS.md)
states the complete conditional theorem and covers every original owner,
including weak ties. No tangent cut remains an independent prerequisite
after `S<=3/200`; that mismatch bound itself is still unproved globally.

### G4: the missing coarse mismatch bounds

Under only the cuts actually established at that point, prove

\[
                            S<2/5,\qquad S<13/50.
\]

The proved closed-tour charge compression says, for
`U_K=sum_(i in K) h(|d_i|)` and `h(x)=(sin x+cos x-1)/2`,

\[
 S\ge2/5\Longrightarrow U_I+(19/125)U_{I^c}>1117/6250,
\]
\[
 S\ge13/50\Longrightarrow U_I+(17/200)U_{I^c}>12119/100000.
\]

These are consequences of a bad mismatch, not the still-missing geometric
upper bounds. See [closed-tour compression](HAND_CLOSED_TOUR_CHARGE_COMPRESSION.md)
and [the exact cycle-stress interface](HAND_CYCLE_STRESS_INTERFACE.md).

[The all-sign linear zero-edge theorem](HAND_G4_ALL_SIGN_ZERO_LINEAR_CHARGE.md)
now covers both signs of the full frame increment, every original
transverse sign and radial state, and both original zero owners on all
three zero-quarter edges. With `p=49/50` it proves
`d-h(|d|)/50+p(max(y_source,0)+max(-y_target,0)-1)>=0`, strictly off
zero. Its six explicit clipped role labels are shared between incident
edges. One polynomial with a whole-interval curvature bound supplies
the complete negative-increment branch. Historical affine labels
cannot be combined with the new zero labels as if they telescoped.

[The exact independent-pair obstruction](HAND_G4_CLIPPED_LINEAR_PAIR_BUDGET_OBSTRUCTION.md)
now shows that these six clipped labels cannot be completed by
independently quantified constant pair bounds with a useful charge
budget. Four original aligned quarter test pairs, using an identical
E state, force a cyclic constant deficit greater than `539/5000`;
each aligned zero constant is at most zero. These are local tests,
not a feasible common cycle. A successful argument must retain shared
vertices or change the labels, rather than fit four more independent
constants to this particular design.

[The coupled aligned-zero/E-zero exclusion](HAND_G4_ALIGNED_ZERO_E_ZERO_BRANCH_EXCLUSION.md)
does retain all seven original shared centers. On its explicit
frame/owner branch, monotone elimination reduces to a two-variable
scalar whose Hessian has a uniform negative reserve. One rational
comparison point excludes the entire branch at Q0 without assuming
contact or outer-boundary equalities. The result is a conditional
branch theorem, not a reduction of arbitrary cycles to that branch.

[The E-interior boundary reduction](HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md)
keeps the other six original vertices fixed on the stated aligned-zero
branch. The two actual E contacts give an explicit one-variable corner
function with strictly negative second derivative on its whole interval.
An auxiliary minimum of the E corner therefore lies on `b_E=0`, DE
alignment, or EH alignment. If a lower mismatch constraint `S>=s0` is
retained, the additional boundary `S=s0` must also be retained. This is
a continuous boundary reduction, not an assertion that E can always be
set to zero or that a bad-mismatch condition survives the deformation.

### G5: the two missing middle contractions

In forward order, prove

\[
 S\le13/50\Longrightarrow S<1/10,
 \qquad S\le1/10\Longrightarrow S<3/200.
\]

Already at the first input threshold,
[the three-edge endpoint-sign theorem](HAND_COARSE_AD_SIGN_RIGIDITY.md)
gives `u_A>0` and `u_D<0` from `S<=13/50`, without any candidate tangent
cut, quarter/mixed owner or later sign theorem. Its actual proof uses only
`|d_A|+|d_B|+|d_T|<=13/50`, retaining the shared error budget and all
original BT witnesses. This is a conditional sign result; it does not
establish the bound on S or either contraction. Its D-sign conclusion
is now also available without that mismatch input from the global
DE cyclic-marker theorem above.

Between the two contraction steps,
[the zero-edge sign theorem](HAND_ZERO_EDGE_SIGN_RIGIDITY_AT_ONE_TENTH.md)
already gives `(sigma_H,sigma_G,sigma_A,sigma_B,sigma_T,sigma_D)
=(+,-,+,-,+,-)` from `S<=1/10`, without G/T/H/D cuts or a preferred
SAT owner. Together with reflection, E has its weak negative sign.
Do not use those signs to justify the preceding contraction.

[The signed middle zero-edge theorem](HAND_G5_SIGNED_ZERO_COERCIVITY_AT_ONE_TENTH.md)
also proves `b+B+d>=1+|d|/32` at `S<=1/10`, and hence the larger
charge `d-h(|d|)/16+b+B-1>=0` on both increment signs and all original
zero owners. It preserves the signed d term for a later cyclic sum.
The quarter/mixed estimates compatible with this linear potential
remain missing, so neither G5 contraction is marked closed.

[The exact ED scalar obstruction](HAND_G5_ED_SCALAR_OBSTRUCTION.md)
rules out extending the unchanged stationary scalar to `S<=1/10`
merely by sharpening Taylor bounds. With only a positive D-owned ED
error `x=1/10`, its exact correction is negative throughout the
stationary tilt interval. This is a failure of that eliminated-scalar
proof, not a feasible packing or a counterexample. A larger-range
argument must retain additional original-center constraints or adapt
the stress.

[The shared-center forward reduction](HAND_G5_SHARED_CENTER_FORWARD_REDUCTION_AT_ONE_TENTH.md)
now retains all five signed errors and the unchanged E corner through
the E--D--T--B--A--H chain. Under explicitly retained original GA0/EH1
and intended BT/DE witnesses at `S<=1/10`, it proves the necessary
scalar inequality `K1^2+K2^2<=Q0` with fully specified cap formulas.
Positivity on the proposed contraction annulus remains an analytic
target, and those owner hypotheses are not yet supplied at this scale.

[The E-zero split theorem](HAND_G5_E_ZERO_HARD_QUARTER_SPLIT_EXCLUSION.md)
extends the preceding coupled branch exclusion to every nonnegative
split of its total frame span between GA and the negative BT error.
A single positive factorization proves convexity of the circular cap;
the two endpoints inherit the already proved scalar deficit. It yields
an exact `149/625000` deficit in the shared A/B transverse-corner sum.
It still assumes E zero, all three zero edges aligned, and the stated
original quarter/mixed witnesses. Negative E coordinates, nonzero
zero-edge errors and the remaining original owner alternatives are
not covered by this branch result.

## 3. A completed alternative: the entire hard-quarter class

[The sharp hard-class assembly](HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md)
proves `q>=q_*` for the full five-anchor system obtained by canceling
G/T from the three aligned zero edges, with GA0, BT2, DE3 and EH1,
the intended transverse signs, and every nonnegative split
`t+u=delta+epsilon=alpha<=7/10`. No bound on `u+delta` or on an
earlier mismatch is used. Its equality theorem fixes the original
five anchors and forces `u=delta=0`, `t=epsilon=t_*`.

The first three shared-anchor inequalities force `0<alpha<11/50`.
The E-zero theorem above and
[the complete epsilon-zero exclusion](HAND_G5_ALIGNED_HARD_EPSILON_ZERO_EXCLUSION.md)
exclude both sign/outer-orientation endpoints. The E-interior
reduction therefore moves only E to `delta=0`, preserving the
other anchors and the actual circle ceiling. Any positive original
delta leaves a strictly smaller E corner value.

[The full feasible-cap convexity theorem](HAND_G5_HARD_SPLIT_CONVEXITY_FULL_FEASIBLE_CAP_RANGE.md)
then moves the A/B common frame to a split endpoint. Its two cap
functions use the separate actual A and B corner ceilings, so
inherited strict corner slack is retained. The whole-arc
[GA/DE endpoint exclusion](HAND_G5_ALIGNED_GA_DE_ENDPOINT_EXCLUSION.md)
rules out `t=delta=0`; the surviving endpoint has `u=delta=0`.
The existing nominal tails give its tilt window, after which a
five-circle stationary identity proves the sharp bound directly.
Every positive circle mass forces equality in each original anchor,
so the strict slack retained by either reduction also proves the
original-orientation equality statement.

[The E-order descent theorem](HAND_G5_E_ORDER_FROM_ALIGNED_NON_E_CHAIN.md)
removes E's order assumption once the three zero edges and the
non-E order are established. The shared chain forces an outside
E primary above one; its exact two-contact corner derivative
then excludes E above H and moves E below D strictly to D.
The zero-transverse obstruction is handled by reflection only
at zero, where E's sign is preserved. The strict E-circle loss
retains original equality. This does not yet order an arbitrary
non-E chain or align its original zero edges.

[The shared-center A/B alignment comparison](HAND_G5_AB_SHARED_CENTER_ALIGNMENT_COMPARISON.md)
and [the signed three-zero reduction](HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md)
provide an original-candidate bridge. With the stated signs
(now automatic from G0--G2 and this original-owner class),
`theta_D<=theta_A,theta_B<=theta_H`, `theta_D<=theta_E<=theta_H`,
and original axes HG2, GA0, AB0/2, BT2, TD0, DE3, EH1, the bridge
aligns all three zero differences in the necessary five-anchor
system at the actual radius. H, D and E remain fixed. Every
nonzero original zero difference leaves strict A/B circle slack.
Section 8 of the sharp assembly consequently proves the complete
lower bound and equality classification for this original ordered
class, without a mismatch premise.

For positive HG0 and reflected TD2,
[the noncanceling positive-owner reduction](HAND_G5_POSITIVE_HG_ZERO_OWNER_BOUNDARY_REDUCTION.md)
retains the exact intermediate circle and supplies a constant cap
compatible with the A/B alignment argument. Once the adjacent
middle tangent is at least one half it aligns with strict slack;
after the opposite side aligns, the other positive side reduces
on its entire feasible error interval to alignment or to a G/T
zero-transverse endpoint. That endpoint is now excluded:
[the active-circle geometry](HAND_G5_G_ZERO_ENDPOINT_EXCLUSION.md)
forces `h>.107` and `alpha+h<.311`, and
[two explicit affine stress formulas](HAND_G5_G_ZERO_TWO_AFFINE_STRESS_SCALARS.md)
give a strict reserve greater than `13/50000` throughout the
resulting domain. The scalar theorem allows either sign of E,
so reflection also covers T-zero. No enlarged intermediate-frame
span is assumed to remain below its original bound.

[The nonnegative outer-error assembly](HAND_G5_NONNEGATIVE_OUTER_OWNERS_SHARP_REDUCTION.md)
therefore closes all four HG0/2 and TD0/2 combinations on the
entire ordered class with nonnegative outer errors and the
stated signs. Every nonzero original zero difference leaves
strict A/B circle loss through the reductions. Separate A/B
ceilings and positive terminal circle masses recover equality
for the original centers, and hence the full five-parameter
family for an original packing in this class.

For negative HG0 and reflected TD2,
[the exact-core transport](HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md)
proves same-anchor alignment when the adjacent middle tangent is
at most one half. It also restores a crossed quarter frame at an
actual core G/T state. For the remaining ordered negative class,
the shared chain still forces `alpha<.27` and retains the E
boundary minimization. The
[endpoint with only the negative outer error remaining](HAND_G5_NEGATIVE_HG_ONLY_ERROR_ENDPOINT_EXCLUSION.md)
is impossible for every E split and either E sign: two retained
circle concavities reduce it to an explicit positive concave
quartic. The complete nonpositive-error assembly below handles
the remaining large-tangent alternatives without asserting that
an arbitrary chain reaches this one-error endpoint.

[AB alignment with all ordered outer errors](HAND_G5_AB_ALIGNMENT_WITH_ALL_ORDERED_OUTER_ERRORS.md)
now supplies the common A/B frame before these reductions.
A negative intermediate frame has a continuous cap through the
crossing with A or B; its crossing derivative exceeds `320/233`.
The same two original AB owner comparisons therefore remain
valid. Normalizing the transverse sum to one leaves at most
one middle tangent above one half. All constructions retain the
actual radius and preserve or recreate strict A/B circle loss.
This theorem retains the original normal-sign, frame-order and
hard-quarter-owner hypotheses.

[The two-sided E-zero deletion theorem](HAND_G5_NEGATIVE_OUTER_E_ZERO_ERROR_DELETION.md)
now excludes E-zero throughout the AB-aligned class with either
or both negative noncanceling outer errors. Small transverse
coordinates absorb their errors into the adjacent hard tilt;
large transverse coordinates delete their errors from the
corresponding E angles. Both operations retain the same A/B
circles and give the already excluded aligned E-zero split.

[The large-transverse DE-alignment theorem](HAND_G5_NEGATIVE_HG_LARGE_TRANSVERSE_DE_ALIGNMENT_EXCLUSION.md)
excludes the entire `t+u+e=alpha<=.27` simplex when `b_A>=.5`
and `delta=0`, at `Q1`. Two explicit cubic weight formulas and
whole-interval derivative bounds cover the simplex with a
single common stress at each alpha. This theorem allows either
E sign. The separate `epsilon=0` exclusion uses nonnegative
E magnitude; after reflection its sign hypothesis must still
be checked. After both other E endpoints are excluded on the
large-B branch, the surviving canonical boundary is now closed
by the following capture and terminal.

On that canonical negative boundary, the
[small-error terminal](HAND_G5_CANONICAL_NEGATIVE_BOUNDARY_SMALL_ERROR_TERMINAL.md)
proves the sharp lower bound and five-anchor equality
when its two errors total at most `3/200`. It reconstructs both
discarded intermediates on the true core while keeping all five
anchors fixed, then applies the exact circle identity and its
proved analytic estimates directly. It does not assume that
the auxiliary system has new physical gaps or G1 membership.
[The full canonical negative capture](HAND_G5_NEGATIVE_CANONICAL_SMALL_ERROR_CAPTURE.md)
now proves that two-error bound on the entire boundary. Two
continuous cubic stress families, each common to the complete
fixed-span simplex, reduce its truncation to four intrinsic
vertices. Explicit rational polynomial inequalities make every
vertex stress positive. The fixed `3/200` sine and cosine are
enclosed independently; no extra circle identity is imposed on
their rational approximants.

[The nonpositive outer-error assembly](HAND_G5_NONPOSITIVE_OUTER_OWNERS_SHARP_REDUCTION.md)
therefore proves the sharp bound and original-center equality
for all four outer-owner combinations when both original outer
differences are nonpositive. Negative canceling errors, crossed
intermediate frames, AB movement and the small-transverse
transport all retain strict middle-circle loss. The only
remaining large-B error reaches the direct canonical terminal,
which forces it to vanish at equality. Reapplying the aligned
theorem to the original anchors then supplies their unique
stationary values and the complete original equality family.

[The mixed G/T-zero domain theorem](HAND_G5_MIXED_G_ZERO_NEGATIVE_DOMAIN.md)
now proves the same endpoint domain opposite a large-transverse
negative error: `h>.107`, `alpha+h<.311`, and opposite total
error below `.12`. Its two convex cap endpoints retain the
same B circle and the exact true-core comparison. The
[mixed stress extension](HAND_G5_MIXED_G_ZERO_NEGATIVE_STRESS_EXTENSION.md)
then uses the unchanged affine weights and proves that the
negative error adds more than `3e/1000` to their positive
scalar margin. Its full derivative bounds allow either E sign.

[The all-outer-sign ordered assembly](HAND_G5_ALL_OUTER_SIGNS_ORDERED_SHARP_REDUCTION.md)
therefore closes both mixed sign possibilities as well. After
AB alignment, it processes the larger tangent first, then
aligns the smaller tangent by excluding either zero-transverse
endpoint. Only an aligned system or the already resolved
single large-tangent negative error can remain. Every strict
circle loss survives, and equality is recovered for the
original centers. No sign of either outer frame difference is
an entry assumption for this complete ordered-class theorem.

[The arbitrary-intermediate-sign AB extension](HAND_G5_AB_ALIGNMENT_WITH_ARBITRARY_INTERMEDIATE_SIGNS.md)
now permits both wrong G/T signs before AB alignment. Its
exact correlated cap has a uniform slope above `11/10`, and
the reflected construction retains the actual E constraints.
[The intermediate-sign removal](HAND_G5_INTERMEDIATE_SIGN_REMOVAL_IN_ORDERED_HARD_CLASS.md)
then moves either wrong sign to transverse zero along a
strictly monotone continuous path. It creates a strict loss
at the corresponding middle circle, even if both signs were
initially wrong. The large-middle-first reduction then joins
the preceding complete ordered theorem. Its positive circle
masses force both original intermediate signs to be normal
at equality, after which reapplication to the original
centers gives the full stationary equality classification.

[The common A/B-frame clamp](HAND_G5_COMMON_AB_FRAME_CLAMP.md)
removes the A/B placement assumption once the three zeros
are aligned and the H/D span is positive. Its signed-quarter
cap comparison has a uniform derivative gap `129/1864`;
moving an outside common frame to the nearer endpoint
strictly lowers both middle circle values.
[The angle-free outer-primary bound](HAND_G5_POSITIVE_HD_SPAN_WITH_ALIGNED_ZEROS.md)
then proves `a_H+a_D<2` for every signed pair of hard-quarter
angles. The mixed constraints force the reverse inequality
if `theta_H<=theta_D`, so the positive span is automatic.
Combined with the existing E-frame reduction, these lemmas
prove sharpness and original-anchor equality for the entire
aligned-three-zero normal-sign hard-owner class, with no
frame-order entry assumption.

Alignment of arbitrary original zero frames without an
order hypothesis, the remaining global sign alternatives,
and the remaining original quarter/mixed witnesses are still
entry obligations. The completed conditional theorems must
not be used to assume them for the unrestricted problem.

## 4. Completed entry and word dependencies

[Central-band identities](HAND_CENTRAL_BANDS_WITHOUT_TABLES.md), with their
specified analytic central-existence and forbidden-width arguments,
supply the core and physical gaps.
[Exterior-frame concentration](../HAND_EXTERIOR_FRAME_CONCENTRATION.md)
assembles the full table-free four-type pair proofs and the closed tour.

[Zero-primary cyclic exclusion](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md)
excludes every originally feasible zero-primary witness before any
candidate cut or mismatch contraction. It is a theorem about the actual
cycle, not an independently quantified local pair assertion.
[The global core-cycle theorem](HAND_GLOBAL_CORE_CYCLE.md) similarly
restricts neighboring core/core edges only in a coherent cycle.

[Quarter-word selection](HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES.md)
assembles every wrong word without the old numerical gap appendix.
Its two residual component assemblies are
[0011011](HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES.md) and
[0010111](HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES.md).
The only surviving word is 0101011. Its reflection changes E's sign and
preserves the whole word, giving `u_E<=0`.

## 5. The completed downstream chain at S<=3/200

This section is a **conditional theorem**, not a claim that an arbitrary
packing satisfies its inputs. Work with an actual G0--G2 candidate,
normalized by `y_E<=0`, satisfying `S<=3/200`. Retain original core
avoidance, corner containment, and the full original separating-axis
disjunctions. For the lower-bound problem it suffices to consider
squared radius at most `Q1=1957767069/500000000`, because the stationary
construction proves `q_*<Q1`. The owner lemmas use the weaker ceiling
`Q0=9789/2500`.

First apply [the complete small-mismatch cut theorem](HAND_G3_ALL_CUTS_AT_THREE_TWO_HUNDREDTHS.md).
It derives all six tangent cuts, all six zero-edge signs, and every
intended quarter owner from exactly these inputs. Its forward proof
starts with [quarter-owner rigidity without tangent cuts](HAND_G3_B_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md),
which is valid on the larger `S<=1/32` range. The earlier proof in
`HAND_QUARTER_OWNER_CLOSURE.md` remains available, but none of its
tangent-cut prerequisites is an additional input to this assembly.
The complete mixed-owner extension is then assembled by

- [E2/E3 exclusion](HAND_E_OWNER_CHAIN_AT_THREE_TWO_HUNDREDTHS.md);
- [G2/G3 exclusion](HAND_G_HIGH_INDEX_OWNERS_AT_THREE_TWO_HUNDREDTHS.md);
- [near-zero mixed-tilt exclusion](HAND_NEAR_ZERO_MIXED_TILT_AT_THREE_TWO_HUNDREDTHS.md);
- [positive G1/E1 exclusion](HAND_MIXED_PRIMARY_AT_THREE_TWO_HUNDREDTHS.md);
- [full mixed-owner rigidity](HAND_MIXED_OWNER_CLOSURE_AT_THREE_TWO_HUNDREDTHS.md).

They prove the original zero-based owner sets

\[
 (\{0,2\},\{0\},\{0,2\},\{2,3\},\{0,2\},\{2,3\},\{1\})
\]

for **every** feasible original witness, including ties. No final
mismatch contraction or tilt window is an input to those lemmas.

Next, [the full negative-tilt proof](HAND_NEGATIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md)
combines with the near-zero theorem to prove `t>S`.
Choose the actual ED owner once, call its physical frame d0, and set
`tau=theta_H-d0`. The
[owner-frame positive-tail theorem](HAND_OWNER_GAUGE_POSITIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md)
proves

\[
                              1/10<\tau<4/25.
\]

Its exact seven-force identity makes `F_E=delta f_0-epsilon f_tau`
constant in all five errors at fixed tau. Thus the inverse-sine E-norm
remainder is absent. The proof uses one continuous stress and one shared
error budget on both full positive tails.

Finally, apply the [sharp owner-frame terminal](HAND_OWNER_GAUGE_SHARP_TERMINAL_AT_THREE_TWO_HUNDREDTHS.md)
with this **same** tau and the same selected owners. Its stationary strip
`1-.7 tan(tau)<u<1-.6 tan(tau)` and whole-domain torque estimates give

\[
 r_0\ge q_*+\mu_H M(q_*,\tau)
 +\sum_{i=A,B,D,E,H}\mu_i
       \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +S/5000\ge q_*.
\]

At equality, S=0, tau=t_*, and all five actual anchors are fixed.
[The full weak five-parameter equality family](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md)
and its converse then apply. Its stationary prerequisites are
[existence and uniqueness](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md),
[position and slider bounds](HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS.md),
and [the original continuous weight identities](HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md).

The owner-frame tilt is not silently substituted for the old A/G tilt:
only `|tau-t|<=S` holds before rigidity. The new terminal was proved in
the frame actually delivered by capture. At equality S=0 the frames
coincide as required.

**Therefore the entire S<=3/200 downstream chain is complete.** The old
`3/200 to 1/1000` contraction and the old small-mismatch positive-tail
and terminal estimates are not premises of this route. The earlier
direct-E support theorem remains valid but is not needed for this assembly.

The [updated fixed-ceiling transfer](HAND_FIXED_CEILING_TRANSFER_AT_THREE_TWO_HUNDREDTHS.md)
proves the complete boundary/radius and original-center implication for
this new terminal. It preserves initially selected signed witnesses
through the boundary deformation, preserves rays and tau during the
outer-radius expansion, and restores the already feasible lower-radius
boundary cycle before applying the terminal. At equality it reapplies
the zero-error stationary identity to the original centers. It requires
only the table-free broad radius bounds `3.9154<q_*<Q1` and no final
contraction. Global mismatch capture remains its explicit missing input;
the tangent cuts are now consequences of that one input.

## 6. Proof discipline and exact global stopping condition

A gate closes only on its entire continuous domain: both signs, all
original feasible axes, chart joins, outer endpoints and weak ties.
Use the same signed/radial label at a shared vertex on both incident
edges. Never change a selected witness merely because another is also
feasible. Core restrictions and angular closure must be used globally.

Permitted ingredients include exact support identities, monotonicity,
convexity, explicit polynomial positivity, and isolated rational reference
comparisons justified by squaring or alternating series. Intrinsic finite
classifications, such as actual owners and signs, are permitted.
A state or angle mesh, generated Bernstein row inventory, recursive owner
table, sampled minimum or numerical PASS is not a proof premise.
An uncomputed potential defined by an infimum is not its own proof.

The next work is **global entry into a completed route**. The small-mismatch
cuts, owners, tilt and terminal, and the entire hard-class reduction in
Section 3, are already proved on their stated domains. If a proposed
one-vertex potential is false, record the obstruction and retain coupled
vertices in a two-edge or whole-cycle argument; do not conceal it by
refining a grid. Later-stage signs, cuts and owners cannot be used in
reverse to justify an earlier stage.

One sufficient remaining unrestricted implication is

\[
 \boxed{\text{G0--G2 actual candidate at }q\le Q_1,
       \quad y_E\le0\quad\Longrightarrow\quad S\le3/200.}
\]

Here `Q1=1957767069/500000000`. The historical G4/G5 contractions are
one possible route to this implication; they are not mandatory intermediate
theorems. A proved global reduction into the hard class of Section 3 would
also supply the lower bound, with every original equality consequence
retained. That route is now complete for the stated ordered
normal-sign hard-owner class, with every outer-error sign and
outer owner; entry from arbitrary candidates remains open.

Once the displayed implication is proved, the completed original-center transfer
and Section 5 close G10 and the unrestricted theorem. The transfer is no
longer a separate open estimate; it does not discharge global capture.

## 7. Published milestones and retained history

The new downstream proofs were pushed on 19 October 2026:

- `fec79e3634c09b79882271bbbdf06b7c35511e68`: complete nonpositive-tilt exclusion at S<=3/200.
- `62de8f125f16fbb11156ec4198bb7ff8f71d1a7e`: both positive tails in the actual ED-owner/H frame, with the exact all-owner scalar identity.
- `6f2dff31474c36bdb73a46445b17fc8c65d6270a`: sharp owner-frame terminal and full equality implications at S<=3/200.
- `a33bfd4d9dfdfdc5b8b06adf2d34bad4405ec6a9`: normalized mathematical typesetting of that terminal; all exact estimates retained.

The preceding full mixed-owner extension is in the history ending at
`79ce198ae3b5d87c54dc5ff8d93e1317b604a41f`.
Earlier entry milestones include `34eafad16ea7f7810aae68c627a3aa3ecf6d32d5`
for conditional sign rigidity, `452d5ad937e441b2ef3008af79d5f5214d5cf15f`
for the complete short-word assembly, and
`201a6ac3b1d15fc7716f48a3408c8d6b03dfe2a0` for G2 selection.

Git retains every individual commit timestamp. The earlier detailed
roadmap and component inventories remain in its versions at
`ca9567729c0839a68e439a91ab63b29e7419b0d4` and
`bbe15f74b3406647b89eb26710629c0bb3a54f11`.
Historical table counts are not new compilation measurements.

