# Gated roadmap: a genuinely table-free hand proof for eight squares

**Branch:** PR #10, based on hand-only commit `d3eafec9a14ab90754bdfd8ca10e2bae82a81cf4`.
**Mode:** mathematical research and complete pen-and-paper derivations only.
**No Lean implementation, compilation, CI, native kernel, or external scripts as a proof premise.**

## 0. What counts as success

The target is the unrestricted sharp eight-unit-square packing theorem, including
the exact stationary squared radius \(q_*\) and the complete five-parameter equality
family, **with no computed lookup table anywhere in its mathematical dependency
chain**.

“Table-free” means:

- No affine arc row mesh, interval subdivision, fixed-box positivity lookup,
  enumerated owner/tilt certificate, recursive word search, or table whose
  asserted numerical PASS status is a mathematical premise.
- Explicit *short* lists of genuine geometric alternatives (the four original
  separating axes, three boundary charts, seven dihedral quarter-word classes,
  or the two signs of an angle) are permitted. Such classification is intrinsic
  and exhaustive, not a numerical partition.
- Elementary exact rational comparisons, a few displayed low-degree polynomial
  identities, circle supports, monotonicity, and derivatives are permitted,
  **provided each is derived and proved symbolically**. Replacing a huge table
  with a disguised smaller numerical table does not count.
- All four *original* feasible signed axes, their possible ties, both signs at
  zero, core side/corner junctions, and weak boundary contacts survive.
- A conditional assertion or new unproved “global inequality” does not close a
  gate. Each delivered hand proof must establish the inequality over its
  entire stated continuous domain.

The old tabular proof remains a comparison oracle for *discovery*, not part of
the new proof. Do not delete it merely on the strength of this roadmap.
No Lean source is to be changed until a complete hand argument exists.

### Current hand-proof status (2026-10-19)

The geometric normalization and the complete frame theorem are now
table-free. The stationary construction, sharp conditional terminal,
and full conditional equality family are also table-free. The
unrestricted theorem is still missing its global capture proof.

| Gate | Current mathematical status |
|---|---|
| G0--G1 | Central core, physical gaps, boundary reduction, and all ten frame-pair inequalities are proved; the real frame spread is strictly below .7. |
| G2 | The four words with a double increment are excluded. The two residual words 0010111 and 0011011 remain open. |
| G3 | The structural tangent-cut proof remains open. |
| G4--G5 | The coarse and middle mismatch contractions remain open. |
| G6 | Quarter-owner rigidity is proved under its stated cuts and \(S\le.015\). |
| G7 | Mixed-owner rigidity is proved under its stated hypotheses and \(S\le.001\); the preceding \(.015\to.001\) contraction remains open. |
| G8 | The positive-tilt tails are excluded under the original owner and mismatch hypotheses. |
| G9 | Stationary existence/uniqueness, the exact packing at \(q_*\), the conditional sharp terminal, and the full conditional equality domain/box are proved without the historical small certificates. |
| G10 | The unrestricted assembly awaits G2--G5 and the remaining G7 contraction. |

All closure statements here are hand mathematics. The retained Lean and
generated data have not been edited, compiled, or run through CI.

### Baseline and existing reusable results

At the currently committed source snapshot, the theorem import closure still
contains **576,828 active affine rows** across the ten original table families.
The owner/tilt layer still contains **8 quarter groups (345 rows), 15 mixed
groups (729 rows), and 41 positive tilt bundles (861 rows)**: 1,935 remaining
quartic certificate declarations in 64 generated modules. The word layer has
1,120 recursive certificate declarations, and the four-type layer has 21
remaining continuous chart decisions. The stationary root subdivision has
been replaced in draft source by geometric uniqueness, but 49 local
formula/bracket checks and 5,376 adaptive scalar checks remain.
The central-core proof also includes a short fixed Bernstein appendix.
These are **source inventories**, not a build or runtime measurement.

Already available as **hand arguments**, with uncompiled Lean drafts where noted:

1. Center-gap and angular-budget arguments; the odd-seven-walk potential
   identity; and the core/core pair and common-word cost bounds.
2. The committed global theorem `HAND_GLOBAL_CORE_CYCLE.md`: any seven-cycle
   with \(g_i>19/25\) has at most one core/core neighboring edge. Therefore
   at most four core vertices occur and only 64 of 128 indexed radial words
   survive. **This fact is global**; it cannot by itself justify deleting
   a locally quantified pair theorem.
3. The exact half-angle SAT-contact reduction in `MISMATCH_GEOMETRY.md`.
   At fixed pair states, all four SAT margins have quadratic numerators,
   so a charged angle minimum is attained at an interval endpoint or an
   SAT contact root. The **continuous state-variable positivity gate is open**.
4. Several complete owner exclusions by four-circle stresses and short
   telescoping chains; notably negative tilt and every forbidden D owner.
5. A geometric stationary-family uniqueness argument using convexity,
   curvature and radius monotonicity. Its retained numerical lemmas are
   **not** yet table-free.

The arithmetic reductions described in earlier work sessions but not visible
in this committed source snapshot are not counted as completed changes.

## 1. The proposed main mathematical mechanism

### 1.1 Preserve the whole cycle, not seven unrelated pair problems

Let \(i\) range over the seven exterior squares in cyclic order. Write
\(x_i=(a_i,b_i,\sigma_i,\kappa_i)\), where \(\kappa_i\) is its geometric
radial chart (outer, core side, core corner). Let \(\phi_i\) be the
canonical *relative frame phase*. Before quarter-word normalization its
integer increment is unknown; afterward
\[
 \phi_i=k_i\pi/2+d_i,\quad
 (k_i)=(0,1,0,1,0,1,1),\quad \sum_i\phi_i=2\pi.
\]
For each edge, at least one of the **four actual** forward SAT margins
\(M_{ij}(x_i,x_{i+1},\phi_i)\) is nonnegative.
The physical center gap is
\[
 g_i=\phi_i+\sigma_i\arctan(b_i/a_i)
              -\sigma_{i+1}\arctan(b_{i+1}/a_{i+1}),
 \quad g_i>19/25,\quad \sum_i g_i=2\pi.
\]
If \(C\) denotes a core chart, additionally
\[
        \#\{i:\kappa_i,\kappa_{i+1}\text{ are core}\}\le1.
\]
The seven edges **share** their vertex states and frame errors; exploit
this before discarding information in a pairwise lower bound.

### 1.2 Exact contact frontier: eliminate angular meshes first

Set \(z_i=\tan(d_i/2)\) on the existing chart \(|z_i|\le3/8\).
For each original SAT axis \(j\), sign, and quarter increment,
\[
 (1+z_i^2)M_{ij}=A_{ij}(x_i,x_{i+1})z_i^2+
                B_{ij}(x_i,x_{i+1})z_i+
                C_{ij}(x_i,x_{i+1}).
\]
The denominator is positive. Therefore an *angle* can be optimized
against feasibility by checking its permitted lower endpoint and
at most two contact roots, including linear, constant and double-root
degeneracies. The existing hand argument establishes this reduction.

**What remains** is not another angle mesh: prove the resulting inequality
over the *two continuous state coordinates* of each adjacent pair, while
respecting the global cycle. Use circle parameters and support inequalities
rather than intervals in those two coordinates.

### 1.3 Two candidate ways to close a charged stage

**Primary: direct cyclic stress.** Find a geometrically derived nonnegative
stress, possibly depending smoothly on the whole configuration, that
combines the actual feasible SAT inequalities and farthest-corner circle
supports to give a uniform seven-cycle obstruction. Prove the obstruction
for an entire geometric regime, not one owner vector or one interval.
The common total error \(S\) must be spent **once**.

**Fallback: analytic Bellman potential.** Derive a single real marker
\(L_i(x_i)\) per vertex from supporting tangents/contact geometry
(or a bounded number of intrinsic chart branches), and establish
\[
 \phi_i+L_i(x_i)-L_{i+1}(x_{i+1})
 -\beta\,\mathbf1_{i\in I}h(|d_i|)>\gamma_i
 \quad\text{for every feasible original axis},
\]
where \(I=\{H,A,B,T,D\}\), \(S=\sum_{i\in I}|d_i|\), and
\(h(s)=(\sin s+\cos s-1)/2\) on \(0\le s\le7/10\).
Summing telescopes the *same* vertex marker at both incident edges:
\[
 \sum_i\gamma_i+\beta\sum_{i\in I}h(|d_i|)<2\pi.
\]
Concavity gives \(\sum h(|d_i|)\ge h(S)\) when \(S\le7/10\).
The existing scalar contraction logic may then be reused without
numerical data.

A marker is **not** a solution merely because it can be defined by an
infimum; its finite-dimensional contact inequalities must be proved.
If a simple one-vertex potential is too weak on locally possible but
globally incompatible states, *do not add 100 piecewise coefficients*:
replace the local inequality by a complete-cycle inequality or a
two-edge infimal convolution sharing the middle vertex.

### 1.4 Geometric primitives for every lane

Use (i) exact disk support
\[
  ua+vb\le\mu q+\frac{u^2+v^2}{4\mu}-\frac{u+v}{2}
  \quad(\mu>0,\ (a+\tfrac12)^2+(b+\tfrac12)^2\le q),
\]
(ii) circle/chord convexity and monotonicity, (iii) exact contact
quadratics, (iv) telescope of adjacent SAT projections, (v) the shared
\(2\pi\) budget, and (vi) one common \(\ell^1\) angular-error budget.
Any proposed multipliers must be explained by equilibrium/corner
forces, not copied unexplained from a numerical certificate.

## 2. Sequential proof gates

A gate has a **complete theorem target**, a hand-proof method, and an
unambiguous exit condition. Later gates may be researched in parallel
but cannot *use* an earlier gate until its proof is complete.

### G0 — Consolidate common geometric invariants (mostly available)

**Target.** Starting from an unrestricted packing, recover the central
core, the witness-preserving boundary cycle, radius expansion to
\(Q_0\), the physical gap bounds, and the global “at most one CC edge”
theorem, retaining all original signed axes.

**Exit.** A standalone hand section proves the precise normalization,
no contradictory radial case assumptions, and the strict inequalities
on *every* actual seven-cycle. Check separately that the center-radius
hypotheses for the core/core chord estimate apply after expansion.

**Status.** The new CC angular-budget theorem is complete on paper.
The central core and strict physical gap now follow without coefficient
tables from `HAND_CENTRAL_BANDS_WITHOUT_TABLES.md`; the normalization,
radial translation, and radius expansion retain the original analytic
arguments. The exact dependency substitution for the physical gap is
recorded in `../HAND_EXTERIOR_FRAME_CONCENTRATION.md`, Section 1.

### G1 — Four-type frame concentration without recursive pair certificates

**Replaces.** The 21 remaining four-type continuous pair decisions
(the odd-seven-walk enumeration has already been removed).

**Target.** With the actual pair gap \(>19/25\), derive the required
four-type pair costs using **one or a few explicit whole-chart** disk
supports and marker bounds. Combine with the existing elementary odd
cycle argument to prove the strict real frame spread \(<7/10\).

**Attack.** Parameterize the two circles by their near-corner support
directions. For each actual forward axis, minimize its angular cost at
the exact contact frontier, then prove the state inequality from the
monotonicity/convexity of the circle supports. Treat core/core directly
and derive a uniform outer-versus-core/outer support. Exploit the
global CC-edge exclusion if a local pair bound is unnecessarily strong.

**Exit.** All four types, including their shared boundaries and all
four axes, are handled by analytic formulas; no chart-pair `certify`
call remains mathematically necessary.

**Status — closed on paper.**
`../HAND_EXTERIOR_FRAME_CONCENTRATION.md` assembles complete
whole-domain proofs for all ten unordered type pairs, hence all 128
ordered source-axis branches and their reflected target axes. Six new
scalar notes replace every inherited Bernstein row and continuous
interval mesh, including the common-point appendix, C/M curvature
mesh, C/L endpoint intervals, C/H corner tail, and L/H short-angle
appendix. The existing odd-seven-walk argument gives
\(\sum\Gamma\ge3881/625\); its closed orientation-tour lift then
proves strict spread \(<7/10\). The complete dependency chain has
been independently audited. This closes G1, not the residual word,
tangent-cut, or mismatch gates.

As an additional consequence, `HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md`
now excludes every primary original axis on every zero-quarter edge
before any tangent cut or mismatch bound, including primary axes tied
with secondary ones. It uses the compulsory return cost of the closed
frame tour and the newly table-free G1 pair inequalities.

### G2 — All six wrong quarter-word exclusions from a cycle inequality

**Replaces.** All 1,120 remaining word-certificate declarations.

**Target.** Every seven-cycle with the G1 lift has the candidate
quarter word \(0101011\) up to a genuine dihedral action.

**Attack.** Separate the intrinsically finite seven dihedral classes:
the four containing an increment 2 need only the *common* marker and
angular budget; for \(0010111\) and \(0011011\), retain the exact
initial-zero-edge sign deductions and build one whole-cycle
contact/stress inequality per **word**, not per state/axis box.
Use shared source/target vertex coordinates to cancel difficult
pairwise terms. Prove the action on original axes, including edge
reversal, not only on abstract words.

**Exit.** Two complete wrong-word contradictions plus the common
double-increment contradiction, valid for all radial types, signs,
axes, endpoints and reflections. A numerical check of a few words
does not close this gate.

**A local route has been ruled out exactly.**
`HAND_TWO_ZERO_EDGE_BOOST_OBSTRUCTION.md` constructs three actual
outer-boundary squares with two zero-quarter secondary contacts,
physical gaps above .76, and frame spread below .4. Their common-G1
path cost, even including the compulsory frame-return charge, is
less than \(46/25\). It cannot pay the remaining five edges at
their universal G1 minimum. A whole-word argument must retain more
of the complementary path or use a different proved stress.

**Additional complete component.**
`HAND_WRONG_0011011_SAME_SIGN_OUTER_WITHOUT_TABLES.md` proves all
sixteen same-sign outer/outer zero-quarter branches of 0011011 without
the former critical-curve or angle-curvature rows. Its contact Hessian
has a uniformly negative determinant, and its diagonal boundary has
whole-interval curvature greater than 1/30. `HAND_WRONG_0011011_NEGATIVE_QUARTER_WITHOUT_TABLES.md` also proves
the complete negative outer edge-2 quarter component and its reflected
edge-6 component. One global fourth-derivative sign replaces its five
endpoint derivative rows, and the full contact surface is strictly
concave in its eliminated source coordinate. The other components of
this residual word are still required.

`HAND_WRONG_0011011_EDGE3_NEGATIVE_WITHOUT_TABLES.md` adds the complete
negative outer edge-3 component and its reflected edge-5 component: a
strongly convex speed product and a linear contact-angle bound remove
all of their speed and scalar interval rows.
`HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md` proves the entire
0010111 outer role-5 opposite-sign family, all original axes and both
angle halves, with cost greater than 42643/47500. The two whole-word
exclusions still require their other components.

`HAND_WRONG_0011011_OPPOSITE_EDGE2_WITHOUT_TABLES.md` now also closes
the complete opposite-sign outer edge-2 quarter family and its
reflected edge-6 family. Two circle support inequalities replace its
source-ratio ranges, one quintic proves the entire support function
concave, and a uniform inverse-contact derivative bound handles both
the full axial minimum and the final target-ratio lemma. This leaves
no derivative-range table in that eight-half-axis component.

`HAND_WRONG_0011011_OPPOSITE_EDGE3_WITHOUT_TABLES.md` closes the
remaining opposite-sign outer quarter family, on edge 3 and its
reflection. It proves both aligned minima, both contact surfaces, and
the full implicit stationary envelope with uniform derivative signs.
All four original axes and both angle halves have cost greater than
.89777. The proof retains the original contact exits and uses no
critical-curve bracket sequence or derivative-range table.

`HAND_WRONG_0011011_MIXED_COMPONENTS_WITHOUT_TABLES.md` now proves
the complete mixed component: all nineteen reflection classes,
thirty-eight directed radial/sign cases, and 152 original axis
branches. Its common actual-circle support argument removes nine
squared-polynomial rows. Whole contact-curve calculus replaces the
early-angle tangent lists, corner derivative ranges, side discriminant
rows, and final implicit zero-curve intervals. Section 9 gives the
full dependency map, including the actual-cycle zero-primary
exclusion before any candidate capture or mismatch assumption.

`HAND_SHORT_WORD_UPPER_PRIMARY_CONTACTS_WITHOUT_TABLES.md` proves
three complete upper-primary branches of 0010111, on edges 2, 4,
and 6, with corrected cost greater than .8978. Its contact minimum
passes through the intrinsic axial/diagonal join; the one possible
interior segment is controlled by an exact angular derivative.
The two curvature polynomials are proved on their whole geometric
sign domains, without angle or state subdivision.

### G3 — Tangent cuts as a single structural theorem

**Replaces.** The six large G/T/H/D tail tables (the H/D part may use
the small-mismatch bound obtained at G4).

**Targets, in dependency order.**
\[
 E:u_E\le0,\qquad
 -4/5<u_G<-1/20,\qquad
 1/20<u_T<4/5,\qquad
 u_H>1/2,\ u_D<-1/2.
\]
The two G cuts are proved before the T cuts; the H/D cuts may be
completed after G4's coarse contraction, but not assumed to obtain it.

**Attack.** A forbidden tangent tail means an outer/core square has
a restricted direction of its nearest corner. Use two neighboring
separators, a shared physical gap, and one disk support to force an
impossible span. Find a *uniform tail lemma* with a role/sign mapping,
not six unrelated coefficient tables. Derive the constants from
where the supporting rays or corners meet.

**Exit.** Every forbidden tail contradicts one whole-domain geometric
inequality without introducing the desired cut as a hidden premise.

### G4 — First coarse mismatch contraction: the critical experiment

**Replaces.** Coarse and enhanced affine tables (the existing
110,425 active coarse rows are not a proof to be compressed).

**Conditional target.** For every candidate cycle at \(Q_1\) with
E/G/T cuts and all original SAT witnesses:
\[
                  S<2/5\quad\text{and then}\quad S<13/50.
\]

**Primary attack.** Prove a global seven-cycle lower bound on phase
cost, with a **single coherent** charge and either equilibrium-derived
markers or an aggregate stress. Take contact roots analytically and
minimize over the shared vertex variables. The historical coarse
values are useful *targets to beat*, not axioms. Apply the core-edge
budget globally rather than demanding a sharp inequality for every
isolated core pair.

**Mandatory early test.** Before attempting fine estimates, write the
candidate inequality on the **full continuous state domain** and
seek counterexamples. A locally feasible pair violating a proposed
marker does not by itself refute a direct seven-cycle proof; an actual
feasible whole-cycle counterexample refutes that proposed inequality.

**Exit.** The two strict bounds follow with visible positive margins
and no retained affine row or 462-piece marker lookup.

**Auxiliary charge theorem, proved.**
`HAND_CLOSED_TOUR_CHARGE_COMPRESSION.md` gives the sharp width bound
from signed closure and arbitrary nonnegative edge weights. In
particular, with \(J=I^c\),
\[
 S\ge.4\Longrightarrow U_I+\frac{19}{125}U_J>
 \frac{1117}{6250},\qquad
 S\ge.26\Longrightarrow U_I+\frac{17}{200}U_J>
 \frac{12119}{100000}.
\]
This keeps the compulsory return charge. It follows by mass matching
and concavity, with only two nonzero increments at the extremum.
The required geometric seven-cycle cost inequality is still open;
these consequences of a bad mismatch do not by themselves close G4.

**First charged contact family, proved.**
`HAND_COARSE_POSITIVE_ZERO_CONTACT_WITHOUT_TABLES.md` proves
\((111/112)\delta+F(b)-F(1-B)\ge0\) for one explicit quintic
\(F\), every \(0\le\delta\le.7\), and both original transverse
owners of a positive \((+,-)\) zero-quarter edge. It includes all
contained radial states and all owner ties. The aligned contact
continuum is an exact equality; every positive angle is strict.
The proof uses circle speed bounds, a concave stationary-radius
chord, and two whole-domain polynomial remainders. The other charged
families and their common seven-cycle assembly are still required
for either coarse contraction.

### G5 — Middle contraction and sign rigidity

**Replaces.** The \(0.26\to0.1\) and \(0.1\to0.015\) affine tables.

**Targets.** Under the preceding cuts:
\[
 S\le13/50\Longrightarrow S<1/10;
\]
then prove the strict sign pattern
\((+,-,+,-,+,-)\) in roles \(H,G,A,B,T,D\), and
\[
 S\le1/10\Longrightarrow S<3/200.
\]

**Attack.** At small error, use the explicit second-order expansion
of every actual SAT projection and the universal width-cusp bound.
A single sum of weighted first derivatives should give a positive
coercive term in \(S\); bound the quadratic remainder by \(CS^2\),
without subdividing its five coordinates. Use the G4 global stress
with a sign-specific refinement only **after** sign rigidity is
proved. Do not let the later sign assumptions enter the first step.

**Exit.** Both implications, the sign theorem, all tie cases and the
needed H/D cuts are established with explicit *whole-domain* error
bounds, not one margin for each of many state boxes.

### G6 — Quarter-owner rigidity as a short-chain theorem

**Replaces.** The 8 remaining quarter groups (345 quartics).

**Target.** At \(S\le3/200\), every feasible axis on B-to-T and
D-to-E lies in zero-based \(\{2,3\}\), **not merely one selected axis**.

**Attack.** Reuse the established forbidden-D contradiction, the
B/T/D/E telescoping span, and the rotated G-corner exclusions.
For the residual B-forbidden/G-primary configurations, obtain one
uniform cycle stress from the *shared* pair constraints instead of
eight owner-vector tests. Group cases by geometric support direction
rather than by a generated owner index.

**Exit.** One theorem covers both edges, all four possible original
axes and simultaneous feasible ties, without a quarter selector.

**Status — conditionally closed on paper.**
`HAND_QUARTER_OWNER_CLOSURE.md` proves exactly this theorem under
the candidate frame, signed cuts, zero owners, \(q\le Q_0\), and
\(S\le3/200\), without the eight remaining quarter groups.

### G7 — Last contraction and the two mixed owners

**Replaces.** The \(0.015\to0.001\) affine table and 15 mixed-owner
groups (729 quartics).

**Ordered targets.**
\[
 S\le3/200\Longrightarrow S<1/1000,
\]
using only quarter-owner information (no assumed mixed owners);
then prove the full seven-edge original-axis owner restriction
\[
 (\{0,2\},\{0\},\{0,2\},\{2,3\},
  \{0,2\},\{2,3\},\{1\}).
\]

**Attack.** Use exact tangent support at the nominal frame to prove
a whole-cycle first-order gap and a single quadratic remainder bound.
For mixed G/E, exploit that their phase errors sum to minus the five
aligned errors. An E or G forbidden axis should be excluded by one
three- or four-edge stress valid for **all** other feasible owners.
Do not assign a fresh error budget to each edge.

**Exit.** The specified ordering is respected and every forbidden
mixed axis is impossible even if a permitted axis is feasible as well.

**Status — owner component conditionally closed; contraction open.**
`HAND_MIXED_OWNER_CLOSURE.md` and its two analytic companions prove
the mixed-owner restriction with \(S\le1/1000\), the signed cuts,
and the already established quarter owners. They retain every
original feasible tie. They do not supply the preceding contraction.

### G8 — Positive tilt tails by the exact envelope, not 41 bundles

**Replaces.** The 41 positive tilt bundles (861 quartics); the
negative half-chart is already excluded by hand geometry.

**Target.** With G7's full owner restriction and \(S\le1/1000\),
show
\[
 1/10<t<4/25,\qquad t=2\arctan z,\quad
             1001/20000<z<2/25.
\]

**Attack.** Derive from the original five-corner chain a *global*
lower envelope in \(t\) plus one uniform \(\ell^1\)-error loss.
Use the exact-family curvature and uniqueness theory to exclude
the two tails as whole connected intervals. A candidate dual calibrated
only at \(t_*\) may fail away from \(t_*\); prove its derivative,
endpoint gap, or an adaptive **symbolic** support rather than freezing
a numerical multiplier vector at the optimum.

**Exit.** Each complete positive tail is excluded by a monotonicity,
convexity or one-support argument, with strict endpoint margins and no
finite interval cover.

**Status — conditionally closed on paper.**
`HAND_POSITIVE_TILT_CLOSURE.md` and
`HAND_POSITIVE_TILT_NOMINAL_GAP.md` prove both entire positive tails,
including the actual shared frame errors, under the original cuts,
owners, \(q\le Q_1\), and \(S\le1/1000\). The negative half
is excluded by the existing analytic owner geometry.

### G9 — Remove the remaining small computational certificates

**Central-core component closed on paper (2026-10-19).**
`HAND_CENTRAL_BANDS_WITHOUT_TABLES.md` proves all three original common-point
statements, including the complete transverse segment and both closed angular
bands, with three full-domain positive-remainder identities and one common
quartic curvature bound. Together with the existing analytic central-existence
and forbidden-width arguments, this proves the unrestricted one-twelfth core
without the 19 Bernstein rows.

**Stationary existence component closed on paper (2026-10-19).**
`HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md` supplies an interior
stationary zero with `3.9154 < q_* < 3.915534138` by compact minimization,
the intermediate value theorem, the single continuous five-circle stress,
and five exact rational trial-point comparisons. The existing geometric
critical-point theorem gives broad uniqueness. The same rational trial is
an unconditional eight-square packing at the upper ceiling. No local root
box or five-interval family enclosure is used. The narrower historical
coordinate brackets are not asserted by this existence theorem.

**Whole-terminal stationary position and slider coefficient, proved.**
`HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS.md` proves
\(.895<u(q,t)<1-.6\tan t\) and \(-1.029<J(q,t)<-.98\)
on the entire strip \(3.9154\le q\le3.9156\),
\(.1\le\tan t\le.164\). The position bound follows by strict
convexity and one affine comparison curve; stationarity simplifies the
slider coefficient exactly and makes its whole-domain monotonicity
available. No local cover is used. These are components of the terminal
reserve theorem, not additional global capture assumptions.

**Conditional sharp terminal closed on paper (2026-10-19).**
`HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md`
proves all nine enlarged owner reserves \(>3/250\), every edge
weight \(<.87\), and automatic original-center slider bounds on
the whole terminal domain. Exact completion of the five center
squares leaves a remainder \(<9.75S^2\), so for \(S\le.001\)
it gives
\[
 r_0\ge q_*+\mu_HM(q_*,t)
 +\sum_{i=A,B,D,E,H}\mu_i
       \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +\frac{S}{500}\ge q_*.
\]
The retained family defect is globally nonnegative and has its unique
zero at \(t_*\), by the table-free existence and uniqueness proof.
Thus the old reduced-curvature table is unnecessary. The theorem
handles every one of the 32 original allowed owner choices, including
ties, and applies directly to original centers. It imports none of
the old four rectangles, position brackets, nine-midpoint owner
checks, or adaptive derivative bounds. The owner/tilt/mismatch
capture hypotheses remain the separate G2--G8 gates.

**Conditional equality and exact construction closed on paper (2026-10-19).**
`HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md` proves
\(.1<\tan t_*<.13\) and \(.916<u_*<.94\) from two tilt
comparisons and whole-domain monotonicity. These coarse bounds suffice
for the original five-anchor pullback, exact weak exterior-slider
ranges, all 21 exterior pairs, and the seven maximum-form central SAT
conditions. It proves the complete weak five-parameter domain and
its converse, including the entire independent parameter box and
pairwise noncongruence. The box gives an unconditional exact packing
at \(q_*\); four anchor vertices determine its unique least enclosing
circle. No narrow stationary/formula bracket, five-interval family
enclosure, or equality-box arithmetic table is imported.

Thus every component of G9 needed by the current hand path is closed.
The sharp lower bound and classification still require the explicitly
stated global capture hypotheses; no conclusion here supplies them
in reverse.

**Replaces.** The 49 stationary existence/bracket comparisons; the
5,376 adaptive fixed-box scalar checks; the short central-core
Bernstein and equality-box arithmetic appendices; any retained
special-purpose box checker still in the theorem dependency chain.

**Attack.**

- Stationary data: use strict position convexity, monotone radius
  inclusion and an intermediate-value sign change at two explicitly
  described trial chains. Prove their square-root bounds by squaring
  and sign control, not by a file of formula checks.
- Adaptive perturbation: derive **one uniform Hessian or Lipschitz
  majorant** on the entire analytic window and integrate it. Preserve
  the positive-defect mixed-derivative term in the Schur complement.
- Central core: replace the 19-entry positivity appendix by
  completed squares, monotonicity and whole-interval low-degree
  polynomial factorization. If a one-variable polynomial remains,
  display and prove its positivity directly.
- Equality box: group all center-distance constraints by geometric
  symmetry and monotonicity; prove the extremal configuration for
  each genuine contact type, not separate numerical rows.

**Exit.** The stationary witness, unrestricted central core, sharp
terminal reserve, full weak equality domain and five-dimensional
noncongruent box are proved without computed test families.

### G10 — Assemble and audit the **hand** proof

**Target.** A self-contained mathematical chain:
unrestricted packing \(\Rightarrow\) unique central core \(\Rightarrow\)
boundary/expansion \(\Rightarrow\) frame \(\Rightarrow\) candidate
quarter word \(\Rightarrow\) cuts/mismatch/owners/tilt
\(\Rightarrow q\ge q_*\); at equality, return to the untouched
original square centers and classify **every** packing by the
five-parameter family, including the converse and the noncongruent box.

**Exit.** Write a consolidated proof with no dependence on:
`affine_rows%`, `RealBox.certify`, generated owner bundles,
`by decide` over large data, adaptive box indices, or historical
manifest PASS claims. Give a cross-reference for each eliminated
original table and its *complete* geometric replacement.
Only **after** this gate should a new Lean implementation be planned.

## 3. Research lanes and priority

### Primary lane — global cycle/charged dual (G3–G5, G7)

This is the **decisive bottleneck**. Prioritize finding a full-domain
seven-cycle inequality over eliminating another 1% of row constructors.
Start with the coarse \(S<13/50\) theorem and its necessary G/T cuts.
A simple potential on the outer chart is worth pursuing because 460/462
of the historical coarse labels have no primary-coordinate coefficient;
however, those labels are *evidence for a conjecture*, not a proof.
Derive coefficients from exact circle tangents and dual equilibrium,
never from fitted decimal values.

### Secondary lane — contact-frontier / two-edge elimination (G1–G2)

Use exact SAT quadratic contacts and parameterize radial boundaries
analytically. Try to minimize over a shared middle vertex in a
two-edge chain to avoid the deliberately over-strong independent pair
certificates. Output full word exclusions and actual frame concentration,
not a collection of increasingly small numerical subdivisions.

### Independent lane — universal circle stresses and analytic tail bounds
(G6, G8–G9)

Transfer already proved four-circle and telescoping identities to
whole classes of owner directions, build a parameter-dependent stress
on the complete positive tilt tails, and replace local stationary
and adaptive checks with uniform calculus. This lane may prove
conditional results while earlier gates remain open; they must be
marked **conditional** until their prerequisites are discharged.

Use at most these three independent lanes. A new lane must attack a
different complete theorem, not duplicate the same numerical cases.

## 4. Anti-rabbit-hole and falsification rules

1. **No micro-pruning as progress.** Deleting more rows, intervals,
   or one of an unbounded family of subcases is not a gate closure.
2. **Prove a full theorem or record the blocker.** Every hand result
   states its exact input conditions, output, proof and all uncovered
   geometric alternatives.
3. **Falsify proposed inequalities early.** For a stress/potential,
   analyze equality, chart junctions, a critical point on each
   continuous state branch, zero transverse coordinates, and both
   signs of tilt. A genuine counterexample invalidates that candidate
   even if it performs well in many sampled configurations.
4. **Pivot on structural failure.** If a one-vertex potential fails due
   to incompatible adjacent pairs, try a two-edge coupled potential or
   whole-cycle stress. If a fixed multiplier fails across a tilt tail,
   derive a variable equilibrium multiplier. Do **not** add a finer
   grid to conceal the obstruction.
5. **Small intrinsic finite classifications are okay.** The two tilt
   signs, three radial charts, four SAT axes and seven dihedral words
   are finite geometric data. Cover them with a uniform argument or
   a clearly finite, exhaustive short classification; do not march
   through increasing discretization sizes.
6. **Keep the labels of correctness separate.** “Hand proved”,
   “numerically explored”, “uncompiled Lean draft”, and “kernel checked”
   are different statuses. No compilation-speed claim follows from
   reducing source counts.

## 5. Commit discipline and next concrete deliverables

Each hand-only milestone goes in a separate `[skip ci]` commit to PR #10.
Preserve the current Lean and historical input files unchanged.
The next useful files are:

1. **`HAND_CYCLE_STRESS_INTERFACE.md`** — write the *exact*
   seven-edge feasible set and proposed cycle stress, prove the
   angular/contact elimination and articulate precisely the
   remaining continuous-state inequality. Include a clear failed
   candidate if a natural simple marker is false.
2. **`HAND_COARSE_MISMATCH_GEOMETRY.md`** — either close both coarse
   contractions \(S<2/5\), \(S<13/50\) with a single geometric
   mechanism or record a concrete global obstruction that forces
   a change of method. This is the first genuinely large-table
   replacement gate.
3. **`HAND_WORD_CYCLE_GEOMETRY.md`** — establish the complete
   \(0010111\) or \(0011011\) exclusion with shared vertex states,
   not a reduction in recursive word certificate counts.
4. **`HAND_POSITIVE_TILT_ENVELOPE.md`** — prove both positive
   tails as complete intervals after the explicit owner conditions,
   using an actual-circle envelope.

Do **not** begin with a new Lean proof, generated rational table, or
a modified checker. The highest-value next mathematical step is the
global coarse seven-cycle inequality, not an optimization of its
current table representation.
