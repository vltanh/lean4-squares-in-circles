# Long two-core capture: exact interfaces and current finite cover

The finite domain cover for the long two-core word is now proved: all32
ordinary exclusion inputs have complete exact manifests and pass the
independent domain/binding audit. The charged angular budget and owner
complement have now passed their exact composition audit as well. Together
with the exact scalar angle audit, this captures the long word into the
nominal32-owner topology with aligned mismatch below1/14000 and common tilt
in[1/10,4/25]. The broad center-free local dual, its stationary graph, and
the projected-slider bounds are now proved and invoked in the terminal
interface note, closing this word. The other boundary necklaces have
separate complete finite covers.

## 1. Fixed role and symmetry convention

The counterclockwise adjacent-pair ring has physical word

\[
(C_0,O_1,O_2,C_3,O_4,O_5,O_6).
\]

Here the core at role0 is the one from which the other core is encountered after
three counterclockwise edges. The signed tangent is
\(t_i=\tan(\theta_i-\arg p_i)\), with the square-frame representative chosen in
\([-\pi/4,\pi/4]\). At either endpoint of this representative interval the two
descriptions identify the same square, and the closed signed cover includes both.

Reflecting the physical ring and then assigning new role \(i\) to old role
\(3-i\pmod7\) preserves this word and changes the tangents by

\[
t'_i=-t_{3-i\pmod7}.
\]

In particular it swaps and negates roles0/3, roles1/2, and roles4/6, while
negating role5. Every use of this reflection below occurs while the preceding
box is invariant under this map.

After the symmetric box in Section3 is established, one may choose the reflected
representative with \(|t_0|\ge |t_3|\). Together with the core signs this means
\(0<t_3\le-t_0\). Thus on an anchor interval \(t_0\in[l,h]\subset(-1,0)\)
one may use the rectangular relaxation \(t_3\in[1/8,-l]\).

For reference, the selected candidate branch is the reflection of the named
clockwise ring \((T,B,A,G,H,E,D)\). Its signed tangents are approximately

\[
(-.27167805,.50008968,-.33610872,.22675727,
 -.93305066,.03238095,.88154510).
\]

These decimals identify a branch; they are never used as exact proof inputs.

## 2. Transport between circle ceilings

The initial six core-anchor certificates use
\(Q_c=9789/2500\). Subsequent certificates use

\[
Q_\sharp=97888353437936885663/25000000000000000000.
\]

The outer-radius monotonicity lemma permits a boundary ring at any
\(q\in[3,Q_\sharp]\) to be expanded to either ceiling with the same center rays,
the same tangents, and every core state held fixed. Every selected adjacent SAT
axis stays valid. In particular the physical C/O word is exactly preserved.
Thus the coarse core-anchor exclusions apply to the sharp ring without any
additional extremality or capture assumption.

For eventual proof closure, take a fixed rational \(q_0<q_*\) with
\(Q_\sharp-q_0\le3\cdot10^{-16}\), and replace any hypothetical smaller circle
by \(\widetilde q=\max(q,q_0)<q_*\). Perform radial boundary reduction at
\(\widetilde q\), then expand only the outer radii to \(Q_\sharp\). After sharp
capture, contracting back moves each center by at most \(10^{-16}\), while
preserving center rays and frames. This leaves ample reserve inside a terminal
center bound of .001 when the sharp capture uses .00099.

## 3. Symmetric finite cover already submitted to exact validation

All intervals below are closed proof domains; after exclusion the remaining
states may safely be enclosed in the corresponding closed complement box.
Every ordinary certificate proves a directed cyclic sum of pair costs greater
than an explicit rational upper bound for \(2\pi\), and therefore excludes its
declared seven-role box.

| Layer | Premise | Domains excluded | Candidate stems | Consequence after full validation |
|---|---|---|---|---|
| Core anchor | Word COOCOOO at coarse Q | Role0 in [-1,-1/2],[-1/2,-3/8],[-1/8,0],[0,1/4],[1/4,1/2],[1/2,1] | `long_core_anchor_{0,1,4,5,6,7}` | t0∈[-3/8,-1/8]; reflection also gives t3∈[1/8,3/8] |
| Outer signs | Both core intervals | Role4 in [-3/4,-1/2],[-1/2,0],[0,1/2],[1/2,1] | `long_sharp_outer_role_{0,1}`, `long_sharp_positive_outer_split_{0,1}` | t4∈[-1,-3/4]; reflection gives t6∈[3/4,1] |
| Other outer roles | Core and outer-sign intervals | Role1 in [-1,0],[0,1/4],[3/4,1]; role5 in[1/4,1] | `long_sharp_refine_{o1_negative,o1_low,o1_high,o5_high}` | t1∈[1/4,3/4],t2∈[-3/4,-1/4],t5∈[-1/4,1/4] |

The resulting symmetric seven-role box is

\[
[-3/8,-1/8]\times[1/4,3/4]\times[-3/4,-1/4]
\times[1/8,3/8]\times[-1,-3/4]\times[-1/4,1/4]
\times[3/4,1].
\]

The six core-anchor exclusions have all passed exact binding and coverage
audits, with `long_core_anchor_4_candidate_v2.json` replacing the rejected
original anchor4. Therefore the two core intervals are proved. The two sharp
outer-role exclusions and both positive outer splits have also passed, using
`long_sharp_positive_outer_split_1_candidate_v2.json` for the repaired split1.
All four other-outer-role refinements have passed. Therefore the entire
symmetric box in this section is established. Exact records, immutable input
paths, hashes, coverage, and arithmetic reserves are indexed by
`m5_agent/completed_capture_registry.json`.

## 4. Selected-branch refinement

Choose \(|t_0|\ge|t_3|\) using the preceding symmetry. Three further positive
continuous-discovery candidates are prepared:

| Stem | Role0 domain | Role3 domain |
|---|---|---|
| `long_sharp_coarse_core_left` | [-3/8,-5/16] | [1/8,3/8] |
| `long_sharp_coarse_core_right_middle` | [-15/64,-3/16] | [1/8,15/64] |
| `long_sharp_coarse_core_right_high` | [-3/16,-1/8] | [1/8,3/16] |

These imply \(t_0\in[-5/16,-15/64]\) and \(t_3\le5/16\), using the two
completed replacement inputs `long_sharp_coarse_core_left_candidate_v2.json`
and `long_sharp_coarse_core_right_middle_candidate_v2.json`. The right-high
input has also passed its exact audit. Finer anchor inputs
`long_sharp_left_complete_round0_candidate.json` and
`long_sharp_right_complete_k96_candidate_v2.json` have passed exact validation.
They respectively exclude anchor ranges[-5/16,-9/32] and
[-17/64,-15/64], using the maximum-core bound on role3. Together they give
\(t_0\in[-9/32,-17/64]\), \(t_3\le9/32\). The older fine-anchor candidates
were refuted by the complete aligned-contact scan and are not proof inputs.

The next explicit bridge consists of13 role cuts. From that anchor premise,
the intended role intervals are

\[
\begin{array}{c|ccccccc}
i&0&1&2&3&4&5&6\\\hline
t_i&[-9/32,-17/64]&[31/64,33/64]&[-23/64,-21/64]&
[13/64,15/64]&[-61/64,-59/64]&[1/64,3/64]&[55/64,57/64].
\end{array}
\]

`probe_long_sharp_terminal_role_domains.py` records each excluded side as its
own closed box. Role5's lower complement crosses zero and is therefore split
into a negative interval and a short nonnegative interval. The first nine cuts
and their current exact status are:

| Excluded side | Effective input | Status |
|---|---|---|
| Role1 below31/64 | `long_terminal_o1_low_complete_round0_candidate.json` | Passed replacement |
| Role1 above33/64 | `long_sharp_terminal_domain_o1_high_candidate.json` | Passed |
| Role2 below-23/64 | `long_sharp_terminal_domain_o2_low_candidate_v2.json` | Passed replacement |
| Role2 above-21/64 | `long_sharp_terminal_domain_o2_high_candidate.json` | Passed |
| Role3 below13/64 | `long_terminal_c3_low_complete_round0_candidate.json` | Passed replacement |
| Role5 negative | `long_sharp_terminal_domain_o5_negative_candidate_v2.json` | Passed replacement |
| Role5 in[0,1/64] | `long_sharp_terminal_domain_o5_low_candidate.json` | Passed |
| Role5 above3/64 | `long_sharp_terminal_domain_o5_high_candidate.json` | Passed |
| Role6 below55/64 | `long_sharp_terminal_domain_o6_low_candidate.json` | Passed |

All statuses are conditional on the preceding anchor box. Four further cuts,
recorded by `probe_long_sharp_terminal_role_domains_second.py`, exclude role3
above15/64, role4 below-61/64 and above-59/64, and role6 above57/64. They are
conditioned on the first nine cuts. Their completed exact inputs are

* `long_terminal_second_c3_high_complete_round0_candidate.json`;
* `long_terminal_second_o4_low_complete_round0_candidate.json`;
* `long_terminal_second_o4_high_complete_round0_candidate.json`;
* `long_sharp_terminal_second_o6_high_candidate.json`.

The full bridge is proved. The independent exact rational audit
`audit_long_two_core_cover.py` verifies all32 complement covers, every input
domain inclusion, both symmetry interfaces, and the exact match of the final
box with the angular-budget domain. Its latest output matches all32 inputs to
complete exact manifests, with an empty pending list.

A complete capture must
continue until every surviving state is covered by the quantitative local
theorem; these intermediate bounds are not the endpoint.

## 5. Completed terminal angular budget

For the selected named branch \((T,B,A,G,H,E,D)\), the five aligned nominal
frame edges have indices \(0,1,3,5,6\), while edges2 and4 join the two frame
families. Set \(h(d)=(\cos d+\sin d-1)/2\) for frame distance
\(0\le d\le\pi/4\).

An exact ordered pair potential certificate of the form

\[
\delta_i-\beta_i h(d_i)+\psi_{i+1}(t_{i+1})-\psi_i(t_i)
\ge\gamma_i
\]

with \(\beta_i=\beta>0\) on those five aligned edges and zero on the other two
implies

\[
\sum_{i\in\{0,1,3,5,6\}}h(d_i)
\le\frac{2\pi-\sum_i\gamma_i}{\beta}.
\]

The concave graph of h lies above its chord from0 toπ/4, hence

\[
S:=\sum_{i\in\{0,1,3,5,6\}}d_i
\le\frac{\pi}{2(\sqrt2-1)}
   \frac{2\pi-\sum_i\gamma_i}{\beta}.
\]

There is a useful elementary improvement. The concavity of h and
\(\sqrt2>7/5,\pi<16/5\) give \(h(d)\ge d/4\) on the whole frame interval.
With β=1/50 and a cyclic deficit at most7·10^-7, first
\(U\le7/200000\) and \(S\le7/50000<1/1000\). For \(d\le1/1000\), the
Taylor bounds for sine and cosine give \(h(d)\ge(49/100)d\). Consequently

\[
\boxed{S\le1/14000<1/10000.}
\]

The concrete rational input `long_local_aligned_budget_v1.json` has passed
the separate exact ordered-edge-β checker on the allowed axes, composed with
the already completed wrong-axis complement. It is conditional on the
seven-role box displayed above, now supplied by the32 completed domain cuts.
Its cyclic deficit is below7·10^-7. The selected-axis manifest is
`m5_agent/long_local_selected_budget_v1_charged_piece_logs_checked/manifest.json`,
SHA256 `4db897f1ad7382dc258cf368bd4ce9aed57e97aa7c781880372062dde2d37369`.
All7 times576 initial pieces passed, using24558 exact interval nodes. The
composition audit treats this as a budget theorem, comparing
\(\sum\gamma+7/10^7\) with the specified upper bound for \(2\pi\).

The common-tilt and quarter-lift interfaces are established by the exact
scalar audit below. The projected-slider formulas are recorded in the terminal
interface note. The separate local proof uses actual transverse slider
projections to remove a center-proximity hypothesis; its broad-chart arithmetic
must be invoked explicitly.

## 6. Completed exact SAT-owner capture on the terminal box

The masked-axis input `long_local_owner_capture_v1.json` takes the same domains,
potentials, and edge penalties as the budget and raises each pair threshold by
exactly7/10^7. Every actual pair residual above its baseline gamma is
nonnegative. Their cyclic sum is below7/10^7, so each actual pair cost is at
most its raised threshold. The exact masked checker excludes every wrong
signed separating axis at that threshold.

In the axis order `(source e, source f, target e, target f, negatives)`, the
surviving axis sets for edges0 through6 are

\[
\{1,2\},\ \{1,3\},\ \{3\},\ \{1,3\},\ \{4\},\ \{1,2\},\ \{1,3\}.
\]

All seven masked signed branches have passed, each with576 initial rectangles
and no subdivision. The audited manifest hash is
`ead804b9221b9cee0970365ce998616ab6002c3efbc6849ceef125cc7d79effa`.
This establishes the owner conclusion after the budget theorem is summed on
its role domain. It is not itself a cyclic exclusion.

The completed budget proof uses the following noncircular composition. The
masked theorem itself is the independent pair statement that any wrong-axis
separated pair has cost at least gamma plus7/10^7, which is strictly stronger
than the target gamma bound. Therefore checking the target bound on just the
allowed axes completes the full-SAT pair theorem. That selected-axis exact
run and its composition audit are complete. Only the subsequent owner
inference uses the cyclic residual budget.

For the mixed edge2, beta is zero. Consequently the budget yields the useful
one-dimensional bound

\[
\gamma_2+\psi_2(t_2)-\psi_3(t_3)
\le\delta_2\le
\gamma_2+\psi_2(t_2)-\psi_3(t_3)+7/10^7.
\]

The exact scalar checker `verify_long_terminal_angle_lift.py` now verifies the
discrete quarter-turn lifts and the common-family tilt interval
\(1/10<t<4/25\), where
\(t=\pi/2-\delta_2-\arctan t_3+\arctan t_2\). Its proof uses only rational
piecewise-linear endpoint bounds, alternating arctangent enclosures, and the
independently checked sharp pi bound. Both its budget and role-domain
hypotheses are now established. The detailed passage to the local dual is in
`LONG_TWO_CORE_TERMINAL_INTERFACE.md`.

## 7. Discovery corrections and proof discipline

The discovery code includes all four known boundary endpoint rings, every
signed aligned-contact branch with relative angle0,pi/2,pi, domain endpoints,
and every piecewise-linear knot as a scalar section. It then iterates
continuous pair minima into the LP. The formerly missing same-sign quarter
contacts refuted several earlier capture inputs; those originals are preserved
as rejected attempts and are replaced under fresh names in this ledger.

Floating discovery is never an acceptance criterion. All acceptance belongs
to the independent exact interval validator and its complete manifest audit.
