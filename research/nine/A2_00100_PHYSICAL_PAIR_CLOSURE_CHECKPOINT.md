# Original-nine 001/00: 99 further whole cells closed, 79 remain open

November 3, 2026. Computer-assisted discovery with complete exact rational
replay and the hand/table argument below. No Lean, Lake or CI.

**The current mask is not yet closed.** This checkpoint discharges 99 of
the 178 previously OPEN original cells. The same fixed register now has
**152 CLOSED / 79 OPEN**, with every one of its 231 IDs and paths retained.
The full-mask ledger remains **8 CLOSED / 24 OPEN**. No positional root,
roadmap gate, global lower bound or equality obligation is newly closed.

## 1. The original domains and the exact accounting

The caller is the unchanged `D_001/00^lt` in
[the coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md): all nine
independently oriented physical unit squares, 36 corners strictly inside
the disk of squared radius `Q=1105/256`, all 36 physical pairs, the five
marked cone comparisons, actual AB/BC/EF/FG, and strictly weak CD.

The accepted low-gap theorem handles `|y_D-y_C|<=2/3`. Its complement is
normalized by a common vertical reflection and by sorting only H and I.
The inherited two closed D-sign roots and the 231 original paths are an
exhaustive cover with shared faces. The [baseline assembly](A2_00100_FIXED_FRONTIER_HAND_TABLE_CHECKPOINT.md)
proves this cover and the first 53 whole-cell exclusions. This continuation
does not change a root, a path, its physical interpretation, or the
version-specific meanings of any old proof leaf.

| Complete input | Distinct new original cells | Exact finite evidence |
|---|---:|---|
| First physical separation package | 87 | 789 terminal leaves |
| Additional physical separation package | 7 | 76 terminal leaves |
| Further derived-coordinate-bound proofs | 5 | 284 rational bound deductions and five final contradictions |
| **Union, with original IDs deduplicated** | **99** | **No open descendant in any accepted parent** |

Six recovered bound certificates were freshly replayed, with 316 bound
deductions in total. One, `negative-e82c87a207fdb074`, is also in the
seven-cell physical package; it is retained as an alternative proof and
counted only once. Thus there are 94 distinct physical-tree proofs and
five additional bound proofs, not 100 new cells.

| Fixed branch family | Previously OPEN | Closed here | Still OPEN |
|---|---:|---:|---:|
| A: D positive, A nonpositive, inward-row escapes | 77 | 53 | 24 |
| B: D negative, A nonpositive, F-height branches | 39 | 6 | 33 |
| C: D negative, A nonnegative, alternate-chain escapes | 33 | 22 | 11 |
| D: D positive, A nonnegative, alternate-chain escapes | 29 | 18 | 11 |
| **Total** | **178** | **99** | **79** |

These are counts of unchanged original full-cell predicates. Internal
nodes and incomplete trials do not replace a parent or add a mandatory
roadmap gate. The table is not an estimate of remaining mathematical effort.

The exact record-to-certificate mapping, all paths, tables, source bindings,
independent reports and remaining IDs are in the
[package manifest](computer_assisted/a2_00100_physical_pair_closure_manifest.json)
and [current register](gates/A2_00100_FIXED_FRONTIER.json).

## 2. Exhaustive physical separation supplies the new proof trees

For original square i retain its unchanged side frame, coordinate
halfwidth `h_i`, and centered aligned inset of halfwidth `g_i=1/(4h_i)`.
Its open inset lies in its open physical square. Therefore, for distinct
originals i,j, at least one of the following four closed inequalities holds:

    x_j-x_i >= g_i+g_j;    x_i-x_j >= g_i+g_j;
    y_j-y_i >= g_i+g_j;    y_i-y_j >= g_i+g_j.

Otherwise both inset coordinate intervals overlap in their interiors, so
the physical interiors intersect. This proves the four-way `proxy` union
on the entire original caller, including contact faces. It does not
assert that a particular separator observed in an LP proposal is forced.

When a full separating-axis split is used, the separating-axis theorem
for two original squares supplies one of their two axes from either
original, with either sign. All eight owner/axis/sign alternatives are
included. Each child uses the same original frames in its pair, corner,
width and product constraints. These are the already reviewed frozen
v14 row semantics, not a new geometric relaxation or a fixed contact graph.

At every new internal node the delivered tree includes exactly the four
or eight eligible children. A separate root-side checker reconstructs
this tree from the complete leaf paths. It rejects missing or repeated
leaves, a leaf that is an ancestor of another leaf, inconsistent queries,
and an invalid original pair, axis, sign or owner. Each new leaf also
passes the frozen exact decoder. Finite induction from each original
prefix proves that its entire physical domain is covered by its leaves.

The four prescribed deep pilots illustrate the compact mechanism:

| Original pilot | First pair split | Second split in the surviving child | Complete leaves |
|---|---|---|---:|
| `positive-c5d1d2351fe764c2` | F/I | G/I when I is right of F | 7 |
| `negative-31ce871c81b35b54` | G/I | G/H when I is above G | 7 |
| `negative-b1a9c1540e73c619` | H/I | D/I when I is right of H | 7 |
| `positive-655c4b699ba028a1` | C/I | D/I when I is above C | 7 |

Each is a complete original parent proof, not four excluded numerical
points. The shallow C pilot, `negative-0b5d0bfec10c8526`, also closes:
its 49-node proof has 37 terminal leaves. The shallow A, B and D pilots
remain OPEN at this checkpoint.

## 3. The printed exact contradiction at each leaf

The inherited [physical review](A2_00100_FIXED_FRONTIER_PHYSICAL_REVIEW.md)
proves that every true original configuration supplies one simultaneous
assignment z satisfying the regenerated rational rows `a_j.z<=b_j` and
the printed absolute bounds `|z_k|<=M_k`. All original variables and
products retain their physical meanings.

A weighted leaf prints positive integer weights w_j, with denominator
`2^40`, and every scalar row receiving a nonzero weight. Put

    r = sum_j w_j a_j,   B = sum_j w_j b_j,
    delta = (-B - sum_k M_k |r_k|) / 2^40.

The table proves `delta>0` exactly. Its weighted inequalities imply
`r.z<=B`, whereas the variable bounds imply
`r.z>=-sum M_k|r_k|>B`, a contradiction. Residual coefficients are paid
explicitly; approximate cancellation and optimizer tolerances are not
proof premises.

The two physical packages contain **865 terminal leaves**, of which
**466** use weighted sums with **6,027 printed rational rows**. The
other 399 leaves are explicit empty propagated intervals or complete
four-inset-option contradictions. Their exact derivations are regenerated
by the frozen verifier; no artificial weighted reserve is assigned to them.

The least positive weighted reserve over these physical proofs is

    117564851397356830528204229549721
    / 1513205620398602154554141758717952000 > 0.

The printed-sum checker is a separate standard-library implementation.
It imports neither an optimizer nor the physical verifier. It verifies
every row sum, residual correction, denominator and positive reserve.
Its arithmetic scope is distinct from physical validity and complete
parent coverage, which are checked separately.

## 4. Acyclic derived bounds discharge five further original parents

These certificates start at an unchanged original parent and derive
coordinate bounds from its valid scalar rows. Given nonnegative rational
weights lambda_j, let `r=sum lambda_j a_j` and `B=sum lambda_j b_j`.
For a coordinate objective c (a signed coordinate unit vector),

    c.z = r.z - (r-c).z <= B + sum_k M_k |r_k-c_k|.

Every printed deduction verifies that this last rational expression is
at most its declared bound U. Hence `c.z<=U` holds for every original
caller. All deductions in one round use only the intervals proved before
that round. Only after checking them all are their bounds intersected
with those intervals. The next round regenerates the same physical rows
on that proved smaller domain. This is an induction, not an added
position assumption or a circular use of a proposed bound.

Each of the six replayed certificates ends in a strictly positive exact
weighted contradiction. The five additionally counted original cells are

    negative-64094241c36c4fc8
    positive-1077638afc8dc284
    positive-9cc839d8f2504bca
    positive-a76638de241e6faf
    positive-fbac60a51d1e7f99.

The numerical producer's proposed positions and candidate LP assignments
are untrusted. The independent reviewer rebuilds the exact starting path,
collects the frozen unweighted rows, calculates every bound with Fraction
arithmetic, and installs only proved intervals in a private function
namespace. It does not modify the imported original decoder. The separate
printed-table checker verifies all 316 replayed deductions and six final
weighted contradictions, including the explicitly identified alternative.

## 5. Verification and acceptance boundaries

The original frozen v14 verifier has SHA-256

    ec1b7de7b15bcc9d89d12087bff974c68e6d056bdaae26b482d514027ec97993.

All 28 inherited checker/source dependencies used by the physical package
were matched byte for byte to the accepted original archive, Git blob
`4a104744e1bf439e006a1c034eea284fd22fa8c8`. Every new leaf was then freshly
replayed. Source identity is not represented as another replay of the
unchanged 11,278 baseline leaves.

The root independently checked both physical proof packages, all six
bound proofs, the deduplicated union, and the printed arithmetic. Damaged
controls were rejected for missing physical children, duplicate leaves,
invalid inset axes, missing weighted sums, unjustified coordinate bounds,
negative multipliers, an altered original parent and an erased final
contradiction. No human or proof-kernel verification is claimed.

The exact registered caller still retains strict CD and strict radius.
The known feasible closed-weak equality configuration is not excluded by
inventing a positive margin. It remains an essential boundary control.

## 6. Remaining work and fixed ledger

Exactly **79 original paths** remain OPEN. Their full physical predicates
are unchanged, and every incomplete continuation remains internal to its
original path. Neither a feasible LP assignment nor failure to find a
packing establishes a physical counterexample.

The next work combines certified original-parent coordinate bounds with
complete physical alternatives, and resolves inconsistent original-frame
relaxations inside named remaining parents. Retain every unproved child.
When a new method fails to close a parent, record that failure without
changing any count. No new mandatory subgate is introduced.

After all 79 cells have a complete proof, the inherited low-gap theorem,
two sign-root covers and all old and new leaves can assemble the entire
`001/00` exclusion. Only then does the exact witness reversal close
`100/00`. The other 22 OPEN masks require their own complete proofs or a
proved global extraction theorem. All 24 remain OPEN now.

The same 7,915 positional roots retain 5,838 historical closed-Q exclusions
and 2,077 OPEN roots; equality root 7820 is preserved. All 15 roadmap IDs
remain unchanged. A.2, the unrestricted bound, equality classification
and final manuscript remain OPEN.
