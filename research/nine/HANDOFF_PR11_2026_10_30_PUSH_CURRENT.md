# PR #11 — current handoff

> **Latest substantive continuation (October 31, 2026): READ FIRST [ADOPTION_PHYSICAL_CAP_AND_GLOBAL_CUT_THEOREMS_2026_10_31.md](ADOPTION_PHYSICAL_CAP_AND_GLOBAL_CUT_THEOREMS_2026_10_31.md).** The new physical two-square cap theorem proves the sharp radius for ANY actual parallel four-plus-three projection chains, with arbitrary square orientations and without common coordinate separation of the other pairs. It is committed as b873732506f2fc2fcec3fbdf2d0820daab679379 and passed separate hand reviews. New full-cut tree-size, boundary-contact margin, common-side endblock pressure and whole-angle access theorems are also adopted there. **No new original fine/coarse closure:** 37/58 coarse, 2373/2513 fine, 18/38 exterior. A global extraction/completion theorem and mixed-interface treatment are still missing. No Lean, CI, numerical tests or mathematical scripts were used. The local-frontier sections below preserve earlier work and are fallback references, not the current discovery order.

> **Research strategy correction (October 31, 2026):** [N9_GLOBAL_PROOF_REORIENTATION_2026_10_31.md](N9_GLOBAL_PROOF_REORIENTATION_2026_10_31.md) is now the current discovery roadmap. The preceding four-row-first proposal is **superseded**. Focus on broad annular/center charge, branching-width compensation and endblock effective-wrench mechanisms; the original 58 coarse and 2,513 fine IDs are acceptance checks, not the order for proving lemmas. Original progress stays 37/58 coarse, 2373/2513 fine, 18/38 six-body exterior.


> **Historical reset:** [N9_RESET_HAND_PROOF_GATES_2026_10_31.md](N9_RESET_HAND_PROOF_GATES_2026_10_31.md) records the superseded four-row-first proposal. Its original full-star, mean, physical-mask and three-extra requirements remain valid, but its research priority is replaced by the broad continuation above.


Updated October 31, 2026 UTC. Branch: `research/nine-tablefree-hand`.

**Current unrestricted theorem status: OPEN.** The latest continuation closes the whole A-only radial-endpoint union by hand. The active local remainder is the A-only both-physically-unique B,C side family, followed by the complete original L135 assembly/audit. The original inventories remain **37/58 coarse, 2373/2513 fine, 18/38 reconciled exterior rows**.

Read the [current hand-only frontier](D02_L135_HAND_ONLY_REPLACEMENT_FRONTIER_2026_10_31.md) first. It supersedes the earlier chronological frontier. This concise handoff replaces repeated historical sections; the complete preceding handoff remains in Git at `47211666cdedabdbd11160eeecb2da7352da4329`, and every individual manuscript remains in the repository.

## 1. Work preserved and pushed in this continuation

The preceding final opposite-return batch had been saved in a Git tree but not committed to the branch. It was recovered and attached as:

    47211666cdedabdbd11160eeecb2da7352da4329
    [skip ci] n=9: preserve full opposite-return hand join and uniform moment lemmas

This preserves the [complete opposite-return hand join](WEST_STRICT_OPPOSITE_RETURN_ALL_MASKS_COMPLETE_HAND_JOIN_2026_10_31.md), its RR and UU completion proofs, the nonacute three-quarters slope theorem, and the earlier three-angle one-half gap theorem. The branch advance was verified. Do not repeat the earlier inaccurate claim that this final batch had already been a branch commit before the recovery.

The new substantive hand-theorem commits are:

| Commit | Result |
| --- | --- |
| `3994f001b0a656fd1594a3c1e10b45cdda1e6466` | All three positive full-moment contact gaps are below 2/5. |
| `e749f54df0893d83999c6ccca73f3a26bd30fe2d` | Every literal strict radial/unique side channel has resultant slope greater than 21/25, for every exterior aperture. |
| `43da8869961d2ffd863c5bc6473b6822e90f142e` | Such an opposite circle resultant is farther than sqrt(6) from its original radial side port. |
| `10d3f5076eef71d2981cfe9091d58c577c76e787` | Both entire asymmetric A-only radial masks are excluded by the same distance contradiction; with the prior RR proof, the whole radial union is hand-closed. |

The current frontier was consolidated after these proofs. All write messages use `[skip ci]`; no Lean or workflow was invoked.

## 2. The new common argument

The new generic scalar theorem is

    THREE_ANGLE_FULL_MOMENT_ALL_GAPS_BELOW_TWO_FIFTHS_HAND_THEOREM_2026_10_31.md.

If A,B,C lie in (pi/4,pi/2), sum to pi, and positive gaps g_i=1-lambda*sin(i) satisfy

    product(g_i)=product(sin(i)-cos(i)),

then every g_i<2/5. The proof chooses a largest alleged gap, reduces the other two angles monotonically to equality, and uses three exact rational intervals plus one concave cubic. It proves the whole continuous domain.

In the original A-only chart, the actual complete moments give

    rho*u=mu*(s-c), nu*t=rho*(H-k), mu*(1-omega)=nu*(S-C).

Thus, with w=1-omega and the third angle pi-alpha-beta,

    0<u,t,w<2/5.

The actual unique V circle corner Z and exterior ports K,L have literal displacement coordinates

    Z-K=(1+cos(alpha)+sin(alpha), w+cos(alpha)-sin(alpha)),
    Z-L=(1+cos(beta)+sin(beta), t+cos(beta)-sin(beta))

in their respective original orthonormal frames. Both squared distances are strictly below 6.

The new whole-aperture channel source is

    RADIAL_UNIQUE_SIDE_CHANNEL_WHOLE_APERTURE_TWENTY_ONE_TWENTY_FIFTHS_SLOPE_HAND_THEOREM_2026_10_31.md.

It uses the complete original radial/unique endpoint stars and two circle equations to prove z>21/25. Its acute proof retains the circle correlation via dD/dy<4/7, then uses 26 printed exact rational comparisons over seven q intervals and four radius slabs. Two impossible slabs are explicitly excluded by the angular upper bound. The nonacute proof uses three complete intervals. All derivative signs, radical enclosures and rational formulas are printed; no generated pose cover is invoked.

The geometric source is

    RADIAL_PORT_RESULTANT_SLOPE_FORCES_SQRT_SIX_SEPARATION_HAND_LEMMA_2026_10_31.md.

For the actual radial port Q=d*f+chi*w, 0<chi<1/2, and the actual opposite circle point Z=R*(-z*f+w)/sqrt(1+z^2), it proves

    |Z-Q|^2>6+29587/20437500.

The original complete A/D/V forces identify this same Z with the V circle corner. The full radial origin moment proves chi>0 without equal circle weights. For B radial Q=K, and for C radial Q=L. Both asymmetric masks therefore contradict their actual distance upper bounds. The full literal mapping, reflection and parallel/tie entry are in

    UNIQUE_V_A_ONLY_BOTH_ASYMMETRIC_RADIAL_MASKS_SQRT_SIX_COMPLETE_HAND_EXCLUSION_2026_10_31.md.

Together with `UNIQUE_V_A_ONLY_RADIAL_RADIAL_COMPLETE_HAND_EXCLUSION_2026_10_31.md`, this removes the entire historical 39488-node A-only radial-endpoint role. The old computational cover is not a premise of this hand union.

## 3. Current complete local hand exits

Do not restart these already written complete hand features:

| Feature | Read first |
| --- | --- |
| Every physical-two two-strict owner | `D02_L135_TWO_STRICT_ALL_OWNERS_COMPLETE_HAND_EXCLUSION_2026_10_31.md` |
| Both D-only West roofs | `PHYSICAL_TWO_WEST_STRICT_D_OWNED_ALL_ROOFS_COMPLETE_HAND_JOIN_2026_10_31.md` |
| A-owned perpendicular D-side return | `WEST_STRICT_PERPENDICULAR_D_SIDE_RETURN_COMPLETE_HAND_JOIN_2026_10_31.md` |
| Entire opposite-D return, all masks and both N widths | `WEST_STRICT_OPPOSITE_RETURN_ALL_MASKS_COMPLETE_HAND_JOIN_2026_10_31.md` |
| Entire D-owned far A return | `TYPE_II_FAR_RETURN_ALL_MASKS_COMPLETE_HAND_JOIN_2026_10_31.md` |
| Entire unique-V A-only radial side union | `UNIQUE_V_A_ONLY_BOTH_ASYMMETRIC_RADIAL_MASKS_SQRT_SIX_COMPLETE_HAND_EXCLUSION_2026_10_31.md`, Section 8 |

Each retains its stated original full-star, owner, mean, physical-mask and common-selection scope. A theorem for unloaded N is not automatically transferred to loaded-N L1345. A proper-feature exclusion does not change an original graph/load-row flag.

## 4. The actual next local mathematical obligation

Work on **unique-V A-only, both B and C physically unique, N the original unloaded unit side transmitter**.

The exact retained system is in

    TYPE_II_A_ONLY_WHOLE_TRANSVERSE_GAP_AND_EXACT_BOTH_UNIQUE_SIDE_MATRIX_2026_10_29.md,
    UNIQUE_V_A_ONLY_CENTRAL_AND_SIDE_POCKET_MUTUAL_HAND_EXCLUSION_2026_10_31.md.

Keep

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C},

with the positive AD chord, all nine actual squares, full original equations, means, physical circle points and common normal selection. The already proved full angular entry is

    pi/4<delta_B,delta_C<pi/2,
    pi/2<Theta=delta_B+delta_C<3*pi/4.

The new u,t,w<2/5 estimates apply throughout this remaining feature. The exact unit-bridge matrix, its possible singular values, the original positive hub cubic and both endpoint circle equations remain. Do not invert a matrix without retaining its singular alternative.

The current complete capacity theorem is only

    capacity(central region and N outer pocket combined)<=1.

**A capacity-one bound at each hub is insufficient:** 1+1+1 permits the required three extras. A sufficient whole-family target is A-pocket emptiness and D-pocket capacity one, or another valid joint estimate reducing the total to two.

The physical hubs are not interchangeable. In the original h,e frame,

    R_A=W+(1-u)*e, K=R_A-h-e,
    A=R_A-[0,1]*h-[0,1]*e.

A's exterior ports R_A,K are opposite vertices and its exterior roof vertex is K+e. The V and B normal ownership at these two ports is literal. A geometric high-roof argument must establish the roof bound, endpoint moments/proper rays, clearance and protected circle interval from these original stars.

For D,

    W=P+(1-t)*tD,
    L=W-nD-tD,
    J_D=P-t*tD=L+nD,
    D=W-[0,1]*nD-[0,1]*tD.

The exterior route P--J_D--L has first length t<2/5 and second length one. P is a V corner and an interior point of a D side. V does not own nD at P. Do not substitute the opposite-vertex tip-owned roof theorem at this D interface.

### Exploratory attack diagnostic, not a theorem

A numerical solve of the necessary complete six-core equations produced a candidate near

    alpha=49.43035 degrees,
    beta=46.39108 degrees,
    R=2.04486850,
    u=.3022833, t=.2680255, w=.0413581.

A numerical geometric probe suggested a short feasible interval of N transverse offsets for those six squares. This is not an exact existence proof, not a nine-square counterexample, and not a premise of any hand theorem. It indicates that simply asserting inconsistency of the six-core equilibrium system is an unsafe attack direction. At that diagnostic, A's roof is high and its available comparison-circle pieces are short, while D has a lower short-side roof. No general roof inequality was adopted from these tests.

## 5. Original global ledger and remaining parent families

The goal is the unrestricted nine-square theorem

    R^2>=1105/256

and its full equality classification. The six-, seven-, eight- and nine-body labels below count the positive-stress component, not the total number of physical squares. Every caller still contains all nine actual units.

Original flags remain unchanged:

    37/58 coarse closed; 21 open.
    2373/2513 fine checked; 140 open.
    Exterior six-body table: 18/38 checked.

The 21 open coarse cells are:

| Positive-component size | Original open coarse cells |
| --- | --- |
| 6 | C1.6.b0 |
| 7 | C1.5.b2; C1.6.b1; C1.7.b0; C2.35.b0 |
| 8 | C1.6.b2; C1.7.b1; C1.8.b0; C2.35.b1; C2.36.b0; C2.45.b0 |
| 9 | C1.6.b3; C1.7.b2; C1.8.b1; C1.9.b0; C2.35.b2; C2.36.b1; C2.37.b0; C2.45.b1; C2.46.b0; C2.55.b0 |

Read `CYCLIC_CELL_LEDGER.md`, `DEEP_GATED_ROADMAP.md` and `PROGRESS.md` for the original inventory. Do not change their denominators or invent a new original fine ID for a proper physical feature.

Within C1.6.b3 the whole connected-private partition3 is already excluded by the return-free true-middle-B3 theorem; disconnected clear-Q Types I and II remain. Their actual larger middle stars cannot be shortened to manufacture B3. See `ADOPTION_RETURN_FREE_MIDDLE_ROOT_CAPACITY_AND_COMPLETE_RR_PROMOTION_2026_10_30.md` and its original full reviews.

Other unresolved global families include one-/zero-RR short seven-cycles with both actual extras, loaded hubs and branching blocks, wholly unloaded modules with at least three cut edges, and two-block articulation pressure. A two-terminal module need not have exactly two outgoing edges. A theorem for an entire simple positive component cannot be applied to a chorded cycle without a literal stronger caller.

The later physical stress sources provide a compatible physical force-and-torque construction at their stated scope. The downstream G4.2.c audit still requires common-normal compatibility, full prerequisites, nonidentity, true degrees and physical-mask checks. The present family exclusions do not discharge that audit or the unrestricted theorem.

## 6. Proof and repository rules

The current requested workflow is **hand proof, no Lean, skip CI**. Exact tables may support hand proofs. Numerical programs may test attack directions but must not discharge exclusions or supply theorem premises.

Keep all actual squares, full positive stars, original means, normal choices and all physical circle corners. An individual zero coefficient does not change a two-physical-corner mask into a unique mask. Retain the distinct loaded-N equation in L1345; do not apply an unloaded transmitter theorem there. Do not change a stress after a motion without proving the required transfer.

The same-nine R>2 entry is the complete analytic hand measure route, with total mass 8997/1000<9. The historical checking program is not required by the current hand arguments.

The new manuscripts have not undergone a separate independent audit or kernel verification. No new original ledger flag, unrestricted theorem, equality classification, Lean compilation, CI run, Comparator export or NanoDa acceptance is claimed. The PR remains draft.

Commit substantive research through the connected GitHub tools on this branch, use `[skip ci]`, and verify the actual branch ref after writing. Update the current frontier when a whole original physical family closes. Do not leave final manuscript trees unattached to a branch commit.

