module

public import SquaresInCircles.Eight.Boundary.SharpEntry
public import SquaresInCircles.Eight.Owners.GA.High.BT2ReducedANegativeOuterE
public import SquaresInCircles.Eight.Owners.GA.High.BT2CoreEFirstNonpositiveT
public import SquaresInCircles.Eight.Owners.GA.Transport.TSecondary

/-!
# Eight squares: the stationary frames of every boundary cycle

`sharp_source_entry` combines `high_GA_BT2_exclusion` with `sharp_source_entry_of_BT2_exclusion`:
the boundary cycle at the stationary level has the stationary frames and normals. With the dual
at the original centres, a packing in the disk of squared radius `q ≤ qStar` has `q = qStar`, its
five squares with a corner on the circle are those of the stationary packing, every gap vanishes,
and `T` and `G` lie on their slider lines (`sharp_original_rigidity`).
-/

section
/-!
## A core E with a `BT2` witness, for every sign of A and T

`core_E_all_T_false` excludes every high-GA source domain with E on the core curve and a feasible
BT2 witness. E is normalized first, on the source domain, which has the gap order; then A is
normalized, and the result is only a signed cycle at the same `q` that satisfies the necessary
conditions. T, B, H and D and the errors of their witnesses survive both moves.

Two splits cover every case:
  * the selected total of the moved A is nonnegative or negative;
  * T has TD0, TD2 with nonpositive signed error, or TD2 with positive signed error.
The branch with A and E both negative and positive TD2 uses the joint-negative stress on the same
cycle and the entry bound of EH1, or the EH0 secondary when it is feasible at the same state.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HighGABT2
open Candidate SignedCycle

/-- No high-GA source domain with E on the core curve has a feasible BT2 witness. A moves only
after E, and the cycle with A moved is used only as a signed cycle, not as a packing. -/
theorem core_E_all_T_false
    {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hcore : (C.point E).Core)
    (hBT : C.Feasible B 2) : False := by
  obtain ⟨R⟩ := core_E_then_A I hqL hqU hcore
  have hBT_E : R.E.cycle.Feasible B 2 :=
    (R.E.other_feasible B (by norm_num [B,D,E])
      (by norm_num [B,E]) 2).2 hBT
  by_cases ha : 0≤GlobalGA.NegativeANormalForm.total
      R.A.ga R.A.ab (delta R.A.cycle.theta G)
        (delta R.A.cycle.theta A)
  · -- Nonnegative A: every normal form of a core E is excluded.
    by_cases ht : tdFlag R.E.source=true ∧
        0<delta R.E.cycle.theta T
    · have hTD : R.E.cycle.Feasible T 2 := by
        have howner := tdFlag_true R.E.source ht.1
        simpa [howner] using R.E.source.feasible T
      have hz : 0≤delta R.A.cycle.theta T := by
        rw [ATransport.original_T_error R.A]
        exact ht.2.le
      exact nonnegative_A_positive_TD2_all_E_false R hqU hBT_E
        hTD hz ha
    · have hnonpos : tdFlag R.E.source=true →
          delta R.A.cycle.theta T≤0 := by
        intro hselected
        rw [ATransport.original_T_error R.A]
        by_contra hgt
        exact ht ⟨hselected,lt_of_not_ge hgt⟩
      exact nonnegative_A_nonpositive_T_all_E_false
        R hqU hBT_E ha hnonpos
  · -- Negative A: a nonpositive T error is excluded for every E, and positive TD2 splits into
    -- a nonnegative E total or exactly one negative DE3 or EH1, with every witness tie kept.
    by_cases ht : tdFlag R.E.source=true ∧
        0<delta R.E.cycle.theta T
    · have hTD : R.E.cycle.Feasible T 2 := by
        have howner := tdFlag_true R.E.source ht.1
        simpa [howner] using R.E.source.feasible T
      have hz : 0≤delta R.A.cycle.theta T := by
        rw [ATransport.original_T_error R.A]
        exact ht.2.le
      rcases R.E_reduced with he|⟨hflat,hcase⟩
      · exact negative_A_nonnegative_E_positive_TD2_false R
          hqU hBT_E hTD hz he ha
      · exact negative_A_negative_E_positive_TD2_false R
          hqU hBT_E hTD hz ha hflat hcase
    · have hnonpos : tdFlag R.E.source=true →
          delta R.E.cycle.theta T≤0 := by
        intro hselected
        by_contra hgt
        exact ht ⟨hselected,lt_of_not_ge hgt⟩
      exact negative_reduced_A_nonpositive_T_false
        R.E.source R.A hqL hqU hBT_E hnonpos ha

end SquaresInCircles.Eight.HighGABT2
end
end
end

section
/-!
## From the exclusion of a high `GA` witness to the stationary frames

`HighGABT2Exclusion` says that no source domain of a high `GA` witness
(`GlobalGA.SourceDomain`) at a squared radius in `[qLow, qCap]` has a feasible `BT2` witness.
Moving `T` turns every high `GA` source into one with a `BT2` witness at the same radius
(`GlobalGA.TTransport.reduce_secondary`), so under that exclusion every feasible `GA` witness of a
boundary cycle is low (`original_GA_low_of_BT2_exclusion`). The other six edges are restricted by
their own lemmas (`GlobalOriginalOwners.normal_owners_of_GA_low`), so every edge has its normal
owner (`original_normal_owners_of_BT2_exclusion`), and the boundary cycle at the stationary level
has the stationary frames and normals (`sharp_source_entry_of_BT2_exclusion`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate SignedCycle

/-- No source domain of a high `GA` witness at a squared radius in `[qLow, qCap]` has a
feasible `BT2` witness, for every sign, owner, radial kind and weak tie. -/
def HighGABT2Exclusion : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (_I : GlobalGA.SourceDomain q C),
    qLow≤q → q≤qCap → C.Feasible B 2 → False

/-- Under `HighGABT2Exclusion` there is no source domain of a high `GA` witness: moving `T`
keeps the radius and gives one with a `BT2` witness. -/
theorem high_GA_source_false_of_BT2_exclusion
    (hBT2 : HighGABT2Exclusion)
    {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) : False := by
  obtain ⟨R⟩ := GlobalGA.TTransport.reduce_secondary I hqL hqU
  exact hBT2 R.transport.source hqL hqU R.BT2

/-- Under `HighGABT2Exclusion` every feasible `GA` witness of a boundary cycle is one of the
two low axes. -/
theorem original_GA_low_of_BT2_exclusion
    (hBT2 : HighGABT2Exclusion)
    {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (hqL : qLow≤q) (hE : C.tangent E≤0) :
    ∀ j : Fin 4,
      (forwardAxis j).Feasible (C.square G) (C.square A) →
      j=0∨j=1 := by
  intro j hj
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (high_GA_source_false_of_BT2_exclusion hBT2
      (GlobalGA.sourceDomain F hq hE 2 (Or.inl rfl) hj)
      hqL hq.2).elim
  · exact (high_GA_source_false_of_BT2_exclusion hBT2
      (GlobalGA.sourceDomain F hq hE 3 (Or.inr rfl) hj)
      hqL hq.2).elim

/-- Under `HighGABT2Exclusion` every edge has its normal owner: the other six edges by their own
lemmas, `GA` by `original_GA_low_of_BT2_exclusion`. -/
theorem original_normal_owners_of_BT2_exclusion
    (hBT2 : HighGABT2Exclusion)
    {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (hqL : qLow≤q) (hE : C.tangent E≤0) :
    Candidate.OwnerRestriction C SignedCycle.normalOwners :=
  GlobalOriginalOwners.normal_owners_of_GA_low F hq hE
    (original_GA_low_of_BT2_exclusion hBT2 F hq hqL hE)

/-- `HighGABT2Exclusion` gives the stationary frames and normals of the boundary cycle at the
stationary level. -/
theorem sharp_source_entry_of_BT2_exclusion
    (hBT2 : HighGABT2Exclusion) : SharpSourceEntry := by
  intro S N hselected
  let F := NormalizationBridge.recoveredFrame N
  have hq : sourceLevel Stationary.qStar∈Icc (5/2:ℝ) Q0 :=
    NormalizationBridge.source_radius_mem GeometricModel.sharp_le_Q1
  have hqL : qLow ≤ sourceLevel Stationary.qStar := by
    rw [GeometricModel.sharp_source_level]
    have h := Stationary.qStar_limits.1
    norm_num [qLow] at h ⊢
    linarith
  have hE : N.recovered.tangent E≤0 :=
    (SignedCycle.atFrame_y_nonpos_iff F E).1
      (NormalizationBridge.recovered_E_nonpos N)
  have ho : Candidate.OwnerRestriction N.recovered SignedCycle.normalOwners :=
    original_normal_owners_of_BT2_exclusion hBT2 F hq hqL hE
  exact source_witnesses_of_normal_owners N hselected ho

end SquaresInCircles.Eight
end
end
end

section
/-!
## No high `GA` witness with a `BT2` witness

`high_GA_BT2_exclusion` proves `HighGABT2Exclusion`. When `E` is outer, normalizing `A`
suffices: the transported total of `A` is nonnegative or negative, and both owners and signs of
`TD` are excluded. When `E` is a core square, `E` is normalized before `A` moves, and the
core-`E` theorem for every sign of `T` excludes that case. The transports keep the seven
separating axes, the signed angular errors, the radial kinds and the squared radius `q`; a cycle
with `A` moved is used only as a signed cycle, not as a packing.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate SignedCycle

/-- No source domain of a high `GA` witness has a `BT2` witness, for every radial kind and
sign. -/
theorem high_GA_BT2_exclusion : HighGABT2Exclusion := by
  intro q C I hqL hqU hBT
  rcases I.radial E with houter|hcore
  · obtain ⟨O⟩ := HighGABT2.A_normalize I hqL hqU
    by_cases ha : 0≤GlobalGA.NegativeANormalForm.total O.ga O.ab
        (delta O.cycle.theta G) (delta O.cycle.theta A)
    · exact HighGABT2.reduced_nonnegative_A_outer_E_false
        I O hqU hBT houter ha
    · exact HighGABT2.negative_A_outer_E_all_T_false
        I O hqL hqU houter hBT ha
  · exact HighGABT2.core_E_all_T_false I hqL hqU hcore hBT

end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight
open Stationary Coordinates GeometricModel

/-- Every boundary normalization at `qStar` with the separating axes of the packing has the
stationary frames and normals. -/
theorem sharp_source_entry : SharpSourceEntry :=
  sharp_source_entry_of_BT2_exclusion high_GA_BT2_exclusion

/-- A packing in the disk of squared radius `q ≤ qStar` has `q = qStar`, the five anchors at
their stationary positions, no gap, and `T`, `G` on their slider lines. -/
theorem sharp_original_rigidity
    {S : Fin 8 → UnitSquare} {q : ℝ}
    (N : GlobalNormalization S qStar)
    (hselected : N.source.selected=N.recovered.selected)
    (hp : SqPacking N.squares (0,0) q)
    (hq : q≤qStar) :
    q=qStar ∧
      StationaryFrames sharpData N.source.square ∧
      (∀ i, (N.source.selected i).normal (N.source.square i)
        (N.source.square (next i))=stationaryNormal sharpData i) ∧
      (∀ i : Fin 5,
        GeometricModel.originalPositions N i.castSucc.castSucc=
          sharpData.anchorCenters i) ∧
      (∀ e : Fin 7,
        OriginalDual.gap sharpData (GeometricModel.originalPositions N) e=0) ∧
      ∃ Z η : ℝ,
        GeometricModel.originalPositions N 5=sharpData.pT Z ∧
        GeometricModel.originalPositions N 6=sharpData.pG η :=
  sharp_source_entry_original_rigidity
    sharp_source_entry N hselected hp hq

end SquaresInCircles.Eight
end
end
end
