module

public import SquaresInCircles.Eight.Owners.GA.Transport.TSecondary
public import SquaresInCircles.Eight.Boundary.NormalizedSourceEntry
public import SquaresInCircles.Eight.Boundary.SharpEntry

/-!
# Eight squares: from the exclusion of a high `GA` witness to the stationary frames

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
