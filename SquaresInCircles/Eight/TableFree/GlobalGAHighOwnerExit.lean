module

public import SquaresInCircles.Eight.TableFree.GlobalGATransportTSecondary
public import SquaresInCircles.Eight.TableFree.GlobalGASourceDomain
public import SquaresInCircles.Eight.TableFree.NormalizedSourceEntry

/-!
# Exact remaining source obligation for original high-GA exclusion

Uncompiled proof-interface join. The complete T reduction now gives an
actual BT2 witness on a same-q necessary descendant, for *every* high-GA
source, with no signed A/E assumption. Thus the only remaining high-GA
mathematical obligation is to exclude such a BT2 source domain. This file
packages that obligation as a Prop rather than assuming it as an axiom.

The original high-GA witness is selected on the untouched boundary cycle.
Once this source contradiction is proved, normal owners and the new sharp
entry follow through the existing original-source equality argument.
A conditional theorem is not an inhabitant of SharpSourceEntry.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate SignedCycle

/-- The remaining whole-domain high-GA source exclusion; it includes
every selected A/E/T sign, owner, radial kind and weak tie. The BT2
witness belongs to the same-radius *current* necessary cycle. This
proposition has no inhabitant declared in this file. -/
def HighGABT2Exclusion : Prop :=
  ∀ {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C),
    qLow≤q → q≤qCap → C.Feasible B 2 → False

/-- An actual high-GA original cycle is impossible once the whole BT2
case has been proved. The moving-T reduction retains the original radius
and returns a new SourceDomain on which the BT2 premise is genuine. -/
theorem high_GA_source_false_of_BT2_exclusion
    (hBT2 : HighGABT2Exclusion)
    {q : ℝ} {C : SignedCycle} (I : GlobalGA.SourceDomain q C)
    (hqL : qLow≤q) (hqU : q≤qCap) : False := by
  obtain ⟨R⟩ := GlobalGA.TTransport.reduce_secondary I hqL hqU
  exact hBT2 R.transport.source hqL hqU R.BT2

/-- All feasible GA witnesses are low on the *original* physical
boundary. Selecting a hypothetical high GA owner changes no other
initially retained normal, and the contradiction uses the actual q. -/
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

/-- The other six owner restrictions are already geometric source lemmas;
the only remaining owner is GA. This includes every feasible weak tie. -/
theorem original_normal_owners_of_BT2_exclusion
    (hBT2 : HighGABT2Exclusion)
    {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0)
    (hqL : qLow≤q) (hE : C.tangent E≤0) :
    Candidate.OwnerRestriction C SignedCycle.normalOwners :=
  GlobalOriginalOwners.normal_owners_of_GA_low F hq hE
    (original_GA_low_of_BT2_exclusion hBT2 F hq hqL hE)

/-- This is a genuine source-to-public *conditional* adapter. The only
remaining hypothesis is precisely HighGABT2Exclusion; it is not hidden
inside a transport, scalar estimate, or nominally universal entry. -/
theorem sharp_source_entry_of_BT2_exclusion
    (hBT2 : HighGABT2Exclusion) : SharpSourceEntry := by
  intro S N hselected
  let F := NormalizationBridge.recoveredFrame N
  have hq : sourceLevel ExactFamily.qStar∈Icc (5/2:ℝ) Q0 :=
    NormalizationBridge.source_radius_mem GeometricModel.sharp_le_Q1
  have hqL : qLow ≤ sourceLevel ExactFamily.qStar := by
    rw [GeometricModel.sharp_source_level]
    have h := ExactFamily.qStar_limits.1
    norm_num [qLow] at h ⊢
    linarith
  have hE : N.recovered.tangent E≤0 :=
    (SignedCycle.atFrame_y_nonpos_iff F E).1
      (NormalizationBridge.recovered_E_nonpos N)
  have ho : Candidate.OwnerRestriction N.recovered SignedCycle.normalOwners :=
    original_normal_owners_of_BT2_exclusion hBT2 F hq hqL hE
  exact source_witnesses_of_normal_owners N hselected ho

end SquaresInCircles.Eight.TableFree
