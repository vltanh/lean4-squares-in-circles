module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD0OriginalStress

/-!
# Negative core DE3, nonnegative high A, actual BT2 and arbitrary TD0

Uncompiled original-witness completion of
HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_A_TD0_EXCLUSION.md.
The high negative-DE / BT3 scalar certificate is applied at an
algebraic zero BT tilt, but no BT3 witness is assumed or selected.
The original BT2 angle remains in B and TD0 remains in the secant D
block; the same original q and original EH0 witness are used.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDETD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

/-- The genuinely new original owner is B2, not the B3 of the
scalar certificate; the original B2 angle remains in B's masses. -/
theorem original_flat_high_false {Q : ℝ} {C : SignedCycle}
    (hg : Fin 4) (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (hs : delta C.theta D≤0) (hflat : (C.point E).a=7/12)
    (hhg : hg=0∨hg=2)
    (hf : ∀i,C.Feasible i (owners hg ga ab i)) : False := by
  let a := aTotal C ga ab
  let k := Explicit.k .high a
  let l := Explicit.l .high a
  let m := Explicit.m .high a
  have ha0 : 0≤a := by dsimp [a]; linarith [ha.1]
  have hb := budgets hg ga ab k l m hvar ha0 hs
  have hn := high_scalar_nonpositive hg ga ab
    hsorted hcontained hQ hHy hGy hBy hDy hvar ha hs hflat hhg hf
  have hp := Scalar.scalar_positive .high
    (a:=a) (z:=0) (s:=magnitude C)
    (fun i => (blocks C hg ga ab k l m i).P)
    (fun i => (blocks C hg ga ab k l m i).N)
    (by simpa only [add_zero] using ha) ha0 le_rfl hb.de_domain
    (fun i => (blocks C hg ga ab k l m i).P_nonneg)
    (fun i => (blocks C hg ga ab k l m i).N_nonneg)
    (by simpa only [add_zero] using hb.positive_bound)
    hb.negative_bound (by simpa only [add_zero] using hb.balance)
  change 0<Explicit.baseline .high a 0 (magnitude C)+
    ∑i,DEBlocks.block .high a 0 (magnitude C)
      (blocks C hg ga ab k l m i).P
      (blocks C hg ga ab k l m i).N i at hp
  exact (not_le_of_gt hp) hn

theorem original_high_false {Q : ℝ} {C : SignedCycle}
    (ga ab : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained Q)
    (hQ : Q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hEy : (C.point E).y≤0) (hEc : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (ha : aTotal C ga ab∈Icc (1/6:ℝ) frameCap)
    (hs : delta C.theta D≤0)
    (hHG : C.Feasible H 0∨C.Feasible H 2)
    (hGA : C.Feasible G (if ga then 3 else 2))
    (hAB : C.Feasible A (if ab then 2 else 0))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D 3) (hEH : C.Feasible E 0) : False := by
  have hflat := NegativeDEPositiveBT.Source.original_flat hsorted hcontained
    hQ hEy hEc hEH
  obtain ⟨hg,hhg,hHG'⟩ : ∃hg : Fin 4,(hg=0∨hg=2)∧C.Feasible H hg := by
    rcases hHG with hh|hh
    · exact ⟨0,Or.inl rfl,hh⟩
    · exact ⟨2,Or.inr rfl,hh⟩
  apply original_flat_high_false hg ga ab hsorted hcontained hQ
    hHy hGy hBy hDy hvar ha hs hflat hhg
  intro i
  fin_cases i
  · simpa [owners,H] using hHG'
  · simpa [owners,G] using hGA
  · simpa [owners,A] using hAB
  · simpa [owners,B] using hBT
  · simpa [owners,T] using hTD
  · simpa [owners,D] using hDE
  · simpa [owners,E] using hEH

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDETD0
