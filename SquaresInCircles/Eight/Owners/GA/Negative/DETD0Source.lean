module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Source
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD0OriginalStress

/-!
# Eight squares: negative core DE3, nonnegative high A, BT2 and TD0 of either sign

The high negative-DE / BT3 scalar certificate (`NegativeDEPositiveBT.Scalar.scalar_positive`) is
applied at a zero BT tilt, as an algebraic statement; no BT3 witness is assumed or selected. The
BT2 angle stays in B and TD0 stays in the secant D block; the radius `q` and the EH0 witness are
those of the cycle (`original_high_false`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDETD0
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

/-- The owner of BT is B2 here, not the B3 of the scalar certificate; the B2 angle stays in the
masses of B. -/
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
  have ha0 : 0≤aTotal C ga ab := by linarith [ha.1]
  have hb := budgets hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
    (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) hvar ha0 hs
  have hn := high_scalar_nonpositive hg ga ab
    hsorted hcontained hQ hHy hGy hBy hDy hvar ha hs hflat hhg hf
  have hp := NegativeDEPositiveBT.Scalar.scalar_positive .high
    (a:=aTotal C ga ab) (z:=0) (s:=magnitude C)
    (fun i => (blocks C hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).P)
    (fun i => (blocks C hg ga ab (NegativeDEPositiveBT.Explicit.k .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.l .high (aTotal C ga ab))
      (NegativeDEPositiveBT.Explicit.m .high (aTotal C ga ab)) i).N)
    (by rw [add_zero]; exact ha) ha0 le_rfl hb.de_domain
    (fun i => (blocks C hg ga ab _ _ _ i).P_nonneg)
    (fun i => (blocks C hg ga ab _ _ _ i).N_nonneg)
    (by simpa only [add_zero] using hb.positive_bound)
    hb.negative_bound (by simpa only [add_zero] using hb.balance)
  simp only [add_zero] at hp
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

end SquaresInCircles.Eight.GlobalGA.NegativeDETD0
