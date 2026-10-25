module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3SmallLowScalar
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3HighScalar
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3FarLowScalar

/-!
# Eight squares: the negative-EH1 / BT3 scalar domain

The small-low family keeps its sorted-D baseline and the distinguished two-sign D minorant; all
other families use four ordinary full-circle blocks. The charge of the EH multiplier is subtracted
from the positive mass. Both signed caps and the signed balance are hypotheses of
`scalar_positive`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Scalar
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def left : Family→ℝ
  | .smallLow => 0 | .smallHigh => 1/6 | .farLow => 0 | .farHigh => 1/4
def right : Family→ℝ
  | .smallLow => 1/6 | .smallHigh => frameCap | .farLow => 1/4 | .farHigh => frameCap
def eLeft (f : Family) : ℝ := if far f then 1/10 else 0
def eRight (f : Family) : ℝ := if far f then 1/4 else 1/10

def block (f : Family) (θ z P N : ℝ) (i : Fin 4) : ℝ :=
  if f=.smallLow then SmallLow.block θ P N i else Blocks.block f θ z P N i

lemma frame_domain (f : Family) {θ : ℝ} (hθ : θ∈Icc (left f) (right f)) :
    θ∈Icc 0 frameCap := by
  cases f <;> norm_num [left,right,frameCap] at hθ ⊢ <;>
    exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem family_cover {θ s : ℝ} (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc (0:ℝ) (1/4)) :
    ∃f : Family,θ∈Icc (left f) (right f) ∧ s∈Icc (eLeft f) (eRight f) := by
  by_cases he : s≤1/10
  · by_cases ht : θ≤1/6
    · exact ⟨.smallLow,⟨hθ.1,ht⟩,⟨hs.1,he⟩⟩
    · exact ⟨.smallHigh,⟨(lt_of_not_ge ht).le,hθ.2⟩,⟨hs.1,he⟩⟩
  · by_cases ht : θ≤1/4
    · exact ⟨.farLow,⟨hθ.1,ht⟩,⟨(lt_of_not_ge he).le,hs.2⟩⟩
    · exact ⟨.farHigh,⟨(lt_of_not_ge ht).le,hθ.2⟩,⟨(lt_of_not_ge he).le,hs.2⟩⟩

/-- The four-block inequality. This is a scalar theorem; the budgets come from the errors of the
cycle in `scalar_nonpositive`. -/
theorem scalar_positive (f : Family) {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (left f) (right f)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (eLeft f) (eRight f)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline f (a+z) a z+charge f s+∑i,block f (a+z) z (P i) (N i) i := by
  cases f
  · exact SmallLow.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact HighScalar.small_high_scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact FarLow.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact HighScalar.far_high_scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Scalar
