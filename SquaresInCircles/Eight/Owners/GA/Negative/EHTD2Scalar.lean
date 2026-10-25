module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SmallLow
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2SmallHigh
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLow
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarHigh

/-!
# Eight squares: every negative-EH / positive-TD2 scalar regime

The two EH-magnitude regimes and the two families of the total positive angle cover the whole
closed range (`family_cover`). Boundaries are included in both adjacent proofs. `scalar_positive`
is a scalar theorem; the exclusion of a signed cycle (`NegativeEHPositiveTD.Source.original`) adds
the stress comparison of the cycle, both mass budgets and the signed balance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Scalar
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem family_cover {θ s : ℝ} (hθ : θ∈Icc 0 frameCap)
    (hs : s∈Icc (0:ℝ) (1/4)) :
    ∃ r : Regime,∃ f : Family,
      θ∈Icc (Explicit.left r f) (Explicit.right r f) ∧
      s∈Icc (Explicit.eLeft r) (Explicit.eRight r) := by
  by_cases he : s≤1/10
  · by_cases ht : θ≤1/6
    · exact ⟨.small,.low,⟨hθ.1,ht⟩,⟨hs.1,he⟩⟩
    · exact ⟨.small,.high,⟨show (1/6:ℝ) ≤ θ by linarith,hθ.2⟩,⟨hs.1,he⟩⟩
  · by_cases ht : θ≤1/4
    · exact ⟨.far,.low,⟨hθ.1,ht⟩,⟨show (1/10:ℝ) ≤ s by linarith,hs.2⟩⟩
    · exact ⟨.far,.high,⟨show (1/4:ℝ) ≤ θ by linarith,hθ.2⟩,⟨show (1/10:ℝ) ≤ s by linarith,hs.2⟩⟩

theorem scalar_positive (r : Regime) (f : Family) {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (Explicit.left r f) (Explicit.right r f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (Explicit.eLeft r) (Explicit.eRight r))
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase r f a z s+∑i,Blocks.block r f (a+z) z (P i) (N i) i := by
  cases r <;> cases f
  · exact SmallLow.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact SmallHigh.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact FarLow.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact FarHigh.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Scalar
