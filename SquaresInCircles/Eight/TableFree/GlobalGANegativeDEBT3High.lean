module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighSplit
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3HighConcentration

/-!
# Complete high-total negative-DE3 / positive-BT3 scalar exclusion

Uncompiled assembly of Sections 5--8. Every original split, every DE
magnitude, both surplus signs and all four signed-mass blocks are joined.
The full-circle scalar is used only below the original sorted-D stress.
No endpoint, right-derivative, concentration or support-switch premise
is left for the source adapter to supply.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.High
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem pure_positive {a z s : ℝ} (hθ : a+z∈Icc (1/6:ℝ) (7/10))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 frameCap) (i j : Fin 4) :
    0<Explicit.baseline .high a z s+Blocks.pure .high (a+z) z s i j := by
  by_cases hst : s≤a+z
  · have hp := HighSplit.negative_positive hθ ha hz ⟨hs.1,hst⟩ (Blocks.ordinaryIndex j)
    have hl := Explicit.full_lower .high a z s
    have he : Blocks.pure .high (a+z) z s i j=
        Explicit.V .high (a+z) (Blocks.ordinaryIndex j) (a+z-s) := by
      change (if s≤a+z then Blocks.negative .high (a+z) (a+z-s) j else _) = _
      rw [if_pos hst,Blocks.negative_to_ordinary]
    rw [he]
    linarith
  · have hp := HighSplit.equal_positive hθ ha hz
    have hc := PositivePure.pure_intrinsic_lower .high hθ ha hz
      (show s∈Icc (a+z) frameCap from ⟨(lt_of_not_ge hst).le,hs.2⟩) i j
    exact hp.trans_le hc

/-- Full closed-domain positivity for the actual four-block mass budgets. -/
theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc 0 frameCap) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.baseline .high a z s+
      ∑i,Blocks.block .high (a+z) z s (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := HighConcentration.sum_to_pure P N hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) hs hP hN hPb hNb hbalance
  have hh := pure_positive hθ ha hz hs i j
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.High
