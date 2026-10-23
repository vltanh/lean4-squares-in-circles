module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowScalar
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3High

/-!
# Full negative-DE3 / nonnegative-BT3 scalar exclusion

Uncompiled low/high assembly. The two closed total-angle families cover
the whole captured variation interval. Every actual A/BT split and DE
magnitude is retained, and the fourth block remains the original signed
TD0 singleton. No scalar endpoint or support branch is assumed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Scalar
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem family_cover {θ : ℝ} (hθ : θ∈Icc 0 frameCap) :
    ∃f : Family,θ∈Icc (Explicit.left f) (Explicit.right f) := by
  by_cases h : θ≤1/6
  · exact ⟨.low,⟨hθ.1,h⟩⟩
  · exact ⟨.high,⟨(lt_of_not_ge h).le,hθ.2⟩⟩

theorem scalar_positive (f : Family) {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.baseline f a z s+
      ∑i,Blocks.block f (a+z) z s (P i) (N i) i := by
  cases f
  · exact Low.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance
  · exact High.scalar_positive P N hθ ha hz hs hP hN hPb hNb hbalance

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.Scalar
