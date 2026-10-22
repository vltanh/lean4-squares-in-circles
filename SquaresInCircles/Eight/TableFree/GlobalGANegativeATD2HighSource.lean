module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2HighAffected

/-!
# The complete original negative-A / high positive-TD2 contradiction

Uncompiled transcription of Sections 9--12. Every concentrated
alternative is paid by the actual coefficient family. The final
statement applies directly to the original sorted and contained cycle
and its original owner witnesses.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.HighSource
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem negative_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (hsz : s≤z) (i : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
      V R (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i)
        (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s i) (z-s) := by
  by_cases hi : HighUnaffected.Unaffected atG i
  · exact HighUnaffected.original atG hz hs hsz i hi
  · have hh := HighAffected.original atG hz hs hsz
    cases atG <;> fin_cases i <;>
      simp [HighUnaffected.Unaffected] at hi <;>
      simpa [HighAffected.value,Source.pWeights,Source.qWeights,lambdaG,lambdaB,Explicit.m] using hh

theorem pure_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i j : Fin 4) :
    0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z+
      Concentration.pure R (diagonal-1/2)
        (Source.pWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s)
        (Source.qWeights atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.m .high z) s) 3 i j s z := by
  by_cases hsz : s≤z
  · simpa only [Concentration.pure,if_pos hsz] using negative_positive atG hz hs hsz j
  · have hp := AffectedPositive.all_positive_reduces_to_equal .high atG hz hs (le_of_not_ge hsz) i
    have he : 0<baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z z := by
      cases atG
      · exact (Certificate.high_endpoints hz).2.2.2.2
      · exact (Certificate.high_endpoints hz).2.2.2.1
    simp only [Concentration.pure,if_neg hsz]
    linarith

theorem intrinsic_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG))
    (i j : Fin 4) :
    0<Source.intrinsic atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z i j := by
  rw [HighSaturated.intrinsic_eq_pure atG hz hs i j]
  exact pure_positive atG hz hs i j

theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : Source.aError C atG=-s)
    (hflat : (C.point A).a=7/12)
    (hz : delta C.theta T∈Icc (1/5:ℝ) (7/10:ℝ))
    (hhg : hg=0 ∨ hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  obtain ⟨i,j,hh⟩ := Source.original_intrinsic_nonpositive .high atG
    hsorted hcontained hq hHy hGy hBy hDy hvar hs ha hflat hz hhg hHG hGA hAB hBT hTD hDE hEH
  exact (not_le_of_gt (intrinsic_positive atG hz hs i j)) hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.HighSource
