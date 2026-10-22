module

public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDScalarCurvature

/-!
# All eight intrinsic negative-TD2 endpoints are positive

Uncompiled transcription of Sections 4--7. Five endpoints use the
whole trapezoid directly. The three pure-negative endpoints use the
actual fixed-e concavity and the three original boundary curves.
All auxiliary mass, coefficient, and boundary premises are discharged.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD
open Secondary TensorWholeIntervalPolynomial TwoVariablePolynomial

namespace Analytic

theorem whole_positive (f : Certificate.Kind) (hf : Certificate.Whole f)
    {t E : ℝ} (hd : NegativeTD.Domain t E) : 0<value f t E := by
  have hn := Certificate.domain_of_angles hd
  have hp := polynomial_transfer f hn (Certificate.whole_positive f hf hn)
  simpa only [add_sub_cancel] using hp

theorem negative_low_boundary (i : Fin 3) {E : ℝ} (hE : E∈Icc 0 L) :
    0<negativeScalar i L E := by
  have hd : Certificate.Domain 0 E := by
    refine ⟨?_,?_⟩
    · norm_num [Certificate.d]
    · simpa [Certificate.L,L] using hE
  have hp := Certificate.boundary_positive .low i
    (by simpa [Certificate.boundaryLength,Certificate.L,L] using hE)
  have hnum : 0<evaluate 0 E (Certificate.numerator (.negative i)) := by
    simpa [Certificate.boundary,evaluate_restrict] using hp
  have hh := polynomial_transfer (.negative i) hd hnum
  simpa [value,Certificate.L,L] using hh

theorem negative_high_boundary (i : Fin 3) {E : ℝ} (hE : E∈Icc 0 frameCap) :
    0<negativeScalar i frameCap E := by
  have hd : Certificate.Domain (Certificate.d:ℝ) E := by
    constructor
    · norm_num [Certificate.d]
    · simpa [Certificate.L,Certificate.d,frameCap] using hE
  have hp := Certificate.boundary_positive .high i
    (by simpa [Certificate.boundaryLength,Certificate.h,frameCap] using hE)
  have hnum : 0<evaluate (Certificate.d:ℝ) E (Certificate.numerator (.negative i)) := by
    simpa [Certificate.boundary,evaluate_restrict] using hp
  have hh := polynomial_transfer (.negative i) hd hnum
  simpa [value,Certificate.L,Certificate.d,frameCap] using hh

theorem negative_equal_boundary (i : Fin 3) {E : ℝ} (hE : E∈Icc L frameCap) :
    0<negativeScalar i E E := by
  have hd : NegativeTD.Domain E E := ⟨hE,⟨by dsimp [L] at hE; linarith [hE.1],le_rfl⟩⟩
  have hn := Certificate.domain_of_angles hd
  have hx : E-(Certificate.L:ℝ)∈Icc 0 (Certificate.boundaryLength .equal:ℝ) := by
    dsimp [Certificate.L,Certificate.boundaryLength,Certificate.d,L,frameCap] at *
    exact ⟨by linarith [hE.1],by linarith [hE.2]⟩
  have hp := Certificate.boundary_positive .equal i hx
  have hnum : 0<evaluate (E-(Certificate.L:ℝ)) E (Certificate.numerator (.negative i)) := by
    simpa [Certificate.boundary,evaluate_restrict] using hp
  have hh := polynomial_transfer (.negative i) hn hnum
  simpa only [value,add_sub_cancel] using hh

end Analytic

theorem negative_positive (i : Fin 3) {t E : ℝ} (hd : Domain t E) :
    0<negativeScalar i t E := by
  have hE := (domain_angles hd).2.1
  have hlow : max L E∈Icc E frameCap :=
    ⟨le_max_right _ _,max_le (by dsimp [L,frameCap]; norm_num) hE.2⟩
  have hconc := (negativeScalar_concave i hE).subset
    (show Icc (max L E) frameCap⊆Icc E frameCap from
      fun x hx => ⟨hlow.1.trans hx.1,hx.2⟩) (convex_Icc _ _)
  have hleft : 0<negativeScalar i (max L E) E := by
    rcases le_total E L with h|h
    · rw [max_eq_left h]
      exact Analytic.negative_low_boundary i ⟨hE.1,h⟩
    · rw [max_eq_right h]
      exact Analytic.negative_equal_boundary i ⟨h,hE.2⟩
  have hright := Analytic.negative_high_boundary i hE
  exact concave_gt_of_endpoints hconc ⟨max_le hd.1.1 hd.2.2,hd.1.2⟩ hleft hright

theorem equal_positive {t E : ℝ} (hd : Domain t E) : 0<equalScalar t E :=
  Analytic.whole_positive .equal trivial hd

theorem positive_positive (i : Fin 3) {t E : ℝ} (hd : Domain t E) :
    0<positiveScalar i t E :=
  Analytic.whole_positive (.positive i) trivial hd

theorem D_positive {t E : ℝ} (hd : Domain t E) : 0<DScalar t E :=
  Analytic.whole_positive .diagonal trivial hd

/-- The complete endpoint package consumed by the signed-variation
argument. No polynomial value or scalar positivity is supplied by the
physical caller. -/
theorem endpoints {t E : ℝ} (hd : Domain t E) :
    (∀i : Fin 3,0<negativeScalar i t E) ∧ 0<equalScalar t E ∧
      (∀i : Fin 3,0<positiveScalar i t E) ∧ 0<DScalar t E :=
  ⟨fun i => negative_positive i hd,equal_positive hd,
    fun i => positive_positive i hd,D_positive hd⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NonnegativeTotals.NegativeTD
