module

public import SquaresInCircles.Eight.TableFree.WrongSignCaptureScalars
public import SquaresInCircles.Eight.TableFree.WrongSignCaptureHull

/-!
# All admissible analytic capture weights

Uncompiled source draft.  Convexity handles the complete first constant
family from its two rational endpoint bounds.  The middle and last
families use their proved exact polynomial radical comparisons.  The
three intrinsic ranges exhaust every actual three-frame hull width.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.WrongSignCaptureWeights
open PositiveAngularEnvelope EndpointRotationPenalty WrongSignCaptureScalars

theorem convex_segment_upper {f : ℝ → ℝ} {u x : ℝ}
    (hf : ConvexOn ℝ (Icc 0 frameCap) f)
    (hu : u∈Icc 0 frameCap) (hx : x∈Icc 0 u) :
    f x≤ max (f 0) (f u) := by
  by_cases hu0 : u=0
  · have hx0 : x=0 := by linarith [hx.1,hx.2]
    simp [hu0,hx0]
  · have hup : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    let a : ℝ := (u-x)/u
    let b : ℝ := x/u
    have ha : 0≤a := div_nonneg (sub_nonneg.mpr hx.2) hu.1
    have hb : 0≤b := div_nonneg hx.1 hu.1
    have hab : a+b=1 := by dsimp [a,b]; field_simp [hu0]; ring
    have harg : a*0+b*u=x := by
      simp only [b,mul_zero,zero_add]
      exact div_mul_cancel₀ x hu0
    have hh := hf.2 (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hu ha hb hab
    simp only [smul_eq_mul,harg] at hh
    have hL := mul_le_mul_of_nonneg_left (le_max_left (f 0) (f u)) ha
    have hU := mul_le_mul_of_nonneg_left (le_max_right (f 0) (f u)) hb
    have hweight := congrArg (fun z : ℝ => z*max (f 0) (f u)) hab
    linarith

theorem convex_translate_lt {f : ℝ → ℝ} {u x c L : ℝ}
    (hf : ConvexOn ℝ (Icc 0 frameCap) f)
    (hu : u∈Icc 0 frameCap) (hx : x∈Icc 0 u)
    (hzero : f 0+c<L) (hend : f u+c<L) :
    f x+c<L := by
  have hh := convex_segment_upper hf hu hx
  rcases le_total (f 0) (f u) with h | h
  · rw [max_eq_right h] at hh
    linarith
  · rw [max_eq_left h] at hh
    linarith

theorem first_family {rho : ℝ} (hrho : rho∈Icc 0 (7/20 : ℝ)) :
    Admissible (4/5) (13/20) ∧
      U_T rho (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G rho (4/5) (13/20)<(WrongSignWeightPolynomial.limit:ℝ) := by
  let cT : ℝ := R*pairNorm 1 (13/20) 0-2*(4/5)/5-8/5-2*(13/20)
  let cG : ℝ := R*pairNorm (4/5) (13/20) 0-7*(4/5)/5-3/5-2*(13/20)
  have heT (t : ℝ) : U_T t (4/5) (13/20)=WrongSignCaptureHull.F (4/5) (13/20) t+cT := by
    dsimp [U_T,WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p,cT]
    ring
  have heG (t : ℝ) : U_G t (4/5) (13/20)=WrongSignCaptureHull.F 1 (13/20) t+cG := by
    dsimp [U_G,WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p,cG]
    ring
  have hu : (7/20 : ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hT := convex_translate_lt
    (WrongSignCaptureHull.F_convex (show (0:ℝ)<13/20 by norm_num)
      (show (13/20 : ℝ)≤4/5 by norm_num)) hu hrho
    (show WrongSignCaptureHull.F (4/5) (13/20) 0+cT<(WrongSignWeightPolynomial.limit:ℝ) by
      rw [← heT]; exact first_at_zero.1)
    (show WrongSignCaptureHull.F (4/5) (13/20) (7/20)+cT<(WrongSignWeightPolynomial.limit:ℝ) by
      rw [← heT]; exact first_at_cap.1)
  have hG := convex_translate_lt
    (WrongSignCaptureHull.F_convex (show (0:ℝ)<13/20 by norm_num)
      (show (13/20 : ℝ)≤1 by norm_num)) hu hrho
    (show WrongSignCaptureHull.F 1 (13/20) 0+cG<(WrongSignWeightPolynomial.limit:ℝ) by
      rw [← heG]; exact first_at_zero.2)
    (show WrongSignCaptureHull.F 1 (13/20) (7/20)+cG<(WrongSignWeightPolynomial.limit:ℝ) by
      rw [← heG]; exact first_at_cap.2)
  rw [← heT] at hT
  rw [← heG] at hG
  exact ⟨by norm_num [Admissible],hT,hG⟩

/-- One proved admissible pair is chosen at the actual hull width.  No
weight is varied during the subsequent convexity comparisons. -/
theorem weights {rho : ℝ} (hrho : rho∈Icc 0 frameCap) :
    ∃ a b,Admissible a b ∧ U_T rho a b<(WrongSignWeightPolynomial.limit:ℝ) ∧
      U_G rho a b<(WrongSignWeightPolynomial.limit:ℝ) := by
  by_cases hfirst : rho≤7/20
  · have hh := first_family (show rho∈Icc 0 (7/20 : ℝ) from ⟨hrho.1,hfirst⟩)
    exact ⟨4/5,13/20,hh⟩
  · by_cases hmiddle : rho≤47/100
    · exact middle_family ⟨by linarith,hmiddle⟩
    · exact last_family ⟨by linarith,hrho.2⟩

end SquaresInCircles.Eight.TableFree.WrongSignCaptureWeights
