module

public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsNegativeTDScalarCurvature
public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TPairedBounds

/-!
# Eight squares: all eight paired nonpositive-T intrinsic endpoints are positive

The three shifted negative-angle scalars are concave at fixed `E` on `[max M E, h]`
(`negativeScalar_concave`). The C¹ join of the primary support charge is covered whether it lies
before, inside or after that interval (`shifted_charge_concave_on`). The three boundary curves then
suffice (`negative_boundary`).
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryNegativeSlope TwoPositive.ASupport TensorWholeIntervalPolynomial TwoVariablePolynomial

theorem shifted_charge_concave_on {b E w : ℝ} {f df ddf : ℝ→ℝ}
    (hw : 0≤w) (hE : 0≤E) (hEb : E≤b) (hb : b≤frameCap)
    (hf : ∀t∈Icc b frameCap,HasDerivAt f (df t) t)
    (hdf : ∀t∈Icc b frameCap,HasDerivAt df (ddf t) t)
    (hcurv : ∀t∈Icc b frameCap,ddf t≤-w/50) :
    ConcaveOn ℝ (Icc b frameCap) (fun t => w*charge (t-E)+f t) := by
  let left : ℝ→ℝ := fun t => w*axialCharge (t-E)+f t
  let right : ℝ→ℝ := fun t => w*circleCharge (t-E)+f t
  have harg {t : ℝ} (ht : t∈Icc b frameCap) : t-E∈Icc 0 frameCap :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have leftD {t : ℝ} (ht : t∈Icc b frameCap) :
      HasDerivAt left (w*axialD (t-E)+df t) t :=
    (((axial_derivative (t-E)).comp_sub_const t E).const_mul w).fun_add (hf t ht)
  have rightD {t : ℝ} (ht : t∈Icc b frameCap) :
      HasDerivAt right (w*circleD (t-E)+df t) t :=
    (((circle_derivative (t-E)).comp_sub_const t E).const_mul w).fun_add (hf t ht)
  have leftDD {t : ℝ} (ht : t∈Icc b frameCap) :
      HasDerivAt (fun t => w*axialD (t-E)+df t) (w*axialDD (t-E)+ddf t) t :=
    (((axial_second (t-E)).comp_sub_const t E).const_mul w).fun_add (hdf t ht)
  have rightDD {t : ℝ} (ht : t∈Icc b frameCap) :
      HasDerivAt (fun t => w*circleD (t-E)+df t) (w*circleDD (t-E)+ddf t) t :=
    (((circle_second (t-E)).comp_sub_const t E).const_mul w).fun_add (hdf t ht)
  have leftConcave {U : ℝ} (hU : U∈Icc b frameCap) (hcut : U-E≤TwoPositive.ASupport.alpha) :
      ConcaveOn ℝ (Icc b U) left := by
    apply concave_of_deriv2
      (fun t ht => leftD ⟨ht.1,ht.2.trans hU.2⟩)
      (fun t ht => leftDD ⟨ht.1,ht.2.trans hU.2⟩)
    intro t ht
    have ht' : t∈Icc b frameCap := ⟨ht.1,ht.2.trans hU.2⟩
    have ha := PositiveANegativeTD.ABounds.axial_second_upper
      (show t-E∈Icc 0 TwoPositive.ASupport.alpha from ⟨(harg ht').1,by linarith [ht.2]⟩)
    have hp := mul_le_mul_of_nonneg_left ha.le hw
    linarith [hcurv t ht']
  have rightConcave {U : ℝ} (hU : U∈Icc b frameCap) :
      ConcaveOn ℝ (Icc U frameCap) right := by
    apply concave_of_deriv2
      (fun t ht => rightD ⟨hU.1.trans ht.1,ht.2⟩)
      (fun t ht => rightDD ⟨hU.1.trans ht.1,ht.2⟩)
    intro t ht
    have ht' : t∈Icc b frameCap := ⟨hU.1.trans ht.1,ht.2⟩
    have hc := mul_nonpos_of_nonneg_of_nonpos hw (circle_curvature (harg ht'))
    linarith [hcurv t ht']
  by_cases hleft : frameCap≤E+TwoPositive.ASupport.alpha
  · refine (leftConcave ⟨hb,le_rfl⟩ (by linarith)).congr fun t ht => ?_
    have hh : t-E≤TwoPositive.ASupport.alpha := by linarith [ht.2]
    simp only [left,TwoPositive.ASupport.charge,hh,↓reduceIte]
  by_cases hright : E+TwoPositive.ASupport.alpha≤b
  · refine (rightConcave ⟨le_rfl,hb⟩).congr fun t ht => ?_
    by_cases hh : t-E≤TwoPositive.ASupport.alpha
    · have he : t-E=TwoPositive.ASupport.alpha := by linarith [ht.1]
      simp only [right,TwoPositive.ASupport.charge,he,le_refl,↓reduceIte,transition_value]
    · simp only [right,TwoPositive.ASupport.charge,hh,↓reduceIte]
  have hjoin : E+TwoPositive.ASupport.alpha∈Icc b frameCap :=
    ⟨(lt_of_not_ge hright).le,(lt_of_not_ge hleft).le⟩
  have he : left (E+TwoPositive.ASupport.alpha)=right (E+TwoPositive.ASupport.alpha) := by
    simp only [left,right,add_sub_cancel_left,transition_value]
  have hdL := leftD hjoin
  have hdR := rightD hjoin
  simp only [add_sub_cancel_left] at hdL hdR
  rw [←transition_derivative] at hdR
  have hj := SplitConcavityTools.join hjoin
    (leftConcave hjoin (by rw [add_sub_cancel_left])) (rightConcave hjoin) he hdL hdR
  refine hj.congr fun t ht => ?_
  by_cases hh : t≤E+TwoPositive.ASupport.alpha
  · have ha : t-E≤TwoPositive.ASupport.alpha := by linarith
    simp only [left,TwoPositive.ASupport.charge,hh,ha,↓reduceIte]
  · have ha : ¬t-E≤TwoPositive.ASupport.alpha := by intro h; exact hh (by linarith)
    simp only [right,TwoPositive.ASupport.charge,hh,ha,↓reduceIte]

theorem negativeScalar_concave (i : Fin 3) {E : ℝ} (hE : E∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc (max M E) frameCap) (fun t => negativeScalar i t E) := by
  have hc := coefficients hE i.castSucc
  have hq := hc.1.trans_le hc.2.1
  have hl := ranges hE
  have ha {t : ℝ} (ht : t∈Icc (max M E) frameCap) : t-M∈Icc 0 frameCap :=
    ⟨by linarith [le_max_left M E,ht.1],by linarith [ht.2,show (0:ℝ)≤M by norm_num [M]]⟩
  let f : ℝ→ℝ := fun t => base E+charge E+gain M+V R (p E i.castSucc) (q E i.castSucc) (t-M)
  let df : ℝ→ℝ := fun t => Vd R (p E i.castSucc) (q E i.castSucc) (t-M)
  let ddf : ℝ→ℝ := fun t => curvature R (p E i.castSucc) (q E i.castSucc) (-(t-M))-
    q E i.castSucc*Real.cos (t-M)
  have hf {t : ℝ} (ht : t∈Icc (max M E) frameCap) : HasDerivAt f (df t) t :=
    ((V_hasDerivAt (R:=R) hc.1 hq (ha ht)).comp_sub_const t M).const_add
      (base E+TwoPositive.ASupport.charge E+gain M)
  have hd {t : ℝ} (ht : t∈Icc (max M E) frameCap) : HasDerivAt df (ddf t) t :=
    (Vd_hasDerivAt (R:=R) hc.1 hq (ha ht)).comp_sub_const t M
  have hcurv {t : ℝ} (ht : t∈Icc (max M E) frameCap) : ddf t≤-l E/50 := by
    have hn := NonnegativeTotals.NegativeTD.negative_curvature hc.1 hc.2.1
      (by linarith [hc.2.2.1]) (ha ht)
    dsimp [ddf]
    linarith [hl.2.2.2.1,hc.2.2.2.1]
  have hh := shifted_charge_concave_on (w:=l E) (by linarith [hl.2.2.1]) hE.1
    (le_max_right M E) (max_le (by norm_num [M,frameCap]) hE.2)
    (fun t ht => hf ht) (fun t ht => hd ht) (fun t ht => hcurv ht)
  convert hh using 1
  funext t
  dsimp [negativeScalar,primaryCost,NonnegativeTotals.NegativeTD.primaryCost,f]
  ring

namespace Analytic

theorem whole_positive (f : Certificate.Kind) (hf : Certificate.Whole f)
    {t E : ℝ} (hd : Domain f t E) : 0<value f t E := by
  have hn := native_of_domain hd
  have hh := polynomial_transfer f hn (Certificate.whole_positive f hf hn)
  have he : (Certificate.origin f:ℝ)+(t-(Certificate.origin f:ℝ))=t := by ring
  simpa only [he] using hh

theorem negative_boundary (b : Certificate.Boundary) (i : Fin 3)
    {x : ℝ} (hx : x∈Icc 0 (Certificate.boundaryLength b:ℝ)) :
    0<negativeScalar i
      (match b with | .low => M | .equal => M+x | .high => frameCap)
      (match b with | .low => x | .equal => M+x | .high => x) := by
  have hp := Certificate.boundary_positive b i hx
  have hM : ((Certificate.M:ℚ):ℝ)=M := by norm_num [Certificate.M,M]
  have hL : ((Certificate.length (.negative i):ℚ):ℝ)=frameCap-M := by
    norm_num [Certificate.length,Certificate.h,Certificate.M,M,frameCap]
  have hO : ((Certificate.origin (.negative i):ℚ):ℝ)=M := by
    norm_num [Certificate.origin,Certificate.M,M]
  cases b
  · have hx' : x∈Icc 0 M := by
      simpa [Certificate.boundaryLength,Certificate.M,M] using hx
    have hd : Certificate.Domain (.negative i) 0 x := by
      refine ⟨⟨le_rfl,?_⟩,?_⟩
      · rw [hL]; norm_num [M,frameCap]
      · rw [hO,add_zero]; exact hx'
    have hn : 0<evaluate 0 x (Certificate.numerator (.negative i)) := by
      simpa [Certificate.boundary,evaluate_restrict] using hp
    have hh := polynomial_transfer (.negative i) hd hn
    rw [hO,add_zero] at hh
    exact hh
  · have hx' : x∈Icc 0 (frameCap-M) := by
      simpa [Certificate.boundaryLength,Certificate.h,Certificate.M,M,frameCap] using hx
    have hd : Certificate.Domain (.negative i) x (M+x) := by
      refine ⟨by rw [hL]; exact hx',?_⟩
      rw [hO]
      exact ⟨by linarith [hx'.1,show (0:ℝ)≤M by norm_num [M]],le_rfl⟩
    have hn : 0<evaluate x (M+x) (Certificate.numerator (.negative i)) := by
      have hh : 0<evaluate x ((Certificate.M:ℚ)+x) (Certificate.numerator (.negative i)) := by
        simpa [Certificate.boundary,evaluate_restrict] using hp
      rwa [hM] at hh
    have hh := polynomial_transfer (.negative i) hd hn
    rw [hO] at hh
    exact hh
  · have hx' : x∈Icc 0 frameCap := by
      simpa [Certificate.boundaryLength,Certificate.h,frameCap] using hx
    have hd : Certificate.Domain (.negative i) (frameCap-M) x := by
      refine ⟨⟨by norm_num [M,frameCap],by rw [hL]⟩,?_⟩
      rw [hO,add_sub_cancel]
      exact hx'
    have hn : 0<evaluate (frameCap-M) x (Certificate.numerator (.negative i)) := by
      have hh : 0<evaluate ((Certificate.h:ℚ)-(Certificate.M:ℚ):ℝ) x
          (Certificate.numerator (.negative i)) := by
        simpa [Certificate.boundary,evaluate_restrict] using hp
      have he : ((Certificate.h:ℚ):ℝ)-((Certificate.M:ℚ):ℝ)=frameCap-M := by
        norm_num [Certificate.h,Certificate.M,M,frameCap]
      rwa [he] at hh
    have hh := polynomial_transfer (.negative i) hd hn
    rw [hO,add_sub_cancel] at hh
    exact hh

end Analytic

theorem negative_positive (i : Fin 3) {t E : ℝ}
    (ht : t∈Icc M frameCap) (hE : E∈Icc 0 t) : 0<negativeScalar i t E := by
  have he : E∈Icc 0 frameCap := ⟨hE.1,hE.2.trans ht.2⟩
  have hleft : 0<negativeScalar i (max M E) E := by
    rcases le_total E M with hh|hh
    · rw [max_eq_left hh]
      exact Analytic.negative_boundary .low i
        (by simpa [Certificate.boundaryLength,Certificate.M,M] using (show E∈Icc 0 M from ⟨he.1,hh⟩))
    · rw [max_eq_right hh]
      have hx : E-M∈Icc 0 (Certificate.boundaryLength .equal:ℝ) := by
        dsimp [Certificate.boundaryLength,Certificate.h,Certificate.M,M,frameCap] at *
        exact ⟨by linarith,by linarith [he.2]⟩
      have hp := Analytic.negative_boundary .equal i hx
      have hid : M+(E-M)=E := by ring
      simpa only [hid] using hp
  have hright := Analytic.negative_boundary .high i
    (by simpa [Certificate.boundaryLength,Certificate.h,frameCap] using he)
  have hh := concave_gt_of_endpoints (negativeScalar_concave i he)
    ⟨max_le ht.1 hE.2,ht.2⟩ hleft hright
  exact hh

theorem equal_positive {t E : ℝ} (ht : t∈Icc L M) (hE : E∈Icc 0 t) :
    0<equalScalar t E :=
  Analytic.whole_positive .equal trivial
    ⟨by simpa [Certificate.origin,Certificate.length,Certificate.L,Certificate.M,L,M] using ht,hE⟩
theorem positive_positive (i : Fin 3) {t E : ℝ} (ht : t∈Icc L M) (hE : E∈Icc 0 t) :
    0<positiveScalar i t E :=
  Analytic.whole_positive (.positive i) trivial
    ⟨by simpa [Certificate.origin,Certificate.length,Certificate.L,Certificate.M,L,M] using ht,hE⟩
theorem D_positive {t E : ℝ} (ht : t∈Icc L M) (hE : E∈Icc 0 t) : 0<DScalar t E :=
  Analytic.whole_positive .diagonal trivial
    ⟨by simpa [Certificate.origin,Certificate.length,Certificate.L,Certificate.M,L,M] using ht,hE⟩

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired
