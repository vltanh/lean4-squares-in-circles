module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTPairedBounds

/-!
# All eight paired nonpositive-T intrinsic endpoints are positive

Uncompiled equation (34).  The three shifted negative-angle scalars
are concave at fixed E on [max(M,E),h].  The genuine C1 join of the
primary support charge is covered whether it lies before, inside or
after that interval.  The original three boundary curves then suffice.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired
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
      HasDerivAt left (w*axialD (t-E)+df t) t := by
    have hh := ((axial_derivative (t-E)).comp t ((hasDerivAt_id t).sub_const E)).const_mul w
    simpa only [left,mul_one] using hh.add (hf t ht)
  have rightD {t : ℝ} (ht : t∈Icc b frameCap) :
      HasDerivAt right (w*circleD (t-E)+df t) t := by
    have hh := ((circle_derivative (t-E)).comp t ((hasDerivAt_id t).sub_const E)).const_mul w
    simpa only [right,mul_one] using hh.add (hf t ht)
  have leftDD {t : ℝ} (ht : t∈Icc b frameCap) :
      HasDerivAt (fun t => w*axialD (t-E)+df t) (w*axialDD (t-E)+ddf t) t := by
    have hh := ((axial_second (t-E)).comp t ((hasDerivAt_id t).sub_const E)).const_mul w
    simpa only [mul_one] using hh.add (hdf t ht)
  have rightDD {t : ℝ} (ht : t∈Icc b frameCap) :
      HasDerivAt (fun t => w*circleD (t-E)+df t) (w*circleDD (t-E)+ddf t) t := by
    have hh := ((circle_second (t-E)).comp t ((hasDerivAt_id t).sub_const E)).const_mul w
    simpa only [mul_one] using hh.add (hdf t ht)
  have leftConcave {U : ℝ} (hU : U∈Icc b frameCap) (hcut : U-E≤alpha) :
      ConcaveOn ℝ (Icc b U) left := by
    apply concave_of_deriv2
      (fun t ht => leftD ⟨ht.1,ht.2.trans hU.2⟩)
      (fun t ht => leftDD ⟨ht.1,ht.2.trans hU.2⟩)
    intro t ht
    have ht' : t∈Icc b frameCap := ⟨ht.1,ht.2.trans hU.2⟩
    have ha := ABounds.axial_second_upper
      (show t-E∈Icc 0 alpha from ⟨(harg ht').1,by linarith [ht.2]⟩)
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
  by_cases hleft : frameCap≤E+alpha
  · exact TwoPositive.Split.congr_on (leftConcave ⟨hb,le_rfl⟩ (by linarith)) (by
      intro t ht
      have hh : t-E≤alpha := by linarith [ht.2]
      simp [left,charge,hh])
  by_cases hright : E+alpha≤b
  · exact TwoPositive.Split.congr_on (rightConcave ⟨le_rfl,hb⟩) (by
      intro t ht
      by_cases hh : t-E≤alpha
      · have he : t-E=alpha := by linarith [ht.1]
        simp [right,charge,hh,he,transition_value]
      · simp [right,charge,hh])
  have hjoin : E+alpha∈Icc b frameCap :=
    ⟨(lt_of_not_ge hright).le,(lt_of_not_ge hleft).le⟩
  have he : left (E+alpha)=right (E+alpha) := by
    simp only [left,right,add_sub_cancel_left,transition_value]
  have hdL := leftD hjoin
  have hdR := rightD hjoin
  simp only [add_sub_cancel_left] at hdL hdR
  rw [←transition_derivative] at hdR
  have hj := SplitConcavityTools.join hjoin
    (leftConcave hjoin (by ring_nf; exact le_rfl)) (rightConcave hjoin) he hdL hdR
  exact TwoPositive.Split.congr_on hj (by
    intro t ht
    by_cases hh : t≤E+alpha
    · have ha : t-E≤alpha := by linarith
      simp [left,charge,hh,ha]
    · have ha : ¬t-E≤alpha := by linarith
      simp [right,charge,hh,ha])

theorem negativeScalar_concave (i : Fin 3) {E : ℝ} (hE : E∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc (max M E) frameCap) (fun t => negativeScalar i t E) := by
  have hc := coefficients hE i.castSucc
  have hq := hc.1.trans_le hc.2.1
  have hl := ranges hE
  have ha {t : ℝ} (ht : t∈Icc (max M E) frameCap) : t-M∈Icc 0 frameCap :=
    ⟨by linarith [le_max_left M E,ht.1],by dsimp [M] at *; linarith [ht.2]⟩
  let f : ℝ→ℝ := fun t => base E+charge E+gain M+V R (p E i.castSucc) (q E i.castSucc) (t-M)
  let df : ℝ→ℝ := fun t => Vd R (p E i.castSucc) (q E i.castSucc) (t-M)
  let ddf : ℝ→ℝ := fun t => curvature R (p E i.castSucc) (q E i.castSucc) (-(t-M))-
    q E i.castSucc*Real.cos (t-M)
  have hf {t : ℝ} (ht : t∈Icc (max M E) frameCap) : HasDerivAt f (df t) t := by
    simpa only [f,df,mul_one] using
      ((V_hasDerivAt hc.1 hq (ha ht)).comp t ((hasDerivAt_id t).sub_const M)).const_add
        (base E+charge E+gain M)
  have hd {t : ℝ} (ht : t∈Icc (max M E) frameCap) : HasDerivAt df (ddf t) t := by
    simpa only [df,ddf,mul_one] using
      (Vd_hasDerivAt hc.1 hq (ha ht)).comp t ((hasDerivAt_id t).sub_const M)
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
  cases b
  · have hd : Certificate.Domain (.negative i) 0 x := by
      dsimp [Certificate.Domain,Certificate.origin,Certificate.length,Certificate.boundaryLength,
        Certificate.M,Certificate.h] at *
      exact ⟨by norm_num,hx⟩
    have hn : 0<evaluate 0 x (Certificate.numerator (.negative i)) := by
      simpa [Certificate.boundary,evaluate_restrict] using hp
    simpa [value,Certificate.origin,Certificate.M,M] using polynomial_transfer (.negative i) hd hn
  · have hd : Certificate.Domain (.negative i) x (M+x) := by
      dsimp [Certificate.Domain,Certificate.origin,Certificate.length,Certificate.boundaryLength,
        Certificate.M,Certificate.h,M] at *
      exact ⟨hx,⟨by linarith [hx.1],le_rfl⟩⟩
    have hn : 0<evaluate x (M+x) (Certificate.numerator (.negative i)) := by
      simpa [Certificate.boundary,evaluate_restrict,Certificate.M,M] using hp
    simpa [value,Certificate.origin,Certificate.M,M] using polynomial_transfer (.negative i) hd hn
  · have hd : Certificate.Domain (.negative i) (frameCap-M) x := by
      dsimp [Certificate.Domain,Certificate.origin,Certificate.length,Certificate.boundaryLength,
        Certificate.M,Certificate.h,M,frameCap] at *
      exact ⟨by norm_num,by simpa using hx⟩
    have hn : 0<evaluate (frameCap-M) x (Certificate.numerator (.negative i)) := by
      simpa [Certificate.boundary,evaluate_restrict,Certificate.M,Certificate.h,M,frameCap] using hp
    simpa [value,Certificate.origin,Certificate.M,M,frameCap] using polynomial_transfer (.negative i) hd hn

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
  exact concave_gt_of_endpoints (negativeScalar_concave i he)
    ⟨max_le ht.1 hE.2,ht.2⟩ hleft hright

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

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired
