module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowSame
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowSeparatedPolynomial

/-!
# Eight squares: the actual interior-D slope comparison

The stricter coefficient rectangle is
used only after c <= sec s has been obtained at the original E angle.
The quartic gives the quadratic D-slope reserve, and the final cubic is
bounded by the displayed completed square on the whole interval.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryCurvatureBounds OrdinaryNegativeSlope

def smallRoot (q : ℝ) : ℝ := Real.sqrt ((17/25:ℝ)^2+q^2)
def smallCurvature (q : ℝ) : ℝ := R*(17/25:ℝ)^2*q^2/(smallRoot q)^3

theorem smallRoot_pos (q : ℝ) : 0<smallRoot q := Real.sqrt_pos.mpr (by positivity)
theorem smallRoot_sq (q : ℝ) : (smallRoot q)^2=(17/25:ℝ)^2+q^2 := Real.sq_sqrt (by positivity)
theorem smallRoot_derivative (q : ℝ) : HasDerivAt smallRoot (q/smallRoot q) q := by
  convert (((hasDerivAt_id q).pow 2).const_add ((17/25:ℝ)^2)).sqrt
    (by positivity : (17/25:ℝ)^2+q^2≠0) using 1
  · rfl
  · dsimp [smallRoot]
    ring

theorem smallCurvature_derivative (q : ℝ) :
    HasDerivAt smallCurvature
      (R*(17/25:ℝ)^2*q*(2*(17/25:ℝ)^2-q^2)/(smallRoot q)^5) q := by
  have hr := smallRoot_pos q
  have hs := smallRoot_sq q
  have hh := (((hasDerivAt_id q).pow 2).const_mul (R*(17/25:ℝ)^2)).div
    ((smallRoot_derivative q).pow 3) (pow_ne_zero 3 hr.ne')
  convert hh using 1
  · rfl
  · simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,
      show (3:ℕ)-1=2 from rfl,pow_one]
    field_simp
    linear_combination (-1250*q)*hs

theorem smallCurvature_antitone : AntitoneOn smallCurvature (Icc (1:ℝ) (283/250)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun q _ => (smallCurvature_derivative q).continuousAt.continuousWithinAt)
    (fun q _ => smallCurvature_derivative q)
  intro q hq
  have hsign : 2*(17/25:ℝ)^2-q^2≤0 := by nlinarith [hq.1]
  have hfactor : 0≤R*(17/25:ℝ)^2*q :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by norm_num)) (by linarith [hq.1])
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hfactor hsign)
    (pow_nonneg (smallRoot_pos q).le 5)

theorem curvature_smaller_monotone {p P q : ℝ}
    (hp : 0<p) (hpP : p≤P) (hPq : P≤q) (hq : 0<q) :
    curvatureZero R p q≤curvatureZero R P q := by
  have hP := hp.trans_le hpP
  obtain ⟨_,_,hC,_⟩ := curvature_constants_normalize (R:=R) hp hq
  obtain ⟨_,_,hC',_⟩ := curvature_constants_normalize (R:=R) hP hq
  rw [hC,hC']
  apply mul_le_mul_of_nonneg_left _ hq.le
  exact NegativeAPositiveTD.Curvature.shapeC0q_monotone
    ⟨div_nonneg hp.le hq.le,(div_le_one hq).2 (hpP.trans hPq)⟩
    ⟨div_nonneg hP.le hq.le,(div_le_one hq).2 hPq⟩
    ((div_le_div_iff_of_pos_right hq).2 hpP)

theorem interior_constants {p q : ℝ} (hp : 0<p) (hpU : p≤17/25)
    (hq : q∈Icc (1:ℝ) (283/250)) :
    NegativeAPositiveTD.Curvature.slopeZero p q<577/500 ∧ curvatureZero R p q<259/500 := by
  have hq0 : 0<q := by linarith [hq.1]
  have hR2 : R^2=qCap := Real.sq_sqrt (by norm_num [qCap])
  have ht : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hD := LowG.zero_slope_rectangle hp hq0 hpU hq.2
  have hDend : NegativeAPositiveTD.Curvature.slopeZero (17/25) (283/250)<577/500 := by
    have hn := pairNorm_pos (p:=(17/25:ℝ)) (q:=(283/250:ℝ)) (by norm_num) (by norm_num) ht
    have hn2 : (pairNorm (17/25:ℝ) (283/250) 0)^2=(17/25:ℝ)^2+(283/250)^2 := by
      rw [pairNorm,Real.sin_zero,mul_zero,add_zero,Real.sq_sqrt (by positivity)]
    unfold NegativeAPositiveTD.Curvature.slopeZero
    apply quotient_lt_of_square hn (by norm_num)
    rw [hn2,mul_pow,hR2,pairProduct]
    norm_num [qCap]
  have hC := curvature_smaller_monotone hp hpU (by linarith [hq.1] : (17/25:ℝ)≤q) hq0
  have hCeq (q : ℝ) : curvatureZero R (17/25) q=smallCurvature q := by
    simp only [curvatureZero,pairProduct,pairNorm,smallCurvature,smallRoot,Real.sin_zero,
      mul_zero,add_zero,mul_pow]
    ring
  rw [hCeq] at hC
  have hCm := smallCurvature_antitone (by norm_num : (1:ℝ)∈Icc 1 (283/250)) hq hq.1
  have hCend : smallCurvature 1<259/500 := by
    unfold smallCurvature
    apply quotient_lt_of_square (pow_pos (smallRoot_pos _) 3) (by norm_num)
    rw [show ((smallRoot 1)^3)^2=((smallRoot 1)^2)^3 by ring,smallRoot_sq,mul_pow,mul_pow,hR2]
    norm_num [qCap]
  exact ⟨hD.trans_lt hDend,(hC.trans hCm).trans_lt hCend⟩

theorem interior_negative_slope {p q d : ℝ} (hp : 0<p) (hpU : p≤17/25)
    (hq : q∈Icc (1:ℝ) (283/250)) (hd : d∈Icc 0 frameCap) :
    Vd R p q d<577/500-(241/500)*d+(189/1000)*d^3 := by
  have hq0 : 0<q := by linarith [hq.1]
  have hn := negative_slope_linear_model hp hq0 hd
  obtain ⟨hD,hC⟩ := interior_constants hp hpU hq
  have hCd := mul_le_mul_of_nonneg_right hC.le hd.1
  have hqd := mul_le_mul_of_nonneg_right hq.1 hd.1
  have hqcube := mul_le_mul_of_nonneg_right hq.2 (pow_nonneg hd.1 3)
  nlinarith [pow_nonneg hd.1 3]

theorem interior_D_quadratic {c s : ℝ} (hc : (519/500:ℝ)≤c)
    (hs : s∈Icc 0 frameCap) (hy : (27/100:ℝ)≤Real.sin s) :
    209/200+(3/5)*(s-1/4)^2<secantGainDeriv qCap c s := by
  have ht := transport_trig hs
  have hcos := NegativeESecant.cos_pos hs
  have hroot := LowD.full_root_upper hc hs
  have hmul := mul_le_mul_of_nonneg_right hroot.le ht.2.2.1
  have hslope := LowSame.sine_linear hs
  have hsinle := Real.sin_le hs.1
  have hsq : (s-1/4)^2≤((25/23)*Real.sin s-1/4)^2 := by
    have hleft : 0≤ s-1/4 := by linarith
    have hright : s-1/4≤(25/23)*Real.sin s-1/4 := by linarith
    exact pow_le_pow_left₀ hleft hright 2
  have hscaled := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.cos s))
  have hpoly := Certificate.interior_positive
    (show Real.sin s∈Icc (27/100:ℝ) (129/200) from ⟨hy,by linarith [ht.2.2.2.1]⟩)
  have hid : aeval (Real.sin s) Certificate.interiorPolynomial=
      13/12-(3/8)*Real.sin s-(11/25)*(Real.sin s)^3-
        (1-(Real.sin s)^2)*(209/200+(3/5)*((25/23)*Real.sin s-1/4)^2) := by
    simp [Certificate.interiorPolynomial]
    ring
  rw [hid] at hpoly
  have htrig : 1-(Real.sin s)^2=(Real.cos s)^2 := by nlinarith [Real.sin_sq_add_cos_sq s]
  rw [htrig] at hpoly
  change 209/200+(3/5)*(s-1/4)^2<
    (13/12+Real.sin s-R*Real.sin s/Real.sqrt (gainRadicand c s))/Real.cos s^2
  apply (lt_div_iff₀ (sq_pos_of_pos hcos)).2
  have he : R*Real.sin s/Real.sqrt (gainRadicand c s)=
      (R/Real.sqrt (gainRadicand c s))*Real.sin s := by ring
  rw [he]
  nlinarith only [hpoly,hmul,hscaled]

theorem interior_slope_comparison {p q c s : ℝ}
    (hp : 0<p) (hpU : p≤17/25) (hq : q∈Icc (1:ℝ) (283/250))
    (hc : (519/500:ℝ)≤c) (hs : s∈Icc 0 frameCap)
    (hy : (27/100:ℝ)≤Real.sin s) :
    Vd R p q (frameCap-s)<secantGainDeriv qCap c s := by
  have hn : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hV := interior_negative_slope hp hpU hq hn
  have hD := interior_D_quadratic hc hs hy
  have hcube := mul_nonneg (sq_nonneg (frameCap-s)) (sub_nonneg.mpr hn.2)
  have hreserve : (1/100:ℝ)<1/80-(29/500)*(frameCap-s)+
      (3/5)*(frameCap-s)^2-(189/1000)*(frameCap-s)^3 := by
    norm_num [frameCap] at hcube
    nlinarith [sq_nonneg ((frameCap-s)-290/4677)]
  dsimp [frameCap] at hV hD hreserve
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowSeparated
