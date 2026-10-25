module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Ranges
public import SquaresInCircles.Eight.Owners.GA.Negative.DEHighOrdinaryShape

/-!
# Eight squares: the high-total D cost is paid at every remaining negative angle

The negative curvature bound is integrated backwards from the original
cap. The resulting slope depends on the actual removed DE magnitude.
The secant and tilted alternatives in gamma are both bounded before the
maximum is taken. The support tie and both zero-angle endpoints remain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighSlopes
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope

lemma negative_derivative {p q s w : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : (2/3)*q≤p)
    (hs : s∈Icc 0 frameCap) (hw : w∈Icc 0 (frameCap-s)) :
    (2/3+(36/125)*s)*q<Vd R p q w := by
  have hq := hp.trans_le hpq
  have hratio : q≤2*p := by linarith
  have hwf : w∈Icc 0 frameCap := ⟨hw.1,by linarith [hw.2,hs.1]⟩
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) :
      HasDerivAt (fun t => -Vd R p q t) (-NegativeDEHighShape.Vdd p q t) t :=
    (Vd_hasDerivAt (R:=R) hp hq ht).fun_neg
  have hg := derivative_reserve
    (f:=fun t => -Vd R p q t) (df:=fun t => -NegativeDEHighShape.Vdd p q t)
    (k:=(36/125)*q)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => by
      have hh := NegativeDEHighShape.second_whole hp hpq hratio (Ioo_subset_Icc_self ht)
      linarith)
    hwf (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hwf.2
  have he := Vd_lower hp hpq hqp
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hremaining := mul_le_mul_of_nonneg_left
    (show s≤frameCap-w by linarith [hw.2]) (show 0≤(36/125)*q by positivity)
  have he' : (2/3)*q<Vd R p q frameCap := he
  linarith

def secantFirst (s : ℝ) : ℝ := Real.sin s/Real.cos s^2
def secantSecond (s : ℝ) : ℝ := (1+Real.sin s^2)/Real.cos s^3

theorem secantFirst_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt secantFirst (secantSecond s) s := by
  have hc := NegativeESecant.cos_pos hs
  have hd := (Real.hasDerivAt_sin s).div ((Real.hasDerivAt_cos s).pow 2)
    (pow_ne_zero 2 hc.ne')
  convert hd using 1
  · rfl
  · dsimp [secantSecond]
    field_simp [hc.ne']
    nlinarith [Real.sin_sq_add_cos_sq s]

def secantReserve (s : ℝ) : ℝ :=
  (431/500)*(2/3+(36/125)*s)-SecantD.slope*Explicit.sec s

theorem secantReserve_concave : ConcaveOn ℝ (Icc 0 frameCap) secantReserve := by
  have hd (s : ℝ) (hs : s∈Icc 0 frameCap) :
      HasDerivAt secantReserve
        ((431/500)*(36/125)-SecantD.slope*secantFirst s) s := by
    have h1 : HasDerivAt (fun s : ℝ => (431/500)*(2/3+(36/125)*s)) ((431/500)*((36/125)*1)) s :=
      (((hasDerivAt_id' s).const_mul (36/125)).const_add (2/3)).const_mul (431/500)
    have h2 : HasDerivAt (fun s => SecantD.slope*NegativeELargeA.secant s)
        (SecantD.slope*(Real.sin s/Real.cos s^2)) s :=
      (NegativeELargeA.secant_hasDerivAt hs).const_mul SecantD.slope
    have he : secantReserve=fun s =>
        (431/500)*(2/3+(36/125)*s)-SecantD.slope*NegativeELargeA.secant s := rfl
    rw [he]
    convert h1.fun_sub h2 using 1
    simp only [secantFirst]
    ring
  have hdd (s : ℝ) (hs : s∈Icc 0 frameCap) :
      HasDerivAt (fun s => (431/500)*(36/125)-SecantD.slope*secantFirst s)
        (-SecantD.slope*secantSecond s) s :=
    (((secantFirst_hasDerivAt hs).const_mul SecantD.slope).const_sub
      ((431/500)*(36/125))).congr_deriv (by ring)
  apply concave_of_deriv2 (fun s hs => hd s hs) (fun s hs => hdd s hs)
  intro s hs
  have hc := NegativeESecant.cos_pos hs
  have hpos : 0<secantSecond s := by
    unfold secantSecond
    positivity
  simp only [SecantD.slope]
  linarith

theorem secantReserve_positive {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<secantReserve s := by
  have h0 : 0<secantReserve 0 := by
    norm_num [secantReserve,SecantD.slope,Explicit.sec,NegativeELargeA.secant]
  have h1 : 0<secantReserve frameCap := by
    have hh := (NegativeELargeA.secant_range
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).2
    dsimp [secantReserve,SecantD.slope,frameCap,SecantD.qUpper] at *
    linarith
  exact concave_gt_of_endpoints secantReserve_concave hs h0 h1

lemma gamma_below_slope {θ z s : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (j : Fin 3) :
    Explicit.gamma .high θ z s<(2/3+(36/125)*s)*Explicit.q .high θ j := by
  have hq := (Explicit.high_q_bounds hθ j).1
  have hfactor : 0<2/3+(36/125)*s := by linarith [hs.1]
  have hqmul := mul_lt_mul_of_pos_left hq hfactor
  have hsec := secantReserve_positive hs
  have hc := Explicit.high_c_ratio hθ hz j
  have hcmul := mul_lt_mul_of_pos_left hc (by norm_num [SecantD.slope] : 0<SecantD.slope)
  have hsq := mul_nonneg hs.1 (show 0≤Explicit.q .high θ j by linarith)
  have hleft : SecantD.slope*Explicit.sec s<
      (2/3+(36/125)*s)*Explicit.q .high θ j := by
    dsimp [secantReserve] at hsec
    nlinarith only [hqmul,hsec]
  have hright : SecantD.slope*Explicit.c .high θ z<
      (2/3+(36/125)*s)*Explicit.q .high θ j := by
    dsimp [SecantD.slope] at hcmul
    nlinarith only [hcmul,hsq,hq]
  rw [Explicit.gamma,mul_max_of_nonneg _ _ (by norm_num [SecantD.slope])]
  exact max_lt hleft hright

/-- The derivative bound retains the actual original DE magnitude s. -/
theorem gamma_derivative {θ z s w : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap)
    (hw : w∈Icc 0 (frameCap-s)) (j : Fin 3) :
    Explicit.gamma .high θ z s<Vd R (Explicit.p .high θ j) (Explicit.q .high θ j) w := by
  have hp := Explicit.high_pairs hθ j
  exact (gamma_below_slope hθ hz hs j).trans
    (negative_derivative hp.1 hp.2.1 hp.2.2.le hs hw)

theorem gamma_growth {θ z s x y : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap)
    (hx : x∈Icc 0 (frameCap-s)) (hy : y∈Icc 0 (frameCap-s))
    (hxy : x≤y) (j : Fin 3) :
    Explicit.gamma .high θ z s*(y-x)≤Explicit.V .high θ j y-Explicit.V .high θ j x := by
  have hp := Explicit.high_pairs hθ j
  have hd (w : ℝ) (hw : w∈Icc 0 (frameCap-s)) :
      HasDerivAt (Explicit.V .high θ j)
        (Vd R (Explicit.p .high θ j) (Explicit.q .high θ j) w) w :=
    V_hasDerivAt (R:=R) hp.1 (hp.1.trans_le hp.2.1)
      (show w∈Icc 0 frameCap from ⟨hw.1,by linarith [hw.2,hs.1]⟩)
  exact derivative_reserve
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w (Ioo_subset_Icc_self hw))
    (fun w hw => (gamma_derivative hθ hz hs (Ioo_subset_Icc_self hw) j).le)
    hx hy hxy

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.HighSlopes
