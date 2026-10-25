module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Weights
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection

/-!
# Eight squares: the low negative-DE correction on both support branches

The full-circle quotient is bounded by a quadratic in `sin s` (`full_root_upper`). The residual
cubic keeps its centered quadratic reserve (`residual_cubic_positive`). Both support branches have
slope greater than `1.045` (`full_derivative_lower`, `diagonal_derivative_lower`); the crossing of
the branches is found by continuity, with the secant coefficient of the cycle kept
(`add_monotone`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowD
open Candidate Secondary PositiveAngularEnvelope

abbrev M : ℝ := 209/200
abbrev sec := NegativeELargeA.secant
abbrev diagonalGain := NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2)
abbrev diagonalFirst := NegativeESecant.gainD (GlobalGA.Secondary.diagonal-1/2)

def correction (c s : ℝ) : ℝ :=
  (sec s-1)/2+(13/12)*Real.tan s-(clippedSupport (sec s) c-clippedSupport 1 c)
def fullCorrection (c s : ℝ) : ℝ :=
  secantGain qCap c s+diagonalSupport 1 c-fullSupport 1 c

def rootPolynomial (v : ℝ) : ℝ :=
  (11/8+(11/25)*v)^2*(1+(519/500:ℝ)^2*(1-v))-qCap
def rootFirst (v : ℝ) : ℝ :=
  2*(11/25)*(11/8+(11/25)*v)*(1+(519/500:ℝ)^2*(1-v))-
    (519/500:ℝ)^2*(11/8+(11/25)*v)^2
def rootSecond (v : ℝ) : ℝ :=
  2*(11/25:ℝ)^2*(1+(519/500:ℝ)^2*(1-v))-
    4*(11/25)*(519/500:ℝ)^2*(11/8+(11/25)*v)

private theorem r74_hA (v : ℝ) : HasDerivAt (fun v : ℝ => 11/8+(11/25)*v) (11/25) v :=
  (((hasDerivAt_id' v).const_mul (11/25:ℝ)).const_add (11/8:ℝ)).congr_deriv (mul_one _)

private theorem r74_hB (v : ℝ) :
    HasDerivAt (fun v : ℝ => 1+(519/500:ℝ)^2*(1-v)) (-(519/500:ℝ)^2) v :=
  ((((hasDerivAt_id' v).const_sub 1).const_mul ((519/500:ℝ)^2)).const_add 1).congr_deriv
    (by ring)

theorem rootPolynomial_derivative (v : ℝ) : HasDerivAt rootPolynomial (rootFirst v) v := by
  have h := (((r74_hA v).fun_pow 2).fun_mul (r74_hB v)).sub_const qCap
  exact h.congr_deriv (by simp only [rootFirst]; norm_num; ring)

theorem rootFirst_derivative (v : ℝ) : HasDerivAt rootFirst (rootSecond v) v := by
  have h := (((r74_hA v).const_mul (2*(11/25:ℝ))).fun_mul (r74_hB v)).fun_sub
    (((r74_hA v).fun_pow 2).const_mul ((519/500:ℝ)^2))
  exact h.congr_deriv (by simp only [rootSecond]; norm_num; ring)

theorem rootPolynomial_positive {v : ℝ} (hv : v∈Icc 0 ((129/200:ℝ)^2)) :
    0<rootPolynomial v := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) ((129/200:ℝ)^2)) rootPolynomial := by
    apply concave_of_deriv2 (fun x _ => rootPolynomial_derivative x)
      (fun x _ => rootFirst_derivative x)
    intro x hx
    dsimp [rootSecond]
    nlinarith [hx.1]
  exact concave_gt_of_endpoints hc hv
    (by norm_num [rootPolynomial,qCap]) (by norm_num [rootPolynomial,qCap])

theorem full_root_upper {c s : ℝ} (hc : (519/500:ℝ)≤c)
    (hs : s∈Icc 0 frameCap) :
    R/Real.sqrt (gainRadicand c s)<11/8+(11/25)*Real.sin s^2 := by
  have ht := transport_trig hs
  have hy : Real.sin s∈Icc (0:ℝ) (129/200) := ⟨ht.2.2.1,by linarith [ht.2.2.2.1]⟩
  have hy2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hpoly := rootPolynomial_positive ⟨sq_nonneg _,hy2⟩
  have hc0 : 0≤c := by linarith
  have hc2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤519/500) hc 2
  have hmul := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (Real.cos s))
  have hrad : 1+(519/500:ℝ)^2*(1-Real.sin s^2)≤gainRadicand c s := by
    dsimp [gainRadicand]
    nlinarith [Real.sin_sq_add_cos_sq s]
  have hn := Real.sqrt_pos.mpr (gainRadicand_pos c s)
  have hn2 := Real.sq_sqrt (gainRadicand_pos c s).le
  have hscaled := mul_le_mul_of_nonneg_left hrad (sq_nonneg (11/8+(11/25)*Real.sin s^2))
  have hR2 := radius_sq
  have hpositive : 0<(11/8+(11/25)*Real.sin s^2)*Real.sqrt (gainRadicand c s) := by positivity
  apply (div_lt_iff₀ hn).2
  apply lt_of_pow_lt_pow_left₀ 2 hpositive.le
  rw [mul_pow,hn2,hR2]
  dsimp [rootPolynomial] at hpoly
  generalize qCap = Q at hpoly ⊢
  linarith [hscaled,hpoly]

theorem residual_cubic_positive {y : ℝ} (hy : y∈Icc (0:ℝ) (129/200)) :
    (3/2000:ℝ)<13/12-209/200-(3/8)*y+(209/200)*y^2-(11/25)*y^3 := by
  let v : ℝ := y-1/5
  have hv : v≤89/200 := by dsimp [v]; linarith [hy.2]
  have htail := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hv)
  have hid : 13/12-209/200-(3/8)*y+(209/200)*y^2-(11/25)*y^3=
      121/75000-(49/5000)*v+(781/1000)*v^2-(11/25)*v^3 := by
    dsimp [v]
    ring
  rw [hid]
  have hm := ChebyshevLeadingBounds.quadratic_min
    (a:=(121/75000:ℝ)) (b:=-(49/5000:ℝ)) (x:=v)
    (show (0:ℝ)<1463/2500 by norm_num)
  norm_num at hm
  nlinarith

theorem full_derivative_lower {c s : ℝ} (hc : (519/500:ℝ)≤c)
    (hs : s∈Icc 0 frameCap) : M<secantGainDeriv qCap c s := by
  have ht := transport_trig hs
  have hcos := NegativeESecant.cos_pos hs
  have hroot := full_root_upper hc hs
  have hmul := mul_le_mul_of_nonneg_right hroot.le ht.2.2.1
  have hpoly := residual_cubic_positive
    ⟨ht.2.2.1,by linarith [ht.2.2.2.1]⟩
  have hid : R*Real.sin s/Real.sqrt (gainRadicand c s)=
      (R/Real.sqrt (gainRadicand c s))*Real.sin s := by ring
  change M<(13/12+Real.sin s-R*Real.sin s/Real.sqrt (gainRadicand c s))/Real.cos s^2
  apply (lt_div_iff₀ (sq_pos_of_pos hcos)).2
  rw [hid]
  dsimp [M]
  nlinarith [Real.sin_sq_add_cos_sq s]

theorem diagonal_derivative_lower {s : ℝ} (hs : s∈Icc 0 frameCap) : M<diagonalFirst s := by
  have ht := transport_trig hs
  have hd := mul_le_mul_of_nonneg_right
    (show GlobalGA.Secondary.diagonal-1/2≤2/5 by linarith [diagonal_bounds.2]) ht.2.2.1
  dsimp [diagonalFirst,NegativeESecant.gainD,NegativeESecant.K,M]
  apply (lt_div_iff₀ (sq_pos_of_pos (NegativeESecant.cos_pos hs))).2
  nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s-(40/209:ℝ))]

theorem correction_diagonal {c s : ℝ} (hc : 1≤c)
    (hs : s∈Icc 0 frameCap) (hsc : sec s≤c) : correction c s=diagonalGain s := by
  rw [correction,clippedSupport,clippedSupport]
  simp only [hsc,hc,↓reduceIte]
  rw [show diagonalGain s=NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s from rfl,
    NegativeESecant.gain_secant _ hs]
  dsimp [sec,NegativeELargeA.secant,diagonalSupport,NegativeESecant.K]
  ring

theorem correction_full {c s : ℝ} (hc : 1≤c)
    (hs : s∈Icc 0 frameCap) (hcs : c≤ sec s) : correction c s=fullCorrection c s := by
  have hsupport : clippedSupport (sec s) c=fullSupport (sec s) c := by
    by_cases hsc : sec s≤c
    · have he : sec s=c := le_antisymm hsc hcs
      rw [clippedSupport,ite_eq_left hsc,full_at_diagonal he (by linarith)]
    · simp [clippedSupport,hsc]
  rw [correction,hsupport,clippedSupport,ite_eq_left hc,fullCorrection,
    secantGain_eq_secant_expression qCap c (NegativeESecant.cos_pos hs)]
  dsimp [sec,NegativeELargeA.secant,diagonalSupport,fullSupport]
  norm_num only [one_pow]
  ring

theorem fullCorrection_derivative (c : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt (fullCorrection c) (secantGainDeriv qCap c s) s :=
  ((secantGain_hasDerivAt qCap c (NegativeESecant.cos_pos hs).ne').add_const (diagonalSupport 1 c)).sub_const (fullSupport 1 c)

@[simp] theorem correction_zero (c : ℝ) : correction c 0=0 := by
  simp [correction,sec,NegativeELargeA.secant]

theorem baseline_correction (f : Family) (a z : ℝ) {s : ℝ}
    (_hs : s∈Icc 0 frameCap) :
    Explicit.baseline f a z s=Explicit.baseline f a z 0+correction (Explicit.c f (a+z)) s := by
  simp only [Explicit.baseline,correction,Explicit.secant,sec,NegativeELargeA.secant,
    Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,add_zero]
  dsimp [Explicit.K]
  ring

/-- Integration through the unique monotone secant support transition.
The derivative hypotheses are needed only on their applicable branches. -/
theorem add_monotone {c a b : ℝ} {f df : ℝ→ℝ} (hc : 1≤c)
    (ha : 0≤a) (hb : b≤frameCap)
    (hf : ∀s∈Icc a b,HasDerivAt f (df s) s)
    (hdiag : ∀s∈Icc a b,sec s≤c → 0≤diagonalFirst s+df s)
    (hfull : ∀s∈Icc a b,c≤ sec s → 0≤ secantGainDeriv qCap c s+df s) :
    MonotoneOn (fun s => correction c s+f s) (Icc a b) := by
  have hdomain {s : ℝ} (hs : s∈Icc a b) : s∈Icc 0 frameCap :=
    ⟨ha.trans hs.1,hs.2.trans hb⟩
  have hd {x y : ℝ} (hx : x∈Icc a b) (hy : y∈Icc a b) (hxy : x≤y)
      (hcy : sec y≤c) : correction c x+f x≤correction c y+f y := by
    have hmono : MonotoneOn (fun s => diagonalGain s+f s) (Icc x y) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro s hs
        have hab : s∈Icc a b := ⟨hx.1.trans hs.1,hs.2.trans hy.2⟩
        exact ((NegativeESecant.gain_hasDerivAt _ (hdomain hab)).add
          (hf s hab)).continuousAt.continuousWithinAt
      · intro s hs
        have hab : s∈Icc a b := ⟨hx.1.trans hs.1.le,hs.2.le.trans hy.2⟩
        exact (NegativeESecant.gain_hasDerivAt _ (hdomain hab)).add (hf s hab)
      · intro s hs
        have hab : s∈Icc a b := ⟨hx.1.trans hs.1.le,hs.2.le.trans hy.2⟩
        exact hdiag s hab ((NegativeELargeA.secant_monotone
          (hdomain hab) (hdomain hy) hs.2.le).trans hcy)
    rw [correction_diagonal hc (hdomain hx)
      ((NegativeELargeA.secant_monotone (hdomain hx) (hdomain hy) hxy).trans hcy),
      correction_diagonal hc (hdomain hy) hcy]
    exact hmono ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩ hxy
  have hg {x y : ℝ} (hx : x∈Icc a b) (hy : y∈Icc a b) (hxy : x≤y)
      (hcx : c≤ sec x) : correction c x+f x≤correction c y+f y := by
    have hmono : MonotoneOn (fun s => fullCorrection c s+f s) (Icc x y) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro s hs
        have hab : s∈Icc a b := ⟨hx.1.trans hs.1,hs.2.trans hy.2⟩
        exact ((fullCorrection_derivative c (hdomain hab)).add
          (hf s hab)).continuousAt.continuousWithinAt
      · intro s hs
        have hab : s∈Icc a b := ⟨hx.1.trans hs.1.le,hs.2.le.trans hy.2⟩
        exact (fullCorrection_derivative c (hdomain hab)).add (hf s hab)
      · intro s hs
        have hab : s∈Icc a b := ⟨hx.1.trans hs.1.le,hs.2.le.trans hy.2⟩
        exact hfull s hab (hcx.trans (NegativeELargeA.secant_monotone
          (hdomain hx) (hdomain hab) hs.1.le))
    rw [correction_full hc (hdomain hx) hcx,correction_full hc (hdomain hy)
      (hcx.trans (NegativeELargeA.secant_monotone (hdomain hx) (hdomain hy) hxy))]
    exact hmono ⟨le_rfl,hxy⟩ ⟨hxy,le_rfl⟩ hxy
  intro x hx y hy hxy
  by_cases hcy : sec y≤c
  · exact hd hx hy hxy hcy
  by_cases hcx : c≤ sec x
  · exact hg hx hy hxy hcx
  have hcont : ContinuousOn sec (Icc x y) := by
    intro s hs
    exact (NegativeELargeA.secant_hasDerivAt
      (hdomain ⟨hx.1.trans hs.1,hs.2.trans hy.2⟩)).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hte⟩ := intermediate_value_Icc hxy hcont
    (show c∈Icc (sec x) (sec y) from ⟨(lt_of_not_ge hcx).le,(lt_of_not_ge hcy).le⟩)
  have htab : t∈Icc a b := ⟨hx.1.trans ht.1,ht.2.trans hy.2⟩
  exact (hd hx htab ht.1 hte.le).trans (hg htab hy ht.2 hte.ge)

theorem correction_growth {c x y : ℝ} (hc : (519/500:ℝ)≤c)
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    M*(y-x)≤correction c y-correction c x := by
  have hm := add_monotone (f:=fun s => -M*s) (df:=fun _ => -M)
    (by linarith : 1≤c) le_rfl le_rfl
    (fun s _ => ((hasDerivAt_id' s).const_mul (-M)).congr_deriv (mul_one _))
    (fun s hs _ => by linarith [diagonal_derivative_lower hs])
    (fun s hs _ => by linarith [full_derivative_lower hc hs])
  have hh := hm hx hy hxy
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowD
