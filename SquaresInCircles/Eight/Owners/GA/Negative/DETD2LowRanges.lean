module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2Weights
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection

/-!
# Eight squares: the low coefficient domain before any E-angle concentration

The upper
bound on the tilted B coefficient is obtained from its actual increasing
split factor and its decreasing total-angle envelope. The tighter
coefficient bounds apply only after the original D support is interior.
-/

section
/-!
## The low negative-DE correction on both support branches

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowRanges
open Candidate Secondary PositiveAngularEnvelope

abbrev factor (z : ℝ) : ℝ := Real.cos z+Explicit.eta*Real.sin z
abbrev factorFirst (z : ℝ) : ℝ := -Real.sin z+Explicit.eta*Real.cos z

theorem factor_derivative (z : ℝ) : HasDerivAt factor (factorFirst z) z := by
  exact (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul Explicit.eta)

theorem factor_monotone : MonotoneOn factor (Icc (0:ℝ) (1/6)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun z _ => (factor_derivative z).continuousAt.continuousWithinAt)
    (fun z _ => factor_derivative z)
  intro z hz
  have hz' := Ioo_subset_Icc_self hz
  have hc := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hs := Real.sin_le hz'.1
  have hz2 := pow_le_pow_left₀ hz'.1 hz'.2 2
  dsimp [factorFirst,Explicit.eta]
  linarith [hz'.2]

theorem factor_lower {z : ℝ} (hz : z∈Icc (0:ℝ) (1/6)) : 1≤factor z := by
  have hh := factor_monotone (by norm_num) hz hz.1
  have h0 : factor 0=1 := by simp [factor]
  linarith

theorem factorFirst_upper {z : ℝ} (hz : z∈Icc (0:ℝ) (1/6)) : factorFirst z≤Explicit.eta := by
  have hs := (transport_trig (show z∈Icc 0 frameCap from
    ⟨hz.1,by norm_num [frameCap]; linarith [hz.2]⟩)).2.2.1
  dsimp [factorFirst,Explicit.eta]
  linarith [Real.cos_le_one z]

theorem c_derivative (θ : ℝ) : HasDerivAt (Explicit.c .low)
    (-69/20+18*(θ-1/6)) θ := by
  have hx : HasDerivAt (fun x : ℝ => x-Explicit.L) 1 θ := (hasDerivAt_id' θ).sub_const _
  have hh := ((hx.const_mul (69/20:ℝ)).const_sub (10389/10000:ℝ)).fun_add
    ((hx.fun_pow 2).const_mul (9:ℝ))
  exact hh.congr_deriv (by simp only [Explicit.L]; push_cast; ring)

theorem tilted_envelope_antitone :
    AntitoneOn (fun θ => Explicit.c .low θ*factor θ) (Icc (0:ℝ) (1/6)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun θ _ => ((c_derivative θ).mul (factor_derivative θ)).continuousAt.continuousWithinAt)
    (fun θ _ => (c_derivative θ).mul (factor_derivative θ))
  intro θ hθ
  have ht := Ioo_subset_Icc_self hθ
  have hc := Explicit.low_ranges ht
  have hc0 : 0≤Explicit.c .low θ := by linarith [hc.2.2.2.2.1]
  have hcd : -69/20+18*(θ-1/6)≤-(69/20:ℝ) := by linarith [ht.2]
  have h1 := mul_le_mul_of_nonpos_left (factor_lower ht) (by linarith : -69/20+18*(θ-1/6)≤0)
  have h2 := mul_le_mul_of_nonneg_left (factorFirst_upper ht) hc0
  dsimp [Explicit.eta] at h2
  nlinarith [hc.2.2.2.2.2.1]

theorem tilted_upper {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    Explicit.m .low θ z<233/125 := by
  have hc := Explicit.low_ranges hθ
  have hz' : z∈Icc (0:ℝ) (1/6) := ⟨hz.1,hz.2.trans hθ.2⟩
  have hfirst := mul_le_mul_of_nonneg_left (factor_monotone hz' hθ hz.2)
    (show 0≤Explicit.c .low θ by linarith [hc.2.2.2.2.1])
  have hsecond := tilted_envelope_antitone (by norm_num) hθ hθ.1
  have h0 : Explicit.c .low 0*factor 0=18639/10000 := by
    simp only [factor,Explicit.c,Explicit.L,Real.cos_zero,Real.sin_zero]
    norm_num
  change Explicit.m .low θ z≤Explicit.c .low θ*factor θ at hfirst
  simp only at hsecond
  linarith

theorem l_lower {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    (10073/10000:ℝ)≤Explicit.l .low θ := by
  have hx : 0≤1/6-θ := by linarith [hθ.2]
  dsimp [Explicit.l,Explicit.L]
  nlinarith [sq_nonneg (θ-1/6)]

theorem pairs {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ)
    (i : Fin 3) :
    0<Explicit.p .low θ z i ∧ Explicit.p .low θ z i≤Explicit.q .low θ z i ∧
      Explicit.q .low θ z i≤2*Explicit.p .low θ z i ∧
      Explicit.p .low θ z i≤LowPositive.pMax ∧ Explicit.q .low θ z i≤LowPositive.qMax := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hmax := tilted_upper hθ hz
  have hlm : Explicit.l .low θ≤Explicit.m .low θ z := hr.2.2.2.2.2.2.1.trans hm.1
  have hp := (Source.family_coefficients .low hθ hz).2.2 i
  refine ⟨hp.1,hp.2.1,hp.2.2,?_,?_⟩
  all_goals
    fin_cases i <;>
      simp only [Explicit.p,Explicit.q,Fin.reduceFinMk,Matrix.cons_val,
        min_eq_left hlm,max_eq_right hlm,LowPositive.pMax,LowPositive.qMax] <;>
      linarith [hr.2.1,hr.2.2.2.1]

theorem HB_ratio {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ)
    (i : Fin 3) (hi : i=0∨i=2) :
    Explicit.q .low θ z i≤(3/2)*Explicit.p .low θ z i := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hlm := hr.2.2.2.2.2.2.1.trans hm.1
  rcases hi with rfl|rfl
  · simp only [Explicit.p,Explicit.q,Matrix.cons_val_zero]
    linarith [hr.1]
  · simp only [Explicit.p,Explicit.q,Matrix.cons_val,
      min_eq_left hlm,max_eq_right hlm]
    nlinarith [hm.2,hr.2.2.1]

theorem interior_q_upper {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hz : z∈Icc 0 θ) (hs : s∈Icc 0 frameCap) (hint : Explicit.c .low θ≤LowD.sec s)
    (i : Fin 3) : Explicit.q .low θ z i<273/200 := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hc0 : 0<Explicit.c .low θ := by linarith [hr.2.2.2.2.1]
  have hcU : Explicit.c .low θ≤327/250 := hint.trans (NegativeELargeA.secant_range hs).2
  have hfactor := PositiveTD.Explicit.factor_upper z
  have hprod := mul_lt_mul_of_pos_left hfactor hc0
  have hmU : Explicit.m .low θ z<273/200 := by
    change Explicit.m .low θ z<Explicit.c .low θ*(1043/1000) at hprod
    nlinarith
  have hlU : Explicit.l .low θ<273/200 := by
    linarith [hr.2.2.2.2.2.2.1]
  fin_cases i <;> simp only [Explicit.q]
  · norm_num
  · exact hlU
  · exact max_lt hlU hmU

theorem interior_ranges {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 frameCap) (hint : Explicit.c .low θ≤LowD.sec s) :
    Explicit.k .low θ<17/25 ∧ Explicit.l .low θ<283/250 ∧ (27/100:ℝ)<Real.sin s := by
  let u : ℝ := 1/6-θ
  have hu : u∈Icc (0:ℝ) (1/6) :=
    ⟨by dsimp [u]; linarith [hθ.2],by dsimp [u]; linarith [hθ.1]⟩
  have hform : Explicit.c .low θ=10389/10000+(69/20)*u+9*u^2 := by
    dsimp [Explicit.c,Explicit.L,u]
    ring
  have hcU := hint.trans (NegativeELargeA.secant_range hs).2
  have huU : u<67/1000 := by
    by_contra hh
    have hlow : 67/1000≤u := le_of_not_gt hh
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤67/1000) hlow 2
    nlinarith
  have hu2 : u^2≤(67/1000)*u := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr huU.le)]
  have hk : Explicit.k .low θ=6708/10000-(3/20)*u+4*u^2 := by
    dsimp [Explicit.k,Explicit.L,u]
    ring
  have hl : Explicit.l .low θ=10073/10000+(17/10)*u+(11/5)*u^2 := by
    dsimp [Explicit.l,Explicit.L,u]
    ring
  have hcos := NegativeESecant.cos_pos hs
  have hprod := (le_div_iff₀ hcos).1 hint
  have hcl := (Explicit.low_ranges hθ).2.2.2.2.1
  have hcosU : (10389/10000)*Real.cos s≤1 := by
    have hh := mul_le_mul_of_nonneg_right hcl hcos.le
    linarith
  have hcos2 := pow_le_pow_left₀ (show 0≤(10389/10000:ℝ)*Real.cos s by positivity) hcosU 2
  have hsin := (transport_trig hs).2.2.1
  refine ⟨by nlinarith,by nlinarith,?_⟩
  by_contra hh
  have hsU : Real.sin s≤27/100 := le_of_not_gt hh
  have hs2 := pow_le_pow_left₀ hsin hsU 2
  nlinarith [Real.sin_sq_add_cos_sq s]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.LowRanges
end
end
end
