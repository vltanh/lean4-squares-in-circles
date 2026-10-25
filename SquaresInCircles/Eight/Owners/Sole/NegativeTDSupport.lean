module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Boundary.ActualSortedSupport
public import SquaresInCircles.Eight.Owners.TD0Span
public import SquaresInCircles.Eight.Owners.GA.One.AngleFunctions
public import SquaresInCircles.Eight.Owners.GA.Secant.Gain
public import SquaresInCircles.Eight.Owners.Sole.LowGapPolynomials
public import SquaresInCircles.Eight.Owners.Sole.OrdinaryData

/-!
# Eight squares: the sorted support of D after a negative T primary

The baseline of D is the clipped support at the radius `q` itself. Its negative increment is
bounded by the smaller of the unchanged D and A charges (`negative_min`). The diagonal comparison
uses a supporting point and the sorting inequality, so it also covers the tie at the transition
of supports (`positive_diagonal_lower`, `negative_diagonal_lower`). The TD gain exceeds its cost
(`TD_gain`), and the sorted support leaves the correction `(8/25)(c - p)²` (`sorted_correction`).
-/

section
/-!
## Two coefficient comparisons for the middle and high sole-E families

The first comparison keeps the correlation between
the two high-family coefficients; it is a quartic with positive Bernstein coefficients on the
high band (`high_norm_square`). The second proves that the actual
middle E-endpoint coefficient is below c, using directed Taylor bounds.
Each is one polynomial inequality on its complete coefficient interval.
The exact reductions have not been run.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SoleBalancedPolynomials
open Polynomial WholeIntervalPolynomial SoleECoefficients HighOrderTaylor

def middleCoefficientGap : ℚ[X] :=
  SoleScalarPolynomials.c .middle-SoleScalarPolynomials.cosine .middle-
    SoleScalarPolynomials.eta .middle*
      SoleLowGapPolynomials.sinUpper.comp (SoleScalarPolynomials.parameter .middle)


/-! ### Kernel certificates

The polynomials are mirrored by scaled integer coefficient lists
(`PolynomialCertificates`); the identities and reserves are integer
computations checked by the kernel. -/

section Certificates
open WholeIntervalPolynomial.Certificate

/-- A rational lower reserve from an integer comparison. -/
private theorem lt_of_int {r : ℚ} {n d s m : ℕ} {Z : ℤ} (hr : r=(n:ℚ)/d) (hd : 0<d)
    (hs : 0<s) (h : (n:ℤ)*(s*2^m)<2*d*Z) : r<(Z:ℚ)/(s*2^m/2) := by
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  have hs' : (0:ℚ)<(s:ℚ)*2^m/2 := by positivity
  rw [hr,div_lt_div_iff₀ hd' hs']
  have h' := (Int.cast_lt (R := ℚ)).mpr h
  push_cast at h'
  linarith

private def sineS : Scaled :=
  ((((((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))).sub
    ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))).add
    ((Scaled.const (1/362880)).mul (Scaled.var.pow 9))).sub
    ((Scaled.const (1/39916800)).mul (Scaled.var.pow 11))).add
    ((Scaled.const (1/6227020800)).mul (Scaled.var.pow 13))).sub
    ((Scaled.const (1/1307674368000)).mul (Scaled.var.pow 15))

private theorem rep_sine : sineS.Rep PositiveScalarPolynomials.sine :=
  ((((((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 9))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 11))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 13))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))

private def cosineS : Scaled :=
  (((((((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))).add
    ((Scaled.const (1/40320)).mul (Scaled.var.pow 8))).sub
    ((Scaled.const (1/3628800)).mul (Scaled.var.pow 10))).add
    ((Scaled.const (1/479001600)).mul (Scaled.var.pow 12))).sub
    ((Scaled.const (1/87178291200)).mul (Scaled.var.pow 14)) |>.add
    ((Scaled.const (1/20922789888000)).mul (Scaled.var.pow 16))

private theorem rep_cosine : cosineS.Rep PositiveScalarPolynomials.cosine :=
  ((((((((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 8))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 10))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 12))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 14))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 16)))

private def sinUpperS : Scaled :=
  sineS.add ((Scaled.const (1/1307674368000)).mul (Scaled.var.pow 15))

private theorem rep_sinUpper : sinUpperS.Rep SoleLowGapPolynomials.sinUpper :=
  rep_sine.add ((Scaled.rep_const _).mul (Scaled.rep_var.pow 15))

/-- The parameter of the middle family is the affine map of `[-4/5,6/5]`. -/
private theorem middle_shift (p : ℚ[X]) :
    p.comp (SoleScalarPolynomials.parameter .middle)=centered (-4/5) (6/5) p := by
  simp only [SoleScalarPolynomials.parameter,SoleScalarPolynomials.origin,centered,affine]
  norm_num

private def middleCoefficientGapS : Scaled :=
  ((((Scaled.const (209/200)).add ((Scaled.const (13/20)).mul Scaled.var)).sub
    ((Scaled.const (3/2)).mul (Scaled.var.pow 2))).sub (cosineS.center 1 5 1 5)).sub
    (((Scaled.const (319/1000)).add ((Scaled.const (1/5)).mul Scaled.var)).mul
      (sinUpperS.center 1 5 1 5))

private theorem rep_middleCoefficientGap :
    middleCoefficientGapS.Rep middleCoefficientGap := by
  have hc : (cosineS.center 1 5 1 5).Rep (SoleScalarPolynomials.cosine .middle) := by
    rw [SoleScalarPolynomials.cosine,middle_shift]
    exact rep_cosine.centered 1 5 1 5 (by norm_num) (by norm_num) (by norm_num)
  have hs : (sinUpperS.center 1 5 1 5).Rep
      (SoleLowGapPolynomials.sinUpper.comp (SoleScalarPolynomials.parameter .middle)) := by
    rw [middle_shift]
    exact rep_sinUpper.centered 1 5 1 5 (by norm_num) (by norm_num) (by norm_num)
  exact ((((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).sub hc).sub
    (((Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)).mul hs)

private theorem rep_middleCoefficientGap_centered :
    (middleCoefficientGapS.center 3 40 1 1).Rep (centered 0 (3/20) middleCoefficientGap) :=
  rep_middleCoefficientGap.centered 3 40 1 1 (by norm_num) (by norm_num) (by norm_num)

end Certificates

theorem middleCoefficientGap_identity : centered 0 (3/20) middleCoefficientGap=
    expansion 16 (centered 0 (3/20) middleCoefficientGap) := by
  exact rep_middleCoefficientGap_centered.eq_expansion (by decide +kernel) (by decide +kernel)

theorem middleCoefficientGap_reserve :
    (1/10000 : ℚ)<lowerOn 16 0 (3/20) middleCoefficientGap := by
  rw [Certificate.lowerOn_eq_of_rep rep_middleCoefficientGap_centered (by decide +kernel)
    (by decide +kernel)]
  exact lt_of_int (n := 1) (d := 10000) (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

theorem high_norm_square {t : ℝ} (ht : t∈domain .high) :
    (k .high t)^2*(1+(g .high t)^2)<(53/50 : ℝ)^2 := by
  simp only [domain,frameCap,Set.mem_Icc] at ht
  have h1 : 0≤t-7/20 := sub_nonneg.2 ht.1
  have h2 : 0≤7/10-t := sub_nonneg.2 ht.2
  simp only [k,g]
  linarith [pow_nonneg h1 4,mul_nonneg (pow_nonneg h1 3) h2,
    mul_nonneg (pow_nonneg h1 2) (pow_nonneg h2 2),mul_nonneg h1 (pow_nonneg h2 3),pow_nonneg h2 4]

theorem middle_p_lt_c {t : ℝ} (ht : t∈domain .middle) :
    p .middle t t<c .middle t := by
  have hz := SoleScalarPolynomials.local_parameter ht
  have hb := positive_on_interval (by norm_num) middleCoefficientGap_identity
    middleCoefficientGap_reserve
    (show t-1/5∈Set.Icc ((0:ℚ):ℝ) ((3/20:ℚ):ℝ) by
      simpa [SoleScalarPolynomials.origin,SoleScalarPolynomials.length] using hz)
  have hc := SoleScalarData.polynomial_parameters .middle t
  have htrig := SoleScalarData.polynomial_trig .middle t
  have hpar : aeval (t-1/5) (SoleScalarPolynomials.parameter .middle)=t := by
    simp [SoleScalarPolynomials.parameter,SoleScalarPolynomials.origin]
  norm_num [SoleScalarPolynomials.origin] at hc htrig
  simp only [middleCoefficientGap,map_sub,map_mul,aeval_comp,hpar,
    SoleLowGapPolynomials.sinUpper_eval,hc.2.2.1,hc.2.2.2.2,htrig.2.1] at hb
  have hs := sin_le_S13 (angle ht).1
  have hcos := cos_le_C16 (angle ht).1
  have heta := (positive ht).2.2.2.2
  have hm := mul_le_mul_of_nonneg_left hs heta
  simp only [p,show Band.middle≠Band.high by decide,ite_false]
  norm_num at hb
  linarith

end SquaresInCircles.Eight.SoleBalancedPolynomials
end
end
end

section
/-!
## Original-split coefficient bounds in the middle and high families

The bounds cover all x,e in [0,t], so no optimizing
split is assumed. The high H upper bound uses the correlated polynomial
family; the low endpoint of that H pair follows from whole-arc harmonic
concavity. The middle sole-DE coefficient retains its larger 59/50 cap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleBalancedCoefficients
open SoleECoefficients SoleOrdinaryData SecondaryEStress

theorem cosine_quadratic {s : ℝ} (hs : 0≤ s) : 1-s^2/2≤Real.cos s := by
  have hh := nonneg_of_deriv_nonneg (fun x => Real.cos x-1+x^2/2)
    (by fun_prop) (by norm_num)
    (fun x hx => by simp (disch := fun_prop); linarith [Real.sin_le hx]) hs
  linarith

theorem tilted_lower {a s : ℝ} (ha : 31/100≤a) (hs : s∈Icc 0 (7/20 : ℝ)) :
    1≤Real.cos s+a*Real.sin s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hs0 := (transport_trig hs').2.2.1
  have hsin := Real.sin_ge_sub_cube hs.1
  have hcos := cosine_quadratic hs.1
  have hsq := mul_le_mul_of_nonneg_left hs.2 hs.1
  have hsq' : s^2≤49/400 := by nlinarith [hs.1,hs.2]
  have hcube := mul_le_mul_of_nonneg_right hsq' hs.1
  have hm := mul_le_mul_of_nonneg_right ha hs0
  nlinarith

theorem tilted_square (a s : ℝ) :
    (Real.cos s+a*Real.sin s)^2≤1+a^2 := by
  have hid : (Real.cos s+a*Real.sin s)^2+(Real.sin s-a*Real.cos s)^2=
      (1+a^2)*((Real.sin s)^2+(Real.cos s)^2) := by ring
  rw [Real.sin_sq_add_cos_sq] at hid
  nlinarith [sq_nonneg (Real.sin s-a*Real.cos s)]

theorem tilted_upper {a s : ℝ} (ha : a∈Icc 0 (7/20 : ℝ)) :
    Real.cos s+a*Real.sin s<53/50 := by
  have hs := tilted_square a s
  have ha2 : a^2≤49/400 := by nlinarith [ha.1,ha.2]
  nlinarith

theorem r_mono : MonotoneOn (fun s : ℝ => Real.cos s+(7/10)*Real.sin s) (Icc 0 (7/20)) := by
  apply monoOn_of_hasDeriv_nonneg
  · fun_prop
  · intro s _
    exact (Real.hasDerivAt_cos s).add ((Real.hasDerivAt_sin s).const_mul (7/10))
  · intro s hs
    have hsin := Real.sin_le hs.1.le
    have hcos := cosine_quadratic hs.1.le
    have hs2 : s^2≤49/400 := by nlinarith [hs.1,hs.2]
    nlinarith [hs.2]

theorem middle_split {t x e : ℝ} (ht : t∈domain .middle)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    k .middle t≤n .middle t x ∧ n .middle t x<53/50 ∧
    1≤p .middle t e ∧ p .middle t e<53/50 ∧
    1≤r .middle e ∧ r .middle e<59/50 := by
  have hx' : x∈Icc 0 (7/20 : ℝ) := ⟨hx.1,hx.2.trans ht.2⟩
  have he' : e∈Icc 0 (7/20 : ℝ) := ⟨he.1,he.2.trans ht.2⟩
  have hp := SoleECoefficients.positive ht
  rcases middle_bounds ht with ⟨hk0,hk1,hc0,hc1,hl0,hl1,hlk,hcl,heta0,heta1⟩
  have hnlo := mul_le_mul_of_nonneg_left (tilted_lower (a := 31/100) le_rfl hx') hp.1.le
  have hnhi := mul_lt_mul_of_pos_left (tilted_upper (a := 31/100) (s := x) (by norm_num)) hp.1
  have hplo := tilted_lower (a := eta .middle t) (by linarith) he'
  have hphi := tilted_upper (a := eta .middle t) (s := e) ⟨hp.2.2.2.2,heta1.le⟩
  have hrlo := tilted_lower (a := 7/10) (by norm_num) he'
  have hrhi := r_mono he' (show (7/20 : ℝ)∈Icc 0 (7/20 : ℝ) by norm_num) he'.2
  dsimp only at hrhi
  have hc := cos_upper_four (x := (7/20 : ℝ)) (by norm_num)
  have hs := sin_upper_five (x := (7/20 : ℝ)) (by norm_num)
  norm_num at hc hs
  dsimp only [n,p,r,g,tiltedWeight]
  simp only [show Band.middle≠Band.high by decide,↓reduceIte]
  refine ⟨by linarith only [hnlo],by linarith only [hnhi,hk1],hplo,hphi,hrlo,
    by linarith only [hrhi,hc,hs]⟩

theorem high_n {t x : ℝ} (ht : t∈domain .high) (hx : x∈Icc 0 t) :
    19/20<n .high t x ∧ n .high t x<53/50 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans ht.2⟩
  rcases high_bounds ht with ⟨hklo,hkhi,hc,hl0,hl1,hlk,hcl,hglo,hghi⟩
  have hk0 := (SoleECoefficients.positive ht).1
  have hg0 := (SoleECoefficients.positive ht).2.2.2.1
  have hh : (19/20 : ℝ)<Real.cos x+(149/500)*Real.sin x := by
    have hz := trig_concave_gt (α := (0:ℝ)) (A := (149/500 : ℝ)) (B := (1:ℝ))
      (m := (19/20 : ℝ)) (l := (0:ℝ)) (u := frameCap)
      (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hx'
      (by norm_num)
      (by have hc := (transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
          have hs := OrdinaryNegativeEnvelope.cap_sin_lower
          nlinarith)
    simpa only [zero_mul,one_mul,zero_add,add_comm] using hz
  have hm := mul_le_mul_of_nonneg_right hglo (transport_trig hx').2.2.1
  have htilt : 19/20<Real.cos x+g .high t*Real.sin x := by linarith
  have hkm := mul_le_mul_of_nonneg_right (show (1:ℝ)≤k .high t by linarith [hklo])
    (show 0≤Real.cos x+g .high t*Real.sin x by linarith)
  have hsq := mul_le_mul_of_nonneg_left (tilted_square (g .high t) x) (sq_nonneg (k .high t))
  have hcorr := SoleBalancedPolynomials.high_norm_square ht
  dsimp [n,tiltedWeight]
  constructor
  · nlinarith
  · nlinarith

theorem ratio_from_interval {a b lo hi : ℝ} (ha : a∈Icc lo hi) (hb : b∈Icc lo hi)
    (hr : (2/3)*hi≤lo) : (2/3)*max a b≤ min a b := by
  have hmax := max_le ha.2 hb.2
  have hmin := le_min ha.1 hb.1
  linarith

theorem middle_conditions {de : Bool} {t x e : ℝ} (ht : t∈domain .middle)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) :
    (∀ i,(2/3)*large .middle de t x e i≤ small .middle de t x e i) ∧
    (∀ i,(983/1000 : ℝ)≤large .middle de t x e i ∧ large .middle de t x e i≤59/50) := by
  obtain ⟨hnlo,hnhi,hplo,hphi,hrlo,hrhi⟩ := middle_split ht hx he
  rcases middle_bounds ht with ⟨hk0,hk1,hc0,hc1,hl0,hl1,hlk,hcl,heta0,heta1⟩
  have hHn : n .middle t x∈Icc (983/1000 : ℝ) (59/50) := ⟨hk0.trans hnlo,by linarith⟩
  have hHr : (if de then r .middle e else 1)∈Icc (983/1000 : ℝ) (59/50) := by
    cases de <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> linarith
  have hDp : (if de then 1 else p .middle t e)∈Icc (1:ℝ) (111/100) := by
    cases de <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> linarith
  have hDc : c .middle t∈Icc (1:ℝ) (111/100) := ⟨by linarith,hc1.le⟩
  constructor
  · intro i
    fin_cases i
    · exact ratio_from_interval hHr hHn (by norm_num)
    · simpa [small,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,min_eq_left hlk.le,max_eq_right hlk.le] using
        (show (2/3)*k .middle t≤ell .middle t by linarith)
    · simpa [small,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,min_eq_left (ell_le_k_c ht).2,
        max_eq_right (ell_le_k_c ht).2] using hcl
    · exact ratio_from_interval hDp hDc (by norm_num)
  · intro i
    fin_cases i
    · exact ⟨hHr.1.trans (le_max_left _ _),max_le hHr.2 hHn.2⟩
    · simpa [large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,max_eq_right hlk.le] using ⟨hk0,show k .middle t≤59/50 by linarith⟩
    · simpa [large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,max_eq_right (ell_le_k_c ht).2] using
        ⟨show 983/1000≤c .middle t by linarith,show c .middle t≤59/50 by linarith⟩
    · exact ⟨(show (983/1000 : ℝ)≤c .middle t by linarith).trans (le_max_right _ _),
        (max_le hDp.2 hDc.2).trans (by norm_num)⟩

theorem high_conditions {de : Bool} {t x e : ℝ} (ht : t∈domain .high)
    (hx : x∈Icc 0 t) (_he : e∈Icc 0 t) :
    (∀ i,(2/3)*large .high de t x e i≤ small .high de t x e i) ∧
    (∀ i,(1:ℝ)≤large .high de t x e i ∧ large .high de t x e i≤113/100) := by
  obtain ⟨hnlo,hnhi⟩ := high_n ht hx
  rcases high_bounds ht with ⟨hk0,hk1,hc,hl0,hl1,hlk,hcl,hg0,hg1⟩
  have hH := ratio_from_interval
    (show (1:ℝ)∈Icc (19/20 : ℝ) (53/50) by norm_num)
    (show n .high t x∈Icc (19/20 : ℝ) (53/50) from ⟨hnlo.le,hnhi.le⟩) (by norm_num)
  have hlk' := hlk.le
  have hlc' := (ell_le_k_c ht).2
  constructor
  · intro i
    fin_cases i
    · cases de <;> simpa [small,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,SoleECoefficients.r] using hH
    · simp only [small,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta]
      simp [min_eq_left hlk',max_eq_right hlk']
      linarith
    · simp only [small,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta]
      simpa [min_eq_left hlc',max_eq_right hlc'] using hcl
    · cases de <;> norm_num [small,large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,SoleECoefficients.p,hc]
  · intro i
    fin_cases i
    · have h0 : large .high de t x e 0=max 1 (n .high t x) := by
        cases de <;> simp [large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,SoleECoefficients.r]
      show (1:ℝ)≤large .high de t x e 0 ∧ large .high de t x e 0≤113/100
      rw [h0]
      exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith)⟩
    · simp only [large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta]
      simp [max_eq_right hlk']
      constructor <;> linarith
    · simp only [large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta]
      simp [hc]
      exact ⟨Or.inr (by norm_num),by linarith⟩
    · cases de <;> norm_num [large,SoleOrdinaryData.alpha,SoleOrdinaryData.beta,SoleECoefficients.p,hc]

end SquaresInCircles.Eight.SoleBalancedCoefficients
end
end
end

section
/-!
## Strict gains of the two negative T primaries

Both gains have slope strictly above `21/20`. The TD gain uses the sorted bound `0.9` on the
tangent, and its whole interval `0 < s ≤ 3/10` follows from one positive quadratic once the
positive cosine is cleared (`TD_strict`). The BT gain uses the capture at `9/100`, before any
scalar enlargement to `3/10` (`BT_quadratic`, `BT_strict`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTGain
open GlobalGA

theorem TD_strict {s : ℝ} (hs : s∈Ioc 0 (3/10:ℝ)) :
    (21/20)*s<(13/12)*Real.tan s-(2/5)*(1/Real.cos s-1) := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcpos : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hsin := Real.sin_ge_sub_cube hs.1.le
  have hcosL := cos_lower_six hs.1.le
  have hcosU := mul_le_mul_of_nonneg_left (cos_upper_four hs.1.le)
    (show 0≤(21/20)*s by linarith [hs.1])
  have hs3 := pow_nonneg hs.1.le 3
  have h4 : s^4≤(3/10)*s^3 := by
    have hh := mul_le_mul_of_nonneg_right hs.2 hs3
    linarith
  have h5 : s^5≤(9/100)*s^3 := by
    have hs2 : s^2≤9/100 := by nlinarith [hs.1,hs.2]
    have hh := mul_le_mul_of_nonneg_right hs2 hs3
    linarith
  have h6 : s^6≤(27/1000)*s^3 := by
    have hs3' : s^3≤27/1000 := by
      have hh := pow_le_pow_left₀ hs.1.le hs.2 3
      norm_num at hh
      exact hh
    have hh := mul_le_mul_of_nonneg_right hs3' hs3
    linarith
  have hpoly : 0<(1/30:ℝ)-s/5+(17/50)*s^2 := by
    have hid : (1/30:ℝ)-s/5+(17/50)*s^2=
        (17/50)*(s-5/17)^2+1/255 := by ring
    rw [hid]
    positivity
  have hprod := mul_pos hs.1 hpoly
  have hs4 := pow_nonneg hs.1.le 4
  have hnum : 0<(13/12)*Real.sin s-(2/5)*(1-Real.cos s)-(21/20)*s*Real.cos s := by
    linarith
  have hid : ((13/12)*Real.tan s-(2/5)*(1/Real.cos s-1)-(21/20)*s)*Real.cos s=
      (13/12)*Real.sin s-(2/5)*(1-Real.cos s)-(21/20)*s*Real.cos s := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hh : 0<((13/12)*Real.tan s-(2/5)*(1/Real.cos s-1)-(21/20)*s)*Real.cos s := by
    rw [hid]
    exact hnum
  have hg := (mul_pos_iff_of_pos_right hcpos).1 hh
  linarith

theorem BT_radius_ratio {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Icc 0 (9/100:ℝ)) :
    Real.sqrt q/Real.sqrt (gainRadicand a s)<214/125 := by
  have hs2 : s^2≤81/10000 := by nlinarith [hs.1,hs.2]
  have hcos : (19919/20000:ℝ)≤Real.cos s := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := s)]
  have hcos2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19919/20000) hcos 2
  have ha2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤117/200) ha 2
  have hprod := mul_le_mul ha2 hcos2 (by positivity) (sq_nonneg a)
  have hrad : 1+(117/200:ℝ)^2*(19919/20000)^2≤gainRadicand a s := by
    dsimp [gainRadicand]
    linarith
  have hQ' : q≤9789/2500 := hQ
  have hreserve : (9789/2500:ℝ)<(214/125:ℝ)^2*(1+(117/200)^2*(19919/20000)^2) := by
    norm_num
  have hh := mul_le_mul_of_nonneg_left hrad (sq_nonneg (214/125:ℝ))
  have hroot := Real.sqrt_pos.mpr (gainRadicand_pos a s)
  apply (div_lt_iff₀ hroot).2
  have h1 : Real.sqrt q<Real.sqrt ((214/125)^2*gainRadicand a s) :=
    Real.sqrt_lt_sqrt hq (by linarith)
  rw [Real.sqrt_mul (by positivity),Real.sqrt_sq (by norm_num)] at h1
  exact h1

theorem BT_derivative {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Icc 0 (9/100:ℝ)) :
    13/12-(89/125)*s≤ secantGainDeriv q a s := by
  have hr := BT_radius_ratio hq hQ ha hs
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by norm_num [frameCap]; linarith [hs.2]⟩
  obtain ⟨hc,hcu,hs0,hsu,hsc⟩ := transport_trig hs'
  have hst := Real.sin_le hs.1
  have hm := mul_le_mul_of_nonneg_right hr.le hs0
  have hlo : 0≤(13/12:ℝ)-(89/125)*s := by linarith [hs.2]
  have hc2 : (Real.cos s)^2≤1 := by nlinarith
  have hcpos : 0<Real.cos s := by linarith
  have hp := mul_nonneg hlo (sub_nonneg.mpr hc2)
  dsimp [secantGainDeriv]
  apply (le_div_iff₀ (sq_pos_of_pos hcpos)).2
  have he : Real.sqrt q*Real.sin s/Real.sqrt (gainRadicand a s)=
      (Real.sqrt q/Real.sqrt (gainRadicand a s))*Real.sin s := by ring
  rw [he]
  nlinarith

theorem BT_quadratic {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Icc 0 (9/100:ℝ)) :
    (13/12)*s-(89/250)*s^2≤ secantGain q a s := by
  have hd (x : ℝ) (hx : x∈Icc 0 (9/100:ℝ)) :
      HasDerivAt (fun x => secantGain q a x-(13/12)*x+(89/250)*x^2)
        (secantGainDeriv q a x-13/12+(89/125)*x) x := by
    have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
    have h := ((secantGain_hasDerivAt q a hc.ne').fun_sub
      ((hasDerivAt_id' x).const_mul (13/12:ℝ))).fun_add
        (((hasDerivAt_id' x).fun_pow 2).const_mul (89/250:ℝ))
    convert h using 1
    push_cast
    ring
  have hm : MonotoneOn (fun x => secantGain q a x-(13/12)*x+(89/250)*x^2)
      (Icc 0 (9/100:ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => hd x (Ioo_subset_Icc_self hx)
    · intro x hx
      linarith [BT_derivative hq hQ ha (Ioo_subset_Icc_self hx)]
  have hh := hm (show (0:ℝ)∈Icc 0 (9/100:ℝ) by norm_num) hs hs.1
  simp only [secantGain_zero] at hh
  linarith

theorem BT_strict {q a s : ℝ} (hq : 0≤q) (hQ : q≤qCap)
    (ha : 117/200≤a) (hs : s∈Ioc 0 (9/100:ℝ)) :
    (21/20)*s<secantGain q a s := by
  have hh := BT_quadratic hq hQ ha (Ioc_subset_Icc_self hs)
  have hm := mul_le_mul_of_nonneg_right hs.2 hs.1.le
  nlinarith [hs.1]

end SquaresInCircles.Eight.SoleNegativeTGain
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNegativeTDSupport
open ActualSortedSupport PositiveAngularEnvelope OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope SingleAngleConcavity SoleNormGain

def increment (q p g d : ℝ) : ℝ :=
  p*(edgeWidth d-1)+ActualSortedSupport.support q p g-ActualSortedSupport.support q (p*Real.cos d) (g+p*Real.sin d)

def actualIncrement (q p g d : ℝ) (D : SignedPoint) : ℝ :=
  p*(edgeWidth d-1)+ActualSortedSupport.support q p g-
    (p*Real.cos d*D.a+(g+p*Real.sin d)*(-D.y))

@[simp] theorem increment_zero (q p g : ℝ) : increment q p g 0=0 := by
  simp [increment,edgeWidth,pairWidth]

theorem full_identity {q p g d : ℝ} (hd : |d|≤frameCap) :
    p*(edgeWidth d-1)+full q p g-full q (p*Real.cos d) (g+p*Real.sin d)=
      p*psi d-Real.sqrt q*(pairNorm p g d-pairNorm p g 0) := by
  have hn := GlobalGA.Secondary.one_force_norm g p d
  rw [pairNorm_symm g p d] at hn
  dsimp [full]
  rw [hn,← pairNorm_zero p g]
  have hw := width_add_half_phi hd
  dsimp [PositiveAngularEnvelope.phi] at hw
  nlinarith [congrArg (fun x : ℝ => p*x) hw]

theorem force_sum_positive {p g d : ℝ} (hp : 0<p) (hgp : p/2≤g)
    (hd : |d|≤frameCap) : 0<p*Real.cos d+(g+p*Real.sin d) := by
  obtain ⟨hc,hs⟩ := small_angle hd
  have hs' := (abs_le.mp hs).1
  have hcos := mul_le_mul_of_nonneg_left hc hp.le
  have hsin := mul_le_mul_of_nonneg_left hs' hp.le
  norm_num [frameCap] at hcos hsin
  linarith

theorem full_lower {q p g d : ℝ} (hq : 0≤q) (hp : 0<p)
    (hgp : g<p) (hglo : p/2≤g) (hd : |d|≤frameCap) :
    p*psi d-Real.sqrt q*(pairNorm p g d-pairNorm p g 0)≤ increment q p g d := by
  have hh := support_le_full hq (force_sum_positive hp hglo hd).le
  rw [← full_identity hd]
  dsimp [increment]
  rw [ActualSortedSupport.support,ite_eq_right (not_le.mpr hgp)]
  linarith

theorem positive_diagonal_identity {q p g v : ℝ}
    (hp : 0≤p) (hpg : p≤g) (hv : v∈Icc 0 frameCap) :
    increment q p g v= -(corner q-1/2)*p*(PositiveAngularEnvelope.phi v-1) := by
  have hsin := (transport_trig hv).2.2.1
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one v) hp
  have hs := mul_nonneg hp hsin
  have hforce : p*Real.cos v≤g+p*Real.sin v := by linarith
  rw [increment,ActualSortedSupport.support,ite_eq_left hpg,ActualSortedSupport.support,ite_eq_left hforce,edgeWidth_positive_formula hv]
  dsimp [ActualSortedSupport.diagonal,PositiveAngularEnvelope.phi]
  ring

theorem positive_diagonal_lower {q p g v : ℝ}
    (hL : qLow≤q) (hQ : q≤qCap) (hp : 0≤p) (hpg : p≤g)
    (hv : v∈Icc 0 frameCap) : -(2/5)*p*v≤ increment q p g v := by
  rw [positive_diagonal_identity hp hpg hv]
  have hphi : 0≤PositiveAngularEnvelope.phi v-1 := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi hv)
  have hphiU : PositiveAngularEnvelope.phi v-1≤v := by
    dsimp [PositiveAngularEnvelope.phi]
    linarith [Real.cos_le_one v,Real.sin_le hv.1]
  have hcorner := corner_bounds hL hQ
  have hpv := mul_le_mul_of_nonneg_left hphiU hp
  have hmult := mul_le_mul_of_nonneg_left hpv (by linarith : 0≤corner q-1/2)
  have hcoef := mul_le_mul_of_nonneg_right
    (show corner q-1/2≤2/5 by linarith) (mul_nonneg hp hv.1)
  nlinarith

theorem positive_full_lower {q p g v : ℝ}
    (hq : 0≤q) (hp : 0<p) (hgp : g<p) (hglo : p/2≤g)
    (hv : v∈Icc 0 frameCap) :
    U (Real.sqrt q) g p v≤ increment q p g v := by
  have hh := full_lower hq hp hgp hglo
    (show |v|≤frameCap by rw [abs_of_nonneg hv.1]; exact hv.2)
  have hpsi := psi_positive hv
  have hphi := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi hv)
  have hcoef := mul_le_mul_of_nonneg_right hgp.le hphi
  rw [hpsi,pairNorm_symm p g v,pairNorm_symm p g 0] at hh
  dsimp [U]
  linarith

theorem negative_diagonal_lower {q p g v : ℝ}
    (hq : 0≤q) (hp : 0<p) (hpg : p≤g) (hv : v∈Icc 0 frameCap) :
    p*Vnu (Real.sqrt q) 1 1 1 v≤ increment q p g (-v) := by
  obtain ⟨hc,_,hs,hsU,_⟩ := transport_trig hv
  have hgn : 0<g-p*Real.sin v := by
    have hh := mul_lt_mul_of_pos_left hsU hp
    linarith
  have hsum : 0≤p*Real.cos v+(g-p*Real.sin v) := by
    have hh := mul_pos hp (show 0<Real.cos v by linarith)
    linarith
  obtain ⟨Ka,Kb,Kcircle,_,_,_,Ktangent,Ksupports⟩ := point hq hsum hgn
  have hfull := raw_full (f:=p*Real.cos v) (g:=p*(1-Real.sin v)) hq Kcircle.le
  have hsort := mul_le_mul_of_nonneg_left Ktangent (sub_nonneg.mpr hpg)
  have hbase : full q p p=diagonal q p p :=
    full_diagonal hq rfl (by linarith)
  have hfullid := full_identity (q:=q) (p:=p) (g:=p)
    (show |-v|≤frameCap by rw [abs_neg,abs_of_nonneg hv.1]; exact hv.2)
  rw [psi_negative hv] at hfullid
  have hhom0 := pairNorm_homogeneous hp.le 1 1 0
  have hhomv := pairNorm_homogeneous hp.le 1 1 (-v)
  simp only [mul_one] at hhom0 hhomv
  rw [hhom0,hhomv,hbase] at hfullid
  simp only [Real.cos_neg,Real.sin_neg] at hfullid
  have he : p+p*(-Real.sin v)=p*(1-Real.sin v) := by ring
  rw [he] at hfullid
  have hidentity : p*Vnu (Real.sqrt q) 1 1 1 v=
      p*(edgeWidth (-v)-1)+diagonal q p p-
        full q (p*Real.cos v) (p*(1-Real.sin v)) := by
    simp only [Vnu]
    linear_combination -hfullid
  have hinc : increment q p g (-v)=p*(edgeWidth (-v)-1)+diagonal q p g-
      (p*Real.cos v*Ka+(g-p*Real.sin v)*Kb) := by
    rw [increment,Real.cos_neg,Real.sin_neg,
      show g+p*-Real.sin v=g-p*Real.sin v by ring,← Ksupports,ActualSortedSupport.support,
      ite_eq_left hpg]
  rw [hidentity,hinc]
  simp only [ActualSortedSupport.diagonal] at hidentity hbase ⊢
  linarith

theorem negative_full_old {q p c g v : ℝ}
    (hq : 0≤q) (hp : 0<p) (_hc : 0<c) (hcg : c≤g)
    (hgp : g<p) (hpc : p≤2*c) (hv : v∈Icc 0 frameCap) :
    Vnu (Real.sqrt q) p c (max p c) v≤ increment q p g (-v) := by
  have hcp : c≤p := hcg.trans hgp.le
  have hcgain := normGain_smaller_mono (Real.sqrt_nonneg q) hp hv
    (show c∈Icc (p/2) p from ⟨by linarith,hcp⟩)
    (show g∈Icc (p/2) p from ⟨by linarith,hgp.le⟩) hcg
  have hh := full_lower hq hp hgp (by linarith : p/2≤g)
    (show |-v|≤frameCap by rw [abs_neg,abs_of_nonneg hv.1]; exact hv.2)
  rw [psi_negative hv] at hh
  rw [max_eq_left hcp]
  dsimp [normGain] at hcgain
  rw [pairNorm_symm c p 0,pairNorm_symm c p (-v),
    pairNorm_symm g p 0,pairNorm_symm g p (-v)] at hcgain
  dsimp [Vnu]
  linarith

theorem negative_min {q p c g k l v : ℝ}
    (hL : qLow≤q) (hp : 1≤p) (hc : 0<c) (hcg : c≤g) (hpc : p≤2*c)
    (hk : 0<k) (hl : 0<l) (hkl : k+l≤2) (hlinear : 11*k+l≤12)
    (hv : v∈Icc 0 frameCap) :
    min (Vnu (Real.sqrt q) p c (max p c) v)
      (Vnu (Real.sqrt q) l k l v)≤ increment q p g (-v) := by
  have hq : 0≤q := by norm_num [qLow] at hL; linarith
  have hR : 3/2≤Real.sqrt q := by
    have hh := Real.sq_sqrt hq
    norm_num [qLow] at hL
    nlinarith [Real.sqrt_nonneg q]
  by_cases hpg : p≤g
  · have hA := BalancedNegativeGain.dominates_A hR hk hl hkl hlinear hp hv
    exact (min_le_right _ _).trans
      (hA.trans (negative_diagonal_lower hq (by linarith) hpg hv))
  · exact (min_le_left _ _).trans
      (negative_full_old hq (by linarith) hc hcg (lt_of_not_ge hpg) hpc hv)

theorem TD_gain {q p c s : ℝ}
    (hL : qLow≤q) (hQ : q≤qCap) (hp : 0≤p) (hc : 0<c)
    (hs : s∈Ioc 0 (3/10:ℝ)) :
    (21/20)*c*s<c*((1/Real.cos s-1)/2+(13/12)*Real.tan s)-
      ActualSortedSupport.support q p (c/Real.cos s)+ActualSortedSupport.support q p c := by
  have hs' : s∈Icc 0 frameCap :=
    ⟨hs.1.le,by norm_num [frameCap]; linarith [hs.2]⟩
  have hcos : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hsec : c≤c/Real.cos s := by
    apply (le_div_iff₀ hcos).2
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one s) hc.le
    simpa only [mul_one] using hh
  have hlip := second_lipschitz_nine_tenths hL hQ
    (show 0≤p+c by positivity) (show 0≤p+c/Real.cos s by positivity)
    (div_pos hc hcos) hsec
  have hgain := mul_lt_mul_of_pos_left (SoleNegativeTGain.TD_strict hs) hc
  have hid : c/Real.cos s-c=c*(1/Real.cos s-1) := by ring
  rw [hid] at hlip
  nlinarith

theorem sorted_correction {q p c : ℝ}
    (hL : qLow≤q) (hQ : q≤qCap) (hp : 0≤p) (hc : 0≤c) (hpc : p≤c)
    (hN : Real.sqrt (p^2+c^2)≤307/200) :
    (8/25)*(c-p)^2≤full q p c-ActualSortedSupport.support q p c := by
  rw [ActualSortedSupport.support,ite_eq_left hpc]
  exact full_gap hL hQ hp hc hN

end SquaresInCircles.Eight.SoleNegativeTDSupport
end
end
end
