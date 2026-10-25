module

public import SquaresInCircles.Eight.Words.Common.OneSecondary
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Eight squares: two complete polynomial supports for a zero-quarter primary contact

The half-angle substitution produces two degree-eight polynomials. Their
explicit differences from one common polynomial have nonnegative
coefficients after the single shift `x = 3/8-z`. The common polynomial
is positive on the whole interval by three grouped factors.

No angle cover or variable-domain certificate is used. The finite exact
coefficient reductions below are unexecuted proof scripts.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set

namespace SquaresInCircles.Eight.ZeroPrimaryPolynomial

open Polynomial CommonQuarter Arithmetic

def mass : Bool→ℚ
  | false => 4/5
  | true => 107/100

def anchor : Bool→ℚ
  | false => 899/1000
  | true => 7/12

def B : Bool→ℚ[X]
  | false => C (2399/1250)+C (3863/2500)*X+C (139/25)*X^2+
      C (2963/2500)*X^3+C (4101/1250)*X^4
  | true => C (107/48)+C (2269/1250)*X+C (61/10)*X^2+
      C (1819/1250)*X^3+C (4213/1200)*X^4

def D : ℚ[X] := 1+X^2
def V (core : Bool) : ℚ[X] :=
  (C (mass core)*D+C (4/5)*X)^2+C (4*(111/100)^2)*X^2
def P (core : Bool) : ℚ[X] := (B core)^2-C (9789/2500)*D^2*V core
def J : ℚ[X] := C (1/100)+C 3*X-C 4*X^2-C 16*X^3+
  C 33*X^4-C 56*X^5+C 45*X^6-C 28*X^7+C 7*X^8
def remainder (core : Bool) : ℚ[X] := (P core).comp (C (3/8)-X)-J

/-- The exact coefficients of the two remainders, by evaluation. -/
private def r11_c : Bool → Fin 9 → ℚ
  | false => ![3060651919197/5242880000000, 55171396631/102400000000, 20322758981/20480000000,
      401086219/128000000, 1190115399/3200000000, 19156109/12500000, 20797309/25000000,
      361067/781250, 1965101/1562500]
  | true => ![6649627203349/15099494400000000, 12806316837187/78643200000000,
      41247230469769/19660800000000, 53775643369/245760000000, 4536743663087/1843200000000,
      1303400833/3840000000, 1542517241/4800000000, 286991131/300000000, 758682229/900000000]

private lemma r11_remainder_eq (core : Bool) :
    remainder core=∑j : Fin 9,C (r11_c core j)*X^j.val := by
  apply Polynomial.funext
  intro r
  simp only [remainder,P,D,V,J,eval_sub,eval_add,eval_mul,eval_pow,eval_C,eval_X,
    eval_comp,eval_one,Fin.sum_univ_succ,Fin.sum_univ_zero]
  cases core <;> simp [B,mass,r11_c] <;> ring

private lemma r11_coeff (core : Bool) (j : Fin 9) :
    (remainder core).coeff j.val=r11_c core j := by
  rw [r11_remainder_eq,finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have hne : (j:ℕ)≠b := fun h => hb (Fin.ext h.symm)
    simp [hne]
  · simp

theorem remainder_coeff_nonneg (core : Bool) :
    ∀j : Fin 9,0≤(remainder core).coeff j.val := by
  intro j
  rw [r11_coeff]
  cases core <;> fin_cases j <;> norm_num [r11_c]

theorem remainder_expansion (core : Bool) :
    (P core).comp (C (3/8)-X)=J+
      ∑j : Fin 9,C ((remainder core).coeff j.val)*X^j.val := by
  simp only [r11_coeff]
  rw [← r11_remainder_eq,remainder]
  ring

lemma J_positive {x : ℝ} (hx : x∈Icc 0 (3/20)) : 0<aeval x J := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h₁ : 0≤3-4*x-16*x^2 := by nlinarith
  have h₂ : 0≤33-56*x := by linarith [hx.2]
  have h₃ : 0≤45-28*x := by linarith [hx.2]
  have ht₁ := mul_nonneg hx.1 h₁
  have ht₂ := mul_nonneg (pow_nonneg hx.1 4) h₂
  have ht₃ := mul_nonneg (pow_nonneg hx.1 6) h₃
  have ht₄ := pow_nonneg hx.1 8
  have he : aeval x J=(1/100:ℝ)+x*(3-4*x-16*x^2)+
      x^4*(33-56*x)+x^6*(45-28*x)+7*x^8 := by
    simp [J]
    ring
  rw [he]
  positivity

theorem polynomial_positive (core : Bool) {z : ℝ} (hz : z∈Icc (9/40) (3/8)) :
    0<aeval z (P core) := by
  set x : ℝ := 3/8-z with hxdef
  have hx : x∈Icc 0 (3/20) := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hh : aeval x ((P core).comp (C (3/8)-X))=
      aeval x (J+∑j : Fin 9,C ((remainder core).coeff j.val)*X^j.val) := by
    rw [remainder_expansion core]
  have he : aeval x (C (3/8:ℚ)-X)=z := by
    simp only [map_sub,aeval_C,aeval_X,eq_ratCast,hxdef]
    push_cast
    ring
  rw [aeval_comp,he] at hh
  simp only [map_add,map_sum,map_mul,aeval_C,map_pow,aeval_X,eq_ratCast] at hh
  have hsum : 0≤∑j : Fin 9,((remainder core).coeff j.val:ℝ)*x^j.val := by
    apply Finset.sum_nonneg
    intro j _
    have hc : (0:ℝ)≤((remainder core).coeff j.val:ℝ) := by
      exact_mod_cast remainder_coeff_nonneg core j
    exact mul_nonneg hc (pow_nonneg hx.1 _)
  linarith [J_positive hx]

theorem numerator_positive (core : Bool) {z : ℝ} (hz : 0≤z) : 0<aeval z (B core) := by
  cases core <;> simp only [B,map_add,map_mul,map_pow,aeval_C,aeval_X] <;>
    norm_num <;> positivity

theorem radical_bound (core : Bool) {z : ℝ} (hz : z∈Icc (9/40) (3/8)) :
    CommonQuarter.radius*(1+z^2)*Real.sqrt (aeval z (V core))<aeval z (B core) := by
  have hV : 0≤aeval z (V core) := by simp [V,D]; positivity
  have hs := Real.sq_sqrt hV
  have hN := Real.sqrt_nonneg (aeval z (V core))
  have hP := polynomial_positive core hz
  have hB := numerator_positive core (z := z) (by linarith [hz.1])
  have hR := radius_sq
  have hR0 : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  simp only [P,map_sub,map_pow,map_mul,aeval_C,D,map_add,aeval_one,aeval_X] at hP
  have he : (CommonQuarter.radius*(1+z^2)*Real.sqrt (aeval z (V core)))^2=
      Q0*(1+z^2)^2*aeval z (V core) := by rw [mul_pow,mul_pow,hR,hs]
  norm_num [Q0] at hR hP he
  have hproduct : 0≤CommonQuarter.radius*(1+z^2)*Real.sqrt (aeval z (V core)) := by positivity
  nlinarith

def angleNumerator (d : ℝ) : ℝ :=
  (d-37/1000)*(1+Real.cos d)-(9/5)*Real.sin d
def angleNumeratorD (d : ℝ) : ℝ :=
  1-(4/5)*Real.cos d-(d-37/1000)*Real.sin d
def angleNumeratorDD (d : ℝ) : ℝ :=
  -(1/5)*Real.sin d-(d-37/1000)*Real.cos d

lemma angleNumerator_deriv (d : ℝ) :
    HasDerivAt angleNumerator (angleNumeratorD d) d := by
  have h := (((hasDerivAt_id' d).sub_const (37/1000)).fun_mul
    ((Real.hasDerivAt_cos d).const_add 1)).fun_sub
      ((Real.hasDerivAt_sin d).const_mul (9/5))
  exact h.congr_deriv (by unfold angleNumeratorD; ring)

lemma angleNumeratorD_deriv (d : ℝ) :
    HasDerivAt angleNumeratorD (angleNumeratorDD d) d := by
  have h := (((Real.hasDerivAt_cos d).const_mul (4/5)).const_sub 1).fun_sub
    (((hasDerivAt_id' d).sub_const (37/1000)).fun_mul (Real.hasDerivAt_sin d))
  exact h.congr_deriv (by unfold angleNumeratorDD; ring)

lemma angleNumerator_concave :
    ConcaveOn ℝ (Icc (9/20) (7/10)) angleNumerator := by
  apply concave_of_deriv2 (fun d _ => angleNumerator_deriv d)
    (fun d _ => angleNumeratorD_deriv d)
  intro d hd
  have ht := positive_trig ⟨by linarith [hd.1],hd.2⟩
  have hh := mul_nonneg (show 0≤d-37/1000 by linarith [hd.1])
    (show 0≤Real.cos d by linarith [ht.1])
  dsimp [angleNumeratorDD]
  nlinarith [ht.2.2.1]

lemma angleNumerator_endpoints :
    0<angleNumerator (9/20) ∧ 0<angleNumerator (7/10) := by
  have hs := sin_upper_five (show (0:ℝ)≤9/20 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤9/20 by norm_num)
  norm_num at hs hc
  have ht := cap_trig
  dsimp [angleNumerator]
  constructor <;> linarith [ht.2.1,ht.2.2.1]

/-- A direct concavity argument gives the affine lower angle bound used
by both polynomial numerators. -/
theorem angle_lower {d : ℝ} (hd : d∈Icc (9/20) (7/10)) :
    (9/5)*halfRatio d+37/1000<d := by
  have hm := angleNumerator_concave.min_le_of_mem_Icc
    (by norm_num) (by norm_num) hd
  have hp : 0<angleNumerator d :=
    (lt_min angleNumerator_endpoints.1 angleNumerator_endpoints.2).trans_le hm
  have hd' : 0≤d ∧ d≤4/5 := ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have hden := halfRatio_den_pos hd'
  have hid := (halfRatio_identities hd').1
  have hprod : 0<(d-(9/5)*halfRatio d-37/1000)*(1+Real.cos d) := by
    dsimp [angleNumerator] at hp
    nlinarith
  have hpos := pos_of_mul_pos_left hprod hden.le
  linarith

theorem half_angle_data {d : ℝ} (hd : d∈Icc (9/20) (7/10)) :
    halfRatio d∈Icc (9/40) (3/8) ∧
    (1+(halfRatio d)^2)*Real.sin d=2*halfRatio d ∧
    (1+(halfRatio d)^2)*Real.cos d=1-(halfRatio d)^2 := by
  have hd' : 0≤d ∧ d≤4/5 := ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have hden := halfRatio_den_pos hd'
  have hid := halfRatio_identities hd'
  have ht := positive_trig ⟨hd'.1,hd.2⟩
  have hlow := halfRatio_lower hd'
  have hu : halfRatio d≤3/8 := by
    apply (div_le_iff₀ hden).2
    linarith [ht.1,ht.2.2.2.1]
  have he : (halfRatio d)^2*(1+Real.cos d)=1-Real.cos d := by
    nlinarith [congrArg (fun r : ℝ => halfRatio d*r) hid.1]
  refine ⟨⟨by linarith [hd.1],hu⟩,?_,?_⟩
  · nlinarith [congrArg (fun r : ℝ => halfRatio d*r) he]
  · nlinarith

def support (core : Bool) (d : ℝ) : ℝ :=
  let l : ℝ := (mass core:ℝ)/Real.sin d
  d+(9/50)*frameCost d+l*(oneWidth d+(anchor core:ℝ)*Real.cos d)+
    (2/5)*outerAxial+(l+2/5+111/100)/2-
      CommonQuarter.radius*Real.sqrt ((l+2/5)^2+(111/100)^2)

/-- The complete two-choice primary support on the full forced angle
interval; its only inputs are the intrinsic core/outer choice and angle. -/
theorem support_gt (core : Bool) {d : ℝ} (hd : d∈Icc (9/20) (7/10)) :
    (197/200:ℝ)<support core d := by
  let z : ℝ := halfRatio d
  let D0 : ℝ := 1+z^2
  let l : ℝ := (mass core:ℝ)/Real.sin d
  have hh := half_angle_data hd
  have hz : z∈Icc (9/40) (3/8) := hh.1
  have hz0 : 0<z := by linarith [hz.1]
  have hD : 0<D0 := by dsimp [D0]; positivity
  have ht := positive_trig ⟨by linarith [hd.1],hd.2⟩
  have hsin : 0<Real.sin d := by
    have hh := (positive_taylor_reserves ⟨by linarith [hd.1],hd.2⟩).1
    linarith [hd.1]
  have hs : Real.sin d=2*z/D0 := by
    apply (eq_div_iff hD.ne').2
    simpa [z,D0,mul_comm] using hh.2.1
  have hc : Real.cos d=(1-z^2)/D0 := by
    apply (eq_div_iff hD.ne').2
    simpa [z,D0,mul_comm] using hh.2.2
  have hl : l=(mass core:ℝ)*D0/(2*z) := by
    dsimp [l]
    rw [hs]
    field_simp [hD.ne',hz0.ne']
  have hl0 : 0≤l := by
    dsimp [l]
    apply div_nonneg _ hsin.le
    cases core <;> norm_num [mass]
  have hnorm : Real.sqrt (aeval z (V core))=
      2*z*Real.sqrt ((l+2/5)^2+(111/100)^2) := by
    have hnormsq := Real.sq_sqrt (show 0≤(l+2/5)^2+(111/100:ℝ)^2 by positivity)
    have hV : aeval z (V core)=
        (2*z*Real.sqrt ((l+2/5)^2+(111/100)^2))^2 := by
      simp only [V,D,map_add,map_mul,map_pow,aeval_C,aeval_one,aeval_X,eq_ratCast]
      rw [mul_pow,mul_pow,hnormsq,hl]
      push_cast
      dsimp [D0]
      field_simp [hz0.ne']
      ring
    rw [hV,Real.sqrt_sq (by positivity)]
  have hrad := radical_bound core hz
  have ha : (707/500:ℝ)<outerAxial := by linarith [fine_outer_endpoint_bounds.1]
  have hang : (9/5)*z+37/1000<d := angle_lower hd
  have hpositive : 0<2*z*D0*(d-((9/5)*z+37/1000)+(2/5)*(outerAxial-707/500)) := by
    apply mul_pos (by positivity)
    linarith
  have hid : 2*z*D0*(support core d-197/200)-
      (aeval z (B core)-CommonQuarter.radius*D0*Real.sqrt (aeval z (V core)))=
      2*z*D0*(d-((9/5)*z+37/1000)+(2/5)*(outerAxial-707/500)) := by
    rw [hnorm]
    dsimp [support]
    change 2*z*D0*(d+(9/50)*frameCost d+l*(oneWidth d+
      (anchor core:ℝ)*Real.cos d)+(2/5)*outerAxial+(l+2/5+111/100)/2-
        CommonQuarter.radius*Real.sqrt ((l+2/5)^2+(111/100)^2)-197/200)-
      (aeval z (B core)-CommonQuarter.radius*D0*(2*z*Real.sqrt ((l+2/5)^2+(111/100)^2)))=_
    dsimp [frameCost,oneWidth]
    rw [abs_of_nonneg hsin.le,hs,hc,hl]
    cases core <;> simp only [B,map_add,map_mul,map_pow,aeval_C,aeval_X,mass,anchor,eq_ratCast]
    all_goals push_cast; dsimp [D0]; field_simp [hz0.ne',hD.ne']; ring
  have hproduct : 0<2*z*D0*(support core d-197/200) := by
    change CommonQuarter.radius*D0*Real.sqrt (aeval z (V core))<aeval z (B core) at hrad
    linarith
  exact sub_pos.mp (pos_of_mul_pos_right hproduct (by positivity))

end SquaresInCircles.Eight.ZeroPrimaryPolynomial
