module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3PolynomialData

/-!
# Positivity of all fourteen BT3 reference numerators

Uncompiled Section 8. Seven curves have direct coefficient bounds,
five use their positive constant and exact polynomial quotient, and
the two tight low curves use the displayed reversed power tails.
The two low estimates retain their full quadratic reserves.
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Certificate
open WholeIntervalPolynomial

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mass_certificate (e : Curve) (j : Fin 4) :
    centered 0 (length e) (mass e j)=expansion 3 (centered 0 (length e) (mass e j)) ∧
    (19/25:ℚ)<lowerOn 3 0 (length e) (mass e j) := by
  cases e <;> fin_cases j <;> decide

theorem length_positive (e : Curve) : 0<length e := by
  cases e <;> norm_num [length,start,family,right,split]

theorem mass_positive (e : Curve) (j : Fin 4) {x : ℝ}
    (hx : x∈Icc 0 (length e:ℝ)) : 0<aeval x (mass e j) := by
  have hh := positive_on_interval (length_positive e) (mass_certificate e j).1
    (mass_certificate e j).2 hx
  linarith

def direct : Curve→Prop
  | .lowM | .lowSH | .lowSG | .highB | .highAB | .abG | .abH => True
  | _ => False
def directReserve : Curve→ℚ
  | .lowM => 63/1000 | .lowSH => 89/500 | .lowSG => 7/40
  | .highB => 259/1000 | .highAB => 287/10000
  | .abG => 337/10000 | .abH => 349/10000 | _ => 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem direct_certificate (e : Curve) (he : direct e) :
    centered 0 (length e) (numerator e)=
      expansion (degree e) (centered 0 (length e) (numerator e)) ∧
    directReserve e<lowerOn (degree e) 0 (length e) (numerator e) := by
  cases e <;> simp only [direct] at he <;> first | contradiction | decide

theorem direct_positive (e : Curve) (he : direct e) {x : ℝ}
    (hx : x∈Icc 0 (length e:ℝ)) : 0<aeval x (numerator e) := by
  have hh := positive_on_interval (length_positive e) (direct_certificate e he).1
    (direct_certificate e he).2 hx
  have hr : (0:ℝ)<(directReserve e:ℝ) := by
    cases e <;> simp only [direct] at he <;> first | contradiction | norm_num [directReserve]
  exact hr.trans hh

def quotientCase : Curve→Prop
  | .highH | .highG | .highGA | .gaH | .gaB => True
  | _ => False
def quotientReserve : Curve→ℚ
  | .highH => 53/1000 | .highG => 119/1000 | .highGA => 1/50
  | .gaH => 221/500 | .gaB => 101/200 | _ => 0
def initialReserve : Curve→ℚ
  | .highH => 1263/1000000 | .highG => 223/20000
  | .highGA | .gaH | .gaB => 1041/1000000 | _ => 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem quotient_certificate (e : Curve) (he : quotientCase e) :
    initialReserve e<(numerator e).eval 0 ∧
    centered 0 (length e) (numerator e).divX=
      expansion (degree e) (centered 0 (length e) (numerator e).divX) ∧
    quotientReserve e<lowerOn (degree e) 0 (length e) (numerator e).divX := by
  cases e <;> simp only [quotientCase] at he <;> first | contradiction | decide

theorem quotient_positive (e : Curve) (he : quotientCase e) {x : ℝ}
    (hx : x∈Icc 0 (length e:ℝ)) : 0<aeval x (numerator e) := by
  have hc := quotient_certificate e he
  have hq := positive_on_interval (length_positive e) hc.2.1 hc.2.2 hx
  have h0 : (initialReserve e:ℝ)<((numerator e).eval 0:ℝ) := by exact_mod_cast hc.1
  have hr0 : (0:ℝ)<(initialReserve e:ℝ) := by
    cases e <;> simp only [quotientCase] at he <;> first | contradiction | norm_num [initialReserve]
  have hrq : (0:ℝ)<(quotientReserve e:ℝ) := by
    cases e <;> simp only [quotientCase] at he <;> first | contradiction | norm_num [quotientReserve]
  exact hr0.trans (NonnegativeTotals.Certificate.initial_lower hx.1 h0 hq hrq.le)

def reversed (e : Curve) : ℚ[X] := (numerator e).comp (C (1/4)-X)
def tailCoefficient (e : Curve) (j : ℕ) : ℚ := (reversed e).coeff j
def tailBound (e : Curve) : ℚ :=
  ∑j : Fin (degree e-3),max (-(tailCoefficient e (j.val+4))) 0*(1/4)^j.val

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem tail_identity (e : Curve) (he : e=.lowH∨e=.lowGA) :
    reversed e=C (tailCoefficient e 0)+C (tailCoefficient e 1)*X+
      C (tailCoefficient e 2)*X^2+C (tailCoefficient e 3)*X^3+
      ∑j : Fin (degree e-3),C (tailCoefficient e (j.val+4))*X^(j.val+4) := by
  rcases he with rfl|rfl <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_H_certificate :
    (10535/10000000:ℚ)<tailCoefficient .lowH 0 ∧
    (-4581/100000:ℚ)<tailCoefficient .lowH 1 ∧
    (55939/50000:ℚ)<tailCoefficient .lowH 2 ∧
    (85067/10000:ℚ)<tailCoefficient .lowH 3 ∧ tailBound .lowH<42969/1000 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem low_GA_certificate :
    (16043/10000000:ℚ)<tailCoefficient .lowGA 0 ∧
    (7459/100000:ℚ)<tailCoefficient .lowGA 1 ∧
    (54229/50000:ℚ)<tailCoefficient .lowGA 2 ∧
    (878451/100000:ℚ)<tailCoefficient .lowGA 3 ∧ tailBound .lowGA<6743/125 := by decide

theorem power_tail {a w : ℝ} (hw : w∈Icc 0 (1/4:ℝ)) (j : ℕ) :
    -(max (-a) 0*(1/4)^j)*w^4≤a*w^(j+4) := by
  have ha : -max (-a) 0≤a := by linarith [le_max_left (-a) 0]
  have h0 : 0≤max (-a) 0 := le_max_right _ _
  have hp := pow_le_pow_left₀ hw.1 hw.2 j
  have h1 := mul_le_mul_of_nonneg_right ha (pow_nonneg hw.1 j)
  have h2 := mul_le_mul_of_nonneg_left hp h0
  have hh : -(max (-a) 0*(1/4)^j)≤a*w^j := by linarith
  have hs := mul_le_mul_of_nonneg_right hh (pow_nonneg hw.1 4)
  simpa only [pow_add,mul_assoc] using hs

theorem tail_lower (e : Curve) (he : e=.lowH∨e=.lowGA) {w : ℝ}
    (hw : w∈Icc 0 (1/4:ℝ)) :
    (tailCoefficient e 0:ℝ)+(tailCoefficient e 1:ℝ)*w+
      (tailCoefficient e 2:ℝ)*w^2+(tailCoefficient e 3:ℝ)*w^3-
      (tailBound e:ℝ)*w^4≤aeval w (reversed e) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ)
    (fun j _ => power_tail (a:=(tailCoefficient e (j.val+4):ℝ)) hw j.val)
  have hid := congrArg (fun p : ℚ[X] => aeval w p) (tail_identity e he)
  simp only [map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X] at hid
  have heq : (∑j : Fin (degree e-3),-(max (-(tailCoefficient e (j.val+4):ℝ)) 0*(1/4)^j.val)*w^4)=
      -(tailBound e:ℝ)*w^4 := by
    simp [tailBound,Finset.sum_mul,Finset.sum_neg_distrib]
  rw [heq] at hs
  linarith

theorem low_H_positive {x : ℝ} (hx : x∈Icc 0 (1/4:ℝ)) :
    0<aeval x (numerator .lowH) := by
  let w : ℝ := 1/4-x
  have hw : w∈Icc 0 (1/4:ℝ) := ⟨by dsimp [w]; linarith [hx.2],by dsimp [w]; linarith [hx.1]⟩
  have hb := tail_lower .lowH (Or.inl rfl) hw
  have h0 : (10535/10000000:ℝ)<(tailCoefficient .lowH 0:ℝ) := by exact_mod_cast low_H_certificate.1
  have h1 : (-4581/100000:ℝ)<(tailCoefficient .lowH 1:ℝ) := by exact_mod_cast low_H_certificate.2.1
  have h2 : (55939/50000:ℝ)<(tailCoefficient .lowH 2:ℝ) := by exact_mod_cast low_H_certificate.2.2.1
  have h3 : (85067/10000:ℝ)<(tailCoefficient .lowH 3:ℝ) := by exact_mod_cast low_H_certificate.2.2.2.1
  have hT : (tailBound .lowH:ℝ)<42969/1000 := by exact_mod_cast low_H_certificate.2.2.2.2
  have hquad : (2799/5000:ℝ)≤55939/50000+(85067/10000)*w-(42969/1000)*w^2 := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hquad' := mul_le_mul_of_nonneg_right hquad (sq_nonneg w)
  have hlin := mul_le_mul_of_nonneg_right h1.le hw.1
  have hsq := mul_le_mul_of_nonneg_right h2.le (sq_nonneg w)
  have hcube := mul_le_mul_of_nonneg_right h3.le (pow_nonneg hw.1 3)
  have hfour := mul_le_mul_of_nonneg_right hT.le (pow_nonneg hw.1 4)
  have hpositive : 0<aeval w (reversed .lowH) := by
    nlinarith [sq_nonneg (w-(4581/100000)/(2*(2799/5000)))]
  simpa [reversed,aeval_comp,w] using hpositive

theorem low_GA_positive {x : ℝ} (hx : x∈Icc 0 (1/4:ℝ)) :
    0<aeval x (numerator .lowGA) := by
  let w : ℝ := 1/4-x
  have hw : w∈Icc 0 (1/4:ℝ) := ⟨by dsimp [w]; linarith [hx.2],by dsimp [w]; linarith [hx.1]⟩
  have hb := tail_lower .lowGA (Or.inr rfl) hw
  have h0 : (16043/10000000:ℝ)<(tailCoefficient .lowGA 0:ℝ) := by exact_mod_cast low_GA_certificate.1
  have h1 : (7459/100000:ℝ)<(tailCoefficient .lowGA 1:ℝ) := by exact_mod_cast low_GA_certificate.2.1
  have h2 : (54229/50000:ℝ)<(tailCoefficient .lowGA 2:ℝ) := by exact_mod_cast low_GA_certificate.2.2.1
  have h3 : (878451/100000:ℝ)<(tailCoefficient .lowGA 3:ℝ) := by exact_mod_cast low_GA_certificate.2.2.2.1
  have hT : (tailBound .lowGA:ℝ)<6743/125 := by exact_mod_cast low_GA_certificate.2.2.2.2
  have hquad : -(91/1000:ℝ)≤54229/50000+(878451/100000)*w-(6743/125)*w^2 := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hquad' := mul_le_mul_of_nonneg_right hquad (sq_nonneg w)
  have hlin := mul_le_mul_of_nonneg_right h1.le hw.1
  have hsq := mul_le_mul_of_nonneg_right h2.le (sq_nonneg w)
  have hcube := mul_le_mul_of_nonneg_right h3.le (pow_nonneg hw.1 3)
  have hfour := mul_le_mul_of_nonneg_right hT.le (pow_nonneg hw.1 4)
  have hpositive : 0<aeval w (reversed .lowGA) := by
    nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  simpa [reversed,aeval_comp,w] using hpositive

/-- Every reference numerator is strictly positive on its whole native interval. -/
theorem numerator_positive (e : Curve) {x : ℝ} (hx : x∈Icc 0 (length e:ℝ)) :
    0<aeval x (numerator e) := by
  cases e
  · exact low_H_positive hx
  · exact direct_positive .lowM trivial hx
  · exact direct_positive .lowSH trivial hx
  · exact direct_positive .lowSG trivial hx
  · exact low_GA_positive hx
  · exact quotient_positive .highH trivial hx
  · exact quotient_positive .highG trivial hx
  · exact direct_positive .highB trivial hx
  · exact quotient_positive .highGA trivial hx
  · exact direct_positive .highAB trivial hx
  · exact quotient_positive .gaH trivial hx
  · exact quotient_positive .gaB trivial hx
  · exact direct_positive .abG trivial hx
  · exact direct_positive .abH trivial hx

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.Certificate
