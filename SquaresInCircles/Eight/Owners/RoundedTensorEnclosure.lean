module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.Tensor.PolynomialEnclosure

/-!
# Eight squares: the rounded degree-ten arithmetic of the critical positive-T certificate

Every primitive rounds coefficients to 10^-24 and its nonnegative error
upwards to 10^-20. Multiplication keeps total degree at most ten and
charges every discarded coefficient. Soundness uses the actual rounding
loss, so no unrecorded floating-point operation occurs in the model.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.RoundedTensorEnclosure
open Polynomial TensorWholeIntervalPolynomial
abbrev Enclosure := TensorPolynomialEnclosure.Enclosure
abbrev Contains := TensorPolynomialEnclosure.Contains
abbrev norm := TensorPolynomialEnclosure.norm

def coefficientScale : ℚ := 10^24
def errorScale : ℚ := 10^20
def roundedCoefficient (a : ℚ) : ℚ :=
  (⌊a*coefficientScale+1/2⌋:ℤ)/coefficientScale
def upwardError (a : ℚ) : ℚ := (⌈a*errorScale⌉:ℤ)/errorScale

def roundedPolynomial (p : Bivar) : Bivar :=
  ∑ i∈p.support,∑ j∈(p.coeff i).support,
    scalar (roundedCoefficient ((p.coeff i).coeff j))*X^i*(C X)^j

def round (a : Enclosure) : Enclosure :=
  let p := roundedPolynomial a.polynomial
  ⟨p,upwardError (a.error+norm (a.polynomial-p))⟩

theorem le_upwardError (a : ℚ) : a≤upwardError a := by
  have h := Int.le_ceil (a*errorScale)
  exact (le_div_iff₀ (by norm_num [errorScale])).2 h

theorem contains_round {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (round a) x y v := by
  have hn := TensorPolynomialEnclosure.norm_nonneg
    (a.polynomial-roundedPolynomial a.polynomial)
  have he := le_upwardError (a.error+norm (a.polynomial-roundedPolynomial a.polynomial))
  have he' : ((a.error+norm (a.polynomial-roundedPolynomial a.polynomial):ℚ):ℝ)≤
      (upwardError (a.error+norm (a.polynomial-roundedPolynomial a.polynomial)):ℝ) := by
    exact_mod_cast he
  have hp := TensorPolynomialEnclosure.evaluate_abs_le_norm
    (a.polynomial-roundedPolynomial a.polynomial) hx hy
  have ht := abs_add_le (v-evaluate x y a.polynomial)
    (evaluate x y a.polynomial-evaluate x y (roundedPolynomial a.polynomial))
  rw [map_sub] at hp
  refine ⟨(add_nonneg ha.1 hn).trans he,?_⟩
  change |v-evaluate x y (roundedPolynomial a.polynomial)|≤
    ((upwardError (a.error+norm (a.polynomial-roundedPolynomial a.polynomial)):ℚ):ℝ)
  have hid : v-evaluate x y a.polynomial+
      (evaluate x y a.polynomial-evaluate x y (roundedPolynomial a.polynomial))=
      v-evaluate x y (roundedPolynomial a.polynomial) := by ring
  rw [hid] at ht
  push_cast at he'
  linarith [ha.2]

def constant (r : ℚ) : Enclosure := round ⟨scalar r,0⟩
def outerVariable : Enclosure := round ⟨X,0⟩
def innerVariable : Enclosure := round ⟨C X,0⟩
def add (a b : Enclosure) : Enclosure :=
  round ⟨a.polynomial+b.polynomial,a.error+b.error⟩
def neg (a : Enclosure) : Enclosure := round ⟨-a.polynomial,a.error⟩
def sub (a b : Enclosure) : Enclosure := add a (neg b)

def truncate (p : Bivar) : Bivar :=
  ∑ i : Fin 11,∑ j : Fin 11,
    if i.val+j.val≤10 then scalar ((p.coeff i.val).coeff j.val)*X^i.val*(C X)^j.val else 0

def rawMul (a b : Enclosure) : Enclosure :=
  let p := a.polynomial*b.polynomial
  ⟨truncate p,norm (p-truncate p)+a.error*norm b.polynomial+
    b.error*norm a.polynomial+a.error*b.error⟩
def mul (a b : Enclosure) : Enclosure := round (rawMul a b)
def scale (r : ℚ) (a : Enclosure) : Enclosure := mul (constant r) a
def widen (a : Enclosure) (e : ℚ) : Enclosure :=
  round ⟨a.polynomial,a.error+e⟩

theorem contains_constant (r : ℚ) {x y : ℝ} (hx : |x|≤1) (hy : |y|≤1) :
    Contains (constant r) x y (r:ℝ) :=
  contains_round (TensorPolynomialEnclosure.contains_constant r x y) hx hy
theorem contains_outer {x y : ℝ} (hx : |x|≤1) (hy : |y|≤1) :
    Contains outerVariable x y x :=
  contains_round (TensorPolynomialEnclosure.contains_outer x y) hx hy
theorem contains_inner {x y : ℝ} (hx : |x|≤1) (hy : |y|≤1) :
    Contains innerVariable x y y :=
  contains_round (TensorPolynomialEnclosure.contains_inner x y) hx hy

theorem contains_add {a b : Enclosure} {x y v w : ℝ}
    (ha : Contains a x y v) (hb : Contains b x y w) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (add a b) x y (v+w) :=
  contains_round (TensorPolynomialEnclosure.Contains.add ha hb) hx hy
theorem contains_neg {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (neg a) x y (-v) :=
  contains_round (TensorPolynomialEnclosure.Contains.neg ha) hx hy
theorem contains_sub {a b : Enclosure} {x y v w : ℝ}
    (ha : Contains a x y v) (hb : Contains b x y w) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (sub a b) x y (v-w) := by
  have h := contains_add ha (contains_neg hb hx hy) hx hy
  rw [sub_eq_add_neg]
  exact h

theorem contains_rawMul {a b : Enclosure} {x y v w : ℝ}
    (ha : Contains a x y v) (hb : Contains b x y w) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (rawMul a b) x y (v*w) := by
  have hea : (0:ℝ)≤(a.error:ℝ) := by exact_mod_cast ha.1
  have heb : (0:ℝ)≤(b.error:ℝ) := by exact_mod_cast hb.1
  have hpa := TensorPolynomialEnclosure.evaluate_abs_le_norm a.polynomial hx hy
  have hpb := TensorPolynomialEnclosure.evaluate_abs_le_norm b.polynomial hx hy
  have htail := TensorPolynomialEnclosure.evaluate_abs_le_norm
    (a.polynomial*b.polynomial-truncate (a.polynomial*b.polynomial)) hx hy
  have hfirst := mul_le_mul ha.2 hpb (abs_nonneg _) hea
  have hsecond := mul_le_mul hb.2 hpa (abs_nonneg _) heb
  have hthird := mul_le_mul ha.2 hb.2 (abs_nonneg _) hea
  let A := evaluate x y a.polynomial
  let B := evaluate x y b.polynomial
  have hid : v*w-evaluate x y (truncate (a.polynomial*b.polynomial))=
      (v-A)*B+(w-B)*A+(v-A)*(w-B)+
        evaluate x y (a.polynomial*b.polynomial-truncate (a.polynomial*b.polynomial)) := by
    dsimp [A,B]
    simp only [map_sub,map_mul]
    ring
  have h1 := abs_add_le ((v-A)*B+(w-B)*A+(v-A)*(w-B))
    (evaluate x y (a.polynomial*b.polynomial-truncate (a.polynomial*b.polynomial)))
  have h2 := abs_add_le ((v-A)*B+(w-B)*A) ((v-A)*(w-B))
  have h3 := abs_add_le ((v-A)*B) ((w-B)*A)
  refine ⟨?_,?_⟩
  · simp only [rawMul]
    have hn1 := TensorPolynomialEnclosure.norm_nonneg
      (a.polynomial*b.polynomial-truncate (a.polynomial*b.polynomial))
    have hna := mul_nonneg ha.1 (TensorPolynomialEnclosure.norm_nonneg b.polynomial)
    have hnb := mul_nonneg hb.1 (TensorPolynomialEnclosure.norm_nonneg a.polynomial)
    have hab := mul_nonneg ha.1 hb.1
    linarith
  · change |v*w-evaluate x y (truncate (a.polynomial*b.polynomial))|≤_
    rw [hid]
    simp only [abs_mul] at h2 h3
    simp only [rawMul]
    push_cast
    dsimp only [A,B] at h1 h2 h3 ⊢
    linarith

theorem contains_mul {a b : Enclosure} {x y v w : ℝ}
    (ha : Contains a x y v) (hb : Contains b x y w) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (mul a b) x y (v*w) :=
  contains_round (contains_rawMul ha hb hx hy) hx hy
theorem contains_scale {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (r : ℚ) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (scale r a) x y ((r:ℝ)*v) :=
  contains_mul (contains_constant r hx hy) ha hx hy
theorem contains_widen {a : Enclosure} {e : ℚ} {x y v w : ℝ}
    (ha : Contains a x y v) (he : 0≤e) (hvw : |w-v|≤(e:ℝ))
    (hx : |x|≤1) (hy : |y|≤1) : Contains (widen a e) x y w :=
  contains_round (TensorPolynomialEnclosure.Contains.widen ha he hvw) hx hy

def power (a : Enclosure) : ℕ → Enclosure
  | 0 => constant 1
  | n+1 => mul (power a n) a
theorem contains_power {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) (n : ℕ) :
    Contains (power a n) x y (v^n) := by
  induction n with
  | zero => simpa [power] using contains_constant 1 hx hy
  | succ n ih => simpa only [power,pow_succ] using contains_mul ih ha hx hy

def sum : (n : ℕ) → (Fin n → Enclosure) → Enclosure
  | 0,_ => constant 0
  | n+1,f => add (sum n (fun i => f i.castSucc)) (f (Fin.last n))
theorem contains_sum {n : ℕ} {a : Fin n→Enclosure} {v : Fin n→ℝ} {x y : ℝ}
    (h : ∀i,Contains (a i) x y (v i)) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (sum n a) x y (∑i,v i) := by
  induction n with
  | zero => simpa [sum] using contains_constant 0 hx hy
  | succ n ih =>
      simpa only [sum,Fin.sum_univ_castSucc] using
        contains_add (ih (fun i => h i.castSucc)) (h (Fin.last n)) hx hy

def sine (a : Enclosure) : Enclosure :=
  widen (sum 7 (fun j => scale ((-1:ℚ)^j.val/(Nat.factorial (2*j.val+1):ℚ))
    (power a (2*j.val+1)))) ((7/10:ℚ)^15/(Nat.factorial 15:ℚ))
def cosine (a : Enclosure) : Enclosure :=
  widen (sum 8 (fun j => scale ((-1:ℚ)^j.val/(Nat.factorial (2*j.val):ℚ))
    (power a (2*j.val)))) ((7/10:ℚ)^16/(Nat.factorial 16:ℚ))

theorem contains_sine {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    (hv : v∈Set.Icc 0 frameCap) : Contains (sine a) x y (Real.sin v) := by
  have hs := contains_sum (fun j : Fin 7 =>
    contains_scale (contains_power ha hx hy (2*j.val+1))
      ((-1:ℚ)^j.val/(Nat.factorial (2*j.val+1):ℚ)) hx hy) hx hy
  have hsum : (∑ i : Fin 7,(((-1:ℚ)^i.val/(Nat.factorial (2*i.val+1):ℚ) : ℚ) : ℝ)*
      v^(2*i.val+1))=HighOrderTaylor.S13 v := by
    exact_mod_cast TensorPolynomialEnclosure.sine_sum v
  rw [hsum] at hs
  apply contains_widen hs (by positivity) ?_ hx hy
  have hlo := HighOrderTaylor.S15_le_sin hv.1
  have hhi := HighOrderTaylor.sin_le_S13 hv.1
  have hp := pow_le_pow_left₀ hv.1 hv.2 15
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  dsimp [HighOrderTaylor.S15,frameCap] at hlo hp
  norm_num
  nlinarith

theorem contains_cosine {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    (hv : v∈Set.Icc 0 frameCap) : Contains (cosine a) x y (Real.cos v) := by
  have hs := contains_sum (fun j : Fin 8 =>
    contains_scale (contains_power ha hx hy (2*j.val))
      ((-1:ℚ)^j.val/(Nat.factorial (2*j.val):ℚ)) hx hy) hx hy
  have hsum : (∑ i : Fin 8,(((-1:ℚ)^i.val/(Nat.factorial (2*i.val):ℚ) : ℚ) : ℝ)*
      v^(2*i.val))=HighOrderTaylor.C14 v := by
    exact_mod_cast TensorPolynomialEnclosure.cosine_sum v
  rw [hsum] at hs
  apply contains_widen hs (by positivity) ?_ hx hy
  have hlo := HighOrderTaylor.C14_le_cos hv.1
  have hhi := HighOrderTaylor.cos_le_C16 hv.1
  have hp := pow_le_pow_left₀ hv.1 hv.2 16
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  dsimp [HighOrderTaylor.C16,frameCap] at hhi hp
  norm_num
  nlinarith

def center (a : Enclosure) : ℚ := (a.polynomial.coeff 0).coeff 0
def floor (a : Enclosure) : ℚ :=
  center a-norm (a.polynomial-scalar (center a))-a.error

theorem lower {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) : (floor a:ℝ)≤v := by
  have h := TensorPolynomialEnclosure.evaluate_abs_le_norm
    (a.polynomial-scalar (center a)) hx hy
  rw [map_sub,evaluate_scalar] at h
  have hp := (abs_le.mp h).1
  have he := (abs_le.mp ha.2).1
  dsimp [floor]
  push_cast
  linarith

end SquaresInCircles.Eight.RoundedTensorEnclosure
