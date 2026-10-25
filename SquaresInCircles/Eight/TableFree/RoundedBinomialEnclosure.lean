module

public import SquaresInCircles.Eight.TableFree.RoundedTensorEnclosure
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The three binomial operations in the degree-ten derivative certificate

Uncompiled transcription of equations (40)--(42) of the critical positive-T
hand proof. The input is normalized about its rounded rational centre.
All three binomial tails are bounded by the first omitted coefficient
times s^13/(1-s), because their absolute coefficients decrease from
index thirteen. Horner evaluation uses the rounded primitive arithmetic.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.RoundedBinomialEnclosure
open Polynomial TensorWholeIntervalPolynomial RoundedTensorEnclosure

inductive Exponent where
  | root | inverseRoot | inverse
  deriving DecidableEq

instance : Fintype Exponent where
  elems := {.root, .inverseRoot, .inverse}
  complete x := by cases x <;> decide

def exponent : Exponent→ℚ
  | .root => 1/2
  | .inverseRoot => -1/2
  | .inverse => -1
def value : Exponent→ℝ→ℝ
  | .root,v => Real.sqrt v
  | .inverseRoot,v => 1/Real.sqrt v
  | .inverse,v => 1/v

def coefficient (e : Exponent) : ℕ→ℚ
  | 0 => 1
  | n+1 => coefficient e n*(exponent e-n)/(n+1)

theorem coefficient_choose (e : Exponent) (n : ℕ) :
    coefficient e n=Ring.choose (exponent e) n := by
  induction n with
  | zero => simp [coefficient,Ring.choose_zero_right]
  | succ n ih =>
      have h := Ring.choose_smul_choose (exponent e) (n := n+1) (k := n) (Nat.le_succ n)
      simp only [Nat.choose_succ_self_right,Nat.add_sub_cancel_left,
        Ring.choose_one_right,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at h
      rw [coefficient,ih]
      apply (div_eq_iff (by positivity : (n+1:ℚ)≠0)).2
      nlinarith [h]

theorem coefficient_cast (e : Exponent) (n : ℕ) :
    (coefficient e n:ℝ)=Ring.choose (exponent e:ℝ) n := by
  rw [coefficient_choose]
  exact Ring.map_choose (algebraMap ℚ ℝ) (exponent e) n

theorem coefficient_abs_step (e : Exponent) {n : ℕ} (hn : 13≤n) :
    |coefficient e (n+1)|≤|coefficient e n| := by
  have hn' : (13:ℚ)≤n := by exact_mod_cast hn
  have hr : |exponent e-(n:ℚ)|≤n+1 := by
    cases e <;> norm_num [exponent] <;>
      rw [abs_of_nonpos (by linarith)] <;> linarith
  rw [coefficient,abs_div,abs_mul,abs_of_pos (by positivity : (0:ℚ)<n+1)]
  exact (div_le_iff₀ (by positivity : (0:ℚ)<n+1)).2
    (mul_le_mul_of_nonneg_left hr (abs_nonneg _))

theorem coefficient_tail (e : Exponent) (n : ℕ) :
    |coefficient e (n+13)|≤|coefficient e 13| := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := coefficient_abs_step e (n := n+13) (by omega)
      simpa only [Nat.succ_add] using h.trans ih

theorem binomial_hasSum (e : Exponent) {v : ℝ} (hv : |v|<1) :
    HasSum (fun n => (coefficient e n:ℝ)*v^n) ((1+v)^(exponent e:ℝ)) := by
  have hm : v∈Metric.eball (0:ℝ) 1 := by
    simpa only [Metric.mem_eball,edist_dist,Real.dist_eq,sub_zero,
      ENNReal.ofReal_lt_one] using hv
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := (exponent e:ℝ))).hasSum hm
  simpa only [binomialSeries_apply,List.ofFn_const,List.prod_replicate,
    smul_eq_mul,zero_add,coefficient_cast] using h

def realHorner (v : ℝ) : List ℚ→ℝ
  | [] => 0
  | c::cs => (c:ℝ)+v*realHorner v cs
def coefficients (e : Exponent) : List ℚ :=
  List.ofFn (fun i : Fin 13 => coefficient e i.val)

private theorem r29_realHorner_ofFn : ∀ (n : ℕ) (f : ℕ → ℚ) (v : ℝ),
    realHorner v (List.ofFn (fun i : Fin n => f i.val))=
      ∑ i ∈ Finset.range n,(f i:ℝ)*v^i
  | 0,f,v => by simp [realHorner]
  | n+1,f,v => by
    rw [List.ofFn_succ]
    simp only [realHorner,Fin.val_zero,Fin.val_succ]
    rw [r29_realHorner_ofFn n (fun i => f (i+1)) v,Finset.sum_range_succ',Finset.mul_sum]
    simp only [pow_zero,mul_one]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)

theorem horner_sum (e : Exponent) (v : ℝ) :
    realHorner v (coefficients e)=
      ∑i∈Finset.range 13,(coefficient e i:ℝ)*v^i :=
  r29_realHorner_ofFn 13 (coefficient e) v

theorem binomial_remainder (e : Exponent) {v s : ℝ}
    (hs : 0≤ s) (hsmall : s<1) (hv : |v|≤ s) :
    |(1+v)^(exponent e:ℝ)-realHorner v (coefficients e)|≤
      |(coefficient e 13:ℝ)| *s^13/(1-s) := by
  have hsum := binomial_hasSum e (hv.trans_lt hsmall)
  have htail := (hasSum_nat_add_iff' 13).2 hsum
  have hgeom := (hasSum_geometric_of_lt_one hs hsmall).mul_left
    (|(coefficient e 13:ℝ)| *s^13)
  have hbound (n : ℕ) :
      ‖(coefficient e (n+13):ℝ)*v^(n+13)‖≤
        (|(coefficient e 13:ℝ)| *s^13)*s^n := by
    have hc : |(coefficient e (n+13):ℝ)|≤|(coefficient e 13:ℝ)| := by
      exact_mod_cast coefficient_tail e n
    have hp : |v^(n+13)| ≤ s^(n+13) := by
      simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg v) hv (n+13)
    have h := mul_le_mul hc hp (abs_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs,abs_mul]
    refine h.trans_eq ?_
    ring
  have h := htail.norm_le_of_bounded hgeom hbound
  rw [horner_sum]
  simpa only [Real.norm_eq_abs,div_eq_mul_inv,mul_assoc] using h

def horner (a : Enclosure) : List ℚ→Enclosure
  | [] => constant 0
  | c::cs => RoundedTensorEnclosure.add (constant c) (mul a (horner a cs))

theorem contains_horner {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) (cs : List ℚ) :
    Contains (horner a cs) x y (realHorner v cs) := by
  induction cs with
  | nil => simpa [horner,realHorner] using contains_constant 0 hx hy
  | cons c cs ih =>
      exact contains_add (contains_constant c hx hy) (contains_mul ha ih hx hy) hx hy

/-- The exact rational midpoint test rounds sqrt(r) to 10^-10. -/
def nearestRoot (r : ℚ) : ℚ :=
  let n := Nat.sqrt ((r.num.natAbs*10^20)/r.den)
  let m := if r*10^20<((n:ℚ)+1/2)^2 then n else n+1
  (m:ℚ)/10^10
def seed (a : Enclosure) : ℚ := nearestRoot (center a)
def base (a : Enclosure) : Exponent→ℚ
  | .root | .inverseRoot => seed a^2
  | .inverse => center a
def factor (a : Enclosure) : Exponent→ℚ
  | .root => seed a
  | .inverseRoot => 1/seed a
  | .inverse => 1/center a
def normalized (a : Enclosure) (e : Exponent) : Enclosure :=
  RoundedTensorEnclosure.sub (RoundedTensorEnclosure.scale (1/base a e) a) (constant 1)
def span (a : Enclosure) (e : Exponent) : ℚ :=
  norm (normalized a e).polynomial+(normalized a e).error
def tail (a : Enclosure) (e : Exponent) : ℚ :=
  |coefficient e 13| *(span a e)^13/(1-span a e)
def enclose (a : Enclosure) (e : Exponent) : Enclosure :=
  RoundedTensorEnclosure.scale (factor a e)
    (widen (horner (normalized a e) (coefficients e)) (tail a e))

def Valid (a : Enclosure) (e : Exponent) : Prop :=
  0<seed a ∧ 0<base a e ∧ span a e<19/200

theorem normalized_contains {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) (e : Exponent) :
    Contains (normalized a e) x y (v/(base a e:ℝ)-1) := by
  have h := contains_sub (contains_scale ha (1/base a e) hx hy)
    (contains_constant 1 hx hy) hx hy
  simpa [normalized,div_eq_mul_inv,mul_comm] using h

theorem normalized_abs {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) (e : Exponent) :
    |v/(base a e:ℝ)-1|≤(span a e:ℝ) := by
  have hn := normalized_contains ha hx hy e
  have hp := TensorPolynomialEnclosure.evaluate_abs_le_norm
    (normalized a e).polynomial hx hy
  have h := abs_add_le
    (v/(base a e:ℝ)-1-evaluate x y (normalized a e).polynomial)
    (evaluate x y (normalized a e).polynomial)
  have he : v/(base a e:ℝ)-1-evaluate x y (normalized a e).polynomial+
      evaluate x y (normalized a e).polynomial=v/(base a e:ℝ)-1 := by ring
  rw [he] at h
  dsimp [span]
  push_cast
  linarith [hn.2]

theorem positive {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    {e : Exponent} (hv : Valid a e) : 0<v := by
  have hb : (0:ℝ)<(base a e:ℝ) := by exact_mod_cast hv.2.1
  have hs : (span a e:ℝ)<19/200 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hv.2.2
    rwa [Rat.cast_div,Rat.cast_ofNat,Rat.cast_ofNat] at h
  have h := (abs_le.mp (normalized_abs ha hx hy e)).1
  have hdiv : 0<v/(base a e:ℝ) := by linarith
  exact (div_pos_iff.mp hdiv).resolve_right (by intro h; linarith [h.2]) |>.1

theorem factor_rpow {a : Enclosure} {e : Exponent} (hv : Valid a e) :
    (factor a e:ℝ)=(base a e:ℝ)^(exponent e:ℝ) := by
  have hρ : (0:ℝ)<(seed a:ℝ) := by exact_mod_cast hv.1
  have hb : (0:ℝ)<(base a e:ℝ) := by exact_mod_cast hv.2.1
  cases e
  · simp only [factor,base,exponent,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow]
    rw [← Real.sqrt_eq_rpow,Real.sqrt_sq_eq_abs,abs_of_pos hρ]
  · simp only [factor,base,exponent,Rat.cast_div,Rat.cast_neg,Rat.cast_one,
      Rat.cast_ofNat,Rat.cast_pow]
    rw [show (-1:ℝ)/2= -(1/2:ℝ) by ring,Real.rpow_neg (sq_nonneg _),
      ← Real.sqrt_eq_rpow,Real.sqrt_sq_eq_abs,abs_of_pos hρ,one_div]
  · simp [factor,base,exponent,Real.rpow_neg_one]

theorem value_rpow (e : Exponent) {v : ℝ} (hv : 0<v) :
    value e v=v^(exponent e:ℝ) := by
  cases e
  · simp [value,exponent,Real.sqrt_eq_rpow]
  · simp only [value,exponent,Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat]
    rw [show (-1:ℝ)/2= -(1/2:ℝ) by ring,Real.rpow_neg hv.le,← Real.sqrt_eq_rpow,one_div]
  · simp [value,exponent,Real.rpow_neg_one]

theorem contains_enclose {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    (e : Exponent) (hv : Valid a e) : Contains (enclose a e) x y (value e v) := by
  have hn := normalized_contains ha hx hy e
  have hs0 : 0 ≤ span a e :=
    add_nonneg (TensorPolynomialEnclosure.norm_nonneg _) hn.1
  have hs : span a e<1 := by linarith [hv.2.2]
  have hs0' : (0:ℝ)≤(span a e:ℝ) := by exact_mod_cast hs0
  have hs' : (span a e:ℝ)<1 := by exact_mod_cast hs
  have ht := binomial_remainder e hs0' hs' (normalized_abs ha hx hy e)
  have hh := contains_horner hn hx hy (coefficients e)
  have htail : 0≤tail a e := by
    dsimp [tail]
    exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hs0 _)) (by linarith)
  have hw := contains_widen hh htail (by simpa [tail] using ht) hx hy
  have hp := contains_scale hw (factor a e) hx hy
  have hb : (0:ℝ)<(base a e:ℝ) := by exact_mod_cast hv.2.1
  have hpos := positive ha hx hy hv
  have he : (factor a e:ℝ)*(v/(base a e:ℝ))^(exponent e:ℝ)=value e v := by
    rw [factor_rpow hv,value_rpow e hpos]
    rw [← Real.mul_rpow hb.le (div_pos hpos hb).le]
    congr 1
    field_simp [hb.ne']
  simpa only [enclose,he] using hp

end SquaresInCircles.Eight.TableFree.RoundedBinomialEnclosure
