module

public import SquaresInCircles.Eight.TableFree.TensorWholeIntervalPolynomial
public import SquaresInCircles.Eight.TableFree.SepticRadicalUpper

/-!
# Exact rational enclosures with total-degree truncation

Uncompiled source. A discarded monomial is charged to the error by the
sum of the absolute values of its coefficients. Products also retain
the two first-order input errors and their product. Thus each enclosure
holds on the complete square; truncation is never an implicit equality.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.TensorPolynomialEnclosure
open Polynomial TensorWholeIntervalPolynomial

def norm (p : Bivar) : ℚ :=
  ∑ i∈p.support,∑ j∈(p.coeff i).support,|(p.coeff i).coeff j|

def truncate (p : Bivar) : Bivar :=
  ∑ i : Fin 15,∑ j : Fin 15,
    if i.val+j.val≤14 then scalar ((p.coeff i.val).coeff j.val)*X^i.val*(C X)^j.val else 0

theorem norm_nonneg (p : Bivar) : 0≤norm p := by
  unfold norm
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))

theorem evaluate_sum (p : Bivar) (x y : ℝ) :
    evaluate x y p=
      ∑ i∈p.support,∑ j∈(p.coeff i).support,
        ((p.coeff i).coeff j:ℝ)*x^i*y^j := by
  simp only [evaluate,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_eq_sum,Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,Polynomial.aeval_def,
    Polynomial.eval₂_eq_sum,Polynomial.sum_def,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eq_ratCast]
  ring

theorem evaluate_abs_le_norm (p : Bivar) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) : |evaluate x y p|≤(norm p:ℝ) := by
  have hxpow (i : ℕ) : |x^i|≤1 := by
    simpa only [abs_pow,one_pow] using pow_le_pow_left₀ (abs_nonneg x) hx i
  have hypow (j : ℕ) : |y^j|≤1 := by
    simpa only [abs_pow,one_pow] using pow_le_pow_left₀ (abs_nonneg y) hy j
  rw [evaluate_sum]
  calc
    |∑ i∈p.support,∑ j∈(p.coeff i).support,
        ((p.coeff i).coeff j:ℝ)*x^i*y^j| ≤
      ∑ i∈p.support,|∑ j∈(p.coeff i).support,
        ((p.coeff i).coeff j:ℝ)*x^i*y^j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i∈p.support,∑ j∈(p.coeff i).support,
        |((p.coeff i).coeff j:ℝ)*x^i*y^j| := by
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i∈p.support,∑ j∈(p.coeff i).support,|((p.coeff i).coeff j:ℝ)| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul,abs_mul]
      have h1 := mul_le_mul_of_nonneg_left (hxpow i) (abs_nonneg (((p.coeff i).coeff j:ℝ)))
      have h2 := mul_le_mul_of_nonneg_left (hypow j)
        (mul_nonneg (abs_nonneg (((p.coeff i).coeff j:ℝ))) (abs_nonneg (x^i)))
      nlinarith
    _ = (norm p:ℝ) := by simp [norm]

structure Enclosure where
  polynomial : Bivar
  error : ℚ

def constant (a : ℚ) : Enclosure := ⟨scalar a,0⟩
def outerVariable : Enclosure := ⟨X,0⟩
def innerVariable : Enclosure := ⟨C X,0⟩

def add (a b : Enclosure) : Enclosure :=
  ⟨a.polynomial+b.polynomial,a.error+b.error⟩

def neg (a : Enclosure) : Enclosure := ⟨-a.polynomial,a.error⟩
def sub (a b : Enclosure) : Enclosure := add a (neg b)

def mul (a b : Enclosure) : Enclosure :=
  let p := a.polynomial*b.polynomial
  let t := truncate p
  ⟨t,norm (p-t)+a.error*norm b.polynomial+b.error*norm a.polynomial+a.error*b.error⟩

def widen (a : Enclosure) (e : ℚ) : Enclosure := ⟨a.polynomial,a.error+e⟩

def Contains (a : Enclosure) (x y v : ℝ) : Prop :=
  0≤a.error ∧ |v-evaluate x y a.polynomial|≤(a.error:ℝ)

theorem contains_constant (a : ℚ) (x y : ℝ) : Contains (constant a) x y (a:ℝ) := by
  simp [Contains,constant]

theorem contains_outer (x y : ℝ) : Contains outerVariable x y x := by
  simp [Contains,outerVariable]

theorem contains_inner (x y : ℝ) : Contains innerVariable x y y := by
  simp [Contains,innerVariable]

theorem Contains.add {a b : Enclosure} {x y v w : ℝ}
    (ha : Contains a x y v) (hb : Contains b x y w) :
    Contains (add a b) x y (v+w) := by
  refine ⟨add_nonneg ha.1 hb.1,?_⟩
  have ht := abs_add_le (v-evaluate x y a.polynomial) (w-evaluate x y b.polynomial)
  have hid : v+w-evaluate x y (a.polynomial+b.polynomial)=
      (v-evaluate x y a.polynomial)+(w-evaluate x y b.polynomial) := by
    rw [map_add]
    ring
  change |v+w-evaluate x y (a.polynomial+b.polynomial)|≤((a.error+b.error:ℚ):ℝ)
  rw [hid]
  push_cast
  linarith [ha.2,hb.2]

theorem Contains.neg {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) : Contains (neg a) x y (-v) := by
  refine ⟨ha.1,?_⟩
  change |-v-evaluate x y (-a.polynomial)|≤(a.error:ℝ)
  rw [map_neg,show -v- -evaluate x y a.polynomial=-(v-evaluate x y a.polynomial) by ring,abs_neg]
  exact ha.2

theorem Contains.sub {a b : Enclosure} {x y v w : ℝ}
    (ha : Contains a x y v) (hb : Contains b x y w) :
    Contains (sub a b) x y (v-w) := by
  change Contains (TensorPolynomialEnclosure.add a (TensorPolynomialEnclosure.neg b)) x y (v-w)
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

theorem Contains.value_bound {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) :
    |v|≤(norm a.polynomial:ℝ)+(a.error:ℝ) := by
  have ht := abs_add_le (v-evaluate x y a.polynomial) (evaluate x y a.polynomial)
  have hn := evaluate_abs_le_norm a.polynomial hx hy
  simp only [sub_add_cancel] at ht
  linarith [ha.2]

theorem Contains.mul {a b : Enclosure} {x y v w : ℝ}
    (ha : Contains a x y v) (hb : Contains b x y w)
    (hx : |x|≤1) (hy : |y|≤1) : Contains (mul a b) x y (v*w) := by
  have hea : (0:ℝ)≤(a.error:ℝ) := by exact_mod_cast ha.1
  have heb : (0:ℝ)≤(b.error:ℝ) := by exact_mod_cast hb.1
  have hna : (0:ℝ)≤(norm a.polynomial:ℝ) := by exact_mod_cast norm_nonneg a.polynomial
  have hnb : (0:ℝ)≤(norm b.polynomial:ℝ) := by exact_mod_cast norm_nonneg b.polynomial
  have hpa := evaluate_abs_le_norm a.polynomial hx hy
  have hpb := evaluate_abs_le_norm b.polynomial hx hy
  have htail := evaluate_abs_le_norm
    (a.polynomial*b.polynomial-truncate (a.polynomial*b.polynomial)) hx hy
  have hfirst := mul_le_mul ha.2 hpb (abs_nonneg _) hea
  have hsecond := mul_le_mul hb.2 hpa (abs_nonneg _) heb
  have hthird := mul_le_mul ha.2 hb.2 (abs_nonneg _) hea
  have hidentity : v*w-evaluate x y (truncate (a.polynomial*b.polynomial))=
      (v-evaluate x y a.polynomial)*evaluate x y b.polynomial+
        (w-evaluate x y b.polynomial)*evaluate x y a.polynomial+
        (v-evaluate x y a.polynomial)*(w-evaluate x y b.polynomial)+
        evaluate x y (a.polynomial*b.polynomial-truncate (a.polynomial*b.polynomial)) := by
    simp only [map_sub,map_mul]
    ring
  have h1 := abs_add_le ((v-evaluate x y a.polynomial)*evaluate x y b.polynomial+
        (w-evaluate x y b.polynomial)*evaluate x y a.polynomial+
        (v-evaluate x y a.polynomial)*(w-evaluate x y b.polynomial))
    (evaluate x y (a.polynomial*b.polynomial-truncate (a.polynomial*b.polynomial)))
  have h2 := abs_add_le ((v-evaluate x y a.polynomial)*evaluate x y b.polynomial+
        (w-evaluate x y b.polynomial)*evaluate x y a.polynomial)
    ((v-evaluate x y a.polynomial)*(w-evaluate x y b.polynomial))
  have h3 := abs_add_le ((v-evaluate x y a.polynomial)*evaluate x y b.polynomial)
    ((w-evaluate x y b.polynomial)*evaluate x y a.polynomial)
  simp only [abs_mul] at h2 h3
  refine ⟨?_,?_⟩
  · exact add_nonneg
      (add_nonneg
        (add_nonneg (norm_nonneg _)
          (mul_nonneg ha.1 (norm_nonneg b.polynomial)))
        (mul_nonneg hb.1 (norm_nonneg a.polynomial)))
      (mul_nonneg ha.1 hb.1)
  · change |v*w-evaluate x y (truncate (a.polynomial*b.polynomial))|≤
      ((norm (a.polynomial*b.polynomial-truncate (a.polynomial*b.polynomial))+
        a.error*norm b.polynomial+b.error*norm a.polynomial+a.error*b.error:ℚ):ℝ)
    rw [hidentity]
    push_cast
    linarith

theorem Contains.widen {a : Enclosure} {e : ℚ} {x y v w : ℝ}
    (ha : Contains a x y v) (he : 0≤e) (hvw : |w-v|≤(e:ℝ)) :
    Contains (widen a e) x y w := by
  refine ⟨add_nonneg ha.1 he,?_⟩
  have ht := abs_add_le (w-v) (v-evaluate x y a.polynomial)
  have hid : (w-v)+(v-evaluate x y a.polynomial)=w-evaluate x y a.polynomial := by ring
  rw [hid] at ht
  change |w-evaluate x y a.polynomial|≤((a.error+e:ℚ):ℝ)
  push_cast
  linarith [ha.2]

/-- Binary exponentiation, exactly as in the rational recipe. -/
def power (a : Enclosure) (n : ℕ) : Enclosure :=
  if n=0 then constant 1 else
    let b := power a (n/2)
    let c := mul b b
    if n%2=0 then c else mul c a
termination_by n
decreasing_by omega

theorem Contains.power {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) (n : ℕ) :
    Contains (power a n) x y (v^n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n=0
    · subst n
      rw [TensorPolynomialEnclosure.power]
      simpa using contains_constant 1 x y
    · have hhalf : n/2<n := by omega
      have hh := ih (n/2) hhalf
      have hs := hh.mul hh hx hy
      rw [TensorPolynomialEnclosure.power]
      simp only [hn,↓reduceIte]
      by_cases he : n%2=0
      · have heq : v^n=v^(n/2)*v^(n/2) := by
          rw [← pow_add]
          congr 1
          omega
        simp only [he,↓reduceIte,heq]
        exact hs
      · have heq : v^n=(v^(n/2)*v^(n/2))*v := by
          rw [← pow_add,← pow_succ]
          congr 1
          omega
        simp only [he,↓reduceIte,heq]
        exact hs.mul ha hx hy

def sum {ι : Type*} [Fintype ι] (f : ι → Enclosure) : Enclosure :=
  ⟨∑ i,(f i).polynomial,∑ i,(f i).error⟩

theorem contains_sum {ι : Type*} [Fintype ι] {f : ι → Enclosure} {g : ι → ℝ} {x y : ℝ}
    (h : ∀ i,Contains (f i) x y (g i)) : Contains (sum f) x y (∑ i,g i) := by
  refine ⟨Finset.sum_nonneg (fun i _ => (h i).1),?_⟩
  have ht := Finset.abs_sum_le_sum_abs (fun i => g i-evaluate x y (f i).polynomial) Finset.univ
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h i).2)
  simpa only [sum,map_sum,← Finset.sum_sub_distrib,Rat.cast_sum] using ht.trans hb

def sine (a : Enclosure) : Enclosure :=
  widen (sum (fun j : Fin 7 =>
    mul (constant ((-1:ℚ)^j.val/(Nat.factorial (2*j.val+1):ℚ))) (power a (2*j.val+1))))
    ((7/10:ℚ)^15/(Nat.factorial 15:ℚ))

def cosine (a : Enclosure) : Enclosure :=
  widen (sum (fun j : Fin 8 =>
    mul (constant ((-1:ℚ)^j.val/(Nat.factorial (2*j.val):ℚ))) (power a (2*j.val))))
    ((7/10:ℚ)^16/(Nat.factorial 16:ℚ))

theorem sine_sum (v : ℝ) :
    (∑ j : Fin 7,((-1:ℚ)^j.val/(Nat.factorial (2*j.val+1):ℚ):ℝ)*v^(2*j.val+1))=
      HighOrderTaylor.S13 v := by
  norm_num [Fin.sum_univ_succ,HighOrderTaylor.S13,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7]
  ring

theorem cosine_sum (v : ℝ) :
    (∑ j : Fin 8,((-1:ℚ)^j.val/(Nat.factorial (2*j.val):ℚ):ℝ)*v^(2*j.val))=
      HighOrderTaylor.C14 v := by
  norm_num [Fin.sum_univ_succ,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.cos10,Arithmetic.cos8]
  ring

theorem Contains.sine {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    (hv : v∈Set.Icc 0 frameCap) : Contains (sine a) x y (Real.sin v) := by
  have hs := contains_sum (fun j : Fin 7 =>
    (contains_constant ((-1:ℚ)^j.val/(Nat.factorial (2*j.val+1):ℚ)) x y).mul
      (ha.power hx hy (2*j.val+1)) hx hy)
  simp only [Rat.cast_div,Rat.cast_pow] at hs
  rw [sine_sum] at hs
  apply hs.widen (by positivity)
  have hlo := HighOrderTaylor.S15_le_sin hv.1
  have hhi := HighOrderTaylor.sin_le_S13 hv.1
  have hp := pow_le_pow_left₀ hv.1 hv.2 15
  rw [abs_of_nonpos (sub_nonpos.mpr hhi)]
  dsimp [HighOrderTaylor.S15,frameCap] at hlo hp
  norm_num
  linarith

theorem Contains.cosine {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    (hv : v∈Set.Icc 0 frameCap) : Contains (cosine a) x y (Real.cos v) := by
  have hs := contains_sum (fun j : Fin 8 =>
    (contains_constant ((-1:ℚ)^j.val/(Nat.factorial (2*j.val):ℚ)) x y).mul
      (ha.power hx hy (2*j.val)) hx hy)
  simp only [Rat.cast_div,Rat.cast_pow] at hs
  rw [cosine_sum] at hs
  apply hs.widen (by positivity)
  have hlo := HighOrderTaylor.C14_le_cos hv.1
  have hhi := HighOrderTaylor.cos_le_C16 hv.1
  have hp := pow_le_pow_left₀ hv.1 hv.2 16
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  dsimp [HighOrderTaylor.C16,frameCap] at hhi hp
  norm_num
  linarith

def h7 (a : Enclosure) : Enclosure :=
  add (constant 1) (mul a (add (constant (1/2)) (mul a
    (add (constant (-1/8)) (mul a (add (constant (1/16)) (mul a
      (add (constant (-5/128)) (mul a (add (constant (7/256)) (mul a
        (add (constant (-21/1024)) (mul a (constant (33/2048)))))))))))))))

theorem Contains.h7 {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (h7 a) x y (SepticRadicalUpper.H7 v) := by
  have hc (r : ℚ) := contains_constant r x y
  have h1 := ha.mul (hc (33/2048)) hx hy
  have h2 := ha.mul ((hc (-21/1024)).add h1) hx hy
  have h3 := ha.mul ((hc (7/256)).add h2) hx hy
  have h4 := ha.mul ((hc (-5/128)).add h3) hx hy
  have h5 := ha.mul ((hc (1/16)).add h4) hx hy
  have h6 := ha.mul ((hc (-1/8)).add h5) hx hy
  have hlast := ha.mul ((hc (1/2)).add h6) hx hy
  simpa [TensorPolynomialEnclosure.h7,SepticRadicalUpper.H7] using (hc 1).add hlast

/-- Rounded to the nearest multiple of 10^-8 using integer square root
and an exact rational midpoint comparison. -/
def nearestRoot (r : ℚ) : ℚ :=
  let n := Nat.sqrt ((r.num.natAbs*10000000000000000)/r.den)
  let m := if (r*10000000000000000)<((n:ℚ)+1/2)^2 then n else n+1
  (m:ℚ)/100000000

def rootSeed (a : Enclosure) : ℚ := nearestRoot ((a.polynomial.coeff 0).coeff 0)

def sqrtUpper (a : Enclosure) : Enclosure :=
  let ρ := rootSeed a
  mul (constant ρ)
    (h7 (mul (sub a (constant (ρ^2))) (constant (1/ρ^2))))

theorem Contains.sqrtUpper_model {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (sqrtUpper a) x y
      ((rootSeed a:ℝ)*SepticRadicalUpper.H7
        ((v-(rootSeed a:ℝ)^2)/(rootSeed a:ℝ)^2)) := by
  have hc (r : ℚ) := contains_constant r x y
  have hs := (ha.sub (hc ((rootSeed a)^2))).mul (hc (1/(rootSeed a)^2)) hx hy
  have hh := hs.h7 hx hy
  have hf := (hc (rootSeed a)).mul hh hx hy
  simpa [sqrtUpper,div_eq_mul_inv] using hf

theorem Contains.sqrt_upper {a : Enclosure} {x y v : ℝ}
    (ha : Contains a x y v) (hx : |x|≤1) (hy : |y|≤1)
    (hv : 0≤v) (hρ : 0<rootSeed a) :
    Real.sqrt v≤evaluate x y (sqrtUpper a).polynomial+((sqrtUpper a).error:ℝ) := by
  have hρ' : (0:ℝ)<(rootSeed a:ℝ) := by exact_mod_cast hρ
  have hu := SepticRadicalUpper.sqrt_upper hv hρ'
  have he := abs_le.mp (ha.sqrtUpper_model hx hy).2
  linarith

/-- A finite arithmetic expression retains the same evaluation order in
the real formula and in the rational enclosure. -/
inductive Expression (ι : Type*) where
  | literal (r : ℚ)
  | variable (i : ι)
  | add (a b : Expression ι)
  | neg (a : Expression ι)
  | mul (a b : Expression ι)
  | power (a : Expression ι) (n : ℕ)

namespace Expression

instance {ι : Type*} : Add (Expression ι) := ⟨.add⟩
instance {ι : Type*} : Neg (Expression ι) := ⟨.neg⟩
instance {ι : Type*} : Sub (Expression ι) := ⟨fun a b => .add a (.neg b)⟩
instance {ι : Type*} : Mul (Expression ι) := ⟨.mul⟩
instance {ι : Type*} : Pow (Expression ι) ℕ := ⟨.power⟩
instance {ι : Type*} (n : ℕ) : OfNat (Expression ι) n := ⟨.literal n⟩

def value {ι : Type*} (v : ι → ℝ) : Expression ι → ℝ
  | .literal r => r
  | .variable i => v i
  | .add a b => value v a+value v b
  | .neg a => -value v a
  | .mul a b => value v a*value v b
  | .power a n => value v a^n

def enclose {ι : Type*} (v : ι → Enclosure) : Expression ι → Enclosure
  | .literal r => constant r
  | .variable i => v i
  | .add a b => TensorPolynomialEnclosure.add (enclose v a) (enclose v b)
  | .neg a => TensorPolynomialEnclosure.neg (enclose v a)
  | .mul a b => TensorPolynomialEnclosure.mul (enclose v a) (enclose v b)
  | .power a n => TensorPolynomialEnclosure.power (enclose v a) n

theorem contains {ι : Type*} (e : Expression ι) {v : ι → ℝ} {w : ι → Enclosure} {x y : ℝ}
    (hw : ∀ i,Contains (w i) x y (v i)) (hx : |x|≤1) (hy : |y|≤1) :
    Contains (enclose w e) x y (value v e) := by
  induction e with
  | literal r => exact contains_constant r x y
  | «variable» i => exact hw i
  | add a b ha hb => exact ha.add hb
  | neg a ha => exact ha.neg
  | mul a b ha hb => exact ha.mul hb hx hy
  | power a n ha => exact ha.power hx hy n

def H7 {ι : Type*} (a : Expression ι) : Expression ι :=
  1+a*(.literal (1/2)+a*(.literal (-1/8)+a*(.literal (1/16)+a*(.literal (-5/128)+
    a*(.literal (7/256)+a*(.literal (-21/1024)+a*.literal (33/2048)))))))

def sqrtUpper {ι : Type*} (w : ι → Enclosure) (a : Expression ι) : Expression ι :=
  let ρ := rootSeed (enclose w a)
  .literal ρ*H7 ((a-.literal (ρ^2))*.literal (1/ρ^2))

theorem H7_value {ι : Type*} (v : ι → ℝ) (a : Expression ι) :
    value v (H7 a)=SepticRadicalUpper.H7 (value v a) := by
  simp [H7,value,SepticRadicalUpper.H7]

theorem sqrtUpper_value {ι : Type*} (v : ι → ℝ) (w : ι → Enclosure) (a : Expression ι) :
    value v (sqrtUpper w a)=
      (rootSeed (enclose w a):ℝ)*SepticRadicalUpper.H7
        ((value v a-(rootSeed (enclose w a):ℝ)^2)/(rootSeed (enclose w a):ℝ)^2) := by
  have hsub : ∀ b c : Expression ι,value v (b-c)=value v b-value v c := fun b c => by
    show value v b+-value v c=_
    ring
  simp [sqrtUpper,value,H7_value,hsub,div_eq_mul_inv]

theorem sqrt_le_value {ι : Type*} (v : ι → ℝ) (w : ι → Enclosure) (a : Expression ι)
    (ha : 0≤value v a) (hρ : 0<rootSeed (enclose w a)) :
    Real.sqrt (value v a)≤value v (sqrtUpper w a) := by
  rw [sqrtUpper_value]
  exact SepticRadicalUpper.sqrt_upper ha (by exact_mod_cast hρ)

end Expression

end SquaresInCircles.Eight.TableFree.TensorPolynomialEnclosure
