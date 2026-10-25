module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTScalarModel
public import SquaresInCircles.Eight.Arithmetic.PackedModels
public import SquaresInCircles.Eight.Owners.Tensor.WholeIntervalBernstein

/-!
# Eight squares: whole-square scalar formulas for an unaligned E contact and positive T

Each
of the four intrinsic intervals is mapped to one complete square, with
z=t(1+Y)/2. The additional H choice is precisely the p charge required by
the unaligned actual EH witness. All roots use the displayed septic
majorant and the same total-degree-14 arithmetic as the hand proof.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTPolynomials
open Polynomial TensorWholeIntervalPolynomial

/-! ### Bernstein re-expansion of polynomials of bounded degree

A polynomial of degree at most `D` in each variable equals its degree-`D` tensor Bernstein
re-expansion; every enclosure polynomial has degree at most 14 in each variable. -/

/-- `scalar` as a ring homomorphism. -/
def r54σ : ℚ →+* Bivar := (Polynomial.C : ℚ[X] →+* Bivar).comp Polynomial.C

theorem r54_scalar_eq (r : ℚ) : scalar r=r54σ r := rfl

/-- `U^k` in the degree-`D` Bernstein basis. -/
theorem r54_pow_eq (U : Bivar) {D k : ℕ} (hk : k≤D) :
    (∑ i ∈ Finset.range (D+1),if k ≤ i then
        scalar ((i.choose k:ℚ)/(D.choose k:ℚ)*(D.choose i:ℚ))*U^i*(1-U)^(D-i) else 0)=U^k := by
  rw [← Finset.sum_range_add_sum_Ico _ (show k≤D+1 by omega)]
  rw [Finset.sum_eq_zero (fun i hi => ite_eq_right (by simp at hi; omega)),zero_add]
  rw [Finset.sum_Ico_eq_sum_range]
  have hD : (D.choose k:ℚ)≠0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h : ∀ m ∈ Finset.range (D+1-k),(if k ≤ k+m then
      scalar (((k+m).choose k:ℚ)/(D.choose k:ℚ)*(D.choose (k+m):ℚ))*U^(k+m)*(1-U)^(D-(k+m))
      else 0)=U^k*(U^m*(1-U)^(D-k-m)*((D-k).choose m:Bivar)) := by
    intro m hm
    simp only [Finset.mem_range] at hm
    rw [ite_eq_left (by omega)]
    have h1 := Nat.choose_mul (n := D) (k := k+m) (s := k) (by omega)
    have hc : ((k+m).choose k:ℚ)/(D.choose k:ℚ)*(D.choose (k+m):ℚ)=((D-k).choose m:ℚ) := by
      rw [div_mul_eq_mul_div,div_eq_iff hD]
      have h2 := congrArg (fun n : ℕ => (n:ℚ)) h1
      simp only [Nat.cast_mul,Nat.add_sub_cancel_left] at h2
      linarith
    rw [hc,r54_scalar_eq,map_natCast,pow_add,show D-(k+m)=D-k-m by omega]
    ring
  rw [Finset.sum_congr rfl h,← Finset.mul_sum]
  have hp := add_pow U (1-U) (D-k)
  rw [add_sub_cancel,one_pow,show D-k+1=D+1-k by omega] at hp
  rw [← hp,mul_one]


theorem r54_scalar_zero : scalar 0=0 := by simp [scalar]

theorem r54_sum_range_ext {M : Type*} [AddCommMonoid M] (f : ℕ → M) {i D : ℕ} (hi : i≤D) :
    (∑ k ∈ Finset.range (i+1),f k)=∑ k ∈ Finset.range (D+1),if k ≤ i then f k else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_range,Finset.mem_filter]
  omega

theorem r54_scalar_half : scalar (1/2)*2=1 := by
  rw [r54_scalar_eq,show (2:Bivar)=r54σ 2 from (map_ofNat r54σ 2).symm,← map_mul]
  norm_num

/-- A polynomial of degree at most `D` in each variable. -/
def r54Bounded (D : ℕ) (p : Bivar) : Prop := ∀ a b,(p.coeff a).coeff b≠0 → a≤D ∧ b≤D

theorem r54_eq_sum {D : ℕ} {p : Bivar} (hp : r54Bounded D p) :
    p=∑ a ∈ Finset.range (D+1),∑ b ∈ Finset.range (D+1),
      scalar ((p.coeff a).coeff b)*X^a*(C X)^b := by
  have hdeg : p.natDegree<D+1 := by
    rw [Nat.lt_succ_iff,Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro a ha
    ext b
    by_contra h
    have := (hp a b h).1
    exact absurd ha (not_lt.mpr (by exact_mod_cast this))
  conv_lhs => rw [p.as_sum_range' (D+1) hdeg]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hdeg' : (p.coeff a).natDegree<D+1 := by
    rw [Nat.lt_succ_iff,Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro b hb
    by_contra h
    have := (hp a b h).2
    exact absurd hb (not_lt.mpr (by exact_mod_cast this))
  rw [← C_mul_X_pow_eq_monomial]
  conv_lhs => rw [(p.coeff a).as_sum_range' (D+1) hdeg']
  rw [map_sum,Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow,r54_scalar_eq]
  simp only [r54σ,RingHom.coe_comp,Function.comp_apply]
  ring


theorem r54_swap4 {M : Type*} [AddCommMonoid M] (s t u v : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → M) :
    (∑ k ∈ s,∑ l ∈ t,∑ a ∈ u,∑ b ∈ v,F k l a b)=∑ a ∈ u,∑ b ∈ v,∑ k ∈ s,∑ l ∈ t,F k l a b := by
  calc _ = ∑ k ∈ s,∑ a ∈ u,∑ l ∈ t,∑ b ∈ v,F k l a b :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ a ∈ u,∑ k ∈ s,∑ l ∈ t,∑ b ∈ v,F k l a b := Finset.sum_comm
    _ = ∑ a ∈ u,∑ k ∈ s,∑ b ∈ v,∑ l ∈ t,F k l a b :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

/-- The binomial expansion of `(2u-1)^a`, written over `range (D+1)`. -/
theorem r54_binomial (U : Bivar) {a D : ℕ} (ha : a≤D) :
    (∑ k ∈ Finset.range (D+1),
      scalar (if k ≤ a then 2^k*(-1)^(a-k)*(a.choose k:ℚ) else 0)*U^k)=(2*U-1)^a := by
  have h := add_pow (2*U) (-1) a
  rw [← sub_eq_add_neg] at h
  rw [h,r54_sum_range_ext _ ha]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with hk
  · rw [r54_scalar_eq,map_mul,map_mul,map_pow,map_pow,map_neg,map_one,map_natCast,
      show r54σ 2=2 from map_ofNat r54σ 2]
    ring
  · rw [r54_scalar_eq,map_zero,zero_mul]

theorem r54_left : 2*TensorWholeIntervalBernstein.left-1=X := by
  unfold TensorWholeIntervalBernstein.left
  linear_combination (X+1)*r54_scalar_half

theorem r54_right : 2*TensorWholeIntervalBernstein.right-1=C X := by
  unfold TensorWholeIntervalBernstein.right
  linear_combination (C X+1)*r54_scalar_half

theorem r54_shifted_sum {D : ℕ} {p : Bivar} (hp : r54Bounded D p) :
    (∑ k ∈ Finset.range (D+1),∑ l ∈ Finset.range (D+1),
      scalar (TensorWholeIntervalBernstein.shiftedCoefficient D p k l)*
        TensorWholeIntervalBernstein.left^k*TensorWholeIntervalBernstein.right^l)=p := by
  set L := TensorWholeIntervalBernstein.left
  set R := TensorWholeIntervalBernstein.right
  have key : ∀ k l,scalar (TensorWholeIntervalBernstein.shiftedCoefficient D p k l)*L^k*R^l=
      ∑ a ∈ Finset.range (D+1),∑ b ∈ Finset.range (D+1),
        scalar ((p.coeff a).coeff b)*
          (scalar (if k ≤ a then 2^k*(-1)^(a-k)*(a.choose k:ℚ) else 0)*L^k)*
          (scalar (if l ≤ b then 2^l*(-1)^(b-l)*(b.choose l:ℚ) else 0)*R^l) := by
    intro k l
    unfold TensorWholeIntervalBernstein.shiftedCoefficient
    rw [Fin.sum_univ_eq_sum_range (fun a => ∑ j : Fin (D+1),if k ≤ a ∧ l ≤ j.val then
      (-1:ℚ)^(a+j.val-k-l)*(a.choose k:ℚ)*(j.val.choose l:ℚ)*(p.coeff a).coeff j.val else 0) (D+1)]
    simp only [fun a => Fin.sum_univ_eq_sum_range (fun b => if k ≤ a ∧ l ≤ b then
      (-1:ℚ)^(a+b-k-l)*(a.choose k:ℚ)*(b.choose l:ℚ)*(p.coeff a).coeff b else 0) (D+1)]
    rw [Finset.mul_sum,r54_scalar_eq,map_sum,Finset.sum_mul,Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum,map_sum,Finset.sum_mul,Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hk : k ≤ a <;> by_cases hl : l ≤ b <;> simp only [hk,hl,and_self,and_true,
      and_false,↓reduceIte,mul_zero,map_zero,zero_mul,mul_zero,r54_scalar_zero]
    rw [show a+b-k-l=(a-k)+(b-l) by omega,pow_add]
    simp only [r54_scalar_eq,map_mul,map_pow,map_neg,map_one,map_natCast,
      show r54σ 2=2 from map_ofNat r54σ 2]
    ring
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => key k l)),r54_swap4]
  conv_rhs => rw [r54_eq_sum hp]
  refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
  simp only [Finset.mem_range] at ha hb
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  rw [r54_binomial L (by omega : a≤D),r54_binomial R (by omega : b≤D),r54_left,r54_right]


theorem r54_double_ext {M : Type*} [AddCommMonoid M] (T : ℕ → ℕ → M) {i j D : ℕ}
    (hi : i≤D) (hj : j≤D) :
    (∑ k ∈ Finset.range (i+1),∑ l ∈ Finset.range (j+1),T k l)=
      ∑ k ∈ Finset.range (D+1),∑ l ∈ Finset.range (D+1),
        if k ≤ i ∧ l ≤ j then T k l else 0 := by
  rw [r54_sum_range_ext _ hi]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with hk
  · rw [r54_sum_range_ext _ hj]
    exact Finset.sum_congr rfl (fun l _ => by simp only [hk,true_and])
  · symm
    exact Finset.sum_eq_zero (fun l _ => by simp only [hk,false_and,↓reduceIte])

theorem r54_expansion_shifted (D : ℕ) (p : Bivar) :
    TensorWholeIntervalBernstein.expansion D p=
      ∑ k ∈ Finset.range (D+1),∑ l ∈ Finset.range (D+1),
        scalar (TensorWholeIntervalBernstein.shiftedCoefficient D p k l)*
          TensorWholeIntervalBernstein.left^k*TensorWholeIntervalBernstein.right^l := by
  set L := TensorWholeIntervalBernstein.left
  set R := TensorWholeIntervalBernstein.right
  set sc := TensorWholeIntervalBernstein.shiftedCoefficient D p
  let A : Bivar → ℕ → ℕ → Bivar := fun U i k => if k ≤ i then
    scalar ((i.choose k:ℚ)/(D.choose k:ℚ)*(D.choose i:ℚ))*U^i*(1-U)^(D-i) else 0
  let G : ℕ → ℕ → Bivar := fun i j =>
    scalar (∑ k ∈ Finset.range (i+1),∑ l ∈ Finset.range (j+1),
      sc k l*((i.choose k:ℚ)/(D.choose k:ℚ))*((j.choose l:ℚ)/(D.choose l:ℚ)))*
    (scalar ((D.choose i:ℚ)*(D.choose j:ℚ))*L^i*(1-L)^(D-i)*R^j*(1-R)^(D-j))
  have e1 : TensorWholeIntervalBernstein.expansion D p=
      ∑ i : Fin (D+1),∑ j : Fin (D+1),G i.val j.val := rfl
  rw [e1,Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (D+1),G i j.val) (D+1)]
  simp only [fun i => Fin.sum_univ_eq_sum_range (fun j => G i j) (D+1)]
  have e2 : ∀ i ∈ Finset.range (D+1),∀ j ∈ Finset.range (D+1),
      G i j=∑ k ∈ Finset.range (D+1),∑ l ∈ Finset.range (D+1),scalar (sc k l)*A L i k*A R j l := by
    intro i hi j hj
    simp only [Finset.mem_range] at hi hj
    simp only [G]
    rw [r54_double_ext _ (show i≤D by omega) (show j≤D by omega),r54_scalar_eq,map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_sum,Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [A]
    by_cases hk : k ≤ i <;> by_cases hl : l ≤ j <;>
      simp only [hk,hl,and_self,and_true,and_false,↓reduceIte,map_zero,
        zero_mul,mul_zero]
    simp only [r54_scalar_eq,map_mul]
    ring
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => e2 i hi j hj)),
    r54_swap4]
  refine Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => ?_))
  simp only [Finset.mem_range] at hk hl
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  rw [show (∑ i ∈ Finset.range (D+1),A L i k)=L^k from r54_pow_eq L (by omega),
    show (∑ j ∈ Finset.range (D+1),A R j l)=R^l from r54_pow_eq R (by omega)]

theorem r54_expansion {D : ℕ} {p : Bivar} (hp : r54Bounded D p) :
    p=TensorWholeIntervalBernstein.expansion D p := by
  rw [r54_expansion_shifted,r54_shifted_sum hp]


theorem r54Bounded.mono {D E : ℕ} {p : Bivar} (hp : r54Bounded D p) (h : D≤E) :
    r54Bounded E p := fun a b hab => ⟨(hp a b hab).1.trans h,(hp a b hab).2.trans h⟩

theorem r54Bounded.add {D : ℕ} {p q : Bivar} (hp : r54Bounded D p) (hq : r54Bounded D q) :
    r54Bounded D (p+q) := by
  intro a b hab
  simp only [coeff_add] at hab
  by_cases h : (p.coeff a).coeff b=0
  · rw [h,zero_add] at hab
    exact hq a b hab
  · exact hp a b h

theorem r54Bounded.neg {D : ℕ} {p : Bivar} (hp : r54Bounded D p) : r54Bounded D (-p) := by
  intro a b hab
  simp only [coeff_neg] at hab
  exact hp a b (fun h => hab (by rw [h,neg_zero]))

theorem r54Bounded.sum {D : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Bivar}
    (hf : ∀ i ∈ s,r54Bounded D (f i)) : r54Bounded D (∑ i ∈ s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro a b hab
    simp at hab
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem r54Bounded_monomial (c : ℚ) {D i j : ℕ} (hi : i≤D) (hj : j≤D) :
    r54Bounded D (scalar c*X^i*(C X)^j) := by
  intro a b hab
  have e : scalar c*X^i*(C X)^j=C (C c*X^j)*X^i := by
    simp only [scalar,map_mul,map_pow]
    ring
  rw [e,coeff_C_mul_X_pow] at hab
  split_ifs at hab with ha
  · rw [coeff_C_mul_X_pow] at hab
    split_ifs at hab with hb
    · exact ⟨ha ▸ hi,hb ▸ hj⟩
    · exact absurd rfl hab
  · exact absurd rfl hab

theorem r54Bounded_scalar (c : ℚ) (D : ℕ) : r54Bounded D (scalar c) := by
  have h := r54Bounded_monomial c (D := D) (Nat.zero_le D) (Nat.zero_le D)
  simpa using h

theorem r54Bounded_truncate (p : Bivar) : r54Bounded 14 (TensorPolynomialEnclosure.truncate p) := by
  unfold TensorPolynomialEnclosure.truncate
  refine r54Bounded.sum _ (fun i _ => r54Bounded.sum _ (fun j _ => ?_))
  split_ifs with h
  · exact r54Bounded_monomial _ (by omega) (by omega)
  · intro a b hab
    simp at hab


section r54_enclosures
open TensorPolynomialEnclosure

theorem r54_constant_bounded (c : ℚ) : r54Bounded 14 (constant c).polynomial :=
  r54Bounded_scalar c 14

theorem r54_add_bounded {a b : Enclosure} (ha : r54Bounded 14 a.polynomial)
    (hb : r54Bounded 14 b.polynomial) : r54Bounded 14 (TensorPolynomialEnclosure.add a b).polynomial :=
  ha.add hb

theorem r54_neg_bounded {a : Enclosure} (ha : r54Bounded 14 a.polynomial) :
    r54Bounded 14 (TensorPolynomialEnclosure.neg a).polynomial :=
  r54Bounded.neg ha

theorem r54_mul_bounded (a b : Enclosure) :
    r54Bounded 14 (TensorPolynomialEnclosure.mul a b).polynomial :=
  r54Bounded_truncate _

theorem r54_power_bounded (a : Enclosure) (n : ℕ) :
    r54Bounded 14 (TensorPolynomialEnclosure.power a n).polynomial := by
  rw [TensorPolynomialEnclosure.power]
  split_ifs
  · exact r54_constant_bounded 1
  · exact r54_mul_bounded _ _
  · exact r54_mul_bounded _ _

theorem r54_sine_bounded (a : Enclosure) : r54Bounded 14 (sine a).polynomial := by
  simp only [sine,widen,TensorPolynomialEnclosure.sum]
  exact r54Bounded.sum _ (fun j _ => r54_mul_bounded _ _)

theorem r54_cosine_bounded (a : Enclosure) : r54Bounded 14 (cosine a).polynomial := by
  simp only [cosine,widen,TensorPolynomialEnclosure.sum]
  exact r54Bounded.sum _ (fun j _ => r54_mul_bounded _ _)

theorem r54_enclose_bounded {ι : Type*} {w : ι → Enclosure}
    (hw : ∀ i,r54Bounded 14 (w i).polynomial) (e : Expression ι) :
    r54Bounded 14 (Expression.enclose w e).polynomial := by
  induction e with
  | literal r => exact r54_constant_bounded r
  | «variable» i => exact hw i
  | add a b ha hb => exact r54_add_bounded ha hb
  | neg a ha => exact r54_neg_bounded ha
  | mul a b _ _ => exact r54_mul_bounded _ _
  | power a n _ => exact r54_power_bounded _ n

end r54_enclosures

section r54_constant
open TensorPolynomialEnclosure

/-- The constant coefficient of a tensor polynomial. -/
def r54κ : Bivar →+* ℚ :=
  (Polynomial.constantCoeff : ℚ[X] →+* ℚ).comp (Polynomial.constantCoeff : Bivar →+* ℚ[X])

theorem r54κ_scalar (c : ℚ) : r54κ (scalar c)=c := by
  simp [r54κ,scalar]

theorem r54κ_X : r54κ X=0 := by simp [r54κ]

theorem r54κ_CX : r54κ (C X)=0 := by simp [r54κ]

theorem r54κ_monomial (c : ℚ) (i j : ℕ) :
    r54κ (scalar c*X^i*(C X)^j)=c*0^i*0^j := by
  rw [map_mul,map_mul,map_pow,map_pow,r54κ_scalar,r54κ_X,r54κ_CX]

theorem r54κ_truncate (p : Bivar) : r54κ (truncate p)=r54κ p := by
  unfold truncate
  rw [map_sum,Finset.sum_eq_single (0 : Fin 15)]
  · rw [map_sum,Finset.sum_eq_single (0 : Fin 15)]
    · simp only [Fin.val_zero,add_zero,zero_le,↓reduceIte,pow_zero,mul_one]
      simp [r54κ,scalar]
    · intro j _ hj
      have hj' : j.val≠0 := fun h => hj (Fin.ext h)
      split_ifs
      · rw [r54κ_monomial,zero_pow hj',mul_zero]
      · exact map_zero _
    · simp
  · intro i _ hi
    have hi' : i.val≠0 := fun h => hi (Fin.ext h)
    rw [map_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    split_ifs
    · rw [r54κ_monomial,zero_pow hi',mul_zero,zero_mul]
    · exact map_zero _
  · simp


theorem r54κ_mul (a b : Enclosure) :
    r54κ (TensorPolynomialEnclosure.mul a b).polynomial=r54κ a.polynomial*r54κ b.polynomial := by
  show r54κ (truncate (a.polynomial*b.polynomial))=_
  rw [r54κ_truncate,map_mul]

theorem r54κ_constant (c : ℚ) : r54κ (constant c).polynomial=c := r54κ_scalar c

theorem r54κ_power (a : Enclosure) (n : ℕ) :
    r54κ (TensorPolynomialEnclosure.power a n).polynomial=r54κ a.polynomial^n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [TensorPolynomialEnclosure.power]
    by_cases hn : n=0
    · subst hn
      simp [r54κ_constant]
    · simp only [hn,↓reduceIte]
      have hh := ih (n/2) (by omega)
      by_cases he : n%2=0
      · simp only [he,↓reduceIte,r54κ_mul,hh,← pow_add]
        congr 1
        omega
      · simp only [he,↓reduceIte,r54κ_mul,hh,← pow_add,← pow_succ]
        congr 1
        omega

theorem r54κ_enclose {ι : Type*} (w : ι → Enclosure) (e : Expression ι) :
    (r54κ (Expression.enclose w e).polynomial:ℝ)=
      Expression.value (fun i => (r54κ (w i).polynomial:ℝ)) e := by
  induction e with
  | literal r => simp [Expression.enclose,Expression.value,r54κ_constant]
  | «variable» i => rfl
  | add a b ha hb =>
    simp only [Expression.enclose,Expression.value,TensorPolynomialEnclosure.add,map_add,
      Rat.cast_add,ha,hb]
  | neg a ha =>
    simp only [Expression.enclose,Expression.value,TensorPolynomialEnclosure.neg,map_neg,
      Rat.cast_neg,ha]
  | mul a b ha hb =>
    simp only [Expression.enclose,Expression.value,r54κ_mul,Rat.cast_mul,ha,hb]
  | power a n ha =>
    simp only [Expression.enclose,Expression.value,r54κ_power,Rat.cast_pow,ha]

theorem r54κ_sine (a : Enclosure) :
    (r54κ (sine a).polynomial:ℝ)=HighOrderTaylor.S13 (r54κ a.polynomial:ℝ) := by
  rw [← sine_sum]
  simp only [sine,widen,TensorPolynomialEnclosure.sum,map_sum,r54κ_mul,r54κ_power,
    r54κ_constant,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Rat.cast_div]

theorem r54κ_cosine (a : Enclosure) :
    (r54κ (cosine a).polynomial:ℝ)=HighOrderTaylor.C14 (r54κ a.polynomial:ℝ) := by
  rw [← cosine_sum]
  simp only [cosine,widen,TensorPolynomialEnclosure.sum,map_sum,r54κ_mul,r54κ_power,
    r54κ_constant,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Rat.cast_div]


theorem r54_rootSeed_eq (a : Enclosure) : rootSeed a=nearestRoot (r54κ a.polynomial) := by
  simp [rootSeed,r54κ]

theorem r54_nearestRoot_pos {r : ℚ} (hr : 1/100≤r) : 0<nearestRoot r := by
  have hr0 : 0<r := by linarith
  have hnum : 0<r.num := Rat.num_pos.mpr hr0
  have hden : (0:ℚ)<r.den := by exact_mod_cast r.den_pos
  have hcross : (r.den:ℚ)≤r.num*10000000000000000 := by
    have h := Rat.num_div_den r
    rw [← h] at hr
    rw [le_div_iff₀ hden] at hr
    linarith
  have hN : 1≤r.num.natAbs*10000000000000000/r.den := by
    rw [Nat.one_le_div_iff r.den_pos]
    have h1 : ((r.num.natAbs:ℤ):ℚ)=r.num := by
      rw [Int.natAbs_of_nonneg hnum.le]
    have h2 : ((r.den:ℕ):ℚ)≤((r.num.natAbs*10000000000000000:ℕ):ℚ) := by
      push_cast
      rw [show ((r.num.natAbs:ℕ):ℚ)=((r.num.natAbs:ℤ):ℚ) from (Int.cast_natCast _).symm,h1]
      exact hcross
    exact_mod_cast h2
  have hn : 1≤Nat.sqrt (r.num.natAbs*10000000000000000/r.den) := Nat.le_sqrt.mpr (by simpa using hN)
  unfold nearestRoot
  dsimp only
  apply div_pos _ (by norm_num)
  split_ifs
  · exact_mod_cast hn
  · exact_mod_cast (Nat.succ_pos _)

end r54_constant

end SquaresInCircles.Eight.ExceptionalPositiveTPolynomials

namespace SquaresInCircles.Eight.ExceptionalPositiveTPolynomials
open TensorPolynomialEnclosure TensorWholeIntervalPolynomial
open ExceptionalPositiveTScalarModel

abbrev Expr := Expression (Fin 10)
abbrev lit (r : ℚ) : Expr := .literal r
abbrev var (i : Fin 10) : Expr := .variable i

def tE : Expr := var 0
def zE : Expr := var 1
def sx : Expr := var 2
def cx : Expr := var 3
def sz : Expr := var 4
def cz : Expr := var 5
def se : Expr := var 6
def ce : Expr := var 7
def st : Expr := var 8
def ct : Expr := var 9

def KE : Family → Expr
  | .lowZero | .lowAfter => lit (17253/20000)+lit (67/100)*tE+lit (27/100)*tE^2
  | .middle | .high => 1
def LE : Family → Expr
  | .lowZero | .lowAfter => lit (50521/100000)+lit (21/25)*tE+tE^2*lit (1/2)
  | .middle => lit (551/1000)+lit (67/100)*tE+lit (21/100)*tE^2
  | .high => lit (7/10)+lit (8/25)*tE
def CE : Family → Expr
  | .lowZero | .lowAfter => lit (17253/20000)+lit (18/25)*tE+lit (3/10)*tE^2
  | .middle => lit (891/1000)+lit (16/25)*tE+tE^2*lit (1/50)
  | .high => lit (113/100)
def etaE : Family → Expr
  | .lowZero | .lowAfter => lit (131/500)+lit (19/100)*tE+lit (2/25)*tE^2
  | .middle => lit (61/200)-tE*lit (1/50)+lit (7/200)*tE^2
  | .high => lit (27/100)+lit (2/25)*tE
def kE (f : Family) : Expr := KE f+lit (3/50)*zE
def ellE (f : Family) : Expr := LE f-lit (23/100)*zE
def cE (f : Family) : Expr := CE f-lit (53/100)*zE
def nE (s : ScalarCase) : Expr := kE s.family*(cx+etaE s.family*sx)
def mE (s : ScalarCase) : Expr := cE s.family*(cz+etaE s.family*sz)
def pE (s : ScalarCase) : Expr := ce+etaE s.family*se
def firstE (s : ScalarCase) : Fin 4 → Expr := ![pE s,kE s.family,ellE s.family,1]
def secondE (s : ScalarCase) : Fin 4 → Expr :=
  ![nE s,ellE s.family,if s.td then mE s else cE s.family,
    if s.td then cE s.family else mE s]
def nuE (s : ScalarCase) : Expr :=
  ![if s.hCoefficient then pE s else nE s,ellE s.family,
    if s.td then mE s+(if s.family=.high then lit (3/100) else 0) else ellE s.family,
    if s.td then cE s.family else mE s] s.negative
def squareE (s : ScalarCase) (i : Fin 4) : Expr :=
  firstE s i^2+secondE s i^2-
    if i=s.negative then 2*firstE s i*secondE s i*st else 0
def rootSquare (s : ScalarCase) (i : Fin 5) : Expr :=
  if hi : i.val<4 then squareE s ⟨i.val,hi⟩ else 1+etaE s.family^2

def parameter (f : Family) : Enclosure :=
  TensorPolynomialEnclosure.add (constant ((left f+right f)/2))
    (mul (constant ((right f-left f)/2)) outerVariable)
def secondParameter (f : Family) : Enclosure :=
  mul (mul (parameter f) (TensorPolynomialEnclosure.add (constant 1) innerVariable)) (constant (1/2))
def xParameter (s : ScalarCase) : Enclosure :=
  if s.atG then TensorPolynomialEnclosure.sub (parameter s.family) (secondParameter s.family) else constant 0
def eParameter (s : ScalarCase) : Enclosure :=
  if s.atG then constant 0 else TensorPolynomialEnclosure.sub (parameter s.family) (secondParameter s.family)
def «variables» (s : ScalarCase) : Fin 10 → Enclosure :=
  ![parameter s.family,secondParameter s.family,sine (xParameter s),cosine (xParameter s),
    sine (secondParameter s.family),cosine (secondParameter s.family),
    sine (eParameter s),cosine (eParameter s),sine (parameter s.family),
    cosine (parameter s.family)]
def rootExpression (s : ScalarCase) (i : Fin 5) : Expr :=
  Expression.sqrtUpper («variables» s) (rootSquare s i)
def baseExpression (s : ScalarCase) : Expr :=
  kE s.family*(1+2*cx+(1+2*etaE s.family)*sx)+
    cE s.family*(1+2*cz+(1+2*etaE s.family)*sz)+2*ellE s.family+
    1+2*ce+(1+2*etaE s.family)*se-
    lit radiusUpper*(kE s.family*sx+cE s.family*sz+se)*rootExpression s 4
def expression (s : ScalarCase) : Expr :=
  ((((baseExpression s+nuE s*(ct-1))-
    lit radiusUpper*rootExpression s 0)-lit radiusUpper*rootExpression s 1)-
      lit radiusUpper*rootExpression s 2)-lit radiusUpper*rootExpression s 3
def enclosure (s : ScalarCase) : Enclosure := Expression.enclose («variables» s) (expression s)
def polynomial (s : ScalarCase) : Bivar := (enclosure s).polynomial

theorem r54_variables_bounded (s : ScalarCase) (i : Fin 10) :
    r54Bounded 14 («variables» s i).polynomial := by
  have hP : r54Bounded 14 (parameter s.family).polynomial :=
    r54_add_bounded (r54_constant_bounded _) (r54_mul_bounded _ _)
  fin_cases i
  · exact hP
  · exact r54_mul_bounded _ _
  · exact r54_sine_bounded _
  · exact r54_cosine_bounded _
  · exact r54_sine_bounded _
  · exact r54_cosine_bounded _
  · exact r54_sine_bounded _
  · exact r54_cosine_bounded _
  · exact r54_sine_bounded _
  · exact r54_cosine_bounded _

section r54_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
@[simp] private theorem r54_value_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
@[simp] private theorem r54_value_neg : Expression.value v (-a)=-Expression.value v a := rfl
@[simp] private theorem r54_value_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
@[simp] private theorem r54_value_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
@[simp] private theorem r54_value_pow (n : ℕ) :
    Expression.value v (a^n)=Expression.value v a^n := rfl
@[simp] private theorem r54_value_one : Expression.value v (1 : Expression ι)=1 := by
  show (((1:ℕ):ℚ):ℝ)=1
  norm_num
@[simp] private theorem r54_value_two : Expression.value v (2 : Expression ι)=2 := by
  show (((2:ℕ):ℚ):ℝ)=2
  norm_num
@[simp] private theorem r54_value_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
@[simp] private theorem r54_value_ite (P : Prop) [Decidable P] :
    Expression.value v (if P then a else b)=
      if P then Expression.value v a else Expression.value v b := by
  split_ifs <;> rfl
end r54_value

@[simp] private theorem r54_value_lit (w : Fin 10 → ℝ) (r : ℚ) :
    Expression.value w (lit r)=(r:ℝ) := rfl
@[simp] private theorem r54_value_var (w : Fin 10 → ℝ) (i : Fin 10) :
    Expression.value w (var i)=w i := rfl

theorem r54_taylor_bounds {y : ℝ} (h0 : 0≤y) (h1 : y≤21/40) :
    0≤HighOrderTaylor.S13 y ∧ HighOrderTaylor.S13 y≤3/5 ∧ 1/2≤HighOrderTaylor.C14 y := by
  have hs := HighOrderTaylor.sin_le_S13 h0
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_three])
  have hs15 := HighOrderTaylor.S15_le_sin h0
  have hsl := Real.sin_le h0
  have hc := HighOrderTaylor.cos_le_C16 h0
  have hc1 := Real.one_sub_sq_div_two_le_cos (x := y)
  have hp15 : y^15≤1 := pow_le_one₀ h0 (by linarith)
  have hp16 : y^16≤1 := pow_le_one₀ h0 (by linarith)
  have hy2 : y^2≤1/2 := by nlinarith
  simp only [HighOrderTaylor.S15,HighOrderTaylor.C16] at hs15 hc
  refine ⟨by linarith,by linarith,by linarith⟩

/-- The constant coefficients of the ten input enclosures. -/
def r54v (s : ScalarCase) : Fin 10 → ℝ := fun j => (r54κ («variables» s j).polynomial:ℝ)

theorem r54κ_parameter (f : Family) :
    r54κ (parameter f).polynomial=(left f+right f)/2 := by
  simp [parameter,TensorPolynomialEnclosure.add,r54κ_mul,r54κ_constant,outerVariable,r54κ_X]

theorem r54κ_secondParameter (f : Family) :
    r54κ (secondParameter f).polynomial=(left f+right f)/2*(1/2) := by
  simp [secondParameter,TensorPolynomialEnclosure.add,r54κ_mul,r54κ_constant,innerVariable,
    r54κ_CX,r54κ_parameter]

theorem r54_parameter_range (f : Family) :
    0≤((left f:ℝ)+(right f:ℝ))/2 ∧ ((left f:ℝ)+(right f:ℝ))/2≤21/40 := by
  cases f <;> norm_num [left,right]

theorem r54v_bounds (s : ScalarCase) :
    r54v s 0=((left s.family:ℝ)+(right s.family:ℝ))/2 ∧
    r54v s 1=((left s.family:ℝ)+(right s.family:ℝ))/2/2 ∧
    0≤r54v s 6 ∧ 1/2≤r54v s 7 ∧ 0≤r54v s 8 ∧ r54v s 8≤3/5 := by
  obtain ⟨h0,h1⟩ := r54_parameter_range s.family
  have hP : (r54κ (parameter s.family).polynomial:ℝ)=((left s.family:ℝ)+(right s.family:ℝ))/2 := by
    rw [r54κ_parameter]
    push_cast
    ring
  have hS : (r54κ (secondParameter s.family).polynomial:ℝ)=
      ((left s.family:ℝ)+(right s.family:ℝ))/2/2 := by
    rw [r54κ_secondParameter]
    push_cast
    ring
  have he : (r54κ (eParameter s).polynomial:ℝ)∈Set.Icc 0 (21/40) := by
    unfold eParameter
    split_ifs
    · simp only [r54κ_constant,Rat.cast_zero,Set.mem_Icc,le_refl,true_and]
      norm_num
    · simp only [TensorPolynomialEnclosure.sub,TensorPolynomialEnclosure.add,
        TensorPolynomialEnclosure.neg,map_add,map_neg,Rat.cast_add,Rat.cast_neg,hP,hS]
      constructor <;> linarith
  have hE := r54_taylor_bounds he.1 he.2
  have hT := r54_taylor_bounds h0 h1
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact hP
  · exact hS
  · simpa [r54v,«variables»,r54κ_sine] using hE.1
  · simpa [r54v,«variables»,r54κ_cosine] using hE.2.2
  · simpa [r54v,«variables»,r54κ_sine,hP] using hT.1
  · simpa [r54v,«variables»,r54κ_sine,hP] using hT.2.1

theorem r54_first_lower (s : ScalarCase) (j : Fin 4) :
    3/10≤Expression.value (r54v s) (firstE s j) := by
  obtain ⟨h0,h1,h6,h7,h8,h8'⟩ := r54v_bounds s
  have heta : 0≤Expression.value (r54v s) (etaE s.family) := by
    cases hf : s.family <;> rw [hf] at h0 <;>
      simp [etaE,ExceptionalPositiveTPolynomials.tE,h0,left,right] <;> norm_num
  fin_cases j
  · show 3/10≤Expression.value (r54v s) (pE s)
    simp only [pE,r54_value_add,r54_value_mul,r54_value_var,ce,se]
    nlinarith
  · show 3/10≤Expression.value (r54v s) (kE s.family)
    cases hf : s.family <;> rw [hf] at h0 h1 <;>
      simp [kE,KE,ExceptionalPositiveTPolynomials.tE,zE,h0,h1,left,right] <;> norm_num
  · show 3/10≤Expression.value (r54v s) (ellE s.family)
    cases hf : s.family <;> rw [hf] at h0 h1 <;>
      simp [ellE,ExceptionalPositiveTPolynomials.LE,ExceptionalPositiveTPolynomials.tE,zE,h0,h1,
        left,right] <;> norm_num
  · show 3/10≤Expression.value (r54v s) 1
    norm_num

theorem r54_rootSquare_lower (s : ScalarCase) (i : Fin 5) :
    1/100≤Expression.value (r54v s) (rootSquare s i) := by
  obtain ⟨h0,h1,h6,h7,h8,h8'⟩ := r54v_bounds s
  unfold rootSquare
  split_ifs with hi
  · have hA := r54_first_lower s ⟨i.val,hi⟩
    simp only [squareE,r54_value_sub,r54_value_add,r54_value_pow,r54_value_ite,r54_value_mul,
      r54_value_two,r54_value_zero,r54_value_var,st]
    set A := Expression.value (r54v s) (firstE s ⟨i.val,hi⟩)
    set B := Expression.value (r54v s) (secondE s ⟨i.val,hi⟩)
    set S := r54v s 8
    have hS2 : S^2≤9/25 := by nlinarith
    have hA2 : 9/100≤A^2 := by nlinarith
    have key : 9/100*(16/25)≤A^2*(1-S^2) :=
      mul_le_mul hA2 (by linarith) (by norm_num) (by positivity)
    split_ifs
    · nlinarith [sq_nonneg (B-A*S),key]
    · nlinarith [sq_nonneg B]
  · simp only [r54_value_add,r54_value_one,r54_value_pow]
    nlinarith [sq_nonneg (Expression.value (r54v s) (etaE s.family))]

theorem seeds_positive (s : ScalarCase) (i : Fin 5) :
    0<rootSeed (Expression.enclose («variables» s) (rootSquare s i)) := by
  rw [r54_rootSeed_eq]
  apply r54_nearestRoot_pos
  have h := r54_rootSquare_lower s i
  rw [show Expression.value (r54v s) (rootSquare s i)=
    (r54κ (Expression.enclose («variables» s) (rootSquare s i)).polynomial:ℝ) from
      (r54κ_enclose _ _).symm] at h
  have h' : (((1/100:ℚ)):ℝ)≤(r54κ (Expression.enclose («variables» s) (rootSquare s i)).polynomial:ℝ) := by
    push_cast
    linarith
  exact Rat.cast_le.mp h'

def parameterValue (f : Family) (X : ℝ) : ℝ :=
  ((left f:ℝ)+(right f:ℝ))/2+((right f:ℝ)-(left f:ℝ))/2*X
def secondValue (f : Family) (X Y : ℝ) : ℝ := parameterValue f X*(1+Y)/2
def inputs (s : ScalarCase) (t z : ℝ) : Fin 10 → ℝ :=
  ![t,z,Real.sin (x s t z),Real.cos (x s t z),Real.sin z,Real.cos z,
    Real.sin (ExceptionalPositiveTScalarModel.e s t z),Real.cos (ExceptionalPositiveTScalarModel.e s t z),Real.sin t,Real.cos t]

theorem parameter_mem (f : Family) {X : ℝ} (hX : |X|≤1) :
    parameterValue f X∈domain f := by
  have h := abs_le.mp hX
  cases f <;> norm_num [parameterValue,domain,left,right] <;>
    constructor <;> linarith [h.1,h.2]
theorem second_mem (f : Family) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    secondValue f X Y∈Set.Icc 0 (parameterValue f X) := by
  have ht := (angle (parameter_mem f hX)).1
  have hy := abs_le.mp hY
  have hp := mul_nonneg ht (show 0≤1+Y by linarith)
  have hu := mul_nonneg ht (show 0≤1-Y by linarith)
  dsimp [secondValue]
  constructor <;> nlinarith

/-! ### The packed certificate

The expression is mirrored by an `IE` expression whose literals are integer fractions and whose
five roots are extra variables. The roots are evaluated once per family, `td`, `atG`, root and
sign pattern by the packed Taylor models of `PackedModels`, then the whole expression, and the
kernel checks its degree-10 Bernstein coefficients in natural-number arithmetic. The root seeds
are checked the same way at the center of the square. -/

section packed
open PackedModels

/-- Expressions of packed models over the ten inputs (`inl`) and the five roots (`inr`). -/
abbrev IExpr := IE (Fin 10 ⊕ Fin 5)
def lq (n d : ℕ) : IExpr := .lit (.q n d)
def tI : IExpr := .var (.inl 0)
def zI : IExpr := .var (.inl 1)
def sxI : IExpr := .var (.inl 2)
def cxI : IExpr := .var (.inl 3)
def szI : IExpr := .var (.inl 4)
def czI : IExpr := .var (.inl 5)
def seI : IExpr := .var (.inl 6)
def ceI : IExpr := .var (.inl 7)
def stI : IExpr := .var (.inl 8)
def ctI : IExpr := .var (.inl 9)

def KI : Family → IExpr
  | .lowZero | .lowAfter => lq 17253 20000+lq 67 100*tI+lq 27 100*tI^2
  | .middle | .high => 1
def LI : Family → IExpr
  | .lowZero | .lowAfter => lq 50521 100000+lq 21 25*tI+tI^2*lq 1 2
  | .middle => lq 551 1000+lq 67 100*tI+lq 21 100*tI^2
  | .high => lq 7 10+lq 8 25*tI
def CI : Family → IExpr
  | .lowZero | .lowAfter => lq 17253 20000+lq 18 25*tI+lq 3 10*tI^2
  | .middle => lq 891 1000+lq 16 25*tI+tI^2*lq 1 50
  | .high => lq 113 100
def etaI : Family → IExpr
  | .lowZero | .lowAfter => lq 131 500+lq 19 100*tI+lq 2 25*tI^2
  | .middle => lq 61 200-tI*lq 1 50+lq 7 200*tI^2
  | .high => lq 27 100+lq 2 25*tI
def kI (f : Family) : IExpr := KI f+lq 3 50*zI
def ellI (f : Family) : IExpr := LI f-lq 23 100*zI
def cI (f : Family) : IExpr := CI f-lq 53 100*zI
def nI (f : Family) : IExpr := kI f*(cxI+etaI f*sxI)
def mI (f : Family) : IExpr := cI f*(czI+etaI f*szI)
def pI (f : Family) : IExpr := ceI+etaI f*seI
def firstI (f : Family) : Fin 4 → IExpr := ![pI f,kI f,ellI f,1]
def secondI (f : Family) (td : Bool) : Fin 4 → IExpr :=
  ![nI f,ellI f,if td then mI f else cI f,if td then cI f else mI f]
def nuI (s : ScalarCase) : IExpr :=
  ![if s.hCoefficient then pI s.family else nI s.family,ellI s.family,
    if s.td then mI s.family+(if s.family=.high then lq 3 100 else 0) else ellI s.family,
    if s.td then cI s.family else mI s.family] s.negative
/-- The square of root `i < 4`, with the cross term when `neg`. -/
def squareI (f : Family) (td : Bool) (i : Fin 4) (neg : Bool) : IExpr :=
  firstI f i^2+secondI f td i^2-
    if neg then 2*firstI f i*secondI f td i*stI else 0
def rootSquareI (f : Family) (td : Bool) (i : Fin 5) (neg : Bool) : IExpr :=
  if hi : i.val<4 then squareI f td ⟨i.val,hi⟩ neg else 1+etaI f^2
def rootI (i : Fin 5) : IExpr := .var (.inr i)
def radiusI : IExpr := lq 989385433 500000000
def baseI (s : ScalarCase) : IExpr :=
  kI s.family*(1+2*cxI+(1+2*etaI s.family)*sxI)+
    cI s.family*(1+2*czI+(1+2*etaI s.family)*szI)+2*ellI s.family+
    1+2*ceI+(1+2*etaI s.family)*seI-
    radiusI*(kI s.family*sxI+cI s.family*szI+seI)*rootI 4
/-- The expression with its roots as variables. -/
def skeleton (s : ScalarCase) : IExpr :=
  ((((baseI s+nuI s*(ctI-1))-
    radiusI*rootI 0)-radiusI*rootI 1)-
      radiusI*rootI 2)-radiusI*rootI 3

/-- Whether root `i` carries the negative cross term. -/
def isNegative (s : ScalarCase) (i : Fin 5) : Bool := decide (i.val=s.negative.val)

/-- The formulas of the variables: the inputs, and the roots or zero. -/
def formulas (s : ScalarCase) : Fin 10 ⊕ Fin 5 → Expr := Sum.elim Expression.variable (rootExpression s)
def inputFormulas : Fin 10 ⊕ Fin 5 → Expr := Sum.elim Expression.variable fun _ => 0

theorem rootSquareI_eq (s : ScalarCase) (i : Fin 5) :
    (rootSquareI s.family s.td i (isNegative s i)).toExpressionWith inputFormulas=rootSquare s i := by
  rcases s with ⟨f,td,atG,negative,h⟩
  cases f <;> cases td <;> fin_cases negative <;> fin_cases i <;> rfl

theorem skeleton_eq (s : ScalarCase) : (skeleton s).toExpressionWith (formulas s)=expression s := by
  rcases s with ⟨f,td,atG,negative,h⟩
  cases f <;> cases td <;> cases h <;> fin_cases negative <;> rfl

/-- The models work at scale `2 ^ 48` with total degree `8`; the seeds use constant models. -/
def config : Config := ⟨48,8,116⟩
def seedConfig : Config := ⟨48,1,116⟩

theorem config_valid : config.Valid := ⟨by decide,by decide⟩
theorem seedConfig_valid : seedConfig.Valid := ⟨by decide,by decide⟩

/-- The center and the half-width of a family's interval. -/
def center : Family → ℕ × ℕ
  | .lowZero => (1,20) | .lowAfter => (17,100) | .middle => (53,200) | .high => (21,40)
def halfWidth : Family → ℕ × ℕ
  | .lowZero => (1,20) | .lowAfter => (1,100) | .middle => (17,200) | .high => (7,40)

theorem center_eq (f : Family) :
    (((center f).1:ℤ):ℝ)/(center f).2=((left f:ℝ)+(right f:ℝ))/2 := by
  cases f <;> norm_num [center,left,right]
theorem halfWidth_eq (f : Family) :
    (((halfWidth f).1:ℤ):ℝ)/(halfWidth f).2=((right f:ℝ)-(left f:ℝ))/2 := by
  cases f <;> norm_num [halfWidth,left,right]

def tModel (c : Config) (f : Family) : Model :=
  Model.add c (Model.lit c (center f).1 (center f).2)
    (Model.mul c (Model.lit c (halfWidth f).1 (halfWidth f).2) (Model.X c))
def zModel (c : Config) (f : Family) : Model :=
  Model.mul c (Model.mul c (tModel c f) (Model.add c (Model.one c) (Model.Y c))) (Model.lit c 1 2)
def gapModel (c : Config) (f : Family) : Model := Model.add c (tModel c f) (Model.neg (zModel c f))
def zeroModel (c : Config) : Model := Model.ofInt c 0 0 true

/-- The models of the ten inputs on the square. -/
def inputModels (f : Family) (atG : Bool) : Fin 10 → Model :=
  let c := config
  let x := if atG then gapModel c f else zeroModel c
  let e := if atG then zeroModel c else gapModel c f
  ![tModel c f,zModel c f,Model.sin c x,Model.cos c x,Model.sin c (zModel c f),
    Model.cos c (zModel c f),Model.sin c e,Model.cos c e,Model.sin c (tModel c f),
    Model.cos c (tModel c f)]

/-- The constant models of the constant coefficients of the input enclosures, and zero. -/
def pointModels (f : Family) (atG : Bool) : Fin 10 ⊕ Fin 5 → Model :=
  let c := seedConfig
  let t := Model.lit c (center f).1 (center f).2
  let z := Model.lit c (center f).1 (2*(center f).2)
  let g := Model.add c t (Model.neg z)
  let x := if atG then g else zeroModel c
  let e := if atG then zeroModel c else g
  Sum.elim ![t,z,Model.sinPoly c x,Model.cosPoly c x,Model.sinPoly c z,Model.cosPoly c z,
    Model.sinPoly c e,Model.cosPoly c e,Model.sinPoly c t,Model.cosPoly c t] fun _ => zeroModel c

/-- The root seeds, `10 ^ 8 · rootSeed`, found from the point models (checked in
`caseCheck`). -/
def seed (f : Family) (td atG : Bool) (i : Fin 5) (neg : Bool) : ℕ :=
  seedOf seedConfig (pointModels f atG) (rootSquareI f td i neg)

/-- The model of a root on the square. -/
def rootModel (f : Family) (td atG : Bool) (i : Fin 5) (neg : Bool) : Model :=
  (IE.sqrtUpper 0 (seed f td atG i neg) (rootSquareI f td i neg)).eval config
    (Sum.elim (inputModels f atG) fun _ => zeroModel config)

/-- The checks of a root. -/
def rootCheck (f : Family) (td atG : Bool) (i : Fin 5) (neg : Bool) : Bool :=
  seedCheck seedConfig (pointModels f atG) (rootSquareI f td i neg) (seed f td atG i neg) &&
    (rootSquareI f td i neg).seedFree && (rootSquareI f td i neg).poly &&
    (IE.sqrtUpper 0 (seed f td atG i neg) (rootSquareI f td i neg)).poly

/-- The models of the inputs and of the roots of a case. -/
def models (s : ScalarCase) : Fin 10 ⊕ Fin 5 → Model :=
  Sum.elim (inputModels s.family s.atG) fun i =>
    if i.val=s.negative.val then rootModel s.family s.td s.atG i true
    else rootModel s.family s.td s.atG i false

/-- Everything the kernel checks for one case. -/
def caseCheck (s : ScalarCase) : Bool :=
  check config 10 (models s) (skeleton s) 77 1000000 true && (skeleton s).poly &&
    (skeleton s).seedFree &&
    ([0,1,2,3,4] : List (Fin 5)).all fun i =>
      if i.val=s.negative.val then rootCheck s.family s.td s.atG i true
      else rootCheck s.family s.td s.atG i false

def allBool (p : Bool → Bool) : Bool := p false && p true
def allFin4 (p : Fin 4 → Bool) : Bool := p 0 && p 1 && p 2 && p 3

theorem allBool_eq {p : Bool → Bool} (h : allBool p=true) (b : Bool) : p b=true := by
  simp only [allBool,Bool.and_eq_true] at h
  cases b
  exacts [h.1,h.2]
theorem allFin4_eq {p : Fin 4 → Bool} (h : allFin4 p=true) (i : Fin 4) : p i=true := by
  simp only [allFin4,Bool.and_eq_true] at h
  fin_cases i
  exacts [h.1.1.1,h.1.1.2,h.1.2,h.2]

/-- The sixteen cases of a family and a `td`. -/
def chunkCheck (f : Family) (td : Bool) : Bool :=
  allBool fun atG => allFin4 fun neg => allBool fun h => caseCheck ⟨f,td,atG,neg,h⟩

/-- `check` with the model given. -/
def checkModel (c : Config) (n : ℕ) (m : Model) (num den : ℕ) (strict : Bool) : Bool :=
  m.ok && Nat.blt 0 den &&
    bernCheck c n m (Model.cdiv (num * 2 ^ c.K) den + m.e + (if strict then 1 else 0))

/-- Every variable of an expression satisfies `p`. -/
def varsAll {ι : Type} (p : ι → Bool) : IE ι → Bool
  | .var i => p i
  | .add a b | .mul a b => varsAll p a && varsAll p b
  | .neg a | .pow a _ | .sin a | .cos a | .sqrt a | .inv a => varsAll p a
  | .lit _ | .seed0 _ _ | .seed1 _ _ | .seed2 _ _ => true

/-- The models of an expression for inputs that agree on its variables agree. -/
theorem eval_congr {ι : Type} (c : Config) {w w' : ι → Model} (p : ι → Bool)
    (hw : ∀ i,p i=true → w i=w' i) : ∀ e : IE ι,varsAll p e=true → e.eval c w=e.eval c w'
  | .lit _,_ | .seed0 _ _,_ | .seed1 _ _,_ | .seed2 _ _,_ => rfl
  | .var i,h => hw i h
  | .add a b,h | .mul a b,h => by
    simp only [varsAll,Bool.and_eq_true] at h
    simp only [IE.eval,eval_congr c p hw a h.1,eval_congr c p hw b h.2]
  | .neg a,h | .pow a _,h | .sin a,h | .cos a,h | .sqrt a,h | .inv a,h => by
    simp only [varsAll] at h
    simp only [IE.eval,eval_congr c p hw a h]

/-- The variables of the root-free part: the inputs and the root `4`, which never carries the
negative cross term. -/
def rootFreeVar : Fin 10 ⊕ Fin 5 → Bool
  | .inl _ => true
  | .inr i => decide (4 ≤ i.val)

/-- The part of the skeleton before the negative index enters. -/
def rootFree (s : ScalarCase) : IExpr := baseI s

theorem rootFree_vars (f : Family) (td atG : Bool) (neg : Fin 4) (h : Bool) :
    varsAll rootFreeVar (rootFree ⟨f,td,atG,neg,h⟩)=true := by
  cases f <;> rfl

theorem rootFree_case (s : ScalarCase) : rootFree ⟨s.family,false,s.atG,0,false⟩=rootFree s := rfl

/-- The model of the skeleton from the model `P` of its root-free part. -/
def skeletonModel (s : ScalarCase) (P : Model) (w : Fin 10 ⊕ Fin 5 → Model) : Model :=
  Model.add config (Model.add config (Model.add config (Model.add config (Model.add config P
      ((nuI s*(ctI-1)).eval config w))
      (Model.neg ((radiusI*rootI 0).eval config w)))
      (Model.neg ((radiusI*rootI 1).eval config w)))
      (Model.neg ((radiusI*rootI 2).eval config w)))
      (Model.neg ((radiusI*rootI 3).eval config w))

theorem eval_add (a b : IExpr) (w : Fin 10 ⊕ Fin 5 → Model) :
    (a+b).eval config w=Model.add config (a.eval config w) (b.eval config w) := rfl
theorem eval_sub (a b : IExpr) (w : Fin 10 ⊕ Fin 5 → Model) :
    (a-b).eval config w=Model.add config (a.eval config w) (Model.neg (b.eval config w)) := rfl

theorem eval_skeleton (s : ScalarCase) (w : Fin 10 ⊕ Fin 5 → Model) :
    (skeleton s).eval config w=skeletonModel s ((rootFree s).eval config w) w := by
  rw [skeleton,eval_sub,eval_sub,eval_sub,eval_sub,eval_add]
  rfl

/-- `caseCheck` with the model `P` of the root-free part, the models and the root checks given. -/
def caseCheckWith (s : ScalarCase) (P : Model) (w : Fin 10 ⊕ Fin 5 → Model)
    (rc : Fin 5 → Bool → Bool) : Bool :=
  checkModel config 10 (skeletonModel s P w) 77 1000000 true && (skeleton s).poly &&
    (skeleton s).seedFree &&
    ([0,1,2,3,4] : List (Fin 5)).all fun i =>
      if i.val=s.negative.val then rc i true else rc i false

/-- The models of the inputs and of the roots without the cross term. -/
def plainModels (f : Family) (td atG : Bool) : Fin 10 ⊕ Fin 5 → Model :=
  Sum.elim (inputModels f atG) fun i => rootModel f td atG i false

/-- `caseCheck` with every model written in terms of the family, `td`, `atG` and the negative
index alone: the kernel caches its reductions by term, so it evaluates the input models, the root
models and the root-free part once for the cases that share them (the root-free part, whose root
does not depend on `td`, for both values of `td`). -/
def caseCheckShared (f : Family) (td atG : Bool) (neg : Fin 4) (h : Bool) : Bool :=
  caseCheckWith ⟨f,td,atG,neg,h⟩
    ((rootFree ⟨f,false,atG,0,false⟩).eval config (plainModels f false atG))
    (Sum.elim (inputModels f atG) fun i =>
      if i.val=neg.val then rootModel f td atG i true else rootModel f td atG i false)
    (rootCheck f td atG)

/-- `chunkCheck` by `caseCheckShared`. The H choice only enters at the negative index `0`, so
the other indices check the same term twice, and the kernel evaluates it once. -/
def chunkCheckShared (f : Family) (td : Bool) : Bool :=
  allBool fun atG =>
    (caseCheckShared f td atG 0 false && caseCheckShared f td atG 0 true) &&
    (caseCheckShared f td atG 1 false && caseCheckShared f td atG 1 false) &&
    (caseCheckShared f td atG 2 false && caseCheckShared f td atG 2 false) &&
    (caseCheckShared f td atG 3 false && caseCheckShared f td atG 3 false)

/-- Both `td` chunks of a family in one kernel check, which evaluates their common input models
and root-free parts once. -/
def familyCheckShared (f : Family) : Bool := chunkCheckShared f false && chunkCheckShared f true

theorem familyCheckShared_eq (f : Family) : familyCheckShared f=true := by
  cases f <;> decide +kernel

theorem rootSquareI_high (f : Family) (td : Bool) (i : Fin 5) (b : Bool) (hi : 4 ≤ i.val) :
    rootSquareI f td i b=rootSquareI f false i false := by
  unfold rootSquareI
  split_ifs <;> first | omega | rfl

/-- The root `4` does not depend on `td` or on the cross term. -/
theorem rootModel_high (f : Family) (td atG : Bool) (i : Fin 5) (b : Bool) (hi : 4 ≤ i.val) :
    rootModel f td atG i b=rootModel f false atG i false := by
  unfold rootModel seed
  rw [rootSquareI_high f td i b hi]

theorem caseCheck_of_shared (s : ScalarCase)
    (h : caseCheckWith s ((rootFree ⟨s.family,false,s.atG,0,false⟩).eval config
      (plainModels s.family false s.atG)) (models s) (rootCheck s.family s.td s.atG)=true) :
    caseCheck s=true := by
  have hw : ∀ k,rootFreeVar k=true → models s k=plainModels s.family false s.atG k := by
    rintro (k|i) hi
    · simp only [models,plainModels,Sum.elim_inl]
    · have h4 : 4 ≤ i.val := by simpa [rootFreeVar] using hi
      simp only [models,plainModels,Sum.elim_inr]
      rw [ite_eq_right (by have := s.negative.isLt; omega),rootModel_high _ _ _ _ _ h4]
  have hP : (rootFree s).eval config (models s)=(rootFree ⟨s.family,false,s.atG,0,false⟩).eval
      config (plainModels s.family false s.atG) :=
    (eval_congr config rootFreeVar hw (rootFree s)
      (rootFree_vars s.family s.td s.atG s.negative s.hCoefficient)).trans
      (congrArg (IE.eval config (plainModels s.family false s.atG)) (rootFree_case s).symm)
  have e : caseCheck s=caseCheckWith s ((rootFree s).eval config (models s)) (models s)
      (rootCheck s.family s.td s.atG) := by
    rw [caseCheckWith,← eval_skeleton]
    rfl
  rw [e,hP]
  exact h

theorem nuI_h (f : Family) (td atG : Bool) (neg : Fin 4) (hn : neg≠0) :
    nuI ⟨f,td,atG,neg,true⟩=nuI ⟨f,td,atG,neg,false⟩ := by
  fin_cases neg
  · exact absurd rfl hn
  all_goals rfl

theorem skeleton_h (f : Family) (td atG : Bool) (neg : Fin 4) (hn : neg≠0) :
    skeleton ⟨f,td,atG,neg,true⟩=skeleton ⟨f,td,atG,neg,false⟩ := by
  rw [skeleton,skeleton,nuI_h f td atG neg hn]
  rfl

/-- The H choice does not enter a case check at a nonzero negative index. -/
theorem caseCheckWith_h (f : Family) (td atG : Bool) (neg : Fin 4) (hn : neg≠0) (P : Model)
    (w : Fin 10 ⊕ Fin 5 → Model) (rc : Fin 5 → Bool → Bool) :
    caseCheckWith ⟨f,td,atG,neg,true⟩ P w rc=caseCheckWith ⟨f,td,atG,neg,false⟩ P w rc := by
  simp only [caseCheckWith,skeletonModel,skeleton_h f td atG neg hn,nuI_h f td atG neg hn]

theorem allBool_of {p : Bool → Bool} (h : ∀ b,p b=true) : allBool p=true := by
  simp only [allBool,h,Bool.and_self]
theorem allFin4_of {p : Fin 4 → Bool} (h : ∀ i,p i=true) : allFin4 p=true := by
  simp only [allFin4,h,Bool.and_self]

theorem chunk_check (f : Family) (td : Bool) : chunkCheck f td=true := by
  have h := familyCheckShared_eq f
  simp only [familyCheckShared,Bool.and_eq_true] at h
  have hc : chunkCheckShared f td=true := by
    cases td
    exacts [h.1,h.2]
  refine allBool_of fun atG => ?_
  have ha := allBool_eq hc atG
  simp only [Bool.and_eq_true] at ha
  obtain ⟨⟨⟨⟨h0,h0'⟩,h1,-⟩,h2,-⟩,h3,-⟩ := ha
  refine allFin4_of fun neg => allBool_of fun b => ?_
  fin_cases neg <;> cases b
  · exact caseCheck_of_shared _ h0
  · exact caseCheck_of_shared _ h0'
  · exact caseCheck_of_shared _ h1
  · exact caseCheck_of_shared _ ((caseCheckWith_h f td atG 1 (by decide) _ _ _).trans h1)
  · exact caseCheck_of_shared _ h2
  · exact caseCheck_of_shared _ ((caseCheckWith_h f td atG 2 (by decide) _ _ _).trans h2)
  · exact caseCheck_of_shared _ h3
  · exact caseCheck_of_shared _ ((caseCheckWith_h f td atG 3 (by decide) _ _ _).trans h3)

theorem case_check (s : ScalarCase) : caseCheck s=true :=
  allBool_eq (allFin4_eq (allBool_eq (chunk_check s.family s.td) s.atG) s.negative) s.hCoefficient

theorem tModel_contains {c : Config} (hc : c.Valid) (f : Family) {X Y : ℝ} (hX : |X|≤1)
    (hY : |Y|≤1) : (tModel c f).Contains c X Y (parameterValue f X) := by
  have h := Model.contains_add hc (Model.contains_lit c (center f).1 (center f).2)
    (Model.contains_mul hc hX hY
      (Model.contains_lit c (halfWidth f).1 (halfWidth f).2) (Model.contains_X hc X Y))
  rw [center_eq,halfWidth_eq] at h
  exact h

theorem zModel_contains {c : Config} (hc : c.Valid) (f : Family) {X Y : ℝ} (hX : |X|≤1)
    (hY : |Y|≤1) : (zModel c f).Contains c X Y (secondValue f X Y) := by
  have h := Model.contains_mul hc hX hY (Model.contains_mul hc hX hY
    (tModel_contains hc f hX hY)
    (Model.contains_add hc (Model.contains_one c X Y) (Model.contains_Y hc X Y)))
    (Model.contains_lit c 1 2)
  have e : secondValue f X Y=parameterValue f X*(1+Y)*(((1:ℤ):ℝ)/((2:ℕ):ℝ)) := by
    unfold secondValue; push_cast; ring
  rw [e]
  exact h

theorem zeroModel_contains (c : Config) (x y : ℝ) : (zeroModel c).Contains c x y 0 :=
  Model.contains_ofInt 0 0 true (by simp)

/-- The input models contain the inputs on the square. -/
theorem inputModels_contain (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    ∀ i,(inputModels s.family s.atG i).Contains config X Y
      (inputs s (parameterValue s.family X) (secondValue s.family X Y) i) := by
  have hc := config_valid
  have ht := parameter_mem s.family hX
  have hz := second_mem s.family hX hY
  have htm := tModel_contains hc s.family hX hY
  have hzm := zModel_contains hc s.family hX hY
  have hgm : (gapModel config s.family).Contains config X Y
      (parameterValue s.family X-secondValue s.family X Y) := by
    have h := Model.contains_add hc htm (Model.contains_neg hzm)
    rwa [← sub_eq_add_neg] at h
  have hxm : (if s.atG then gapModel config s.family else zeroModel config).Contains config X Y
      (x s (parameterValue s.family X) (secondValue s.family X Y)) := by
    unfold x
    split_ifs
    exacts [hgm,zeroModel_contains config X Y]
  have hem : (if s.atG then zeroModel config else gapModel config s.family).Contains config X Y
      (ExceptionalPositiveTScalarModel.e s (parameterValue s.family X) (secondValue s.family X Y)) := by
    unfold ExceptionalPositiveTScalarModel.e
    split_ifs
    exacts [zeroModel_contains config X Y,hgm]
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  intro i
  fin_cases i
  · exact htm
  · exact hzm
  · exact Model.contains_sin hc hX hY hxm hx
  · exact Model.contains_cos hc hX hY hxm hx
  · exact Model.contains_sin hc hX hY hzm hz'
  · exact Model.contains_cos hc hX hY hzm hz'
  · exact Model.contains_sin hc hX hY hem he
  · exact Model.contains_cos hc hX hY hem he
  · exact Model.contains_sin hc hX hY htm (angle ht)
  · exact Model.contains_cos hc hX hY htm (angle ht)

theorem value_zero (v : Fin 10 → ℝ) : Expression.value v (0 : Expr)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  simp

/-- The point models contain the constant coefficients of the input enclosures. -/
theorem pointModels_contain (s : ScalarCase) :
    ∀ k,(pointModels s.family s.atG k).Contains seedConfig 0 0
      ((inputFormulas k).value (r54v s)) := by
  have hc := seedConfig_valid
  have h0 : |(0:ℝ)|≤1 := by simp
  set M : ℝ := ((left s.family:ℝ)+(right s.family:ℝ))/2 with hM
  have hP : (r54κ (parameter s.family).polynomial:ℝ)=M := by
    rw [r54κ_parameter]; push_cast; ring
  have hS : (r54κ (secondParameter s.family).polynomial:ℝ)=M*(1/2) := by
    rw [r54κ_secondParameter]; push_cast; ring
  have hD : (r54κ (TensorPolynomialEnclosure.sub (parameter s.family)
      (secondParameter s.family)).polynomial:ℝ)=M+-(M*(1/2)) := by
    simp only [TensorPolynomialEnclosure.sub,TensorPolynomialEnclosure.add,
      TensorPolynomialEnclosure.neg,map_add,map_neg,Rat.cast_add,Rat.cast_neg,hP,hS]
  have h0κ : (r54κ (constant 0).polynomial:ℝ)=0 := by simp [r54κ_constant]
  have htm : (Model.lit seedConfig (center s.family).1 (center s.family).2).Contains
      seedConfig 0 0 M := by
    have h := Model.contains_lit seedConfig (center s.family).1 (center s.family).2 (x := 0) (y := 0)
    rwa [center_eq] at h
  have hzm : (Model.lit seedConfig (center s.family).1 (2*(center s.family).2)).Contains
      seedConfig 0 0 (M*(1/2)) := by
    have h := Model.contains_lit seedConfig (center s.family).1 (2*(center s.family).2)
      (x := 0) (y := 0)
    have e := center_eq s.family
    convert h using 1
    rw [← hM] at e
    push_cast at e ⊢
    rw [mul_comm (2:ℝ),← div_div,e]
    ring
  have hgm := Model.contains_add hc htm (Model.contains_neg hzm)
  have hxm : (if s.atG then Model.add seedConfig
      (Model.lit seedConfig (center s.family).1 (center s.family).2)
      (Model.neg (Model.lit seedConfig (center s.family).1 (2*(center s.family).2)))
      else zeroModel seedConfig).Contains seedConfig 0 0 (r54κ (xParameter s).polynomial:ℝ) := by
    unfold xParameter
    split_ifs
    · rw [hD]; exact hgm
    · rw [h0κ]; exact zeroModel_contains seedConfig 0 0
  have hem : (if s.atG then zeroModel seedConfig else Model.add seedConfig
      (Model.lit seedConfig (center s.family).1 (center s.family).2)
      (Model.neg (Model.lit seedConfig (center s.family).1 (2*(center s.family).2)))).Contains
      seedConfig 0 0 (r54κ (eParameter s).polynomial:ℝ) := by
    unfold eParameter
    split_ifs
    · rw [h0κ]; exact zeroModel_contains seedConfig 0 0
    · rw [hD]; exact hgm
  rintro (j|j)
  · fin_cases j
    · show (Model.lit seedConfig ((center s.family).1:ℤ) (center s.family).2).Contains seedConfig 0 0
        (r54κ (parameter s.family).polynomial:ℝ)
      rw [hP]; exact htm
    · show (Model.lit seedConfig ((center s.family).1:ℤ) (2*(center s.family).2)).Contains
        seedConfig 0 0 (r54κ (secondParameter s.family).polynomial:ℝ)
      rw [hS]; exact hzm
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0
        (r54κ (sine (xParameter s)).polynomial:ℝ)
      rw [r54κ_sine]; exact Model.contains_sinPoly hc h0 h0 hxm
    · show (Model.cosPoly seedConfig _).Contains seedConfig 0 0
        (r54κ (cosine (xParameter s)).polynomial:ℝ)
      rw [r54κ_cosine]; exact Model.contains_cosPoly hc h0 h0 hxm
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0
        (r54κ (sine (secondParameter s.family)).polynomial:ℝ)
      rw [r54κ_sine,hS]; exact Model.contains_sinPoly hc h0 h0 hzm
    · show (Model.cosPoly seedConfig _).Contains seedConfig 0 0
        (r54κ (cosine (secondParameter s.family)).polynomial:ℝ)
      rw [r54κ_cosine,hS]; exact Model.contains_cosPoly hc h0 h0 hzm
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0
        (r54κ (sine (eParameter s)).polynomial:ℝ)
      rw [r54κ_sine]; exact Model.contains_sinPoly hc h0 h0 hem
    · show (Model.cosPoly seedConfig _).Contains seedConfig 0 0
        (r54κ (cosine (eParameter s)).polynomial:ℝ)
      rw [r54κ_cosine]; exact Model.contains_cosPoly hc h0 h0 hem
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0
        (r54κ (sine (parameter s.family)).polynomial:ℝ)
      rw [r54κ_sine,hP]; exact Model.contains_sinPoly hc h0 h0 htm
    · show (Model.cosPoly seedConfig _).Contains seedConfig 0 0
        (r54κ (cosine (parameter s.family)).polynomial:ℝ)
      rw [r54κ_cosine,hP]; exact Model.contains_cosPoly hc h0 h0 htm
  · show (zeroModel seedConfig).Contains seedConfig 0 0 (Expression.value (r54v s) 0)
    rw [value_zero]
    exact zeroModel_contains seedConfig 0 0

theorem rootCheck_eq (s : ScalarCase) (i : Fin 5) :
    rootCheck s.family s.td s.atG i (isNegative s i)=true := by
  have hc := case_check s
  simp only [caseCheck,Bool.and_eq_true,List.all_eq_true] at hc
  have h := hc.2 i (by fin_cases i <;> simp)
  unfold isNegative
  split_ifs at h with hi
  · simpa [hi] using h
  · simpa [hi] using h

theorem seed_eq (s : ScalarCase) (i : Fin 5) :
    rootSeed (Expression.enclose («variables» s) (rootSquare s i))=
      (seed s.family s.td s.atG i (isNegative s i):ℚ)/100000000 := by
  have h := rootCheck_eq s i
  simp only [rootCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨hs,hf⟩,hp⟩,-⟩ := h
  have hval : Expression.value (r54v s) (rootSquare s i)=
      (r54κ (Expression.enclose («variables» s) (rootSquare s i)).polynomial:ℝ) :=
    (r54κ_enclose _ _).symm
  have hI : (rootSquareI s.family s.td i (isNegative s i)).value (fun k => (inputFormulas k).value (r54v s))=
      Expression.value (r54v s) (rootSquare s i) := by
    rw [← rootSquareI_eq s i,IE.value_toExpressionWith _ _ _ (IE.isPoly_of_poly _ hp)]
  rw [r54_rootSeed_eq]
  apply seedCheck_sound seedConfig_valid hs (pointModels_contain s) (IE.seedsOK_of_seedFree _ hf)
    (by rw [hI,hval])
  have h := r54_rootSquare_lower s i
  rw [hval] at h
  have h' : (0:ℝ)≤(r54κ (Expression.enclose («variables» s) (rootSquare s i)).polynomial:ℝ) := by
    linarith
  exact_mod_cast h'

/-- The root models contain the roots on the square. -/
theorem rootModel_contains (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) (i : Fin 5) :
    (rootModel s.family s.td s.atG i (isNegative s i)).Contains config X Y
      (Expression.value (inputs s (parameterValue s.family X) (secondValue s.family X Y))
        (rootExpression s i)) := by
  set v := inputs s (parameterValue s.family X) (secondValue s.family X Y)
  have h := rootCheck_eq s i
  simp only [rootCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨-,hf⟩,-⟩,hp⟩ := h
  have hw : ∀ k,((Sum.elim (inputModels s.family s.atG) fun _ => zeroModel config) k).Contains
      config X Y ((inputFormulas k).value v) := by
    rintro (k|k)
    · exact inputModels_contain s hX hY k
    · show (zeroModel config).Contains config X Y (Expression.value v 0)
      rw [value_zero]; exact zeroModel_contains config X Y
  set a := rootSquareI s.family s.td i (isNegative s i)
  have hs : (IE.sqrtUpper (rootSeed (Expression.enclose («variables» s) (rootSquare s i)))
      (seed s.family s.td s.atG i (isNegative s i)) a).SeedsOK :=
    IE.seedsOK_sqrtUpper (seed_eq s i) (IE.seedsOK_of_seedFree _ hf)
  have hc := IE.eval_sound config_valid hX hY hw _ hs
  have hpoly : (IE.sqrtUpper (rootSeed (Expression.enclose («variables» s) (rootSquare s i)))
      (seed s.family s.td s.atG i (isNegative s i)) a).IsPoly :=
    IE.isPoly_of_poly _ hp
  have hv := IE.value_toExpressionWith v inputFormulas _ hpoly
  have he : (IE.sqrtUpper (rootSeed (Expression.enclose («variables» s) (rootSquare s i)))
      (seed s.family s.td s.atG i (isNegative s i)) a).toExpressionWith inputFormulas=
      rootExpression s i := by
    rw [rootExpression,← rootSquareI_eq s i]
    exact IE.toExpressionWith_sqrtUpper _ _ _ _
  rw [he] at hv
  rw [hv]
  rw [IE.eval_sqrtUpper config _ _ 0] at hc
  exact hc

theorem models_contain (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    ∀ k,(models s k).Contains config X Y
      ((formulas s k).value (inputs s (parameterValue s.family X) (secondValue s.family X Y))) := by
  rintro (k|i)
  · exact inputModels_contain s hX hY k
  · have h := rootModel_contains s hX hY i
    show (if i.val=s.negative.val then rootModel s.family s.td s.atG i true
      else rootModel s.family s.td s.atG i false).Contains config X Y _
    unfold isNegative at h
    split_ifs with hi
    · rw [decide_eq_true hi] at h; exact h
    · rw [decide_eq_false hi] at h; exact h

end packed

theorem model_positive (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    (77/1000000:ℝ)<Expression.value
      (inputs s (parameterValue s.family X) (secondValue s.family X Y)) (expression s) := by
  have hc := case_check s
  simp only [caseCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hm,hp⟩,hf⟩,-⟩ := hc
  have h := PackedModels.check_lt config_valid hm hX hY (models_contain s hX hY)
    (PackedModels.IE.seedsOK_of_seedFree _ hf)
  rw [← skeleton_eq,PackedModels.IE.value_toExpressionWith _ _ _ (PackedModels.IE.isPoly_of_poly _ hp)]
  push_cast at h
  exact h

end SquaresInCircles.Eight.ExceptionalPositiveTPolynomials
