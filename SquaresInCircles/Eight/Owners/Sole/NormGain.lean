module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Owners.OccupiedSignedConcentration
public import SquaresInCircles.Eight.Owners.Sole.PositiveTScalar

/-!
# Eight squares: actual coefficient comparisons for the negative norm gain

The gain is differentiated in its larger coefficient
on the complete interval between the two actual coefficients. The short
angle estimate follows from a monotone normalized integrand on one
rectangle. Its far-angle counterpart uses the actual negative norm.
-/

section
/-!
## Whole-square coefficient correlations for the positive-T envelope

These are coefficient inequalities for the same five
analytic families as the scalar theorem. Their rational reductions use
the complete square and the existing enclosure arithmetic. The weak
upper bounds include constant coefficients which equal their cap.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTCoefficients
section r64_bernstein
open Polynomial Finset TensorWholeIntervalPolynomial

/-! Degree-`D` Bernstein re-expansion of a bivariate polynomial whose degrees in both
variables are at most `D`, and the degree bound `14` of every enclosure polynomial.
(The same private lemmas are in `SolePositiveTPolynomials`.) -/

section generic
variable {R : Type*} [CommRing R]

private theorem r64_pow_bern (φ : ℚ →+* R) (u : R) {D k : ℕ} (hk : k ≤ D) :
    u^k=∑ i ∈ range (D+1),φ ((i.choose k : ℚ)/(D.choose k : ℚ))*
      ((D.choose i : R)*u^i*(1-u)^(D-i)) := by
  rw [← sum_range_add_sum_Ico _ (show k ≤ D+1 by omega)]
  have h0 : ∑ i ∈ range k,φ ((i.choose k : ℚ)/(D.choose k : ℚ))*
      ((D.choose i : R)*u^i*(1-u)^(D-i))=0 := by
    apply sum_eq_zero
    intro i hi
    rw [Nat.choose_eq_zero_of_lt (mem_range.1 hi)]
    simp
  rw [h0,zero_add,sum_Ico_eq_sum_range]
  have hD : (D.choose k : ℚ)≠0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have key : ∀ m ∈ range (D+1-k),φ (((k+m).choose k : ℚ)/(D.choose k : ℚ))*
      ((D.choose (k+m) : R)*u^(k+m)*(1-u)^(D-(k+m)))=
      u^k*(u^m*(1-u)^(D-k-m)*((D-k).choose m : R)) := by
    intro m hm
    have hm' : m ≤ D-k := by simp at hm; omega
    have hchoose : ((D.choose (k+m) : ℚ)*((k+m).choose k : ℚ))=
        (D.choose k : ℚ)*((D-k).choose m : ℚ) := by
      have h := Nat.choose_mul (n := D) (k := k+m) (s := k) (by omega)
      rw [show k+m-k=m by omega] at h
      exact_mod_cast h
    have hcoef : φ (((k+m).choose k : ℚ)/(D.choose k : ℚ))*(D.choose (k+m) : R)=
        ((D-k).choose m : R) := by
      rw [← map_natCast φ (D.choose (k+m)),← map_mul,← map_natCast φ ((D-k).choose m)]
      congr 1
      field_simp
      linarith [hchoose]
    rw [show D-(k+m)=D-k-m by omega,pow_add]
    calc _=(φ (((k+m).choose k : ℚ)/(D.choose k : ℚ))*(D.choose (k+m) : R))*
          (u^k*u^m)*(1-u)^(D-k-m) := by ring
      _=_ := by rw [hcoef]; ring
  rw [sum_congr rfl key,← mul_sum]
  have h := (add_pow u (1-u) (D-k)).symm
  rw [add_sub_cancel,one_pow,show D-k+1=D+1-k by omega] at h
  rw [h,mul_one]

/-- The Bernstein coefficients of `x^a` on `[-1,1]`. -/
private def r64_beta (D a i : ℕ) : ℚ :=
  ∑ k ∈ range (i+1),(if k ≤ a then (2:ℚ)^k*(-1)^(a-k)*(a.choose k : ℚ) else 0)*
    ((i.choose k : ℚ)/(D.choose k : ℚ))

private theorem r64_beta_eq {D a i : ℕ} (ha : a ≤ D) (hi : i ≤ D) :
    r64_beta D a i=∑ k ∈ range (a+1),(2:ℚ)^k*(-1)^(a-k)*(a.choose k : ℚ)*
      ((i.choose k : ℚ)/(D.choose k : ℚ)) := by
  have h1 : r64_beta D a i=∑ k ∈ range (D+1),(if k ≤ a then (2:ℚ)^k*(-1)^(a-k)*(a.choose k : ℚ) else 0)*
      ((i.choose k : ℚ)/(D.choose k : ℚ)) := by
    unfold r64_beta
    apply sum_subset (range_subset_range.2 (by omega))
    intro k hk hk'
    rw [Nat.choose_eq_zero_of_lt (n := i) (k := k) (by simp at hk'; omega)]
    simp
  rw [h1]
  simp only [ite_mul,zero_mul]
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [mem_filter,mem_range]
  omega

private theorem r64_mono_bern (φ : ℚ →+* R) (x : R) {D a : ℕ} (ha : a ≤ D) :
    x^a=∑ i ∈ range (D+1),φ (r64_beta D a i)*((D.choose i : R)*(φ (1/2)*(x+1))^i*
      (1-φ (1/2)*(x+1))^(D-i)) := by
  obtain ⟨u,hu⟩ : ∃ u : R,u=φ (1/2)*(x+1) := ⟨_,rfl⟩
  rw [← hu]
  have hx : x=2*u+(-1) := by
    rw [hu,← mul_assoc]
    have : (2:R)*φ (1/2)=1 := by
      rw [← map_ofNat φ 2,← map_mul]
      norm_num
    rw [this]
    ring
  have hexp : x^a=∑ k ∈ range (a+1),φ ((2:ℚ)^k*(-1)^(a-k)*(a.choose k : ℚ))*u^k := by
    rw [hx,add_pow]
    apply sum_congr rfl
    intro k _
    simp only [map_mul,map_pow,map_neg,map_one,map_natCast,map_ofNat]
    ring
  rw [hexp]
  have hk : ∀ k ∈ range (a+1),φ ((2:ℚ)^k*(-1)^(a-k)*(a.choose k : ℚ))*u^k=
      ∑ i ∈ range (D+1),φ ((2:ℚ)^k*(-1)^(a-k)*(a.choose k : ℚ)*
        ((i.choose k : ℚ)/(D.choose k : ℚ)))*((D.choose i : R)*u^i*(1-u)^(D-i)) := by
    intro k hk
    rw [r64_pow_bern φ u (show k ≤ D by simp at hk; omega),mul_sum]
    apply sum_congr rfl
    intro i _
    simp only [map_mul]
    ring
  rw [sum_congr rfl hk,sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [← sum_mul,r64_beta_eq ha (by simp at hi; omega),map_sum]

end generic

private theorem r64_sum_comm4 {M α β γ δ : Type*} [AddCommMonoid M] (K : Finset α) (L : Finset β)
    (A : Finset γ) (B : Finset δ) (f : α → β → γ → δ → M) :
    ∑ k ∈ K,∑ l ∈ L,∑ a ∈ A,∑ b ∈ B,f k l a b=∑ a ∈ A,∑ b ∈ B,∑ k ∈ K,∑ l ∈ L,f k l a b := by
  calc _=∑ k ∈ K,∑ a ∈ A,∑ l ∈ L,∑ b ∈ B,f k l a b := sum_congr rfl (fun _ _ => sum_comm)
    _=∑ k ∈ K,∑ a ∈ A,∑ b ∈ B,∑ l ∈ L,f k l a b :=
      sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => sum_comm))
    _=∑ a ∈ A,∑ k ∈ K,∑ b ∈ B,∑ l ∈ L,f k l a b := sum_comm
    _=_ := sum_congr rfl (fun _ _ => sum_comm)

/-- The scalar embedding as a ring homomorphism. -/
private def r64_sigma : ℚ →+* Bivar := (C : ℚ[X] →+* Bivar).comp (C : ℚ →+* ℚ[X])

private theorem r64_scalar_eq (r : ℚ) : scalar r=r64_sigma r := rfl

private theorem r64_shifted_eq (D : ℕ) (p : Bivar) (k l : ℕ) :
    TensorWholeIntervalBernstein.shiftedCoefficient D p k l=
      ∑ a ∈ range (D+1),∑ b ∈ range (D+1),
        (if k ≤ a then (2:ℚ)^k*(-1)^(a-k)*(a.choose k : ℚ) else 0)*
        (if l ≤ b then (2:ℚ)^l*(-1)^(b-l)*(b.choose l : ℚ) else 0)*((p.coeff a).coeff b) := by
  unfold TensorWholeIntervalBernstein.shiftedCoefficient
  rw [mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => 2^(k+l)*∑ j : Fin (D+1),
    if k ≤ a ∧ l ≤ j.val then (-1:ℚ)^(a+j.val-k-l)*(a.choose k : ℚ)*(j.val.choose l : ℚ)*
      ((p.coeff a).coeff j.val) else 0) (D+1)]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun b => 2^(k+l)*
    if k ≤ a ∧ l ≤ b then (-1:ℚ)^(a+b-k-l)*(a.choose k : ℚ)*(b.choose l : ℚ)*
      ((p.coeff a).coeff b) else 0) (D+1)]
  apply sum_congr rfl
  intro b _
  by_cases hk : k ≤ a <;> by_cases hl : l ≤ b <;> simp only [hk,hl,and_self,and_true,
    and_false,↓reduceIte,mul_zero,zero_mul]
  rw [show a+b-k-l=(a-k)+(b-l) by omega,pow_add,pow_add]
  ring

private theorem r64_coefficient_eq (D : ℕ) (p : Bivar) (i j : Fin (D+1)) :
    TensorWholeIntervalBernstein.coefficient D p i j=
      ∑ a ∈ range (D+1),∑ b ∈ range (D+1),
        (p.coeff a).coeff b*r64_beta D a i*r64_beta D b j := by
  unfold TensorWholeIntervalBernstein.coefficient
  simp only [r64_shifted_eq,r64_beta,sum_mul,mul_sum]
  rw [r64_sum_comm4]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl; intro k _
  apply sum_congr rfl; intro l _
  ring

private theorem r64_poly_sum {D : ℕ} {p : Bivar}
    (hp : ∀ a b,(D < a ∨ D < b) → (p.coeff a).coeff b=0) :
    p=∑ a ∈ range (D+1),∑ b ∈ range (D+1),r64_sigma ((p.coeff a).coeff b)*X^a*(C X)^b := by
  have hdeg : p.natDegree < D+1 := by
    have h : p.natDegree ≤ D := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      ext b
      simpa using hp N b (Or.inl hN)
    omega
  conv_lhs => rw [as_sum_range_C_mul_X_pow' p hdeg]
  apply sum_congr rfl
  intro a _
  have hdeg' : (p.coeff a).natDegree < D+1 := by
    have h : (p.coeff a).natDegree ≤ D := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      exact hp a N (Or.inr hN)
    omega
  conv_lhs => rw [as_sum_range_C_mul_X_pow' (p.coeff a) hdeg']
  rw [map_sum,sum_mul]
  apply sum_congr rfl
  intro b _
  simp only [r64_sigma,RingHom.coe_comp,Function.comp_apply,map_mul,map_pow]
  ring

private theorem r64_expansion_eq {D : ℕ} {p : Bivar}
    (hp : ∀ a b,(D < a ∨ D < b) → (p.coeff a).coeff b=0) :
    p=TensorWholeIntervalBernstein.expansion D p := by
  have hX : ∀ a ∈ range (D+1),(X:Bivar)^a=∑ i ∈ range (D+1),r64_sigma (r64_beta D a i)*
      ((D.choose i : Bivar)*TensorWholeIntervalBernstein.left^i*
        (1-TensorWholeIntervalBernstein.left)^(D-i)) := fun a ha =>
    r64_mono_bern r64_sigma X (by simp at ha; omega)
  have hY : ∀ b ∈ range (D+1),(C X:Bivar)^b=∑ j ∈ range (D+1),r64_sigma (r64_beta D b j)*
      ((D.choose j : Bivar)*TensorWholeIntervalBernstein.right^j*
        (1-TensorWholeIntervalBernstein.right)^(D-j)) := fun b hb =>
    r64_mono_bern r64_sigma (C X) (by simp at hb; omega)
  conv_lhs => rw [r64_poly_sum hp]
  unfold TensorWholeIntervalBernstein.expansion
  have hstep : ∀ a ∈ range (D+1),∀ b ∈ range (D+1),
      r64_sigma ((p.coeff a).coeff b)*X^a*(C X)^b=
        ∑ i : Fin (D+1),∑ j : Fin (D+1),r64_sigma ((p.coeff a).coeff b)*
          (r64_sigma (r64_beta D a i)*((D.choose i : Bivar)*TensorWholeIntervalBernstein.left^(i:ℕ)*
            (1-TensorWholeIntervalBernstein.left)^(D-i)))*
          (r64_sigma (r64_beta D b j)*((D.choose j : Bivar)*TensorWholeIntervalBernstein.right^(j:ℕ)*
            (1-TensorWholeIntervalBernstein.right)^(D-j))) := by
    intro a ha b hb
    rw [hX a ha,hY b hb,← Fin.sum_univ_eq_sum_range (fun i => r64_sigma (r64_beta D a i)*
      ((D.choose i : Bivar)*TensorWholeIntervalBernstein.left^i*
        (1-TensorWholeIntervalBernstein.left)^(D-i))),
      ← Fin.sum_univ_eq_sum_range (fun j => r64_sigma (r64_beta D b j)*
      ((D.choose j : Bivar)*TensorWholeIntervalBernstein.right^j*
        (1-TensorWholeIntervalBernstein.right)^(D-j))),mul_assoc,sum_mul_sum,mul_sum]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [sum_congr rfl (fun a ha => sum_congr rfl (fun b hb => hstep a ha b hb)),r64_sum_comm4]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [r64_coefficient_eq,r64_scalar_eq,map_sum,sum_mul]
  apply sum_congr rfl
  intro a _
  rw [map_sum,sum_mul]
  apply sum_congr rfl
  intro b _
  simp only [TensorWholeIntervalBernstein.basis,r64_scalar_eq,map_mul,map_natCast]
  ring

/-! Every enclosure polynomial has degree at most 14 in each variable. -/

private def r64_Low (p : Bivar) : Prop := ∀ a b,(14 < a ∨ 14 < b) → (p.coeff a).coeff b=0

private theorem r64_low_scalar (r : ℚ) : r64_Low (scalar r) := by
  intro a b h
  simp only [scalar,coeff_C]
  split_ifs with ha
  · simp only [coeff_C]
    split_ifs with hb
    · omega
    · rfl
  · rfl

private theorem r64_low_add {p q : Bivar} (hp : r64_Low p) (hq : r64_Low q) : r64_Low (p+q) := by
  intro a b h
  simp [hp a b h,hq a b h]

private theorem r64_low_neg {p : Bivar} (hp : r64_Low p) : r64_Low (-p) := by
  intro a b h
  simp [hp a b h]

private theorem r64_low_sum {ι : Type*} (s : Finset ι) (f : ι → Bivar) (hf : ∀ i,r64_Low (f i)) :
    r64_Low (∑ i ∈ s,f i) := by
  intro a b h
  simp only [finsetSum_coeff]
  exact sum_eq_zero (fun i _ => hf i a b h)

private theorem r64_low_monomial (c : ℚ) (i j : ℕ) (hi : i ≤ 14) (hj : j ≤ 14) :
    r64_Low (scalar c*X^i*(C X)^j) := by
  intro a b h
  have he : scalar c*X^i*(C X:Bivar)^j=C (C c*X^j)*X^i := by
    simp only [scalar,map_mul,map_pow]
    ring
  rw [he,coeff_C_mul_X_pow]
  split_ifs with ha
  · rw [coeff_C_mul_X_pow]
    split_ifs with hb
    · omega
    · rfl
  · rfl

private theorem r64_low_truncate (p : Bivar) : r64_Low (TensorPolynomialEnclosure.truncate p) := by
  unfold TensorPolynomialEnclosure.truncate
  apply r64_low_sum
  intro i
  apply r64_low_sum
  intro j
  split_ifs
  · exact r64_low_monomial _ _ _ (by omega) (by omega)
  · intro a b _
    simp

open TensorPolynomialEnclosure in
private theorem r64_low_mul (a b : Enclosure) : r64_Low (TensorPolynomialEnclosure.mul a b).polynomial :=
  r64_low_truncate _

open TensorPolynomialEnclosure in
private theorem r64_low_power (a : Enclosure) (n : ℕ) : r64_Low (power a n).polynomial := by
  rw [TensorPolynomialEnclosure.power]
  split_ifs
  · exact r64_low_scalar 1
  · exact r64_low_mul _ _
  · exact r64_low_mul _ _

open TensorPolynomialEnclosure in
private theorem r64_low_sine (a : Enclosure) : r64_Low (sine a).polynomial := by
  unfold TensorPolynomialEnclosure.sine TensorPolynomialEnclosure.widen TensorPolynomialEnclosure.sum
  dsimp only
  exact r64_low_sum _ _ (fun _ => r64_low_mul _ _)

open TensorPolynomialEnclosure in
private theorem r64_low_cosine (a : Enclosure) : r64_Low (cosine a).polynomial := by
  unfold TensorPolynomialEnclosure.cosine TensorPolynomialEnclosure.widen TensorPolynomialEnclosure.sum
  dsimp only
  exact r64_low_sum _ _ (fun _ => r64_low_mul _ _)

open TensorPolynomialEnclosure in
private theorem r64_low_enclose {ι : Type*} (v : ι → Enclosure) (hv : ∀ i,r64_Low (v i).polynomial)
    (e : Expression ι) : r64_Low (Expression.enclose v e).polynomial := by
  induction e with
  | literal r => exact r64_low_scalar r
  | «variable» i => exact hv i
  | add a b ha hb => exact r64_low_add ha hb
  | neg a ha => exact r64_low_neg ha
  | mul a b _ _ => exact r64_low_mul _ _
  | power a n _ => exact r64_low_power _ n

private theorem r64_expansion_of_low {p : Bivar} (hp : r64_Low p) :
    p=TensorWholeIntervalBernstein.expansion 16 p :=
  r64_expansion_eq (fun a b h => hp a b (by omega))

end r64_bernstein


open SoleTScalarModel SolePositiveTPolynomials TensorPolynomialEnclosure
open TensorWholeIntervalPolynomial

section r64_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
@[simp] private theorem r64_value_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
@[simp] private theorem r64_value_neg : Expression.value v (-a)=-Expression.value v a := rfl
@[simp] private theorem r64_value_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
@[simp] private theorem r64_value_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
@[simp] private theorem r64_value_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
end r64_value

@[simp] private theorem r64_value_lit (w : Fin 11 → ℝ) (r : ℚ) :
    Expression.value w (lit r)=(r:ℝ) := rfl
@[simp] private theorem r64_value_var (w : Fin 11 → ℝ) (i : Fin 11) :
    Expression.value w (var i)=w i := rfl
@[simp] private theorem r64_inputs_0 (s : ScalarCase) (t z : ℝ) :
    SolePositiveTPolynomials.inputs s t z 0=t := rfl

def cap : Family → ℚ
  | .ehLow => 21/20
  | .ehMiddle => 111/100
  | .ehHigh => 1131/1000
  | .deLow | .deHigh => 5/4

def largeFloor : Family → ℚ
  | .ehLow => 431/500
  | .ehMiddle => 923/1000
  | _ => 0

def smallFloor : Family → ℚ
  | .ehHigh => 149/200
  | .deHigh => 749/1000
  | _ => 0

def ratioE (f : Family) (i : Fin 4) : Expr :=
  match f with
  | .ehLow => lit (117/200)+lit (3/10)*tE
  | .ehMiddle => lit (13/20)
  | .ehHigh | .deHigh => lit (18/25)
  | .deLow => if i=1 then lit (533/1000)
      else if i=2 then lit (5/8)+lit (27/100)*tE else lit (18/25)

def witnessE (s : ScalarCase) (i : Fin 4) : Expr :=
  if i=2 then secondE s i else firstE s i

inductive Test where
  | ratioFirst (i : Fin 4)
  | ratioSecond (i : Fin 4)
  | upperFirst (i : Fin 4)
  | upperSecond (i : Fin 4)
  | larger (i : Fin 4)
  | smallerFirst (i : Fin 4)
  | smallerSecond (i : Fin 4)
  | mixedB | deAUpper | deALower | DFirstUpper | DSecondUpper
  deriving DecidableEq

instance : Fintype Test where
  elems := {.mixedB, .deAUpper, .deALower, .DFirstUpper, .DSecondUpper} ∪
    Finset.univ.image Test.ratioFirst ∪
    Finset.univ.image Test.ratioSecond ∪
    Finset.univ.image Test.upperFirst ∪
    Finset.univ.image Test.upperSecond ∪
    Finset.univ.image Test.larger ∪
    Finset.univ.image Test.smallerFirst ∪
    Finset.univ.image Test.smallerSecond
  complete x := by
    cases x <;> first | decide | (rename_i i; fin_cases i <;> decide)

def test (s : ScalarCase) : Test → Expr
  | .ratioFirst i => firstE s i-ratioE s.family i*secondE s i
  | .ratioSecond i => secondE s i-ratioE s.family i*firstE s i
  | .upperFirst i => lit (cap s.family)-firstE s i
  | .upperSecond i => lit (cap s.family)-secondE s i
  | .larger i => witnessE s i-lit (largeFloor s.family)
  | .smallerFirst i => firstE s i-lit (smallFloor s.family)
  | .smallerSecond i => secondE s i-lit (smallFloor s.family)
  | .mixedB => mE s-ellE s.family
  | .deAUpper => if s.family=.deLow then lit (81/100)*kE s.family-ellE s.family else 0
  | .deALower => if s.family=.deLow then ellE s.family-lit (113/200) else 0
  | .DFirstUpper => lit (1131/1000)-firstE s 3
  | .DSecondUpper => lit (1131/1000)-secondE s 3

/-- These expressions do not depend on the later negative index. -/
def canonical (s : ScalarCase) : ScalarCase := { s with negative := 0 }

def testEnclosure (s : ScalarCase) (j : Test) : Enclosure :=
  Expression.enclose («variables» (canonical s)) (test (canonical s) j)

theorem identity (f : Family) (td atG : Bool) (j : Test) :
    (testEnclosure ⟨f,td,atG,0⟩ j).polynomial=
      TensorWholeIntervalBernstein.expansion 16 (testEnclosure ⟨f,td,atG,0⟩ j).polynomial := by
  have hv : ∀ i,r64_Low ((«variables» (canonical ⟨f,td,atG,0⟩)) i).polynomial := by
    intro i
    fin_cases i
    · exact r64_low_add (r64_low_scalar _) (r64_low_mul _ _)
    · exact r64_low_mul _ _
    · exact r64_low_sine _
    · exact r64_low_cosine _
    · exact r64_low_sine _
    · exact r64_low_cosine _
    · exact r64_low_sine _
    · exact r64_low_cosine _
    · exact r64_low_sine _
    · exact r64_low_cosine _
    · exact r64_low_sine _
  exact r64_expansion_of_low (r64_low_enclose _ hv _)

/-! ### The packed certificate

Each test is mirrored by an `IE` expression, evaluated by the packed Taylor models of
`SolePositiveTPolynomials` (at total degree `10`), and the kernel checks that its degree-12
Bernstein coefficients are nonnegative, in natural-number arithmetic. Three tests vanish at a
corner of the square (`tight`); they are affine and are checked directly. -/

section packed
open PackedModels

def capI : Family → IExpr
  | .ehLow => lq 21 20
  | .ehMiddle => lq 111 100
  | .ehHigh => lq 1131 1000
  | .deLow | .deHigh => lq 5 4
def largeFloorI : Family → IExpr
  | .ehLow => lq 431 500
  | .ehMiddle => lq 923 1000
  | _ => .lit (.num 0)
def smallFloorI : Family → IExpr
  | .ehHigh => lq 149 200
  | .deHigh => lq 749 1000
  | _ => .lit (.num 0)
def ratioI (f : Family) (i : Fin 4) : IExpr :=
  match f with
  | .ehLow => lq 117 200+lq 3 10*tI
  | .ehMiddle => lq 13 20
  | .ehHigh | .deHigh => lq 18 25
  | .deLow => if i=1 then lq 533 1000
      else if i=2 then lq 5 8+lq 27 100*tI else lq 18 25
def witnessI (f : Family) (td : Bool) (i : Fin 4) : IExpr :=
  if i=2 then secondI f td i else firstI f i
def testI (f : Family) (td : Bool) : Test → IExpr
  | .ratioFirst i => firstI f i-ratioI f i*secondI f td i
  | .ratioSecond i => secondI f td i-ratioI f i*firstI f i
  | .upperFirst i => capI f-firstI f i
  | .upperSecond i => capI f-secondI f td i
  | .larger i => witnessI f td i-largeFloorI f
  | .smallerFirst i => firstI f i-smallFloorI f
  | .smallerSecond i => secondI f td i-smallFloorI f
  | .mixedB => mI f-ellI f
  | .deAUpper => if f=.deLow then lq 81 100*kI f-ellI f else 0
  | .deALower => if f=.deLow then ellI f-lq 113 200 else 0
  | .DFirstUpper => lq 1131 1000-firstI f 3
  | .DSecondUpper => lq 1131 1000-secondI f td 3

theorem testI_eq (f : Family) (td atG : Bool) (j : Test) :
    (testI f td j).toExpressionWith inputFormulas=test ⟨f,td,atG,0⟩ j := by
  cases f <;> cases td <;> rcases j with (i|i|i|i|i|i|i|_|_|_|_|_) <;> (try fin_cases i) <;> rfl

/-- The thirty-three tests. -/
def allTests : List Test :=
  ([0,1,2,3] : List (Fin 4)).flatMap (fun i => [.ratioFirst i,.ratioSecond i,.upperFirst i,
    .upperSecond i,.larger i,.smallerFirst i,.smallerSecond i])++
    [.mixedB,.deAUpper,.deALower,.DFirstUpper,.DSecondUpper]

theorem mem_allTests (j : Test) : j∈allTests := by
  rcases j with (i|i|i|i|i|i|i|_|_|_|_|_) <;> (try fin_cases i) <;> decide

/-- The tests whose minimum on the square is zero. -/
def tight : Family → Test → Bool
  | .deHigh,.smallerFirst 2 | .deHigh,.smallerSecond 1 | .deLow,.deALower => true
  | _,_ => false

/-- The tests run at scale `2 ^ 48` with total degree `10`. -/
def testConfig : Config := ⟨48,10,116⟩

theorem testConfig_valid : testConfig.Valid := ⟨by decide,by decide⟩

/-- The models of the inputs (the roots do not occur). -/
def testModels (f : Family) (atG : Bool) : Fin 11 ⊕ Fin 7 → Model :=
  Sum.elim (inputModels testConfig f atG) fun _ => zeroModel testConfig

/-- Everything the kernel checks for one test. -/
def testCheck (f : Family) (td atG : Bool) (j : Test) : Bool :=
  tight f j || (check testConfig 12 (testModels f atG) (testI f td j) 0 1 false &&
    (testI f td j).poly && (testI f td j).seedFree)

theorem tests_check (f : Family) (td atG : Bool) : allTests.all (testCheck f td atG)=true := by
  cases f <;> cases td <;> cases atG <;> decide +kernel

theorem tight_nonneg (f : Family) (td atG : Bool) (j : Test) (h : tight f j=true) {X Y : ℝ}
    (hX : |X|≤1) (hY : |Y|≤1) :
    0≤Expression.value (inputs ⟨f,td,atG,0⟩ (parameterValue f X) (secondValue f X Y))
      (test ⟨f,td,atG,0⟩ j) := by
  have ht := parameter_mem f hX
  have hz := second_mem f hX hY
  set t := parameterValue f X
  set z := secondValue f X Y
  cases f <;> rcases j with (i|i|i|i|i|i|i|_|_|_|_|_) <;> (try fin_cases i) <;>
    simp [tight] at h
  · change 0≤Expression.value (inputs ⟨.deLow,td,atG,0⟩ t z) (ellE .deLow)+
      -((113/200:ℚ):ℝ)
    rw [SolePositiveTScalar.ellE_value]
    simp only [domain,left,right,Set.mem_Icc] at ht hz
    simp only [ell,L]
    push_cast at ht ⊢
    linarith [ht.1,hz.2]
  · change 0≤Expression.value (inputs ⟨.deHigh,td,atG,0⟩ t z) (ellE .deHigh)+
      -((smallFloor .deHigh:ℚ):ℝ)
    rw [SolePositiveTScalar.ellE_value]
    simp only [domain,left,right,Set.mem_Icc] at ht hz
    simp only [ell,L,smallFloor]
    push_cast at ht ⊢
    linarith [ht.2,hz.2]
  · change 0≤Expression.value (inputs ⟨.deHigh,td,atG,0⟩ t z) (ellE .deHigh)+
      -((smallFloor .deHigh:ℚ):ℝ)
    rw [SolePositiveTScalar.ellE_value]
    simp only [domain,left,right,Set.mem_Icc] at ht hz
    simp only [ell,L,smallFloor]
    push_cast at ht ⊢
    linarith [ht.2,hz.2]

theorem reserve (f : Family) (td atG : Bool) (j : Test) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    0≤Expression.value (inputs ⟨f,td,atG,0⟩ (parameterValue f X) (secondValue f X Y))
      (test ⟨f,td,atG,0⟩ j) := by
  have hc := List.all_eq_true.mp (tests_check f td atG) j (mem_allTests j)
  simp only [testCheck,Bool.or_eq_true,Bool.and_eq_true] at hc
  rcases hc with ht|⟨⟨hm,hp⟩,hf⟩
  · exact tight_nonneg f td atG j ht hX hY
  set v := inputs ⟨f,td,atG,0⟩ (parameterValue f X) (secondValue f X Y)
  have hw : ∀ k,(testModels f atG k).Contains testConfig X Y ((inputFormulas k).value v) := by
    rintro (k|k)
    · exact inputModels_contain testConfig_valid ⟨f,td,atG,0⟩ hX hY k
    · show (zeroModel testConfig).Contains testConfig X Y (Expression.value v 0)
      rw [value_zero]
      exact zeroModel_contains testConfig X Y
  have h := check_le testConfig_valid hm hX hY hw (IE.seedsOK_of_seedFree _ hf)
  rw [← testI_eq f td atG j,IE.value_toExpressionWith _ _ _ (IE.isPoly_of_poly _ hp)]
  simpa using h

end packed

open SolePositiveTScalar

def ratio (f : Family) (t : ℝ) (i : Fin 4) : ℝ :=
  match f with
  | .ehLow => 117/200+3/10*t
  | .ehMiddle => 13/20
  | .ehHigh | .deHigh => 18/25
  | .deLow => if i=1 then 533/1000 else if i=2 then 5/8+27/100*t else 18/25

@[simp] theorem ratioE_value (s : ScalarCase) (f : Family) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (ratioE f i)=ratio f t i := by
  cases f <;> simp only [ratioE,ratio] <;> (try split_ifs) <;> norm_num [tE]

theorem tests_nonnegative (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (j : Test) :
    0≤Expression.value (inputs s t z) (test s j) := by
  obtain ⟨X,Y,hX,hY,htX,hzY⟩ := square_coordinates s ht hz
  have h := reserve s.family s.td s.atG j hX hY
  have hinput : inputs ⟨s.family,s.td,s.atG,0⟩ t z=inputs s t z := rfl
  have htest : test ⟨s.family,s.td,s.atG,0⟩ j=test s j := by cases j <;> rfl
  rw [htX,hzY,hinput,htest] at h
  exact h

theorem ratio_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    ratio s.family t i*max (first s t z i) (second s t z i)≤
      min (first s t z i) (second s t z i) := by
  have h1 := tests_nonnegative s ht hz (.ratioFirst i)
  have h2 := tests_nonnegative s ht hz (.ratioSecond i)
  simp only [test,r64_value_sub,r64_value_mul,firstE_value,secondE_value,ratioE_value] at h1 h2
  rcases le_total (first s t z i) (second s t z i) with h | h
  · rw [max_eq_right h,min_eq_left h]
    linarith
  · rw [max_eq_left h,min_eq_right h]
    linarith

theorem pair_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    max (first s t z i) (second s t z i)≤(cap s.family:ℝ) := by
  have h1 := tests_nonnegative s ht hz (.upperFirst i)
  have h2 := tests_nonnegative s ht hz (.upperSecond i)
  simp only [test,r64_value_sub,r64_value_lit,firstE_value,secondE_value] at h1 h2
  exact max_le (by linarith) (by linarith)

theorem larger_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    (largeFloor s.family:ℝ)≤ max (first s t z i) (second s t z i) := by
  have h := tests_nonnegative s ht hz (.larger i)
  simp only [test,witnessE,r64_value_sub,r64_value_lit] at h
  split_ifs at h with hi
  · rw [secondE_value] at h
    exact (by linarith : (largeFloor s.family:ℝ) ≤ second s t z i).trans (le_max_right _ _)
  · rw [firstE_value] at h
    exact (by linarith : (largeFloor s.family:ℝ) ≤ first s t z i).trans (le_max_left _ _)

theorem smaller_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    (smallFloor s.family:ℝ)≤ min (first s t z i) (second s t z i) := by
  have h1 := tests_nonnegative s ht hz (.smallerFirst i)
  have h2 := tests_nonnegative s ht hz (.smallerSecond i)
  simp only [test,r64_value_sub,r64_value_lit,firstE_value,secondE_value] at h1 h2
  exact le_min (by linarith) (by linarith)

theorem m_ge_ell (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) : ell s.family t z≤ m s t z := by
  have h := tests_nonnegative s ht hz .mixedB
  simp only [test,r64_value_sub,mE_value,ellE_value] at h
  linarith

theorem de_A (s : ScalarCase) {t z : ℝ} (hf : s.family=.deLow)
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    (113/200:ℝ)≤ell s.family t z ∧ ell s.family t z≤(81/100)*k s.family t z := by
  have h1 := tests_nonnegative s ht hz .deALower
  have h2 := tests_nonnegative s ht hz .deAUpper
  simp only [test,hf,↓reduceIte,r64_value_sub,r64_value_mul,r64_value_lit,kE_value,
    ellE_value] at h1 h2
  rw [hf]
  constructor
  · push_cast at h1
    linarith
  · push_cast at h2
    linarith

theorem D_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    max (first s t z 3) (second s t z 3)≤1131/1000 := by
  have h1 := tests_nonnegative s ht hz .DFirstUpper
  have h2 := tests_nonnegative s ht hz .DSecondUpper
  simp only [test,r64_value_sub,r64_value_lit,firstE_value,secondE_value] at h1 h2
  push_cast at h1 h2
  exact max_le (by linarith) (by linarith)

theorem half_ratio (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    max (first s t z i) (second s t z i)≤2*min (first s t z i) (second s t z i) := by
  have hr := ratio_lower s ht hz i
  have hpos := (weights_positive s ht hz).2.2.2.1 i
  have hmax : 0 < max (first s t z i) (second s t z i) := hpos.trans_le (le_max_left _ _)
  have hratio : (1/2:ℝ) ≤ ratio s.family t i := by
    have ht0 := (angle ht).1
    cases s.family <;> simp only [ratio] <;> (try split_ifs) <;> linarith
  have hh := mul_le_mul_of_nonneg_right hratio hmax.le
  linarith

end SquaresInCircles.Eight.SolePositiveTCoefficients
end
end
end

section
/-!
## Actual one-angle coefficients on the two positive-T faces

The four pairs remain unordered until this layer.
The one-angle/mixed distinction is the actual owner distinction. The
uniform D enlargement appears only in the final pure scalar comparison.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTOrdinaryData
open SoleTScalarModel SolePositiveTCoefficients PositiveAngularEnvelope
open OrdinaryAngleConcavity SingleAngleConcavity

def small (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  min (first s t z i) (second s t z i)
def large (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  max (first s t z i) (second s t z i)
def single (s : ScalarCase) : Fin 4 → Bool :=
  ![!isDE s.family,true,!s.td,isDE s.family || s.td]
def actualNu (s : ScalarCase) (t z : ℝ) : Fin 4 → ℝ :=
  ![if isDE s.family then lambda s.family else n s t z,
    ell s.family t z,if s.td then m s t z else ell s.family t z,
    if isDE s.family then (if s.td then c s.family t z else m s t z)
      else if s.td then p s t z else max (p s t z) (m s t z)]

theorem small_pos (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) : 0<small s t z i := by
  obtain ⟨hn,hm,hp,ha,hb⟩ := weights_positive s ht hz
  exact lt_min (ha i) (hb i)

theorem small_le_large (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i≤large s t z i := min_le_max

theorem nu_between (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i≤actualNu s t z i ∧ actualNu s t z i≤large s t z i := by
  rcases s with ⟨f,td,atG,j⟩
  fin_cases i <;> cases td <;> cases hD : isDE f <;>
    simp [small,large,actualNu,first,second,hD]

theorem mixed_nu (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (hi : single s i=false) :
    actualNu s t z i=large s t z i := by
  have hB := m_ge_ell s ht hz
  have hH := pair_upper s ht hz 0
  fin_cases i <;> cases hf : s.family <;> cases htd : s.td <;>
    simp_all [single,actualNu,large,first,second,lambda,isDE,cap,
      p,tiltedE]

theorem pure_eq (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (u : ℝ) :
    pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) u=
      Vnu R (small s t z i) (large s t z i) (actualNu s t z i) u := by
  cases hi : single s i
  · rw [mixed_nu s ht hz i hi]
    rfl
  · rfl

theorem m_ge_c (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) : c s.family t z≤ m s t z := by
  have ht' := angle ht
  have hz' := (split_angles s ht hz).1
  have hηlo : 1/4+33/100*z≤eta t := by simp only [eta]; linarith [hz.2]
  have hηhi : eta t≤481/1000 := by
    have h2 := ht'.2
    simp only [eta,frameCap] at h2 ⊢
    linarith
  have hη0 : 0≤eta t := (coefficient_positive ht hz).2.2.2.2.2
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz.1) hη0
  have hηz := mul_le_mul_of_nonneg_right hηlo hz.1
  have hηz3 := mul_le_mul_of_nonneg_right hηhi (pow_nonneg hz.1 3)
  have hz7 : z≤7/10 := by have h2 := hz'.2; simp only [frameCap] at h2; exact h2
  have hz2 : z^2≤(7/10)*z := by nlinarith [hz'.1]
  have hz3 : z^3≤(49/100)*z := by
    have hh := mul_le_mul_of_nonneg_right hz2 hz.1
    nlinarith
  have hfactor : 1≤Real.cos z+eta t*Real.sin z := by
    nlinarith [hz.1]
  have hh := mul_le_mul_of_nonneg_left hfactor (coefficient_positive ht hz).2.2.1.le
  rw [mul_one] at hh
  exact hh

theorem DE_A_data (s : ScalarCase) {t z : ℝ} (hf : s.family=.deLow)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) :
    small s t z 1=ell s.family t z ∧ large s t z 1=k s.family t z ∧
    actualNu s t z 1=ell s.family t z ∧
    ell s.family t z/k s.family t z∈Icc (533/1000:ℝ) (81/100) := by
  have hk := (coefficient_positive ht hz).1
  have hdata := de_A s hf ht hz
  have horder : ell s.family t z≤k s.family t z := by nlinarith
  have hr := ratio_lower s ht hz 1
  have hf1 : first s t z 1=k s.family t z := rfl
  have hs1 : second s t z 1=ell s.family t z := rfl
  have hs : small s t z 1=ell s.family t z := by
    rw [small,hf1,hs1,min_eq_right horder]
  have hl : large s t z 1=k s.family t z := by
    rw [large,hf1,hs1,max_eq_left horder]
  have hratio : ratio s.family t 1=533/1000 := by rw [hf]; rfl
  rw [hf1,hs1,max_eq_left horder,min_eq_right horder,hratio] at hr
  refine ⟨hs,hl,rfl,?_,?_⟩
  · exact (le_div_iff₀ hk).2 hr
  · exact (div_le_iff₀ hk).2 hdata.2

theorem DE_B_large (s : ScalarCase) {t z : ℝ} (hf : s.family=.deLow)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) : 903/1000≤large s t z 2 := by
  have hc : 903/1000≤c s.family t z := by
    rw [hf]
    simp only [c,SoleTScalarModel.C]
    linarith [hz.1,hz.2]
  have hm := m_ge_c s ht hz
  have hsec : 903/1000 ≤ second s t z 2 := by
    by_cases htd : s.td=true
    · simp only [second,htd,↓reduceIte,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons]
      linarith
    · simp only [second,htd,Bool.false_eq_true,↓reduceIte,Matrix.cons_val_two,Matrix.tail_cons,
        Matrix.head_cons]
      linarith
  exact hsec.trans (le_max_right _ _)

theorem DE_outer_small (s : ScalarCase) {t z : ℝ} (hf : s.family=.deLow)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) (hi : i=0 ∨ i=3) :
    18/25≤ small s t z i := by
  have hr := ratio_lower s ht hz i
  have hmax := le_max_left (first s t z i) (second s t z i)
  have hratio : ratio s.family t i=18/25 := by
    rw [hf]
    rcases hi with rfl | rfl <;> rfl
  rw [hratio] at hr
  have hfirst : 1 ≤ first s t z i := by
    rcases hi with rfl | rfl
    · norm_num [first,lambda,hf,isDE]
    · norm_num [first,p,hf,tiltedE]
  change 18/25 ≤ min _ _
  linarith

theorem norm_eq (s : ScalarCase) (t z u : ℝ) (i : Fin 4) :
    pairNorm (small s t z i) (large s t z i) u=pairNorm (first s t z i) (second s t z i) u := by
  rcases le_total (first s t z i) (second s t z i) with h | h
  · simp [small,large,min_eq_left h,max_eq_right h]
  · simp [small,large,min_eq_right h,max_eq_left h,pairNorm_symm]

def baseline (s : ScalarCase) (R M t z : ℝ) : ℝ :=
  k s.family t z*primaryCoefficient R (g s.family t) (x s t z)+
    c s.family t z*primaryCoefficient R (eta t) z+2*ell s.family t z+eTerm s R M t z-
      R*∑ i,pairNorm (first s t z i) (second s t z i) 0

theorem scalar_identity (s : ScalarCase) (R M t z : ℝ) (i : Fin 4) :
    value {s with negative:=i} R M t z=baseline s R M t z+
      Vnu R (small s t z i) (large s t z i) (nu {s with negative:=i} t z) t := by
  rw [Vnu,norm_eq,norm_eq]
  fin_cases i <;>
    simp [value,baseline,square,nu,first,second,x,SoleTScalarModel.e,n,m,p,eTerm,pairNorm,
      Fin.sum_univ_succ,Real.sin_neg] <;> ring

theorem scalar_nu_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    actualNu s t z i≤nu {s with negative:=i} t z := by
  have hD : actualNu s t z 3≤1131/1000 := (nu_between s t z 3).2.trans (D_upper s ht hz)
  rcases s with ⟨f,td,atG,j⟩
  fin_cases i
  · cases hd : isDE f <;> simp [actualNu,nu,lambda,hd,n,SoleTScalarModel.x]
  · simp [actualNu,nu]
  · cases td <;> simp [actualNu,nu,m]
  · simpa [nu] using hD

theorem pure_scalar_lower (s : ScalarCase) {R M t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    value {s with negative:=i} R M t z≤baseline s R M t z+
      pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t := by
  rw [scalar_identity,pure_eq s ht hz]
  have hh := mul_le_mul_of_nonpos_right (scalar_nu_upper s ht hz i)
    (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  dsimp [Vnu]
  linarith

end SquaresInCircles.Eight.SolePositiveTOrdinaryData
end
end
end

section
/-!
## The 34 sole-E negative-T endpoint scalars

The intervals of the rows (`Row`, `Case`, `domain`) add one endpoint to those of the sole-E
families, the cap `3/10` of a negative TD error; the coefficient families are those of the sole-E
families. The reserve of the sorted D enters after the G/E split, and the shifted D charge keeps
the coefficient `c` (`value`, `scalar_identity`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleNegativeTScalarModel
open SoleTScalarModel SolePositiveTOrdinaryData PositiveAngularEnvelope SingleAngleConcavity

inductive Row where
  | ehLowDiagonal | ehMiddleDiagonal | ehMiddleShifted (i : Fin 4)
  | ehHighShifted (i : Fin 4) | deLowDiagonal | deLowShifted (i : Fin 3)
  | deHighShifted (i : Fin 3)
  deriving DecidableEq

instance : Fintype Row where
  elems := {.ehLowDiagonal, .ehMiddleDiagonal, .deLowDiagonal} ∪
    Finset.univ.image Row.ehMiddleShifted ∪
    Finset.univ.image Row.ehHighShifted ∪
    Finset.univ.image Row.deLowShifted ∪
    Finset.univ.image Row.deHighShifted
  complete x := by cases x <;> simp

structure Case where
  row : Row
  atG : Bool
  deriving DecidableEq

instance : Fintype Case :=
  Fintype.ofEquiv (Row × Bool)
    ⟨fun p => ⟨p.1, p.2⟩, fun a => (a.row, a.atG), fun _ => rfl, fun _ => rfl⟩

def family : Row → Family
  | .ehLowDiagonal => .ehLow
  | .ehMiddleDiagonal | .ehMiddleShifted _ => .ehMiddle
  | .ehHighShifted _ => .ehHigh
  | .deLowDiagonal | .deLowShifted _ => .deLow
  | .deHighShifted _ => .deHigh

def left : Row → ℚ
  | .ehLowDiagonal | .deLowDiagonal => 0
  | .ehMiddleDiagonal => 1/5
  | .ehMiddleShifted _ | .deLowShifted _ => 3/10
  | .ehHighShifted _ | .deHighShifted _ => 7/20

def right : Row → ℚ
  | .ehLowDiagonal => 1/5
  | .ehMiddleDiagonal | .deLowDiagonal => 3/10
  | .ehMiddleShifted _ | .deLowShifted _ => 7/20
  | .ehHighShifted _ | .deHighShifted _ => 7/10

def shifted : Row → Bool
  | .ehLowDiagonal | .ehMiddleDiagonal | .deLowDiagonal => false
  | _ => true

def index : Row → Fin 4
  | .ehMiddleShifted i | .ehHighShifted i => i
  | .deLowShifted i | .deHighShifted i => ⟨i.val,lt_trans i.isLt (by decide : 3<4)⟩
  | _ => 0

def domain (r : Row) : Set ℝ := Icc (left r:ℝ) (right r:ℝ)
def scalar (s : Case) : ScalarCase := ⟨family s.row,true,s.atG,index s.row⟩
def angle (r : Row) (t : ℝ) : ℝ := if shifted r then t-3/10 else 0
def removed (r : Row) (t : ℝ) : ℝ := if shifted r then 3/10 else t
def correction (s : Case) (t : ℝ) : ℝ :=
  if family s.row=.ehMiddle ∨ family s.row=.ehHigh then
    (8/25)*(c (family s.row) t 0-p (scalar s) t 0)^2 else 0
def coefficient (s : Case) (t : ℝ) : ℝ :=
  if index s.row=3 then c (family s.row) t 0 else nu (scalar s) t 0
def square (s : Case) (t : ℝ) (i : Fin 4) : ℝ :=
  first (scalar s) t 0 i^2+second (scalar s) t 0 i^2-
    if i=index s.row then 2*first (scalar s) t 0 i*second (scalar s) t 0 i*Real.sin (angle s.row t) else 0

def value (s : Case) (R M t : ℝ) : ℝ :=
  k (family s.row) t 0*primaryCoefficient R (g (family s.row) t) (x (scalar s) t 0)+
    3*c (family s.row) t 0+2*ell (family s.row) t 0+eTerm (scalar s) R M t 0+
    correction s t+(21/20)*c (family s.row) t 0*removed s.row t+
    coefficient s t*(Real.cos (angle s.row t)-1)-R*∑i,Real.sqrt (square s t i)

theorem interval_order (r : Row) : 0≤left r ∧ left r<right r ∧ right r≤7/10 := by
  cases r <;> norm_num [left,right]

theorem family_mem {r : Row} {t : ℝ} (ht : t∈domain r) :
    t∈SoleTScalarModel.domain (family r) := by
  cases r <;> norm_num [domain,left,right,SoleTScalarModel.domain,
    SoleTScalarModel.left,SoleTScalarModel.right,family] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

theorem angles {r : Row} {t : ℝ} (ht : t∈domain r) :
    t∈Icc 0 frameCap ∧ angle r t∈Icc 0 frameCap ∧ removed r t∈Icc 0 (3/10:ℝ) := by
  have hf := SoleTScalarModel.angle (family_mem ht)
  refine ⟨hf,?_,?_⟩ <;> cases r <;>
    norm_num [domain,left,right,angle,removed,shifted,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

theorem square_nonneg (s : Case) {t : ℝ} (ht : t∈domain s.row) (i : Fin 4) :
    0≤ square s t i := by
  have hf := family_mem ht
  have hz : (0:ℝ)∈Icc 0 t := ⟨le_rfl,(angles ht).1.1⟩
  obtain ⟨hn,hm,hp,ha,hb⟩ := weights_positive (scalar s) hf hz
  dsimp only [square]
  split_ifs
  · have hh := mul_nonneg (mul_pos (ha i) (hb i)).le
      (sub_nonneg.mpr (Real.sin_le_one (angle s.row t)))
    nlinarith [sq_nonneg (first (scalar s) t 0 i-second (scalar s) t 0 i)]
  · rw [sub_zero]
    positivity

theorem scalar_identity (s : Case) (R M t : ℝ) :
    value s R M t=baseline (scalar s) R M t 0+correction s t+
      (21/20)*c (family s.row) t 0*removed s.row t+
      Vnu R (small (scalar s) t 0 (index s.row)) (large (scalar s) t 0 (index s.row))
        (coefficient s t) (angle s.row t) := by
  have key : ∀ i, Real.sqrt (square s t i)=
      pairNorm (first (scalar s) t 0 i) (second (scalar s) t 0 i) 0+
        (if i=index s.row then
          pairNorm (first (scalar s) t 0 i) (second (scalar s) t 0 i) (-angle s.row t)-
            pairNorm (first (scalar s) t 0 i) (second (scalar s) t 0 i) 0 else 0) := by
    intro i
    unfold square pairNorm
    split_ifs with h
    · rw [Real.sin_neg,Real.sin_zero]
      ring_nf
    · rw [Real.sin_zero]
      ring_nf
  have hsum : ∑ i,Real.sqrt (square s t i)=
      ∑ i,pairNorm (first (scalar s) t 0 i) (second (scalar s) t 0 i) 0+
        (pairNorm (first (scalar s) t 0 (index s.row)) (second (scalar s) t 0 (index s.row))
          (-angle s.row t)-
          pairNorm (first (scalar s) t 0 (index s.row)) (second (scalar s) t 0 (index s.row)) 0) := by
    rw [Finset.sum_congr rfl (fun i _ => key i),Finset.sum_add_distrib,Finset.sum_ite_eq']
    simp
  rw [Vnu,norm_eq,norm_eq]
  simp only [value,baseline,hsum,primaryCoefficient,Real.cos_zero,Real.sin_zero,mul_zero,
    add_zero]
  dsimp only [scalar]
  ring

end SquaresInCircles.Eight.SoleNegativeTScalarModel
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SoleNormGain
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope VaryingBFunctions VaryingBComparison

def normGain (R p q s : ℝ) : ℝ := R*(pairNorm p q 0-pairNorm p q (-s))

theorem normGain_hasDerivAt_large {R p q s : ℝ} (hp : 0<p) (hq : 0<q)
    (hs : s∈Icc 0 frameCap) :
    HasDerivAt (fun x => normGain R p x s) (R*gain (p/q) (Real.sin s)) q := by
  have hh := (V_hasDerivAt_q (R := R) hp hq hs).sub
    ((hasDerivAt_id q).mul_const (Real.cos s-1))
  convert hh using 1
  · funext x
    dsimp [normGain,V]
    ring
  · dsimp [D]
    ring

theorem gain_nonneg {r z : ℝ} (hr : r∈Icc 0 1)
    (hz : z∈Icc 0 frameCap) (hzr : z≤r) : 0≤gain r z := by
  have hS := shape_pos r
  have hN := root_pos r hz
  have hS2 := shape_sq r
  have hN2 := root_sq r hz
  have hr2 : r^2≤1 := by
    have h := mul_le_mul hr.2 hr.2 hr.1 (by norm_num : (0:ℝ)≤1)
    nlinarith
  have hprod : r*z≤1 := by
    have h := mul_le_mul hr.2 (hzr.trans hr.2) hz.1 (by norm_num : (0:ℝ)≤1)
    linarith
  have hnum : 0≤1-r*z := by linarith
  have hinner : 0≤2*r-z*(1+r^2) := by
    have hh := mul_le_mul_of_nonneg_right hzr (show 0≤1+r^2 by positivity)
    have ht := mul_nonneg hr.1 (sub_nonneg.mpr hr2)
    nlinarith
  have hp := mul_nonneg (mul_nonneg (sq_nonneg r) hz.1) hinner
  have hid : (root r z)^2-((1-r*z)*shape r)^2=r^2*z*(2*r-z*(1+r^2)) := by
    rw [mul_pow,hS2,hN2]
    ring
  have hc : (1-r*z)*shape r≤root r z :=
    le_of_pow_le_pow_left₀ two_ne_zero hN.le (by linarith)
  have hd : (1-r*z)/root r z≤1/shape r := by
    apply (div_le_div_iff₀ hN hS).2
    simpa only [one_mul] using hc
  dsimp [gain]
  linarith

theorem normGain_larger_mono {R p a b s : ℝ}
    (hR : 0≤R) (hp : 0<p) (hpa : p≤a) (hab : a≤b)
    (hs : s∈Icc 0 frameCap) (hratio : Real.sin s*b≤p) :
    normGain R p a s≤normGain R p b s := by
  have ha : 0<a := hp.trans_le hpa
  have hsin := (transport_trig hs).2.2.1
  have hz := sin_mem hs
  have hx (x : ℝ) (hx : x∈Icc a b) :
      0<x ∧ p/x∈Icc 0 1 ∧ Real.sin s≤p/x := by
    have hxp : 0<x := ha.trans_le hx.1
    refine ⟨hxp,⟨div_nonneg hp.le hxp.le,(div_le_one hxp).2 (hpa.trans hx.1)⟩,?_⟩
    exact (le_div_iff₀ hxp).2
      ((mul_le_mul_of_nonneg_left hx.2 hsin).trans hratio)
  have hm : MonotoneOn (fun x => normGain R p x s) (Icc a b) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hxx
      exact (normGain_hasDerivAt_large hp (hx x hxx).1 hs).continuousAt.continuousWithinAt
    · intro x hxx
      exact normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs
    · intro x hxx
      have hc := hx x (Ioo_subset_Icc_self hxx)
      exact mul_nonneg hR (gain_nonneg hc.2.1 hz hc.2.2)
  exact hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

theorem normGain_smaller_mono {R q p p' s : ℝ}
    (hR : 0≤R) (hq : 0<q) (hs : s∈Icc 0 frameCap)
    (hp : p∈Icc (q/2) q) (hp' : p'∈Icc (q/2) q) (hpp : p≤p') :
    normGain R p q s≤normGain R p' q s := by
  have hh := V_monotone_smaller hR hq hs hp hp' hpp
  dsimp [V,normGain] at *
  linarith

theorem integrand_hasDerivAt_r {r z : ℝ} (hz : z∈Icc 0 frameCap) :
    HasDerivAt (fun x => integrand x z)
      (r*(3*r-2*z-2*r^2*z+r*z^2)/(root r z)^5) r := by
  have hn := root_hasDerivAt_r (r := r) hz
  have hN := root_pos r hz
  have hN2 := root_sq r hz
  have hnum : HasDerivAt (fun x => x^2*(x-z)) (2*r*(r-z)+r^2) r := by
    have h := ((hasDerivAt_id' (x := r)).fun_pow 2).fun_mul ((hasDerivAt_id' (x := r)).sub_const z)
    convert h using 1
    push_cast
    ring
  have hh := hnum.div (hn.fun_pow 3) (pow_ne_zero 3 hN.ne')
  convert hh using 1
  · funext x
    rfl
  · field_simp
    linear_combination (-(root r z)^2*(3*r^2-2*r*z))*hN2

theorem integrand_monotone_ratio {z : ℝ} (hz : z∈Icc 0 (1/5 : ℝ)) :
    MonotoneOn (fun r => integrand r z) (Icc (117/200 : ℝ) (18/25)) := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  apply monoOn_of_hasDeriv_nonneg
  · intro r _
    exact (integrand_hasDerivAt_r hz').continuousAt.continuousWithinAt
  · intro r _
    exact integrand_hasDerivAt_r hz'
  · intro r hr
    have hr0 : 0≤r := by linarith [hr.1]
    have hr2 : r^2≤324/625 := by nlinarith [hr.2,sq_nonneg (r-18/25)]
    have hp := mul_le_mul hr2 hz.2 hz.1 (by norm_num : (0:ℝ)≤324/625)
    have hin : 0≤3*r-2*z-2*r^2*z+r*z^2 := by
      nlinarith [mul_nonneg hr0 (sq_nonneg z),hr.1,hz.2]
    exact div_nonneg (mul_nonneg hr0 hin) (pow_pos (root_pos r hz') 5).le

theorem scaled_integrand_upper {R r z : ℝ}
    (hR : R∈Icc 0 2) (hr : r∈Icc (117/200 : ℝ) (18/25))
    (hz : z∈Icc 0 (1/5 : ℝ)) : R*integrand r z≤11/20 := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hm := mul_le_mul_of_nonneg_left
    (integrand_monotone_ratio hz hr ⟨by norm_num,le_rfl⟩ hr.2) hR.1
  have hN := root_pos (18/25) hz'
  have hN2 := root_sq (18/25) hz'
  have hNlo : 1109/1000≤root (18/25) z := by nlinarith [hz.2]
  have hN3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1109/1000) hNlo 3
  have hnum0 : 0≤(18/25:ℝ)-z := by linarith [hz.2]
  have hnum := mul_le_mul_of_nonneg_right hR.2
    (mul_nonneg (by norm_num : (0:ℝ)≤(18/25)^2) hnum0)
  have hlast : R*integrand (18/25) z≤11/20 := by
    dsimp [integrand]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hN 3)).2
    nlinarith [hz.1]
  exact hm.trans hlast

theorem scaled_gain_short {R r s : ℝ}
    (hR : R∈Icc 0 2) (hr : r∈Icc (117/200 : ℝ) (18/25))
    (hs : s∈Icc 0 (1/5 : ℝ)) : R*gain r (Real.sin s)≤(11/20)*s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hsin : Real.sin s∈Icc 0 (1/5 : ℝ) :=
    ⟨(transport_trig hs').2.2.1,(Real.sin_le hs.1).trans hs.2⟩
  have hmem {z : ℝ} (hz : z∈Icc 0 (1/5 : ℝ)) : z∈Icc 0 frameCap :=
    ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hh := derivative_reserve
    (f := fun z => -R*gain r z) (df := fun z => -R*integrand r z)
    (k := -(11/20 : ℝ))
    (fun z hz => ((gain_hasDerivAt_u r (hmem hz)).const_mul (-R)).continuousAt.continuousWithinAt)
    (fun z hz => (gain_hasDerivAt_u r (hmem (Ioo_subset_Icc_self hz))).const_mul (-R))
    (fun z hz => by linarith [scaled_integrand_upper hR hr (Ioo_subset_Icc_self hz)])
    (show (0:ℝ)∈Icc 0 (1/5:ℝ) by norm_num) hsin hsin.1
  have hz : gain r 0=0 := by simp [gain,root,shape]
  rw [hz] at hh
  nlinarith [Real.sin_le hs.1]

theorem scaled_gain_cap {R r : ℝ} (hR : R∈Icc 0 2)
    (hr : r∈Icc (117/200 : ℝ) (18/25)) : R*gain r (Real.sin frameCap)≤1 := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hz := sin_mem hh
  have hsl := cap_sin_lower
  have hsu := (transport_trig hh).2.2.2.1
  have hN := root_pos r hz
  have hN2 := root_sq r hz
  have hS := shape_pos r
  have hS2 := shape_sq r
  have hr0 : 0≤r := by linarith [hr.1]
  have hN1 : root r (Real.sin frameCap)≤1 := by
    have hp := mul_nonneg hr0 (show 0≤2*Real.sin frameCap-r by linarith [hr.2])
    nlinarith
  have hS1 : 1≤ shape r := by nlinarith [sq_nonneg r]
  have hp := mul_le_mul hr.2 hsu.le hz.1 (by norm_num : (0:ℝ)≤18/25)
  have hn0 : 0≤1-r*Real.sin frameCap := by nlinarith
  have hquot : 1-r*Real.sin frameCap≤(1-r*Real.sin frameCap)/root r (Real.sin frameCap) := by
    apply (le_div_iff₀ hN).2
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hN1)]
  have hinv : 1/shape r≤1 := (div_le_one hS).2 hS1
  have hg : gain r (Real.sin frameCap)≤(18/25)*(6443/10000) := by
    dsimp [gain]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hg hR.1
  nlinarith [hR.2]

theorem coefficient_short {R p a b s : ℝ}
    (hR : R∈Icc 0 2) (ha : 0<a) (hab : a≤b)
    (hplo : (117/200)*b≤p) (hphi : p≤(18/25)*a)
    (hs : s∈Icc 0 (1/5 : ℝ)) :
    normGain R p b s-normGain R p a s≤(11/20)*s*(b-a) := by
  have hp : 0<p := by nlinarith
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hx (x : ℝ) (hx : x∈Icc a b) : 0<x ∧ p/x∈Icc (117/200 : ℝ) (18/25) := by
    have hxp : 0<x := ha.trans_le hx.1
    refine ⟨hxp,⟨(le_div_iff₀ hxp).2 ?_,(div_le_iff₀ hxp).2 ?_⟩⟩ <;>
      nlinarith [hx.1,hx.2]
  have hh := derivative_reserve
    (f := fun x => -normGain R p x s)
    (df := fun x => -(R*gain (p/x) (Real.sin s))) (k := -(11/20)*s)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x hxx).1 hs').neg.continuousAt.continuousWithinAt)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs').neg)
    (fun x hxx => by linarith [scaled_gain_short hR (hx x (Ioo_subset_Icc_self hxx)).2 hs])
    (show a∈Icc a b from ⟨le_rfl,hab⟩) (show b∈Icc a b from ⟨hab,le_rfl⟩) hab
  linarith

theorem coefficient_cap {R p a b : ℝ}
    (hR : R∈Icc 0 2) (ha : 0<a) (hab : a≤b)
    (hplo : (117/200)*b≤p) (hphi : p≤(18/25)*a) :
    normGain R p b frameCap-normGain R p a frameCap≤b-a := by
  have hp : 0<p := by nlinarith
  have hs : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hx (x : ℝ) (hx : x∈Icc a b) : 0<x ∧ p/x∈Icc (117/200 : ℝ) (18/25) := by
    have hxp : 0<x := ha.trans_le hx.1
    refine ⟨hxp,⟨(le_div_iff₀ hxp).2 ?_,(div_le_iff₀ hxp).2 ?_⟩⟩ <;>
      nlinarith [hx.1,hx.2]
  have hh := derivative_reserve
    (f := fun x => -normGain R p x frameCap)
    (df := fun x => -(R*gain (p/x) (Real.sin frameCap))) (k := -1)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x hxx).1 hs).neg.continuousAt.continuousWithinAt)
    (fun x hxx => (normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs).neg)
    (fun x hxx => by linarith [scaled_gain_cap hR (hx x (Ioo_subset_Icc_self hxx)).2])
    (show a∈Icc a b from ⟨le_rfl,hab⟩) (show b∈Icc a b from ⟨hab,le_rfl⟩) hab
  linarith

end SquaresInCircles.Eight.SoleNormGain
end
end
end
