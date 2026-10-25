module

public import SquaresInCircles.Eight.TableFree.SoleTScalarModel
public import SquaresInCircles.Eight.TableFree.PackedModels
public import SquaresInCircles.Eight.TableFree.TensorPolynomialEnclosure
public import SquaresInCircles.Eight.TableFree.TensorWholeIntervalBernstein

/-!
# Whole-square rational formulas for positive T and a sole E primary

Uncompiled source. Each intrinsic family interval is parameterized by
one full square, with `z=t(1+Y)/2`. The only finite choices are the five
coefficient families, the two actual T rows, the two primary-split
endpoints and the four negative indices. Every coefficient reserve is
an exact rational reduction of the displayed expression recipe.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SolePositiveTPolynomials
section r64_bernstein
open Polynomial Finset TensorWholeIntervalPolynomial

/-! Degree-`D` Bernstein re-expansion of a bivariate polynomial whose degrees in both
variables are at most `D`, and the degree bound `14` of every enclosure polynomial. -/

section generic
variable {R : Type*} [CommRing R]

private theorem r64_bern_sum (u : R) (D : ℕ) :
    ∑ i ∈ range (D+1),(D.choose i : R)*u^i*(1-u)^(D-i)=1 := by
  have h := (add_pow u (1-u) D).symm
  rw [add_sub_cancel,one_pow] at h
  exact (sum_congr rfl (fun i _ => by ring)).trans h

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

private theorem r64_partition (D : ℕ) :
    (∑ i : Fin (D+1),∑ j : Fin (D+1),TensorWholeIntervalBernstein.basis D i j)=1 := by
  have hsplit : ∀ i j : Fin (D+1),TensorWholeIntervalBernstein.basis D i j=
      ((D.choose i : Bivar)*TensorWholeIntervalBernstein.left^(i:ℕ)*
        (1-TensorWholeIntervalBernstein.left)^(D-i))*
      ((D.choose j : Bivar)*TensorWholeIntervalBernstein.right^(j:ℕ)*
        (1-TensorWholeIntervalBernstein.right)^(D-j)) := by
    intro i j
    simp only [TensorWholeIntervalBernstein.basis,r64_scalar_eq,map_mul,map_natCast]
    ring
  simp only [hsplit,← mul_sum,← sum_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => (D.choose i : Bivar)*TensorWholeIntervalBernstein.left^i*
        (1-TensorWholeIntervalBernstein.left)^(D-i)),
    Fin.sum_univ_eq_sum_range (fun j => (D.choose j : Bivar)*TensorWholeIntervalBernstein.right^j*
        (1-TensorWholeIntervalBernstein.right)^(D-j)),r64_bern_sum,r64_bern_sum,one_mul]

end r64_bernstein

open TensorPolynomialEnclosure TensorWholeIntervalPolynomial
open SoleTScalarModel

abbrev Expr := Expression (Fin 11)
abbrev lit (r : ℚ) : Expr := .literal r
abbrev var (i : Fin 11) : Expr := .variable i

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
def shalf : Expr := var 10

def KE : Family → Expr
  | .ehLow => lit (17253/20000)+lit (11/20)*tE+lit (3/10)*tE^2
  | .ehMiddle => lit (983/1000)+lit (1/10)*(tE-lit (1/5))-lit (3/10)*(tE-lit (1/5))^2
  | .ehHigh => lit (1017/1000)-lit (1/50)*tE
  | .deLow => lit (53/50)-lit (1/10)*tE
  | .deHigh => lit (107/100)-lit (3/25)*tE

def LE : Family → Expr
  | .ehLow => lit (50521/100000)+lit (823/1000)*tE+lit (7/10)*tE^2
  | .ehMiddle => lit (349/500)+lit (9/10)*(tE-lit (1/5))-(tE-lit (1/5))^2
  | .ehHigh => lit (7/10)+lit (9/25)*tE
  | .deLow => lit (113/200)+lit (3/4)*tE
  | .deHigh => lit (77/100)+lit (1/5)*tE

def CE : Family → Expr
  | .ehLow => KE .ehLow+lit (3/10)*tE
  | .ehMiddle => lit (209/200)+lit (13/20)*(tE-lit (1/5))-lit (3/2)*(tE-lit (1/5))^2
  | .ehHigh | .deHigh => lit (113/100)
  | .deLow => lit (903/1000)+lit (13/20)*tE

def gE : Family → Expr
  | .ehLow | .deLow => lit (8/25)
  | .ehMiddle => lit (31/100)
  | .ehHigh => lit (27/100)+lit (2/25)*tE
  | .deHigh => lit (3/10)+lit (1/20)*tE

def epsilonE : Family → Expr
  | .ehLow => lit (131/500)+lit (267/1000)*tE+lit (1/10)*tE^2
  | .ehMiddle => lit (319/1000)+lit (1/5)*(tE-lit (1/5))
  | _ => 0

def kE (f : Family) : Expr := KE f+lit (3/50)*zE
def ellE (f : Family) : Expr := LE f-lit (23/100)*zE
def cE (f : Family) : Expr := CE f-lit (53/100)*zE
def etaE : Expr := lit (1/4)+lit (33/100)*tE
def lambdaE (f : Family) : Expr := if isDE f then lit (5/4) else 1
def nE (s : ScalarCase) : Expr := kE s.family*(cx+gE s.family*sx)
def mE (s : ScalarCase) : Expr := cE s.family*(cz+etaE*sz)
def pE (s : ScalarCase) : Expr := if tiltedE s.family then ce+epsilonE s.family*se else 1

def firstE (s : ScalarCase) : Fin 4 → Expr :=
  ![lambdaE s.family,kE s.family,ellE s.family,pE s]
def secondE (s : ScalarCase) : Fin 4 → Expr :=
  ![nE s,ellE s.family,if s.td then mE s else cE s.family,
    if s.td then cE s.family else mE s]
def nuE (s : ScalarCase) : Expr :=
  ![if isDE s.family then lit (5/4) else nE s,ellE s.family,
    if s.td then mE s else ellE s.family,lit (1131/1000)] s.negative

def squareE (s : ScalarCase) (i : Fin 4) : Expr :=
  firstE s i^2+secondE s i^2-
    if i=s.negative then 2*firstE s i*secondE s i*st else 0

def rootSquare (s : ScalarCase) (i : Fin 7) : Expr :=
  if hi : i.val<4 then squareE s ⟨i.val,hi⟩
  else if i.val=4 then 1+gE s.family^2
  else if i.val=5 then 1+etaE^2 else 1+epsilonE s.family^2

def parameter (f : Family) : Enclosure :=
  TensorPolynomialEnclosure.add (constant ((left f+right f)/2))
    (mul (constant ((right f-left f)/2)) outerVariable)

def secondParameter (f : Family) : Enclosure :=
  mul (mul (parameter f) (TensorPolynomialEnclosure.add (constant 1) innerVariable)) (constant (1/2))

def xParameter (s : ScalarCase) : Enclosure :=
  if s.atG then TensorPolynomialEnclosure.sub (parameter s.family) (secondParameter s.family) else constant 0

def eParameter (s : ScalarCase) : Enclosure :=
  if s.atG then constant 0 else TensorPolynomialEnclosure.sub (parameter s.family) (secondParameter s.family)

def «variables» (s : ScalarCase) : Fin 11 → Enclosure :=
  ![parameter s.family,secondParameter s.family,sine (xParameter s),cosine (xParameter s),
    sine (secondParameter s.family),cosine (secondParameter s.family),
    sine (eParameter s),cosine (eParameter s),sine (parameter s.family),
    cosine (parameter s.family),sine (mul (eParameter s) (constant (1/2)))]

def rootExpression (s : ScalarCase) (i : Fin 7) : Expr :=
  Expression.sqrtUpper («variables» s) (rootSquare s i)

def baseExpression (s : ScalarCase) : Expr :=
  kE s.family*(1+2*cx+(1+2*gE s.family)*sx)+
    cE s.family*(1+2*cz+(1+2*etaE)*sz)+2*ellE s.family-
    lit radiusUpper*(kE s.family*sx*rootExpression s 4+
      cE s.family*sz*rootExpression s 5)

def eExpression (s : ScalarCase) : Expr :=
  if tiltedE s.family then
    1+2*ce+(1+2*epsilonE s.family)*se-lit radiusUpper*se*rootExpression s 6
  else if isDE s.family then
    1+lit (1/2)*ce+lit (1-axisUpper)*se+lit (3/2)*lit (5/4)
  else 3+se-lit (2*radiusUpper)*shalf

def expression (s : ScalarCase) : Expr :=
  ((((baseExpression s+eExpression s+nuE s*(ct-1))-
    lit radiusUpper*rootExpression s 0)-lit radiusUpper*rootExpression s 1)-
      lit radiusUpper*rootExpression s 2)-lit radiusUpper*rootExpression s 3

def enclosure (s : ScalarCase) : Enclosure := Expression.enclose («variables» s) (expression s)
def polynomial (s : ScalarCase) : Bivar := (enclosure s).polynomial

section r64_seeds
open Polynomial

/-- The constant coefficient of an enclosure polynomial. -/
private def r64_c0 (E : Enclosure) : ℚ := (E.polynomial.coeff 0).coeff 0

private theorem r64_c0_constant (r : ℚ) : r64_c0 (constant r)=r := by
  simp [r64_c0,constant,scalar]

private theorem r64_c0_add (a b : Enclosure) :
    r64_c0 (TensorPolynomialEnclosure.add a b)=r64_c0 a+r64_c0 b := by
  simp [r64_c0,TensorPolynomialEnclosure.add]

private theorem r64_c0_neg (a : Enclosure) : r64_c0 (TensorPolynomialEnclosure.neg a)=-r64_c0 a := by
  simp [r64_c0,TensorPolynomialEnclosure.neg]

private theorem r64_c0_sub (a b : Enclosure) :
    r64_c0 (TensorPolynomialEnclosure.sub a b)=r64_c0 a-r64_c0 b := by
  rw [TensorPolynomialEnclosure.sub,r64_c0_add,r64_c0_neg]
  ring

private theorem r64_coeff00_monomial (c : ℚ) (i j : ℕ) :
    (((scalar c*X^i*(Polynomial.C X)^j : Bivar).coeff 0).coeff 0)=if i=0 ∧ j=0 then c else 0 := by
  have he : scalar c*X^i*(Polynomial.C X:Bivar)^j=
      Polynomial.C (Polynomial.C c*X^j)*X^i := by
    simp only [scalar,map_mul,map_pow]
    ring
  rw [he,coeff_C_mul_X_pow]
  by_cases hi : i=0
  · subst hi
    simp only [↓reduceIte,true_and,coeff_C_mul_X_pow]
    by_cases hj : j=0
    · simp [hj]
    · simp [hj,Ne.symm hj]
  · simp [Ne.symm hi,hi]

private theorem r64_c0_truncate (p : Bivar) :
    (((TensorPolynomialEnclosure.truncate p).coeff 0).coeff 0)=(p.coeff 0).coeff 0 := by
  unfold TensorPolynomialEnclosure.truncate
  simp only [finsetSum_coeff]
  rw [Finset.sum_eq_single (0:Fin 15)]
  · rw [Finset.sum_eq_single (0:Fin 15)]
    · rw [ite_eq_left_of_eq_true _ _ (by simp),r64_coeff00_monomial]
      simp
    · intro j _ hj
      split_ifs
      · rw [r64_coeff00_monomial]
        simp only [Fin.val_zero,true_and]
        split_ifs with h
        · exact absurd (Fin.ext h) hj
        · rfl
      · simp
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    split_ifs
    · rw [r64_coeff00_monomial]
      split_ifs with h
      · exact absurd (Fin.ext h.1) hi
      · rfl
    · simp
  · simp

private theorem r64_c0_mul (a b : Enclosure) :
    r64_c0 (TensorPolynomialEnclosure.mul a b)=r64_c0 a*r64_c0 b := by
  simp only [r64_c0,TensorPolynomialEnclosure.mul]
  rw [r64_c0_truncate,mul_coeff_zero,mul_coeff_zero]

private theorem r64_c0_power (a : Enclosure) (n : ℕ) : r64_c0 (power a n)=r64_c0 a^n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [TensorPolynomialEnclosure.power]
    split_ifs with hn he
    · subst hn
      simp [r64_c0_constant]
    · rw [r64_c0_mul,ih (n/2) (by omega),← pow_add]
      congr 1
      omega
    · rw [r64_c0_mul,r64_c0_mul,ih (n/2) (by omega),← pow_add,← pow_succ]
      congr 1
      omega

private theorem r64_c0_sum {ι : Type*} [Fintype ι] (f : ι → Enclosure) :
    r64_c0 (TensorPolynomialEnclosure.sum f)=∑ i,r64_c0 (f i) := by
  simp [r64_c0,TensorPolynomialEnclosure.sum,finsetSum_coeff]

private theorem r64_c0_widen (a : Enclosure) (e : ℚ) : r64_c0 (widen a e)=r64_c0 a := rfl

private theorem r64_c0_sine (a : Enclosure) : (r64_c0 (sine a):ℝ)=HighOrderTaylor.S13 (r64_c0 a) := by
  unfold sine
  rw [← TensorPolynomialEnclosure.sine_sum,r64_c0_widen,r64_c0_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [r64_c0_mul,r64_c0_constant,r64_c0_power]
  push_cast
  ring

private theorem r64_c0_cosine (a : Enclosure) : (r64_c0 (cosine a):ℝ)=HighOrderTaylor.C14 (r64_c0 a) := by
  unfold cosine
  rw [← TensorPolynomialEnclosure.cosine_sum,r64_c0_widen,r64_c0_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [r64_c0_mul,r64_c0_constant,r64_c0_power]
  push_cast
  ring

private theorem r64_c0_enclose {ι : Type*} (w : ι → Enclosure) (e : Expression ι) :
    (r64_c0 (Expression.enclose w e):ℝ)=Expression.value (fun i => (r64_c0 (w i):ℝ)) e := by
  induction e with
  | literal r => simp [Expression.enclose,Expression.value,r64_c0_constant]
  | «variable» i => rfl
  | add a b ha hb =>
    simp only [Expression.enclose,Expression.value,r64_c0_add]
    push_cast
    rw [ha,hb]
  | neg a ha =>
    simp only [Expression.enclose,Expression.value,r64_c0_neg]
    push_cast
    rw [ha]
  | mul a b ha hb =>
    simp only [Expression.enclose,Expression.value,r64_c0_mul]
    push_cast
    rw [ha,hb]
  | power a n ha =>
    simp only [Expression.enclose,Expression.value,r64_c0_power]
    push_cast
    rw [ha]

private theorem r64_nearestRoot_pos {r : ℚ} (hr : 1/20 ≤ r) : 0 < nearestRoot r := by
  have hr0 : 0 < r := by linarith
  have hnum : 0 < r.num := Rat.num_pos.mpr hr0
  have hden : (0:ℚ) < r.den := by exact_mod_cast r.den_pos
  have hq : (r.den:ℚ) ≤ r.num*10000000000000000 := by
    have h := Rat.num_div_den r
    rw [← h] at hr
    rw [le_div_iff₀ hden] at hr
    linarith
  have hq' : r.den ≤ r.num.natAbs*10000000000000000 := by
    have h1 : ((r.num.natAbs:ℤ):ℚ)=(r.num:ℚ) := by
      rw [Int.natAbs_of_nonneg hnum.le]
    have h2 : ((r.den:ℕ):ℚ) ≤ ((r.num.natAbs*10000000000000000:ℕ):ℚ) := by
      push_cast
      rw [show ((r.num.natAbs:ℕ):ℚ)=((r.num.natAbs:ℤ):ℚ) from rfl,h1]
      exact hq
    exact_mod_cast h2
  have hn : 0 < Nat.sqrt ((r.num.natAbs*10000000000000000)/r.den) := by
    apply Nat.sqrt_pos.mpr
    exact Nat.div_pos hq' r.den_pos
  unfold nearestRoot
  dsimp only
  split_ifs
  · apply div_pos _ (by norm_num)
    exact_mod_cast hn
  · apply div_pos _ (by norm_num)
    exact_mod_cast Nat.succ_pos _

section r64_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
private theorem r64_v_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
private theorem r64_v_neg : Expression.value v (-a)=-Expression.value v a := rfl
private theorem r64_v_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
private theorem r64_v_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
private theorem r64_v_pow (n : ℕ) :
    Expression.value v (a^n)=Expression.value v a^n := rfl
private theorem r64_v_one : Expression.value v (1 : Expression ι)=1 := by
  show (((1:ℕ):ℚ):ℝ)=1
  norm_num
private theorem r64_v_two : Expression.value v (2 : Expression ι)=2 := by
  show (((2:ℕ):ℚ):ℝ)=2
  norm_num
private theorem r64_v_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
end r64_value

private theorem r64_v_lit (w : Fin 11 → ℝ) (r : ℚ) : Expression.value w (lit r)=(r:ℝ) := rfl
private theorem r64_v_var (w : Fin 11 → ℝ) (i : Fin 11) : Expression.value w (var i)=w i := rfl

private theorem r64_kE_w (w : Fin 11 → ℝ) (f : Family) :
    Expression.value w (kE f)=k f (w 0) (w 1) := by
  cases f <;> simp only [kE,KE,k,K,tE,zE,r64_v_add,r64_v_sub,r64_v_mul,r64_v_pow,r64_v_lit,
    r64_v_var] <;> push_cast <;> ring

private theorem r64_ellE_w (w : Fin 11 → ℝ) (f : Family) :
    Expression.value w (ellE f)=ell f (w 0) (w 1) := by
  cases f <;> simp only [ellE,SolePositiveTPolynomials.LE,ell,L,tE,zE,r64_v_add,r64_v_sub,
    r64_v_mul,r64_v_pow,r64_v_lit,r64_v_var] <;> push_cast <;> ring

private theorem r64_epsilonE_w (w : Fin 11 → ℝ) (f : Family) :
    Expression.value w (epsilonE f)=epsilon f (w 0) := by
  cases f <;> simp only [epsilonE,epsilon,tE,r64_v_add,r64_v_sub,r64_v_mul,r64_v_pow,r64_v_lit,
    r64_v_var,r64_v_zero] <;> push_cast <;> ring

private theorem r64_cos14_lower {x : ℝ} (hx : x∈Set.Icc 0 (7/10:ℝ)) :
    (3/4:ℝ) ≤ HighOrderTaylor.C14 x := by
  have h1 := HighOrderTaylor.cos_le_C16 hx.1
  have h2 := (transport_trig hx).1
  have h3 : x^16 ≤ 1 := pow_le_one₀ hx.1 (by linarith [hx.2])
  simp only [HighOrderTaylor.C16] at h1
  linarith

private theorem r64_sin13_bounds {x : ℝ} (hx : x∈Set.Icc 0 (7/10:ℝ)) :
    0 ≤ HighOrderTaylor.S13 x ∧ HighOrderTaylor.S13 x ≤ 13/20 := by
  have h1 := HighOrderTaylor.sin_le_S13 hx.1
  have h2 := HighOrderTaylor.S15_le_sin hx.1
  have h3 := transport_trig hx
  have h4 : x^15 ≤ 1 := pow_le_one₀ hx.1 (by linarith [hx.2])
  simp only [HighOrderTaylor.S15] at h2
  constructor <;> linarith [h3.2.2.1,h3.2.2.2.1]

private theorem r64_k_lower {f : Family} {t z : ℝ} (ht : t∈domain f) (hz : z∈Set.Icc 0 t) :
    (4/5:ℝ) ≤ k f t z := by
  have hz0 := hz.1
  have hzt := hz.2
  cases f <;> norm_num [domain,left,right] at ht <;> obtain ⟨ht1,ht2⟩ := ht <;>
    simp only [k,K] <;> nlinarith

private theorem r64_ell_lower {f : Family} {t z : ℝ} (ht : t∈domain f) (hz : z∈Set.Icc 0 t) :
    (2/5:ℝ) ≤ ell f t z := by
  have hz0 := hz.1
  have hzt := hz.2
  cases f <;> norm_num [domain,left,right] at ht <;> obtain ⟨ht1,ht2⟩ := ht <;>
    simp only [ell,L] <;> nlinarith

private theorem r64_c0_outer : r64_c0 outerVariable=0 := by simp [r64_c0,outerVariable]
private theorem r64_c0_inner : r64_c0 innerVariable=0 := by simp [r64_c0,innerVariable]

private theorem r64_c0_parameter (f : Family) :
    r64_c0 (SolePositiveTPolynomials.parameter f)=(left f+right f)/2 := by
  simp only [SolePositiveTPolynomials.parameter,r64_c0_add,r64_c0_mul,r64_c0_constant,
    r64_c0_outer,mul_zero,add_zero]

private theorem r64_c0_second (f : Family) :
    r64_c0 (secondParameter f)=(left f+right f)/2/2 := by
  simp only [secondParameter,r64_c0_mul,r64_c0_add,r64_c0_constant,r64_c0_inner,
    r64_c0_parameter]
  ring

private theorem r64_seed_value (s : ScalarCase) (i : Fin 7) :
    (1/20:ℝ) ≤ Expression.value (fun j => (r64_c0 ((«variables» s) j):ℝ)) (rootSquare s i) := by
  obtain ⟨tq,htq⟩ : ∃ tq : ℚ,tq=(left s.family+right s.family)/2 := ⟨_,rfl⟩
  have ho := interval_order s.family
  have hl : (0:ℝ) ≤ (left s.family:ℝ) := by exact_mod_cast ho.1
  have hlr : (left s.family:ℝ) < (right s.family:ℝ) := by exact_mod_cast ho.2.1
  have hr : (right s.family:ℝ) ≤ 7/10 := by
    have h := (Rat.cast_le (K := ℝ)).mpr ho.2.2
    simpa using h
  have htqr : (tq:ℝ)=((left s.family:ℝ)+(right s.family:ℝ))/2 := by rw [htq]; push_cast; ring
  have ht : (tq:ℝ)∈domain s.family := ⟨by rw [htqr]; linarith,by rw [htqr]; linarith⟩
  have hz : (tq:ℝ)/2∈Set.Icc 0 (tq:ℝ) := ⟨by rw [htqr]; linarith,by rw [htqr]; linarith⟩
  have ht7 : (tq:ℝ)∈Set.Icc 0 (7/10:ℝ) := ⟨by rw [htqr]; linarith,by rw [htqr]; linarith⟩
  have hz7 : (tq:ℝ)/2∈Set.Icc 0 (7/10:ℝ) := ⟨by rw [htqr]; linarith,by rw [htqr]; linarith⟩
  have hp : r64_c0 (SolePositiveTPolynomials.parameter s.family)=tq := by
    rw [r64_c0_parameter,htq]
  have hs2 : r64_c0 (secondParameter s.family)=tq/2 := by rw [r64_c0_second,htq]
  have hd : r64_c0 (TensorPolynomialEnclosure.sub (SolePositiveTPolynomials.parameter s.family)
      (secondParameter s.family))=tq/2 := by
    rw [r64_c0_sub,hp,hs2]
    ring
  have hU0 : (r64_c0 ((«variables» s) 0):ℝ)=tq := by
    show (r64_c0 (SolePositiveTPolynomials.parameter s.family):ℝ)=tq
    rw [hp]
  have hU1 : (r64_c0 ((«variables» s) 1):ℝ)=tq/2 := by
    show (r64_c0 (secondParameter s.family):ℝ)=tq/2
    rw [hs2]
    push_cast
    ring
  have hU6 : 0 ≤ (r64_c0 ((«variables» s) 6):ℝ) := by
    show 0 ≤ (r64_c0 (sine (eParameter s)):ℝ)
    rw [r64_c0_sine]
    apply (r64_sin13_bounds _).1
    unfold eParameter
    split_ifs
    · rw [r64_c0_constant]
      norm_num
    · rw [hd]
      push_cast
      exact hz7
  have hU7 : (3/4:ℝ) ≤ (r64_c0 ((«variables» s) 7):ℝ) := by
    show (3/4:ℝ) ≤ (r64_c0 (cosine (eParameter s)):ℝ)
    rw [r64_c0_cosine]
    apply r64_cos14_lower
    unfold eParameter
    split_ifs
    · rw [r64_c0_constant]
      norm_num
    · rw [hd]
      push_cast
      exact hz7
  have hU8 : 0 ≤ (r64_c0 ((«variables» s) 8):ℝ) ∧ (r64_c0 ((«variables» s) 8):ℝ) ≤ 13/20 := by
    show 0 ≤ (r64_c0 (sine (SolePositiveTPolynomials.parameter s.family)):ℝ) ∧
      (r64_c0 (sine (SolePositiveTPolynomials.parameter s.family)):ℝ) ≤ 13/20
    rw [r64_c0_sine,hp]
    exact r64_sin13_bounds ht7
  set U := fun j => (r64_c0 ((«variables» s) j):ℝ) with hU
  have hfirst : ∀ j : Fin 4,(2/5:ℝ) ≤ Expression.value U (firstE s j) := by
    intro j
    fin_cases j
    · show (2/5:ℝ) ≤ Expression.value U (lambdaE s.family)
      unfold lambdaE
      split_ifs <;> simp [r64_v_lit,r64_v_one] <;> norm_num
    · show (2/5:ℝ) ≤ Expression.value U (kE s.family)
      rw [r64_kE_w]
      have h := r64_k_lower ht hz
      simp only [hU,hU0,hU1]
      linarith
    · show (2/5:ℝ) ≤ Expression.value U (ellE s.family)
      rw [r64_ellE_w]
      simp only [hU,hU0,hU1]
      exact r64_ell_lower ht hz
    · show (2/5:ℝ) ≤ Expression.value U (pE s)
      unfold pE
      split_ifs
      · simp only [ce,se,r64_v_add,r64_v_mul,r64_v_var,r64_epsilonE_w]
        have he := (coefficient_positive ht hz).2.2.2.2.1
        simp only [hU,hU0] at he ⊢
        have := mul_nonneg he hU6
        linarith
      · rw [r64_v_one]
        norm_num
  unfold rootSquare
  split_ifs with h4 h5 h6
  · unfold squareE
    obtain ⟨F,hF⟩ : ∃ F,F=Expression.value U (firstE s ⟨i.val,h4⟩) := ⟨_,rfl⟩
    obtain ⟨S,hS⟩ : ∃ S,S=Expression.value U (secondE s ⟨i.val,h4⟩) := ⟨_,rfl⟩
    have hF2 := hfirst ⟨i.val,h4⟩
    rw [← hF] at hF2
    have hsq : (2/5:ℝ)^2 ≤ F^2 := pow_le_pow_left₀ (by norm_num) hF2 2
    split_ifs
    · simp only [r64_v_sub,r64_v_add,r64_v_pow,r64_v_mul,r64_v_two,st,r64_v_var]
      rw [← hF,← hS]
      have hσ := hU8
      simp only [hU] at hσ ⊢
      set σ := (r64_c0 ((«variables» s) 8):ℝ)
      nlinarith [mul_nonneg hσ.1 (sq_nonneg (F-S)),sq_nonneg S]
    · simp only [r64_v_sub,r64_v_add,r64_v_pow,r64_v_zero]
      rw [← hF,← hS]
      nlinarith [sq_nonneg S]
  · simp only [r64_v_add,r64_v_pow,r64_v_one]
    nlinarith [sq_nonneg (Expression.value U (gE s.family))]
  · simp only [r64_v_add,r64_v_pow,r64_v_one]
    nlinarith [sq_nonneg (Expression.value U etaE)]
  · simp only [r64_v_add,r64_v_pow,r64_v_one]
    nlinarith [sq_nonneg (Expression.value U (epsilonE s.family))]

private theorem r64_seeds_positive (s : ScalarCase) (i : Fin 7) :
    0<rootSeed (Expression.enclose («variables» s) (rootSquare s i)) := by
  apply r64_nearestRoot_pos
  have h := r64_seed_value s i
  rw [← r64_c0_enclose] at h
  show (1/20:ℚ) ≤ r64_c0 (Expression.enclose («variables» s) (rootSquare s i))
  have h2 : ((1/20:ℚ):ℝ) ≤ (r64_c0 (Expression.enclose («variables» s) (rootSquare s i)):ℝ) := by
    push_cast
    exact h
  exact Rat.cast_le.mp h2

end r64_seeds

/- Exact reductions of one expression recipe. No precomputed coefficient
array, angle subdivision, or external arithmetic result is imported. -/
theorem seeds_positive (s : ScalarCase) (i : Fin 7) :
    0<rootSeed (Expression.enclose («variables» s) (rootSquare s i)) :=
  r64_seeds_positive s i

theorem polynomial_identity (s : ScalarCase) :
    polynomial s=TensorWholeIntervalBernstein.expansion 16 (polynomial s) := by
  have hv : ∀ i,r64_Low ((«variables» s) i).polynomial := by
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

theorem basis_partition :
    (∑ i : Fin 17,∑ j : Fin 17,TensorWholeIntervalBernstein.basis 16 i j)=1 :=
  r64_partition 16

def parameterValue (f : Family) (X : ℝ) : ℝ :=
  ((left f:ℝ)+(right f:ℝ))/2+((right f:ℝ)-(left f:ℝ))/2*X
def secondValue (f : Family) (X Y : ℝ) : ℝ := parameterValue f X*(1+Y)/2

def inputs (s : ScalarCase) (t z : ℝ) : Fin 11 → ℝ :=
  ![t,z,Real.sin (x s t z),Real.cos (x s t z),Real.sin z,Real.cos z,
    Real.sin (SoleTScalarModel.e s t z),Real.cos (SoleTScalarModel.e s t z),Real.sin t,Real.cos t,Real.sin (SoleTScalarModel.e s t z/2)]

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

theorem parameter_contains (f : Family) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    Contains (parameter f) X Y (parameterValue f X) := by
  have h := (contains_constant ((left f+right f)/2) X Y).add
    ((contains_constant ((right f-left f)/2) X Y).mul (contains_outer X Y) hX hY)
  simpa [parameter,parameterValue] using h

theorem variables_contain (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    ∀ i,Contains («variables» s i) X Y
      (inputs s (parameterValue s.family X) (secondValue s.family X Y) i) := by
  obtain ⟨t,htd⟩ : ∃ t,t=parameterValue s.family X := ⟨_,rfl⟩
  obtain ⟨z,hzd⟩ : ∃ z,z=secondValue s.family X Y := ⟨_,rfl⟩
  rw [← htd,← hzd]
  have ht : t∈domain s.family := htd ▸ parameter_mem s.family hX
  have hz : z∈Set.Icc 0 t := by rw [htd,hzd]; exact second_mem s.family hX hY
  have htc : Contains (parameter s.family) X Y t := htd ▸ parameter_contains s.family hX hY
  have hzc : Contains (secondParameter s.family) X Y z := by
    have h := (htc.mul ((contains_constant 1 X Y).add (contains_inner X Y)) hX hY).mul
      (contains_constant (1/2) X Y) hX hY
    have he : t*((1:ℚ)+Y)*((1/2:ℚ):ℝ)=z := by
      rw [hzd,htd,secondValue]
      push_cast
      ring
    rw [he] at h
    exact h
  have hzero : Contains (constant 0) X Y 0 := by simpa using contains_constant 0 X Y
  have hxc : Contains (xParameter s) X Y (x s t z) := by
    unfold xParameter x
    split_ifs
    · exact htc.sub hzc
    · exact hzero
  have hec : Contains (eParameter s) X Y (SoleTScalarModel.e s t z) := by
    unfold eParameter SoleTScalarModel.e
    split_ifs
    · exact hzero
    · exact htc.sub hzc
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  have hhalf : SoleTScalarModel.e s t z/2∈Set.Icc 0 frameCap := by
    have he' := he
    simp only [frameCap,Set.mem_Icc] at he' ⊢
    constructor <;> linarith [he'.1,he'.2]
  have hh := (hec.mul (contains_constant (1/2) X Y) hX hY).sine hX hY
    (by simpa [div_eq_mul_inv] using hhalf)
  have hhalf_eq : SoleTScalarModel.e s t z*((1/2:ℚ):ℝ)=SoleTScalarModel.e s t z/2 := by
    push_cast
    ring
  rw [hhalf_eq] at hh
  intro i
  fin_cases i
  · exact htc
  · exact hzc
  · exact hxc.sine hX hY hx
  · exact hxc.cosine hX hY hx
  · exact hzc.sine hX hY hz'
  · exact hzc.cosine hX hY hz'
  · exact hec.sine hX hY he
  · exact hec.cosine hX hY he
  · exact htc.sine hX hY (angle ht)
  · exact htc.cosine hX hY (angle ht)
  · exact hh

/-! ### The packed certificate

The expression is mirrored by an `IE` expression whose literals are integer fractions and whose
seven roots are extra variables. The roots are evaluated once per family, `td`, `atG`, root and
sign pattern by the packed Taylor models of `PackedModels`, then the whole expression, and the
kernel checks its degree-16 Bernstein coefficients in natural-number arithmetic. The root seeds
are checked the same way at the center of the square. -/

section packed
open PackedModels

/-- Expressions of packed models over the eleven inputs (`inl`) and the seven roots (`inr`). -/
abbrev IExpr := IE (Fin 11 ⊕ Fin 7)
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
def shalfI : IExpr := .var (.inl 10)

def KI : Family → IExpr
  | .ehLow => lq 17253 20000+lq 11 20*tI+lq 3 10*tI^2
  | .ehMiddle => lq 983 1000+lq 1 10*(tI-lq 1 5)-lq 3 10*(tI-lq 1 5)^2
  | .ehHigh => lq 1017 1000-lq 1 50*tI
  | .deLow => lq 53 50-lq 1 10*tI
  | .deHigh => lq 107 100-lq 3 25*tI
def LI : Family → IExpr
  | .ehLow => lq 50521 100000+lq 823 1000*tI+lq 7 10*tI^2
  | .ehMiddle => lq 349 500+lq 9 10*(tI-lq 1 5)-(tI-lq 1 5)^2
  | .ehHigh => lq 7 10+lq 9 25*tI
  | .deLow => lq 113 200+lq 3 4*tI
  | .deHigh => lq 77 100+lq 1 5*tI
def CI : Family → IExpr
  | .ehLow => KI .ehLow+lq 3 10*tI
  | .ehMiddle => lq 209 200+lq 13 20*(tI-lq 1 5)-lq 3 2*(tI-lq 1 5)^2
  | .ehHigh | .deHigh => lq 113 100
  | .deLow => lq 903 1000+lq 13 20*tI
def gI : Family → IExpr
  | .ehLow | .deLow => lq 8 25
  | .ehMiddle => lq 31 100
  | .ehHigh => lq 27 100+lq 2 25*tI
  | .deHigh => lq 3 10+lq 1 20*tI
def epsilonI : Family → IExpr
  | .ehLow => lq 131 500+lq 267 1000*tI+lq 1 10*tI^2
  | .ehMiddle => lq 319 1000+lq 1 5*(tI-lq 1 5)
  | _ => 0
def kI (f : Family) : IExpr := KI f+lq 3 50*zI
def ellI (f : Family) : IExpr := LI f-lq 23 100*zI
def cI (f : Family) : IExpr := CI f-lq 53 100*zI
def etaI : IExpr := lq 1 4+lq 33 100*tI
def lambdaI (f : Family) : IExpr := if isDE f then lq 5 4 else 1
def nI (f : Family) : IExpr := kI f*(cxI+gI f*sxI)
def mI (f : Family) : IExpr := cI f*(czI+etaI*szI)
def pI (f : Family) : IExpr := if tiltedE f then ceI+epsilonI f*seI else 1
def firstI (f : Family) : Fin 4 → IExpr := ![lambdaI f,kI f,ellI f,pI f]
def secondI (f : Family) (td : Bool) : Fin 4 → IExpr :=
  ![nI f,ellI f,if td then mI f else cI f,if td then cI f else mI f]
def nuI (s : ScalarCase) : IExpr :=
  ![if isDE s.family then lq 5 4 else nI s.family,ellI s.family,
    if s.td then mI s.family else ellI s.family,lq 1131 1000] s.negative
/-- The square of root `i < 4`, with the cross term when `neg`. -/
def squareI (f : Family) (td : Bool) (i : Fin 4) (neg : Bool) : IExpr :=
  firstI f i^2+secondI f td i^2-
    if neg then 2*firstI f i*secondI f td i*stI else 0
def rootSquareI (f : Family) (td : Bool) (i : Fin 7) (neg : Bool) : IExpr :=
  if hi : i.val<4 then squareI f td ⟨i.val,hi⟩ neg
  else if i.val=4 then 1+gI f^2
  else if i.val=5 then 1+etaI^2 else 1+epsilonI f^2
def rootI (i : Fin 7) : IExpr := .var (.inr i)
def radiusI : IExpr := lq 989385433 500000000
def baseI (s : ScalarCase) : IExpr :=
  kI s.family*(1+2*cxI+(1+2*gI s.family)*sxI)+
    cI s.family*(1+2*czI+(1+2*etaI)*szI)+2*ellI s.family-
    radiusI*(kI s.family*sxI*rootI 4+cI s.family*szI*rootI 5)
def eExpressionI (s : ScalarCase) : IExpr :=
  if tiltedE s.family then
    1+2*ceI+(1+2*epsilonI s.family)*seI-radiusI*seI*rootI 6
  else if isDE s.family then
    1+lq 1 2*ceI+.lit (.sub (.num 1) (.q 1914558470771 1000000000000))*seI+lq 3 2*lq 5 4
  else 3+seI-.lit (.mul (.num 2) (.q 989385433 500000000))*shalfI
/-- The expression with its roots as variables. -/
def skeleton (s : ScalarCase) : IExpr :=
  ((((baseI s+eExpressionI s+nuI s*(ctI-1))-
    radiusI*rootI 0)-radiusI*rootI 1)-
      radiusI*rootI 2)-radiusI*rootI 3

/-- Whether root `i` carries the negative cross term. -/
def isNegative (s : ScalarCase) (i : Fin 7) : Bool := decide (i.val=s.negative.val)

/-- The formulas of the variables: the inputs, and the roots or zero. -/
def formulas (s : ScalarCase) : Fin 11 ⊕ Fin 7 → Expr := Sum.elim Expression.variable (rootExpression s)
def inputFormulas : Fin 11 ⊕ Fin 7 → Expr := Sum.elim Expression.variable fun _ => 0

theorem rootSquareI_eq (s : ScalarCase) (i : Fin 7) :
    (rootSquareI s.family s.td i (isNegative s i)).toExpressionWith inputFormulas=rootSquare s i := by
  rcases s with ⟨f,td,atG,negative⟩
  cases f <;> cases td <;> fin_cases negative <;> fin_cases i <;> rfl

theorem skeleton_eq (s : ScalarCase) : (skeleton s).toExpressionWith (formulas s)=expression s := by
  rcases s with ⟨f,td,atG,negative⟩
  cases f <;> cases td <;> fin_cases negative <;> rfl

/-- The models work at scale `2 ^ 52` with total degree `14`; the seeds use constant models. -/
def config : Config := ⟨52,14,120⟩
def seedConfig : Config := ⟨48,1,116⟩

theorem config_valid : config.Valid := ⟨by decide,by decide⟩
theorem seedConfig_valid : seedConfig.Valid := ⟨by decide,by decide⟩

/-- The center and the half-width of a family's interval. -/
def center : Family → ℕ × ℕ
  | .ehLow => (1,10) | .ehMiddle => (11,40) | .ehHigh => (21,40) | .deLow => (7,40)
  | .deHigh => (21,40)
def halfWidth : Family → ℕ × ℕ
  | .ehLow => (1,10) | .ehMiddle => (3,40) | .ehHigh => (7,40) | .deLow => (7,40)
  | .deHigh => (7,40)

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

/-- The models of the eleven inputs on the square, at any configuration. -/
def inputModels (c : Config) (f : Family) (atG : Bool) : Fin 11 → Model :=
  let x := if atG then gapModel c f else zeroModel c
  let e := if atG then zeroModel c else gapModel c f
  ![tModel c f,zModel c f,Model.sin c x,Model.cos c x,Model.sin c (zModel c f),
    Model.cos c (zModel c f),Model.sin c e,Model.cos c e,Model.sin c (tModel c f),
    Model.cos c (tModel c f),Model.sin c (Model.mul c e (Model.lit c 1 2))]

/-- The constant models of the constant coefficients of the input enclosures, and zero. -/
def pointModels (f : Family) (atG : Bool) : Fin 11 ⊕ Fin 7 → Model :=
  let c := seedConfig
  let t := Model.lit c (center f).1 (center f).2
  let z := Model.lit c (center f).1 (2*(center f).2)
  let g := Model.add c t (Model.neg z)
  let x := if atG then g else zeroModel c
  let e := if atG then zeroModel c else g
  Sum.elim ![t,z,Model.sinPoly c x,Model.cosPoly c x,Model.sinPoly c z,Model.cosPoly c z,
    Model.sinPoly c e,Model.cosPoly c e,Model.sinPoly c t,Model.cosPoly c t,
    Model.sinPoly c (Model.mul c e (Model.lit c 1 2))] fun _ => zeroModel c

/-- The root seeds, `10 ^ 8 · rootSeed`, found from the point models (checked in
`caseCheck`). -/
def seed (f : Family) (td atG : Bool) (i : Fin 7) (neg : Bool) : ℕ :=
  seedOf seedConfig (pointModels f atG) (rootSquareI f td i neg)

/-- The model of a root on the square. -/
def rootModel (f : Family) (td atG : Bool) (i : Fin 7) (neg : Bool) : Model :=
  (IE.sqrtUpper 0 (seed f td atG i neg) (rootSquareI f td i neg)).eval config
    (Sum.elim (inputModels config f atG) fun _ => zeroModel config)

/-- The checks of a root. -/
def rootCheck (f : Family) (td atG : Bool) (i : Fin 7) (neg : Bool) : Bool :=
  seedCheck seedConfig (pointModels f atG) (rootSquareI f td i neg) (seed f td atG i neg) &&
    (rootSquareI f td i neg).seedFree && (rootSquareI f td i neg).poly &&
    (IE.sqrtUpper 0 (seed f td atG i neg) (rootSquareI f td i neg)).poly

/-- The models of the inputs and of the roots of a case. -/
def models (s : ScalarCase) : Fin 11 ⊕ Fin 7 → Model :=
  Sum.elim (inputModels config s.family s.atG) fun i =>
    if i.val=s.negative.val then rootModel s.family s.td s.atG i true
    else rootModel s.family s.td s.atG i false

/-- Everything the kernel checks for one case. -/
def caseCheck (s : ScalarCase) : Bool :=
  check config 16 (models s) (skeleton s) 1 10000 true && (skeleton s).poly &&
    (skeleton s).seedFree &&
    ([0,1,2,3,4,5,6] : List (Fin 7)).all fun i =>
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

/-- The eight cases of a family and a `td`. -/
def chunkCheck (f : Family) (td : Bool) : Bool :=
  allBool fun atG => allFin4 fun neg => caseCheck ⟨f,td,atG,neg⟩

theorem chunk_check (f : Family) (td : Bool) : chunkCheck f td=true := by
  cases f <;> cases td <;> decide +kernel

theorem case_check (s : ScalarCase) : caseCheck s=true :=
  allFin4_eq (allBool_eq (chunk_check s.family s.td) s.atG) s.negative

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

theorem half_contains {c : Config} (hc : c.Valid) {m : Model} {x y v : ℝ} (hx : |x|≤1)
    (hy : |y|≤1) (h : m.Contains c x y v) :
    (Model.mul c m (Model.lit c 1 2)).Contains c x y (v/2) := by
  have h' := Model.contains_mul hc hx hy h (Model.contains_lit c 1 2)
  have e : v/2=v*(((1:ℤ):ℝ)/((2:ℕ):ℝ)) := by push_cast; ring
  rw [e]
  exact h'

/-- The input models contain the inputs on the square. -/
theorem inputModels_contain {c : Config} (hc : c.Valid) (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1)
    (hY : |Y|≤1) : ∀ i,(inputModels c s.family s.atG i).Contains c X Y
      (inputs s (parameterValue s.family X) (secondValue s.family X Y) i) := by
  have ht := parameter_mem s.family hX
  have hz := second_mem s.family hX hY
  have htm := tModel_contains hc s.family hX hY
  have hzm := zModel_contains hc s.family hX hY
  have hgm : (gapModel c s.family).Contains c X Y
      (parameterValue s.family X-secondValue s.family X Y) := by
    have h := Model.contains_add hc htm (Model.contains_neg hzm)
    rwa [← sub_eq_add_neg] at h
  have hxm : (if s.atG then gapModel c s.family else zeroModel c).Contains c X Y
      (x s (parameterValue s.family X) (secondValue s.family X Y)) := by
    unfold x
    split_ifs
    exacts [hgm,zeroModel_contains c X Y]
  have hem : (if s.atG then zeroModel c else gapModel c s.family).Contains c X Y
      (SoleTScalarModel.e s (parameterValue s.family X) (secondValue s.family X Y)) := by
    unfold SoleTScalarModel.e
    split_ifs
    exacts [zeroModel_contains c X Y,hgm]
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  have hhalf : SoleTScalarModel.e s (parameterValue s.family X) (secondValue s.family X Y)/2∈
      Set.Icc 0 frameCap := by
    have he' := he
    simp only [frameCap,Set.mem_Icc] at he' ⊢
    constructor <;> linarith [he'.1,he'.2]
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
  · exact Model.contains_sin hc hX hY (half_contains hc hX hY hem) hhalf

theorem value_zero (v : Fin 11 → ℝ) : Expression.value v (0 : Expr)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  simp

/-- The point models contain the constant coefficients of the input enclosures. -/
private theorem pointModels_contain (s : ScalarCase) :
    ∀ k,(pointModels s.family s.atG k).Contains seedConfig 0 0
      ((inputFormulas k).value (fun j => (r64_c0 ((«variables» s) j):ℝ))) := by
  have hc := seedConfig_valid
  have h0 : |(0:ℝ)|≤1 := by simp
  set M : ℝ := ((left s.family:ℝ)+(right s.family:ℝ))/2 with hM
  have hP : (r64_c0 (SolePositiveTPolynomials.parameter s.family):ℝ)=M := by
    rw [r64_c0_parameter]; push_cast; ring
  have hS : (r64_c0 (secondParameter s.family):ℝ)=M*(1/2) := by
    rw [r64_c0_second]; push_cast; ring
  have hD : (r64_c0 (TensorPolynomialEnclosure.sub (SolePositiveTPolynomials.parameter s.family)
      (secondParameter s.family)):ℝ)=M+-(M*(1/2)) := by
    rw [r64_c0_sub]; push_cast; rw [hP,hS]; ring
  have h0κ : (r64_c0 (constant 0):ℝ)=0 := by rw [r64_c0_constant]; simp
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
      else zeroModel seedConfig).Contains seedConfig 0 0 (r64_c0 (xParameter s):ℝ) := by
    unfold xParameter
    split_ifs
    · rw [hD]; exact hgm
    · rw [h0κ]; exact zeroModel_contains seedConfig 0 0
  have hem : (if s.atG then zeroModel seedConfig else Model.add seedConfig
      (Model.lit seedConfig (center s.family).1 (center s.family).2)
      (Model.neg (Model.lit seedConfig (center s.family).1 (2*(center s.family).2)))).Contains
      seedConfig 0 0 (r64_c0 (eParameter s):ℝ) := by
    unfold eParameter
    split_ifs
    · rw [h0κ]; exact zeroModel_contains seedConfig 0 0
    · rw [hD]; exact hgm
  have hhm := half_contains hc h0 h0 hem
  have hH : (r64_c0 (mul (eParameter s) (constant (1/2))):ℝ)=(r64_c0 (eParameter s):ℝ)/2 := by
    rw [r64_c0_mul,r64_c0_constant]; push_cast; ring
  rintro (j|j)
  · fin_cases j
    · show (Model.lit seedConfig ((center s.family).1:ℤ) (center s.family).2).Contains seedConfig 0 0
        (r64_c0 (SolePositiveTPolynomials.parameter s.family):ℝ)
      rw [hP]; exact htm
    · show (Model.lit seedConfig ((center s.family).1:ℤ) (2*(center s.family).2)).Contains
        seedConfig 0 0 (r64_c0 (secondParameter s.family):ℝ)
      rw [hS]; exact hzm
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0 (r64_c0 (sine (xParameter s)):ℝ)
      rw [r64_c0_sine]; exact Model.contains_sinPoly hc h0 h0 hxm
    · show (Model.cosPoly seedConfig _).Contains seedConfig 0 0 (r64_c0 (cosine (xParameter s)):ℝ)
      rw [r64_c0_cosine]; exact Model.contains_cosPoly hc h0 h0 hxm
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0
        (r64_c0 (sine (secondParameter s.family)):ℝ)
      rw [r64_c0_sine,hS]; exact Model.contains_sinPoly hc h0 h0 hzm
    · show (Model.cosPoly seedConfig _).Contains seedConfig 0 0
        (r64_c0 (cosine (secondParameter s.family)):ℝ)
      rw [r64_c0_cosine,hS]; exact Model.contains_cosPoly hc h0 h0 hzm
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0 (r64_c0 (sine (eParameter s)):ℝ)
      rw [r64_c0_sine]; exact Model.contains_sinPoly hc h0 h0 hem
    · show (Model.cosPoly seedConfig _).Contains seedConfig 0 0 (r64_c0 (cosine (eParameter s)):ℝ)
      rw [r64_c0_cosine]; exact Model.contains_cosPoly hc h0 h0 hem
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0
        (r64_c0 (sine (SolePositiveTPolynomials.parameter s.family)):ℝ)
      rw [r64_c0_sine,hP]; exact Model.contains_sinPoly hc h0 h0 htm
    · show (Model.cosPoly seedConfig _).Contains seedConfig 0 0
        (r64_c0 (cosine (SolePositiveTPolynomials.parameter s.family)):ℝ)
      rw [r64_c0_cosine,hP]; exact Model.contains_cosPoly hc h0 h0 htm
    · show (Model.sinPoly seedConfig _).Contains seedConfig 0 0
        (r64_c0 (sine (mul (eParameter s) (constant (1/2)))):ℝ)
      rw [r64_c0_sine,hH]; exact Model.contains_sinPoly hc h0 h0 hhm
  · show (zeroModel seedConfig).Contains seedConfig 0 0
      (Expression.value (fun j => (r64_c0 ((«variables» s) j):ℝ)) 0)
    rw [value_zero]
    exact zeroModel_contains seedConfig 0 0

theorem rootCheck_eq (s : ScalarCase) (i : Fin 7) :
    rootCheck s.family s.td s.atG i (isNegative s i)=true := by
  have hc := case_check s
  simp only [caseCheck,Bool.and_eq_true,List.all_eq_true] at hc
  have h := hc.2 i (by fin_cases i <;> simp)
  unfold isNegative
  split_ifs at h with hi
  · rw [decide_eq_true hi]; exact h
  · rw [decide_eq_false hi]; exact h

theorem seed_eq (s : ScalarCase) (i : Fin 7) :
    rootSeed (Expression.enclose («variables» s) (rootSquare s i))=
      (seed s.family s.td s.atG i (isNegative s i):ℚ)/100000000 := by
  have h := rootCheck_eq s i
  simp only [rootCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨hs,hf⟩,hp⟩,-⟩ := h
  have hval : Expression.value (fun j => (r64_c0 ((«variables» s) j):ℝ)) (rootSquare s i)=
      (r64_c0 (Expression.enclose («variables» s) (rootSquare s i)):ℝ) :=
    (r64_c0_enclose _ _).symm
  have hI : (rootSquareI s.family s.td i (isNegative s i)).value
      (fun k => (inputFormulas k).value (fun j => (r64_c0 ((«variables» s) j):ℝ)))=
      Expression.value (fun j => (r64_c0 ((«variables» s) j):ℝ)) (rootSquare s i) := by
    rw [← rootSquareI_eq s i,IE.value_toExpressionWith _ _ _ (IE.isPoly_of_poly _ hp)]
  show nearestRoot (r64_c0 (Expression.enclose («variables» s) (rootSquare s i)))=_
  apply seedCheck_sound seedConfig_valid hs (pointModels_contain s) (IE.seedsOK_of_seedFree _ hf)
    (by rw [hI,hval])
  have h := r64_seed_value s i
  rw [hval] at h
  have h' : (0:ℝ)≤(r64_c0 (Expression.enclose («variables» s) (rootSquare s i)):ℝ) := by
    linarith
  exact_mod_cast h'

/-- The root models contain the roots on the square. -/
theorem rootModel_contains (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) (i : Fin 7) :
    (rootModel s.family s.td s.atG i (isNegative s i)).Contains config X Y
      (Expression.value (inputs s (parameterValue s.family X) (secondValue s.family X Y))
        (rootExpression s i)) := by
  set v := inputs s (parameterValue s.family X) (secondValue s.family X Y)
  have h := rootCheck_eq s i
  simp only [rootCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨-,hf⟩,-⟩,hp⟩ := h
  have hw : ∀ k,((Sum.elim (inputModels config s.family s.atG) fun _ => zeroModel config) k).Contains
      config X Y ((inputFormulas k).value v) := by
    rintro (k|k)
    · exact inputModels_contain config_valid s hX hY k
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
  · exact inputModels_contain config_valid s hX hY k
  · have h := rootModel_contains s hX hY i
    show (if i.val=s.negative.val then rootModel s.family s.td s.atG i true
      else rootModel s.family s.td s.atG i false).Contains config X Y _
    unfold isNegative at h
    split_ifs with hi
    · rw [decide_eq_true hi] at h; exact h
    · rw [decide_eq_false hi] at h; exact h

end packed

theorem model_positive (s : ScalarCase) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    (1/10000:ℝ)<Expression.value
      (inputs s (parameterValue s.family X) (secondValue s.family X Y)) (expression s) := by
  have hc := case_check s
  simp only [caseCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hm,hp⟩,hf⟩,-⟩ := hc
  have h := PackedModels.check_lt config_valid hm hX hY (models_contain s hX hY)
    (PackedModels.IE.seedsOK_of_seedFree _ hf)
  rw [← skeleton_eq,PackedModels.IE.value_toExpressionWith _ _ _ (PackedModels.IE.isPoly_of_poly _ hp)]
  push_cast at h
  exact h

end SquaresInCircles.Eight.TableFree.SolePositiveTPolynomials
