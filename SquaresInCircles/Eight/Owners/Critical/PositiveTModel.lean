module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Int.Star
public import SquaresInCircles.Eight.Owners.Critical.EPosition
public import SquaresInCircles.Eight.Owners.RoundedRadicalExpression

/-!
# Eight squares: the single whole-triangle positive-T derivative model

The expression below is the displayed chain and its displayed derivative,
in their original order. Every radical and reciprocal uses the rounded
degree-twelve binomial rule. The polynomial has total degree at most ten;
there is no angular subdivision or inventory of precomputed coefficients.

The exact rational checks are proved by one kernel evaluation of an exact
natural-number mirror of the rounded arithmetic (namespace `r52_K`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTModel
open RoundedTensorEnclosure RoundedRadicalExpression

inductive Input where
  | q | u | t | z | sinT | cosT | sinZ | cosZ | sinRest | cosRest
  deriving DecidableEq

instance : Fintype Input where
  elems := {.q, .u, .t, .z, .sinT, .cosT, .sinZ, .cosZ, .sinRest, .cosRest}
  complete x := by cases x <;> decide

abbrev Expr := Expression Input
def lit (a : ℚ) : Expr := .literal a
def root (a : Expr) : Expr := .binomial .root a
def inverseRoot (a : Expr) : Expr := .binomial .inverseRoot a
def q : Expr := .variable .q
def u : Expr := .variable .u
def t : Expr := .variable .t
def z : Expr := .variable .z
def sinT : Expr := .variable .sinT
def cosT : Expr := .variable .cosT
def sinZ : Expr := .variable .sinZ
def cosZ : Expr := .variable .cosZ
def sinRest : Expr := .variable .sinRest
def cosRest : Expr := .variable .cosRest

/- The successive circle roots in (6). -/
def r : Expr := root (q-u^2)
def upperRight : Expr := root (q-(2-u)^2)
def upperLeft : Expr := 3-upperRight
def upperHeight : Expr := root (q-upperLeft^2)
def lowerHeight : Expr := 2-upperHeight
def lowerLeft : Expr := root (q-lowerHeight^2)
def first : Expr := 2-cosT*(r-1)+sinT*u
def second : Expr := 1+cosT*lowerHeight-sinT*(lowerLeft-1)
def eta : Expr := lowerHeight/lowerLeft
def lambda : Expr := cosT+eta*sinT
def k0 : Expr := lambda*upperLeft/upperHeight
def ell0 : Expr := k0*(2-u)/upperRight
def c0 : Expr := first/second

/- The adaptation and the four differentiated norm numerators. -/
def ak : Expr := lit (3/50)
def al : Expr := lit (-23/100)
def ac : Expr := lit (-53/100)
def k : Expr := k0+ak*z
def ell : Expr := ell0+al*z
def c : Expr := c0+ac*z
def fZ : Expr := cosZ+eta*sinZ
def p : Expr := cosRest+eta*sinRest
def m : Expr := c*fZ
def pDeriv : Expr := sinRest-eta*cosRest
def mDeriv : Expr := ac*fZ+c*(-sinZ+eta*cosZ)
def radius : Expr := root q
def contactA : Expr := 1+2*eta-radius*root (1+eta^2)
def contactZ : Expr := 1+2*cosZ+contactA*sinZ
def contactDerivZ : Expr := -2*sinZ+contactA*cosZ
def contactDerivRest : Expr := -2*sinRest+contactA*cosRest
def normH2 : Expr := p^2+k^2
def normA2 : Expr := k^2+ell^2
def normB2 : Expr := ell^2+m^2-2*ell*m*sinT
def normD2 : Expr := 1+c^2
def numeratorH : Expr := p*pDeriv+k*ak
def numeratorA : Expr := k*ak+ell*al
def numeratorB : Expr := ell*al+m*mDeriv-(al*m+ell*mDeriv)*sinT
def numeratorD : Expr := c*ac

/-- Exactly the differentiated expression (36). Reciprocal norms use
exponent -1/2 directly, as specified in the polynomial builder. -/
def derivative : Expr :=
  3*ak+2*al+ac*contactZ+c*contactDerivZ-contactDerivRest+
    mDeriv*(cosT-1)-radius*(
      numeratorH*inverseRoot normH2+numeratorA*inverseRoot normA2+
      numeratorB*inverseRoot normB2+numeratorD*inverseRoot normD2)

def qMid : ℚ := ((19577/5000)+(1957767069/500000000))/2
def qWidth : ℚ := ((1957767069/500000000)-(19577/5000))/2
def qModel : Enclosure :=
  round ⟨TensorWholeIntervalPolynomial.scalar qMid,qWidth⟩
def tModel : Enclosure := RoundedTensorEnclosure.add (constant (13/100)) (RoundedTensorEnclosure.scale (3/100) outerVariable)
def zModel : Enclosure := RoundedTensorEnclosure.scale (1/2) (mul tModel (RoundedTensorEnclosure.add (constant 1) innerVariable))
def uModel : Enclosure := widen (RoundedTensorEnclosure.sub (constant 1) (RoundedTensorEnclosure.scale (51/80) tModel)) (7/4000)
def restModel : Enclosure := RoundedTensorEnclosure.sub tModel zModel
def models : Input→Enclosure
  | .q => qModel
  | .u => uModel
  | .t => tModel
  | .z => zModel
  | .sinT => sine tModel
  | .cosT => cosine tModel
  | .sinZ => sine zModel
  | .cosZ => cosine zModel
  | .sinRest => sine restModel
  | .cosRest => cosine restModel
def enclosure : Enclosure := derivative.model models

/-! ## A kernel-checked evaluation of the rounded model

The noncomputable enclosure is mirrored by natural-number data: each polynomial is
stored as the base-`2^170` packing of its positive and negative coefficient parts
(Kronecker substitution), so a product is one big multiplication followed by a
walk over its digits. `rep_eval` proves that the mirror represents the enclosure
exactly, and `finalCheck_true` evaluates the mirror once in the kernel. -/

namespace r52_K
open Polynomial

/-! ### Base-`b` digits (generic) -/

section Digits
variable {b : ℕ} (hb : 0 < b)
include hb

def gdig (b x u : ℕ) : ℕ := x / b^u % b

omit hb in
theorem sum_lt (e : ℕ → ℕ) (he : ∀ u, e u < b) :
    ∀ n, ∑ u ∈ Finset.range n, e u * b^u < b^n
  | 0 => by simp
  | n+1 => by
    rw [Finset.sum_range_succ,pow_succ]
    have h1 := sum_lt e he n
    have h2 : e n+1 ≤ b := he n
    have h3 : (e n+1) * b^n ≤ b*b^n := Nat.mul_le_mul_right _ h2
    rw [mul_comm (b^n) b]
    nlinarith

theorem dig_sum (e : ℕ → ℕ) (he : ∀ u, e u < b) :
    ∀ n k, gdig b (∑ u ∈ Finset.range n, e u * b^u) k = if k < n then e k else 0
  | 0, k => by simp [gdig]
  | n+1, k => by
    rw [Finset.sum_range_succ]
    have hS := sum_lt e he n
    rcases lt_trichotomy k n with hk|hk|hk
    · rw [ite_eq_left (by omega)]
      have hd := dig_sum e he n k
      rw [ite_eq_left hk] at hd
      have hpow : b^n=b^k*b^(n-k) := by rw [← pow_add]; congr 1; omega
      unfold gdig at hd ⊢
      rw [hpow,← mul_assoc,mul_comm (e n) (b^k),mul_assoc,
        Nat.add_mul_div_left _ _ (pow_pos hb k),Nat.add_mod,hd]
      have hm : e n * b^(n-k) % b=0 := by
        apply Nat.mod_eq_zero_of_dvd
        exact Dvd.dvd.mul_left (dvd_pow_self b (by omega)) _
      rw [hm,add_zero]
      exact Nat.mod_eq_of_lt (he k)
    · subst hk
      rw [ite_eq_left (by omega)]
      unfold gdig
      rw [mul_comm (e k),Nat.add_mul_div_left _ _ (pow_pos hb k),
        Nat.div_eq_of_lt hS,zero_add]
      exact Nat.mod_eq_of_lt (he k)
    · rw [ite_eq_right (by omega)]
      unfold gdig
      have hlt : ∑ u ∈ Finset.range n, e u * b^u+e n * b^n<b^k := by
        have h := sum_lt e he (n+1)
        rw [Finset.sum_range_succ] at h
        exact h.trans_le (Nat.pow_le_pow_right hb (by omega))
      rw [Nat.div_eq_of_lt hlt,Nat.zero_mod]

omit hb in
theorem double_sum (w : ℕ) (hw : 0 < w) (d : ℕ → ℕ → ℕ) :
    ∀ I, ∑ i ∈ Finset.range I,∑ j ∈ Finset.range w,d i j * b^(w*i+j)=
      ∑ u ∈ Finset.range (w*I),d (u/w) (u%w) * b^u
  | 0 => by simp
  | I+1 => by
    rw [Finset.sum_range_succ,double_sum w hw d I,Nat.mul_succ,Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j<w := Finset.mem_range.mp hj
    have h1 : (w*I+j)/w=I := by
      rw [Nat.add_comm,Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt hj',zero_add]
    have h2 : (w*I+j)%w=j := by
      rw [Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj']
    rw [h1,h2]

theorem dig_double (w : ℕ) (hw : 0 < w) (d : ℕ → ℕ → ℕ) (hd : ∀ i j, d i j < b)
    (I i j : ℕ) (hi : i < I) (hj : j < w) :
    gdig b (∑ i ∈ Finset.range I,∑ j ∈ Finset.range w,d i j * b^(w*i+j)) (w*i+j)=d i j := by
  rw [double_sum w hw,dig_sum hb (fun u => d (u/w) (u%w)) (fun u => hd _ _)]
  have h1 : (w*i+j)/w=i := by
    rw [Nat.add_comm,Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt hj,zero_add]
  have h2 : (w*i+j)%w=j := by
    rw [Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj]
  have h3 : w*i+j<w*I := by nlinarith
  rw [ite_eq_left h3,h1,h2]

omit hb in
theorem double_lt (w : ℕ) (hw : 0 < w) (d : ℕ → ℕ → ℕ) (hd : ∀ i j, d i j < b) (I : ℕ) :
    ∑ i ∈ Finset.range I,∑ j ∈ Finset.range w,d i j * b^(w*i+j)<b^(w*I) := by
  rw [double_sum w hw]
  exact sum_lt _ (fun u => hd _ _) _

end Digits

@[irreducible] def B : ℕ := 1496577676626844588240573268701473812127674924007424
@[irreducible] def W : ℕ := 21

theorem B_pos : 0 < B := by norm_num [B]
theorem W_pos : 0 < W := by norm_num [W]

def dig (x u : ℕ) : ℕ := gdig B x u

/-! ### Natural bivariate polynomials and their evaluations -/

abbrev NB := Polynomial (Polynomial ℕ)

def cf (P : NB) (i j : ℕ) : ℕ := (P.coeff i).coeff j

def evXY (x y : ℕ) : NB →+* ℕ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (RingHom.id ℕ) y) x

theorem natDegree_lt_of_coeff {R : Type*} [Semiring R] {p : R[X]} {I : ℕ} (hI : 0 < I)
    (h : ∀ i, I ≤ i → p.coeff i=0) : p.natDegree < I := by
  have : p.natDegree ≤ I-1 :=
    natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => h N (by omega))
  omega

theorem evXY_eq (x y : ℕ) {P : NB} {I J : ℕ} (hI : 0 < I) (hJ : 0 < J)
    (hP : ∀ i j, cf P i j ≠ 0 → i < I ∧ j < J) :
    evXY x y P=∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,cf P i j * x^i * y^j := by
  have hdeg : P.natDegree < I := by
    apply natDegree_lt_of_coeff hI
    intro i hi
    ext j
    by_contra hne
    exact absurd (hP i j hne).1 (by omega)
  simp only [evXY,Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_eq_sum_range' _ hdeg]
  apply Finset.sum_congr rfl
  intro i hi
  have hdeg' : (P.coeff i).natDegree < J := by
    apply natDegree_lt_of_coeff hJ
    intro j hj
    by_contra hne
    exact absurd (hP i j hne).2 (by omega)
  rw [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_eq_sum_range' _ hdeg',Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [RingHom.id_apply,cf]
  ring

def evB : NB →+* ℕ := evXY (B^W) B
def ev1 : NB →+* ℕ := evXY 1 1

theorem evB_eq {P : NB} {I : ℕ} (hI : 0 < I) (hP : ∀ i j, cf P i j ≠ 0 → i < I ∧ j < W) :
    evB P=∑ i ∈ Finset.range I,∑ j ∈ Finset.range W,cf P i j * B^(W*i+j) := by
  rw [evB,evXY_eq _ _ hI (by norm_num [W]) hP]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [pow_add,pow_mul]; ring

theorem ev1_eq {P : NB} {I J : ℕ} (hI : 0 < I) (hJ : 0 < J)
    (hP : ∀ i j, cf P i j ≠ 0 → i < I ∧ j < J) :
    ev1 P=∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,cf P i j := by
  rw [ev1,evXY_eq _ _ hI hJ hP]
  simp

theorem cf_le_ev1 {P : NB} {I J : ℕ} (hP : ∀ i j, cf P i j ≠ 0 → i < I ∧ j < J) (i j : ℕ) :
    cf P i j ≤ ev1 P := by
  by_cases h : cf P i j=0
  · rw [h]; exact Nat.zero_le _
  · have hij := hP i j h
    rw [ev1_eq (I := I) (J := J) (by omega) (by omega) hP]
    calc cf P i j ≤ ∑ j ∈ Finset.range J,cf P i j :=
          Finset.single_le_sum (f := fun j => cf P i j) (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr hij.2)
      _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range J,cf P i j)
            (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hij.1)

theorem cf_add (P Q : NB) (i j : ℕ) : cf (P+Q) i j=cf P i j+cf Q i j := by
  simp [cf]

theorem cf_mul_eq_zero {P Q : NB} {a b : ℕ} (hP : ∀ i j, cf P i j ≠ 0 → i+j ≤ a)
    (hQ : ∀ i j, cf Q i j ≠ 0 → i+j ≤ b) (i j : ℕ) (h : a+b < i+j) : cf (P*Q) i j=0 := by
  simp only [cf,Polynomial.coeff_mul,Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  by_cases h1 : cf P x.1 y.1=0
  · simp only [cf] at h1; rw [h1,zero_mul]
  · by_cases h2 : cf Q x.2 y.2=0
    · simp only [cf] at h2; rw [h2,mul_zero]
    · have := hP _ _ h1
      have := hQ _ _ h2
      omega

/-! ### Rational bivariate polynomials -/

abbrev Bv := TensorWholeIntervalPolynomial.Bivar

def bcf (p : Bv) (i j : ℕ) : ℚ := (p.coeff i).coeff j

theorem bv_ext {p q : Bv} (h : ∀ i j, bcf p i j=bcf q i j) : p=q :=
  Polynomial.ext (fun i => Polynomial.ext (fun j => h i j))

def toQ : NB →+* Bv := Polynomial.mapRingHom (Polynomial.mapRingHom (Nat.castRingHom ℚ))

theorem bcf_toQ (P : NB) (i j : ℕ) : bcf (toQ P) i j=(cf P i j : ℚ) := by
  simp [bcf,toQ,cf,Polynomial.coeff_map]

theorem bcf_add (p q : Bv) (i j : ℕ) : bcf (p+q) i j=bcf p i j+bcf q i j := by
  simp [bcf]

theorem bcf_sub (p q : Bv) (i j : ℕ) : bcf (p-q) i j=bcf p i j-bcf q i j := by
  simp [bcf]

theorem bcf_scalar_mul (r : ℚ) (p : Bv) (i j : ℕ) :
    bcf (TensorWholeIntervalPolynomial.scalar r * p) i j=r * bcf p i j := by
  simp [bcf,TensorWholeIntervalPolynomial.scalar,Polynomial.coeff_C_mul]

theorem bcf_scalar (r : ℚ) (i j : ℕ) :
    bcf (TensorWholeIntervalPolynomial.scalar r) i j=if i=0 ∧ j=0 then r else 0 := by
  simp only [bcf,TensorWholeIntervalPolynomial.scalar,Polynomial.coeff_C]
  by_cases hi : i=0
  · subst hi; simp [Polynomial.coeff_C]
  · simp [hi]

theorem bcf_monomial (r : ℚ) (i j a b : ℕ) :
    bcf (TensorWholeIntervalPolynomial.scalar r * X^i * (C X)^j) a b=
      if a=i ∧ b=j then r else 0 := by
  have h : TensorWholeIntervalPolynomial.scalar r * X^i * (C X)^j=C (C r * X^j) * X^i := by
    simp only [TensorWholeIntervalPolynomial.scalar,map_mul,map_pow]; ring
  rw [h]
  simp only [bcf,Polynomial.coeff_C_mul_X_pow]
  by_cases ha : a=i
  · simp only [ha,ite_true,true_and,Polynomial.coeff_C_mul_X_pow]
  · simp [ha]

theorem bcf_double_sum (s : Finset ℕ) (t : ℕ → Finset ℕ) (f : ℕ → ℕ → ℚ) (a b : ℕ) :
    bcf (∑ i ∈ s,∑ j ∈ t i,TensorWholeIntervalPolynomial.scalar (f i j) * X^i * (C X)^j) a b=
      if a ∈ s ∧ b ∈ t a then f a b else 0 := by
  simp only [bcf,Polynomial.finsetSum_coeff]
  have h : ∀ i ∈ s,∑ j ∈ t i,
      ((TensorWholeIntervalPolynomial.scalar (f i j) * X^i * (C X)^j).coeff a).coeff b=
      if a=i ∧ b ∈ t i then f i b else 0 := by
    intro i _
    have h2 : ∀ j ∈ t i,((TensorWholeIntervalPolynomial.scalar (f i j) * X^i * (C X)^j).coeff a).coeff b=
        if a=i ∧ b=j then f i j else 0 := fun j _ => bcf_monomial _ _ _ _ _
    rw [Finset.sum_congr rfl h2]
    by_cases ha : a=i
    · simp only [ha,true_and]
      rw [Finset.sum_ite_eq]
    · simp [ha]
  rw [Finset.sum_congr rfl h]
  by_cases ha : a ∈ s
  · rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro i _ hi; simp [Ne.symm hi]
    · intro h; exact absurd ha h
  · rw [Finset.sum_eq_zero]
    · simp [ha]
    · intro i hi
      have : a ≠ i := fun h => ha (h ▸ hi)
      simp [this]

theorem norm_eq_range {p : Bv} {I J : ℕ} (hp : ∀ i j, bcf p i j ≠ 0 → i < I ∧ j < J) :
    TensorPolynomialEnclosure.norm p=
      ∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,|bcf p i j| := by
  unfold TensorPolynomialEnclosure.norm
  have hin : ∀ i ∈ p.support,∑ j ∈ (p.coeff i).support,|(p.coeff i).coeff j|=
      ∑ j ∈ Finset.range J,|bcf p i j| := by
    intro i _
    apply Finset.sum_subset
    · intro j hj
      rw [Polynomial.mem_support_iff] at hj
      exact Finset.mem_range.mpr (hp i j hj).2
    · intro j _ hj
      rw [Polynomial.notMem_support_iff] at hj
      simp [hj]
  rw [Finset.sum_congr rfl hin]
  apply Finset.sum_subset
  · intro i hi
    rw [Polynomial.mem_support_iff] at hi
    obtain ⟨j,hj⟩ : ∃ j,(p.coeff i).coeff j ≠ 0 := by
      by_contra h
      exact hi (Polynomial.ext (fun j => by
        by_contra hj
        exact h ⟨j,by simpa using hj⟩))
    exact Finset.mem_range.mpr (hp i j hj).1
  · intro i _ hi
    rw [Polynomial.notMem_support_iff] at hi
    simp [bcf,hi]

theorem rc_zero : roundedCoefficient 0=0 := by
  norm_num [roundedCoefficient]

theorem bcf_roundedPolynomial (p : Bv) (a b : ℕ) :
    bcf (roundedPolynomial p) a b=roundedCoefficient (bcf p a b) := by
  unfold roundedPolynomial
  rw [bcf_double_sum]
  by_cases ha : a ∈ p.support ∧ b ∈ (p.coeff a).support
  · rw [ite_eq_left ha]; rfl
  · rw [ite_eq_right ha]
    have : bcf p a b=0 := by
      by_cases h1 : a ∈ p.support
      · have h2 : b ∉ (p.coeff a).support := fun h => ha ⟨h1,h⟩
        rw [Polynomial.notMem_support_iff] at h2
        exact h2
      · rw [Polynomial.notMem_support_iff] at h1
        simp [bcf,h1]
    rw [this,rc_zero]

theorem sum_sum_ite_eq {M : Type*} [AddCommMonoid M] (I J a b : ℕ) (v : M) :
    ∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,(if a=i ∧ b=j then v else 0)=
      if a < I ∧ b < J then v else 0 := by
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,
    Finset.mem_range]

theorem bcf_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Bv) (a b : ℕ) :
    bcf (∑ i ∈ s,f i) a b=∑ i ∈ s,bcf (f i) a b := by
  simp [bcf,Polynomial.finsetSum_coeff]

theorem fin_double_sum {M : Type*} [AddCommMonoid M] (n m : ℕ) (F : ℕ → ℕ → M) :
    ∑ i : Fin n,∑ j : Fin m,F i j=∑ i ∈ Finset.range n,∑ j ∈ Finset.range m,F i j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin m,F i j)]
  exact Finset.sum_congr rfl (fun i _ => Fin.sum_univ_eq_sum_range (F i) m)

theorem bcf_truncate (p : Bv) (a b : ℕ) :
    bcf (RoundedTensorEnclosure.truncate p) a b=if a+b ≤ 10 then bcf p a b else 0 := by
  unfold RoundedTensorEnclosure.truncate
  rw [fin_double_sum 11 11 (fun i j => if i+j ≤ 10 then
    TensorWholeIntervalPolynomial.scalar ((p.coeff i).coeff j)*X^i*(C X)^j else 0)]
  rw [bcf_finset_sum]
  simp only [bcf_finset_sum]
  have h : ∀ i ∈ Finset.range 11,∀ j ∈ Finset.range 11,
      bcf (if i+j ≤ 10 then
        TensorWholeIntervalPolynomial.scalar ((p.coeff i).coeff j)*X^i*(C X)^j else 0) a b=
      if a=i ∧ b=j then (if a+b ≤ 10 then bcf p a b else 0) else 0 := by
    intro i _ j _
    by_cases hij : i+j ≤ 10
    · rw [ite_eq_left hij,bcf_monomial]
      by_cases h' : a=i ∧ b=j
      · obtain ⟨rfl,rfl⟩ := h'; simp [hij,bcf]
      · simp [h']
    · rw [ite_eq_right hij]
      by_cases h' : a=i ∧ b=j
      · obtain ⟨rfl,rfl⟩ := h'; simp [hij,bcf]
      · simp [h',bcf]
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => h i hi j hj)),
    sum_sum_ite_eq]
  by_cases hab : a+b ≤ 10
  · rw [ite_eq_left (by omega)]
  · simp [hab]

/-! ### Rounding arithmetic -/

@[irreducible] def T : ℕ := 1000000000000000000000000

theorem T_pos : 0 < T := by norm_num [T]
theorem T_cast : (T : ℚ)=10^24 := by norm_num [T]

theorem floor_div_nat (N D : ℕ) (hD : 0 < D) : ⌊(N : ℚ)/(D : ℚ)⌋=((N/D : ℕ) : ℤ) := by
  rw [Int.floor_eq_iff]
  simp only [Int.cast_natCast]
  have h1 := Nat.div_mul_le_self N D
  have h2 := Nat.lt_div_mul_add (a := N) hD
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  have h1' : ((N/D:ℕ):ℚ)*D ≤ N := by exact_mod_cast h1
  have h2' : (N:ℚ) < ((N/D:ℕ):ℚ)*D+D := by exact_mod_cast h2
  constructor
  · rw [le_div_iff₀ hD']; exact h1'
  · rw [div_lt_iff₀ hD']; linarith

theorem floor_neg_round (m T : ℕ) (hT : 0 < T) :
    ⌊((T : ℚ)-2*m)/(2*T)⌋= -(((2*m+T-1)/(2*T) : ℕ) : ℤ) := by
  rw [Int.floor_eq_iff]
  set k := (2*m+T-1)/(2*T) with hk
  have h1 : k*(2*T) ≤ 2*m+T-1 := Nat.div_mul_le_self _ _
  have h2 : 2*m+T-1 < k*(2*T)+2*T := Nat.lt_div_mul_add (by omega)
  have h1' : (k:ℚ)*(2*T) ≤ 2*m+T-1 := by
    have : ((2*m+T-1 : ℕ) : ℚ)=2*m+T-1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ 2*m+T)]; ring
    rw [← this]; exact_mod_cast h1
  have h2' : (2*m+T-1 : ℚ) < k*(2*T)+2*T := by
    have : ((2*m+T-1 : ℕ) : ℚ)=2*m+T-1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ 2*m+T)]; ring
    rw [← this]; exact_mod_cast h2
  have hT' : (0:ℚ)<2*T := by positivity
  have hint : ∀ a b : ℕ, (a:ℚ) < b+1 → (a:ℚ) ≤ b := by
    intro a b h
    have : a < b+1 := by exact_mod_cast h
    exact_mod_cast (by omega : a ≤ b)
  constructor
  · push_cast
    rw [le_div_iff₀ hT']
    have : (2*m : ℚ) ≤ k*(2*T)+T := by
      have h3 : 2*m+T-1 < k*(2*T)+2*T := h2
      exact_mod_cast (by omega : 2*m ≤ k*(2*T)+T)
    nlinarith
  · push_cast
    rw [div_lt_iff₀ hT']
    nlinarith

/-- Rounding of a signed digit `x - y` of a product (scale `10^-48`) to scale `10^-24`. -/
def rP (x y : ℕ) : ℕ := if y ≤ x then (2*(x-y)+T)/(2*T) else 0
def rN (x y : ℕ) : ℕ := if y ≤ x then 0 else (2*(y-x)+T-1)/(2*T)

theorem rc_digits (x y : ℕ) :
    roundedCoefficient (((x:ℚ)-y)/10^48)=((rP x y : ℚ)-rN x y)/10^24 := by
  unfold roundedCoefficient coefficientScale
  have hT := T_pos
  by_cases hxy : y ≤ x
  · simp only [rP,rN,ite_eq_left hxy,Nat.cast_zero,sub_zero]
    have e : ((x:ℚ)-y)/10^48*10^24+1/2=((2*(x-y)+T : ℕ) : ℚ)/((2*T : ℕ) : ℚ) := by
      rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hxy,Nat.cast_mul,T_cast]
      field_simp
      ring
    rw [e,floor_div_nat _ _ (by omega),Int.cast_natCast]
  · simp only [rP,rN,ite_eq_right hxy,Nat.cast_zero,zero_sub]
    have e : ((x:ℚ)-y)/10^48*10^24+1/2=((T : ℚ)-2*((y-x : ℕ) : ℚ))/(2*T) := by
      rw [Nat.cast_sub (by omega),T_cast]
      field_simp
      ring
    rw [e,floor_neg_round _ _ hT,Int.cast_neg,Int.cast_natCast]

theorem ceil_div_nat (E D : ℕ) (hD : 0 < D) : ⌈(E : ℚ)/(D : ℚ)⌉=(((E+D-1)/D : ℕ) : ℤ) := by
  rw [Int.ceil_eq_iff]
  simp only [Int.cast_natCast]
  set k := (E+D-1)/D with hk
  have h1 : k*D ≤ E+D-1 := Nat.div_mul_le_self _ _
  have h2 : E+D-1 < k*D+D := Nat.lt_div_mul_add hD
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  constructor
  · rw [lt_div_iff₀ hD']
    rcases Nat.eq_zero_or_pos k with h0|h0
    · rw [h0]; push_cast; nlinarith [(Nat.cast_nonneg E : (0:ℚ) ≤ E)]
    · have : (k-1)*D < E := by
        have : (k-1)*D+D=k*D := by
          rw [Nat.sub_mul,one_mul]; have : D ≤ k*D := Nat.le_mul_of_pos_left D h0; omega
        omega
      have h3 : ((k-1 : ℕ) : ℚ)*D < E := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h3
      push_cast at h3
      linarith
  · rw [div_le_iff₀ hD']
    have : E ≤ k*D := by omega
    exact_mod_cast this

def monoN (i j v : ℕ) : NB := C (C v * X^j) * X^i

theorem cf_monoN (i j v a b : ℕ) : cf (monoN i j v) a b=if a=i ∧ b=j then v else 0 := by
  simp only [cf,monoN,Polynomial.coeff_C_mul_X_pow]
  by_cases ha : a=i
  · simp only [ha,ite_true,true_and,Polynomial.coeff_C_mul_X_pow]
  · simp [ha]

theorem cf_finset_sum {ι : Type*} (s : Finset ι) (f : ι → NB) (a b : ℕ) :
    cf (∑ i ∈ s,f i) a b=∑ i ∈ s,cf (f i) a b := by
  simp [cf,Polynomial.finsetSum_coeff]

theorem cf_monoN_sum (I J : ℕ) (f : ℕ → ℕ → ℕ) (a b : ℕ) :
    cf (∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,monoN i j (f i j)) a b=
      if a < I ∧ b < J then f a b else 0 := by
  simp only [cf_finset_sum,cf_monoN]
  have h : ∀ i ∈ Finset.range I,∀ j ∈ Finset.range J,
      (if a=i ∧ b=j then f i j else 0)=(if a=i ∧ b=j then f a b else 0) := by
    intro i _ j _
    by_cases h : a=i ∧ b=j
    · obtain ⟨rfl,rfl⟩ := h; rfl
    · simp [h]
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => h i hi j hj)),
    sum_sum_ite_eq]

theorem evXY_monoN (x y i j v : ℕ) : evXY x y (monoN i j v)=v*x^i*y^j := by
  simp only [evXY,monoN,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow,RingHom.id_apply]
  ring

theorem evB_monoN_sum (I J : ℕ) (f : ℕ → ℕ → ℕ) :
    evB (∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,monoN i j (f i j))=
      ∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,f i j*B^(W*i+j) := by
  simp only [map_sum,evB,evXY_monoN]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [pow_add,pow_mul]; ring

theorem ev1_monoN_sum (I J : ℕ) (f : ℕ → ℕ → ℕ) :
    ev1 (∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,monoN i j (f i j))=
      ∑ i ∈ Finset.range I,∑ j ∈ Finset.range J,f i j := by
  simp [map_sum,ev1,evXY_monoN]

/-! ### The kernel digit walk -/

@[irreducible] def BW : ℕ := B^W

theorem B_eq : B=2^170 := by unfold B; norm_num
theorem BW_eq : BW=2^3570 := by
  unfold BW; rw [B_eq,show W=21 by unfold W; rfl,← pow_mul]
theorem shr_B (x : ℕ) : x >>> 170=x / B := by rw [Nat.shiftRight_eq_div_pow,B_eq]
theorem land_B (x : ℕ) : x &&& (B-1)=x % B := by rw [B_eq,Nat.and_two_pow_sub_one_eq_mod]
theorem shr_BW (x : ℕ) : x >>> 3570=x / BW := by rw [Nat.shiftRight_eq_div_pow,BW_eq]
theorem land_BW (x : ℕ) : x &&& (BW-1)=x % BW := by rw [BW_eq,Nat.and_two_pow_sub_one_eq_mod]
theorem shl_B (a k : ℕ) : a <<< (170*k)=a * B^k := by rw [Nat.shiftLeft_eq,B_eq,← pow_mul]

abbrev Acc := ℕ × ℕ × ℕ × ℕ × ℕ

def accAdd (a b : Acc) : Acc :=
  (a.1+b.1,a.2.1+b.2.1,a.2.2.1+b.2.2.1,a.2.2.2.1+b.2.2.2.1,a.2.2.2.2+b.2.2.2.2)

theorem accAdd_eq (a b : Acc) : accAdd a b=a+b := rfl

def rowWalk (h : ℕ → ℕ → ℕ → ℕ → Acc) (i : ℕ) : ℕ → ℕ → ℕ → ℕ → Acc → Acc
  | 0, _, _, _, acc => acc
  | f+1, j, x, y, acc =>
    bif x == 0 && y == 0 then acc
    else rowWalk h i f (j+1) (x >>> 170) (y >>> 170) (accAdd acc (h i j (x &&& (B-1)) (y &&& (B-1))))

def walk (h : ℕ → ℕ → ℕ → ℕ → Acc) : ℕ → ℕ → ℕ → ℕ → Acc → Acc
  | 0, _, _, _, acc => acc
  | f+1, i, X, Y, acc =>
    bif X == 0 && Y == 0 then acc
    else walk h f (i+1) (X >>> 3570) (Y >>> 3570) (rowWalk h i W 0 (X &&& (BW-1)) (Y &&& (BW-1)) acc)

theorem rowWalk_eq (h : ℕ → ℕ → ℕ → ℕ → Acc) (h0 : ∀ i j, h i j 0 0=0) (i : ℕ) :
    ∀ f j x y acc,rowWalk h i f j x y acc=
      acc+∑ k ∈ Finset.range f,h i (j+k) (x / B^k % B) (y / B^k % B)
  | 0, j, x, y, acc => by simp [rowWalk]
  | f+1, j, x, y, acc => by
    rw [rowWalk]
    by_cases hxy : x=0 ∧ y=0
    · obtain ⟨rfl,rfl⟩ := hxy
      simp [h0]
    · have hb : (x == 0 && y == 0)=false := by
        rw [Bool.eq_false_iff]
        intro hc
        simp only [Bool.and_eq_true,beq_iff_eq] at hc
        exact hxy hc
      rw [hb,Bool.cond_false,shr_B,shr_B,land_B,land_B,rowWalk_eq h h0 i f (j+1) (x/B) (y/B),
        Finset.sum_range_succ',accAdd_eq]
      simp only [pow_zero,Nat.div_one,add_zero]
      rw [add_assoc]
      congr 1
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,← pow_succ',show j+1+k=j+(k+1) by ring]

theorem mod_digit {b w : ℕ} (hb : 0 < b) (X k : ℕ) (hk : k < w) :
    X % b^w / b^k % b=X / b^k % b := by
  conv_rhs => rw [← Nat.mod_add_div X (b^w)]
  have hpow : b^w=b^k*b^(w-k) := by rw [← pow_add]; congr 1; omega
  rw [hpow,mul_assoc,Nat.add_mul_div_left _ _ (pow_pos hb k),← hpow]
  have hd : b ∣ b^(w-k)*(X/b^w) := Dvd.dvd.mul_right (dvd_pow_self b (by omega)) _
  obtain ⟨c,hc⟩ := hd
  rw [hc,Nat.add_mul_mod_self_left]

theorem walk_eq (h : ℕ → ℕ → ℕ → ℕ → Acc) (h0 : ∀ i j, h i j 0 0=0) :
    ∀ f i X Y acc,walk h f i X Y acc=
      acc+∑ r ∈ Finset.range f,∑ k ∈ Finset.range W,
        h (i+r) k (dig X (W*r+k)) (dig Y (W*r+k))
  | 0, i, X, Y, acc => by simp [walk]
  | f+1, i, X, Y, acc => by
    rw [walk]
    by_cases hXY : X=0 ∧ Y=0
    · obtain ⟨rfl,rfl⟩ := hXY
      simp [h0,dig,gdig]
    · have hb : (X == 0 && Y == 0)=false := by
        rw [Bool.eq_false_iff]
        intro hc
        simp only [Bool.and_eq_true,beq_iff_eq] at hc
        exact hXY hc
      have e1 : ∑ r ∈ Finset.range f,∑ k ∈ Finset.range W,
          h (i+1+r) k (dig (X/BW) (W*r+k)) (dig (Y/BW) (W*r+k))=
          ∑ r ∈ Finset.range f,∑ k ∈ Finset.range W,
          h (i+(r+1)) k (dig X (W*(r+1)+k)) (dig Y (W*(r+1)+k)) := by
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro k _
        have ex : ∀ Z : ℕ, dig (Z/BW) (W*r+k)=dig Z (W*(r+1)+k) := by
          intro Z
          simp only [dig,gdig,BW]
          rw [Nat.div_div_eq_div_mul,← pow_add,show W+(W*r+k)=W*(r+1)+k by ring]
        rw [ex X,ex Y,show i+1+r=i+(r+1) by ring]
      have e2 : ∑ k ∈ Finset.range W,h i (0+k) (X % BW / B^k % B) (Y % BW / B^k % B)=
          ∑ k ∈ Finset.range W,h (i+0) k (dig X (W*0+k)) (dig Y (W*0+k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simp only [dig,gdig,BW,zero_add,add_zero,mul_zero]
        rw [mod_digit B_pos X k hk',mod_digit B_pos Y k hk']
      rw [hb,Bool.cond_false,shr_BW,shr_BW,land_BW,land_BW,walk_eq h h0 f (i+1) (X/BW) (Y/BW),
        rowWalk_eq h h0,e1,e2,
        Finset.sum_range_succ' (fun r => ∑ k ∈ Finset.range W,
          h (i+r) k (dig X (W*r+k)) (dig Y (W*r+k))),add_assoc,add_comm (∑ k ∈ Finset.range W, _)]

/-! ### The representation invariant -/

structure Inv (P N : NB) : Prop where
  supP : ∀ i j, cf P i j ≠ 0 → i+j ≤ 10
  supN : ∀ i j, cf N i j ≠ 0 → i+j ≤ 10
  bP : ∀ i j, cf P i j < B
  bN : ∀ i j, cf N i j < B
  disj : ∀ i j, cf P i j=0 ∨ cf N i j=0

def pol (P N : NB) : Bv := TensorWholeIntervalPolynomial.scalar (1/10^24) * (toQ P-toQ N)

theorem bcf_pol (P N : NB) (i j : ℕ) : bcf (pol P N) i j=((cf P i j : ℚ)-cf N i j)/10^24 := by
  rw [pol,bcf_scalar_mul,bcf_sub,bcf_toQ,bcf_toQ]; ring

theorem sup_lt {P : NB} (h : ∀ i j, cf P i j ≠ 0 → i+j ≤ 10) {I J : ℕ} (hI : 11 ≤ I) (hJ : 11 ≤ J) :
    ∀ i j, cf P i j ≠ 0 → i < I ∧ j < J := by
  intro i j hij; have := h i j hij; omega

theorem Inv.norm {P N : NB} (h : Inv P N) :
    TensorPolynomialEnclosure.norm (pol P N)=((ev1 P : ℚ)+ev1 N)/10^24 := by
  have hs : ∀ i j, bcf (pol P N) i j ≠ 0 → i < 11 ∧ j < 11 := by
    intro i j hij
    rw [bcf_pol] at hij
    by_cases hP : cf P i j=0
    · by_cases hN : cf N i j=0
      · rw [hP,hN] at hij; simp at hij
      · exact sup_lt h.supN (le_refl _) (le_refl _) i j hN
    · exact sup_lt h.supP (le_refl _) (le_refl _) i j hP
  rw [norm_eq_range hs,ev1_eq (by norm_num) (by norm_num) (sup_lt h.supP (le_refl _) (le_refl _)),
    ev1_eq (by norm_num) (by norm_num) (sup_lt h.supN (le_refl _) (le_refl _))]
  push_cast
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl; intro j _
  rw [bcf_pol]
  rcases h.disj i j with h0|h0 <;> rw [h0] <;> simp [abs_div]

theorem Inv.digits {P N : NB} (h : Inv P N) {i j : ℕ} (hj : j < W) :
    dig (evB P) (W*i+j)=cf P i j ∧ dig (evB N) (W*i+j)=cf N i j := by
  have hW : 11 ≤ W := by norm_num [W]
  by_cases hi : i < 11
  · constructor
    · rw [evB_eq (I := 11) (by norm_num) (sup_lt h.supP (le_refl _) hW)]
      exact dig_double B_pos W W_pos _ h.bP 11 i j hi hj
    · rw [evB_eq (I := 11) (by norm_num) (sup_lt h.supN (le_refl _) hW)]
      exact dig_double B_pos W W_pos _ h.bN 11 i j hi hj
  · have hP : cf P i j=0 := by
      by_contra hc; have := h.supP i j hc; omega
    have hN : cf N i j=0 := by
      by_contra hc; have := h.supN i j hc; omega
    rw [hP,hN]
    have e1 : evB P < B^(W*11) := by
      rw [evB_eq (I := 11) (by norm_num) (sup_lt h.supP (le_refl _) hW)]
      exact double_lt W W_pos _ h.bP 11
    have e2 : evB N < B^(W*11) := by
      rw [evB_eq (I := 11) (by norm_num) (sup_lt h.supN (le_refl _) hW)]
      exact double_lt W W_pos _ h.bN 11
    have hle : B^(W*11) ≤ B^(W*i+j) := Nat.pow_le_pow_right B_pos (by nlinarith)
    simp only [dig,gdig]
    rw [Nat.div_eq_of_lt (e1.trans_le hle),Nat.div_eq_of_lt (e2.trans_le hle),Nat.zero_mod]
    exact ⟨rfl,rfl⟩

theorem rc_int (z : ℤ) : roundedCoefficient ((z:ℚ)/10^24)=(z:ℚ)/10^24 := by
  unfold roundedCoefficient coefficientScale
  have e : (z:ℚ)/10^24*10^24+1/2=(z:ℚ)+1/2 := by field_simp
  rw [e]
  have : ⌊(z:ℚ)+1/2⌋=z := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  rw [this]

theorem roundedPolynomial_pol (P N : NB) : roundedPolynomial (pol P N)=pol P N := by
  apply bv_ext; intro i j
  rw [bcf_roundedPolynomial,bcf_pol]
  have := rc_int ((cf P i j : ℤ)-cf N i j)
  push_cast at this
  exact this

theorem upwardError_nat (e : ℕ) : upwardError ((e:ℚ)/10^20)=(e:ℚ)/10^20 := by
  unfold upwardError errorScale
  have : (e:ℚ)/10^20*10^20=((e:ℤ):ℚ) := by field_simp; push_cast; ring
  rw [this,Int.ceil_intCast]
  push_cast; ring

theorem round_pol (P N : NB) (e : ℚ) :
    RoundedTensorEnclosure.round ⟨pol P N,e⟩=⟨pol P N,upwardError e⟩ := by
  simp only [RoundedTensorEnclosure.round,roundedPolynomial_pol,sub_self]
  congr
  simp [TensorPolynomialEnclosure.norm]

/-! ### Kernel records -/

@[irreducible] def E4 : ℕ := 10000
@[irreducible] def E8 : ℕ := 100000000
@[irreducible] def E20 : ℕ := 100000000000000000000
@[irreducible] def E28 : ℕ := 10000000000000000000000000000

structure Enc where
  pos : ℕ
  neg : ℕ
  nrm : ℕ
  err : ℕ
  ok : Bool

def Rep (E : Enc) (A : TensorPolynomialEnclosure.Enclosure) : Prop :=
  ∃ P N : NB,Inv P N ∧ E.pos=evB P ∧ E.neg=evB N ∧ E.nrm=ev1 P+ev1 N ∧
    A.polynomial=pol P N ∧ A.error=(E.err : ℚ)/10^20

theorem digits_of {P : NB} {L : ℕ} (hL : L < W) (hs : ∀ i j, cf P i j ≠ 0 → i+j ≤ L)
    (hb : ∀ i j, cf P i j < B) {i j : ℕ} (hj : j < W) : dig (evB P) (W*i+j)=cf P i j := by
  have hs' : ∀ i j, cf P i j ≠ 0 → i < L+1 ∧ j < W := by
    intro i j h; have := hs i j h; omega
  by_cases hi : i < L+1
  · rw [evB_eq (I := L+1) (by omega) hs']
    exact dig_double B_pos W W_pos _ hb (L+1) i j hi hj
  · have hP : cf P i j=0 := by
      by_contra hc; have := hs i j hc; omega
    rw [hP]
    have e1 : evB P < B^(W*(L+1)) := by
      rw [evB_eq (I := L+1) (by omega) hs']
      exact double_lt W W_pos _ hb (L+1)
    have hle : B^(W*(L+1)) ≤ B^(W*i+j) := Nat.pow_le_pow_right B_pos (by nlinarith)
    simp only [dig,gdig]
    rw [Nat.div_eq_of_lt (e1.trans_le hle),Nat.zero_mod]

def cdiv (a b : ℕ) : ℕ := (a+b-1)/b
def absdiff (a b : ℕ) : ℕ := bif Nat.ble b a then a-b else b-a

theorem absdiff_cast (a b : ℕ) : (absdiff a b : ℚ)=|(a:ℚ)-b| := by
  unfold absdiff
  by_cases h : b ≤ a
  · rw [Nat.ble_eq_true_of_le h,Bool.cond_true,Nat.cast_sub h,abs_of_nonneg (by
      have : (b:ℚ) ≤ a := by exact_mod_cast h
      linarith)]
  · have h' : Nat.ble b a=false := by
      cases hb : Nat.ble b a
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [h',Bool.cond_false,Nat.cast_sub (by omega),abs_of_neg (by
      have : (a:ℚ) < b := by exact_mod_cast (by omega : a < b)
      linarith)]
    ring

theorem cdiv_cast (a b : ℕ) (hb : 0 < b) : ((cdiv a b : ℕ) : ℤ)=⌈(a:ℚ)/(b:ℚ)⌉ := by
  rw [ceil_div_nat a b hb]; rfl

def hAdd (i j x y : ℕ) : Acc :=
  bif Nat.ble y x then ((x-y) <<< (170*(W*i+j)),0,x-y,0,0) else (0,(y-x) <<< (170*(W*i+j)),y-x,0,0)


def kadd (a b : Enc) : Enc :=
  let r := walk hAdd 11 0 (a.pos+b.pos) (a.neg+b.neg) (0,0,0,0,0)
  ⟨r.1,r.2.1,r.2.2.1,a.err+b.err,a.ok && b.ok && Nat.blt (a.nrm+b.nrm) B⟩

def kneg (a : Enc) : Enc := ⟨a.neg,a.pos,a.nrm,a.err,a.ok⟩

def kwiden (a : Enc) (n d : ℕ) : Enc :=
  ⟨a.pos,a.neg,a.nrm,a.err+cdiv (n*E20) d,a.ok && Nat.blt 0 d⟩

/-- positive and negative parts of a signed digit. -/
def ppart (x y : ℕ) : ℕ := if y ≤ x then x-y else 0
def npart (x y : ℕ) : ℕ := if y ≤ x then 0 else y-x

theorem hAdd_spec (i j x y : ℕ) :
    hAdd i j x y=(ppart x y * B^(W*i+j),npart x y * B^(W*i+j),ppart x y+npart x y,0,0) := by
  unfold hAdd ppart npart
  simp only [shl_B]
  by_cases h : y ≤ x
  · rw [Nat.ble_eq_true_of_le h,Bool.cond_true]; simp [h]
  · have h' : Nat.ble y x=false := by
      cases hb : Nat.ble y x
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) h
    rw [h',Bool.cond_false]; simp [h]

theorem hAdd_zero (i j : ℕ) : hAdd i j 0 0=0 := by
  rw [hAdd_spec]; simp [ppart,npart]

theorem part_cast (x y : ℕ) : (ppart x y : ℚ)-npart x y=(x:ℚ)-y := by
  unfold ppart npart
  by_cases h : y ≤ x
  · simp [h,Nat.cast_sub h]
  · simp only [h,ite_false,Nat.cast_zero,zero_sub]
    rw [Nat.cast_sub (by omega)]; ring

theorem rep_neg {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a) :
    Rep (kneg A) (RoundedTensorEnclosure.neg a) := by
  obtain ⟨P,N,hI,hp,hn,hm,hpol,he⟩ := h
  refine ⟨N,P,⟨hI.supN,hI.supP,hI.bN,hI.bP,fun i j => (hI.disj i j).symm⟩,hn,hp,
    by simp [kneg,hm,add_comm],?_,?_⟩
  · simp only [RoundedTensorEnclosure.neg]
    have : -a.polynomial=pol N P := by rw [hpol,pol,pol]; ring
    rw [this,round_pol]
  · simp only [RoundedTensorEnclosure.neg]
    have : -a.polynomial=pol N P := by rw [hpol,pol,pol]; ring
    rw [this,round_pol,he,upwardError_nat]
    simp only [kneg]

section fields
variable (A : Enc) (n d : ℕ)
theorem kwiden_pos : (kwiden A n d).pos=A.pos := by unfold kwiden; exact rfl
theorem kwiden_neg : (kwiden A n d).neg=A.neg := by unfold kwiden; exact rfl
theorem kwiden_nrm : (kwiden A n d).nrm=A.nrm := by unfold kwiden; exact rfl
theorem kwiden_err : (kwiden A n d).err=A.err+cdiv (n*E20) d := by unfold kwiden; exact rfl
theorem kwiden_ok : (kwiden A n d).ok=(A.ok && Nat.blt 0 d) := by unfold kwiden; exact rfl
end fields

theorem rep_widen {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a)
    (n d : ℕ) (hok : (kwiden A n d).ok=true) :
    Rep (kwiden A n d) (RoundedTensorEnclosure.widen a ((n:ℚ)/d)) := by
  obtain ⟨P,N,hI,hp,hn,hm,hpol,he⟩ := h
  have hd : 0 < d := by
    rw [kwiden_ok] at hok
    simp only [Bool.and_eq_true,Nat.blt_eq] at hok; exact hok.2
  refine ⟨P,N,hI,by rw [kwiden_pos]; exact hp,by rw [kwiden_neg]; exact hn,
    by rw [kwiden_nrm]; exact hm,?_,?_⟩
  · simp only [RoundedTensorEnclosure.widen]; rw [hpol,round_pol]
  · simp only [RoundedTensorEnclosure.widen]
    rw [hpol,round_pol,he,kwiden_err]
    unfold upwardError errorScale
    have e : ((A.err:ℚ)/10^20+n/d)*10^20=((A.err : ℤ) : ℚ)+((n*E20 : ℕ) : ℚ)/((d : ℕ) : ℚ) := by
      have : (E20 : ℚ)=10^20 := by norm_num [E20]
      push_cast; rw [this]; field_simp
    rw [e,Int.ceil_intCast_add,← cdiv_cast _ _ hd]
    push_cast; ring

section kadd_fields
variable (E1 E2 : Enc)
theorem kadd_pos : (kadd E1 E2).pos=(walk hAdd 11 0 (E1.pos+E2.pos) (E1.neg+E2.neg) (0,0,0,0,0)).1 := by
  unfold kadd; exact rfl
theorem kadd_neg : (kadd E1 E2).neg=(walk hAdd 11 0 (E1.pos+E2.pos) (E1.neg+E2.neg) (0,0,0,0,0)).2.1 := by
  unfold kadd; exact rfl
theorem kadd_nrm : (kadd E1 E2).nrm=(walk hAdd 11 0 (E1.pos+E2.pos) (E1.neg+E2.neg) (0,0,0,0,0)).2.2.1 := by
  unfold kadd; exact rfl
theorem kadd_err : (kadd E1 E2).err=E1.err+E2.err := by unfold kadd; exact rfl
theorem kadd_ok : (kadd E1 E2).ok=(E1.ok && E2.ok && Nat.blt (E1.nrm+E2.nrm) B) := by
  unfold kadd; exact rfl
end kadd_fields

theorem walk_sum (h : ℕ → ℕ → ℕ → ℕ → Acc) (h0 : ∀ i j, h i j 0 0=0) (f : ℕ) (P N : NB) {L : ℕ}
    (hL : L < W) (sP : ∀ i j, cf P i j ≠ 0 → i+j ≤ L) (sN : ∀ i j, cf N i j ≠ 0 → i+j ≤ L)
    (bP : ∀ i j, cf P i j < B) (bN : ∀ i j, cf N i j < B) :
    walk h f 0 (evB P) (evB N) (0,0,0,0,0)=
      ∑ r ∈ Finset.range f,∑ k ∈ Finset.range W,h r k (cf P r k) (cf N r k) := by
  rw [walk_eq h h0,show ((0,0,0,0,0) : Acc)=0 from rfl,zero_add]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [zero_add,digits_of hL sP bP hk',digits_of hL sN bN hk']

theorem ppart_le (x y : ℕ) : ppart x y ≤ x := by unfold ppart; split_ifs <;> omega
theorem npart_le (x y : ℕ) : npart x y ≤ y := by unfold npart; split_ifs <;> omega
theorem ppart_ne (x y : ℕ) (h : ppart x y ≠ 0) : x ≠ 0 := by
  unfold ppart at h; split_ifs at h <;> omega
theorem npart_ne (x y : ℕ) (h : npart x y ≠ 0) : y ≠ 0 := by
  unfold npart at h; split_ifs at h <;> omega
theorem part_disj (x y : ℕ) : ppart x y=0 ∨ npart x y=0 := by
  unfold ppart npart; split_ifs <;> simp

theorem rep_add {E1 E2 : Enc} {e1 e2 : TensorPolynomialEnclosure.Enclosure}
    (h1 : Rep E1 e1) (h2 : Rep E2 e2) (hok : (kadd E1 E2).ok=true) :
    Rep (kadd E1 E2) (RoundedTensorEnclosure.add e1 e2) := by
  obtain ⟨P1,N1,I1,hp1,hn1,hm1,hpol1,he1⟩ := h1
  obtain ⟨P2,N2,I2,hp2,hn2,hm2,hpol2,he2⟩ := h2
  rw [kadd_ok] at hok
  simp only [Bool.and_eq_true,Nat.blt_eq] at hok
  have hlt := hok.2
  have hW : (10:ℕ) < W := by norm_num [W]
  have hX : E1.pos+E2.pos=evB (P1+P2) := by rw [hp1,hp2,map_add]
  have hY : E1.neg+E2.neg=evB (N1+N2) := by rw [hn1,hn2,map_add]
  have l1P := cf_le_ev1 (sup_lt I1.supP (le_refl 11) (le_refl 11))
  have l1N := cf_le_ev1 (sup_lt I1.supN (le_refl 11) (le_refl 11))
  have l2P := cf_le_ev1 (sup_lt I2.supP (le_refl 11) (le_refl 11))
  have l2N := cf_le_ev1 (sup_lt I2.supN (le_refl 11) (le_refl 11))
  have sX : ∀ i j, cf (P1+P2) i j ≠ 0 → i+j ≤ 10 := by
    intro i j h; rw [cf_add] at h
    by_cases h1 : cf P1 i j=0
    · exact I2.supP i j (by omega)
    · exact I1.supP i j h1
  have sY : ∀ i j, cf (N1+N2) i j ≠ 0 → i+j ≤ 10 := by
    intro i j h; rw [cf_add] at h
    by_cases h1 : cf N1 i j=0
    · exact I2.supN i j (by omega)
    · exact I1.supN i j h1
  have bX : ∀ i j, cf (P1+P2) i j < B := by
    intro i j; rw [cf_add]; have := l1P i j; have := l2P i j; omega
  have bY : ∀ i j, cf (N1+N2) i j < B := by
    intro i j; rw [cf_add]; have := l1N i j; have := l2N i j; omega
  have hw := walk_sum hAdd hAdd_zero 11 (P1+P2) (N1+N2) hW sX sY bX bY
  set x := fun r k => cf (P1+P2) r k with hx
  set y := fun r k => cf (N1+N2) r k with hy
  set Rp := ∑ r ∈ Finset.range 11,∑ k ∈ Finset.range W,monoN r k (ppart (x r k) (y r k)) with hRp
  set Rn := ∑ r ∈ Finset.range 11,∑ k ∈ Finset.range W,monoN r k (npart (x r k) (y r k)) with hRn
  have cRp : ∀ a b, cf Rp a b=if a < 11 ∧ b < W then ppart (x a b) (y a b) else 0 :=
    fun a b => cf_monoN_sum _ _ _ a b
  have cRn : ∀ a b, cf Rn a b=if a < 11 ∧ b < W then npart (x a b) (y a b) else 0 :=
    fun a b => cf_monoN_sum _ _ _ a b
  have hInv : Inv Rp Rn := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b h; rw [cRp] at h; split_ifs at h with hab
      · exact sX a b (ppart_ne _ _ h)
      · exact absurd rfl h
    · intro a b h; rw [cRn] at h; split_ifs at h with hab
      · exact sY a b (npart_ne _ _ h)
      · exact absurd rfl h
    · intro a b; rw [cRp]; split_ifs
      · exact (ppart_le _ _).trans_lt (bX a b)
      · exact B_pos
    · intro a b; rw [cRn]; split_ifs
      · exact (npart_le _ _).trans_lt (bY a b)
      · exact B_pos
    · intro a b; rw [cRp,cRn]; split_ifs
      · exact part_disj _ _
      · simp
  have hp : e1.polynomial+e2.polynomial=pol Rp Rn := by
    rw [hpol1,hpol2]
    apply bv_ext; intro a b
    rw [bcf_add,bcf_pol,bcf_pol,bcf_pol,cRp,cRn]
    split_ifs with hab
    · rw [part_cast]; simp only [hx,hy,cf_add]; push_cast; ring
    · have h0 : ¬ a+b ≤ 10 := by intro h; apply hab; constructor <;> omega
      have e1 : cf P1 a b=0 := by by_contra hc; exact h0 (I1.supP a b hc)
      have e2 : cf P2 a b=0 := by by_contra hc; exact h0 (I2.supP a b hc)
      have e3 : cf N1 a b=0 := by by_contra hc; exact h0 (I1.supN a b hc)
      have e4 : cf N2 a b=0 := by by_contra hc; exact h0 (I2.supN a b hc)
      rw [e1,e2,e3,e4]; simp
  refine ⟨Rp,Rn,hInv,?_,?_,?_,?_,?_⟩
  · rw [kadd_pos,hX,hY,hw,Prod.fst_sum,hRp,evB_monoN_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [Prod.fst_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [hAdd_spec]
  · rw [kadd_neg,hX,hY,hw,Prod.snd_sum,Prod.fst_sum,hRn,evB_monoN_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [Prod.snd_sum,Prod.fst_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [hAdd_spec]
  · rw [kadd_nrm,hX,hY,hw,Prod.snd_sum,Prod.snd_sum,Prod.fst_sum,hRp,hRn,ev1_monoN_sum,
      ev1_monoN_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    rw [Prod.snd_sum,Prod.snd_sum,Prod.fst_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [hAdd_spec]
  · simp only [RoundedTensorEnclosure.add]
    rw [hp,round_pol]
  · simp only [RoundedTensorEnclosure.add]
    rw [hp,round_pol,he1,he2,kadd_err,← add_div,← Nat.cast_add,upwardError_nat]

def sval (s : Bool) (n d : ℕ) : ℚ := if s then -((n:ℚ)/d) else (n:ℚ)/d

def kconstK (s : Bool) (n d : ℕ) : ℕ := bif s then (2*n*T+d-1)/(2*d) else (2*n*T+d)/(2*d)

def kconst (s : Bool) (n d : ℕ) : Enc :=
  ⟨bif s then 0 else kconstK s n d,bif s then kconstK s n d else 0,kconstK s n d,
    cdiv (absdiff (n*T) (kconstK s n d*d)) (d*E4),Nat.blt (kconstK s n d) B && Nat.blt 0 d⟩

section kconst_fields
variable (s : Bool) (n d : ℕ)
theorem kconst_pos : (kconst s n d).pos=(bif s then 0 else kconstK s n d) := by
  unfold kconst; exact rfl
theorem kconst_neg : (kconst s n d).neg=(bif s then kconstK s n d else 0) := by
  unfold kconst; exact rfl
theorem kconst_nrm : (kconst s n d).nrm=kconstK s n d := by unfold kconst; exact rfl
theorem kconst_err : (kconst s n d).err=cdiv (absdiff (n*T) (kconstK s n d*d)) (d*E4) := by
  unfold kconst; exact rfl
theorem kconst_ok : (kconst s n d).ok=(Nat.blt (kconstK s n d) B && Nat.blt 0 d) := by
  unfold kconst; exact rfl
end kconst_fields

theorem rc_sval (s : Bool) (n d : ℕ) (hd : 0 < d) :
    roundedCoefficient (sval s n d)=(if s then -(kconstK s n d : ℚ) else (kconstK s n d : ℚ))/10^24 := by
  unfold roundedCoefficient coefficientScale sval kconstK
  have hT := T_pos
  cases s
  · simp only [Bool.false_eq_true,ite_false,Bool.cond_false]
    have e : (n:ℚ)/d*10^24+1/2=((2*n*T+d : ℕ) : ℚ)/((2*d : ℕ) : ℚ) := by
      push_cast; rw [T_cast]; field_simp
    rw [e,floor_div_nat _ _ (by omega),Int.cast_natCast]
  · simp only [ite_true,Bool.cond_true]
    have e : -((n:ℚ)/d)*10^24+1/2=((d : ℚ)-2*((n*T : ℕ) : ℚ))/(2*d) := by
      push_cast; rw [T_cast]; field_simp; ring
    rw [e,floor_neg_round _ _ hd,Int.cast_neg,Int.cast_natCast,show 2*(n*T)=2*n*T by ring]

theorem norm_scalar (r : ℚ) : TensorPolynomialEnclosure.norm (TensorWholeIntervalPolynomial.scalar r)=|r| := by
  have hs : ∀ i j, bcf (TensorWholeIntervalPolynomial.scalar r) i j ≠ 0 → i < 1 ∧ j < 1 := by
    intro i j h; rw [bcf_scalar] at h; split_ifs at h with hij
    · omega
    · exact absurd rfl h
  rw [norm_eq_range hs]; simp [bcf_scalar]

theorem roundedPolynomial_scalar (r : ℚ) :
    roundedPolynomial (TensorWholeIntervalPolynomial.scalar r)=
      TensorWholeIntervalPolynomial.scalar (roundedCoefficient r) := by
  apply bv_ext; intro i j
  rw [bcf_roundedPolynomial,bcf_scalar,bcf_scalar]
  split_ifs <;> simp [rc_zero]

theorem cf_zero (i j : ℕ) : cf 0 i j=0 := by simp [cf]

theorem rep_const (s : Bool) (n d : ℕ) (hok : (kconst s n d).ok=true) :
    Rep (kconst s n d) (RoundedTensorEnclosure.constant (sval s n d)) := by
  rw [kconst_ok] at hok
  simp only [Bool.and_eq_true,Nat.blt_eq] at hok
  obtain ⟨hk,hd⟩ := hok
  set k := kconstK s n d with hkdef
  have hsupp : ∀ i j, cf (monoN 0 0 k) i j ≠ 0 → i+j ≤ 10 := by
    intro i j h; rw [cf_monoN] at h; split_ifs at h with hij
    · omega
    · exact absurd rfl h
  have hbd : ∀ i j, cf (monoN 0 0 k) i j < B := by
    intro i j; rw [cf_monoN]; split_ifs
    · exact hk
    · exact B_pos
  have hz0 : ∀ i j, cf (0:NB) i j ≠ 0 → i+j ≤ 10 := by intro i j h; simp [cf_zero] at h
  have hzb : ∀ i j, cf (0:NB) i j < B := by intro i j; rw [cf_zero]; exact B_pos
  have evm : evB (monoN 0 0 k)=k := by simp [evB,evXY_monoN]
  have ev1m : ev1 (monoN 0 0 k)=k := by simp [ev1,evXY_monoN]
  have hrc := rc_sval s n d hd
  have herr : RoundedTensorEnclosure.upwardError
      (0+TensorPolynomialEnclosure.norm (TensorWholeIntervalPolynomial.scalar (sval s n d)-
        TensorWholeIntervalPolynomial.scalar (roundedCoefficient (sval s n d))))=
      ((kconst s n d).err : ℚ)/10^20 := by
    rw [show TensorWholeIntervalPolynomial.scalar (sval s n d)-
        TensorWholeIntervalPolynomial.scalar (roundedCoefficient (sval s n d))=
        TensorWholeIntervalPolynomial.scalar (sval s n d-roundedCoefficient (sval s n d)) by
        simp only [TensorWholeIntervalPolynomial.scalar,map_sub],norm_scalar,hrc,zero_add,kconst_err]
    unfold upwardError errorScale
    have hT := T_pos
    have e : |sval s n d-(if s then -(k:ℚ) else (k:ℚ))/10^24| * 10^20=
        ((absdiff (n*T) (k*d) : ℕ) : ℚ)/((d*E4 : ℕ) : ℚ) := by
      rw [absdiff_cast]
      have hE4 : (E4 : ℚ)=10^4 := by norm_num [E4]
      have hdq : (0:ℚ) < d := by exact_mod_cast hd
      push_cast; rw [hE4,T_cast]
      unfold sval
      cases s
      · simp only [Bool.false_eq_true,ite_false]
        rw [show (n:ℚ)/d-k/10^24=((n:ℚ)*10^24-k*d)/(d*10^24) by field_simp,abs_div,
          abs_of_pos (by positivity : (0:ℚ) < d*10^24)]
        field_simp
      · simp only [ite_true]
        rw [show -((n:ℚ)/d)- -(k:ℚ)/10^24=-(((n:ℚ)*10^24-k*d)/(d*10^24)) by field_simp; ring,
          abs_neg,abs_div,abs_of_pos (by positivity : (0:ℚ) < d*10^24)]
        field_simp
    rw [e,← cdiv_cast _ _ (Nat.mul_pos hd (by norm_num [E4])),Int.cast_natCast]
  cases s
  · refine ⟨monoN 0 0 k,0,⟨hsupp,hz0,hbd,hzb,fun i j => Or.inr (cf_zero i j)⟩,?_,?_,?_,?_,?_⟩
    · rw [kconst_pos,evm]; rfl
    · rw [kconst_neg,map_zero]; rfl
    · rw [kconst_nrm,ev1m,map_zero,hkdef]; rfl
    · simp only [RoundedTensorEnclosure.constant,RoundedTensorEnclosure.round,
        roundedPolynomial_scalar]
      apply bv_ext; intro i j
      rw [bcf_scalar,bcf_pol,cf_monoN,cf_zero]
      by_cases h : i=0 ∧ j=0
      · simp only [h,and_self,ite_true,hrc,hkdef]; simp
      · simp [h]
    · simp only [RoundedTensorEnclosure.constant,RoundedTensorEnclosure.round,
        roundedPolynomial_scalar]
      exact herr
  · refine ⟨0,monoN 0 0 k,⟨hz0,hsupp,hzb,hbd,fun i j => Or.inl (cf_zero i j)⟩,?_,?_,?_,?_,?_⟩
    · rw [kconst_pos,map_zero]; rfl
    · rw [kconst_neg,evm]; rfl
    · rw [kconst_nrm,ev1m,map_zero,zero_add,hkdef]
    · simp only [RoundedTensorEnclosure.constant,RoundedTensorEnclosure.round,
        roundedPolynomial_scalar]
      apply bv_ext; intro i j
      rw [bcf_scalar,bcf_pol,cf_monoN,cf_zero]
      by_cases h : i=0 ∧ j=0
      · simp only [h,and_self,ite_true,hrc,hkdef]; simp
      · simp [h]
    · simp only [RoundedTensorEnclosure.constant,RoundedTensorEnclosure.round,
        roundedPolynomial_scalar]
      exact herr

/-! ### Multiplication -/

def hMul (i j x y : ℕ) : Acc :=
  bif Nat.ble (i+j) 10 then
    (bif Nat.ble y x then
      (((2*(x-y)+T)/(2*T)) <<< (170*(W*i+j)),0,(2*(x-y)+T)/(2*T),0,
        absdiff (x-y) (T*((2*(x-y)+T)/(2*T))))
    else
      (0,((2*(y-x)+T-1)/(2*T)) <<< (170*(W*i+j)),(2*(y-x)+T-1)/(2*T),0,
        absdiff (y-x) (T*((2*(y-x)+T-1)/(2*T)))))
  else (0,0,0,absdiff x y,0)

def kmul (a b : Enc) : Enc :=
  let r := walk hMul 21 0 (a.pos*b.pos+a.neg*b.neg) (a.pos*b.neg+a.neg*b.pos) (0,0,0,0,0)
  ⟨r.1,r.2.1,r.2.2.1,
    cdiv (r.2.2.2.1+a.err*b.nrm*E4+b.err*a.nrm*E4+a.err*b.err*E8+r.2.2.2.2) E28,
    a.ok && b.ok && Nat.blt (a.nrm*b.nrm) B⟩

section kmul_fields
variable (E1 E2 : Enc)
local notation "WK" => walk hMul 21 0 (E1.pos*E2.pos+E1.neg*E2.neg) (E1.pos*E2.neg+E1.neg*E2.pos)
  (0,0,0,0,0)
theorem kmul_pos : (kmul E1 E2).pos=(WK).1 := by unfold kmul; exact rfl
theorem kmul_neg : (kmul E1 E2).neg=(WK).2.1 := by unfold kmul; exact rfl
theorem kmul_nrm : (kmul E1 E2).nrm=(WK).2.2.1 := by unfold kmul; exact rfl
theorem kmul_err : (kmul E1 E2).err=cdiv ((WK).2.2.2.1+E1.err*E2.nrm*E4+E2.err*E1.nrm*E4+
    E1.err*E2.err*E8+(WK).2.2.2.2) E28 := by unfold kmul; exact rfl
theorem kmul_ok : (kmul E1 E2).ok=(E1.ok && E2.ok && Nat.blt (E1.nrm*E2.nrm) B) := by
  unfold kmul; exact rfl
end kmul_fields

def lossV (x y : ℕ) : ℕ := if y ≤ x then absdiff (x-y) (T*rP x y) else absdiff (y-x) (T*rN x y)

theorem hMul_spec (i j x y : ℕ) :
    hMul i j x y=((if i+j ≤ 10 then rP x y else 0) * B^(W*i+j),
      (if i+j ≤ 10 then rN x y else 0) * B^(W*i+j),
      (if i+j ≤ 10 then rP x y else 0)+(if i+j ≤ 10 then rN x y else 0),
      (if i+j ≤ 10 then 0 else absdiff x y),(if i+j ≤ 10 then lossV x y else 0)) := by
  unfold hMul
  simp only [shl_B]
  by_cases hk : i+j ≤ 10
  · rw [Nat.ble_eq_true_of_le hk,Bool.cond_true]
    simp only [hk,ite_true]
    unfold lossV rP rN
    by_cases h : y ≤ x
    · rw [Nat.ble_eq_true_of_le h,Bool.cond_true]; simp [h]
    · have h' : Nat.ble y x=false := by
        cases hb : Nat.ble y x
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true hb) h
      rw [h',Bool.cond_false]; simp [h]
  · have h' : Nat.ble (i+j) 10=false := by
      cases hb : Nat.ble (i+j) 10
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) hk
    rw [h',Bool.cond_false]; simp [hk]

theorem rP_zero : rP 0 0=0 := by
  unfold rP; have := T_pos; simp only [le_refl,ite_true,Nat.sub_self,mul_zero,zero_add]
  exact Nat.div_eq_of_lt (by omega)

theorem hMul_zero (i j : ℕ) : hMul i j 0 0=0 := by
  rw [hMul_spec]
  have h1 : rN 0 0=0 := by simp [rN]
  have h2 : lossV 0 0=0 := by simp [lossV,rP_zero,absdiff]
  have h3 : absdiff 0 0=0 := by simp [absdiff]
  simp [rP_zero,h1,h2,h3]

theorem T_two : 2 ≤ T := by norm_num [T]

theorem rP_le (x y : ℕ) : rP x y ≤ x := by
  unfold rP; split_ifs with h
  · have := T_two
    rcases Nat.eq_zero_or_pos (x-y) with h0|h0
    · rw [h0]; simp only [mul_zero,zero_add]
      rw [Nat.div_eq_of_lt (by omega)]; omega
    · calc (2*(x-y)+T)/(2*T) ≤ x-y := Nat.div_le_of_le_mul (by nlinarith)
        _ ≤ x := Nat.sub_le x y
  · omega

theorem rN_le (x y : ℕ) : rN x y ≤ y := by
  unfold rN; split_ifs with h
  · omega
  · have := T_two
    calc (2*(y-x)+T-1)/(2*T) ≤ y-x := Nat.div_le_of_le_mul (by
          have hm : 1 ≤ y-x := by omega
          have h1 : 2*T*1 ≤ 2*T*(y-x) := Nat.mul_le_mul_left (2*T) hm
          have h2 : 2*2*(y-x) ≤ 2*T*(y-x) := Nat.mul_le_mul_right (y-x) (by omega)
          omega)
      _ ≤ y := Nat.sub_le y x

theorem rPN_disj (x y : ℕ) : rP x y=0 ∨ rN x y=0 := by
  unfold rP rN; split_ifs <;> simp

theorem loss_cast (x y : ℕ) :
    |((x:ℚ)-y)/10^48-((rP x y : ℚ)-rN x y)/10^24|=(lossV x y : ℚ)/10^48 := by
  unfold lossV
  have hT : (T:ℚ)=10^24 := T_cast
  by_cases h : y ≤ x
  · have h0 : rN x y=0 := by simp [rN,h]
    rw [ite_eq_left h,absdiff_cast,h0,Nat.cast_sub h]
    push_cast; rw [hT]
    rw [show ((x:ℚ)-y)/10^48-(rP x y-0)/10^24=((x:ℚ)-y-10^24*rP x y)/10^48 by field_simp; ring,
      abs_div,abs_of_pos (by norm_num : (0:ℚ)<10^48)]
  · have h0 : rP x y=0 := by simp [rP,h]
    rw [ite_eq_right h,absdiff_cast,h0,Nat.cast_sub (by omega)]
    push_cast; rw [hT]
    rw [show ((x:ℚ)-y)/10^48-(0-rN x y)/10^24=-(((y:ℚ)-x-10^24*rN x y)/10^48) by field_simp; ring,
      abs_neg,abs_div,abs_of_pos (by norm_num : (0:ℚ)<10^48)]

theorem W_eq : W=21 := by unfold W; rfl

theorem sup_mul {P Q : NB} (hP : ∀ i j, cf P i j ≠ 0 → i+j ≤ 10) (hQ : ∀ i j, cf Q i j ≠ 0 → i+j ≤ 10) :
    ∀ i j, cf (P*Q) i j ≠ 0 → i+j ≤ 20 := by
  intro i j h; by_contra hc; exact h (cf_mul_eq_zero hP hQ i j (by omega))

theorem sup_add {P Q : NB} {L : ℕ} (hP : ∀ i j, cf P i j ≠ 0 → i+j ≤ L)
    (hQ : ∀ i j, cf Q i j ≠ 0 → i+j ≤ L) : ∀ i j, cf (P+Q) i j ≠ 0 → i+j ≤ L := by
  intro i j h; rw [cf_add] at h
  by_cases h1 : cf P i j=0
  · exact hQ i j (by omega)
  · exact hP i j h1

theorem upwardError_E48 (E : ℕ) : upwardError ((E:ℚ)/10^48)=((cdiv E E28 : ℕ) : ℚ)/10^20 := by
  unfold upwardError errorScale
  have e : (E:ℚ)/10^48*10^20=(E:ℚ)/((E28 : ℕ) : ℚ) := by
    have : ((E28 : ℕ) : ℚ)=10^28 := by norm_num [E28]
    rw [this]; field_simp
  rw [e,← cdiv_cast _ _ (by norm_num [E28]),Int.cast_natCast]

theorem rep_mul {E1 E2 : Enc} {e1 e2 : TensorPolynomialEnclosure.Enclosure}
    (h1 : Rep E1 e1) (h2 : Rep E2 e2) (hok : (kmul E1 E2).ok=true) :
    Rep (kmul E1 E2) (RoundedTensorEnclosure.mul e1 e2) := by
  obtain ⟨P1,N1,I1,hp1,hn1,hm1,hpol1,he1⟩ := h1
  obtain ⟨P2,N2,I2,hp2,hn2,hm2,hpol2,he2⟩ := h2
  rw [kmul_ok] at hok
  simp only [Bool.and_eq_true,Nat.blt_eq] at hok
  have hlt := hok.2
  have hW : (20:ℕ) < W := by rw [W_eq]; norm_num
  have hX : E1.pos*E2.pos+E1.neg*E2.neg=evB (P1*P2+N1*N2) := by
    rw [hp1,hp2,hn1,hn2,map_add,map_mul,map_mul]
  have hY : E1.pos*E2.neg+E1.neg*E2.pos=evB (P1*N2+N1*P2) := by
    rw [hp1,hp2,hn1,hn2,map_add,map_mul,map_mul]
  have sX : ∀ i j, cf (P1*P2+N1*N2) i j ≠ 0 → i+j ≤ 20 :=
    sup_add (sup_mul I1.supP I2.supP) (sup_mul I1.supN I2.supN)
  have sY : ∀ i j, cf (P1*N2+N1*P2) i j ≠ 0 → i+j ≤ 20 :=
    sup_add (sup_mul I1.supP I2.supN) (sup_mul I1.supN I2.supP)
  have s21 : ∀ {P : NB}, (∀ i j, cf P i j ≠ 0 → i+j ≤ 20) → ∀ i j, cf P i j ≠ 0 → i < 21 ∧ j < 21 := by
    intro P h i j hij; have := h i j hij; omega
  have evX : ev1 (P1*P2+N1*N2) ≤ E1.nrm*E2.nrm := by
    rw [hm1,hm2,map_add,map_mul,map_mul]
    calc ev1 P1*ev1 P2+ev1 N1*ev1 N2 ≤ ev1 P1*ev1 P2+ev1 N1*ev1 N2+(ev1 P1*ev1 N2+ev1 N1*ev1 P2) :=
          Nat.le_add_right _ _
      _=(ev1 P1+ev1 N1)*(ev1 P2+ev1 N2) := by ring
  have evY : ev1 (P1*N2+N1*P2) ≤ E1.nrm*E2.nrm := by
    rw [hm1,hm2,map_add,map_mul,map_mul]
    calc ev1 P1*ev1 N2+ev1 N1*ev1 P2 ≤ ev1 P1*ev1 N2+ev1 N1*ev1 P2+(ev1 P1*ev1 P2+ev1 N1*ev1 N2) :=
          Nat.le_add_right _ _
      _=(ev1 P1+ev1 N1)*(ev1 P2+ev1 N2) := by ring
  have bX : ∀ i j, cf (P1*P2+N1*N2) i j < B :=
    fun i j => lt_of_le_of_lt ((cf_le_ev1 (s21 sX) i j).trans evX) hlt
  have bY : ∀ i j, cf (P1*N2+N1*P2) i j < B :=
    fun i j => lt_of_le_of_lt ((cf_le_ev1 (s21 sY) i j).trans evY) hlt
  have hw := walk_sum hMul hMul_zero 21 (P1*P2+N1*N2) (P1*N2+N1*P2) hW sX sY bX bY
  set x := fun r k => cf (P1*P2+N1*N2) r k with hx
  set y := fun r k => cf (P1*N2+N1*P2) r k with hy
  set Rp := ∑ r ∈ Finset.range 21,∑ k ∈ Finset.range W,
    monoN r k (if r+k ≤ 10 then rP (x r k) (y r k) else 0) with hRp
  set Rn := ∑ r ∈ Finset.range 21,∑ k ∈ Finset.range W,
    monoN r k (if r+k ≤ 10 then rN (x r k) (y r k) else 0) with hRn
  have cRp : ∀ a b, cf Rp a b=if a < 21 ∧ b < W then
      (if a+b ≤ 10 then rP (x a b) (y a b) else 0) else 0 :=
    fun a b => cf_monoN_sum _ _ _ a b
  have cRn : ∀ a b, cf Rn a b=if a < 21 ∧ b < W then
      (if a+b ≤ 10 then rN (x a b) (y a b) else 0) else 0 :=
    fun a b => cf_monoN_sum _ _ _ a b
  have hInv : Inv Rp Rn := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b h; rw [cRp] at h; split_ifs at h with hab hk
      · exact hk
      · exact absurd rfl h
      · exact absurd rfl h
    · intro a b h; rw [cRn] at h; split_ifs at h with hab hk
      · exact hk
      · exact absurd rfl h
      · exact absurd rfl h
    · intro a b; rw [cRp]; split_ifs
      · exact (rP_le _ _).trans_lt (bX a b)
      · exact B_pos
      · exact B_pos
    · intro a b; rw [cRn]; split_ifs
      · exact (rN_le _ _).trans_lt (bY a b)
      · exact B_pos
      · exact B_pos
    · intro a b; rw [cRp,cRn]; split_ifs
      · exact rPN_disj _ _
      · simp
      · simp
  have hprod : e1.polynomial*e2.polynomial=
      TensorWholeIntervalPolynomial.scalar (1/10^48)*(toQ (P1*P2+N1*N2)-toQ (P1*N2+N1*P2)) := by
    rw [hpol1,hpol2,pol,pol]
    simp only [map_add,map_mul]
    have : TensorWholeIntervalPolynomial.scalar (1/10^48)=
        TensorWholeIntervalPolynomial.scalar (1/10^24)*TensorWholeIntervalPolynomial.scalar (1/10^24) := by
      simp only [TensorWholeIntervalPolynomial.scalar,← map_mul]; norm_num
    rw [this]; ring
  have bprod : ∀ a b, bcf (e1.polynomial*e2.polynomial) a b=((x a b : ℚ)-y a b)/10^48 := by
    intro a b; rw [hprod,bcf_scalar_mul,bcf_sub,bcf_toQ,bcf_toQ]; ring
  have zxy : ∀ a b, ¬ (a < 21 ∧ b < W) → x a b=0 ∧ y a b=0 := by
    intro a b hab
    have h20 : ¬ a+b ≤ 20 := by intro h; apply hab; rw [W_eq]; constructor <;> omega
    exact ⟨by by_contra hc; exact h20 (sX a b hc),by by_contra hc; exact h20 (sY a b hc)⟩
  have hround : roundedPolynomial (RoundedTensorEnclosure.truncate (e1.polynomial*e2.polynomial))=
      pol Rp Rn := by
    apply bv_ext; intro a b
    rw [bcf_roundedPolynomial,bcf_truncate,bcf_pol,cRp,cRn,bprod]
    by_cases hk : a+b ≤ 10
    · have hab : a < 21 ∧ b < W := ⟨by omega,by rw [W_eq]; omega⟩
      rw [ite_eq_left hk,ite_eq_left hab,ite_eq_left hab,ite_eq_left hk,ite_eq_left hk,rc_digits]
    · rw [ite_eq_right hk,rc_zero]; split_ifs <;> simp
  have hsupp : ∀ (q : Bv), (∀ a b, ¬ (a < 21 ∧ b < W) → bcf q a b=0) →
      ∀ a b, bcf q a b ≠ 0 → a < 21 ∧ b < W := by
    intro q hq a b h; by_contra hc; exact h (hq a b hc)
  have hdisc : TensorPolynomialEnclosure.norm (e1.polynomial*e2.polynomial-
      RoundedTensorEnclosure.truncate (e1.polynomial*e2.polynomial))=
      ((∑ r ∈ Finset.range 21,∑ k ∈ Finset.range W,(hMul r k (x r k) (y r k)).2.2.2.1 : ℕ) : ℚ)/10^48 := by
    have hz : ∀ a b, ¬ (a < 21 ∧ b < W) → bcf (e1.polynomial*e2.polynomial-
        RoundedTensorEnclosure.truncate (e1.polynomial*e2.polynomial)) a b=0 := by
      intro a b hab
      rw [bcf_sub,bcf_truncate,bprod,(zxy a b hab).1,(zxy a b hab).2]; simp
    rw [norm_eq_range (hsupp _ hz)]
    push_cast
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro r _
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro k _
    rw [bcf_sub,bcf_truncate,bprod,hMul_spec]
    by_cases hk : r+k ≤ 10
    · simp [hk]
    · simp only [hk,ite_false,sub_zero]
      rw [absdiff_cast,abs_div,abs_of_pos (by norm_num : (0:ℚ)<10^48)]
  have hloss : TensorPolynomialEnclosure.norm (RoundedTensorEnclosure.truncate (e1.polynomial*e2.polynomial)-
      roundedPolynomial (RoundedTensorEnclosure.truncate (e1.polynomial*e2.polynomial)))=
      ((∑ r ∈ Finset.range 21,∑ k ∈ Finset.range W,(hMul r k (x r k) (y r k)).2.2.2.2 : ℕ) : ℚ)/10^48 := by
    rw [hround]
    have hz : ∀ a b, ¬ (a < 21 ∧ b < W) → bcf (RoundedTensorEnclosure.truncate (e1.polynomial*e2.polynomial)-
        pol Rp Rn) a b=0 := by
      intro a b hab
      rw [bcf_sub,bcf_truncate,bprod,bcf_pol,cRp,cRn,ite_eq_right hab,ite_eq_right hab,(zxy a b hab).1,
        (zxy a b hab).2]; simp
    rw [norm_eq_range (hsupp _ hz)]
    push_cast
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro r hr
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro k hk'
    have hrk : r < 21 ∧ k < W := ⟨Finset.mem_range.mp hr,Finset.mem_range.mp hk'⟩
    rw [bcf_sub,bcf_truncate,bprod,bcf_pol,cRp,cRn,ite_eq_left hrk,ite_eq_left hrk,hMul_spec]
    by_cases hk : r+k ≤ 10
    · simp only [hk,ite_true]; exact loss_cast _ _
    · simp [hk]
  refine ⟨Rp,Rn,hInv,?_,?_,?_,?_,?_⟩
  · rw [kmul_pos,hX,hY,hw,Prod.fst_sum,hRp,evB_monoN_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [Prod.fst_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [hMul_spec]
  · rw [kmul_neg,hX,hY,hw,Prod.snd_sum,Prod.fst_sum,hRn,evB_monoN_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [Prod.snd_sum,Prod.fst_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [hMul_spec]
  · rw [kmul_nrm,hX,hY,hw,Prod.snd_sum,Prod.snd_sum,Prod.fst_sum,hRp,hRn,ev1_monoN_sum,
      ev1_monoN_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    rw [Prod.snd_sum,Prod.snd_sum,Prod.fst_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [hMul_spec]
  · simp only [RoundedTensorEnclosure.mul,RoundedTensorEnclosure.round,RoundedTensorEnclosure.rawMul]
    exact hround
  · simp only [RoundedTensorEnclosure.mul,RoundedTensorEnclosure.round,RoundedTensorEnclosure.rawMul,
      RoundedTensorEnclosure.norm]
    have hm1' : ((ev1 P1 : ℚ)+ev1 N1)=E1.nrm := by rw [hm1]; push_cast; ring
    have hm2' : ((ev1 P2 : ℚ)+ev1 N2)=E2.nrm := by rw [hm2]; push_cast; ring
    rw [hdisc,hloss,he1,he2,hpol1,hpol2,I1.norm,I2.norm,hm1',hm2',kmul_err,hX,hY,hw]
    rw [← upwardError_E48]
    congr 1
    simp only [Prod.snd_sum,Prod.fst_sum]
    have h4 : ((E4 : ℕ) : ℚ)=10^4 := by norm_num [E4]
    have h8 : ((E8 : ℕ) : ℚ)=10^8 := by norm_num [E8]
    push_cast
    rw [h4,h8]
    field_simp
    ring

/-! ### Composite operations -/

def kscale (s : Bool) (n d : ℕ) (a : Enc) : Enc := kmul (kconst s n d) a

def kpower (a : Enc) : ℕ → Enc
  | 0 => kconst false 1 1
  | n+1 => kmul (kpower a n) a

def ksum (g : ℕ → Enc) : ℕ → Enc
  | 0 => kconst false 0 1
  | n+1 => kadd (ksum g n) (g n)

def ksine (a : Enc) : Enc :=
  kwiden (ksum (fun j => kscale (j % 2 == 1) 1 (Nat.factorial (2*j+1)) (kpower a (2*j+1))) 7)
    (7^15) (10^15*Nat.factorial 15)

def kcosine (a : Enc) : Enc :=
  kwiden (ksum (fun j => kscale (j % 2 == 1) 1 (Nat.factorial (2*j)) (kpower a (2*j))) 8)
    (7^16) (10^16*Nat.factorial 16)

theorem kmul_ok_left {E1 E2 : Enc} (h : (kmul E1 E2).ok=true) : E1.ok=true := by
  rw [kmul_ok] at h; simp only [Bool.and_eq_true] at h; exact h.1.1
theorem kmul_ok_right {E1 E2 : Enc} (h : (kmul E1 E2).ok=true) : E2.ok=true := by
  rw [kmul_ok] at h; simp only [Bool.and_eq_true] at h; exact h.1.2
theorem kadd_ok_left {E1 E2 : Enc} (h : (kadd E1 E2).ok=true) : E1.ok=true := by
  rw [kadd_ok] at h; simp only [Bool.and_eq_true] at h; exact h.1.1
theorem kadd_ok_right {E1 E2 : Enc} (h : (kadd E1 E2).ok=true) : E2.ok=true := by
  rw [kadd_ok] at h; simp only [Bool.and_eq_true] at h; exact h.1.2
theorem kneg_ok (E : Enc) : (kneg E).ok=E.ok := by unfold kneg; exact rfl

theorem kwiden_ok_left {E : Enc} {n d : ℕ} (h : (kwiden E n d).ok=true) : E.ok=true := by
  rw [kwiden_ok] at h; simp only [Bool.and_eq_true] at h; exact h.1

theorem rep_scale {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a) (s : Bool) (n d : ℕ)
    (hok : (kscale s n d A).ok=true) :
    Rep (kscale s n d A) (RoundedTensorEnclosure.scale (sval s n d) a) :=
  rep_mul (rep_const s n d (kmul_ok_left hok)) h hok

theorem sval_one : sval false 1 1=1 := by simp [sval]
theorem sval_zero : sval false 0 1=0 := by simp [sval]

theorem rep_power {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a) :
    ∀ n, (kpower A n).ok=true → Rep (kpower A n) (RoundedTensorEnclosure.power a n)
  | 0, hok => by
    have := rep_const false 1 1 hok
    rw [sval_one] at this
    exact this
  | n+1, hok => rep_mul (rep_power h n (kmul_ok_left hok)) h hok

theorem rep_sum (g : ℕ → Enc) :
    ∀ (n : ℕ) (f : Fin n → TensorPolynomialEnclosure.Enclosure), (∀ i : Fin n, Rep (g i) (f i)) →
      (ksum g n).ok=true → Rep (ksum g n) (RoundedTensorEnclosure.sum n f)
  | 0, f, _, hok => by
    have := rep_const false 0 1 hok
    rw [sval_zero] at this
    exact this
  | n+1, f, hf, hok =>
    rep_add (rep_sum g n (fun i => f i.castSucc) (fun i => hf i.castSucc) (kadd_ok_left hok))
      (hf (Fin.last n)) hok

theorem neg_one_pow_sval (j : ℕ) (d : ℕ) :
    ((-1:ℚ)^j/(d:ℚ))=sval (j % 2 == 1) 1 d := by
  unfold sval
  rcases Nat.mod_two_eq_zero_or_one j with h|h
  · have he : Even j := Nat.even_iff.mpr h
    rw [he.neg_one_pow]; simp [h]
  · have ho : Odd j := Nat.odd_iff.mpr h
    rw [ho.neg_one_pow]; simp [h]; ring

theorem ksum_ok (g : ℕ → Enc) : ∀ n, (ksum g n).ok=true → ∀ i < n, (g i).ok=true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n+1, h, i, hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|hi
    · exact ksum_ok g n (kadd_ok_left h) i hi
    · rw [hi]; exact kadd_ok_right h

theorem rep_sine {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a)
    (hok : (ksine A).ok=true) : Rep (ksine A) (RoundedTensorEnclosure.sine a) := by
  unfold RoundedTensorEnclosure.sine
  have e : (7/10:ℚ)^15/(Nat.factorial 15:ℚ)=((7^15 : ℕ) : ℚ)/((10^15*Nat.factorial 15 : ℕ) : ℚ) := by
    push_cast; ring
  rw [e]
  apply rep_widen _ _ _ hok
  apply rep_sum _ 7 _ _ (kwiden_ok_left hok)
  intro i
  have hgi := ksum_ok _ 7 (kwiden_ok_left hok) i i.isLt
  rw [neg_one_pow_sval]
  exact rep_scale (rep_power h _ (kmul_ok_right hgi)) _ _ _ hgi

theorem rep_cosine {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a)
    (hok : (kcosine A).ok=true) : Rep (kcosine A) (RoundedTensorEnclosure.cosine a) := by
  unfold RoundedTensorEnclosure.cosine
  have e : (7/10:ℚ)^16/(Nat.factorial 16:ℚ)=((7^16 : ℕ) : ℚ)/((10^16*Nat.factorial 16 : ℕ) : ℚ) := by
    push_cast; ring
  rw [e]
  apply rep_widen _ _ _ hok
  apply rep_sum _ 8 _ _ (kwiden_ok_left hok)
  intro i
  have hgi := ksum_ok _ 8 (kwiden_ok_left hok) i i.isLt
  rw [neg_one_pow_sval]
  exact rep_scale (rep_power h _ (kmul_ok_right hgi)) _ _ _ hgi

/-! ### Binomial coefficients and Horner evaluation -/

open RoundedBinomialEnclosure in
def kcoef (e : Exponent) : ℕ → Bool × ℕ × ℕ
  | 0 => (false,1,1)
  | n+1 =>
    match e with
    | .root => bif n == 0 then ((kcoef e n).1,(kcoef e n).2.1,(kcoef e n).2.2*(2*(n+1)))
        else (!(kcoef e n).1,(kcoef e n).2.1*(2*n-1),(kcoef e n).2.2*(2*(n+1)))
    | .inverseRoot => (!(kcoef e n).1,(kcoef e n).2.1*(1+2*n),(kcoef e n).2.2*(2*(n+1)))
    | .inverse => (!(kcoef e n).1,(kcoef e n).2.1*(1+n),(kcoef e n).2.2*(n+1))

def sv (c : Bool × ℕ × ℕ) : ℚ := sval c.1 c.2.1 c.2.2

open RoundedBinomialEnclosure in
theorem kcoef_den_pos (e : Exponent) : ∀ n, 0 < (kcoef e n).2.2
  | 0 => by simp [kcoef]
  | n+1 => by
    have ih := kcoef_den_pos e n
    cases e
    · simp only [kcoef]
      cases h : (n == 0) <;> simp only [Bool.cond_true,Bool.cond_false] <;> positivity
    · simp only [kcoef]; positivity
    · simp only [kcoef]; positivity

open RoundedBinomialEnclosure in
theorem coefficient_eq (e : Exponent) : ∀ n, coefficient e n=sv (kcoef e n)
  | 0 => by simp [coefficient,kcoef,sv,sval]
  | n+1 => by
    have ih := coefficient_eq e n
    have hd := kcoef_den_pos e n
    rw [coefficient,ih]
    cases e
    · by_cases hn : n=0
      · subst hn
        rw [show kcoef .root (0+1)=((kcoef .root 0).1,(kcoef .root 0).2.1,
          (kcoef .root 0).2.2*(2*(0+1))) from rfl]
        simp [kcoef,sv,sval,exponent]
      · rw [show kcoef .root (n+1)=(!(kcoef .root n).1,(kcoef .root n).2.1*(2*n-1),
          (kcoef .root n).2.2*(2*(n+1))) by
            simp only [kcoef]; have h : (n == 0)=false := by simpa using hn
            rw [h,Bool.cond_false]]
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        generalize kcoef .root n=c at hd ⊢
        obtain ⟨s,a,b⟩ := c
        simp only at hd
        have hb : (b:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
        have hsub : ((2*n-1 : ℕ) : ℚ)=2*n-1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
        cases s <;> simp only [sv,sval,exponent,Bool.not_true,Bool.not_false,ite_true,ite_false,
          Bool.false_eq_true,Nat.cast_mul,hsub] <;> push_cast <;> field_simp <;> ring
    · rw [show kcoef .inverseRoot (n+1)=(!(kcoef .inverseRoot n).1,(kcoef .inverseRoot n).2.1*(1+2*n),
          (kcoef .inverseRoot n).2.2*(2*(n+1))) from rfl]
      generalize kcoef .inverseRoot n=c at hd ⊢
      obtain ⟨s,a,b⟩ := c
      simp only at hd
      have hb : (b:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
      cases s <;> simp only [sv,sval,exponent,Bool.not_true,Bool.not_false,ite_true,ite_false,
        Bool.false_eq_true,Nat.cast_mul] <;> push_cast <;> field_simp <;> ring
    · rw [show kcoef .inverse (n+1)=(!(kcoef .inverse n).1,(kcoef .inverse n).2.1*(1+n),
          (kcoef .inverse n).2.2*(n+1)) from rfl]
      generalize kcoef .inverse n=c at hd ⊢
      obtain ⟨s,a,b⟩ := c
      simp only at hd
      have hb : (b:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
      cases s <;> simp only [sv,sval,exponent,Bool.not_true,Bool.not_false,ite_true,ite_false,
        Bool.false_eq_true,Nat.cast_mul] <;> push_cast <;> field_simp <;> ring

open RoundedBinomialEnclosure in
def coefList (e : Exponent) : List (Bool × ℕ × ℕ) := (List.range 13).map (kcoef e)

open RoundedBinomialEnclosure in
theorem coefList_ne (e : Exponent) : coefList e ≠ [] :=
  List.ne_nil_of_length_pos (by simp only [coefList,List.length_map,List.length_range]; norm_num)

open RoundedBinomialEnclosure in
theorem coefficients_eq (e : Exponent) : coefficients e=(coefList e).map sv := by
  apply List.ext_getElem
  · simp [coefficients,coefList]
  · intro i h1 h2
    simp only [coefficients,coefList,List.getElem_ofFn,List.getElem_map,List.getElem_range]
    exact coefficient_eq e i

def khorner (a : Enc) : List (Bool × ℕ × ℕ) → Enc
  | [] => kconst false 0 1
  | c :: cs => kadd (kconst c.1 c.2.1 c.2.2) (kmul a (khorner a cs))

theorem rep_horner {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a) :
    ∀ cs : List (Bool × ℕ × ℕ),(khorner A cs).ok=true →
      Rep (khorner A cs) (RoundedBinomialEnclosure.horner a (cs.map sv))
  | [], hok => by
    have := rep_const false 0 1 hok
    rw [sval_zero] at this
    exact this
  | c :: cs, hok => by
    simp only [List.map_cons,RoundedBinomialEnclosure.horner]
    exact rep_add (rep_const c.1 c.2.1 c.2.2 (kadd_ok_left hok))
      (rep_mul h (rep_horner h cs (kmul_ok_right (kadd_ok_right hok))) (kadd_ok_right hok)) hok

/-! ### The centre and the rounded square root -/

def cpos (a : Enc) : ℕ := a.pos % B
def cneg (a : Enc) : ℕ := a.neg % B

theorem rep_center {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a) :
    RoundedTensorEnclosure.center a=((cpos A : ℚ)-cneg A)/10^24 ∧ (cpos A=0 ∨ cneg A=0) := by
  obtain ⟨P,N,hI,hp,hn,_,hpol,_⟩ := h
  have hd := hI.digits (i := 0) (j := 0) W_pos
  simp only [mul_zero,add_zero,dig,gdig,pow_zero,Nat.div_one] at hd
  have e1 : cpos A=cf P 0 0 := by rw [cpos,hp]; exact hd.1
  have e2 : cneg A=cf N 0 0 := by rw [cneg,hn]; exact hd.2
  refine ⟨?_,?_⟩
  · unfold RoundedTensorEnclosure.center
    rw [hpol,e1,e2]
    exact bcf_pol P N 0 0
  · rw [e1,e2]; exact hI.disj 0 0

def sqArg (a : Enc) : ℕ := (cpos a+cneg a)/E4

def sqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | f+1, X, g => bif Nat.blt ((g+X/g)/2) g then sqrtIter f X ((g+X/g)/2) else g

def isqrt (X : ℕ) : ℕ := sqrtIter 200 X X

def sqrtOK (a : Enc) : Bool :=
  Nat.ble (isqrt (sqArg a)*isqrt (sqArg a)) (sqArg a) &&
    Nat.blt (sqArg a) ((isqrt (sqArg a)+1)*(isqrt (sqArg a)+1))

def kseed (a : Enc) : ℕ :=
  bif cneg a == 0 then
    (bif Nat.blt (4*cpos a) ((2*isqrt (sqArg a)+1)^2*E4) then isqrt (sqArg a) else isqrt (sqArg a)+1)
  else isqrt (sqArg a)

theorem natAbs_num_div (r : ℚ) (k : ℕ) : (r.num.natAbs*k)/r.den=⌊|r| * k⌋₊ := by
  rw [← Nat.floor_div_eq_div (K := ℚ)]
  congr 1
  conv_rhs => rw [← Rat.num_div_den r]
  rw [abs_div]
  push_cast
  rw [Nat.cast_natAbs,Int.cast_abs]
  simp only [Nat.abs_cast]
  ring

theorem nearestRoot_eq {A : Enc} (hc : cpos A=0 ∨ cneg A=0) (hok : sqrtOK A=true) :
    RoundedBinomialEnclosure.nearestRoot (((cpos A : ℚ)-cneg A)/10^24)=(kseed A : ℚ)/10^10 := by
  unfold sqrtOK at hok
  simp only [Bool.and_eq_true,Nat.ble_eq,Nat.blt_eq] at hok
  set n := isqrt (sqArg A) with hn
  have hsq : Nat.sqrt (sqArg A)=n := (Nat.eq_sqrt.mpr hok).symm
  have hE4 : (E4 : ℚ)=10^4 := by norm_num [E4]
  have harg : ((((cpos A : ℚ)-cneg A)/10^24).num.natAbs*10^20)/(((cpos A : ℚ)-cneg A)/10^24).den=
      sqArg A := by
    rw [show (10:ℕ)^20=((10^20 : ℕ) : ℕ) from rfl,natAbs_num_div,sqArg]
    rw [← Nat.floor_div_eq_div (K := ℚ)]
    congr 1
    push_cast
    rw [hE4]
    rcases hc with h|h
    · rw [h]; simp only [Nat.cast_zero,zero_sub,zero_add,neg_div,abs_neg]
      rw [abs_of_nonneg (by positivity)]; field_simp; norm_num
    · rw [h]; simp only [Nat.cast_zero,sub_zero,add_zero]
      rw [abs_of_nonneg (by positivity)]; field_simp; norm_num
  unfold RoundedBinomialEnclosure.nearestRoot
  simp only
  rw [harg,hsq]
  unfold kseed
  by_cases h0 : cneg A=0
  · have hb : (cneg A == 0)=true := by simp [h0]
    rw [hb,Bool.cond_true]
    rw [h0]; simp only [Nat.cast_zero,sub_zero]
    have key : (cpos A : ℚ)/10^24*10^20 < ((n:ℚ)+1/2)^2 ↔ 4*cpos A < (2*n+1)^2*E4 := by
      constructor
      · intro hlt
        have : (4*cpos A : ℚ) < (2*n+1)^2*10^4 := by nlinarith
        exact_mod_cast (by rw [hE4.symm] at this; exact_mod_cast this : 4*cpos A < (2*n+1)^2*E4)
      · intro hlt
        have : (4*cpos A : ℚ) < (2*n+1)^2*10^4 := by
          rw [← hE4]; exact_mod_cast hlt
        nlinarith
    by_cases hlt : 4*cpos A < (2*n+1)^2*E4
    · rw [ite_eq_left (key.mpr hlt)]
      have : Nat.blt (4*cpos A) ((2*n+1)^2*E4)=true := Nat.blt_eq.mpr hlt
      rw [← hn,this,Bool.cond_true]
    · rw [ite_eq_right (fun h => hlt (key.mp h))]
      have : Nat.blt (4*cpos A) ((2*n+1)^2*E4)=false := by
        rw [Bool.eq_false_iff]; intro h; exact hlt (Nat.blt_eq.mp h)
      rw [← hn,this,Bool.cond_false]
  · have hb : (cneg A == 0)=false := by simpa using h0
    rw [hb,Bool.cond_false]
    have hp0 : cpos A=0 := hc.resolve_right h0
    rw [hp0]
    have hneg : ((0:ℕ):ℚ)-cneg A < 0 := by
      have : (0:ℚ) < cneg A := by exact_mod_cast Nat.pos_of_ne_zero h0
      simp only [Nat.cast_zero,zero_sub,neg_lt_zero]; exact this
    rw [ite_eq_left (by nlinarith [sq_nonneg ((n:ℚ)+1/2)])]

/-! ### The binomial enclosure -/

@[irreducible] def E10 : ℕ := 10000000000

open RoundedBinomialEnclosure in
def invBase (a : Enc) : Exponent → ℕ × ℕ
  | .inverse => (T,cpos a)
  | _ => (E20,kseed a^2)

open RoundedBinomialEnclosure in
def kfactor (a : Enc) : Exponent → ℕ × ℕ
  | .root => (kseed a,E10)
  | .inverseRoot => (E10,kseed a)
  | .inverse => (T,cpos a)

open RoundedBinomialEnclosure in
def knormalized (a : Enc) (e : Exponent) : Enc :=
  kadd (kscale false (invBase a e).1 (invBase a e).2 a) (kneg (kconst false 1 1))

def spanN (n : Enc) : ℕ := n.nrm+n.err*E4

open RoundedBinomialEnclosure in
def invOK (a : Enc) : Exponent → Bool
  | .inverse => (cneg a == 0) && Nat.blt 0 (cpos a)
  | _ => true

open RoundedBinomialEnclosure in
def kvalid (a : Enc) (e : Exponent) : Bool :=
  sqrtOK a && Nat.blt 0 (kseed a) && invOK a e &&
    Nat.blt (200*spanN (knormalized a e)) (19*T)

def withOk (E : Enc) (b : Bool) : Enc := ⟨E.pos,E.neg,E.nrm,E.err,E.ok && b⟩

open RoundedBinomialEnclosure in
def kenclose (a : Enc) (e : Exponent) : Enc :=
  withOk (kscale false (kfactor a e).1 (kfactor a e).2
    (kwiden (khorner (knormalized a e) (coefList e)) ((kcoef e 13).2.1*spanN (knormalized a e)^13)
      ((kcoef e 13).2.2*T^12*(T-spanN (knormalized a e))))) (kvalid a e)

theorem withOk_ok (E : Enc) (b : Bool) : (withOk E b).ok=(E.ok && b) := by unfold withOk; exact rfl

theorem rep_withOk {E : Enc} {x : TensorPolynomialEnclosure.Enclosure} (h : Rep E x) (b : Bool) :
    Rep (withOk E b) x := by
  obtain ⟨P,N,hI,hp,hn,hm,hpol,he⟩ := h
  have e1 : (withOk E b).pos=E.pos := by unfold withOk; exact rfl
  have e2 : (withOk E b).neg=E.neg := by unfold withOk; exact rfl
  have e3 : (withOk E b).nrm=E.nrm := by unfold withOk; exact rfl
  have e4 : (withOk E b).err=E.err := by unfold withOk; exact rfl
  exact ⟨P,N,hI,by rw [e1]; exact hp,by rw [e2]; exact hn,by rw [e3]; exact hm,hpol,
    by rw [e4]; exact he⟩

theorem rep_span {N : Enc} {n : TensorPolynomialEnclosure.Enclosure} (h : Rep N n) :
    TensorPolynomialEnclosure.norm n.polynomial+n.error=((spanN N : ℕ) : ℚ)/10^24 := by
  obtain ⟨P,Q,hI,_,_,hm,hpol,he⟩ := h
  rw [hpol,hI.norm,he,spanN,hm]
  have : (E4 : ℚ)=10^4 := by norm_num [E4]
  push_cast; rw [this]; field_simp

open RoundedBinomialEnclosure in
theorem enclose_data {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a) (e : Exponent)
    (hsq : sqrtOK A=true) (hseed : 0 < kseed A) (hinv : invOK A e=true) :
    seed a=(kseed A : ℚ)/10^10 ∧ 1/base a e=sval false (invBase A e).1 (invBase A e).2 ∧
      RoundedBinomialEnclosure.factor a e=sval false (kfactor A e).1 (kfactor A e).2 ∧
      0 < base a e := by
  obtain ⟨hcen,hdisj⟩ := rep_center h
  have hseedq : seed a=(kseed A : ℚ)/10^10 := by
    rw [seed,hcen]; exact nearestRoot_eq hdisj hsq
  have hE20 : (E20 : ℚ)=10^20 := by norm_num [E20]
  have hE10 : (E10 : ℚ)=10^10 := by norm_num [E10]
  have hmq : (0:ℚ) < kseed A := by exact_mod_cast hseed
  refine ⟨hseedq,?_,?_,?_⟩
  · cases e
    · simp only [base,invBase,sval,Bool.false_eq_true,ite_false,hseedq,hE20]
      push_cast; field_simp
    · simp only [base,invBase,sval,Bool.false_eq_true,ite_false,hseedq,hE20]
      push_cast; field_simp
    · simp only [invOK,Bool.and_eq_true,beq_iff_eq,Nat.blt_eq] at hinv
      simp only [base,invBase,sval,Bool.false_eq_true,ite_false,hcen,hinv.1,T_cast,Nat.cast_zero,
        sub_zero,one_div_div]
  · cases e
    · simp only [RoundedBinomialEnclosure.factor,kfactor,sval,Bool.false_eq_true,ite_false,hseedq,hE10]
    · simp only [RoundedBinomialEnclosure.factor,kfactor,sval,Bool.false_eq_true,ite_false,hseedq,
        hE10]
      field_simp
    · simp only [invOK,Bool.and_eq_true,beq_iff_eq,Nat.blt_eq] at hinv
      simp only [RoundedBinomialEnclosure.factor,kfactor,sval,Bool.false_eq_true,ite_false,hcen,
        hinv.1,T_cast,Nat.cast_zero,sub_zero,one_div_div]
  · cases e
    · simp only [base]; rw [hseedq]; positivity
    · simp only [base]; rw [hseedq]; positivity
    · simp only [invOK,Bool.and_eq_true,beq_iff_eq,Nat.blt_eq] at hinv
      simp only [base]; rw [hcen,hinv.1]
      have : (0:ℚ) < cpos A := by exact_mod_cast hinv.2
      simp only [Nat.cast_zero,sub_zero]; positivity

open RoundedBinomialEnclosure in
theorem rep_enclose {A : Enc} {a : TensorPolynomialEnclosure.Enclosure} (h : Rep A a) (e : Exponent)
    (hok : (kenclose A e).ok=true) : Rep (kenclose A e) (enclose a e) ∧ Valid a e := by
  unfold kenclose at hok
  rw [withOk_ok] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hin,hv⟩ := hok
  unfold kvalid at hv
  simp only [Bool.and_eq_true,Nat.blt_eq] at hv
  obtain ⟨⟨⟨hsq,hseed⟩,hinv⟩,hspan⟩ := hv
  obtain ⟨hseedq,hinvb,hfac,hbase⟩ := enclose_data h e hsq hseed hinv
  -- okay flags
  have hok1 := kmul_ok_right hin
  have hok2 := kwiden_ok_left hok1
  have hNok : (knormalized A e).ok=true := by
    have : ∀ (cs : List (Bool × ℕ × ℕ)), cs ≠ [] → (khorner (knormalized A e) cs).ok=true →
        (knormalized A e).ok=true := by
      intro cs hcs hk
      cases cs with
      | nil => exact absurd rfl hcs
      | cons c cs =>
        rw [khorner.eq_2] at hk
        exact kmul_ok_left (kadd_ok_right hk)
    exact this _ (coefList_ne e) hok2
  have hrepN : Rep (knormalized A e) (normalized a e) := by
    unfold knormalized at hNok ⊢
    unfold normalized RoundedTensorEnclosure.sub
    rw [hinvb]
    have hc1 : (kconst false 1 1).ok=true := by
      have := kadd_ok_right hNok; rwa [kneg_ok] at this
    have r1 := rep_neg (rep_const false 1 1 hc1)
    rw [sval_one] at r1
    exact rep_add (rep_scale h false _ _ (kadd_ok_left hNok)) r1 hNok
  have hspanq : span a e=((spanN (knormalized A e) : ℕ) : ℚ)/10^24 := rep_span hrepN
  have hST : spanN (knormalized A e) < T := by
    have : 19*T < 200*T := by have := T_pos; omega
    omega
  have hvalid : Valid a e := by
    refine ⟨?_,hbase,?_⟩
    · rw [hseedq]; have : (0:ℚ) < kseed A := by exact_mod_cast hseed
      positivity
    · rw [hspanq]
      have : (200*spanN (knormalized A e) : ℚ) < 19*T := by exact_mod_cast hspan
      rw [T_cast] at this
      rw [div_lt_iff₀ (by norm_num)]; linarith
  have htail : tail a e=sval false ((kcoef e 13).2.1*spanN (knormalized A e)^13)
      ((kcoef e 13).2.2*T^12*(T-spanN (knormalized A e))) := by
    unfold tail
    rw [hspanq,coefficient_eq]
    have hd := kcoef_den_pos e 13
    have habs : |sv (kcoef e 13)|=((kcoef e 13).2.1 : ℚ)/(kcoef e 13).2.2 := by
      unfold sv sval; split_ifs
      · rw [abs_neg,abs_of_nonneg (by positivity)]
      · rw [abs_of_nonneg (by positivity)]
    rw [habs]
    unfold sval
    simp only [Bool.false_eq_true,ite_false]
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Nat.cast_sub hST.le,T_cast]
    have hS : ((spanN (knormalized A e) : ℕ) : ℚ) < 10^24 := by
      have := hST; rw [← T_cast]; exact_mod_cast this
    have hd' : (0:ℚ) < (kcoef e 13).2.2 := by exact_mod_cast hd
    have h1 : (1:ℚ)-(spanN (knormalized A e) : ℚ)/10^24 ≠ 0 := by
      have : (spanN (knormalized A e) : ℚ)/10^24 < 1 := by rw [div_lt_one (by norm_num)]; exact hS
      linarith
    have h2 : (10^24 : ℚ)-(spanN (knormalized A e) : ℚ) ≠ 0 := by linarith
    field_simp
  refine ⟨?_,hvalid⟩
  apply rep_withOk
  unfold enclose
  rw [hfac,htail,coefficients_eq]
  exact rep_scale (rep_widen (rep_horner hrepN _ hok2) _ _ hok1) false _ _ hin

/-! ### Expressions -/

open RoundedBinomialEnclosure in
inductive IExpr where
  | nat (n : ℕ)
  | lit (r : ℚ) (s : Bool) (n d : ℕ) (h : r=sval s n d)
  | var (i : Input)
  | add (a b : IExpr)
  | neg (a : IExpr)
  | mul (a b : IExpr)
  | power (a : IExpr) (n : ℕ)
  | binomial (e : Exponent) (a : IExpr)

namespace IExpr
instance : Add IExpr := ⟨.add⟩
instance : Neg IExpr := ⟨.neg⟩
instance : Sub IExpr := ⟨fun a b => .add a (.neg b)⟩
instance : Mul IExpr := ⟨.mul⟩
instance : Pow IExpr ℕ := ⟨.power⟩
instance (n : ℕ) : OfNat IExpr n := ⟨.nat n⟩
instance : Div IExpr := ⟨fun a b => .mul a (.binomial .inverse b)⟩

def toExpr : IExpr → Expr
  | .nat n => .literal n
  | .lit r _ _ _ _ => .literal r
  | .var i => .variable i
  | .add a b => .add (toExpr a) (toExpr b)
  | .neg a => .neg (toExpr a)
  | .mul a b => .mul (toExpr a) (toExpr b)
  | .power a n => .power (toExpr a) n
  | .binomial e a => .binomial e (toExpr a)

def eval (w : Input → Enc) : IExpr → Enc
  | .nat n => kconst false n 1
  | .lit _ s n d _ => kconst s n d
  | .var i => w i
  | .add a b => kadd (eval w a) (eval w b)
  | .neg a => kneg (eval w a)
  | .mul a b => kmul (eval w a) (eval w b)
  | .power a n => withOk (kpower (eval w a) n) (eval w a).ok
  | .binomial e a => kenclose (eval w a) e
end IExpr

open RoundedBinomialEnclosure in
theorem kenclose_ok_arg {X : Enc} {e : Exponent} (h : (kenclose X e).ok=true) : X.ok=true := by
  unfold kenclose at h
  rw [withOk_ok] at h
  simp only [Bool.and_eq_true] at h
  have h2 := kwiden_ok_left (kmul_ok_right h.1)
  have h3 : (knormalized X e).ok=true := by
    have : ∀ (cs : List (Bool × ℕ × ℕ)), cs ≠ [] → (khorner (knormalized X e) cs).ok=true →
        (knormalized X e).ok=true := by
      intro cs hcs hk
      cases cs with
      | nil => exact absurd rfl hcs
      | cons c cs =>
        rw [khorner.eq_2] at hk
        exact kmul_ok_left (kadd_ok_right hk)
    exact this _ (coefList_ne e) h2
  unfold knormalized at h3
  exact kmul_ok_right (kadd_ok_left h3)

theorem rep_eval (w : Input → Enc) (hw : ∀ i, Rep (w i) (models i)) :
    ∀ e : IExpr,(IExpr.eval w e).ok=true →
      Rep (IExpr.eval w e) ((IExpr.toExpr e).model models) ∧ (IExpr.toExpr e).safe models=true
  | .nat n, hok => by
    have := rep_const false n 1 hok
    rw [show sval false n 1=(n:ℚ) by simp [sval]] at this
    exact ⟨this,rfl⟩
  | .lit r s n d hr, hok => by
    have := rep_const s n d hok
    rw [← hr] at this
    exact ⟨this,rfl⟩
  | .var i, _ => ⟨hw i,rfl⟩
  | .add a b, hok => by
    have ha := rep_eval w hw a (kadd_ok_left hok)
    have hb := rep_eval w hw b (kadd_ok_right hok)
    refine ⟨rep_add ha.1 hb.1 hok,?_⟩
    simp only [IExpr.toExpr,Expression.safe,ha.2,hb.2,Bool.and_self]
  | .neg a, hok => by
    have ha := rep_eval w hw a (by rw [IExpr.eval,kneg_ok] at hok; exact hok)
    exact ⟨rep_neg ha.1,ha.2⟩
  | .mul a b, hok => by
    have ha := rep_eval w hw a (kmul_ok_left hok)
    have hb := rep_eval w hw b (kmul_ok_right hok)
    refine ⟨rep_mul ha.1 hb.1 hok,?_⟩
    simp only [IExpr.toExpr,Expression.safe,ha.2,hb.2,Bool.and_self]
  | .power a n, hok => by
    simp only [IExpr.eval] at hok
    rw [withOk_ok] at hok
    simp only [Bool.and_eq_true] at hok
    have ha := rep_eval w hw a hok.2
    exact ⟨rep_withOk (rep_power ha.1 n hok.1) _,ha.2⟩
  | .binomial e a, hok => by
    rw [IExpr.eval.eq_8] at hok
    rw [IExpr.eval.eq_8,IExpr.toExpr.eq_8,Expression.model.eq_7,Expression.safe.eq_7]
    have ha := rep_eval w hw a (kenclose_ok_arg hok)
    have hr := rep_enclose ha.1 e hok
    rw [ha.2,Bool.true_and,decide_eq_true_eq]
    exact hr

/-! ### The derivative, with integer data on its literals -/

namespace D
open IExpr
def root (a : IExpr) : IExpr := .binomial .root a
def inverseRoot (a : IExpr) : IExpr := .binomial .inverseRoot a
def q : IExpr := .var .q
def u : IExpr := .var .u
def z : IExpr := .var .z
def sinT : IExpr := .var .sinT
def cosT : IExpr := .var .cosT
def sinZ : IExpr := .var .sinZ
def cosZ : IExpr := .var .cosZ
def sinRest : IExpr := .var .sinRest
def cosRest : IExpr := .var .cosRest
def r : IExpr := root (q-u^2)
def upperRight : IExpr := root (q-(2-u)^2)
def upperLeft : IExpr := 3-upperRight
def upperHeight : IExpr := root (q-upperLeft^2)
def lowerHeight : IExpr := 2-upperHeight
def lowerLeft : IExpr := root (q-lowerHeight^2)
def first : IExpr := 2-cosT*(r-1)+sinT*u
def second : IExpr := 1+cosT*lowerHeight-sinT*(lowerLeft-1)
def eta : IExpr := lowerHeight/lowerLeft
def lambda : IExpr := cosT+eta*sinT
def k0 : IExpr := lambda*upperLeft/upperHeight
def ell0 : IExpr := k0*(2-u)/upperRight
def c0 : IExpr := first/second
def ak : IExpr := .lit (3/50) false 3 50 (by norm_num [sval])
def al : IExpr := .lit (-23/100) true 23 100 (by norm_num [sval])
def ac : IExpr := .lit (-53/100) true 53 100 (by norm_num [sval])
def k : IExpr := k0+ak*z
def ell : IExpr := ell0+al*z
def c : IExpr := c0+ac*z
def fZ : IExpr := cosZ+eta*sinZ
def p : IExpr := cosRest+eta*sinRest
def m : IExpr := c*fZ
def pDeriv : IExpr := sinRest-eta*cosRest
def mDeriv : IExpr := ac*fZ+c*(-sinZ+eta*cosZ)
def radius : IExpr := root q
def contactA : IExpr := 1+2*eta-radius*root (1+eta^2)
def contactZ : IExpr := 1+2*cosZ+contactA*sinZ
def contactDerivZ : IExpr := -2*sinZ+contactA*cosZ
def contactDerivRest : IExpr := -2*sinRest+contactA*cosRest
def normH2 : IExpr := p^2+k^2
def normA2 : IExpr := k^2+ell^2
def normB2 : IExpr := ell^2+m^2-2*ell*m*sinT
def normD2 : IExpr := 1+c^2
def numeratorH : IExpr := p*pDeriv+k*ak
def numeratorA : IExpr := k*ak+ell*al
def numeratorB : IExpr := ell*al+m*mDeriv-(al*m+ell*mDeriv)*sinT
def numeratorD : IExpr := c*ac
def derivative : IExpr :=
  3*ak+2*al+ac*contactZ+c*contactDerivZ-contactDerivRest+
    mDeriv*(cosT-1)-radius*(
      numeratorH*inverseRoot normH2+numeratorA*inverseRoot normA2+
      numeratorB*inverseRoot normB2+numeratorD*inverseRoot normD2)
end D

theorem toExpr_derivative : IExpr.toExpr D.derivative=CriticalPositiveTModel.derivative := rfl

/-! ### The ten input models -/

def kouter : Enc := ⟨T*BW,0,T,0,true⟩
def kinner : Enc := ⟨T*B,0,T,0,true⟩
def kq : Enc := ⟨3915467069000000000000000,0,3915467069000000000000000,6706900000000000,true⟩
def kt : Enc := kadd (kconst false 13 100) (kscale false 3 100 kouter)
def kz : Enc := kscale false 1 2 (kmul kt (kadd (kconst false 1 1) kinner))
def ku : Enc := kwiden (kadd (kconst false 1 1) (kneg (kscale false 51 80 kt))) 7 4000
def krest : Enc := kadd kt (kneg kz)

def kmodels : Input → Enc
  | .q => kq
  | .u => ku
  | .t => kt
  | .z => kz
  | .sinT => ksine kt
  | .cosT => kcosine kt
  | .sinZ => ksine kz
  | .cosZ => kcosine kz
  | .sinRest => ksine krest
  | .cosRest => kcosine krest

def kresult : Enc := IExpr.eval kmodels D.derivative

def finalCheck : Bool :=
  ku.ok && (kt.ok && (kz.ok && (krest.ok && ((ksine kt).ok && ((kcosine kt).ok && ((ksine kz).ok &&
  ((kcosine kz).ok && ((ksine krest).ok && ((kcosine krest).ok &&
  (kresult.ok && ((cneg kresult == 0) && (Nat.ble (cpos kresult) kresult.nrm &&
  (Nat.blt (4183*T) (100000*cpos kresult) &&
  (Nat.blt (50000*(kresult.nrm-cpos kresult)) (973*T) &&
  (Nat.blt (100000*kresult.err) (2053*E20) &&
  Nat.blt (9*T+5000*kresult.nrm+5000*E4*kresult.err) (10000*cpos kresult))))))))))))))))

theorem rep_grid {E : Enc} {P : NB} (hI : Inv P 0) (hp : E.pos=evB P) (hn : E.neg=0)
    (hm : E.nrm=ev1 P) (he : E.err=0) (x : Bv) (hx : x=pol P 0) :
    Rep E (RoundedTensorEnclosure.round ⟨x,0⟩) := by
  refine ⟨P,0,hI,hp,by rw [hn,map_zero],by rw [hm,map_zero,add_zero],?_,?_⟩
  · rw [hx,round_pol]
  · rw [hx,round_pol,he]
    have := upwardError_nat 0
    simp only [Nat.cast_zero,zero_div] at this ⊢
    exact this

theorem inv_mono (i j v : ℕ) (hv : v < B) (hij : i+j ≤ 10) : Inv (monoN i j v) 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a b h; rw [cf_monoN] at h; split_ifs at h with hab
    · omega
    · exact absurd rfl h
  · intro a b h; simp [cf_zero] at h
  · intro a b; rw [cf_monoN]; split_ifs
    · exact hv
    · exact B_pos
  · intro a b; rw [cf_zero]; exact B_pos
  · intro a b; exact Or.inr (cf_zero a b)

theorem T_lt_B : T < B := by
  unfold T B; norm_num

theorem rep_outer : Rep kouter RoundedTensorEnclosure.outerVariable := by
  unfold RoundedTensorEnclosure.outerVariable
  apply rep_grid (P := monoN 1 0 T) (inv_mono 1 0 T T_lt_B (by norm_num))
  · rw [show kouter.pos=T*BW by unfold kouter; exact rfl]
    simp [evB,evXY_monoN,BW]
  · unfold kouter; exact rfl
  · rw [show kouter.nrm=T by unfold kouter; exact rfl]; simp [ev1,evXY_monoN]
  · unfold kouter; exact rfl
  · apply bv_ext; intro i j
    rw [bcf_pol,cf_monoN,cf_zero,show (X : Bv)=TensorWholeIntervalPolynomial.scalar 1*X^1*(C X)^0 by
      simp [TensorWholeIntervalPolynomial.scalar],bcf_monomial]
    split_ifs <;> simp [T_cast]

theorem rep_inner : Rep kinner RoundedTensorEnclosure.innerVariable := by
  unfold RoundedTensorEnclosure.innerVariable
  apply rep_grid (P := monoN 0 1 T) (inv_mono 0 1 T T_lt_B (by norm_num))
  · rw [show kinner.pos=T*B by unfold kinner; exact rfl]
    simp [evB,evXY_monoN]
  · unfold kinner; exact rfl
  · rw [show kinner.nrm=T by unfold kinner; exact rfl]; simp [ev1,evXY_monoN]
  · unfold kinner; exact rfl
  · apply bv_ext; intro i j
    rw [bcf_pol,cf_monoN,cf_zero,show (C X : Bv)=TensorWholeIntervalPolynomial.scalar 1*X^0*(C X)^1 by
      simp [TensorWholeIntervalPolynomial.scalar],bcf_monomial]
    split_ifs <;> simp [T_cast]

theorem rep_q : Rep kq qModel := by
  unfold qModel
  have hk : (3915467069000000000000000:ℕ) < B := by unfold B; norm_num
  have hI := inv_mono 0 0 _ hk (by norm_num)
  refine ⟨monoN 0 0 3915467069000000000000000,0,hI,?_,?_,?_,?_,?_⟩
  · rw [show kq.pos=3915467069000000000000000 by unfold kq; exact rfl]; simp [evB,evXY_monoN]
  · rw [show kq.neg=0 by unfold kq; exact rfl,map_zero]
  · rw [show kq.nrm=3915467069000000000000000 by unfold kq; exact rfl]; simp [ev1,evXY_monoN]
  · have : TensorWholeIntervalPolynomial.scalar qMid=pol (monoN 0 0 3915467069000000000000000) 0 := by
      apply bv_ext; intro i j
      rw [bcf_scalar,bcf_pol,cf_monoN,cf_zero]
      split_ifs <;> norm_num [qMid]
    rw [this,round_pol]
  · have : TensorWholeIntervalPolynomial.scalar qMid=pol (monoN 0 0 3915467069000000000000000) 0 := by
      apply bv_ext; intro i j
      rw [bcf_scalar,bcf_pol,cf_monoN,cf_zero]
      split_ifs <;> norm_num [qMid]
    rw [this,round_pol,show kq.err=6706900000000000 by unfold kq; exact rfl]
    have hw : qWidth=((6706900000000000:ℕ):ℚ)/10^20 := by norm_num [qWidth]
    rw [hw,upwardError_nat]

theorem finalCheck_parts (h : finalCheck=true) :
    ku.ok=true ∧ kt.ok=true ∧ kz.ok=true ∧ krest.ok=true ∧ (ksine kt).ok=true ∧
    (kcosine kt).ok=true ∧ (ksine kz).ok=true ∧ (kcosine kz).ok=true ∧ (ksine krest).ok=true ∧
    (kcosine krest).ok=true ∧ kresult.ok=true ∧ cneg kresult=0 ∧ cpos kresult ≤ kresult.nrm ∧
    4183*T < 100000*cpos kresult ∧ 50000*(kresult.nrm-cpos kresult) < 973*T ∧
    100000*kresult.err < 2053*E20 ∧ 9*T+5000*kresult.nrm+5000*E4*kresult.err < 10000*cpos kresult := by
  unfold finalCheck at h
  simp only [Bool.and_eq_true,Nat.blt_eq,Nat.ble_eq,beq_iff_eq] at h
  exact h

theorem rep_models (h : finalCheck=true) : ∀ i, Rep (kmodels i) (models i) := by
  obtain ⟨hu,ht,hz,hr,h1,h2,h3,h4,h5,h6,-⟩ := finalCheck_parts h
  have e1 : ∀ n d : ℕ, ((n:ℚ)/d)=sval false n d := fun n d => by simp [sval]
  have rt : Rep kt tModel := by
    unfold tModel kt at *
    rw [show (13/100:ℚ)=sval false 13 100 by norm_num [sval],
      show (3/100:ℚ)=sval false 3 100 by norm_num [sval]]
    exact rep_add (rep_const false 13 100 (kadd_ok_left ht))
      (rep_scale rep_outer false 3 100 (kadd_ok_right ht)) ht
  have rz : Rep kz zModel := by
    unfold zModel kz at *
    rw [show (1/2:ℚ)=sval false 1 2 by norm_num [sval],
      show (1:ℚ)=sval false 1 1 by norm_num [sval]]
    have hm := kmul_ok_right hz
    exact rep_scale (rep_mul rt (rep_add (rep_const false 1 1 (kadd_ok_left (kmul_ok_right hm)))
      rep_inner (kmul_ok_right hm)) hm) false 1 2 hz
  have ru : Rep ku uModel := by
    unfold uModel ku at *
    unfold RoundedTensorEnclosure.sub
    rw [show (7/4000:ℚ)=((7:ℕ):ℚ)/((4000:ℕ):ℚ) by norm_num,
      show (51/80:ℚ)=sval false 51 80 by norm_num [sval],
      show (1:ℚ)=sval false 1 1 by norm_num [sval]]
    have ha := kwiden_ok_left hu
    have hn : (kscale false 51 80 kt).ok=true := by
      have := kadd_ok_right ha; rwa [kneg_ok] at this
    exact rep_widen (rep_add (rep_const false 1 1 (kadd_ok_left ha))
      (rep_neg (rep_scale rt false 51 80 hn)) ha) 7 4000 hu
  have rr : Rep krest restModel := by
    unfold restModel krest at *
    unfold RoundedTensorEnclosure.sub
    exact rep_add rt (rep_neg rz) hr
  intro i
  cases i
  · exact rep_q
  · exact ru
  · exact rt
  · exact rz
  · exact rep_sine rt h1
  · exact rep_cosine rt h2
  · exact rep_sine rz h3
  · exact rep_cosine rz h4
  · exact rep_sine rr h5
  · exact rep_cosine rr h6

theorem norm_sub_center {R : Enc} {x : TensorPolynomialEnclosure.Enclosure} (h : Rep R x)
    (hn : cneg R=0) :
    TensorPolynomialEnclosure.norm (x.polynomial-TensorWholeIntervalPolynomial.scalar
      (RoundedTensorEnclosure.center x))=((R.nrm : ℚ)-cpos R)/10^24 := by
  obtain ⟨hcen,_⟩ := rep_center h
  rw [hcen,hn]
  obtain ⟨P,N,hI,hp,hnn,hm,hpol,he⟩ := h
  have hd := hI.digits (i := 0) (j := 0) W_pos
  simp only [mul_zero,add_zero,dig,gdig,pow_zero,Nat.div_one] at hd
  have e1 : cpos R=cf P 0 0 := by rw [cpos,hp]; exact hd.1
  have e2 : cneg R=cf N 0 0 := by rw [cneg,hnn]; exact hd.2
  rw [hpol]
  have h00 : bcf (pol P N) 0 0=((cpos R : ℚ)-((0:ℕ):ℚ))/10^24 := by
    rw [bcf_pol,e1,← e2,hn]
  have hs : ∀ i j, bcf (pol P N-TensorWholeIntervalPolynomial.scalar (((cpos R : ℚ)-((0:ℕ):ℚ))/10^24)) i j ≠ 0 →
      i < 11 ∧ j < 11 := by
    intro i j hij
    rw [bcf_sub,bcf_pol,bcf_scalar] at hij
    by_cases h0 : i=0 ∧ j=0
    · omega
    · by_cases hP : cf P i j=0
      · by_cases hN : cf N i j=0
        · rw [hP,hN,ite_eq_right h0] at hij; simp at hij
        · exact sup_lt hI.supN (le_refl _) (le_refl _) i j hN
      · exact sup_lt hI.supP (le_refl _) (le_refl _) i j hP
  have hs' : ∀ i j, bcf (pol P N) i j ≠ 0 → i < 11 ∧ j < 11 := by
    intro i j hij
    rw [bcf_pol] at hij
    by_cases hP : cf P i j=0
    · by_cases hN : cf N i j=0
      · rw [hP,hN] at hij; simp at hij
      · exact sup_lt hI.supN (le_refl _) (le_refl _) i j hN
    · exact sup_lt hI.supP (le_refl _) (le_refl _) i j hP
  have hterm : ∀ i j, |bcf (pol P N-TensorWholeIntervalPolynomial.scalar
      (((cpos R : ℚ)-((0:ℕ):ℚ))/10^24)) i j|=
      |bcf (pol P N) i j|-(if 0=i ∧ 0=j then |bcf (pol P N) 0 0| else 0) := by
    intro i j
    rw [bcf_sub,bcf_scalar]
    by_cases h0 : i=0 ∧ j=0
    · obtain ⟨rfl,rfl⟩ := h0; rw [h00]; simp
    · rw [ite_eq_right h0,ite_eq_right (fun h => h0 ⟨h.1.symm,h.2.symm⟩)]; simp
  rw [norm_eq_range hs]
  simp only [hterm,Finset.sum_sub_distrib,sum_sum_ite_eq]
  rw [← norm_eq_range hs',hI.norm,hm,h00]
  simp only [show (0:ℕ) < 11 from by norm_num,and_self,ite_true,Nat.cast_zero,sub_zero]
  rw [abs_of_nonneg (by positivity)]
  push_cast
  ring

theorem finalCheck_true : finalCheck=true := by decide +kernel

theorem rep_result : Rep kresult enclosure ∧ derivative.safe models=true := by
  have h := rep_eval kmodels (rep_models finalCheck_true) D.derivative
    (finalCheck_parts finalCheck_true).2.2.2.2.2.2.2.2.2.2.1
  rw [toExpr_derivative] at h
  exact h

end r52_K

theorem all_binomial_arguments : derivative.safe models=true := r52_K.rep_result.2

theorem uniform_reserve : (9/5000:ℚ)<RoundedTensorEnclosure.floor enclosure := by
  have hp := r52_K.finalCheck_parts r52_K.finalCheck_true
  have hres := r52_K.rep_result.1
  obtain ⟨hc,_⟩ := r52_K.rep_center hres
  have hn := r52_K.norm_sub_center hres hp.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨P,N,_,_,_,_,_,he⟩ := hres
  unfold RoundedTensorEnclosure.floor
  rw [show RoundedTensorEnclosure.norm=TensorPolynomialEnclosure.norm from rfl]
  rw [hn,he,hc,hp.2.2.2.2.2.2.2.2.2.2.2.1]
  have h := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hE : (r52_K.E4 : ℚ)=10^4 := by norm_num [r52_K.E4]
  have h' : (9:ℚ)*10^24+5000*r52_K.kresult.nrm+5000*10^4*r52_K.kresult.err <
      10000*r52_K.cpos r52_K.kresult := by
    rw [← r52_K.T_cast,← hE]; exact_mod_cast h
  generalize (r52_K.cpos r52_K.kresult : ℚ)=c at h' ⊢
  generalize (r52_K.kresult.nrm : ℚ)=n at h' ⊢
  generalize (r52_K.kresult.err : ℚ)=e at h' ⊢
  have key : (c-((0:ℕ):ℚ))/10^24-(n-c)/10^24-e/10^20=(2*c-n-10^4*e)/10^24 := by
    push_cast; ring
  rw [key,lt_div_iff₀ (by norm_num)]
  linarith

noncomputable section

def values (Q U T Z : ℝ) : Input→ℝ
  | .q => Q
  | .u => U
  | .t => T
  | .z => Z
  | .sinT => Real.sin T
  | .cosT => Real.cos T
  | .sinZ => Real.sin Z
  | .cosZ => Real.cos Z
  | .sinRest => Real.sin (T-Z)
  | .cosRest => Real.cos (T-Z)

def outerCoordinate (T : ℝ) : ℝ := (T-13/100)/(3/100)
def innerCoordinate (T Z : ℝ) : ℝ := 2*Z/T-1

theorem coordinates_mem {T Z : ℝ} (hT : T∈Icc (1/10:ℝ) (4/25))
    (hZ : Z∈Icc 0 T) :
    |outerCoordinate T|≤1 ∧ |innerCoordinate T Z|≤1 := by
  have hT0 : 0<T := by linarith [hT.1]
  constructor
  · rw [abs_le]
    dsimp [outerCoordinate]
    constructor <;> norm_num <;> linarith [hT.1,hT.2]
  · rw [abs_le]
    dsimp [innerCoordinate]
    constructor
    · have h := div_nonneg (show 0≤2*Z by linarith [hZ.1]) hT0.le
      linarith
    · have h : 2*Z/T≤2 := (div_le_iff₀ hT0).2 (by linarith [hZ.2])
      linarith

theorem position_error {T U : ℝ} (hT : T∈Icc (1/10:ℝ) (4/25))
    (hU : 499/500-127/200*T<U ∧ U<501/500-16/25*T) :
    |U-(1-51/80*T)|≤7/4000 := by
  rw [abs_le]
  constructor <;> linarith [hU.1,hU.2,hT.1]

theorem input_contains {Q U T Z : ℝ} (hQ : Q∈Icc qLow qTrial)
    (hT : T∈Icc (1/10:ℝ) (4/25)) (hZ : Z∈Icc 0 T)
    (hU : 499/500-127/200*T<U ∧ U<501/500-16/25*T) :
    ∀i,Contains (models i) (outerCoordinate T) (innerCoordinate T Z) (values Q U T Z i) := by
  obtain ⟨hX,hY⟩ := coordinates_mem hT hZ
  have hT0 : 0<T := by linarith [hT.1]
  have hTm : Contains tModel (outerCoordinate T) (innerCoordinate T Z) T := by
    have h := contains_add (contains_constant (13/100) hX hY)
      (contains_scale (contains_outer hX hY) (3/100) hX hY) hX hY
    have he : ((13/100:ℚ):ℝ)+((3/100:ℚ):ℝ)*outerCoordinate T=T := by
      simp only [outerCoordinate]
      push_cast
      ring
    rw [he] at h
    exact h
  have hZm : Contains zModel (outerCoordinate T) (innerCoordinate T Z) Z := by
    have h := contains_scale (contains_mul hTm
      (contains_add (contains_constant 1 hX hY) (contains_inner hX hY) hX hY) hX hY)
      (1/2) hX hY
    have he : ((1/2:ℚ):ℝ)*(T*(((1:ℚ):ℝ)+innerCoordinate T Z))=Z := by
      simp only [innerCoordinate]
      push_cast
      field_simp
      ring
    rw [he] at h
    exact h
  have hUm : Contains uModel (outerCoordinate T) (innerCoordinate T Z) U := by
    apply contains_widen
      (contains_sub (contains_constant 1 hX hY) (contains_scale hTm (51/80) hX hY) hX hY)
      (by norm_num) ?_ hX hY
    have h := position_error hT hU
    push_cast
    convert h using 2
  have hQm : Contains qModel (outerCoordinate T) (innerCoordinate T Z) Q := by
    apply contains_round ?_ hX hY
    refine ⟨by norm_num [qWidth],?_⟩
    change |Q-TensorWholeIntervalPolynomial.evaluate _ _
      (TensorWholeIntervalPolynomial.scalar qMid)|≤((qWidth:ℚ):ℝ)
    rw [TensorWholeIntervalPolynomial.evaluate_scalar,abs_le]
    have h1 := hQ.1
    have h2 := hQ.2
    simp only [qLow,qTrial] at h1 h2
    constructor <;> norm_num [qMid,qWidth] <;> linarith
  have hRm := contains_sub hTm hZm hX hY
  have hTF : T∈Icc 0 frameCap := ⟨by linarith [hT.1],by norm_num [frameCap]; linarith [hT.2]⟩
  have hZF : Z∈Icc 0 frameCap := ⟨hZ.1,hZ.2.trans hTF.2⟩
  have hRF : T-Z∈Icc 0 frameCap := ⟨by linarith [hZ.2],by linarith [hZ.1,hTF.2]⟩
  intro i
  cases i
  · exact hQm
  · exact hUm
  · exact hTm
  · exact hZm
  · exact contains_sine hTm hX hY hTF
  · exact contains_cosine hTm hX hY hTF
  · exact contains_sine hZm hX hY hZF
  · exact contains_cosine hZm hX hY hZF
  · exact contains_sine hRm hX hY hRF
  · exact contains_cosine hRm hX hY hRF

/-- The model encloses the explicit real expression for every q,u in
the printed strips independently, before choosing the exact minimizer. -/
theorem derivative_lower {Q U T Z : ℝ} (hQ : Q∈Icc qLow qTrial)
    (hT : T∈Icc (1/10:ℝ) (4/25)) (hZ : Z∈Icc 0 T)
    (hU : 499/500-127/200*T<U ∧ U<501/500-16/25*T) :
    9/5000<derivative.value (values Q U T Z) := by
  obtain ⟨hX,hY⟩ := coordinates_mem hT hZ
  have hc := derivative.contains (input_contains hQ hT hZ hU) hX hY all_binomial_arguments
  have hl := RoundedTensorEnclosure.lower hc hX hY
  have hr : ((9/5000:ℚ):ℝ)<(RoundedTensorEnclosure.floor enclosure:ℝ) := by
    exact_mod_cast uniform_reserve
  have h9 : ((9/5000:ℚ):ℝ)=9/5000 := by norm_num
  rw [h9] at hr
  exact hr.trans_le hl

theorem minimizing_derivative_lower {Q T Z : ℝ} (hQ : Q∈Icc qLow qTrial)
    (hT : T∈Icc (1/10:ℝ) (4/25)) (hZ : Z∈Icc 0 T) :
    9/5000<derivative.value
      (values Q (Stationary.FiveCornerGeometry.minimizingPosition Q T) T Z) := by
  apply derivative_lower hQ hT hZ
  exact CriticalEPosition.minimizingPosition_strip
    (by simpa [CriticalEPolynomials.qLower,CriticalEPolynomials.qUpper,qLow,qTrial] using hQ) hT

end
end SquaresInCircles.Eight.CriticalPositiveTModel
