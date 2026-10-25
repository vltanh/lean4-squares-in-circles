module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PolynomialData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: whole-interval positivity of the fourteen negative-A / TD2 numerators

The two tight low numerators keep their
displayed leading terms, the mixed numerator keeps its Chebyshev
quadratic, and the three endpoint quotients keep their positive constant.
Every remaining bound is the stated whole-interval coefficient sum.
The rational identities are proof terms, not executed certificates.

The kernel evaluates integer coefficient lists that mirror the polynomials.  Sums are divided
by the gcd of the list and its scale, which keeps the integers short; long products and the
affine changes of variable are one integer product or evaluation read back in a large base
(Kronecker substitution).  Each bound is one kernel evaluation of integer inequalities.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
open Polynomial WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (h)
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep toPoly chebList lowerZ scale_pos)
open PositiveTD.Certificate (S5 S9 S11 C4 C10 C12 num3 num4 etaQ Rbar cbar sigmabar)

/-! ### Reduced scaled lists

`Scaled.add` and `Scaled.sub` multiply the two scales.  Their reduced forms `addN` and `subN`
divide the list and the scale by their gcd, which keeps the integers of the kernel
computation short. -/

/-- The gcd of `g` and the entries of `l`. -/
private def r42gcd : List ℤ → ℕ → ℕ
  | [],g => g
  | a :: l,g => r42gcd l (Nat.gcd a.natAbs g)

private theorem r42gcd_dvd : ∀ (l : List ℤ) (g : ℕ),
    r42gcd l g ∣ g ∧ ∀ a ∈ l,(r42gcd l g : ℤ) ∣ a
  | [],g => ⟨dvd_rfl,by simp⟩
  | a :: l,g => by
    obtain ⟨h1,h2⟩ := r42gcd_dvd l (Nat.gcd a.natAbs g)
    refine ⟨h1.trans (Nat.gcd_dvd_right _ _),fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl|hb
    · exact Int.ofNat_dvd_left.2 (h1.trans (Nat.gcd_dvd_left _ _))
    · exact h2 b hb

/-- The list and the scale divided by `g`. -/
private def r42div (g : ℕ) (S : Scaled) : Scaled := ⟨S.l.map (· / (g:ℤ)),S.s / g⟩
/-- The list and the scale divided by their gcd. -/
private def r42norm (S : Scaled) : Scaled := r42div (r42gcd S.l S.s) S

private theorem r42_toPoly_div {g : ℤ} : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    C (g:ℚ)*toPoly (l.map (· / g))=toPoly l
  | [],_ => by simp [toPoly]
  | a :: l,h => by
    have ih := r42_toPoly_div l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha : ((a / g : ℤ) : ℚ)*g=a := by exact_mod_cast Int.ediv_mul_cancel (h a List.mem_cons_self)
    simp only [List.map_cons,toPoly]
    rw [mul_add,mul_left_comm,ih,← map_mul,mul_comm,ha]

private theorem r42_toPoly_div_zero : ∀ l : List ℤ,toPoly (l.map (· / (0:ℤ)))=0
  | [] => by simp [toPoly]
  | a :: l => by rw [List.map_cons,toPoly,r42_toPoly_div_zero l,Int.ediv_zero]; simp

private theorem r42_rep_norm {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) : (r42norm S).Rep p := by
  obtain ⟨h1,h2⟩ := r42gcd_dvd S.l S.s
  unfold Scaled.Rep at *
  rw [r42norm,r42div]
  dsimp only
  generalize r42gcd S.l S.s=g at h1 h2
  rcases Nat.eq_zero_or_pos g with rfl|hg
  · simp only [Nat.cast_zero,Nat.div_zero,map_zero,zero_mul,r42_toPoly_div_zero]
  · have hC : C (g:ℚ)≠0 := by rw [Ne,C_eq_zero]; exact_mod_cast hg.ne'
    apply mul_left_cancel₀ hC
    have e := r42_toPoly_div S.l h2
    push_cast at e
    rw [e,hS,← mul_assoc,← map_mul]
    congr 2
    rw [← Nat.cast_mul,Nat.mul_div_cancel' h1]

/-- `Scaled.add`, reduced. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.addN
    (a b : Scaled) : Scaled := r42norm (a.add b)
/-- `Scaled.sub`, reduced. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.subN
    (a b : Scaled) : Scaled := r42norm (a.sub b)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.addN
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.addN b).Rep (p+q) :=
  r42_rep_norm (ha.add hb)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.subN
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.subN b).Rep (p-q) :=
  r42_rep_norm (ha.sub hb)

/-! ### Kronecker substitution

An integer list is evaluated at an integer `B`; when every entry lies in `[-B/2,B/2)`, the list
is read back from the value as its balanced base-`B` digits (`r42_dec_enc`). -/

/-- The list evaluated at `B`. -/
private def r42enc (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a+B*r42enc B l

/-- The residue of `N` modulo `B` in `[-B/2,B/2)`. -/
private def r42bal (B N : ℤ) : ℤ := if 2*(N % B)<B then N % B else N % B-B

/-- The first `n` balanced base-`B` digits of `N`. -/
private def r42dec (B : ℤ) : ℕ → ℤ → List ℤ
  | 0,_ => []
  | n+1,N => r42bal B N :: r42dec B n ((N-r42bal B N) / B)

/-- The sum of the absolute values of the entries. -/
private def r42asum : List ℤ → ℕ
  | [] => 0
  | a :: l => a.natAbs+r42asum l

/-- The largest absolute value of an entry. -/
private def r42amax : List ℤ → ℕ
  | [] => 0
  | a :: l => max a.natAbs (r42amax l)

private theorem r42_enc_eq (B : ℤ) : ∀ l : List ℤ,(r42enc B l : ℚ)=(toPoly l).eval (B:ℚ)
  | [] => by simp [r42enc,toPoly]
  | a :: l => by simp [r42enc,toPoly,r42_enc_eq B l]

private theorem r42_bal_eq {B c M : ℤ} (hc : -B≤2*c ∧ 2*c<B) : r42bal B (c+B*M)=c := by
  have hB : 0<B := by omega
  unfold r42bal
  rw [Int.add_mul_emod_self_left]
  rcases le_or_gt 0 c with h0|h0
  · rw [Int.emod_eq_of_lt h0 (by omega),ite_eq_left hc.2]
  · have e : c % B=c+B := by
      rw [show c=(c+B)+B*(-1) by ring,Int.add_mul_emod_self_left,Int.emod_eq_of_lt (by omega) (by omega)]
      ring
    rw [e,ite_eq_right (by omega)]
    ring

private theorem r42_dec_enc {B : ℤ} (hB : 0<B) : ∀ (n : ℕ) (c : List ℤ),c.length≤n →
    (∀ j,-B≤2*c.getD j 0 ∧ 2*c.getD j 0<B) → toPoly (r42dec B n (r42enc B c))=toPoly c
  | 0,c,hl,_ => by
    rw [List.length_eq_zero_iff.1 (by omega : c.length=0)]
    rfl
  | n+1,[],_,_ => by
    have h0 : r42bal B 0=0 := by
      simpa using r42_bal_eq (c:=0) (M:=0) (B:=B) (by omega)
    have ih : toPoly (r42dec B n 0)=0 := r42_dec_enc hB n [] (by simp) (fun j => by simp; omega)
    show toPoly (r42dec B (n+1) 0)=0
    rw [r42dec,h0,sub_zero,Int.zero_ediv]
    simp [toPoly,ih]
  | n+1,x :: c,hl,hb => by
    have hx := hb 0
    simp only [List.getD_cons_zero] at hx
    have h1 := r42_bal_eq (M:=r42enc B c) hx
    have h2 : (x+B*r42enc B c-x) / B=r42enc B c := by
      rw [add_sub_cancel_left,Int.mul_ediv_cancel_left _ hB.ne']
    have ih := r42_dec_enc hB n c (by simpa using hl) (fun j => by simpa using hb (j+1))
    simp only [r42enc,r42dec,h1,h2]
    rw [toPoly,toPoly,ih]

private theorem r42_getD_smul (c : ℤ) : ∀ (l : List ℤ) (j : ℕ),
    (Certificate.smul c l).getD j 0=c*l.getD j 0
  | [],j => by simp [Certificate.smul]
  | a :: l,0 => by simp [Certificate.smul]
  | a :: l,j+1 => by
    simp only [Certificate.smul,List.getD_cons_succ,r42_getD_smul c l j]

private theorem r42_getD_le_amax : ∀ (l : List ℤ) (j : ℕ),|l.getD j 0|≤r42amax l
  | [],j => by simp
  | a :: l,0 => by simp only [List.getD_cons_zero,r42amax]; push_cast; exact le_max_left _ _
  | a :: l,j+1 => by
    simp only [List.getD_cons_succ,r42amax]
    push_cast
    exact (r42_getD_le_amax l j).trans (le_max_right _ _)

private theorem r42_mul_bound : ∀ (a m : List ℤ) (j : ℕ),
    |(Certificate.mul a m).getD j 0|≤r42asum a*r42amax m
  | [],m,j => by simp [Certificate.mul]; positivity
  | a :: l,[],j => by simp [Certificate.mul]; positivity
  | a :: l,b :: m,j => by
    rw [Certificate.mul,Certificate.getD_add,
      r42_getD_smul]
    have h1 : |a*(b :: m).getD j 0|≤|a| * r42amax (b :: m) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (r42_getD_le_amax _ j) (abs_nonneg a)
    have h2 : |(0 :: Certificate.mul l (b :: m)).getD j 0|≤
        r42asum l*r42amax (b :: m) := by
      rcases j with _|j
      · simp only [List.getD_cons_zero,abs_zero]; positivity
      · simpa only [List.getD_cons_succ] using r42_mul_bound l (b :: m) j
    simp only [r42asum]
    push_cast
    calc _≤_ := abs_add_le _ _
      _≤_ := add_le_add h1 h2
      _=_ := by ring

private theorem r42_length_add : ∀ l m : List ℤ,
    (Certificate.add l m).length=max l.length m.length
  | [],m => by simp [Certificate.add]
  | a :: l,[] => by simp [Certificate.add]
  | a :: l,b :: m => by
    simp [Certificate.add,r42_length_add l m,Nat.succ_max_succ]

private theorem r42_length_smul (c : ℤ) : ∀ l : List ℤ,
    (Certificate.smul c l).length=l.length
  | [] => rfl
  | a :: l => by simp [Certificate.smul,r42_length_smul c l]

private theorem r42_length_mul : ∀ a m : List ℤ,
    (Certificate.mul a m).length≤a.length+m.length-1
  | [],m => by simp [Certificate.mul]
  | a :: l,[] => by simp [Certificate.mul]
  | a :: l,b :: m => by
    have ih := r42_length_mul l (b :: m)
    rw [Certificate.mul,r42_length_add,r42_length_smul]
    rcases l with _|⟨c,l⟩
    · simp [Certificate.mul]
    · simp only [List.length_cons] at ih ⊢
      omega

/-! ### Encoded sums and products

`r42K` holds the value `N` at a base `B` of an integer list of at most `n` entries, each of
absolute value at most `β`, that represents `s` times a polynomial.  Sums and products act on
`N` alone, so a whole expression costs a few integer operations; `toScaled` reads the list
back as balanced base-`B` digits once `B` exceeds `2β`. -/

private structure r42K where
  N : ℤ
  s : ℕ
  n : ℕ
  β : ℕ

private def r42K.Rep (B : ℤ) (k : r42K) (p : ℚ[X]) : Prop :=
  ∃ l : List ℤ,l.length≤k.n ∧ (∀ j,|l.getD j 0|≤k.β) ∧ k.N=r42enc B l ∧ toPoly l=C (k.s:ℚ)*p

private def r42K.add (a b : r42K) : r42K := ⟨a.N*b.s+b.N*a.s,a.s*b.s,max a.n b.n,a.β*b.s+b.β*a.s⟩
private def r42K.sub (a b : r42K) : r42K := ⟨a.N*b.s-b.N*a.s,a.s*b.s,max a.n b.n,a.β*b.s+b.β*a.s⟩
private def r42K.mul (a b : r42K) : r42K := ⟨a.N*b.N,a.s*b.s,a.n+b.n-1,a.n*a.β*b.β⟩
private def r42K.const (q : ℚ) : r42K := ⟨q.num,q.den,1,q.num.natAbs⟩
private def r42K.ofScaled (B : ℤ) (S : Scaled) : r42K := ⟨r42enc B S.l,S.s,S.l.length,r42amax S.l⟩
private def r42K.toScaled (B : ℤ) (k : r42K) : Scaled :=
  if 2*(k.β:ℤ)<B then ⟨r42dec B k.n k.N,k.s⟩ else ⟨[],0⟩

private theorem r42_enc_add (B : ℤ) (l m : List ℤ) :
    r42enc B (Certificate.add l m)=r42enc B l+r42enc B m := by
  have e : (r42enc B (Certificate.add l m) : ℚ)=r42enc B l+r42enc B m := by
    rw [r42_enc_eq,r42_enc_eq,r42_enc_eq,Certificate.toPoly_add,eval_add]
  exact_mod_cast e

private theorem r42_enc_smul (B c : ℤ) (l : List ℤ) :
    r42enc B (Certificate.smul c l)=c*r42enc B l := by
  have e : (r42enc B (Certificate.smul c l) : ℚ)=c*r42enc B l := by
    rw [r42_enc_eq,r42_enc_eq,Certificate.toPoly_smul,eval_mul,eval_C]
  exact_mod_cast e

private theorem r42_enc_mul (B : ℤ) (l m : List ℤ) :
    r42enc B (Certificate.mul l m)=r42enc B l*r42enc B m := by
  have e : (r42enc B (Certificate.mul l m) : ℚ)=r42enc B l*r42enc B m := by
    rw [r42_enc_eq,r42_enc_eq,r42_enc_eq,Certificate.toPoly_mul,eval_mul]
  exact_mod_cast e

private theorem r42_amax_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) : r42amax l≤β := by
  induction l generalizing β with
  | nil => simp [r42amax]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    exact max_le h0 h1

private theorem r42_asum_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) :
    r42asum l≤l.length*β := by
  induction l generalizing β with
  | nil => simp [r42asum]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    simp only [r42asum,List.length_cons]
    nlinarith

private theorem r42K.Rep.add {B : ℤ} {a b : r42K} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.add b).Rep B (p+q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨Certificate.add (Certificate.smul b.s la) (Certificate.smul a.s lb),?_,?_,?_,?_⟩
  · rw [r42_length_add,r42_length_smul,r42_length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [Certificate.getD_add,r42_getD_smul,r42_getD_smul]
    calc _≤|(b.s:ℤ)*la.getD j 0|+|(a.s:ℤ)*lb.getD j 0| := abs_add_le _ _
      _≤(b.s:ℤ)*a.β+(a.s:ℤ)*b.β := by
        rw [abs_mul,abs_mul,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by simp only [r42K.add]; push_cast; ring
  · simp only [r42K.add,r42_enc_add,r42_enc_smul,hNa,hNb]
    ring
  · simp only [r42K.add,Certificate.toPoly_add,Certificate.toPoly_smul,hpa,hpb,Int.cast_natCast,
      Nat.cast_mul,map_mul]
    ring

private theorem r42K.Rep.sub {B : ℤ} {a b : r42K} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.sub b).Rep B (p-q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨Certificate.add (Certificate.smul b.s la) (Certificate.smul (-(a.s:ℤ)) lb),?_,?_,?_,?_⟩
  · rw [r42_length_add,r42_length_smul,r42_length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [Certificate.getD_add,r42_getD_smul,r42_getD_smul]
    calc _≤|(b.s:ℤ)*la.getD j 0|+|(-(a.s:ℤ))*lb.getD j 0| := abs_add_le _ _
      _≤(b.s:ℤ)*a.β+(a.s:ℤ)*b.β := by
        rw [abs_mul,abs_mul,abs_neg,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by simp only [r42K.sub]; push_cast; ring
  · simp only [r42K.sub,r42_enc_add,r42_enc_smul,hNa,hNb]
    ring
  · simp only [r42K.sub,Certificate.toPoly_add,Certificate.toPoly_smul,hpa,hpb,Int.cast_natCast,
      Int.cast_neg,Nat.cast_mul,map_mul,map_neg]
    ring

private theorem r42K.Rep.mul {B : ℤ} {a b : r42K} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.mul b).Rep B (p*q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨Certificate.mul la lb,?_,?_,?_,?_⟩
  · have := r42_length_mul la lb
    simp only [r42K.mul]
    omega
  · intro j
    have h1 := r42_mul_bound la lb j
    have h2 : r42asum la*r42amax lb≤a.n*a.β*b.β :=
      Nat.mul_le_mul ((r42_asum_le hba).trans (Nat.mul_le_mul_right _ hla)) (r42_amax_le hbb)
    simp only [r42K.mul]
    calc _≤((r42asum la*r42amax lb:ℕ):ℤ) := by exact_mod_cast h1
      _≤_ := by exact_mod_cast h2
  · simp only [r42K.mul,r42_enc_mul,hNa,hNb]
  · simp only [r42K.mul,Certificate.toPoly_mul,hpa,hpb,Nat.cast_mul,map_mul]
    ring

private theorem r42K.rep_const (B : ℤ) (q : ℚ) : (r42K.const q).Rep B (C q) := by
  refine ⟨[q.num],by simp [r42K.const],fun j => ?_,by simp [r42K.const,r42enc],?_⟩
  · rcases j with _|j
    · simp only [List.getD_cons_zero,r42K.const]
      exact (Int.abs_eq_natAbs _).le
    · simp
  · simp only [r42K.const,toPoly,mul_zero,add_zero,← map_mul,Rat.den_mul_eq_num]

private theorem r42K.rep_ofScaled (B : ℤ) {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) :
    (r42K.ofScaled B S).Rep B p :=
  ⟨S.l,le_rfl,r42_getD_le_amax S.l,rfl,hS⟩

private theorem r42K.Rep.toScaled {B : ℤ} {k : r42K} {p : ℚ[X]} (hk : k.Rep B p) :
    (k.toScaled B).Rep p := by
  unfold r42K.toScaled
  split_ifs with h
  · obtain ⟨l,hl,hb,hN,hp⟩ := hk
    have hB : 0<B := lt_of_le_of_lt (by positivity) h
    show toPoly (r42dec B k.n k.N)=_
    rw [hN,r42_dec_enc hB _ _ hl (fun j => by obtain ⟨h1,h2⟩ := abs_le.1 (hb j); constructor <;> linarith)]
    exact hp
  · show toPoly []=C ((0:ℕ):ℚ)*p
    simp [toPoly]

/-! ### Products by Kronecker substitution

`Scaled.mul` multiplies entry by entry.  `kmul` evaluates both lists at an integer `B`,
multiplies the two values and reads the coefficients of the product back; `B` exceeds twice
the bound `n·max|aᵢ|·max|bⱼ|` on those coefficients. -/

/-- The base of `kmul`. -/
private def r42kmulB (a b : Scaled) : ℤ := 2*(a.l.length*r42amax a.l*r42amax b.l)+1
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.kmul
    (a b : Scaled) : Scaled :=
  ((r42K.ofScaled (r42kmulB a b) a).mul (r42K.ofScaled (r42kmulB a b) b)).toScaled (r42kmulB a b)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.kmul
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.kmul b).Rep (p*q) :=
  ((r42K.rep_ofScaled _ ha).mul (r42K.rep_ofScaled _ hb)).toScaled
/-- The square, by `kmul`. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.ksq
    (a : Scaled) : Scaled := a.kmul a
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.ksq
    {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.ksq.Rep (p^2) := by
  rw [sq]; exact ha.kmul ha

/-! ### Composition with `s+tX` by Kronecker substitution

The entries of the composition of `L` with `s+tX` are at most `Σ|Lᵢ| (|s|+|t|+1)^(n-1)`, so they
are the balanced base-`B` digits of the value of `L` at `s+tB` for `B` above twice that bound. -/

private theorem r42_asum_add : ∀ l m : List ℤ,
    r42asum (Certificate.add l m)≤r42asum l+r42asum m
  | [],m => by simp [Certificate.add,r42asum]
  | a :: l,[] => by simp [Certificate.add,r42asum]
  | a :: l,b :: m => by
    have ih := r42_asum_add l m
    have := Int.natAbs_add_le a b
    simp only [Certificate.add,r42asum]
    omega

private theorem r42_asum_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    r42asum (Certificate.affMulAux s t c z)≤
      s.natAbs*r42asum z+t.natAbs*c.natAbs+t.natAbs*r42asum z
  | c,[] => by simp [Certificate.affMulAux,r42asum,Int.natAbs_mul]
  | c,x :: z => by
    have ih := r42_asum_affMulAux s t x z
    have h1 := Int.natAbs_add_le (s*x) (t*c)
    simp only [Certificate.affMulAux,r42asum,Int.natAbs_mul] at h1 ⊢
    nlinarith

private theorem r42_asum_affMul (s t : ℤ) (z : List ℤ) :
    r42asum (Certificate.affMul s t z)≤(s.natAbs+t.natAbs)*r42asum z := by
  unfold Certificate.affMul
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    cases z with
    | nil => simp [Certificate.shiftMul,r42asum]
    | cons x z =>
      have := r42_asum_add (x :: z) (0 :: x :: z)
      simp only [Certificate.shiftMul]
      simp only [r42asum] at this ⊢
      simp
      omega
  · cases z with
    | nil => simp [Certificate.affMulGen,r42asum]
    | cons x z =>
      have := r42_asum_affMulAux s t x z
      simp only [Certificate.affMulGen,r42asum,Int.natAbs_mul]
      nlinarith

private theorem r42_asum_compAff (s t : ℤ) : ∀ l : List ℤ,
    r42asum (Certificate.compAff s t l)≤
      r42asum l*(s.natAbs+t.natAbs+1)^(l.length-1)
  | [] => by simp [Certificate.compAff,r42asum]
  | b :: l => by
    have h1 := r42_asum_add [b] (Certificate.affMul s t
      (Certificate.compAff s t l))
    have h2 := r42_asum_affMul s t (Certificate.compAff s t l)
    have hb : r42asum [b]=b.natAbs := by simp [r42asum]
    rw [Certificate.compAff]
    simp only [r42asum,List.length_cons,Nat.add_sub_cancel]
    rcases l with _|⟨c,l⟩
    · simp [Certificate.compAff,Certificate.affMul,
        Certificate.shiftMul,Certificate.affMulGen,
        Certificate.add,r42asum]
    · have ih := r42_asum_compAff s t (c :: l)
      generalize r42asum (Certificate.compAff s t (c :: l))=A at h1 h2 ih
      simp only [List.length_cons,Nat.add_sub_cancel] at ih ⊢
      have key : (s.natAbs+t.natAbs)*A≤r42asum (c :: l)*(s.natAbs+t.natAbs+1)^(l.length+1) :=
        calc (s.natAbs+t.natAbs)*A≤(s.natAbs+t.natAbs+1)*A := Nat.mul_le_mul_right _ (Nat.le_succ _)
          _≤(s.natAbs+t.natAbs+1)*(r42asum (c :: l)*(s.natAbs+t.natAbs+1)^l.length) :=
            Nat.mul_le_mul_left _ ih
          _=_ := by ring
      have hM : 1≤(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.one_le_pow _ _ (by omega)
      have hb' : b.natAbs≤b.natAbs*(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.le_mul_of_pos_right _ hM
      rw [hb] at h1
      rw [add_mul]
      omega

private theorem r42_getD_le_asum : ∀ (l : List ℤ) (j : ℕ),(l.getD j 0).natAbs≤r42asum l
  | [],j => by simp [r42asum]
  | a :: l,0 => by simp [r42asum]
  | a :: l,j+1 => by
    have := r42_getD_le_asum l j
    simp only [List.getD_cons_succ,r42asum]
    omega

private theorem r42_length_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    (Certificate.affMulAux s t c z).length=z.length+1
  | c,[] => rfl
  | c,x :: z => by
    simp [Certificate.affMulAux,r42_length_affMulAux s t x z]

private theorem r42_length_affMul (s t : ℤ) (z : List ℤ) :
    (Certificate.affMul s t z).length≤z.length+1 := by
  unfold Certificate.affMul
  split_ifs
  · cases z with
    | nil => simp [Certificate.shiftMul]
    | cons x z =>
      rw [Certificate.shiftMul,r42_length_add]
      simp
  · cases z with
    | nil => simp [Certificate.affMulGen]
    | cons x z =>
      simp [Certificate.affMulGen,r42_length_affMulAux]

private theorem r42_length_compAff (s t : ℤ) : ∀ l : List ℤ,
    (Certificate.compAff s t l).length≤l.length
  | [] => by simp [Certificate.compAff]
  | b :: l => by
    have ih := r42_length_compAff s t l
    have h := r42_length_affMul s t (Certificate.compAff s t l)
    rw [Certificate.compAff,r42_length_add]
    simp only [List.length_cons,List.length_nil]
    omega

private def r42kcenterWith (B s t : ℤ) (L : List ℤ) : List ℤ :=
  r42dec B L.length (r42enc (s+t*B) L)
/-- The composition of `L` with `s+tX`, by one evaluation at `s+tB`, read back in base
`B = 2 Σ|Lᵢ| (|s|+|t|+1)^(n-1) + 1`. -/
private def r42kcenterAux (s t : ℤ) (L : List ℤ) : List ℤ :=
  r42kcenterWith (2*(r42asum L*(s.natAbs+t.natAbs+1)^(L.length-1))+1) s t L

private theorem r42_toPoly_kcenterAux (s t : ℤ) (L : List ℤ) :
    toPoly (r42kcenterAux s t L)=toPoly (Certificate.compAff s t L) := by
  rw [r42kcenterAux,r42kcenterWith]
  generalize hB : (2*(r42asum L*(s.natAbs+t.natAbs+1)^(L.length-1))+1 : ℤ)=B
  have hB0 : 0<B := by rw [← hB]; positivity
  have he : r42enc (s+t*B) L=r42enc B (Certificate.compAff s t L) := by
    have e : (r42enc (s+t*B) L : ℚ)=(r42enc B (Certificate.compAff s t L) : ℚ) := by
      rw [r42_enc_eq,r42_enc_eq,Certificate.toPoly_compAff,eval_comp]
      simp
    exact_mod_cast e
  rw [he]
  apply r42_dec_enc hB0 _ _ (r42_length_compAff s t L)
  intro j
  have h1 := r42_getD_le_asum (Certificate.compAff s t L) j
  have h2 := r42_asum_compAff s t L
  have h3 : ((Certificate.compAff s t L).getD j 0).natAbs≤
      r42asum L*(s.natAbs+t.natAbs+1)^(L.length-1) := h1.trans h2
  have h4 : |(Certificate.compAff s t L).getD j 0|≤
      ((r42asum L*(s.natAbs+t.natAbs+1)^(L.length-1) : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h3
  obtain ⟨h5,h6⟩ := abs_le.1 h4
  push_cast at h5 h6 hB
  constructor <;> linarith

/-- `Scaled.center`, with the composition by `r42kcenterAux`. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.kcenter
    (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨r42kcenterAux s t (Certificate.prescale num den (c.l.length-1) 0 c.l),
    c.s*den^(c.l.length-1)⟩

private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.kcentered
    {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (c.kcenter num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  have h := hc.centered num den s t hden hm hh
  unfold Scaled.Rep at h ⊢
  show toPoly (r42kcenterAux s t _)=_
  rw [r42_toPoly_kcenterAux]
  exact h

/-! ### The numerators as scaled integer coefficient lists

Each polynomial of the companion is mirrored by a `Scaled` list built with the same
operations, and `Scaled.Rep` proves that the list represents it.  The kernel evaluates
only these integer lists. -/

/-- The monomial `X^k`. -/
private def r42mono (k : ℕ) : Scaled := ⟨List.replicate k 0++[1],1⟩
private theorem r42mono_rep (k : ℕ) : (r42mono k).Rep (X^k) := by
  unfold Scaled.Rep r42mono
  simp only [Nat.cast_one,map_one,one_mul]
  induction k with
  | zero => simp [toPoly]
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,toPoly,ih,pow_succ]
    simp only [Int.cast_zero,map_zero,zero_add]
    ring

private def r42S5 : Scaled :=
  (Scaled.var.subN ((Scaled.const (1/6)).mul (r42mono 3))).addN
    ((Scaled.const (1/120)).mul (r42mono 5))
private theorem r42S5_rep : r42S5.Rep S5 :=
  (Scaled.rep_var.subN ((Scaled.rep_const _).mul (r42mono_rep 3))).addN
    ((Scaled.rep_const _).mul (r42mono_rep 5))
private def r42S9 : Scaled :=
  (r42S5.subN ((Scaled.const (1/5040)).mul (r42mono 7))).addN
    ((Scaled.const (1/362880)).mul (r42mono 9))
private theorem r42S9_rep : r42S9.Rep S9 :=
  (r42S5_rep.subN ((Scaled.rep_const _).mul (r42mono_rep 7))).addN
    ((Scaled.rep_const _).mul (r42mono_rep 9))
private def r42S11 : Scaled := r42S9.subN ((Scaled.const (1/39916800)).mul (r42mono 11))
private theorem r42S11_rep : r42S11.Rep S11 :=
  r42S9_rep.subN ((Scaled.rep_const _).mul (r42mono_rep 11))
private def r42C4 : Scaled :=
  ((Scaled.ofNat 1).subN ((Scaled.const (1/2)).mul (r42mono 2))).addN
    ((Scaled.const (1/24)).mul (r42mono 4))
private theorem r42C4_rep : r42C4.Rep C4 :=
  (Scaled.rep_one.subN ((Scaled.rep_const _).mul (r42mono_rep 2))).addN
    ((Scaled.rep_const _).mul (r42mono_rep 4))
private def r42C10 : Scaled :=
  ((r42C4.subN ((Scaled.const (1/720)).mul (r42mono 6))).addN
    ((Scaled.const (1/40320)).mul (r42mono 8))).subN
    ((Scaled.const (1/3628800)).mul (r42mono 10))
private theorem r42C10_rep : r42C10.Rep C10 :=
  ((r42C4_rep.subN ((Scaled.rep_const _).mul (r42mono_rep 6))).addN
    ((Scaled.rep_const _).mul (r42mono_rep 8))).subN
    ((Scaled.rep_const _).mul (r42mono_rep 10))
private def r42C12 : Scaled := r42C10.addN ((Scaled.const (1/479001600)).mul (r42mono 12))
private theorem r42C12_rep : r42C12.Rep C12 :=
  r42C10_rep.addN ((Scaled.rep_const _).mul (r42mono_rep 12))

private theorem r42_rep_eq {S : Scaled} {p q : ℚ[X]} (e : q=p) (h : S.Rep q) : S.Rep p := e ▸ h

/-- `num3` on encoded lists, with `w = r1 r2`:
`2 A r0 w - R ((P0+r0²) w + ((P1+r1²) r2 + (P2+r2²) r1) r0)`. -/
private def r42num3K (A P0 P1 P2 r0 r1 r2 w : r42K) : r42K :=
  ((((r42K.const 2).mul A).mul r0).mul w).sub ((r42K.const Rbar).mul
    (((P0.add (r0.mul r0)).mul w).add
      ((((P1.add (r1.mul r1)).mul r2).add ((P2.add (r2.mul r2)).mul r1)).mul r0)))
private def r42num3B (B : ℤ) (A P0 P1 P2 r0 r1 r2 : Scaled) : r42K :=
  r42num3K (r42K.ofScaled B A) (r42K.ofScaled B P0) (r42K.ofScaled B P1) (r42K.ofScaled B P2)
    (r42K.ofScaled B r0) (r42K.ofScaled B r1) (r42K.ofScaled B r2)
    ((r42K.ofScaled B r1).mul (r42K.ofScaled B r2))
private def r42num3With (B : ℤ) (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  r42norm ((r42num3B B A P0 P1 P2 r0 r1 r2).toScaled B)
/-- `num3` of the lists, read back in a base above twice its coefficient bound. -/
private def r42num3 (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  r42num3With (2*(r42num3B 0 A P0 P1 P2 r0 r1 r2).β+1) A P0 P1 P2 r0 r1 r2
private theorem r42num3With_rep (B : ℤ) {A P0 P1 P2 r0 r1 r2 : Scaled}
    {a p0 p1 p2 s0 s1 s2 : ℚ[X]} (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1)
    (h2 : P2.Rep p2) (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (r42num3With B A P0 P1 P2 r0 r1 r2).Rep (num3 a p0 p1 p2 s0 s1 s2) := by
  have kA := r42K.rep_ofScaled B hA
  have k0 := r42K.rep_ofScaled B h0
  have k1 := r42K.rep_ofScaled B h1
  have k2 := r42K.rep_ofScaled B h2
  have j0 := r42K.rep_ofScaled B g0
  have j1 := r42K.rep_ofScaled B g1
  have j2 := r42K.rep_ofScaled B g2
  exact r42_rep_eq (by unfold num3; ring) (r42_rep_norm (r42K.Rep.toScaled
    (((((r42K.rep_const B 2).mul kA).mul j0).mul (j1.mul j2)).sub ((r42K.rep_const B Rbar).mul
      (((k0.add (j0.mul j0)).mul (j1.mul j2)).add
        ((((k1.add (j1.mul j1)).mul j2).add ((k2.add (j2.mul j2)).mul j1)).mul j0))))))
private theorem r42num3_rep {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 s0 s1 s2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (r42num3 A P0 P1 P2 r0 r1 r2).Rep (num3 a p0 p1 p2 s0 s1 s2) :=
  r42num3With_rep _ hA h0 h1 h2 g0 g1 g2

/-- `num4` on encoded lists, with `u = r0 r1` and `v = r2 r3`:
`2 A u v - R (((P0+r0²) r1 + (P1+r1²) r0) v + ((P2+r2²) r3 + (P3+r3²) r2) u)`. -/
private def r42num4K (A P0 P1 P2 P3 r0 r1 r2 r3 u v : r42K) : r42K :=
  ((((r42K.const 2).mul A).mul u).mul v).sub ((r42K.const Rbar).mul
    (((((P0.add (r0.mul r0)).mul r1).add ((P1.add (r1.mul r1)).mul r0)).mul v).add
      ((((P2.add (r2.mul r2)).mul r3).add ((P3.add (r3.mul r3)).mul r2)).mul u)))
private def r42num4B (B : ℤ) (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : r42K :=
  r42num4K (r42K.ofScaled B A) (r42K.ofScaled B P0) (r42K.ofScaled B P1) (r42K.ofScaled B P2)
    (r42K.ofScaled B P3) (r42K.ofScaled B r0) (r42K.ofScaled B r1) (r42K.ofScaled B r2)
    (r42K.ofScaled B r3) ((r42K.ofScaled B r0).mul (r42K.ofScaled B r1))
    ((r42K.ofScaled B r2).mul (r42K.ofScaled B r3))
private def r42num4With (B : ℤ) (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  r42norm ((r42num4B B A P0 P1 P2 P3 r0 r1 r2 r3).toScaled B)
/-- `num4` of the lists, read back in a base above twice its coefficient bound. -/
private def r42num4 (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  r42num4With (2*(r42num4B 0 A P0 P1 P2 P3 r0 r1 r2 r3).β+1) A P0 P1 P2 P3 r0 r1 r2 r3
private theorem r42num4With_rep (B : ℤ) {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (r42num4With B A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) := by
  have kA := r42K.rep_ofScaled B hA
  have k0 := r42K.rep_ofScaled B h0
  have k1 := r42K.rep_ofScaled B h1
  have k2 := r42K.rep_ofScaled B h2
  have k3 := r42K.rep_ofScaled B h3
  have j0 := r42K.rep_ofScaled B g0
  have j1 := r42K.rep_ofScaled B g1
  have j2 := r42K.rep_ofScaled B g2
  have j3 := r42K.rep_ofScaled B g3
  exact r42_rep_eq (by unfold num4; ring) (r42_rep_norm (r42K.Rep.toScaled
    (((((r42K.rep_const B 2).mul kA).mul (j0.mul j1)).mul (j2.mul j3)).sub
      ((r42K.rep_const B Rbar).mul
        (((((k0.add (j0.mul j0)).mul j1).add ((k1.add (j1.mul j1)).mul j0)).mul (j2.mul j3)).add
          ((((k2.add (j2.mul j2)).mul j3).add ((k3.add (j3.mul j3)).mul j2)).mul (j0.mul j1)))))))
private theorem r42num4_rep {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (r42num4 A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) :=
  r42num4With_rep _ hA h0 h1 h2 h3 g0 g1 g2 g3

private def r42t : Family → Scaled
  | .low => (Scaled.const split).subN Scaled.var
  | .high => Scaled.var.subN (Scaled.const split)
private theorem r42t_rep : ∀ f, (r42t f).Rep (t f)
  | .low => (Scaled.rep_const _).subN Scaled.rep_var
  | .high => Scaled.rep_var.subN (Scaled.rep_const _)

private def r42k : Family → Scaled
  | .low => (((Scaled.const (169/250)).subN ((Scaled.const (1/5)).mul (r42t .low))).addN
      ((Scaled.const (19/5)).mul ((r42t .low).pow 2))).subN
      ((Scaled.const 5).mul ((r42t .low).pow 3))
  | .high => (((Scaled.const (169/250)).addN ((Scaled.const (1/5)).mul (r42t .high))).addN
      ((Scaled.const (9/10)).mul ((r42t .high).pow 2))).subN
      ((Scaled.const (13/10)).mul ((r42t .high).pow 3))
private theorem r42k_rep : ∀ f, (r42k f).Rep (k f)
  | .low => (((Scaled.rep_const _).subN ((Scaled.rep_const _).mul (r42t_rep .low))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))).subN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 3))
  | .high => (((Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r42t_rep .high))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))).subN
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 3))

private def r42l : Family → Scaled
  | .low => ((((Scaled.const (41/40)).subN ((Scaled.const (1/4)).mul (r42t .low))).addN
      ((Scaled.const (29/2)).mul ((r42t .low).pow 2))).addN
      ((Scaled.const (55/4)).mul ((r42t .low).pow 3))).subN
      ((Scaled.const 200).mul ((r42t .low).pow 4))
  | .high => ((Scaled.const (41/40)).addN ((Scaled.const (11/50)).mul (r42t .high))).subN
      ((Scaled.const (3/10)).mul ((r42t .high).pow 2))
private theorem r42l_rep : ∀ f, (r42l f).Rep (l f)
  | .low => ((((Scaled.rep_const _).subN ((Scaled.rep_const _).mul (r42t_rep .low))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 3))).subN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 4))
  | .high => ((Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r42t_rep .high))).subN
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))

private def r42c : Family → Scaled
  | .low => ((Scaled.ofNat 1).addN ((Scaled.const (11/10)).mul (r42t .low))).addN
      ((Scaled.const 17).mul ((r42t .low).pow 2))
  | .high => ((Scaled.ofNat 1).subN ((Scaled.const (7/10)).mul (r42t .high))).addN
      ((Scaled.const (22/25)).mul ((r42t .high).pow 2))
private theorem r42c_rep : ∀ f, (r42c f).Rep (c f)
  | .low => (Scaled.rep_one.addN ((Scaled.rep_const _).mul (r42t_rep .low))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .low).pow 2))
  | .high => (Scaled.rep_one.subN ((Scaled.rep_const _).mul (r42t_rep .high))).addN
      ((Scaled.rep_const _).mul ((r42t_rep .high).pow 2))

private def r42mLo (f : Family) : Scaled := (r42c f).mul (r42C10.addN ((Scaled.const etaQ).mul r42S11))
private theorem r42mLo_rep (f : Family) : (r42mLo f).Rep (mLo f) :=
  (r42c_rep f).mul (r42C10_rep.addN ((Scaled.rep_const _).mul r42S11_rep))
private def r42mHi (f : Family) : Scaled := (r42c f).mul (r42C12.addN ((Scaled.const etaQ).mul r42S9))
private theorem r42mHi_rep (f : Family) : (r42mHi f).Rep (mHi f) :=
  (r42c_rep f).mul (r42C12_rep.addN ((Scaled.rep_const _).mul r42S9_rep))
private def r42mu (f : Family) : Scaled := (r42c f).mul (r42C4.addN ((Scaled.const etaQ).mul r42S5))
private theorem r42mu_rep (f : Family) : (r42mu f).Rep (mu f) :=
  (r42c_rep f).mul (r42C4_rep.addN ((Scaled.rep_const _).mul r42S5_rep))
private def r42widthLo : Scaled := (Scaled.const (1/2)).mul (((Scaled.ofNat 1).addN r42C10).addN r42S11)
private theorem r42widthLo_rep : r42widthLo.Rep widthLo :=
  (Scaled.rep_const _).mul ((Scaled.rep_one.addN r42C10_rep).addN r42S11_rep)

private def r42elemBase (f : Family) : Scaled :=
  ((((((Scaled.const 2).mul (r42k f)).addN ((Scaled.const 3).mul (r42l f))).addN
    ((Scaled.const (3/2)).mul (r42mLo f))).addN ((r42c f).mul r42widthLo)).addN
    (Scaled.const (5/2))).subN (((r42c f).mul (Scaled.const sigmabar)).mul r42S9)
private theorem r42elemBase_rep (f : Family) : (r42elemBase f).Rep
    (C 2*k f+C 3*l f+C (3/2)*mLo f+c f*widthLo+C (5/2)-c f*C sigmabar*S9) :=
  ((((((Scaled.rep_const _).mul (r42k_rep f)).addN ((Scaled.rep_const _).mul (r42l_rep f))).addN
    ((Scaled.rep_const _).mul (r42mLo_rep f))).addN ((r42c_rep f).mul r42widthLo_rep)).addN
    (Scaled.rep_const _)).subN (((r42c_rep f).mul (Scaled.rep_const _)).mul r42S9_rep)
private def r42elem : Family → Scaled
  | .low => (r42elemBase .low).addN (((Scaled.ofNat 1).addN (r42c .low)).neg.mul (Scaled.const cbar))
  | .high => (r42elemBase .high).addN ((Scaled.const (1/2)).mul ((Scaled.ofNat 1).addN (r42c .high)))
private theorem r42elem_rep : ∀ f, (r42elem f).Rep (elementary f)
  | .low => by
    rw [elementary,ite_eq_left_of_eq_true _ _ (eq_self _)]
    exact (r42elemBase_rep .low).addN ((Scaled.rep_one.addN (r42c_rep .low)).neg.mul (Scaled.rep_const _))
  | .high => by
    rw [elementary,ite_eq_right_of_eq_false _ _ (by decide)]
    exact (r42elemBase_rep .high).addN ((Scaled.rep_const _).mul (Scaled.rep_one.addN (r42c_rep .high)))

private def r42PH (f : Family) : Scaled := (Scaled.ofNat 1).addN ((r42k f).pow 2)
private theorem r42PH_rep (f : Family) : (r42PH f).Rep (PH f) := Scaled.rep_one.addN ((r42k_rep f).pow 2)
private def r42PG (f : Family) : Scaled := ((r42k f).pow 2).addN ((r42l f).pow 2)
private theorem r42PG_rep (f : Family) : (r42PG f).Rep (PG f) := ((r42k_rep f).pow 2).addN ((r42l_rep f).pow 2)
private def r42PB (f : Family) : Scaled := (r42mHi f).ksq.addN ((r42l f).pow 2)
private theorem r42PB_rep (f : Family) : (r42PB f).Rep (PB f) := (r42mHi_rep f).ksq.addN ((r42l_rep f).pow 2)
private def r42PD (f : Family) : Scaled := (Scaled.ofNat 1).addN ((r42c f).pow 2)
private theorem r42PD_rep (f : Family) : (r42PD f).Rep (PD f) := Scaled.rep_one.addN ((r42c_rep f).pow 2)
private def r42RH (f : Family) : Scaled := (Scaled.const (83/100)).addN ((Scaled.const (279/500)).mul (r42k f))
private theorem r42RH_rep (f : Family) : (r42RH f).Rep (RH f) :=
  (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r42k_rep f))
private def r42RG (f : Family) : Scaled :=
  ((Scaled.const (11/20)).mul (r42k f)).addN ((Scaled.const (167/200)).mul (r42l f))
private theorem r42RG_rep (f : Family) : (r42RG f).Rep (RG f) :=
  ((Scaled.rep_const _).mul (r42k_rep f)).addN ((Scaled.rep_const _).mul (r42l_rep f))
private def r42RB (f : Family) : Scaled :=
  ((Scaled.const (29/40)).mul (r42mu f)).addN ((Scaled.const (689/1000)).mul (r42l f))
private theorem r42RB_rep (f : Family) : (r42RB f).Rep (RB f) :=
  ((Scaled.rep_const _).mul (r42mu_rep f)).addN ((Scaled.rep_const _).mul (r42l_rep f))
private def r42RD (f : Family) : Scaled := (Scaled.const (7071/10000)).mul ((Scaled.ofNat 1).addN (r42c f))
private theorem r42RD_rep (f : Family) : (r42RD f).Rep (RD f) :=
  (Scaled.rep_const _).mul (Scaled.rep_one.addN (r42c_rep f))

private def r42AZ (f : Family) : Scaled :=
  ((r42C10.kmul ((r42elem f).subN (r42l f))).addN (r42l f)).addN
    (((Scaled.const (13/12)).mul (r42l f)).mul r42S11)
private theorem r42AZ_rep (f : Family) : (r42AZ f).Rep (AZ f) :=
  ((r42C10_rep.kmul ((r42elem_rep f).subN (r42l_rep f))).addN (r42l_rep f)).addN
    (((Scaled.rep_const _).mul (r42l_rep f)).mul r42S11_rep)

private def r42PHminus (f : Family) : Scaled :=
  (r42PH f).subN (((Scaled.const 2).mul (r42k f)).mul r42S11)
private theorem r42PHminus_rep (f : Family) : (r42PHminus f).Rep (PHminus f) :=
  (r42PH_rep f).subN (((Scaled.rep_const _).mul (r42k_rep f)).mul r42S11_rep)
private def r42PGminus (f : Family) : Scaled :=
  (r42PG f).subN ((((Scaled.const 2).mul (r42k f)).mul (r42l f)).mul r42S11)
private theorem r42PGminus_rep (f : Family) : (r42PGminus f).Rep (PGminus f) :=
  (r42PG_rep f).subN ((((Scaled.rep_const _).mul (r42k_rep f)).mul (r42l_rep f)).mul r42S11_rep)
private def r42PBminus (f : Family) : Scaled :=
  (r42PB f).subN ((((Scaled.const 2).mul (r42l f)).mul (r42mLo f)).kmul r42S11)
private theorem r42PBminus_rep (f : Family) : (r42PBminus f).Rep (PBminus f) :=
  (r42PB_rep f).subN ((((Scaled.rep_const _).mul (r42l_rep f)).mul (r42mLo_rep f)).kmul r42S11_rep)
private def r42RHminus (f : Family) : Scaled :=
  ((Scaled.const (179/200)).mul r42C4).addN ((Scaled.const (223/500)).mul ((r42k f).subN r42S5))
private theorem r42RHminus_rep (f : Family) : (r42RHminus f).Rep (RHminus f) :=
  ((Scaled.rep_const _).mul r42C4_rep).addN ((Scaled.rep_const _).mul ((r42k_rep f).subN r42S5_rep))
private def r42RGminus (f : Family) : Scaled :=
  (((Scaled.const (9/10)).mul (r42l f)).mul r42C4).addN
    ((Scaled.const (109/250)).mul ((r42k f).subN ((r42l f).mul r42S5)))
private theorem r42RGminus_rep (f : Family) : (r42RGminus f).Rep (RGminus f) :=
  (((Scaled.rep_const _).mul (r42l_rep f)).mul r42C4_rep).addN
    ((Scaled.rep_const _).mul ((r42k_rep f).subN ((r42l_rep f).mul r42S5_rep)))
private def r42RBminus (f : Family) : Scaled :=
  (((Scaled.const (94/125)).mul (r42l f)).mul r42C4).addN
    ((Scaled.const (33/50)).mul ((r42mu f).subN ((r42l f).mul r42S5)))
private theorem r42RBminus_rep (f : Family) : (r42RBminus f).Rep (RBminus f) :=
  (((Scaled.rep_const _).mul (r42l_rep f)).mul r42C4_rep).addN
    ((Scaled.rep_const _).mul ((r42mu_rep f).subN ((r42l_rep f).mul r42S5_rep)))
private def r42qStar (f : Family) : Scaled :=
  (r42l f).addN ((Scaled.const (3/100)).mul ((Scaled.const h).subN Scaled.var))
private theorem r42qStar_rep (f : Family) : (r42qStar f).Rep (qStar f) :=
  (r42l_rep f).addN ((Scaled.rep_const _).mul ((Scaled.rep_const _).subN Scaled.rep_var))

/-! Constants given by evaluating a represented polynomial at a rational point. -/

private theorem r42_rep_eval {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) : (S.kcenter num den s 0).Rep (C (p.eval a)) := by
  have hc := hp.kcentered num den s 0 (a:=a) (b:=a) hden (by rw [← ha]; ring) (by simp)
  have he : WholeIntervalPolynomial.centered a a p=C (p.eval a) := by
    rw [WholeIntervalPolynomial.centered,affine,sub_self,zero_div,map_zero,zero_mul,add_zero,
      add_self_div_two,comp_C]
  rwa [he] at hc
private theorem r42_rep_Cadd {S T : Scaled} {a b : ℚ} (hS : S.Rep (C a)) (hT : T.Rep (C b)) :
    (S.addN T).Rep (C (a+b)) := by rw [map_add]; exact hS.addN hT
private theorem r42_rep_Csub {S T : Scaled} {a b : ℚ} (hS : S.Rep (C a)) (hT : T.Rep (C b)) :
    (S.subN T).Rep (C (a-b)) := by rw [map_sub]; exact hS.subN hT
private theorem r42_rep_Cmul {S T : Scaled} {a b : ℚ} (hS : S.Rep (C a)) (hT : T.Rep (C b)) :
    (S.mul T).Rep (C (a*b)) := by rw [map_mul]; exact hS.mul hT
private theorem r42_rep_Cpow {S : Scaled} {a : ℚ} (hS : S.Rep (C a)) (n : ℕ) :
    (S.pow n).Rep (C (a^n)) := by rw [map_pow]; exact hS.pow n

/-- A represented constant, cut down to its constant entry. -/
private def r42head (S : Scaled) : Scaled := ⟨[S.l.getD 0 0],S.s⟩
private theorem r42head_rep {S : Scaled} {c : ℚ} (hS : S.Rep (C c)) : (r42head S).Rep (C c) := by
  unfold Scaled.Rep at *
  have h0 := congrArg (fun q => q.coeff 0) hS
  simp only [Certificate.coeff_toPoly,coeff_C_mul,coeff_C_zero] at h0
  simp only [r42head,Certificate.toPoly,mul_zero,add_zero,h0,map_mul]

private def r42ch : Scaled := r42head (r42C10.kcenter 7 10 1 0)
private theorem r42ch_rep : r42ch.Rep (C PositiveTD.Certificate.ch) :=
  r42head_rep <| r42_rep_eval r42C10_rep 7 10 1 (by norm_num) (by norm_num [h])
private def r42Ch : Scaled := r42head (r42C12.kcenter 7 10 1 0)
private theorem r42Ch_rep : r42Ch.Rep (C PositiveTD.Certificate.Ch) :=
  r42head_rep <| r42_rep_eval r42C12_rep 7 10 1 (by norm_num) (by norm_num [h])
private def r42sh : Scaled := r42head (r42S11.kcenter 7 10 1 0)
private theorem r42sh_rep : r42sh.Rep (C PositiveTD.Certificate.sh) :=
  r42head_rep <| r42_rep_eval r42S11_rep 7 10 1 (by norm_num) (by norm_num [h])

/-! The fourteen numerators. -/

private def r42NH : Family → Scaled
  | .low => r42num3 (((r42elem .low).addN r42C10).subN (Scaled.ofNat 1))
      (r42PG .low) (r42PB .low) (r42PHminus .low) (r42RG .low) (r42RB .low) (r42RHminus .low)
  | .high => r42num4 (((r42elem .high).addN r42C10).subN (Scaled.ofNat 1))
      (r42PG .high) (r42PB .high) (r42PHminus .high) (r42PD .high)
      (r42RG .high) (r42RB .high) (r42RHminus .high) (r42RD .high)
private theorem r42NH_rep : ∀ f, (r42NH f).Rep (NH f)
  | .low => by
    rw [NH,ite_eq_left_of_eq_true _ _ (eq_self _)]
    exact r42num3_rep (((r42elem_rep .low).addN r42C10_rep).subN Scaled.rep_one)
      (r42PG_rep .low) (r42PB_rep .low) (r42PHminus_rep .low) (r42RG_rep .low) (r42RB_rep .low)
      (r42RHminus_rep .low)
  | .high => by
    rw [NH,ite_eq_right_of_eq_false _ _ (by decide)]
    exact r42num4_rep (((r42elem_rep .high).addN r42C10_rep).subN Scaled.rep_one)
      (r42PG_rep .high) (r42PB_rep .high) (r42PHminus_rep .high) (r42PD_rep .high)
      (r42RG_rep .high) (r42RB_rep .high) (r42RHminus_rep .high) (r42RD_rep .high)

private def r42NG : Scaled :=
  r42num4 ((r42elem .high).addN ((r42l .high).mul (r42C10.subN (Scaled.ofNat 1))))
    (r42PH .high) (r42PB .high) (r42PGminus .high) (r42PD .high)
    (r42RH .high) (r42RB .high) (r42RGminus .high) (r42RD .high)
private theorem r42NG_rep : r42NG.Rep NG :=
  r42num4_rep ((r42elem_rep .high).addN ((r42l_rep .high).mul (r42C10_rep.subN Scaled.rep_one)))
    (r42PH_rep .high) (r42PB_rep .high) (r42PGminus_rep .high) (r42PD_rep .high)
    (r42RH_rep .high) (r42RB_rep .high) (r42RGminus_rep .high) (r42RD_rep .high)

private def r42NB : Scaled :=
  r42num4 ((r42elem .high).addN ((r42qStar .high).mul (r42C10.subN (Scaled.ofNat 1))))
    (r42PH .high) (r42PG .high) (r42PBminus .high) (r42PD .high)
    (r42RH .high) (r42RG .high) (r42RBminus .high) (r42RD .high)
private theorem r42NB_rep : r42NB.Rep NB :=
  r42num4_rep ((r42elem_rep .high).addN ((r42qStar_rep .high).mul (r42C10_rep.subN Scaled.rep_one)))
    (r42PH_rep .high) (r42PG_rep .high) (r42PBminus_rep .high) (r42PD_rep .high)
    (r42RH_rep .high) (r42RG_rep .high) (r42RBminus_rep .high) (r42RD_rep .high)

private def r42GAP0 (f : Family) : Scaled := r42C12.ksq.kmul (r42PH f)
private def r42GAP1 (f : Family) : Scaled := ((r42l f).pow 2).addN (((r42k f).pow 2).kmul r42C12.ksq)
private def r42GAP2 (f : Family) : Scaled := r42C12.ksq.kmul (r42PB f)
private def r42GAP3 (f : Family) : Scaled := r42C12.ksq.kmul (r42PD f)
private def r42GAR0 (f : Family) : Scaled := r42C4.mul (r42RH f)
private def r42GAR1 (f : Family) : Scaled :=
  ((Scaled.const (21/25)).mul (r42l f)).addN (((Scaled.const (543/1000)).mul (r42k f)).mul r42C4)
private def r42GAR2 (f : Family) : Scaled := r42C4.mul (r42RB f)
private def r42GAR3 (f : Family) : Scaled := r42C4.mul (r42RD f)
private theorem r42GAP0_rep (f : Family) : (r42GAP0 f).Rep (equalGAP f 0) :=
  r42C12_rep.ksq.kmul (r42PH_rep f)
private theorem r42GAP1_rep (f : Family) : (r42GAP1 f).Rep (equalGAP f 1) :=
  ((r42l_rep f).pow 2).addN (((r42k_rep f).pow 2).kmul r42C12_rep.ksq)
private theorem r42GAP2_rep (f : Family) : (r42GAP2 f).Rep (equalGAP f 2) :=
  r42C12_rep.ksq.kmul (r42PB_rep f)
private theorem r42GAP3_rep (f : Family) : (r42GAP3 f).Rep (equalGAP f 3) :=
  r42C12_rep.ksq.kmul (r42PD_rep f)
private theorem r42GAR0_rep (f : Family) : (r42GAR0 f).Rep (equalGAR f 0) := r42C4_rep.mul (r42RH_rep f)
private theorem r42GAR1_rep (f : Family) : (r42GAR1 f).Rep (equalGAR f 1) :=
  ((Scaled.rep_const _).mul (r42l_rep f)).addN (((Scaled.rep_const _).mul (r42k_rep f)).mul r42C4_rep)
private theorem r42GAR2_rep (f : Family) : (r42GAR2 f).Rep (equalGAR f 2) := r42C4_rep.mul (r42RB_rep f)
private theorem r42GAR3_rep (f : Family) : (r42GAR3 f).Rep (equalGAR f 3) := r42C4_rep.mul (r42RD_rep f)

private def r42NZ : Family → Scaled
  | .low => r42num3 (r42AZ .low) (r42GAP0 .low) (r42GAP1 .low) (r42GAP2 .low)
      (r42GAR0 .low) (r42GAR1 .low) (r42GAR2 .low)
  | .high => r42num4 (r42AZ .high) (r42GAP0 .high) (r42GAP1 .high) (r42GAP2 .high) (r42GAP3 .high)
      (r42GAR0 .high) (r42GAR1 .high) (r42GAR2 .high) (r42GAR3 .high)
private theorem r42NZ_rep : ∀ f, (r42NZ f).Rep (NZ f)
  | .low => by
    rw [NZ,ite_eq_left_of_eq_true _ _ (eq_self _)]
    exact r42num3_rep (r42AZ_rep .low) (r42GAP0_rep .low) (r42GAP1_rep .low) (r42GAP2_rep .low)
      (r42GAR0_rep .low) (r42GAR1_rep .low) (r42GAR2_rep .low)
  | .high => by
    rw [NZ,ite_eq_right_of_eq_false _ _ (by decide)]
    exact r42num4_rep (r42AZ_rep .high) (r42GAP0_rep .high) (r42GAP1_rep .high)
      (r42GAP2_rep .high) (r42GAP3_rep .high)
      (r42GAR0_rep .high) (r42GAR1_rep .high) (r42GAR2_rep .high) (r42GAR3_rep .high)

private def r42NZA : Scaled :=
  r42num4 (r42AZ .high) (r42GAP0 .high) (r42C12.ksq.kmul (r42PG .high))
    (((r42l .high).pow 2).addN ((r42mHi .high).ksq.kmul r42C12.ksq)) (r42GAP3 .high)
    (r42GAR0 .high) (r42C4.mul (r42RG .high))
    (((Scaled.const (4/5)).mul (r42l .high)).addN (((Scaled.const (3/5)).mul (r42mu .high)).mul r42C4))
    (r42GAR3 .high)
private theorem r42NZA_rep : r42NZA.Rep NZA :=
  r42num4_rep (r42AZ_rep .high) (r42GAP0_rep .high) (r42C12_rep.ksq.kmul (r42PG_rep .high))
    (((r42l_rep .high).pow 2).addN ((r42mHi_rep .high).ksq.kmul r42C12_rep.ksq))
    (r42GAP3_rep .high) (r42GAR0_rep .high) (r42C4_rep.mul (r42RG_rep .high))
    (((Scaled.rep_const _).mul (r42l_rep .high)).addN
      (((Scaled.rep_const _).mul (r42mu_rep .high)).mul r42C4_rep))
    (r42GAR3_rep .high)

private def r42phiLo : Scaled :=
  ((r42ch.addN r42sh).mul r42C10).subN ((r42Ch.subN r42sh).mul r42S9)
private theorem r42phiLo_rep : r42phiLo.Rep phiLo :=
  ((r42_rep_Cadd r42ch_rep r42sh_rep).mul r42C10_rep).subN ((r42_rep_Csub r42Ch_rep r42sh_rep).mul r42S9_rep)
private def r42chm1 : Scaled := r42ch.subN (Scaled.const 1)
private theorem r42chm1_rep : r42chm1.Rep (C (PositiveTD.Certificate.ch-1)) :=
  r42_rep_Csub r42ch_rep (Scaled.rep_const 1)

private def r42NM : Scaled :=
  r42num3 (((r42elem .low).addN ((r42k .low).mul (r42phiLo.subN (Scaled.ofNat 1)))).addN
      ((r42l .low).mul r42chm1))
    (r42PH .low) (r42PB .low) (r42PGminus .low) (r42RH .low) (r42RB .low) (r42RGminus .low)
private theorem r42NM_rep : r42NM.Rep NM :=
  r42num3_rep (((r42elem_rep .low).addN ((r42k_rep .low).mul (r42phiLo_rep.subN Scaled.rep_one))).addN
      ((r42l_rep .low).mul r42chm1_rep))
    (r42PH_rep .low) (r42PB_rep .low) (r42PGminus_rep .low) (r42RH_rep .low) (r42RB_rep .low)
    (r42RGminus_rep .low)

private def r42lowStar : Scaled :=
  (r42elem .low).subN (((Scaled.const (109/200)).mul ((r42mHi .low).addN
    ((Scaled.const (2/5)).mul Scaled.var))).mul ((Scaled.const h).subN Scaled.var))
private theorem r42lowStar_rep : r42lowStar.Rep lowStar :=
  (r42elem_rep .low).subN (((Scaled.rep_const _).mul ((r42mHi_rep .low).addN
    ((Scaled.rep_const _).mul Scaled.rep_var))).mul ((Scaled.rep_const _).subN Scaled.rep_var))
private def r42twosh : Scaled := (Scaled.const 2).mul r42sh
private theorem r42twosh_rep : r42twosh.Rep (C (2*PositiveTD.Certificate.sh)) :=
  r42_rep_Cmul (Scaled.rep_const 2) r42sh_rep
private def r42NSH : Scaled :=
  r42num3 (r42lowStar.addN r42chm1) (r42PG .low) (r42PB .low)
    ((r42PH .low).subN (r42twosh.mul (r42k .low))) (r42RG .low) (r42RB .low)
    (Scaled.const (77/100))
private theorem r42NSH_rep : r42NSH.Rep NSH :=
  r42num3_rep (r42lowStar_rep.addN r42chm1_rep) (r42PG_rep .low) (r42PB_rep .low)
    ((r42PH_rep .low).subN (r42twosh_rep.mul (r42k_rep .low))) (r42RG_rep .low) (r42RB_rep .low)
    (Scaled.rep_const _)
private def r42NSG : Scaled :=
  r42num3 (r42lowStar.addN ((r42l .low).mul r42chm1)) (r42PH .low) (r42PB .low)
    ((r42PG .low).subN ((r42twosh.mul (r42k .low)).mul (r42l .low))) (r42RH .low) (r42RB .low)
    ((Scaled.const (77/100)).mul (r42l .low))
private theorem r42NSG_rep : r42NSG.Rep NSG :=
  r42num3_rep (r42lowStar_rep.addN ((r42l_rep .low).mul r42chm1_rep)) (r42PH_rep .low) (r42PB_rep .low)
    ((r42PG_rep .low).subN ((r42twosh_rep.mul (r42k_rep .low)).mul (r42l_rep .low)))
    (r42RH_rep .low) (r42RB_rep .low) ((Scaled.rep_const _).mul (r42l_rep .low))

/-! The four angle cuts. -/

private def r42ang (e : Cut) (S : Scaled) : Scaled :=
  r42head (if cutAtG e then S.kcenter 1 4 1 0 else S.kcenter 19 50 1 0)
private theorem r42ang_rep (e : Cut) {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r42ang e S).Rep (C (p.eval (cutAngle e))) := by
  apply r42head_rep
  rcases hb : cutAtG e with _|_ <;> simp only [cutAngle,hb,Bool.false_eq_true,↓reduceIte]
  · exact r42_rep_eval hp 19 50 1 (by norm_num) (by norm_num)
  · exact r42_rep_eval hp 1 4 1 (by norm_num) (by norm_num)

private def r42gl (e : Cut) : Scaled := r42ang e r42C10
private def r42gh (e : Cut) : Scaled := r42ang e r42C12
private def r42tl (e : Cut) : Scaled := r42ang e r42S11
private def r42th (e : Cut) : Scaled := r42ang e r42S9
private def r42ga (e : Cut) : Scaled := r42ang e r42C4
private def r42ta (e : Cut) : Scaled := r42ang e r42S5
private theorem r42gl_rep (e : Cut) : (r42gl e).Rep (C (gammaLo e)) := r42ang_rep e r42C10_rep
private theorem r42gh_rep (e : Cut) : (r42gh e).Rep (C (gammaHi e)) := r42ang_rep e r42C12_rep
private theorem r42tl_rep (e : Cut) : (r42tl e).Rep (C (tauLo e)) := r42ang_rep e r42S11_rep
private theorem r42th_rep (e : Cut) : (r42th e).Rep (C (tauHi e)) := r42ang_rep e r42S9_rep
private theorem r42ga_rep (e : Cut) : (r42ga e).Rep (C (gammaApprox e)) := r42ang_rep e r42C4_rep
private theorem r42ta_rep (e : Cut) : (r42ta e).Rep (C (tauApprox e)) := r42ang_rep e r42S5_rep

private def r42cosLo (e : Cut) : Scaled := ((r42gl e).mul r42C10).addN ((r42tl e).mul r42S11)
private theorem r42cosLo_rep (e : Cut) : (r42cosLo e).Rep (thetaCosLo e) :=
  ((r42gl_rep e).mul r42C10_rep).addN ((r42tl_rep e).mul r42S11_rep)
private def r42sinLo (e : Cut) : Scaled := ((r42gl e).mul r42S11).subN ((r42th e).mul r42C12)
private theorem r42sinLo_rep (e : Cut) : (r42sinLo e).Rep (thetaSinLo e) :=
  ((r42gl_rep e).mul r42S11_rep).subN ((r42th_rep e).mul r42C12_rep)
private def r42cosAp (e : Cut) : Scaled := ((r42ga e).mul r42C4).addN ((r42ta e).mul r42S5)
private theorem r42cosAp_rep (e : Cut) : (r42cosAp e).Rep (thetaCosApprox e) :=
  ((r42ga_rep e).mul r42C4_rep).addN ((r42ta_rep e).mul r42S5_rep)
private def r42sinAp (e : Cut) : Scaled := ((r42ga e).mul r42S5).subN ((r42ta e).mul r42C4)
private theorem r42sinAp_rep (e : Cut) : (r42sinAp e).Rep (thetaSinApprox e) :=
  ((r42ga_rep e).mul r42S5_rep).subN ((r42ta_rep e).mul r42C4_rep)
private def r42theta (e : Cut) : Scaled := Scaled.var.subN (Scaled.const (cutAngle e))
private theorem r42theta_rep (e : Cut) : (r42theta e).Rep (theta e) :=
  Scaled.rep_var.subN (Scaled.rep_const _)

private def r42cutA (e : Cut) : Scaled :=
  ((((r42gl e).mul ((r42elem .high).subN (r42l .high))).addN (r42l .high)).addN
    (((Scaled.const (13/12)).mul (r42tl e)).mul (r42l .high))).addN
    (((r42gh e).mul (if cutRole e=0 then Scaled.ofNat 1 else r42l .high)).mul
      ((r42cosLo e).subN (Scaled.ofNat 1)))
private theorem r42cutA_rep (e : Cut) : (r42cutA e).Rep (cutA e) := by
  unfold r42cutA cutA
  by_cases hr : cutRole e=0
  · simp only [hr,↓reduceIte]
    exact ((((r42gl_rep e).mul ((r42elem_rep .high).subN (r42l_rep .high))).addN (r42l_rep .high)).addN
      ((r42_rep_Cmul (Scaled.rep_const _) (r42tl_rep e)).mul (r42l_rep .high))).addN
      (((r42gh_rep e).mul Scaled.rep_one).mul ((r42cosLo_rep e).subN Scaled.rep_one))
  · simp only [hr,↓reduceIte]
    exact ((((r42gl_rep e).mul ((r42elem_rep .high).subN (r42l_rep .high))).addN (r42l_rep .high)).addN
      ((r42_rep_Cmul (Scaled.rep_const _) (r42tl_rep e)).mul (r42l_rep .high))).addN
      (((r42gh_rep e).mul (r42l_rep .high)).mul ((r42cosLo_rep e).subN Scaled.rep_one))

private def r42gh2 (e : Cut) : Scaled := (r42gh e).pow 2
private theorem r42gh2_rep (e : Cut) : (r42gh2 e).Rep (C (gammaHi e)^2) := (r42gh_rep e).pow 2
private def r42gl2 (e : Cut) : Scaled := (Scaled.const 2).mul ((r42gl e).pow 2)
private theorem r42gl2_rep (e : Cut) : (r42gl2 e).Rep (C (2*gammaLo e^2)) :=
  r42_rep_Cmul (Scaled.rep_const 2) (r42_rep_Cpow (r42gl_rep e) 2)

-- the P and R entries
private def r42cP0 (e : Cut) : Scaled := (r42gh2 e).mul (r42PH .high)
private theorem r42cP0_rep (e : Cut) : (r42cP0 e).Rep (C (gammaHi e)^2*PH .high) :=
  (r42gh2_rep e).mul (r42PH_rep .high)
private def r42cP0u (e : Cut) : Scaled :=
  ((r42gh2 e).mul (r42PH .high)).subN (((r42gl2 e).mul (r42k .high)).mul (r42sinLo e))
private theorem r42cP0u_rep (e : Cut) : (r42cP0u e).Rep
    (C (gammaHi e)^2*PH .high-C (2*gammaLo e^2)*k .high*thetaSinLo e) :=
  ((r42gh2_rep e).mul (r42PH_rep .high)).subN (((r42gl2_rep e).mul (r42k_rep .high)).mul (r42sinLo_rep e))
private def r42cP1g (e : Cut) : Scaled := ((r42l .high).pow 2).addN ((r42gh2 e).mul ((r42k .high).pow 2))
private theorem r42cP1g_rep (e : Cut) : (r42cP1g e).Rep ((l .high)^2+C (gammaHi e)^2*(k .high)^2) :=
  ((r42l_rep .high).pow 2).addN ((r42gh2_rep e).mul ((r42k_rep .high).pow 2))
private def r42cP1a (e : Cut) : Scaled := (r42gh2 e).mul (r42PG .high)
private theorem r42cP1a_rep (e : Cut) : (r42cP1a e).Rep (C (gammaHi e)^2*PG .high) :=
  (r42gh2_rep e).mul (r42PG_rep .high)
private def r42cP1u (e : Cut) : Scaled :=
  ((r42gh2 e).mul (r42PG .high)).subN ((((r42gl2 e).mul (r42k .high)).mul (r42l .high)).mul (r42sinLo e))
private theorem r42cP1u_rep (e : Cut) : (r42cP1u e).Rep
    (C (gammaHi e)^2*PG .high-C (2*gammaLo e^2)*k .high*l .high*thetaSinLo e) :=
  ((r42gh2_rep e).mul (r42PG_rep .high)).subN
    ((((r42gl2_rep e).mul (r42k_rep .high)).mul (r42l_rep .high)).mul (r42sinLo_rep e))
private def r42cP2g (e : Cut) : Scaled := (r42gh2 e).mul (r42PB .high)
private theorem r42cP2g_rep (e : Cut) : (r42cP2g e).Rep (C (gammaHi e)^2*PB .high) :=
  (r42gh2_rep e).mul (r42PB_rep .high)
private def r42cP2a (e : Cut) : Scaled := ((r42l .high).pow 2).addN ((r42gh2 e).mul (r42mHi .high).ksq)
private theorem r42cP2a_rep (e : Cut) : (r42cP2a e).Rep ((l .high)^2+C (gammaHi e)^2*(mHi .high)^2) :=
  ((r42l_rep .high).pow 2).addN ((r42gh2_rep e).mul (r42mHi_rep .high).ksq)
private def r42cP2u (e : Cut) : Scaled :=
  ((r42gh2 e).mul (r42PB .high)).subN ((((r42gl2 e).mul (r42l .high)).mul (r42mLo .high)).mul (r42sinLo e))
private theorem r42cP2u_rep (e : Cut) : (r42cP2u e).Rep
    (C (gammaHi e)^2*PB .high-C (2*gammaLo e^2)*l .high*mLo .high*thetaSinLo e) :=
  ((r42gh2_rep e).mul (r42PB_rep .high)).subN
    ((((r42gl2_rep e).mul (r42l_rep .high)).mul (r42mLo_rep .high)).mul (r42sinLo_rep e))
private def r42cP3 (e : Cut) : Scaled := (r42gh2 e).mul (r42PD .high)
private theorem r42cP3_rep (e : Cut) : (r42cP3 e).Rep (C (gammaHi e)^2*PD .high) :=
  (r42gh2_rep e).mul (r42PD_rep .high)

private def r42cR0 (e : Cut) : Scaled := (r42ga e).mul (r42RH .high)
private theorem r42cR0_rep (e : Cut) : (r42cR0 e).Rep (C (gammaApprox e)*RH .high) :=
  (r42ga_rep e).mul (r42RH_rep .high)
private def r42cR0u (e : Cut) : Scaled :=
  (r42ga e).mul (((Scaled.const (87/100)).mul (r42cosAp e)).addN
    ((Scaled.const (493/1000)).mul ((r42k .high).subN (r42sinAp e))))
private theorem r42cR0u_rep (e : Cut) : (r42cR0u e).Rep (C (gammaApprox e)*
    (C (87/100)*thetaCosApprox e+C (493/1000)*(k .high-thetaSinApprox e))) :=
  (r42ga_rep e).mul (((Scaled.rep_const _).mul (r42cosAp_rep e)).addN
    ((Scaled.rep_const _).mul ((r42k_rep .high).subN (r42sinAp_rep e))))
private def r42cR1g (e : Cut) : Scaled :=
  ((Scaled.const (21/25)).mul (r42l .high)).addN
    (((Scaled.const (543/1000)).mul (r42ga e)).mul (r42k .high))
private theorem r42cR1g_rep (e : Cut) : (r42cR1g e).Rep
    (C (21/25)*l .high+C (543/1000*gammaApprox e)*k .high) :=
  ((Scaled.rep_const _).mul (r42l_rep .high)).addN
    ((r42_rep_Cmul (Scaled.rep_const _) (r42ga_rep e)).mul (r42k_rep .high))
private def r42cR1a (e : Cut) : Scaled := (r42ga e).mul (r42RG .high)
private theorem r42cR1a_rep (e : Cut) : (r42cR1a e).Rep (C (gammaApprox e)*RG .high) :=
  (r42ga_rep e).mul (r42RG_rep .high)
private def r42cR1u (e : Cut) : Scaled :=
  (r42ga e).mul ((((Scaled.const (9/10)).mul (r42l .high)).mul (r42cosAp e)).addN
    ((Scaled.const (109/250)).mul ((r42k .high).subN ((r42l .high).mul (r42sinAp e)))))
private theorem r42cR1u_rep (e : Cut) : (r42cR1u e).Rep (C (gammaApprox e)*
    (C (9/10)*l .high*thetaCosApprox e+C (109/250)*(k .high-l .high*thetaSinApprox e))) :=
  (r42ga_rep e).mul ((((Scaled.rep_const _).mul (r42l_rep .high)).mul (r42cosAp_rep e)).addN
    ((Scaled.rep_const _).mul ((r42k_rep .high).subN ((r42l_rep .high).mul (r42sinAp_rep e)))))
private def r42cR2g (e : Cut) : Scaled := (r42ga e).mul (r42RB .high)
private theorem r42cR2g_rep (e : Cut) : (r42cR2g e).Rep (C (gammaApprox e)*RB .high) :=
  (r42ga_rep e).mul (r42RB_rep .high)
private def r42cR2a (e : Cut) : Scaled :=
  ((Scaled.const (4/5)).mul (r42l .high)).addN (((Scaled.const (3/5)).mul (r42ga e)).mul (r42mu .high))
private theorem r42cR2a_rep (e : Cut) : (r42cR2a e).Rep
    (C (4/5)*l .high+C (3/5*gammaApprox e)*mu .high) :=
  ((Scaled.rep_const _).mul (r42l_rep .high)).addN
    ((r42_rep_Cmul (Scaled.rep_const _) (r42ga_rep e)).mul (r42mu_rep .high))
private def r42cR2u (e : Cut) : Scaled :=
  (r42ga e).mul (((((Scaled.const (357/500)).addN ((Scaled.const (11/20)).mul (r42theta e))).mul
      (r42l .high)).mul (r42cosAp e)).addN
    (((Scaled.const (7/10)).subN ((Scaled.const (41/50)).mul (r42theta e))).mul
      ((r42mu .high).subN ((r42l .high).mul (r42sinAp e)))))
private theorem r42cR2u_rep (e : Cut) : (r42cR2u e).Rep (C (gammaApprox e)*
    ((C (357/500)+C (11/20)*theta e)*l .high*thetaCosApprox e+
      (C (7/10)-C (41/50)*theta e)*(mu .high-l .high*thetaSinApprox e))) :=
  (r42ga_rep e).mul (((((Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r42theta_rep e))).mul
      (r42l_rep .high)).mul (r42cosAp_rep e)).addN
    (((Scaled.rep_const _).subN ((Scaled.rep_const _).mul (r42theta_rep e))).mul
      ((r42mu_rep .high).subN ((r42l_rep .high).mul (r42sinAp_rep e)))))
private def r42cR3 (e : Cut) : Scaled := (r42ga e).mul (r42RD .high)
private theorem r42cR3_rep (e : Cut) : (r42cR3 e).Rep (C (gammaApprox e)*RD .high) :=
  (r42ga_rep e).mul (r42RD_rep .high)

private def r42cutN : Cut → Scaled
  | .gaH => r42num4 (r42cutA .gaH) (r42cP0u .gaH) (r42cP1g .gaH) (r42cP2g .gaH) (r42cP3 .gaH)
      (r42cR0u .gaH) (r42cR1g .gaH) (r42cR2g .gaH) (r42cR3 .gaH)
  | .gaB => r42num4 (r42cutA .gaB) (r42cP0 .gaB) (r42cP1g .gaB) (r42cP2u .gaB) (r42cP3 .gaB)
      (r42cR0 .gaB) (r42cR1g .gaB) (r42cR2u .gaB) (r42cR3 .gaB)
  | .abG => r42num4 (r42cutA .abG) (r42cP0 .abG) (r42cP1u .abG) (r42cP2a .abG) (r42cP3 .abG)
      (r42cR0 .abG) (r42cR1u .abG) (r42cR2a .abG) (r42cR3 .abG)
  | .abH => r42num4 (r42cutA .abH) (r42cP0u .abH) (r42cP1a .abH) (r42cP2a .abH) (r42cP3 .abH)
      (r42cR0u .abH) (r42cR1a .abH) (r42cR2a .abH) (r42cR3 .abH)
private theorem r42cutN_rep : ∀ e, (r42cutN e).Rep (cutN e)
  | .gaH => r42num4_rep (r42cutA_rep .gaH) (r42cP0u_rep .gaH) (r42cP1g_rep .gaH) (r42cP2g_rep .gaH)
      (r42cP3_rep .gaH) (r42cR0u_rep .gaH) (r42cR1g_rep .gaH) (r42cR2g_rep .gaH) (r42cR3_rep .gaH)
  | .gaB => r42num4_rep (r42cutA_rep .gaB) (r42cP0_rep .gaB) (r42cP1g_rep .gaB) (r42cP2u_rep .gaB)
      (r42cP3_rep .gaB) (r42cR0_rep .gaB) (r42cR1g_rep .gaB) (r42cR2u_rep .gaB) (r42cR3_rep .gaB)
  | .abG => r42num4_rep (r42cutA_rep .abG) (r42cP0_rep .abG) (r42cP1u_rep .abG) (r42cP2a_rep .abG)
      (r42cP3_rep .abG) (r42cR0_rep .abG) (r42cR1u_rep .abG) (r42cR2a_rep .abG) (r42cR3_rep .abG)
  | .abH => r42num4_rep (r42cutA_rep .abH) (r42cP0u_rep .abH) (r42cP1a_rep .abH) (r42cP2a_rep .abH)
      (r42cP3_rep .abH) (r42cR0u_rep .abH) (r42cR1a_rep .abH) (r42cR2a_rep .abH) (r42cR3_rep .abH)

/-! Composition with affine maps. -/

private theorem r42_comp_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hab : (a+b)/2=num*s/den) (hba : (b-a)/2=num*t/den)
    {q : ℚ[X]} (hq : C ((a+b)/2)+C ((b-a)/2)*X=q) :
    (S.kcenter num den s t).Rep (p.comp q) := by
  have hc := hp.kcentered num den s t hden hab hba
  rwa [WholeIntervalPolynomial.centered,affine,hq] at hc

private theorem r42_flip_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (S.kcenter 1 5 1 (-5)).Rep (p.comp (C split-X)) :=
  r42_comp_rep hp 1 5 1 (-5) (a:=6/5) (b:=-4/5) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((6/5:ℚ)+-4/5)/2=split by norm_num [split],
      show ((-4/5:ℚ)-6/5)/2=-1 by norm_num,map_neg,map_one]; ring)

private theorem r42_shift_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.kcenter num den s t).Rep (p.comp (X+C a)) :=
  r42_comp_rep hp num den s t (a:=a-1) (b:=a+1) hden (by rw [← ha]; ring) (by rw [← h1]; ring)
    (by rw [show (a-1+(a+1))/2=a by ring,show (a+1-(a-1))/2=1 by ring,map_one,one_mul,add_comm])

private theorem r42_quot_eq (p : ℚ[X]) (a : ℚ) :
    (p-C (p.eval a)) /ₘ (X-C a)=(divX (p.comp (X+C a))).comp (X-C a) := by
  have h0 : (p.comp (X+C a)).coeff 0=p.eval a := by
    rw [coeff_zero_eq_eval_zero,eval_comp]; simp
  have h1 := X_mul_divX_add (p.comp (X+C a))
  have h2 : (p.comp (X+C a)).comp (X-C a)=p := by
    rw [comp_assoc]; simp
  have key : p-C (p.eval a)=(X-C a)*(divX (p.comp (X+C a))).comp (X-C a) := by
    have h3 := congrArg (fun q => q.comp (X-C a)) h1
    simp only [add_comp,mul_comp,X_comp,C_comp,h2,h0] at h3
    linear_combination (-1:ℚ[X])*h3
  rw [key,mul_divByMonic_cancel_left _ (monic_X_sub_C a)]

private theorem r42_quot_identity (p : ℚ[X]) (a : ℚ) :
    p=C (p.eval a)+(X-C a)*((p-C (p.eval a)) /ₘ (X-C a)) := by
  have hr : IsRoot (p-C (p.eval a)) a := by simp [IsRoot]
  rw [mul_divByMonic_eq_iff_isRoot.mpr hr]; ring

private theorem r42_centered_shift (r : ℚ[X]) (a b : ℚ) :
    centered a b (r.comp (X-C a))=centered 0 (b-a) r := by
  unfold WholeIntervalPolynomial.centered affine
  rw [comp_assoc]
  congr 1
  rw [sub_comp,X_comp,C_comp,show (0+(b-a))/2=(a+b)/2-a by ring,
    show (b-a-0)/2=(b-a)/2 by ring,map_sub]
  ring

/-! The low tails. -/

private def r42HFlip : Scaled := (r42NH .low).kcenter 1 5 1 (-5)
private theorem r42HFlip_rep : r42HFlip.Rep lowHFlip := r42_flip_rep (r42NH_rep .low)
private def r42HTail : Scaled := (r42HFlip.divX.divX.divX).kcenter 1 10 1 1
private theorem r42HTail_rep : r42HTail.Rep (centered 0 split lowHTail) :=
  r42HFlip_rep.divX.divX.divX.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])
private def r42ZFlip : Scaled := (r42NZ .low).kcenter 1 5 1 (-5)
private theorem r42ZFlip_rep : r42ZFlip.Rep lowZFlip := r42_flip_rep (r42NZ_rep .low)
private def r42ZTail : Scaled := (r42ZFlip.divX.divX).kcenter 1 10 1 1
private theorem r42ZTail_rep : r42ZTail.Rep (centered 0 split lowZTail) :=
  r42ZFlip_rep.divX.divX.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])



private lemma r42_icc {a b : ℚ} {a' b' z : ℝ} (ha : (a:ℝ)=a') (hb : (b:ℝ)=b')
    (hz : z∈Set.Icc a' b') : z∈Set.Icc (a:ℝ) (b:ℝ) := by
  rw [ha,hb]; exact hz

private lemma r42_flip {u z : ℝ} (hu : u=1/5-z) (p : ℚ[X]) :
    aeval u (p.comp (C split-X))=aeval z p := by
  rw [aeval_comp]
  congr 1
  simp only [map_sub,aeval_C,aeval_X,eq_ratCast,split,hu]
  push_cast
  ring_nf

private lemma r42_cast_lt {a b : ℚ} (h : a<b) : (a:ℝ)<(b:ℝ) := Rat.cast_lt.mpr h

/-! ### Integer checks

Each statement below is one kernel evaluation of a few integer conditions on the lists. -/

/-- `ρ` is below the `i`-th coefficient of the polynomial represented by `S`, in integers. -/
private abbrev r42CoeffOK (S : Scaled) (ρ : ℚ) (i : ℕ) : Prop :=
  S.s≠0 ∧ ρ.num*S.s<ρ.den*S.l.getD i 0

/-- The list of `c` fits degree `D`, and `ρ` is below the coefficient-norm bound, in integers. -/
private abbrev r42BoundOK (c : Scaled) (D : ℕ) (ρ : ℚ) : Prop :=
  c.s≠0 ∧ c.l.length≤D+1 ∧
    ρ.num*(c.s*2^c.l.length)<2*ρ.den*lowerZ D (fun j => (chebList c.l).getD j 0)

/-- `0 < b 2` and `ρ` below `quadraticReserve b count` for the degree-`D` Chebyshev coefficients
`b` of the polynomial represented by `c`, in integers. -/
private abbrev r42QuadOK (c : Scaled) (D count : ℕ) (ρ : ℚ) : Prop :=
  c.s≠0 ∧ c.l.length≤D+1 ∧ 0<(chebList c.l).getD 2 0 ∧
    ρ.num*(8*(chebList c.l).getD 2 0*(c.s*2^c.l.length))<
      2*ρ.den*(8*(chebList c.l).getD 2 0*((chebList c.l).getD 0 0-(chebList c.l).getD 2 0-
        ∑ j : Fin count,|(chebList c.l).getD (j.val+3) 0|)-(chebList c.l).getD 1 0^2)

private theorem r42_coeff_lt {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) {ρ : ℚ} {i : ℕ}
    (h : r42CoeffOK S ρ i) : ρ<p.coeff i := by
  obtain ⟨hs,hlt⟩ := h
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  have hc : ((ρ.num*S.s:ℤ):ℚ)<((ρ.den*S.l.getD i 0:ℤ):ℚ) := by exact_mod_cast hlt
  push_cast at hc
  rw [hS.coeff hs,lt_div_iff₀ hs',← Rat.num_div_den ρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

private theorem r42_bound {c : Scaled} {a b : ℚ} {p : ℚ[X]} (hc : c.Rep (centered a b p))
    {D : ℕ} {ρ : ℚ} (h : r42BoundOK c D ρ) :
    centered a b p=expansion D (centered a b p) ∧ ρ<lowerOn D a b p := by
  obtain ⟨hs,hl,hlt⟩ := h
  refine ⟨hc.eq_expansion hs hl,?_⟩
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  have hc' : ((ρ.num*(c.s*2^c.l.length):ℤ):ℚ)<
      ((2*ρ.den*lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ) := by exact_mod_cast hlt
  push_cast at hc'
  rw [lowerOn_eq_of_rep hc hs hl,lt_div_iff₀ (scale_pos hs),← Rat.num_div_den ρ,
    div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

private theorem r42_quad {c : Scaled} {a b : ℚ} {p : ℚ[X]} (hc : c.Rep (centered a b p))
    {D count : ℕ} {ρ : ℚ} (h : r42QuadOK c D count ρ) :
    centered a b p=expansion D (centered a b p) ∧ 0<coefficient D (centered a b p) 2 ∧
      ρ<quadraticReserve (coefficient D (centered a b p)) count := by
  obtain ⟨hs,hl,h2,hlt⟩ := h
  refine ⟨hc.eq_expansion hs hl,?_⟩
  rw [Certificate.coefficient_centered_eq hc hs hl]
  have hK := scale_pos hs
  have hd : (0:ℚ)<ρ.den := by exact_mod_cast ρ.den_pos
  have hB2 : (0:ℚ)<((chebList c.l).getD 2 0:ℤ) := by exact_mod_cast h2
  have e2 : (c.s:ℚ)*2^c.l.length=2*(c.s*2^c.l.length/2) := by ring
  generalize (c.s:ℚ)*2^c.l.length/2=K at hK e2
  have htail : tailNorm (fun j => ((chebList c.l).getD j 0:ℚ)/K) 3 count=
      ((∑ j : Fin count,|(chebList c.l).getD (j.val+3) 0|:ℤ):ℚ)/K := by
    unfold tailNorm
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [abs_div,abs_of_pos hK]
  refine ⟨div_pos hB2 hK,?_⟩
  unfold quadraticReserve
  rw [htail]
  beta_reduce
  push_cast
  have hc' := (Int.cast_lt (R:=ℚ)).2 hlt
  push_cast at hc'
  rw [e2] at hc'
  generalize ((chebList c.l).getD 0 0:ℚ)=B0 at hc' ⊢
  generalize ((chebList c.l).getD 1 0:ℚ)=B1 at hc' ⊢
  generalize ((chebList c.l).getD 2 0:ℚ)=B2 at hc' hB2 ⊢
  generalize (∑ j : Fin count,(|(chebList c.l).getD (j.val+3) 0|:ℚ))=T at hc' ⊢
  have key : B0/K-B2/K-(B1/K)^2/(8*(B2/K))-T/K=(8*B2*(B0-B2-T)-B1^2)/(8*B2*K) := by
    field_simp
    ring
  rw [key,lt_div_iff₀ (by positivity),← Rat.num_div_den ρ,div_mul_eq_mul_div,div_lt_iff₀ hd]
  linarith

theorem low_H_identity : lowHFlip=C (lowHFlip.coeff 0)+C (lowHFlip.coeff 1)*X+
    C (lowHFlip.coeff 2)*X^2+X^3*lowHTail := by
  have e1 := X_mul_divX_add lowHFlip
  have e2 := X_mul_divX_add lowHFlip.divX
  have e3 := X_mul_divX_add lowHFlip.divX.divX
  norm_num only [coeff_divX] at e2 e3
  rw [lowHTail]
  linear_combination (-1:ℚ[X])*e1+(-X)*e2+(-X^2)*e3

private theorem r42_low_H_check : r42CoeffOK r42HFlip (161/100000) 0 ∧
    r42CoeffOK r42HFlip (-173/5000) 1 ∧ r42CoeffOK r42HFlip (-191/500) 2 ∧
    r42BoundOK r42HTail 34 (158/5) := by
  decide +kernel

theorem low_H_coefficients :
    (161/100000:ℚ)<lowHFlip.coeff 0 ∧
    (-173/5000:ℚ)<lowHFlip.coeff 1 ∧
    (-191/500:ℚ)<lowHFlip.coeff 2 :=
  ⟨r42_coeff_lt r42HFlip_rep r42_low_H_check.1,r42_coeff_lt r42HFlip_rep r42_low_H_check.2.1,
    r42_coeff_lt r42HFlip_rep r42_low_H_check.2.2.1⟩

theorem low_H_tail_expansion : centered 0 split lowHTail=
    expansion 34 (centered 0 split lowHTail) :=
  (r42_bound r42HTail_rep r42_low_H_check.2.2.2).1

theorem low_H_tail_reserve : (158/5:ℚ)<lowerOn 34 0 split lowHTail :=
  (r42_bound r42HTail_rep r42_low_H_check.2.2.2).2

theorem low_H_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (97/100000:ℝ)<aeval z (NH .low) := by
  obtain ⟨u,hu_def⟩ : ∃ u : ℝ,u=1/5-z := ⟨_,rfl⟩
  have hu : u∈Set.Icc ((0:ℚ):ℝ) ((split:ℚ):ℝ) :=
    r42_icc (a':=0) (b':=1/5) (by norm_num) (by norm_num [split])
      ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hu0 : 0≤u := by linarith [hz.2]
  have ht := positive_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_H_tail_expansion low_H_tail_reserve hu
  have h0 : (161/100000:ℝ)<(lowHFlip.coeff 0:ℝ) := by
    have hc := r42_cast_lt low_H_coefficients.1
    push_cast at hc
    exact hc
  have h1 : (-173/5000:ℝ)<(lowHFlip.coeff 1:ℝ) := by
    have hc := r42_cast_lt low_H_coefficients.2.1
    push_cast at hc
    exact hc
  have h2 : (-191/500:ℝ)<(lowHFlip.coeff 2:ℝ) := by
    have hc := r42_cast_lt low_H_coefficients.2.2
    push_cast at hc
    exact hc
  have he := congrArg (fun p : ℚ[X] => aeval u p) low_H_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hrefl : aeval u lowHFlip=aeval z (NH .low) := r42_flip hu_def _
  rw [hrefl] at he
  have hlinear := mul_le_mul_of_nonneg_right h1.le hu0
  have hquadratic := mul_le_mul_of_nonneg_right h2.le (sq_nonneg u)
  have hcubic := mul_le_mul_of_nonneg_left ht.le (pow_nonneg hu0 3)
  have hretained := mul_nonneg hu0 (sq_nonneg (u-1/50))
  have hcomplete := sq_nonneg (u-(1181/25000)/(2*(441/500)))
  norm_num at ht hcubic
  linarith

theorem low_Z_identity : lowZFlip=C (lowZFlip.coeff 0)+C (lowZFlip.coeff 1)*X+
    X^2*lowZTail := by
  have e1 := X_mul_divX_add lowZFlip
  have e2 := X_mul_divX_add lowZFlip.divX
  norm_num only [coeff_divX] at e2
  rw [lowZTail]
  linear_combination (-1:ℚ[X])*e1+(-X)*e2

private theorem r42_low_Z_check : r42CoeffOK r42ZFlip (753/500000) 0 ∧
    r42CoeffOK r42ZFlip (-987/10000) 1 ∧ r42BoundOK r42ZTail 64 (77/10) := by
  decide +kernel

theorem low_Z_coefficients :
    (753/500000:ℚ)<lowZFlip.coeff 0 ∧
    (-987/10000:ℚ)<lowZFlip.coeff 1 :=
  ⟨r42_coeff_lt r42ZFlip_rep r42_low_Z_check.1,r42_coeff_lt r42ZFlip_rep r42_low_Z_check.2.1⟩

theorem low_Z_tail_expansion : centered 0 split lowZTail=
    expansion 64 (centered 0 split lowZTail) :=
  (r42_bound r42ZTail_rep r42_low_Z_check.2.2).1

theorem low_Z_tail_reserve : (77/10:ℚ)<lowerOn 64 0 split lowZTail :=
  (r42_bound r42ZTail_rep r42_low_Z_check.2.2).2

theorem low_Z_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (59/50000:ℝ)<aeval z (NZ .low) := by
  obtain ⟨u,hu_def⟩ : ∃ u : ℝ,u=1/5-z := ⟨_,rfl⟩
  have hu : u∈Set.Icc ((0:ℚ):ℝ) ((split:ℚ):ℝ) :=
    r42_icc (a':=0) (b':=1/5) (by norm_num) (by norm_num [split])
      ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hu0 : 0≤u := by linarith [hz.2]
  have ht := positive_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_Z_tail_expansion low_Z_tail_reserve hu
  have h0 : (753/500000:ℝ)<(lowZFlip.coeff 0:ℝ) := by
    have hc := r42_cast_lt low_Z_coefficients.1
    push_cast at hc
    exact hc
  have h1 : (-987/10000:ℝ)<(lowZFlip.coeff 1:ℝ) := by
    have hc := r42_cast_lt low_Z_coefficients.2
    push_cast at hc
    exact hc
  have he := congrArg (fun p : ℚ[X] => aeval u p) low_Z_identity
  simp only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast] at he
  have hrefl : aeval u lowZFlip=aeval z (NZ .low) := r42_flip hu_def _
  rw [hrefl] at he
  have hlinear := mul_le_mul_of_nonneg_right h1.le hu0
  have hquadratic := mul_le_mul_of_nonneg_left ht.le (sq_nonneg u)
  have hcomplete := sq_nonneg (u-(987/10000)/(2*(77/10)))
  norm_num at ht hquadratic
  linarith

def mixedCoefficient : ℕ→ℚ := coefficient 40 (centered 0 split NM)

private def r42NMc : Scaled := r42NM.kcenter 1 10 1 1
private theorem r42NMc_rep : r42NMc.Rep (centered 0 split NM) :=
  r42NM_rep.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])
private theorem r42_mixed_check : r42QuadOK r42NMc 40 38 (153/5000) := by decide +kernel

theorem low_mixed_identity : centered 0 split NM=
    C (mixedCoefficient 0-mixedCoefficient 2)+C (mixedCoefficient 1)*X+
      C (2*mixedCoefficient 2)*X^2+tail mixedCoefficient 3 38 := by
  rw [(r42_quad r42NMc_rep r42_mixed_check).1]
  change series 40 mixedCoefficient=_
  rw [series,tail,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,Nat.cast_zero,
    zero_add]
  have hrest : ∀ j : Fin 38,C (mixedCoefficient (j.val+1+1+1))*
      Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+1+1+1)=
      C (mixedCoefficient (j.val+3))*Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+3) := fun j => by
    ring_nf
  simp only [hrest,Polynomial.Chebyshev.T_one,show (1:ℕ)+1=2 from rfl,show (1:ℤ)+1=2 by norm_num,
    Polynomial.Chebyshev.T_two,map_sub,map_mul,map_ofNat]
  ring

theorem low_mixed_reserve : 0< mixedCoefficient 2 ∧
    (153/5000:ℚ)<quadraticReserve mixedCoefficient 38 :=
  (r42_quad r42NMc_rep r42_mixed_check).2

theorem low_M_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    (153/5000:ℝ)<aeval z NM := by
  have hb := quadratic_on_interval (by norm_num [split] : (0:ℚ)<split)
    low_mixed_identity low_mixed_reserve.1
    (r42_icc (by norm_num) (by norm_num [split]) hz)
  have hr : (153/5000:ℝ)<(quadraticReserve mixedCoefficient 38:ℝ) := by
    have hc := r42_cast_lt low_mixed_reserve.2
    push_cast at hc
    exact hc
  exact hr.trans_le hb

/-- The eight direct coefficient-norm certificates in the companion. -/
inductive Direct where
  | lowSH | lowSG | highB | highZ | highZA | cutGAB | cutABG | cutABH
  deriving DecidableEq

instance : Fintype Direct where
  elems := {.lowSH, .lowSG, .highB, .highZ, .highZA, .cutGAB, .cutABG, .cutABH}
  complete x := by cases x <;> decide
def directPolynomial : Direct→ℚ[X]
  | .lowSH => NSH | .lowSG => NSG | .highB => NB | .highZ => NZ .high
  | .highZA => NZA | .cutGAB => cutN .gaB | .cutABG => cutN .abG | .cutABH => cutN .abH
def directDegree : Direct→ℕ
  | .lowSH => 32 | .lowSG => 35 | .highB => 36 | .highZ => 72
  | .highZA => 72 | .cutGAB => 36 | .cutABG => 40 | .cutABH => 38
def directLeft : Direct→ℚ
  | .lowSH => 0 | .lowSG => 0 | .highB => split | .highZ => split
  | .highZA => split | .cutGAB => 1/4 | .cutABG => 19/50 | .cutABH => 19/50
def directRight : Direct→ℚ | .lowSH => split | .lowSG => split | _ => h
def directReserve : Direct→ℚ
  | .lowSH => 231/1250 | .lowSG => 157/5000 | .highB => 1/200
  | .highZ => 91/50000 | .highZA => 51/12500 | .cutGAB => 21/3125
  | .cutABG => 107/2000 | .cutABH => 111/2000

/-! Per-case certificates of the direct coefficient norms. -/

private def r42c_lowSH : Scaled := r42NSH.kcenter 1 10 1 1
private theorem r42c_lowSH_rep : r42c_lowSH.Rep (centered 0 split NSH) :=
  r42NSH_rep.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])
private theorem r42_lowSH_check : r42BoundOK r42c_lowSH 32 (231/1250) := by decide +kernel

private def r42c_lowSG : Scaled := r42NSG.kcenter 1 10 1 1
private theorem r42c_lowSG_rep : r42c_lowSG.Rep (centered 0 split NSG) :=
  r42NSG_rep.kcentered 1 10 1 1 (by norm_num) (by norm_num [split]) (by norm_num [split])
private theorem r42_lowSG_check : r42BoundOK r42c_lowSG 35 (157/5000) := by decide +kernel

private def r42c_highB : Scaled := r42NB.kcenter 1 20 9 5
private theorem r42c_highB_rep : r42c_highB.Rep (centered split h NB) :=
  r42NB_rep.kcentered 1 20 9 5 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highB_check : r42BoundOK r42c_highB 36 (1/200) := by decide +kernel

private def r42c_highZ : Scaled := (r42NZ .high).kcenter 1 20 9 5
private theorem r42c_highZ_rep : r42c_highZ.Rep (centered split h (NZ .high)) :=
  (r42NZ_rep .high).kcentered 1 20 9 5 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highZ_check : r42BoundOK r42c_highZ 72 (91/50000) := by decide +kernel

private def r42c_highZA : Scaled := r42NZA.kcenter 1 20 9 5
private theorem r42c_highZA_rep : r42c_highZA.Rep (centered split h NZA) :=
  r42NZA_rep.kcentered 1 20 9 5 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highZA_check : r42BoundOK r42c_highZA 72 (51/12500) := by decide +kernel

private def r42c_cutGAB : Scaled := (r42cutN .gaB).kcenter 1 40 19 9
private theorem r42c_cutGAB_rep : r42c_cutGAB.Rep (centered (1/4) h (cutN .gaB)) :=
  (r42cutN_rep .gaB).kcentered 1 40 19 9 (by norm_num) (by norm_num [h]) (by norm_num [h])
private theorem r42_cutGAB_check : r42BoundOK r42c_cutGAB 36 (21/3125) := by decide +kernel

private def r42c_cutABG : Scaled := (r42cutN .abG).kcenter 1 50 27 8
private theorem r42c_cutABG_rep : r42c_cutABG.Rep (centered (19/50) h (cutN .abG)) :=
  (r42cutN_rep .abG).kcentered 1 50 27 8 (by norm_num) (by norm_num [h]) (by norm_num [h])
private theorem r42_cutABG_check : r42BoundOK r42c_cutABG 40 (107/2000) := by decide +kernel

private def r42c_cutABH : Scaled := (r42cutN .abH).kcenter 1 50 27 8
private theorem r42c_cutABH_rep : r42c_cutABH.Rep (centered (19/50) h (cutN .abH)) :=
  (r42cutN_rep .abH).kcentered 1 50 27 8 (by norm_num) (by norm_num [h]) (by norm_num [h])
private theorem r42_cutABH_check : r42BoundOK r42c_cutABH 38 (111/2000) := by decide +kernel

theorem direct_expansion (e : Direct) :
    centered (directLeft e) (directRight e) (directPolynomial e)=
      expansion (directDegree e)
        (centered (directLeft e) (directRight e) (directPolynomial e)) := by
  cases e
  exacts [(r42_bound r42c_lowSH_rep r42_lowSH_check).1,
    (r42_bound r42c_lowSG_rep r42_lowSG_check).1,
    (r42_bound r42c_highB_rep r42_highB_check).1,
    (r42_bound r42c_highZ_rep r42_highZ_check).1,
    (r42_bound r42c_highZA_rep r42_highZA_check).1,
    (r42_bound r42c_cutGAB_rep r42_cutGAB_check).1,
    (r42_bound r42c_cutABG_rep r42_cutABG_check).1,
    (r42_bound r42c_cutABH_rep r42_cutABH_check).1]

theorem direct_reserve (e : Direct) : directReserve e<
    lowerOn (directDegree e) (directLeft e) (directRight e) (directPolynomial e) := by
  cases e
  exacts [(r42_bound r42c_lowSH_rep r42_lowSH_check).2,
    (r42_bound r42c_lowSG_rep r42_lowSG_check).2,
    (r42_bound r42c_highB_rep r42_highB_check).2,
    (r42_bound r42c_highZ_rep r42_highZ_check).2,
    (r42_bound r42c_highZA_rep r42_highZA_check).2,
    (r42_bound r42c_cutGAB_rep r42_cutGAB_check).2,
    (r42_bound r42c_cutABG_rep r42_cutABG_check).2,
    (r42_bound r42c_cutABH_rep r42_cutABH_check).2]

theorem direct_positive (e : Direct) {z : ℝ}
    (hz : z∈Set.Icc (directLeft e:ℝ) (directRight e:ℝ)) :
    (directReserve e:ℝ)<aeval z (directPolynomial e) := by
  apply positive_on_interval _ (direct_expansion e) (direct_reserve e) hz
  cases e <;> norm_num [directLeft,directRight,split,h]

/-- The three positive secant quotients. -/
inductive Quotient where | highH | highG | cutGAH
  deriving DecidableEq

instance : Fintype Quotient where
  elems := {.highH, .highG, .cutGAH}
  complete x := by cases x <;> decide
def quotientPolynomial : Quotient→ℚ[X]
  | .highH => highHQuotient | .highG => highGQuotient | .cutGAH => cutHQuotient
def quotientNumerator : Quotient→ℚ[X]
  | .highH => NH .high | .highG => NG | .cutGAH => cutN .gaH
def quotientLeft : Quotient→ℚ | .highH => split | .highG => split | .cutGAH => 1/4
def quotientDegree : Quotient→ℕ | .highH => 37 | .highG => 39 | .cutGAH => 37
def quotientReserve : Quotient→ℚ | .highH => 53/2500 | .highG => 457/5000 | .cutGAH => 453/1000
def quotientEndpoint : Quotient→ℚ | .highH => 57/25000 | .highG => 173/20000 | .cutGAH => 33/5000

/-! Per-case certificates of the secant quotients. -/

private def r42s_highH : Scaled := (r42NH .high).kcenter 1 5 1 5
private theorem r42s_highH_rep : r42s_highH.Rep ((NH .high).comp (X+C split)) :=
  r42_shift_rep (r42NH_rep .high) 1 5 1 5 (by norm_num) (by norm_num [split]) (by norm_num)
private def r42q_highH : Scaled := r42s_highH.divX.kcenter 1 4 1 1
private theorem r42q_highH_rep :
    r42q_highH.Rep (centered 0 (h-split) (divX ((NH .high).comp (X+C split)))) :=
  r42s_highH_rep.divX.kcentered 1 4 1 1 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highH_check :
    r42BoundOK r42q_highH 37 (53/2500) ∧ r42CoeffOK r42s_highH (57/25000) 0 := by
  decide +kernel
private theorem r42_highH_expansion :
    centered split h highHQuotient=expansion 37 (centered split h highHQuotient) := by
  rw [highHQuotient,r42_quot_eq,r42_centered_shift]
  exact (r42_bound r42q_highH_rep r42_highH_check.1).1
private theorem r42_highH_reserve : (53/2500:ℚ)<lowerOn 37 split h highHQuotient := by
  rw [lowerOn,highHQuotient,r42_quot_eq,r42_centered_shift,← lowerOn]
  exact (r42_bound r42q_highH_rep r42_highH_check.1).2
private theorem r42_highH_endpoint : (57/25000:ℚ)<(NH .high).eval split := by
  have he : (NH .high).eval split=((NH .high).comp (X+C split)).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]; simp
  rw [he]
  exact r42_coeff_lt r42s_highH_rep r42_highH_check.2

private def r42s_highG : Scaled := r42NG.kcenter 1 5 1 5
private theorem r42s_highG_rep : r42s_highG.Rep (NG.comp (X+C split)) :=
  r42_shift_rep r42NG_rep 1 5 1 5 (by norm_num) (by norm_num [split]) (by norm_num)
private def r42q_highG : Scaled := r42s_highG.divX.kcenter 1 4 1 1
private theorem r42q_highG_rep :
    r42q_highG.Rep (centered 0 (h-split) (divX (NG.comp (X+C split)))) :=
  r42s_highG_rep.divX.kcentered 1 4 1 1 (by norm_num) (by norm_num [split,h]) (by norm_num [split,h])
private theorem r42_highG_check :
    r42BoundOK r42q_highG 39 (457/5000) ∧ r42CoeffOK r42s_highG (173/20000) 0 := by
  decide +kernel
private theorem r42_highG_expansion :
    centered split h highGQuotient=expansion 39 (centered split h highGQuotient) := by
  rw [highGQuotient,r42_quot_eq,r42_centered_shift]
  exact (r42_bound r42q_highG_rep r42_highG_check.1).1
private theorem r42_highG_reserve : (457/5000:ℚ)<lowerOn 39 split h highGQuotient := by
  rw [lowerOn,highGQuotient,r42_quot_eq,r42_centered_shift,← lowerOn]
  exact (r42_bound r42q_highG_rep r42_highG_check.1).2
private theorem r42_highG_endpoint : (173/20000:ℚ)<NG.eval split := by
  have he : NG.eval split=(NG.comp (X+C split)).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]; simp
  rw [he]
  exact r42_coeff_lt r42s_highG_rep r42_highG_check.2

private def r42s_cutGAH : Scaled := (r42cutN .gaH).kcenter 1 4 1 4
private theorem r42s_cutGAH_rep : r42s_cutGAH.Rep ((cutN .gaH).comp (X+C (1/4))) :=
  r42_shift_rep (r42cutN_rep .gaH) 1 4 1 4 (by norm_num) (by norm_num) (by norm_num)
private def r42q_cutGAH : Scaled := r42s_cutGAH.divX.kcenter 9 40 1 1
private theorem r42q_cutGAH_rep :
    r42q_cutGAH.Rep (centered 0 (h-(1/4)) (divX ((cutN .gaH).comp (X+C (1/4))))) :=
  r42s_cutGAH_rep.divX.kcentered 9 40 1 1 (by norm_num) (by norm_num [h]) (by norm_num [h])
private theorem r42_cutGAH_check :
    r42BoundOK r42q_cutGAH 37 (453/1000) ∧ r42CoeffOK r42s_cutGAH (33/5000) 0 := by
  decide +kernel
private theorem r42_cutGAH_expansion :
    centered (1/4) h cutHQuotient=expansion 37 (centered (1/4) h cutHQuotient) := by
  rw [cutHQuotient,r42_quot_eq,r42_centered_shift]
  exact (r42_bound r42q_cutGAH_rep r42_cutGAH_check.1).1
private theorem r42_cutGAH_reserve : (453/1000:ℚ)<lowerOn 37 (1/4) h cutHQuotient := by
  rw [lowerOn,cutHQuotient,r42_quot_eq,r42_centered_shift,← lowerOn]
  exact (r42_bound r42q_cutGAH_rep r42_cutGAH_check.1).2
private theorem r42_cutGAH_endpoint : (33/5000:ℚ)<(cutN .gaH).eval (1/4) := by
  have he : (cutN .gaH).eval (1/4)=((cutN .gaH).comp (X+C (1/4))).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]; simp
  rw [he]
  exact r42_coeff_lt r42s_cutGAH_rep r42_cutGAH_check.2

theorem quotient_identity (e : Quotient) :
    quotientNumerator e=C ((quotientNumerator e).eval (quotientLeft e))+
      (X-C (quotientLeft e))*quotientPolynomial e := by
  cases e <;> exact r42_quot_identity _ _

theorem quotient_expansion (e : Quotient) :
    centered (quotientLeft e) h (quotientPolynomial e)=
      expansion (quotientDegree e) (centered (quotientLeft e) h (quotientPolynomial e)) := by
  cases e
  exacts [r42_highH_expansion,r42_highG_expansion,r42_cutGAH_expansion]

theorem quotient_reserve (e : Quotient) :
    quotientReserve e<lowerOn (quotientDegree e) (quotientLeft e) h (quotientPolynomial e) ∧
    quotientEndpoint e<(quotientNumerator e).eval (quotientLeft e) := by
  cases e
  exacts [⟨r42_highH_reserve,r42_highH_endpoint⟩,⟨r42_highG_reserve,r42_highG_endpoint⟩,
    ⟨r42_cutGAH_reserve,r42_cutGAH_endpoint⟩]

theorem quotient_positive (e : Quotient) {z : ℝ}
    (hz : z∈Set.Icc (quotientLeft e:ℝ) (h:ℝ)) :
    (quotientEndpoint e:ℝ)<aeval z (quotientNumerator e) := by
  have ht := positive_on_interval
    (by cases e <;> norm_num [quotientLeft,split,h] : quotientLeft e<h)
    (quotient_expansion e) (quotient_reserve e).1 hz
  have hp : 0≤aeval z (quotientPolynomial e) := by
    have hr : (0:ℝ)<(quotientReserve e:ℝ) := by
      cases e <;> norm_num [quotientReserve]
    exact (hr.trans ht).le
  have he := congrArg (fun p : ℚ[X] => aeval z p) (quotient_identity e)
  simp only [map_add,map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at he
  have hleft := r42_cast_lt (quotient_reserve e).2
  have hterm := mul_nonneg (sub_nonneg.mpr hz.1) hp
  linarith

theorem low_numerators_positive {z : ℝ} (hz : z∈Set.Icc 0 (1/5:ℝ)) :
    0<aeval z (NH .low) ∧ 0<aeval z (NZ .low) ∧ 0<aeval z NM ∧
      0<aeval z NSH ∧ 0<aeval z NSG := by
  have hH := low_H_positive hz
  have hZ := low_Z_positive hz
  have hM := low_M_positive hz
  have hSH := direct_positive .lowSH
    (r42_icc (by norm_num [directLeft]) (by norm_num [directRight,split]) hz)
  have hSG := direct_positive .lowSG
    (r42_icc (by norm_num [directLeft]) (by norm_num [directRight,split]) hz)
  norm_num [directReserve,directPolynomial] at hSH hSG
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem high_numerators_positive {z : ℝ} (hz : z∈Set.Icc (1/5:ℝ) (7/10:ℝ)) :
    0<aeval z (NH .high) ∧ 0<aeval z NG ∧ 0<aeval z NB ∧
      0<aeval z (NZ .high) ∧ 0<aeval z NZA := by
  have hq (e : Quotient) (he : quotientLeft e=split) :
      z∈Set.Icc (quotientLeft e:ℝ) (h:ℝ) :=
    r42_icc (by rw [he]; norm_num [split]) (by norm_num [h]) hz
  have hd (e : Direct) (hl : directLeft e=split) (hr : directRight e=h) :
      z∈Set.Icc (directLeft e:ℝ) (directRight e:ℝ) :=
    r42_icc (by rw [hl]; norm_num [split]) (by rw [hr]; norm_num [h]) hz
  have hH := quotient_positive .highH (hq .highH rfl)
  have hG := quotient_positive .highG (hq .highG rfl)
  have hB := direct_positive .highB (hd .highB rfl rfl)
  have hZ := direct_positive .highZ (hd .highZ rfl rfl)
  have hZA := direct_positive .highZA (hd .highZA rfl rfl)
  norm_num [quotientEndpoint,quotientNumerator] at hH hG
  norm_num [directReserve,directPolynomial] at hB hZ hZA
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem cut_numerator_positive (e : Cut) {z : ℝ}
    (hz : z∈Set.Icc (cutAngle e:ℝ) (h:ℝ)) : 0<aeval z (cutN e) := by
  cases e
  · have hh := quotient_positive .cutGAH hz
    norm_num [quotientEndpoint,quotientNumerator] at hh
    linarith
  · have hh := direct_positive .cutGAB hz
    norm_num [directReserve,directPolynomial] at hh
    linarith
  · have hh := direct_positive .cutABG hz
    norm_num [directReserve,directPolynomial] at hh
    linarith
  · have hh := direct_positive .cutABH hz
    norm_num [directReserve,directPolynomial] at hh
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.Certificate
