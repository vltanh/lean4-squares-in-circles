module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2PolynomialData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: whole-interval positivity of all eighteen negative-DE numerators

Each rational certificate is a coefficient identity. The two low T endpoints keep only the
adverse power coefficients (`low_power_positive`); the tight mixed and equal-angle numerators keep
their Chebyshev quadratic (`quadratic_positive`), and the high G numerators their cubic
(`high_G_positive`).

The kernel evaluates integer coefficient lists that mirror the polynomials. The long products of
the numerators and the affine changes of variable are one integer product or evaluation read
back in a large base (Kronecker substitution).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
open Polynomial WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (L h C4)
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep upperOn_eq_of_rep toPoly)
open PositiveTD.Certificate (S5 S9 S11 C10 C12 num3 num4 Rbar cbar sigmabar etaQ ch Ch sh)

inductive Direct where
  | lowTSH | lowTSG | lowAM | lowASH | lowASG | highTB | highAB | derivativeH | derivativeG
  deriving DecidableEq

instance : Fintype Direct where
  elems := {.lowTSH, .lowTSG, .lowAM, .lowASH, .lowASG, .highTB, .highAB, .derivativeH, .derivativeG}
  complete x := by cases x <;> decide

inductive Quadratic where | lowTM | highTZ | highAZ | highQStar
  deriving DecidableEq

instance : Fintype Quadratic where
  elems := {.lowTM, .highTZ, .highAZ, .highQStar}
  complete x := by cases x <;> decide

/-- An encoded scaled list (see `r42K.Rep`). -/
private structure r42K where
  N : ℤ
  s : ℕ
  n : ℕ
  β : ℕ

theorem eval_rat (p : ℚ[X]) (x : ℚ) : aeval (x:ℝ) p=((p.eval x:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

/-! ### The numerators as scaled integer coefficient lists

Each polynomial of the endpoint data is mirrored by a `Scaled` list (from
`WholeIntervalPolynomial.Certificate`) built with the same operations as its
definition; `Scaled.Rep` proves that the list represents it, and the kernel
evaluates only integer lists. -/

private theorem r75_repC (n : ℤ) (d : ℕ) {q : ℚ} (hd : d≠0) (h : q=n/d) :
    (⟨[n],d⟩ : Scaled).Rep (C q) := by
  unfold Scaled.Rep
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd
  simp only [WholeIntervalPolynomial.Certificate.toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  rw [h]
  field_simp

private def r75_gcdL : ℕ → List ℤ → ℕ
  | s,[] => s
  | s,a :: l => r75_gcdL (Nat.gcd s a.natAbs) l

private theorem r75_gcdL_dvd : ∀ (s : ℕ) (l : List ℤ),
    r75_gcdL s l ∣ s ∧ ∀ x ∈ l,((r75_gcdL s l : ℕ) : ℤ) ∣ x
  | s,[] => ⟨dvd_rfl,by simp⟩
  | s,a :: l => by
    obtain ⟨h1,h2⟩ := r75_gcdL_dvd (Nat.gcd s a.natAbs) l
    refine ⟨h1.trans (Nat.gcd_dvd_left _ _),?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact Int.ofNat_dvd_left.mpr (h1.trans (Nat.gcd_dvd_right _ _))
    · exact h2 x hx

private theorem r75_toPoly_map (g : ℤ) : ∀ l : List ℤ,(∀ x ∈ l,g ∣ x) →
    WholeIntervalPolynomial.Certificate.toPoly l=
      C (g:ℚ)*WholeIntervalPolynomial.Certificate.toPoly (l.map (fun x => x/g))
  | [],_ => by simp [WholeIntervalPolynomial.Certificate.toPoly]
  | a :: l,h => by
    simp only [List.map_cons,WholeIntervalPolynomial.Certificate.toPoly]
    rw [r75_toPoly_map g l (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have ha : (a:ℚ)=g*((a/g : ℤ):ℚ) := by
      have h1 := Int.ediv_mul_cancel (h a List.mem_cons_self)
      rw [mul_comm]
      exact_mod_cast h1.symm
    rw [ha,map_mul]
    ring

/-- A scaled list divided by the gcd of its scale and entries; this keeps the
integers of the kernel computation small. -/
private def r75_nrm (c : Scaled) : Scaled :=
  if r75_gcdL c.s c.l=0 then c
  else ⟨c.l.map (fun x => x/((r75_gcdL c.s c.l : ℕ):ℤ)),c.s/r75_gcdL c.s c.l⟩

private theorem r75_nrm_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r75_nrm c).Rep p := by
  unfold r75_nrm
  split_ifs with hg
  · exact hc
  · obtain ⟨h1,h2⟩ := r75_gcdL_dvd c.s c.l
    unfold Scaled.Rep at *
    have hl := r75_toPoly_map ((r75_gcdL c.s c.l : ℕ):ℤ) c.l h2
    have hg' : (r75_gcdL c.s c.l : ℚ)≠0 := by exact_mod_cast hg
    have hs : (c.s:ℚ)=(r75_gcdL c.s c.l : ℚ)*((c.s/r75_gcdL c.s c.l : ℕ) : ℚ) := by
      rw [Nat.cast_div h1 hg']
      field_simp
    have hC : C (r75_gcdL c.s c.l : ℚ)≠0 := by rwa [Ne,C_eq_zero]
    apply mul_left_cancel₀ hC
    push_cast at hl
    rw [← hl,hc,hs,map_mul]
    ring

private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.nadd (a b : Scaled) : Scaled := r75_nrm (a.add b)
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.nsub (a b : Scaled) : Scaled := r75_nrm (a.sub b)
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.nmul (a b : Scaled) : Scaled := r75_nrm (a.mul b)
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.npow (a : Scaled) (n : ℕ) : Scaled :=
  r75_nrm (a.pow n)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.nadd {a b : Scaled} {p q : ℚ[X]}
    (ha : a.Rep p) (hb : b.Rep q) : (a.nadd b).Rep (p+q) := r75_nrm_rep (ha.add hb)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.nsub {a b : Scaled} {p q : ℚ[X]}
    (ha : a.Rep p) (hb : b.Rep q) : (a.nsub b).Rep (p-q) := r75_nrm_rep (ha.sub hb)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.nmul {a b : Scaled} {p q : ℚ[X]}
    (ha : a.Rep p) (hb : b.Rep q) : (a.nmul b).Rep (p*q) := r75_nrm_rep (ha.mul hb)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.npow {a : Scaled} {p : ℚ[X]}
    (ha : a.Rep p) (n : ℕ) : (a.npow n).Rep (p^n) := r75_nrm_rep (ha.pow n)


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
  r75_nrm ((r42num3B B A P0 P1 P2 r0 r1 r2).toScaled B)
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
  exact r42_rep_eq (by unfold num3; ring) (r75_nrm_rep (r42K.Rep.toScaled
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
  r75_nrm ((r42num4B B A P0 P1 P2 P3 r0 r1 r2 r3).toScaled B)
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
  exact r42_rep_eq (by unfold num4; ring) (r75_nrm_rep (r42K.Rep.toScaled
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

/-- Products and squares by Kronecker substitution (`r42K`), reduced. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.nkmul (a b : Scaled) : Scaled :=
  r75_nrm (((r42K.ofScaled (2*(a.l.length*r42amax a.l*r42amax b.l)+1) a).mul
    (r42K.ofScaled (2*(a.l.length*r42amax a.l*r42amax b.l)+1) b)).toScaled
      (2*(a.l.length*r42amax a.l*r42amax b.l)+1))
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.nkmul {a b : Scaled}
    {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.nkmul b).Rep (p*q) :=
  r75_nrm_rep ((r42K.rep_ofScaled _ ha).mul (r42K.rep_ofScaled _ hb)).toScaled
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.nksq (a : Scaled) : Scaled :=
  a.nkmul a
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.nksq {a : Scaled}
    {p : ℚ[X]} (ha : a.Rep p) : a.nksq.Rep (p^2) := by
  rw [sq]; exact ha.nkmul ha

private theorem r75_ch : ch=3964941898733393/5184000000000000 := by
  norm_num [ch,C10,PositiveTD.Certificate.C4,h]
private theorem r75_Ch : Ch=52337233065258114343/68428800000000000000 := by
  norm_num [Ch,C12,C10,PositiveTD.Certificate.C4,h]
private theorem r75_sh : sh=367358693969535751/570240000000000000 := by
  norm_num [sh,S11,S9,S5,h]

private def r75_S5 : Scaled :=
  (Scaled.var.nsub ((⟨[1],6⟩ : Scaled).nmul (Scaled.var.npow 3))).nadd
    ((⟨[1],120⟩ : Scaled).nmul (Scaled.var.npow 5))
private theorem r75_S5_rep : r75_S5.Rep S5 :=
  (Scaled.rep_var.nsub ((r75_repC 1 6 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 3))).nadd
    ((r75_repC 1 120 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 5))
private def r75_S9 : Scaled :=
  (r75_S5.nsub ((⟨[1],5040⟩ : Scaled).nmul (Scaled.var.npow 7))).nadd
    ((⟨[1],362880⟩ : Scaled).nmul (Scaled.var.npow 9))
private theorem r75_S9_rep : r75_S9.Rep S9 :=
  (r75_S5_rep.nsub ((r75_repC 1 5040 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 7))).nadd
    ((r75_repC 1 362880 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 9))
private def r75_S11 : Scaled := r75_S9.nsub ((⟨[1],39916800⟩ : Scaled).nmul (Scaled.var.npow 11))
private theorem r75_S11_rep : r75_S11.Rep S11 :=
  r75_S9_rep.nsub ((r75_repC 1 39916800 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 11))
private def r75_C4 : Scaled :=
  ((Scaled.ofNat 1).nsub ((⟨[1],2⟩ : Scaled).nmul (Scaled.var.npow 2))).nadd
    ((⟨[1],24⟩ : Scaled).nmul (Scaled.var.npow 4))
private theorem r75_C4_rep : r75_C4.Rep C4 :=
  (Scaled.rep_one.nsub ((r75_repC 1 2 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 2))).nadd
    ((r75_repC 1 24 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 4))
private def r75_C10 : Scaled :=
  ((r75_C4.nsub ((⟨[1],720⟩ : Scaled).nmul (Scaled.var.npow 6))).nadd
    ((⟨[1],40320⟩ : Scaled).nmul (Scaled.var.npow 8))).nsub
    ((⟨[1],3628800⟩ : Scaled).nmul (Scaled.var.npow 10))
private theorem r75_C10_rep : r75_C10.Rep C10 :=
  ((r75_C4_rep.nsub ((r75_repC 1 720 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 6))).nadd
    ((r75_repC 1 40320 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 8))).nsub
    ((r75_repC 1 3628800 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 10))
private def r75_C12 : Scaled := r75_C10.nadd ((⟨[1],479001600⟩ : Scaled).nmul (Scaled.var.npow 12))
private theorem r75_C12_rep : r75_C12.Rep C12 :=
  r75_C10_rep.nadd ((r75_repC 1 479001600 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 12))

private def r75_num3 (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled := r42num3 A P0 P1 P2 r0 r1 r2
private theorem r75_num3_rep {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 s0 s1 s2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (r75_num3 A P0 P1 P2 r0 r1 r2).Rep (num3 a p0 p1 p2 s0 s1 s2) :=
  r42num3_rep hA h0 h1 h2 g0 g1 g2
private def r75_num4 (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled := r42num4 A P0 P1 P2 P3 r0 r1 r2 r3
private theorem r75_num4_rep {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (r75_num4 A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) :=
  r42num4_rep hA h0 h1 h2 h3 g0 g1 g2 g3

private def r75_XL : Scaled := Scaled.var.nsub ⟨[1],6⟩
private theorem r75_XL_rep : r75_XL.Rep (X-C L) :=
  Scaled.rep_var.nsub (r75_repC 1 6 (by norm_num) (by norm_num [L]))
private def r75_t : Scaled := (⟨[15],8⟩ : Scaled).nmul r75_XL
private theorem r75_t_rep : r75_t.Rep t :=
  (r75_repC 15 8 (by norm_num) (by norm_num)).nmul r75_XL_rep

private def r75_k : Family → Scaled
  | .low => ((⟨[6708],10000⟩ : Scaled).nadd ((⟨[3],20⟩ : Scaled).nmul r75_XL)).nadd
      ((⟨[4],1⟩ : Scaled).nmul (r75_XL.npow 2))
  | .high => ((((⟨[670158],1000000⟩ : Scaled).nadd ((⟨[113718],1000000⟩ : Scaled).nmul r75_t)).nadd
      ((⟨[6506],1000000⟩ : Scaled).nmul (r75_t.npow 2))).nadd
      ((⟨[9026],1000000⟩ : Scaled).nmul (r75_t.npow 3))).nadd ((⟨[1],1000⟩ : Scaled).nmul (r75_t.npow 4))
private theorem r75_k_rep : ∀ f,(r75_k f).Rep (k f)
  | .low => ((r75_repC 6708 10000 (by norm_num) (by norm_num)).nadd
      ((r75_repC 3 20 (by norm_num) (by norm_num)).nmul r75_XL_rep)).nadd
      ((r75_repC 4 1 (by norm_num) (by norm_num)).nmul (r75_XL_rep.npow 2))
  | .high => ((((r75_repC 670158 1000000 (by norm_num) (by norm_num)).nadd
      ((r75_repC 113718 1000000 (by norm_num) (by norm_num)).nmul r75_t_rep)).nadd
      ((r75_repC 6506 1000000 (by norm_num) (by norm_num)).nmul (r75_t_rep.npow 2))).nadd
      ((r75_repC 9026 1000000 (by norm_num) (by norm_num)).nmul (r75_t_rep.npow 3))).nadd
      ((r75_repC 1 1000 (by norm_num) (by norm_num)).nmul (r75_t_rep.npow 4))
private def r75_l : Family → Scaled
  | .low => ((⟨[10073],10000⟩ : Scaled).nsub ((⟨[17],10⟩ : Scaled).nmul r75_XL)).nadd
      ((⟨[11],5⟩ : Scaled).nmul (r75_XL.npow 2))
  | .high => (((⟨[1005069],1000000⟩ : Scaled).nsub ((⟨[146411],1000000⟩ : Scaled).nmul r75_t)).nsub
      ((⟨[157739],1000000⟩ : Scaled).nmul (r75_t.npow 2))).nadd
      ((⟨[162815],1000000⟩ : Scaled).nmul (r75_t.npow 3))
private theorem r75_l_rep : ∀ f,(r75_l f).Rep (l f)
  | .low => ((r75_repC 10073 10000 (by norm_num) (by norm_num)).nsub
      ((r75_repC 17 10 (by norm_num) (by norm_num)).nmul r75_XL_rep)).nadd
      ((r75_repC 11 5 (by norm_num) (by norm_num)).nmul (r75_XL_rep.npow 2))
  | .high => (((r75_repC 1005069 1000000 (by norm_num) (by norm_num)).nsub
      ((r75_repC 146411 1000000 (by norm_num) (by norm_num)).nmul r75_t_rep)).nsub
      ((r75_repC 157739 1000000 (by norm_num) (by norm_num)).nmul (r75_t_rep.npow 2))).nadd
      ((r75_repC 162815 1000000 (by norm_num) (by norm_num)).nmul (r75_t_rep.npow 3))
private def r75_c : Family → Scaled
  | .low => ((⟨[10389],10000⟩ : Scaled).nsub ((⟨[69],20⟩ : Scaled).nmul r75_XL)).nadd
      ((⟨[9],1⟩ : Scaled).nmul (r75_XL.npow 2))
  | .high => (((⟨[1021248],1000000⟩ : Scaled).nsub ((⟨[168873],1000000⟩ : Scaled).nmul r75_t)).nsub
      ((⟨[165381],1000000⟩ : Scaled).nmul (r75_t.npow 2))).nadd
      ((⟨[175944],1000000⟩ : Scaled).nmul (r75_t.npow 3))
private theorem r75_c_rep : ∀ f,(r75_c f).Rep (c f)
  | .low => ((r75_repC 10389 10000 (by norm_num) (by norm_num)).nsub
      ((r75_repC 69 20 (by norm_num) (by norm_num)).nmul r75_XL_rep)).nadd
      ((r75_repC 9 1 (by norm_num) (by norm_num)).nmul (r75_XL_rep.npow 2))
  | .high => (((r75_repC 1021248 1000000 (by norm_num) (by norm_num)).nsub
      ((r75_repC 168873 1000000 (by norm_num) (by norm_num)).nmul r75_t_rep)).nsub
      ((r75_repC 165381 1000000 (by norm_num) (by norm_num)).nmul (r75_t_rep.npow 2))).nadd
      ((r75_repC 175944 1000000 (by norm_num) (by norm_num)).nmul (r75_t_rep.npow 3))

private def r75_C2 : Scaled := (Scaled.ofNat 1).nsub ((⟨[1],2⟩ : Scaled).nmul (Scaled.var.npow 2))
private theorem r75_C2_rep : r75_C2.Rep C2 :=
  Scaled.rep_one.nsub ((r75_repC 1 2 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 2))
private def r75_S3 : Scaled := Scaled.var.nsub ((⟨[1],6⟩ : Scaled).nmul (Scaled.var.npow 3))
private theorem r75_S3_rep : r75_S3.Rep S3 :=
  Scaled.rep_var.nsub ((r75_repC 1 6 (by norm_num) (by norm_num)).nmul (Scaled.rep_var.npow 3))
private def r75_J0 : Scaled :=
  ((⟨[1],2⟩ : Scaled).nmul (r75_C10.nsub (Scaled.ofNat 1))).nadd
    ((⟨[-114321959],125000000⟩ : Scaled).nmul r75_S9)
private theorem r75_J0_rep : r75_J0.Rep J0 :=
  ((r75_repC 1 2 (by norm_num) (by norm_num)).nmul (r75_C10_rep.nsub Scaled.rep_one)).nadd
    ((r75_repC (-114321959) 125000000 (by norm_num) (by norm_num [abar])).nmul r75_S9_rep)
private def r75_J1 : Scaled := r75_J0.nsub ((⟨[151],500⟩ : Scaled).nmul (r75_XL.npow 6))
private theorem r75_J1_rep : r75_J1.Rep J1 :=
  r75_J0_rep.nsub ((r75_repC 151 500 (by norm_num) (by norm_num)).nmul (r75_XL_rep.npow 6))

private def r75_eta : Scaled := ⟨[293],1000⟩
private theorem r75_eta_rep : r75_eta.Rep (C etaQ) := r75_repC 293 1000 (by norm_num) (by norm_num [etaQ])

private def r75_mLo (f : Family) : Split → Scaled
  | .atT => (r75_c f).nmul (r75_C10.nadd (r75_eta.nmul r75_S11))
  | .atA => r75_c f
private theorem r75_mLo_rep (f : Family) : ∀ e,(r75_mLo f e).Rep (mLo f e)
  | .atT => (r75_c_rep f).nmul (r75_C10_rep.nadd (r75_eta_rep.nmul r75_S11_rep))
  | .atA => r75_c_rep f
private def r75_mHi (f : Family) : Split → Scaled
  | .atT => (r75_c f).nmul (r75_C12.nadd (r75_eta.nmul r75_S9))
  | .atA => r75_c f
private theorem r75_mHi_rep (f : Family) : ∀ e,(r75_mHi f e).Rep (mHi f e)
  | .atT => (r75_c_rep f).nmul (r75_C12_rep.nadd (r75_eta_rep.nmul r75_S9_rep))
  | .atA => r75_c_rep f
private def r75_mu : Family → Split → Scaled
  | .low,.atT => (r75_c .low).nmul (r75_C2.nadd (r75_eta.nmul Scaled.var))
  | .high,.atT => (r75_c .high).nmul (r75_C4.nadd (r75_eta.nmul r75_S5))
  | f,.atA => r75_c f
private theorem r75_mu_rep : ∀ f e,(r75_mu f e).Rep (mu f e)
  | .low,.atT => by
    simp only [mu,↓reduceIte]
    exact (r75_c_rep .low).nmul (r75_C2_rep.nadd (r75_eta_rep.nmul Scaled.rep_var))
  | .high,.atT => by
    simp only [mu,reduceCtorEq,↓reduceIte]
    exact (r75_c_rep .high).nmul (r75_C4_rep.nadd (r75_eta_rep.nmul r75_S5_rep))
  | .low,.atA => r75_c_rep .low
  | .high,.atA => r75_c_rep .high

private def r75_lowE : Split → Scaled
  | .atT => (((((⟨[2],1⟩ : Scaled).nmul (r75_k .low)).nadd ((⟨[3],1⟩ : Scaled).nmul (r75_l .low))).nadd
      ((⟨[3],2⟩ : Scaled).nmul (r75_mLo .low .atT))).nadd (⟨[5],2⟩ : Scaled)).nadd
      (((⟨[1],2⟩ : Scaled).nmul (r75_c .low)).nmul (((Scaled.ofNat 1).nadd r75_C10).nadd r75_S11)) |>.nsub
      (((r75_c .low).nmul (⟨[1415477291],1000000000⟩ : Scaled)).nmul r75_S9)
  | .atA => ((((⟨[2],1⟩ : Scaled).nmul (r75_k .low)).nadd ((⟨[3],1⟩ : Scaled).nmul (r75_l .low))).nadd
      ((⟨[5],2⟩ : Scaled).nmul (r75_c .low))).nadd (⟨[5],2⟩ : Scaled) |>.nadd ((r75_l .low).nmul r75_J0)
private theorem r75_lowE_rep : ∀ e,(r75_lowE e).Rep (lowE e)
  | .atT => (((((r75_repC 2 1 (by norm_num) (by norm_num)).nmul (r75_k_rep .low)).nadd
      ((r75_repC 3 1 (by norm_num) (by norm_num)).nmul (r75_l_rep .low))).nadd
      ((r75_repC 3 2 (by norm_num) (by norm_num)).nmul (r75_mLo_rep .low .atT))).nadd
      (r75_repC 5 2 (by norm_num) (by norm_num))).nadd
      (((r75_repC 1 2 (by norm_num) (by norm_num)).nmul (r75_c_rep .low)).nmul
        ((Scaled.rep_one.nadd r75_C10_rep).nadd r75_S11_rep)) |>.nsub
      (((r75_c_rep .low).nmul (r75_repC 1415477291 1000000000 (by norm_num)
        (by norm_num [sigmabar]))).nmul r75_S9_rep)
  | .atA => ((((r75_repC 2 1 (by norm_num) (by norm_num)).nmul (r75_k_rep .low)).nadd
      ((r75_repC 3 1 (by norm_num) (by norm_num)).nmul (r75_l_rep .low))).nadd
      ((r75_repC 5 2 (by norm_num) (by norm_num)).nmul (r75_c_rep .low))).nadd
      (r75_repC 5 2 (by norm_num) (by norm_num)) |>.nadd ((r75_l_rep .low).nmul r75_J0_rep)
private def r75_lowB (e : Split) : Scaled :=
  (r75_lowE e).nsub ((⟨[449607033],500000000⟩ : Scaled).nmul ((Scaled.ofNat 1).nadd (r75_c .low)))
private theorem r75_lowB_rep (e : Split) : (r75_lowB e).Rep (lowB e) :=
  (r75_lowE_rep e).nsub ((r75_repC 449607033 500000000 (by norm_num) (by norm_num [cbar])).nmul
    (Scaled.rep_one.nadd (r75_c_rep .low)))
private def r75_highB : Split → Scaled
  | .atT => ((((((⟨[2],1⟩ : Scaled).nmul (r75_k .high)).nadd ((⟨[3],1⟩ : Scaled).nmul (r75_l .high))).nadd
      ((⟨[3],2⟩ : Scaled).nmul (r75_mLo .high .atT))).nadd ((⟨[1],2⟩ : Scaled).nmul (r75_c .high))).nadd
      (⟨[3],1⟩ : Scaled)).nadd
      (((⟨[1],2⟩ : Scaled).nmul (r75_c .high)).nmul (((Scaled.ofNat 1).nadd r75_C10).nadd r75_S11)) |>.nsub
      (((r75_c .high).nmul (⟨[1415477291],1000000000⟩ : Scaled)).nmul r75_S9)
  | .atA => ((((⟨[2],1⟩ : Scaled).nmul (r75_k .high)).nadd ((⟨[3],1⟩ : Scaled).nmul (r75_l .high))).nadd
      ((⟨[3],1⟩ : Scaled).nmul (r75_c .high))).nadd (⟨[3],1⟩ : Scaled) |>.nadd ((r75_l .high).nmul r75_J1)
private theorem r75_highB_rep : ∀ e,(r75_highB e).Rep (highB e)
  | .atT => ((((((r75_repC 2 1 (by norm_num) (by norm_num)).nmul (r75_k_rep .high)).nadd
      ((r75_repC 3 1 (by norm_num) (by norm_num)).nmul (r75_l_rep .high))).nadd
      ((r75_repC 3 2 (by norm_num) (by norm_num)).nmul (r75_mLo_rep .high .atT))).nadd
      ((r75_repC 1 2 (by norm_num) (by norm_num)).nmul (r75_c_rep .high))).nadd
      (r75_repC 3 1 (by norm_num) (by norm_num))).nadd
      (((r75_repC 1 2 (by norm_num) (by norm_num)).nmul (r75_c_rep .high)).nmul
        ((Scaled.rep_one.nadd r75_C10_rep).nadd r75_S11_rep)) |>.nsub
      (((r75_c_rep .high).nmul (r75_repC 1415477291 1000000000 (by norm_num)
        (by norm_num [sigmabar]))).nmul r75_S9_rep)
  | .atA => ((((r75_repC 2 1 (by norm_num) (by norm_num)).nmul (r75_k_rep .high)).nadd
      ((r75_repC 3 1 (by norm_num) (by norm_num)).nmul (r75_l_rep .high))).nadd
      ((r75_repC 3 1 (by norm_num) (by norm_num)).nmul (r75_c_rep .high))).nadd
      (r75_repC 3 1 (by norm_num) (by norm_num)) |>.nadd ((r75_l_rep .high).nmul r75_J1_rep)

private def r75_PH (f : Family) : Scaled := (Scaled.ofNat 1).nadd ((r75_k f).npow 2)
private theorem r75_PH_rep (f : Family) : (r75_PH f).Rep (PH f) :=
  Scaled.rep_one.nadd ((r75_k_rep f).npow 2)
private def r75_PG (f : Family) : Scaled := ((r75_k f).npow 2).nadd ((r75_l f).npow 2)
private theorem r75_PG_rep (f : Family) : (r75_PG f).Rep (PG f) :=
  ((r75_k_rep f).npow 2).nadd ((r75_l_rep f).npow 2)
private def r75_PB (f : Family) (e : Split) : Scaled := ((r75_mHi f e).nksq).nadd ((r75_l f).npow 2)
private theorem r75_PB_rep (f : Family) (e : Split) : (r75_PB f e).Rep (PB f e) :=
  ((r75_mHi_rep f e).nksq).nadd ((r75_l_rep f).npow 2)
private def r75_PD (f : Family) : Scaled := (Scaled.ofNat 1).nadd ((r75_c f).npow 2)
private theorem r75_PD_rep (f : Family) : (r75_PD f).Rep (PD f) :=
  Scaled.rep_one.nadd ((r75_c_rep f).npow 2)
private def r75_PHminus (f : Family) : Scaled :=
  (r75_PH f).nsub (((⟨[2],1⟩ : Scaled).nmul (r75_k f)).nmul r75_S11)
private theorem r75_PHminus_rep (f : Family) : (r75_PHminus f).Rep (PHminus f) :=
  (r75_PH_rep f).nsub (((r75_repC 2 1 (by norm_num) (by norm_num)).nmul (r75_k_rep f)).nmul r75_S11_rep)
private def r75_PGminus (f : Family) : Scaled :=
  (r75_PG f).nsub ((((⟨[2],1⟩ : Scaled).nmul (r75_k f)).nmul (r75_l f)).nmul r75_S11)
private theorem r75_PGminus_rep (f : Family) : (r75_PGminus f).Rep (PGminus f) :=
  (r75_PG_rep f).nsub ((((r75_repC 2 1 (by norm_num) (by norm_num)).nmul (r75_k_rep f)).nmul
    (r75_l_rep f)).nmul r75_S11_rep)
private def r75_PBminus (f : Family) (e : Split) : Scaled :=
  (r75_PB f e).nsub ((((⟨[2],1⟩ : Scaled).nmul (r75_l f)).nmul (r75_mLo f e)).nmul r75_S11)
private theorem r75_PBminus_rep (f : Family) (e : Split) : (r75_PBminus f e).Rep (PBminus f e) :=
  (r75_PB_rep f e).nsub ((((r75_repC 2 1 (by norm_num) (by norm_num)).nmul (r75_l_rep f)).nmul
    (r75_mLo_rep f e)).nmul r75_S11_rep)
private def r75_twosh : Scaled := ⟨[367358693969535751],285120000000000000⟩
private theorem r75_twosh_rep : r75_twosh.Rep (C (2*sh)) :=
  r75_repC 367358693969535751 285120000000000000 (by norm_num) (by rw [r75_sh]; norm_num)
private def r75_PHcap : Scaled := (r75_PH .low).nsub (r75_twosh.nmul (r75_k .low))
private theorem r75_PHcap_rep : r75_PHcap.Rep PHcap :=
  (r75_PH_rep .low).nsub (r75_twosh_rep.nmul (r75_k_rep .low))
private def r75_PGcap : Scaled := (r75_PG .low).nsub ((r75_twosh.nmul (r75_k .low)).nmul (r75_l .low))
private theorem r75_PGcap_rep : r75_PGcap.Rep PGcap :=
  (r75_PG_rep .low).nsub ((r75_twosh_rep.nmul (r75_k_rep .low)).nmul (r75_l_rep .low))

private def r75_RH : Family → Scaled
  | .low => (⟨[41],50⟩ : Scaled).nadd ((⟨[143],250⟩ : Scaled).nmul (r75_k .low))
  | .high => (⟨[4],5⟩ : Scaled).nadd ((⟨[3],5⟩ : Scaled).nmul (r75_k .high))
private theorem r75_RH_rep : ∀ f,(r75_RH f).Rep (RH f)
  | .low => (r75_repC 41 50 (by norm_num) (by norm_num)).nadd
      ((r75_repC 143 250 (by norm_num) (by norm_num)).nmul (r75_k_rep .low))
  | .high => (r75_repC 4 5 (by norm_num) (by norm_num)).nadd
      ((r75_repC 3 5 (by norm_num) (by norm_num)).nmul (r75_k_rep .high))
private def r75_RG : Family → Scaled
  | .low => ((⟨[11],20⟩ : Scaled).nmul (r75_k .low)).nadd ((⟨[167],200⟩ : Scaled).nmul (r75_l .low))
  | .high => ((⟨[31],50⟩ : Scaled).nmul (r75_k .high)).nadd ((⟨[3923],5000⟩ : Scaled).nmul (r75_l .high))
private theorem r75_RG_rep : ∀ f,(r75_RG f).Rep (RG f)
  | .low => ((r75_repC 11 20 (by norm_num) (by norm_num)).nmul (r75_k_rep .low)).nadd
      ((r75_repC 167 200 (by norm_num) (by norm_num)).nmul (r75_l_rep .low))
  | .high => ((r75_repC 31 50 (by norm_num) (by norm_num)).nmul (r75_k_rep .high)).nadd
      ((r75_repC 3923 5000 (by norm_num) (by norm_num)).nmul (r75_l_rep .high))
private def r75_RB : Family → Split → Scaled
  | .low,e => ((⟨[729],1000⟩ : Scaled).nmul (r75_mu .low e)).nadd
      ((⟨[1369],2000⟩ : Scaled).nmul (r75_l .low))
  | .high,e => (⟨[7071],10000⟩ : Scaled).nmul ((r75_l .high).nadd (r75_mu .high e))
private theorem r75_RB_rep : ∀ f e,(r75_RB f e).Rep (RB f e)
  | .low,e => by
    simp only [RB,↓reduceIte]
    exact ((r75_repC 729 1000 (by norm_num) (by norm_num)).nmul (r75_mu_rep .low e)).nadd
      ((r75_repC 1369 2000 (by norm_num) (by norm_num)).nmul (r75_l_rep .low))
  | .high,e => by
    simp only [RB,reduceCtorEq,↓reduceIte]
    exact (r75_repC 7071 10000 (by norm_num) (by norm_num)).nmul
      ((r75_l_rep .high).nadd (r75_mu_rep .high e))
private def r75_RD : Scaled := (⟨[18],25⟩ : Scaled).nadd ((⟨[347],500⟩ : Scaled).nmul (r75_c .high))
private theorem r75_RD_rep : r75_RD.Rep RD :=
  (r75_repC 18 25 (by norm_num) (by norm_num)).nadd
    ((r75_repC 347 500 (by norm_num) (by norm_num)).nmul (r75_c_rep .high))
private def r75_RHminus : Family → Scaled
  | .low => ((⟨[89],100⟩ : Scaled).nmul r75_C2).nadd ((⟨[57],125⟩ : Scaled).nmul ((r75_k .low).nsub r75_S3))
  | .high => ((⟨[93],100⟩ : Scaled).nmul r75_C4).nadd
      ((⟨[919],2500⟩ : Scaled).nmul ((r75_k .high).nsub r75_S5))
private theorem r75_RHminus_rep : ∀ f,(r75_RHminus f).Rep (RHminus f)
  | .low => ((r75_repC 89 100 (by norm_num) (by norm_num)).nmul r75_C2_rep).nadd
      ((r75_repC 57 125 (by norm_num) (by norm_num)).nmul ((r75_k_rep .low).nsub r75_S3_rep))
  | .high => ((r75_repC 93 100 (by norm_num) (by norm_num)).nmul r75_C4_rep).nadd
      ((r75_repC 919 2500 (by norm_num) (by norm_num)).nmul ((r75_k_rep .high).nsub r75_S5_rep))
private def r75_RGminus : Scaled :=
  (((⟨[93],100⟩ : Scaled).nmul (r75_l .high)).nmul r75_C4).nadd
    ((⟨[919],2500⟩ : Scaled).nmul ((r75_k .high).nsub ((r75_l .high).nmul r75_S5)))
private theorem r75_RGminus_rep : r75_RGminus.Rep RGminus :=
  (((r75_repC 93 100 (by norm_num) (by norm_num)).nmul (r75_l_rep .high)).nmul r75_C4_rep).nadd
    ((r75_repC 919 2500 (by norm_num) (by norm_num)).nmul
      ((r75_k_rep .high).nsub ((r75_l_rep .high).nmul r75_S5_rep)))
private def r75_RBminus (e : Split) : Scaled :=
  (((⟨[83],100⟩ : Scaled).nmul (r75_l .high)).nmul r75_C4).nadd
    ((⟨[14],25⟩ : Scaled).nmul ((r75_mu .high e).nsub ((r75_l .high).nmul r75_S5)))
private theorem r75_RBminus_rep (e : Split) : (r75_RBminus e).Rep (RBminus e) :=
  (((r75_repC 83 100 (by norm_num) (by norm_num)).nmul (r75_l_rep .high)).nmul r75_C4_rep).nadd
    ((r75_repC 14 25 (by norm_num) (by norm_num)).nmul
      ((r75_mu_rep .high e).nsub ((r75_l_rep .high).nmul r75_S5_rep)))
private def r75_RHcap : Scaled := ⟨[77],100⟩
private theorem r75_RHcap_rep : r75_RHcap.Rep RHcap := r75_repC 77 100 (by norm_num) (by norm_num)
private def r75_RGcap : Scaled := (⟨[153],200⟩ : Scaled).nmul (r75_l .low)
private theorem r75_RGcap_rep : r75_RGcap.Rep RGcap :=
  (r75_repC 153 200 (by norm_num) (by norm_num)).nmul (r75_l_rep .low)
private def r75_hX : Scaled := (⟨[7],10⟩ : Scaled).nsub Scaled.var
private theorem r75_hX_rep : r75_hX.Rep (C h-X) :=
  (r75_repC 7 10 (by norm_num) (by norm_num [h])).nsub Scaled.rep_var
private def r75_qStar : Scaled := (r75_l .high).nadd ((⟨[3],20⟩ : Scaled).nmul r75_hX)
private theorem r75_qStar_rep : r75_qStar.Rep qStar :=
  (r75_l_rep .high).nadd ((r75_repC 3 20 (by norm_num) (by norm_num)).nmul r75_hX_rep)

private def r75_NH : Family → Split → Scaled
  | .low,e => r75_num3 (((r75_lowB e).nadd r75_C10).nsub (Scaled.ofNat 1))
      (r75_PHminus .low) (r75_PG .low) (r75_PB .low e) (r75_RHminus .low) (r75_RG .low) (r75_RB .low e)
  | .high,e => r75_num4 (((r75_highB e).nadd r75_C10).nsub (Scaled.ofNat 1))
      (r75_PG .high) (r75_PB .high e) (r75_PHminus .high) (r75_PD .high)
      (r75_RG .high) (r75_RB .high e) (r75_RHminus .high) r75_RD
private theorem r75_NH_rep : ∀ f e,(r75_NH f e).Rep (NH f e)
  | .low,e => by
    simp only [NH,↓reduceIte]
    exact r75_num3_rep (((r75_lowB_rep e).nadd r75_C10_rep).nsub Scaled.rep_one)
      (r75_PHminus_rep .low) (r75_PG_rep .low) (r75_PB_rep .low e) (r75_RHminus_rep .low)
      (r75_RG_rep .low) (r75_RB_rep .low e)
  | .high,e => by
    simp only [NH,reduceCtorEq,↓reduceIte]
    exact r75_num4_rep (((r75_highB_rep e).nadd r75_C10_rep).nsub Scaled.rep_one)
      (r75_PG_rep .high) (r75_PB_rep .high e) (r75_PHminus_rep .high) (r75_PD_rep .high)
      (r75_RG_rep .high) (r75_RB_rep .high e) (r75_RHminus_rep .high) r75_RD_rep
private def r75_lowDen (e : Split) : Scaled :=
  (((⟨[2],1⟩ : Scaled).nmul (r75_RHminus .low)).nmul (r75_RG .low)).nmul (r75_RB .low e)
private theorem r75_lowDen_rep (e : Split) : (r75_lowDen e).Rep (lowDen e) :=
  (((r75_repC 2 1 (by norm_num) (by norm_num)).nmul (r75_RHminus_rep .low)).nmul
    (r75_RG_rep .low)).nmul (r75_RB_rep .low e)
private def r75_ZG : Scaled :=
  ((r75_k .low).nmul ((((⟨[803502302830208981],570240000000000000⟩ : Scaled).nmul r75_C10).nsub
    ((⟨[8254189788913824223],68428800000000000000⟩ : Scaled).nmul r75_S9)).nsub (Scaled.ofNat 1))).nadd
    ((r75_l .low).nmul ((⟨[3964941898733393],5184000000000000⟩ : Scaled).nsub r75_C12))
private theorem r75_ZG_rep : r75_ZG.Rep ZG :=
  ((r75_k_rep .low).nmul ((((r75_repC 803502302830208981 570240000000000000 (by norm_num)
    (by rw [r75_ch,r75_sh]; norm_num)).nmul r75_C10_rep).nsub
    ((r75_repC 8254189788913824223 68428800000000000000 (by norm_num)
      (by rw [r75_Ch,r75_sh]; norm_num)).nmul r75_S9_rep)).nsub Scaled.rep_one)).nadd
    ((r75_l_rep .low).nmul ((r75_repC 3964941898733393 5184000000000000 (by norm_num)
      (by rw [r75_ch]; norm_num)).nsub r75_C12_rep))
private def r75_NM (e : Split) : Scaled := (r75_NH .low e).nadd ((r75_lowDen e).nkmul r75_ZG)
private theorem r75_NM_rep (e : Split) : (r75_NM e).Rep (NM e) :=
  (r75_NH_rep .low e).nadd ((r75_lowDen_rep e).nkmul r75_ZG_rep)
private def r75_chm1 : Scaled := ⟨[-1219058101266607],5184000000000000⟩
private theorem r75_chm1_rep : r75_chm1.Rep (C (ch-1)) :=
  r75_repC (-1219058101266607) 5184000000000000 (by norm_num) (by rw [r75_ch]; norm_num)
private def r75_NSH (e : Split) : Scaled :=
  r75_num3 (((r75_lowB e).nsub (((⟨[109],200⟩ : Scaled).nmul (r75_mHi .low e)).nmul r75_hX)).nadd r75_chm1)
    r75_PHcap (r75_PG .low) (r75_PB .low e) r75_RHcap (r75_RG .low) (r75_RB .low e)
private theorem r75_NSH_rep (e : Split) : (r75_NSH e).Rep (NSH e) :=
  r75_num3_rep (((r75_lowB_rep e).nsub (((r75_repC 109 200 (by norm_num) (by norm_num)).nmul
    (r75_mHi_rep .low e)).nmul r75_hX_rep)).nadd r75_chm1_rep)
    r75_PHcap_rep (r75_PG_rep .low) (r75_PB_rep .low e) r75_RHcap_rep (r75_RG_rep .low)
    (r75_RB_rep .low e)
private def r75_NSG (e : Split) : Scaled :=
  r75_num3 (((r75_lowB e).nsub (((⟨[109],200⟩ : Scaled).nmul (r75_mHi .low e)).nmul r75_hX)).nadd
    ((r75_l .low).nmul r75_chm1))
    (r75_PH .low) r75_PGcap (r75_PB .low e) (r75_RH .low) r75_RGcap (r75_RB .low e)
private theorem r75_NSG_rep (e : Split) : (r75_NSG e).Rep (NSG e) :=
  r75_num3_rep (((r75_lowB_rep e).nsub (((r75_repC 109 200 (by norm_num) (by norm_num)).nmul
    (r75_mHi_rep .low e)).nmul r75_hX_rep)).nadd ((r75_l_rep .low).nmul r75_chm1_rep))
    (r75_PH_rep .low) r75_PGcap_rep (r75_PB_rep .low e) (r75_RH_rep .low) r75_RGcap_rep
    (r75_RB_rep .low e)
private def r75_NG (e : Split) : Scaled :=
  r75_num4 ((r75_highB e).nadd ((r75_l .high).nmul (r75_C10.nsub (Scaled.ofNat 1))))
    (r75_PH .high) (r75_PB .high e) (r75_PGminus .high) (r75_PD .high)
    (r75_RH .high) (r75_RB .high e) r75_RGminus r75_RD
private theorem r75_NG_rep (e : Split) : (r75_NG e).Rep (NG e) :=
  r75_num4_rep ((r75_highB_rep e).nadd ((r75_l_rep .high).nmul (r75_C10_rep.nsub Scaled.rep_one)))
    (r75_PH_rep .high) (r75_PB_rep .high e) (r75_PGminus_rep .high) (r75_PD_rep .high)
    (r75_RH_rep .high) (r75_RB_rep .high e) r75_RGminus_rep r75_RD_rep
private def r75_NB (e : Split) : Scaled :=
  r75_num4 ((r75_highB e).nadd (r75_qStar.nmul (r75_C10.nsub (Scaled.ofNat 1))))
    (r75_PH .high) (r75_PG .high) (r75_PBminus .high e) (r75_PD .high)
    (r75_RH .high) (r75_RG .high) (r75_RBminus e) r75_RD
private theorem r75_NB_rep (e : Split) : (r75_NB e).Rep (NB e) :=
  r75_num4_rep ((r75_highB_rep e).nadd (r75_qStar_rep.nmul (r75_C10_rep.nsub Scaled.rep_one)))
    (r75_PH_rep .high) (r75_PG_rep .high) (r75_PBminus_rep .high e) (r75_PD_rep .high)
    (r75_RH_rep .high) (r75_RG_rep .high) (r75_RBminus_rep e) r75_RD_rep
private def r75_secantR : Scaled :=
  (⟨[379],500⟩ : Scaled).nadd (((⟨[163],250⟩ : Scaled).nmul (r75_c .high)).nmul r75_C4)
private theorem r75_secantR_rep : r75_secantR.Rep secantR :=
  (r75_repC 379 500 (by norm_num) (by norm_num)).nadd
    (((r75_repC 163 250 (by norm_num) (by norm_num)).nmul (r75_c_rep .high)).nmul r75_C4_rep)
private def r75_dbar : Scaled := ⟨[199607033],500000000⟩
private theorem r75_dbar_rep : r75_dbar.Rep (C dbar) :=
  r75_repC 199607033 500000000 (by norm_num) (by norm_num [dbar,cbar])
private def r75_K : Scaled := ⟨[13],12⟩
private theorem r75_K_rep : r75_K.Rep (C K) := r75_repC 13 12 (by norm_num) (by norm_num [K])
private def r75_NZ : Family → Split → Scaled
  | .low,e => r75_num3 (((r75_C10.nkmul ((r75_lowB e).nadd r75_dbar)).nadd (r75_K.nmul r75_S11)).nsub r75_dbar)
      ((r75_C12.nksq).nkmul (r75_PH .low)) ((r75_C12.nksq).nkmul (r75_PG .low))
      ((r75_C12.nksq).nkmul (r75_PB .low e))
      (r75_C4.nkmul (r75_RH .low)) (r75_C4.nkmul (r75_RG .low)) (r75_C4.nkmul (r75_RB .low e))
  | .high,e => r75_num4 (((r75_C10.nkmul ((r75_highB e).nsub (Scaled.ofNat 1))).nadd
        (Scaled.ofNat 1)).nadd (r75_K.nmul r75_S11))
      ((r75_C12.nksq).nkmul (r75_PH .high)) ((r75_C12.nksq).nkmul (r75_PG .high))
      ((r75_C12.nksq).nkmul (r75_PB .high e))
      ((Scaled.ofNat 1).nadd (((r75_c .high).nksq).nkmul (r75_C12.nksq)))
      (r75_C4.nkmul (r75_RH .high)) (r75_C4.nkmul (r75_RG .high)) (r75_C4.nkmul (r75_RB .high e))
      r75_secantR
private theorem r75_NZ_rep : ∀ f e,(r75_NZ f e).Rep (NZ f e)
  | .low,e => by
    simp only [NZ,↓reduceIte]
    exact r75_num3_rep (((r75_C10_rep.nkmul ((r75_lowB_rep e).nadd r75_dbar_rep)).nadd
        (r75_K_rep.nmul r75_S11_rep)).nsub r75_dbar_rep)
      ((r75_C12_rep.nksq).nkmul (r75_PH_rep .low)) ((r75_C12_rep.nksq).nkmul (r75_PG_rep .low))
      ((r75_C12_rep.nksq).nkmul (r75_PB_rep .low e))
      (r75_C4_rep.nkmul (r75_RH_rep .low)) (r75_C4_rep.nkmul (r75_RG_rep .low))
      (r75_C4_rep.nkmul (r75_RB_rep .low e))
  | .high,e => by
    simp only [NZ,reduceCtorEq,↓reduceIte]
    exact r75_num4_rep (((r75_C10_rep.nkmul ((r75_highB_rep e).nsub Scaled.rep_one)).nadd
        Scaled.rep_one).nadd (r75_K_rep.nmul r75_S11_rep))
      ((r75_C12_rep.nksq).nkmul (r75_PH_rep .high)) ((r75_C12_rep.nksq).nkmul (r75_PG_rep .high))
      ((r75_C12_rep.nksq).nkmul (r75_PB_rep .high e))
      (Scaled.rep_one.nadd (((r75_c_rep .high).nksq).nkmul (r75_C12_rep.nksq)))
      (r75_C4_rep.nkmul (r75_RH_rep .high)) (r75_C4_rep.nkmul (r75_RG_rep .high))
      (r75_C4_rep.nkmul (r75_RB_rep .high e)) r75_secantR_rep
private def r75_dN (P r f : Scaled) : Scaled :=
  let A := P.nadd (r.nksq)
  let D := ((Scaled.ofNat 1).nadd (((r75_c .high).nksq).nkmul (r75_C12.nksq))).nadd (r75_secantR.nksq)
  ((((((⟨[1978787507],500000000⟩ : Scaled).nmul r).nkmul f).nkmul (r75_C10.nksq)).nkmul D).nadd
    ((((⟨[1978787507],500000000⟩ : Scaled).nmul r75_secantR).nkmul r75_S11).nkmul A)).nsub
    (((r75_K.nadd r75_S9).nkmul A).nkmul D)
private theorem r75_dN2R : (⟨[1978787507],500000000⟩ : Scaled).Rep (C (2*Rlo)) :=
  r75_repC 1978787507 500000000 (by norm_num) (by norm_num [Rlo])
private theorem r75_dND : (((Scaled.ofNat 1).nadd (((r75_c .high).nksq).nkmul (r75_C12.nksq))).nadd
    (r75_secantR.nksq)).Rep (1+(c .high)^2*C12^2+secantR^2) :=
  (Scaled.rep_one.nadd (((r75_c_rep .high).nksq).nkmul (r75_C12_rep.nksq))).nadd
    (r75_secantR_rep.nksq)

/-! ### General reductions of the certificate statements to integer facts -/

/-- A polynomial of degree below `k+n` is its first `k` monomials plus its tail. -/
private theorem r75_split {p : ℚ[X]} (k n : ℕ) (hp : p.natDegree<k+n) :
    p=(∑ i ∈ Finset.range k,C (p.coeff i)*X^i)+PowerTailBounds.tail p k n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hp]
  rw [Finset.sum_range_add,PowerTailBounds.tail,
    Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+k))*X^(j+k)) n]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_comm k j]

private theorem r75_reverse_eq (a : ℚ) (p : ℚ[X]) :
    DirectedPowerBounds.reverse a p=centered (a+1) (a-1) p := by
  rw [DirectedPowerBounds.reverse,centered,affine,show (a+1+(a-1))/2=a by ring,
    show (a-1-(a+1))/2=-1 by ring,map_neg,map_one,neg_one_mul,sub_eq_add_neg]

/-- The constant `p.eval a` from the centered polynomial at the point `a`. -/
private theorem r75_rep_eval {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) : (S.kcenter num den s 0).Rep (C (p.eval a)) := by
  have hc := hp.kcentered num den s 0 (a:=a) (b:=a) hden (by rw [← ha]; ring) (by simp)
  have he : centered a a p=C (p.eval a) := by
    rw [centered,affine,sub_self,zero_div,map_zero,zero_mul,add_zero,add_self_div_two,comp_C]
  rwa [he] at hc

private theorem r75_eval_lt {S : Scaled} {q : ℚ} (hS : S.Rep (C q)) (hs : S.s≠0) {r : ℚ}
    {a : ℤ} {b : ℕ} (hr : r=a/b) (hb : 0<b) (h : a*S.s<S.l.getD 0 0*b) : r<q := by
  have h0 := hS.coeff hs 0
  rw [coeff_C_zero] at h0
  rw [h0,hr,div_lt_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast Nat.pos_of_ne_zero hs)]
  exact_mod_cast h

/-- A rational number below an integer fraction, from an integer inequality. -/
private theorem r75_lt_frac {r : ℚ} {a N : ℤ} {b D : ℕ} (hr : r=a/b) (hb : 0<b) (hD : 0<D)
    (h : a*D<N*b) : r<(N:ℚ)/(D:ℚ) := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  rw [hr,div_lt_div_iff₀ hb' hD']
  exact_mod_cast h

/-- `r < lowerOn`-type bound: a reserve below an integer over the scale. -/
private theorem r75_lt_scale {r : ℚ} {a N : ℤ} {b S n : ℕ} (hr : r=a/b) (hb : 0<b) (hS : S≠0)
    (h : a*(S*2^n)<N*b*2) : r<(N:ℚ)/((S:ℚ)*2^n/2) := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hS' : (0:ℚ)<(S:ℚ)*2^n/2 := by
    have : (0:ℚ)<S := by exact_mod_cast Nat.pos_of_ne_zero hS
    positivity
  rw [hr,div_lt_div_iff₀ hb' hS']
  have h' : ((a*(S*2^n):ℤ):ℚ)<((N*b*2:ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- An `upperOn`-type bound below a rational number. -/
private theorem r75_scale_lt {r : ℚ} {a N : ℤ} {b S n : ℕ} (hr : r=a/b) (hb : 0<b) (hS : S≠0)
    (h : N*b*2<a*(S*2^n)) : (N:ℚ)/((S:ℚ)*2^n/2)<r := by
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have hS' : (0:ℚ)<(S:ℚ)*2^n/2 := by
    have : (0:ℚ)<S := by exact_mod_cast Nat.pos_of_ne_zero hS
    positivity
  rw [hr,div_lt_div_iff₀ hS' hb']
  have h' : ((N*b*2:ℤ):ℚ)<((a*(S*2^n):ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

private theorem r75_coeff_sub_negnorm {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (j0 k n m : ℕ) (hm : 0 < m) {r : ℚ} (hr : r*m=1) :
    p.coeff j0-DirectedPowerBounds.negativeNorm p k n r=
      ((c.l.getD j0 0*(m:ℤ)^n-
        ∑ j : Fin n,max (-c.l.getD (j.val+k) 0) 0*(m:ℤ)^(n-1-j.val) : ℤ):ℚ)/
        ((c.s*m^n:ℕ):ℚ) := by
  have hs' : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  have hr' : r=1/m := by field_simp; linarith
  unfold DirectedPowerBounds.negativeNorm
  simp only [hc.coeff hs]
  push_cast
  rw [sub_div,Finset.sum_div]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := j.isLt
    have hpow : (m:ℚ)^n=m^(n-1-j.val)*m^(j.val+1) := by
      rw [← pow_add]
      congr 1
      omega
    have key : max (-(((c.l.getD (j.val+k) 0:ℤ):ℚ)/c.s)) 0=
        max (-((c.l.getD (j.val+k) 0:ℤ):ℚ)) 0/c.s := by
      rw [← max_div_div_right hs'.le,zero_div,neg_div]
    rw [key,hr',hpow,div_pow,one_pow]
    field_simp

/-- The Chebyshev quadratic part of an expansion. -/
private theorem r75_quad_id {p : ℚ[X]} {D : ℕ} (hD : 2≤D) (hp : p=expansion D p) :
    p=C (coefficient D p 0-coefficient D p 2)+C (coefficient D p 1)*X+
      C (2*coefficient D p 2)*X^2+tail (coefficient D p) 3 (D-2) := by
  obtain ⟨n,rfl⟩ : ∃ n,D=n+2 := ⟨D-2,by omega⟩
  conv_lhs => rw [hp]
  rw [expansion,series,tail,Fin.sum_univ_succ,Fin.sum_univ_succ,show n+2-2=n by omega]
  simp only [Fin.val_zero,Fin.val_succ,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,Nat.cast_zero,
    zero_add]
  have hrest : ∀ j : Fin n,C (coefficient (n+2) p (j.val+1+1+1))*
      Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+1+1+1)=
      C (coefficient (n+2) p (j.val+3))*Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+3) := fun j => by
    ring_nf
  simp only [hrest,Polynomial.Chebyshev.T_one,show (1:ℤ)+1=2 by norm_num,
    Polynomial.Chebyshev.T_two,map_sub,map_mul,map_ofNat]
  ring

/-- The Chebyshev cubic part of an expansion. -/
private theorem r75_cubic_id {p : ℚ[X]} {D : ℕ} (hD : 3≤D) (hp : p=expansion D p) :
    p=C (coefficient D p 0-coefficient D p 2)+C (coefficient D p 1-3*coefficient D p 3)*X+
      C (2*coefficient D p 2)*X^2+C (4*coefficient D p 3)*X^3+
      tail (coefficient D p) 4 (D-3) := by
  obtain ⟨n,rfl⟩ : ∃ n,D=n+3 := ⟨D-3,by omega⟩
  conv_lhs => rw [hp]
  rw [expansion,series,tail,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,
    show n+3-3=n by omega]
  simp only [Fin.val_zero,Fin.val_succ,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,Nat.cast_zero,
    zero_add]
  have hrest : ∀ j : Fin n,C (coefficient (n+3) p (j.val+1+1+1+1))*
      Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+1+1+1+1)=
      C (coefficient (n+3) p (j.val+4))*Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+4) := fun j => by
    ring_nf
  have hT3 : Polynomial.Chebyshev.T ℚ 3=4*X^3-3*X := by
    have h := Polynomial.Chebyshev.T_add_two ℚ 1
    rw [show (1:ℤ)+2=3 by norm_num,show (1:ℤ)+1=2 by norm_num,Polynomial.Chebyshev.T_two,
      Polynomial.Chebyshev.T_one] at h
    rw [h]
    ring
  simp only [hrest,Polynomial.Chebyshev.T_one,show (1:ℤ)+1=2 by norm_num,show (2:ℤ)+1=3 by norm_num,
    Polynomial.Chebyshev.T_two,map_sub,map_mul,map_ofNat]
  rw [hT3]
  ring

private theorem r75_tailNorm_div (B : ℕ→ℤ) {U : ℚ} (hU : 0<U) (start count : ℕ) :
    tailNorm (fun j => (B j:ℚ)/U) start count=
      ((∑ j : Fin count,|B (j.val+start)| : ℤ):ℚ)/U := by
  unfold tailNorm
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [abs_div,abs_of_pos hU]

/-- The quadratic reserve of scaled integer coefficients, as an integer inequality. -/
private theorem r75_quad_reserve (B : ℕ→ℤ) {S n : ℕ} (hS : S≠0) (count : ℕ) {r : ℚ} {a : ℤ}
    {b : ℕ} (hr : r=a/b) (hb : 0<b) (hB : 0<B 2)
    (h : a*(4*B 2*(S*2^n))<(8*B 2*(B 0-B 2-∑ j : Fin count,|B (j.val+3)|)-B 1^2)*b) :
    r<quadraticReserve (fun j => (B j:ℚ)/((S:ℚ)*2^n/2)) count := by
  have hU : (0:ℚ)<(S:ℚ)*2^n/2 := by
    have : (0:ℚ)<S := by exact_mod_cast Nat.pos_of_ne_zero hS
    positivity
  have hB' : (0:ℚ)<B 2 := by exact_mod_cast hB
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  unfold quadraticReserve
  rw [r75_tailNorm_div B hU]
  have e : (B 0:ℚ)/((S:ℚ)*2^n/2)-(B 2:ℚ)/((S:ℚ)*2^n/2)-((B 1:ℚ)/((S:ℚ)*2^n/2))^2/
      (8*((B 2:ℚ)/((S:ℚ)*2^n/2)))-((∑ j : Fin count,|B (j.val+3)| : ℤ):ℚ)/((S:ℚ)*2^n/2)=
      (((8*B 2*(B 0-B 2-∑ j : Fin count,|B (j.val+3)|)-B 1^2 : ℤ)):ℚ)/(4*B 2*(S*2^n)) := by
    push_cast
    field_simp
    try ring
  rw [e,hr,div_lt_div_iff₀ hb' (by positivity)]
  exact_mod_cast h

/-- The cubic curvature and reserve of scaled integer coefficients. -/
private theorem r75_cubic_reserve (B : ℕ→ℤ) {S n : ℕ} (hS : S≠0) (count : ℕ)
    {r : ℚ} {a : ℤ} {b : ℕ} (hr : r=a/b) (hb : 0<b) {r' : ℚ} {a' : ℤ} {b' : ℕ}
    (hr' : r'=a'/b') (hb' : 0<b') (hM : 0<2*B 2-4*|B 3|)
    (hc : a'*(S*2^n)<2*(2*B 2-4*|B 3|)*b')
    (h : a*(2*(2*B 2-4*|B 3|)*(S*2^n))<
      (4*(2*B 2-4*|B 3|)*(B 0-B 2-∑ j : Fin count,|B (j.val+4)|)-(B 1-3*B 3)^2)*b) :
    r'<2*((B 2:ℚ)/((S:ℚ)*2^n/2))-4*|(B 3:ℚ)/((S:ℚ)*2^n/2)| ∧
    r<cubicReserve (fun j => (B j:ℚ)/((S:ℚ)*2^n/2)) count := by
  have hS' : (0:ℚ)<S := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hU : (0:ℚ)<(S:ℚ)*2^n/2 := by positivity
  have hM' : (0:ℚ)<2*B 2-4*|(B 3:ℚ)| := by exact_mod_cast hM
  have hbq : (0:ℚ)<b := by exact_mod_cast hb
  have hbq' : (0:ℚ)<b' := by exact_mod_cast hb'
  have habs : |(B 3:ℚ)/((S:ℚ)*2^n/2)|=|(B 3:ℚ)|/((S:ℚ)*2^n/2) := by
    rw [abs_div,abs_of_pos hU]
  constructor
  · rw [habs]
    have e : 2*((B 2:ℚ)/((S:ℚ)*2^n/2))-4*(|(B 3:ℚ)|/((S:ℚ)*2^n/2))=
        2*(2*B 2-4*|(B 3:ℚ)|)/(S*2^n) := by
      field_simp
      try ring
    rw [e,hr',div_lt_div_iff₀ hbq' (by positivity)]
    have h' : ((a'*(S*2^n):ℤ):ℚ)<((2*(2*B 2-4*|B 3|)*b':ℤ):ℚ) := by exact_mod_cast hc
    push_cast at h' ⊢
    linarith
  · unfold cubicReserve
    rw [r75_tailNorm_div B hU,habs]
    have e : (B 0:ℚ)/((S:ℚ)*2^n/2)-(B 2:ℚ)/((S:ℚ)*2^n/2)-
        ((B 1:ℚ)/((S:ℚ)*2^n/2)-3*((B 3:ℚ)/((S:ℚ)*2^n/2)))^2/
        (4*(2*((B 2:ℚ)/((S:ℚ)*2^n/2))-4*(|(B 3:ℚ)|/((S:ℚ)*2^n/2))))-
        ((∑ j : Fin count,|B (j.val+4)| : ℤ):ℚ)/((S:ℚ)*2^n/2)=
        ((4*(2*B 2-4*|B 3|)*(B 0-B 2-∑ j : Fin count,|B (j.val+4)|)-(B 1-3*B 3)^2 : ℤ):ℚ)/
          (2*(2*B 2-4*|(B 3:ℚ)|)*(S*2^n)) := by
      push_cast
      field_simp
      try ring
    rw [e,hr,div_lt_div_iff₀ hbq (by positivity)]
    have h' : ((a*(2*(2*B 2-4*|B 3|)*(S*2^n)):ℤ):ℚ)<
        (((4*(2*B 2-4*|B 3|)*(B 0-B 2-∑ j : Fin count,|B (j.val+4)|)-(B 1-3*B 3)^2)*b:ℤ):ℚ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    linarith

/-! ### Derivatives of integer coefficient lists -/

private def r75_dl : ℕ→List ℤ→List ℤ
  | _,[] => []
  | n,a :: l => ((n:ℤ)*a) :: r75_dl (n+1) l

private theorem r75_dl_getD : ∀ (n : ℕ) (l : List ℤ) (i : ℕ),
    (r75_dl n l).getD i 0=((n+i:ℕ):ℤ)*l.getD i 0
  | _,[],i => by simp [r75_dl]
  | n,a :: l,0 => by simp [r75_dl]
  | n,a :: l,i+1 => by
    simp only [r75_dl,List.getD_cons_succ,r75_dl_getD (n+1) l i]
    congr 2
    omega

private def r75_deriv (c : Scaled) : Scaled := ⟨r75_dl 1 c.l.tail,c.s⟩

private theorem r75_deriv_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r75_deriv c).Rep (derivative p) := by
  unfold Scaled.Rep at *
  have hd : WholeIntervalPolynomial.Certificate.toPoly (r75_dl 1 c.l.tail)=
      derivative (WholeIntervalPolynomial.Certificate.toPoly c.l) := by
    ext i
    rw [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_derivative,
      WholeIntervalPolynomial.Certificate.coeff_toPoly,r75_dl_getD]
    cases c.l with
    | nil => simp
    | cons a l =>
      simp only [List.tail_cons,List.getD_cons_succ]
      push_cast
      ring
  rw [r75_deriv,hd,hc,derivative_C_mul]

def directPolynomial : Direct → ℚ[X]
  | .lowTSH => NSH .atT | .lowTSG => NSG .atT | .lowAM => NM .atA
  | .lowASH => NSH .atA | .lowASG => NSG .atA
  | .highTB => NB .atT | .highAB => NB .atA
  | .derivativeH => derivativeNumerator true | .derivativeG => derivativeNumerator false
def directFamily : Direct → Family
  | .lowTSH => .low | .lowTSG => .low | .lowAM => .low
  | .lowASH => .low | .lowASG => .low | _ => .high
def directDegree : Direct → ℕ
  | .lowTSH => 30 | .lowTSG => 32 | .lowAM => 21 | .lowASH => 16 | .lowASG => 18
  | .highTB => 41 | .highAB => 32 | .derivativeH => 58 | .derivativeG => 61
def directReserve : Direct → ℚ
  | .lowTSH => 3021758/10000000 | .lowTSG => 1617320/10000000
  | .lowAM => 475408/10000000 | .lowASH => 3024216/10000000
  | .lowASG => 1682265/10000000 | .highTB => 16343/10000000
  | .highAB => 669354/10000000 | .derivativeH => 5310/10000
  | .derivativeG => 4744/100000

private theorem r75_low_mem {θ : ℝ} (hθ : θ∈Set.Icc (0:ℝ) (1/6)) :
    θ∈Set.Icc ((0:ℚ):ℝ) ((L:ℚ):ℝ) := by
  norm_num [L]
  exact hθ

private theorem r75_high_mem {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    θ∈Set.Icc ((L:ℚ):ℝ) ((h:ℚ):ℝ) := by
  norm_num [L,h]
  exact hθ

private theorem r75_lower_lt {c : Scaled} {a b : ℚ} {p : ℚ[X]} {D : ℕ}
    (hc : c.Rep (centered a b p)) (hs : c.s≠0) (hl : c.l.length≤D+1) {r : ℚ} {x : ℤ} {y : ℕ}
    (hr : r=x/y) (hy : 0<y)
    (h : x*(c.s*2^c.l.length)<WholeIntervalPolynomial.Certificate.lowerZ D
      (fun j => (WholeIntervalPolynomial.Certificate.chebList c.l).getD j 0)*y*2) :
    r<lowerOn D a b p := by
  rw [lowerOn_eq_of_rep hc hs hl]
  exact r75_lt_scale hr hy hs h

private theorem r75_upper_lt {c : Scaled} {a b : ℚ} {p : ℚ[X]} {D : ℕ}
    (hc : c.Rep (centered a b p)) (hs : c.s≠0) (hl : c.l.length≤D+1) {r : ℚ} {x : ℤ} {y : ℕ}
    (hr : r=x/y) (hy : 0<y)
    (h : WholeIntervalPolynomial.Certificate.upperZ D
      (fun j => (WholeIntervalPolynomial.Certificate.chebList c.l).getD j 0)*y*2<x*(c.s*2^c.l.length)) :
    upperOn D a b p<r := by
  rw [upperOn_eq_of_rep hc hs hl]
  exact r75_scale_lt hr hy hs h

/-! ### Centering and the integer facts of each certificate -/

private theorem r75_cen_low {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r75_nrm (S.kcenter 1 12 1 1)).Rep (centered 0 L p) :=
  r75_nrm_rep (hp.kcentered 1 12 1 1 (by norm_num) (by norm_num [L]) (by norm_num [L]))
private theorem r75_cen_high {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r75_nrm (S.kcenter 1 30 13 8)).Rep (centered L h p) :=
  r75_nrm_rep (hp.kcentered 1 30 13 8 (by norm_num) (by norm_num [L,h]) (by norm_num [L,h]))
private theorem r75_cen_rev {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r75_nrm (S.kcenter 1 6 1 (-6))).Rep (DirectedPowerBounds.reverse L p) := by
  rw [r75_reverse_eq]
  exact r75_nrm_rep (hp.kcentered 1 6 1 (-6) (by norm_num) (by norm_num [L]) (by norm_num [L]))
private theorem r75_cen_evalL {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r75_nrm (S.kcenter 1 6 1 0)).Rep (C (p.eval L)) :=
  r75_nrm_rep (r75_rep_eval hp 1 6 1 (by norm_num) (by norm_num [L]))

private theorem r75_dNH_rep :
    (r75_dN (r75_PH .high) (r75_RH .high) (r75_k .high)).Rep (derivativeNumerator true) := by
  simp only [derivativeNumerator,↓reduceIte,r75_dN]
  have hA := (r75_PH_rep .high).nadd ((r75_RH_rep .high).nksq)
  exact ((((((r75_dN2R.nmul (r75_RH_rep .high)).nkmul (r75_k_rep .high)).nkmul
    (r75_C10_rep.nksq)).nkmul r75_dND).nadd (((r75_dN2R.nmul r75_secantR_rep).nkmul
      r75_S11_rep).nkmul hA)).nsub (((r75_K_rep.nadd r75_S9_rep).nkmul hA).nkmul r75_dND))
private theorem r75_dNG_rep :
    (r75_dN (r75_PG .high) (r75_RG .high) ((r75_k .high).nkmul (r75_l .high))).Rep
      (derivativeNumerator false) := by
  simp only [derivativeNumerator,Bool.false_eq_true,↓reduceIte,r75_dN]
  have hA := (r75_PG_rep .high).nadd ((r75_RG_rep .high).nksq)
  exact ((((((r75_dN2R.nmul (r75_RG_rep .high)).nkmul ((r75_k_rep .high).nkmul (r75_l_rep .high))).nkmul
    (r75_C10_rep.nksq)).nkmul r75_dND).nadd (((r75_dN2R.nmul r75_secantR_rep).nkmul
      r75_S11_rep).nkmul hA)).nsub (((r75_K_rep.nadd r75_S9_rep).nkmul hA).nkmul r75_dND))

private def r75_Z_lowTSH : Scaled := r75_nrm ((r75_NSH .atT).kcenter 1 12 1 1)
private theorem r75_Z_lowTSH_rep : r75_Z_lowTSH.Rep (centered 0 L (NSH .atT)) :=
  r75_cen_low (r75_NSH_rep .atT)
private theorem r75_F_lowTSH : r75_Z_lowTSH.s≠0 ∧ r75_Z_lowTSH.l.length≤30+1 ∧
    3021758*(r75_Z_lowTSH.s*2^r75_Z_lowTSH.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 30 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTSH.l).getD j 0)*10000000*2 := by
  decide +kernel

private def r75_Z_lowTSG : Scaled := r75_nrm ((r75_NSG .atT).kcenter 1 12 1 1)
private theorem r75_Z_lowTSG_rep : r75_Z_lowTSG.Rep (centered 0 L (NSG .atT)) :=
  r75_cen_low (r75_NSG_rep .atT)
private theorem r75_F_lowTSG : r75_Z_lowTSG.s≠0 ∧ r75_Z_lowTSG.l.length≤32+1 ∧
    1617320*(r75_Z_lowTSG.s*2^r75_Z_lowTSG.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 32 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTSG.l).getD j 0)*10000000*2 := by
  decide +kernel

private def r75_Z_lowAM : Scaled := r75_nrm ((r75_NM .atA).kcenter 1 12 1 1)
private theorem r75_Z_lowAM_rep : r75_Z_lowAM.Rep (centered 0 L (NM .atA)) :=
  r75_cen_low (r75_NM_rep .atA)
private theorem r75_F_lowAM : r75_Z_lowAM.s≠0 ∧ r75_Z_lowAM.l.length≤21+1 ∧
    475408*(r75_Z_lowAM.s*2^r75_Z_lowAM.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 21 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_lowAM.l).getD j 0)*10000000*2 := by
  decide +kernel

private def r75_Z_lowASH : Scaled := r75_nrm ((r75_NSH .atA).kcenter 1 12 1 1)
private theorem r75_Z_lowASH_rep : r75_Z_lowASH.Rep (centered 0 L (NSH .atA)) :=
  r75_cen_low (r75_NSH_rep .atA)
private theorem r75_F_lowASH : r75_Z_lowASH.s≠0 ∧ r75_Z_lowASH.l.length≤16+1 ∧
    3024216*(r75_Z_lowASH.s*2^r75_Z_lowASH.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 16 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_lowASH.l).getD j 0)*10000000*2 := by
  decide +kernel

private def r75_Z_lowASG : Scaled := r75_nrm ((r75_NSG .atA).kcenter 1 12 1 1)
private theorem r75_Z_lowASG_rep : r75_Z_lowASG.Rep (centered 0 L (NSG .atA)) :=
  r75_cen_low (r75_NSG_rep .atA)
private theorem r75_F_lowASG : r75_Z_lowASG.s≠0 ∧ r75_Z_lowASG.l.length≤18+1 ∧
    1682265*(r75_Z_lowASG.s*2^r75_Z_lowASG.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 18 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_lowASG.l).getD j 0)*10000000*2 := by
  decide +kernel

private def r75_Z_highTB : Scaled := r75_nrm ((r75_NB .atT).kcenter 1 30 13 8)
private theorem r75_Z_highTB_rep : r75_Z_highTB.Rep (centered L h (NB .atT)) :=
  r75_cen_high (r75_NB_rep .atT)
private theorem r75_F_highTB : r75_Z_highTB.s≠0 ∧ r75_Z_highTB.l.length≤41+1 ∧
    16343*(r75_Z_highTB.s*2^r75_Z_highTB.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 41 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_highTB.l).getD j 0)*10000000*2 := by
  decide +kernel

private def r75_Z_highAB : Scaled := r75_nrm ((r75_NB .atA).kcenter 1 30 13 8)
private theorem r75_Z_highAB_rep : r75_Z_highAB.Rep (centered L h (NB .atA)) :=
  r75_cen_high (r75_NB_rep .atA)
private theorem r75_F_highAB : r75_Z_highAB.s≠0 ∧ r75_Z_highAB.l.length≤32+1 ∧
    669354*(r75_Z_highAB.s*2^r75_Z_highAB.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 32 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_highAB.l).getD j 0)*10000000*2 := by
  decide +kernel

private def r75_Z_derivativeH : Scaled := r75_nrm ((r75_dN (r75_PH .high) (r75_RH .high) (r75_k .high)).kcenter 1 30 13 8)
private theorem r75_Z_derivativeH_rep : r75_Z_derivativeH.Rep (centered L h (derivativeNumerator true)) :=
  r75_cen_high (r75_dNH_rep)
private theorem r75_F_derivativeH : r75_Z_derivativeH.s≠0 ∧ r75_Z_derivativeH.l.length≤58+1 ∧
    5310*(r75_Z_derivativeH.s*2^r75_Z_derivativeH.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 58 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_derivativeH.l).getD j 0)*10000*2 := by
  decide +kernel

private def r75_Z_derivativeG : Scaled := r75_nrm ((r75_dN (r75_PG .high) (r75_RG .high) ((r75_k .high).nkmul (r75_l .high))).kcenter 1 30 13 8)
private theorem r75_Z_derivativeG_rep : r75_Z_derivativeG.Rep (centered L h (derivativeNumerator false)) :=
  r75_cen_high (r75_dNG_rep)
private theorem r75_F_derivativeG : r75_Z_derivativeG.s≠0 ∧ r75_Z_derivativeG.l.length≤61+1 ∧
    4744*(r75_Z_derivativeG.s*2^r75_Z_derivativeG.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 61 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_derivativeG.l).getD j 0)*100000*2 := by
  decide +kernel

theorem direct_identity (e : Direct) :
    centered (left (directFamily e)) (right (directFamily e)) (directPolynomial e)=
      expansion (directDegree e)
        (centered (left (directFamily e)) (right (directFamily e)) (directPolynomial e)) := by
  cases e
  · exact r75_Z_lowTSH_rep.eq_expansion r75_F_lowTSH.1 r75_F_lowTSH.2.1
  · exact r75_Z_lowTSG_rep.eq_expansion r75_F_lowTSG.1 r75_F_lowTSG.2.1
  · exact r75_Z_lowAM_rep.eq_expansion r75_F_lowAM.1 r75_F_lowAM.2.1
  · exact r75_Z_lowASH_rep.eq_expansion r75_F_lowASH.1 r75_F_lowASH.2.1
  · exact r75_Z_lowASG_rep.eq_expansion r75_F_lowASG.1 r75_F_lowASG.2.1
  · exact r75_Z_highTB_rep.eq_expansion r75_F_highTB.1 r75_F_highTB.2.1
  · exact r75_Z_highAB_rep.eq_expansion r75_F_highAB.1 r75_F_highAB.2.1
  · exact r75_Z_derivativeH_rep.eq_expansion r75_F_derivativeH.1 r75_F_derivativeH.2.1
  · exact r75_Z_derivativeG_rep.eq_expansion r75_F_derivativeG.1 r75_F_derivativeG.2.1

theorem direct_reserve (e : Direct) : directReserve e<
    lowerOn (directDegree e) (left (directFamily e)) (right (directFamily e))
      (directPolynomial e) := by
  cases e
  · exact r75_lower_lt r75_Z_lowTSH_rep r75_F_lowTSH.1 r75_F_lowTSH.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_lowTSH.2.2
  · exact r75_lower_lt r75_Z_lowTSG_rep r75_F_lowTSG.1 r75_F_lowTSG.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_lowTSG.2.2
  · exact r75_lower_lt r75_Z_lowAM_rep r75_F_lowAM.1 r75_F_lowAM.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_lowAM.2.2
  · exact r75_lower_lt r75_Z_lowASH_rep r75_F_lowASH.1 r75_F_lowASH.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_lowASH.2.2
  · exact r75_lower_lt r75_Z_lowASG_rep r75_F_lowASG.1 r75_F_lowASG.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_lowASG.2.2
  · exact r75_lower_lt r75_Z_highTB_rep r75_F_highTB.1 r75_F_highTB.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_highTB.2.2
  · exact r75_lower_lt r75_Z_highAB_rep r75_F_highAB.1 r75_F_highAB.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_highAB.2.2
  · exact r75_lower_lt r75_Z_derivativeH_rep r75_F_derivativeH.1 r75_F_derivativeH.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_derivativeH.2.2
  · exact r75_lower_lt r75_Z_derivativeG_rep r75_F_derivativeG.1 r75_F_derivativeG.2.1 (by norm_num [directReserve])
      (by norm_num) r75_F_derivativeG.2.2

theorem direct_positive (e : Direct) {θ : ℝ}
    (hθ : θ∈Set.Icc (left (directFamily e):ℝ) (right (directFamily e):ℝ)) :
    (directReserve e:ℝ)<aeval θ (directPolynomial e) := by
  apply positive_on_interval _ (direct_identity e) (direct_reserve e) hθ
  cases e <;> norm_num [directFamily,left,right,L,h]

def lowPowerPolynomial (atZ : Bool) : ℚ[X] := if atZ then NZ .low .atT else NH .low .atT
def lowPowerDegree : Bool → ℕ | false => 33 | true => 64
def lowPowerReserve : Bool → ℚ | false => 18458/10000000 | true => 18219/10000000
def lowReverse (atZ : Bool) : ℚ[X] := DirectedPowerBounds.reverse L (lowPowerPolynomial atZ)
def lowEndpointAggregate (atZ : Bool) : ℚ := (lowReverse atZ).coeff 0-
  DirectedPowerBounds.negativeNorm (lowReverse atZ) 1 (lowPowerDegree atZ) L

private def r75_Z_lowPower_false : Scaled := r75_nrm ((r75_NH .low .atT).kcenter 1 6 1 (-6))
private theorem r75_Z_lowPower_false_rep : r75_Z_lowPower_false.Rep (DirectedPowerBounds.reverse L (NH .low .atT)) :=
  r75_cen_rev (r75_NH_rep .low .atT)
private theorem r75_F_lowPower_false : r75_Z_lowPower_false.s≠0 ∧ r75_Z_lowPower_false.l.length≤33+1 ∧
    (18458:ℤ)*((r75_Z_lowPower_false.s*6^33:ℕ):ℤ)<(r75_Z_lowPower_false.l.getD 0 0*((6:ℕ):ℤ)^33-
      ∑ j : Fin 33,max (-r75_Z_lowPower_false.l.getD (j.val+1) 0) 0*((6:ℕ):ℤ)^(33-1-j.val))*((10000000:ℕ):ℤ) := by
  decide +kernel

private def r75_Z_lowPower_true : Scaled := r75_nrm ((r75_NZ .low .atT).kcenter 1 6 1 (-6))
private theorem r75_Z_lowPower_true_rep : r75_Z_lowPower_true.Rep (DirectedPowerBounds.reverse L (NZ .low .atT)) :=
  r75_cen_rev (r75_NZ_rep .low .atT)
private theorem r75_F_lowPower_true : r75_Z_lowPower_true.s≠0 ∧ r75_Z_lowPower_true.l.length≤64+1 ∧
    (18219:ℤ)*((r75_Z_lowPower_true.s*6^64:ℕ):ℤ)<(r75_Z_lowPower_true.l.getD 0 0*((6:ℕ):ℤ)^64-
      ∑ j : Fin 64,max (-r75_Z_lowPower_true.l.getD (j.val+1) 0) 0*((6:ℕ):ℤ)^(64-1-j.val))*((10000000:ℕ):ℤ) := by
  decide +kernel

theorem low_power_identity (atZ : Bool) : lowReverse atZ=C ((lowReverse atZ).coeff 0)+
    PowerTailBounds.tail (lowReverse atZ) 1 (lowPowerDegree atZ) := by
  cases atZ
  · have h := r75_split 1 33 (lt_of_le_of_lt
      (r75_Z_lowPower_false_rep.natDegree_le r75_F_lowPower_false.1)
      (by have := r75_F_lowPower_false.2.1; omega))
    rw [Finset.sum_range_one,pow_zero,mul_one] at h
    exact h
  · have h := r75_split 1 64 (lt_of_le_of_lt
      (r75_Z_lowPower_true_rep.natDegree_le r75_F_lowPower_true.1)
      (by have := r75_F_lowPower_true.2.1; omega))
    rw [Finset.sum_range_one,pow_zero,mul_one] at h
    exact h

theorem low_power_reserve (atZ : Bool) : lowPowerReserve atZ<lowEndpointAggregate atZ := by
  cases atZ
  · show lowPowerReserve false<(lowReverse false).coeff 0-
      DirectedPowerBounds.negativeNorm (lowReverse false) 1 33 L
    have hc : r75_Z_lowPower_false.Rep (lowReverse false) := r75_Z_lowPower_false_rep
    rw [r75_coeff_sub_negnorm hc r75_F_lowPower_false.1 0 1 33 6 (by norm_num) (r:=L) (by norm_num [L])]
    exact r75_lt_frac (a:=18458) (b:=10000000) (by norm_num [lowPowerReserve]) (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero r75_F_lowPower_false.1) (by norm_num))
      r75_F_lowPower_false.2.2
  · show lowPowerReserve true<(lowReverse true).coeff 0-
      DirectedPowerBounds.negativeNorm (lowReverse true) 1 64 L
    have hc : r75_Z_lowPower_true.Rep (lowReverse true) := r75_Z_lowPower_true_rep
    rw [r75_coeff_sub_negnorm hc r75_F_lowPower_true.1 0 1 64 6 (by norm_num) (r:=L) (by norm_num [L])]
    exact r75_lt_frac (a:=18219) (b:=10000000) (by norm_num [lowPowerReserve]) (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero r75_F_lowPower_true.1) (by norm_num))
      r75_F_lowPower_true.2.2

theorem low_power_positive (atZ : Bool) {θ : ℝ} (hθ : θ∈Set.Icc (0:ℝ) (1/6)) :
    (lowPowerReserve atZ:ℝ)<aeval θ (lowPowerPolynomial atZ) := by
  obtain ⟨x,hx_def⟩ : ∃ x : ℝ,x=1/6-θ := ⟨_,rfl⟩
  have hx : x∈Set.Icc 0 (L:ℝ) := by
    rw [hx_def]
    norm_num [L]
    exact ⟨by linarith [hθ.2],by linarith [hθ.1]⟩
  have ht := DirectedPowerBounds.tail_lower (p:=lowReverse atZ) (k:=0)
    (n:=lowPowerDegree atZ) hx
  have hi := congrArg (fun p : ℚ[X] => aeval x p) (low_power_identity atZ)
  simp only [map_add,aeval_C,eq_ratCast] at hi
  have hr : (lowPowerReserve atZ:ℝ)<(lowEndpointAggregate atZ:ℝ) := by
    exact_mod_cast low_power_reserve atZ
  have hxθ : ((L:ℚ):ℝ)-x=θ := by rw [hx_def]; norm_num [L]
  have he : aeval x (lowReverse atZ)=aeval θ (lowPowerPolynomial atZ) := by
    rw [lowReverse,DirectedPowerBounds.reverse_eval,hxθ]
  rw [he] at hi
  simp only [pow_zero,mul_one,zero_add] at ht
  simp only [lowEndpointAggregate] at hr
  push_cast at hr
  linarith

def quadraticPolynomial : Quadratic → ℚ[X]
  | .lowTM => NM .atT | .highTZ => NZ .high .atT | .highAZ => NZ .high .atA
  | .highQStar => qStar-mu .high .atT
def quadraticFamily : Quadratic → Family | .lowTM => .low | _ => .high
def quadraticDegree : Quadratic → ℕ | .lowTM => 33 | .highTZ => 77 | .highAZ => 54 | .highQStar => 8
def quadraticReserveValue : Quadratic → ℚ
  | .lowTM => 304587/10000000 | .highTZ => 3948/10000000
  | .highAZ => 1815/10000000 | .highQStar => 51799/10000000
def quadraticCoefficient (e : Quadratic) : ℕ → ℚ := coefficient (quadraticDegree e)
  (centered (left (quadraticFamily e)) (right (quadraticFamily e)) (quadraticPolynomial e))

private def r75_Z_lowTM : Scaled := r75_nrm ((r75_NM .atT).kcenter 1 12 1 1)
private theorem r75_Z_lowTM_rep : r75_Z_lowTM.Rep (centered 0 L (NM .atT)) :=
  r75_cen_low (r75_NM_rep .atT)
private theorem r75_F_lowTM : r75_Z_lowTM.s≠0 ∧ r75_Z_lowTM.l.length≤33+1 ∧ 0<(WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTM.l).getD 2 0 ∧
    304587*(4*(WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTM.l).getD 2 0*(r75_Z_lowTM.s*2^r75_Z_lowTM.l.length))<(8*(WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTM.l).getD 2 0*((WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTM.l).getD 0 0-(WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTM.l).getD 2 0-
      ∑ j : Fin 31,|(WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTM.l).getD (j.val+3) 0|)-(WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTM.l).getD 1 0^2)*10000000 := by
  decide +kernel

private def r75_Z_highTZ : Scaled := r75_nrm ((r75_NZ .high .atT).kcenter 1 30 13 8)
private theorem r75_Z_highTZ_rep : r75_Z_highTZ.Rep (centered L h (NZ .high .atT)) :=
  r75_cen_high (r75_NZ_rep .high .atT)
private theorem r75_F_highTZ : r75_Z_highTZ.s≠0 ∧ r75_Z_highTZ.l.length≤77+1 ∧ 0<(WholeIntervalPolynomial.Certificate.chebList r75_Z_highTZ.l).getD 2 0 ∧
    3948*(4*(WholeIntervalPolynomial.Certificate.chebList r75_Z_highTZ.l).getD 2 0*(r75_Z_highTZ.s*2^r75_Z_highTZ.l.length))<(8*(WholeIntervalPolynomial.Certificate.chebList r75_Z_highTZ.l).getD 2 0*((WholeIntervalPolynomial.Certificate.chebList r75_Z_highTZ.l).getD 0 0-(WholeIntervalPolynomial.Certificate.chebList r75_Z_highTZ.l).getD 2 0-
      ∑ j : Fin 75,|(WholeIntervalPolynomial.Certificate.chebList r75_Z_highTZ.l).getD (j.val+3) 0|)-(WholeIntervalPolynomial.Certificate.chebList r75_Z_highTZ.l).getD 1 0^2)*10000000 := by
  decide +kernel

private def r75_Z_highAZ : Scaled := r75_nrm ((r75_NZ .high .atA).kcenter 1 30 13 8)
private theorem r75_Z_highAZ_rep : r75_Z_highAZ.Rep (centered L h (NZ .high .atA)) :=
  r75_cen_high (r75_NZ_rep .high .atA)
private theorem r75_F_highAZ : r75_Z_highAZ.s≠0 ∧ r75_Z_highAZ.l.length≤54+1 ∧ 0<(WholeIntervalPolynomial.Certificate.chebList r75_Z_highAZ.l).getD 2 0 ∧
    1815*(4*(WholeIntervalPolynomial.Certificate.chebList r75_Z_highAZ.l).getD 2 0*(r75_Z_highAZ.s*2^r75_Z_highAZ.l.length))<(8*(WholeIntervalPolynomial.Certificate.chebList r75_Z_highAZ.l).getD 2 0*((WholeIntervalPolynomial.Certificate.chebList r75_Z_highAZ.l).getD 0 0-(WholeIntervalPolynomial.Certificate.chebList r75_Z_highAZ.l).getD 2 0-
      ∑ j : Fin 52,|(WholeIntervalPolynomial.Certificate.chebList r75_Z_highAZ.l).getD (j.val+3) 0|)-(WholeIntervalPolynomial.Certificate.chebList r75_Z_highAZ.l).getD 1 0^2)*10000000 := by
  decide +kernel

private def r75_Z_highQStar : Scaled := r75_nrm ((r75_qStar.nsub (r75_mu .high .atT)).kcenter 1 30 13 8)
private theorem r75_Z_highQStar_rep : r75_Z_highQStar.Rep (centered L h (qStar-mu .high .atT)) :=
  r75_cen_high (r75_qStar_rep.nsub (r75_mu_rep .high .atT))
private theorem r75_F_highQStar : r75_Z_highQStar.s≠0 ∧ r75_Z_highQStar.l.length≤8+1 ∧ 0<(WholeIntervalPolynomial.Certificate.chebList r75_Z_highQStar.l).getD 2 0 ∧
    51799*(4*(WholeIntervalPolynomial.Certificate.chebList r75_Z_highQStar.l).getD 2 0*(r75_Z_highQStar.s*2^r75_Z_highQStar.l.length))<(8*(WholeIntervalPolynomial.Certificate.chebList r75_Z_highQStar.l).getD 2 0*((WholeIntervalPolynomial.Certificate.chebList r75_Z_highQStar.l).getD 0 0-(WholeIntervalPolynomial.Certificate.chebList r75_Z_highQStar.l).getD 2 0-
      ∑ j : Fin 6,|(WholeIntervalPolynomial.Certificate.chebList r75_Z_highQStar.l).getD (j.val+3) 0|)-(WholeIntervalPolynomial.Certificate.chebList r75_Z_highQStar.l).getD 1 0^2)*10000000 := by
  decide +kernel

theorem quadratic_identity (e : Quadratic) :
    centered (left (quadraticFamily e)) (right (quadraticFamily e)) (quadraticPolynomial e)=
      C (quadraticCoefficient e 0-quadraticCoefficient e 2)+C (quadraticCoefficient e 1)*X+
        C (2*quadraticCoefficient e 2)*X^2+tail (quadraticCoefficient e) 3 (quadraticDegree e-2) := by
  cases e
  · exact r75_quad_id (by decide) (r75_Z_lowTM_rep.eq_expansion r75_F_lowTM.1 r75_F_lowTM.2.1)
  · exact r75_quad_id (by decide) (r75_Z_highTZ_rep.eq_expansion r75_F_highTZ.1 r75_F_highTZ.2.1)
  · exact r75_quad_id (by decide) (r75_Z_highAZ_rep.eq_expansion r75_F_highAZ.1 r75_F_highAZ.2.1)
  · exact r75_quad_id (by decide) (r75_Z_highQStar_rep.eq_expansion r75_F_highQStar.1 r75_F_highQStar.2.1)

theorem quadratic_reserve (e : Quadratic) : 0<quadraticCoefficient e 2 ∧
    quadraticReserveValue e<quadraticReserve (quadraticCoefficient e) (quadraticDegree e-2) := by
  cases e
  · have hcoef : quadraticCoefficient .lowTM=fun j =>
        ((WholeIntervalPolynomial.Certificate.chebList r75_Z_lowTM.l).getD j 0:ℚ)/
          (r75_Z_lowTM.s*2^r75_Z_lowTM.l.length/2) :=
      WholeIntervalPolynomial.Certificate.coefficient_centered_eq r75_Z_lowTM_rep r75_F_lowTM.1 r75_F_lowTM.2.1
    rw [hcoef]
    exact ⟨div_pos (by exact_mod_cast r75_F_lowTM.2.2.1)
        (WholeIntervalPolynomial.Certificate.scale_pos r75_F_lowTM.1),
      r75_quad_reserve _ r75_F_lowTM.1 _ (a:=304587) (b:=10000000) (by norm_num [quadraticReserveValue])
        (by norm_num) r75_F_lowTM.2.2.1 r75_F_lowTM.2.2.2⟩
  · have hcoef : quadraticCoefficient .highTZ=fun j =>
        ((WholeIntervalPolynomial.Certificate.chebList r75_Z_highTZ.l).getD j 0:ℚ)/
          (r75_Z_highTZ.s*2^r75_Z_highTZ.l.length/2) :=
      WholeIntervalPolynomial.Certificate.coefficient_centered_eq r75_Z_highTZ_rep r75_F_highTZ.1 r75_F_highTZ.2.1
    rw [hcoef]
    exact ⟨div_pos (by exact_mod_cast r75_F_highTZ.2.2.1)
        (WholeIntervalPolynomial.Certificate.scale_pos r75_F_highTZ.1),
      r75_quad_reserve _ r75_F_highTZ.1 _ (a:=3948) (b:=10000000) (by norm_num [quadraticReserveValue])
        (by norm_num) r75_F_highTZ.2.2.1 r75_F_highTZ.2.2.2⟩
  · have hcoef : quadraticCoefficient .highAZ=fun j =>
        ((WholeIntervalPolynomial.Certificate.chebList r75_Z_highAZ.l).getD j 0:ℚ)/
          (r75_Z_highAZ.s*2^r75_Z_highAZ.l.length/2) :=
      WholeIntervalPolynomial.Certificate.coefficient_centered_eq r75_Z_highAZ_rep r75_F_highAZ.1 r75_F_highAZ.2.1
    rw [hcoef]
    exact ⟨div_pos (by exact_mod_cast r75_F_highAZ.2.2.1)
        (WholeIntervalPolynomial.Certificate.scale_pos r75_F_highAZ.1),
      r75_quad_reserve _ r75_F_highAZ.1 _ (a:=1815) (b:=10000000) (by norm_num [quadraticReserveValue])
        (by norm_num) r75_F_highAZ.2.2.1 r75_F_highAZ.2.2.2⟩
  · have hcoef : quadraticCoefficient .highQStar=fun j =>
        ((WholeIntervalPolynomial.Certificate.chebList r75_Z_highQStar.l).getD j 0:ℚ)/
          (r75_Z_highQStar.s*2^r75_Z_highQStar.l.length/2) :=
      WholeIntervalPolynomial.Certificate.coefficient_centered_eq r75_Z_highQStar_rep r75_F_highQStar.1 r75_F_highQStar.2.1
    rw [hcoef]
    exact ⟨div_pos (by exact_mod_cast r75_F_highQStar.2.2.1)
        (WholeIntervalPolynomial.Certificate.scale_pos r75_F_highQStar.1),
      r75_quad_reserve _ r75_F_highQStar.1 _ (a:=51799) (b:=10000000) (by norm_num [quadraticReserveValue])
        (by norm_num) r75_F_highQStar.2.2.1 r75_F_highQStar.2.2.2⟩

theorem quadratic_positive (e : Quadratic) {θ : ℝ}
    (hθ : θ∈Set.Icc (left (quadraticFamily e):ℝ) (right (quadraticFamily e):ℝ)) :
    (quadraticReserveValue e:ℝ)<aeval θ (quadraticPolynomial e) := by
  have hb := quadratic_on_interval
    (by cases e <;> norm_num [quadraticFamily,left,right,L,h] :
      left (quadraticFamily e)<right (quadraticFamily e))
    (quadratic_identity e) (quadratic_reserve e).1 hθ
  have hr : (quadraticReserveValue e:ℝ)<
      (quadraticReserve (quadraticCoefficient e) (quadraticDegree e-2):ℝ) := by
    exact_mod_cast (quadratic_reserve e).2
  exact hr.trans_le hb

def cubicDegree : Split → ℕ | .atT => 45 | .atA => 31
def cubicCoefficient (e : Split) : ℕ → ℚ := coefficient (cubicDegree e) (centered L h (NG e))
def cubicReserveValue : Split → ℚ | .atT => 6044/10000000 | .atA => 3537/10000000
def cubicCurvature : Split → ℚ | .atT => 46795/10000000 | .atA => 35767/10000000

private def r75_Z_cubic_atT : Scaled := r75_nrm ((r75_NG .atT).kcenter 1 30 13 8)
private theorem r75_Z_cubic_atT_rep : r75_Z_cubic_atT.Rep (centered L h (NG .atT)) :=
  r75_cen_high (r75_NG_rep .atT)
private theorem r75_F_cubic_atT : r75_Z_cubic_atT.s≠0 ∧ r75_Z_cubic_atT.l.length≤45+1 ∧ 0<(2*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 2 0-4*|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 3 0|) ∧
    46795*(r75_Z_cubic_atT.s*2^r75_Z_cubic_atT.l.length)<2*(2*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 2 0-4*|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 3 0|)*10000000 ∧
    6044*(2*(2*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 2 0-4*|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 3 0|)*(r75_Z_cubic_atT.s*2^r75_Z_cubic_atT.l.length))<(4*(2*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 2 0-4*|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 3 0|)*((WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 0 0-(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 2 0-
      ∑ j : Fin 42,|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD (j.val+4) 0|)-((WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 1 0-3*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD 3 0)^2)*10000000 := by
  decide +kernel

private def r75_Z_cubic_atA : Scaled := r75_nrm ((r75_NG .atA).kcenter 1 30 13 8)
private theorem r75_Z_cubic_atA_rep : r75_Z_cubic_atA.Rep (centered L h (NG .atA)) :=
  r75_cen_high (r75_NG_rep .atA)
private theorem r75_F_cubic_atA : r75_Z_cubic_atA.s≠0 ∧ r75_Z_cubic_atA.l.length≤31+1 ∧ 0<(2*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 2 0-4*|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 3 0|) ∧
    35767*(r75_Z_cubic_atA.s*2^r75_Z_cubic_atA.l.length)<2*(2*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 2 0-4*|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 3 0|)*10000000 ∧
    3537*(2*(2*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 2 0-4*|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 3 0|)*(r75_Z_cubic_atA.s*2^r75_Z_cubic_atA.l.length))<(4*(2*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 2 0-4*|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 3 0|)*((WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 0 0-(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 2 0-
      ∑ j : Fin 28,|(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD (j.val+4) 0|)-((WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 1 0-3*(WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD 3 0)^2)*10000000 := by
  decide +kernel

theorem cubic_identity (e : Split) : centered L h (NG e)=
    C (cubicCoefficient e 0-cubicCoefficient e 2)+
      C (cubicCoefficient e 1-3*cubicCoefficient e 3)*X+C (2*cubicCoefficient e 2)*X^2+
      C (4*cubicCoefficient e 3)*X^3+tail (cubicCoefficient e) 4 (cubicDegree e-3) := by
  cases e
  · exact r75_cubic_id (by decide) (r75_Z_cubic_atT_rep.eq_expansion r75_F_cubic_atT.1
      r75_F_cubic_atT.2.1)
  · exact r75_cubic_id (by decide) (r75_Z_cubic_atA_rep.eq_expansion r75_F_cubic_atA.1
      r75_F_cubic_atA.2.1)

theorem cubic_reserve (e : Split) :
    cubicCurvature e<2*cubicCoefficient e 2-4*|cubicCoefficient e 3| ∧
    cubicReserveValue e<cubicReserve (cubicCoefficient e) (cubicDegree e-3) := by
  cases e
  · have hcoef : cubicCoefficient .atT=fun j =>
        ((WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD j 0:ℚ)/
          (r75_Z_cubic_atT.s*2^r75_Z_cubic_atT.l.length/2) :=
      WholeIntervalPolynomial.Certificate.coefficient_centered_eq r75_Z_cubic_atT_rep r75_F_cubic_atT.1 r75_F_cubic_atT.2.1
    rw [hcoef]
    exact r75_cubic_reserve (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atT.l).getD j 0)
      r75_F_cubic_atT.1 _ (a:=6044) (b:=10000000) (by norm_num [cubicReserveValue])
      (by norm_num) (a':=46795) (b':=10000000) (by norm_num [cubicCurvature]) (by norm_num) r75_F_cubic_atT.2.2.1
      r75_F_cubic_atT.2.2.2.1 r75_F_cubic_atT.2.2.2.2
  · have hcoef : cubicCoefficient .atA=fun j =>
        ((WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD j 0:ℚ)/
          (r75_Z_cubic_atA.s*2^r75_Z_cubic_atA.l.length/2) :=
      WholeIntervalPolynomial.Certificate.coefficient_centered_eq r75_Z_cubic_atA_rep r75_F_cubic_atA.1 r75_F_cubic_atA.2.1
    rw [hcoef]
    exact r75_cubic_reserve (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_cubic_atA.l).getD j 0)
      r75_F_cubic_atA.1 _ (a:=3537) (b:=10000000) (by norm_num [cubicReserveValue])
      (by norm_num) (a':=35767) (b':=10000000) (by norm_num [cubicCurvature]) (by norm_num) r75_F_cubic_atA.2.2.1
      r75_F_cubic_atA.2.2.2.1 r75_F_cubic_atA.2.2.2.2

theorem high_G_positive (e : Split) {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    (cubicReserveValue e:ℝ)<aeval θ (NG e) := by
  have hc : 0<2*cubicCoefficient e 2-4*|cubicCoefficient e 3| :=
    (by cases e <;> norm_num [cubicCurvature] : 0<cubicCurvature e).trans (cubic_reserve e).1
  have hb := cubic_on_interval (by norm_num [L,h] : L<h) (cubic_identity e) hc (r75_high_mem hθ)
  have hr : (cubicReserveValue e:ℝ)<
      (cubicReserve (cubicCoefficient e) (cubicDegree e-3):ℝ) := by
    exact_mod_cast (cubic_reserve e).2
  exact hr.trans_le hb

def lowDerivativePolynomial (atZ : Bool) : ℚ[X] :=
  if atZ then NZ .low .atA else NH .low .atA
def lowDerivativeDegree : Bool → ℕ | false => 18 | true => 39
def lowDerivativeBound : Bool → ℚ | false => -(9115/10000) | true => -(8814/10000)
def lowDerivativeEndpoint : Bool → ℚ | false => 125371/10000000 | true => 129080/10000000

private def r75_Z_lowDeriv_false : Scaled := r75_nrm ((r75_deriv (r75_NH .low .atA)).kcenter 1 12 1 1)
private theorem r75_Z_lowDeriv_false_rep : r75_Z_lowDeriv_false.Rep (centered 0 L (NH .low .atA).derivative) :=
  r75_cen_low (r75_deriv_rep (r75_NH_rep .low .atA))
private def r75_Z_lowDeriv_false_end : Scaled := r75_nrm ((r75_NH .low .atA).kcenter 1 6 1 0)
private theorem r75_Z_lowDeriv_false_end_rep : r75_Z_lowDeriv_false_end.Rep (C ((NH .low .atA).eval L)) :=
  r75_cen_evalL (r75_NH_rep .low .atA)
private theorem r75_F_lowDeriv_false : r75_Z_lowDeriv_false.s≠0 ∧ r75_Z_lowDeriv_false.l.length≤18+1 ∧
    WholeIntervalPolynomial.Certificate.upperZ 18 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_lowDeriv_false.l).getD j 0)*10000*2<(-9115)*(r75_Z_lowDeriv_false.s*2^r75_Z_lowDeriv_false.l.length) ∧
    r75_Z_lowDeriv_false_end.s≠0 ∧ 125371*r75_Z_lowDeriv_false_end.s<r75_Z_lowDeriv_false_end.l.getD 0 0*10000000 := by
  decide +kernel

private def r75_Z_lowDeriv_true : Scaled := r75_nrm ((r75_deriv (r75_NZ .low .atA)).kcenter 1 12 1 1)
private theorem r75_Z_lowDeriv_true_rep : r75_Z_lowDeriv_true.Rep (centered 0 L (NZ .low .atA).derivative) :=
  r75_cen_low (r75_deriv_rep (r75_NZ_rep .low .atA))
private def r75_Z_lowDeriv_true_end : Scaled := r75_nrm ((r75_NZ .low .atA).kcenter 1 6 1 0)
private theorem r75_Z_lowDeriv_true_end_rep : r75_Z_lowDeriv_true_end.Rep (C ((NZ .low .atA).eval L)) :=
  r75_cen_evalL (r75_NZ_rep .low .atA)
private theorem r75_F_lowDeriv_true : r75_Z_lowDeriv_true.s≠0 ∧ r75_Z_lowDeriv_true.l.length≤39+1 ∧
    WholeIntervalPolynomial.Certificate.upperZ 39 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_lowDeriv_true.l).getD j 0)*10000*2<(-8814)*(r75_Z_lowDeriv_true.s*2^r75_Z_lowDeriv_true.l.length) ∧
    r75_Z_lowDeriv_true_end.s≠0 ∧ 129080*r75_Z_lowDeriv_true_end.s<r75_Z_lowDeriv_true_end.l.getD 0 0*10000000 := by
  decide +kernel

theorem low_derivative_certificate (atZ : Bool) :
    centered 0 L (lowDerivativePolynomial atZ).derivative=
      expansion (lowDerivativeDegree atZ) (centered 0 L (lowDerivativePolynomial atZ).derivative) ∧
    upperOn (lowDerivativeDegree atZ) 0 L (lowDerivativePolynomial atZ).derivative<
      lowDerivativeBound atZ ∧
    lowDerivativeEndpoint atZ<(lowDerivativePolynomial atZ).eval L := by
  cases atZ
  · exact ⟨r75_Z_lowDeriv_false_rep.eq_expansion r75_F_lowDeriv_false.1 r75_F_lowDeriv_false.2.1,
      r75_upper_lt r75_Z_lowDeriv_false_rep r75_F_lowDeriv_false.1 r75_F_lowDeriv_false.2.1 (x:=-9115) (y:=10000)
        (by norm_num [lowDerivativeBound]) (by norm_num) r75_F_lowDeriv_false.2.2.1,
      r75_eval_lt r75_Z_lowDeriv_false_end_rep r75_F_lowDeriv_false.2.2.2.1 (a:=125371) (b:=10000000)
        (by norm_num [lowDerivativeEndpoint]) (by norm_num) r75_F_lowDeriv_false.2.2.2.2⟩
  · exact ⟨r75_Z_lowDeriv_true_rep.eq_expansion r75_F_lowDeriv_true.1 r75_F_lowDeriv_true.2.1,
      r75_upper_lt r75_Z_lowDeriv_true_rep r75_F_lowDeriv_true.1 r75_F_lowDeriv_true.2.1 (x:=-8814) (y:=10000)
        (by norm_num [lowDerivativeBound]) (by norm_num) r75_F_lowDeriv_true.2.2.1,
      r75_eval_lt r75_Z_lowDeriv_true_end_rep r75_F_lowDeriv_true.2.2.2.1 (a:=129080) (b:=10000000)
        (by norm_num [lowDerivativeEndpoint]) (by norm_num) r75_F_lowDeriv_true.2.2.2.2⟩

theorem low_A_monotone_positive (atZ : Bool) {θ : ℝ} (hθ : θ∈Set.Icc (0:ℝ) (1/6)) :
    (lowDerivativeEndpoint atZ:ℝ)<aeval θ (lowDerivativePolynomial atZ) := by
  have hc := low_derivative_certificate atZ
  have hm : AntitoneOn (fun x : ℝ => aeval x (lowDerivativePolynomial atZ))
      (Set.Icc (0:ℝ) (1/6)) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt _ x)
    intro x hx
    have hb := (interval_bounds (by norm_num [L] : (0:ℚ)<L)
      hc.1 (r75_low_mem (Set.Ioo_subset_Icc_self hx))).2
    have hr : (upperOn (lowDerivativeDegree atZ) 0 L (lowDerivativePolynomial atZ).derivative:ℝ)<
        (lowDerivativeBound atZ:ℝ) := by exact_mod_cast hc.2.1
    have hn : (lowDerivativeBound atZ:ℝ)<0 := by cases atZ <;> norm_num [lowDerivativeBound]
    linarith
  have he : (lowDerivativeEndpoint atZ:ℝ)<aeval (1/6:ℝ) (lowDerivativePolynomial atZ) := by
    have hr : (lowDerivativeEndpoint atZ:ℝ)<(((lowDerivativePolynomial atZ).eval L:ℚ):ℝ) := by
      exact_mod_cast hc.2.2
    rw [← eval_rat,show ((L:ℚ):ℝ)=1/6 by norm_num [L]] at hr
    exact hr
  exact he.trans_le (hm hθ ⟨by norm_num,le_rfl⟩ hθ.2)

def highDerivativeDegree : Split → ℕ | .atT => 41 | .atA => 27
def highDerivativeBound : Split → ℚ | .atT => 275690/10000000 | .atA => 77290/10000000
def highDerivativeEndpoint : Split → ℚ | .atT => 12686/10000000 | .atA => 10199/10000000

private def r75_Z_highDeriv_atT : Scaled := r75_nrm ((r75_deriv (r75_NH .high .atT)).kcenter 1 30 13 8)
private theorem r75_Z_highDeriv_atT_rep : r75_Z_highDeriv_atT.Rep (centered L h (NH .high .atT).derivative) :=
  r75_cen_high (r75_deriv_rep (r75_NH_rep .high .atT))
private def r75_Z_highDeriv_atT_end : Scaled := r75_nrm ((r75_NH .high .atT).kcenter 1 6 1 0)
private theorem r75_Z_highDeriv_atT_end_rep : r75_Z_highDeriv_atT_end.Rep (C ((NH .high .atT).eval L)) :=
  r75_cen_evalL (r75_NH_rep .high .atT)
private theorem r75_F_highDeriv_atT : r75_Z_highDeriv_atT.s≠0 ∧ r75_Z_highDeriv_atT.l.length≤41+1 ∧
    275690*(r75_Z_highDeriv_atT.s*2^r75_Z_highDeriv_atT.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 41 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_highDeriv_atT.l).getD j 0)*10000000*2 ∧
    r75_Z_highDeriv_atT_end.s≠0 ∧ 12686*r75_Z_highDeriv_atT_end.s<r75_Z_highDeriv_atT_end.l.getD 0 0*10000000 := by
  decide +kernel

private def r75_Z_highDeriv_atA : Scaled := r75_nrm ((r75_deriv (r75_NH .high .atA)).kcenter 1 30 13 8)
private theorem r75_Z_highDeriv_atA_rep : r75_Z_highDeriv_atA.Rep (centered L h (NH .high .atA).derivative) :=
  r75_cen_high (r75_deriv_rep (r75_NH_rep .high .atA))
private def r75_Z_highDeriv_atA_end : Scaled := r75_nrm ((r75_NH .high .atA).kcenter 1 6 1 0)
private theorem r75_Z_highDeriv_atA_end_rep : r75_Z_highDeriv_atA_end.Rep (C ((NH .high .atA).eval L)) :=
  r75_cen_evalL (r75_NH_rep .high .atA)
private theorem r75_F_highDeriv_atA : r75_Z_highDeriv_atA.s≠0 ∧ r75_Z_highDeriv_atA.l.length≤27+1 ∧
    77290*(r75_Z_highDeriv_atA.s*2^r75_Z_highDeriv_atA.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 27 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_highDeriv_atA.l).getD j 0)*10000000*2 ∧
    r75_Z_highDeriv_atA_end.s≠0 ∧ 10199*r75_Z_highDeriv_atA_end.s<r75_Z_highDeriv_atA_end.l.getD 0 0*10000000 := by
  decide +kernel

theorem high_derivative_certificate (e : Split) :
    centered L h (NH .high e).derivative=
      expansion (highDerivativeDegree e) (centered L h (NH .high e).derivative) ∧
    highDerivativeBound e<lowerOn (highDerivativeDegree e) L h (NH .high e).derivative ∧
    highDerivativeEndpoint e<(NH .high e).eval L := by
  cases e
  · exact ⟨r75_Z_highDeriv_atT_rep.eq_expansion r75_F_highDeriv_atT.1 r75_F_highDeriv_atT.2.1,
      r75_lower_lt r75_Z_highDeriv_atT_rep r75_F_highDeriv_atT.1 r75_F_highDeriv_atT.2.1 (x:=275690) (y:=10000000)
        (by norm_num [highDerivativeBound]) (by norm_num) r75_F_highDeriv_atT.2.2.1,
      r75_eval_lt r75_Z_highDeriv_atT_end_rep r75_F_highDeriv_atT.2.2.2.1 (a:=12686) (b:=10000000)
        (by norm_num [highDerivativeEndpoint]) (by norm_num) r75_F_highDeriv_atT.2.2.2.2⟩
  · exact ⟨r75_Z_highDeriv_atA_rep.eq_expansion r75_F_highDeriv_atA.1 r75_F_highDeriv_atA.2.1,
      r75_lower_lt r75_Z_highDeriv_atA_rep r75_F_highDeriv_atA.1 r75_F_highDeriv_atA.2.1 (x:=77290) (y:=10000000)
        (by norm_num [highDerivativeBound]) (by norm_num) r75_F_highDeriv_atA.2.2.1,
      r75_eval_lt r75_Z_highDeriv_atA_end_rep r75_F_highDeriv_atA.2.2.2.1 (a:=10199) (b:=10000000)
        (by norm_num [highDerivativeEndpoint]) (by norm_num) r75_F_highDeriv_atA.2.2.2.2⟩

theorem high_H_positive (e : Split) {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    (highDerivativeEndpoint e:ℝ)<aeval θ (NH .high e) := by
  have hc := high_derivative_certificate e
  have hm : MonotoneOn (fun x : ℝ => aeval x (NH .high e)) (Set.Icc (1/6:ℝ) (7/10)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (CenteredMonomialBounds.aeval_hasDerivAt _ x).continuousAt.continuousWithinAt)
      (fun x _ => CenteredMonomialBounds.aeval_hasDerivAt _ x)
    intro x hx
    have hb := positive_on_interval (by norm_num [L,h] : L<h)
      hc.1 hc.2.1 (r75_high_mem (Set.Ioo_subset_Icc_self hx))
    have hr : (0:ℝ)<(highDerivativeBound e:ℝ) := by cases e <;> norm_num [highDerivativeBound]
    exact (hr.trans hb).le
  have he : (highDerivativeEndpoint e:ℝ)<aeval (1/6:ℝ) (NH .high e) := by
    have hr : (highDerivativeEndpoint e:ℝ)<(((NH .high e).eval L:ℚ):ℝ) := by exact_mod_cast hc.2.2
    rw [← eval_rat,show ((L:ℚ):ℝ)=1/6 by norm_num [L]] at hr
    exact hr
  exact he.trans_le (hm ⟨le_rfl,by norm_num⟩ hθ hθ.1)

theorem low_numerators_positive (e : Split) {θ : ℝ} (hθ : θ∈Set.Icc (0:ℝ) (1/6)) :
    0<aeval θ (NH .low e) ∧ 0<aeval θ (NM e) ∧
      0<aeval θ (NSH e) ∧ 0<aeval θ (NSG e) ∧ 0<aeval θ (NZ .low e) := by
  have hθ' := r75_low_mem hθ
  cases e
  · have hH := low_power_positive false hθ
    have hM := quadratic_positive .lowTM hθ'
    have hSH := direct_positive .lowTSH hθ'
    have hSG := direct_positive .lowTSG hθ'
    have hZ := low_power_positive true hθ
    norm_num [lowPowerReserve,lowPowerPolynomial,quadraticReserveValue,quadraticPolynomial,
      directReserve,directPolynomial] at hH hM hSH hSG hZ
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · have hH := low_A_monotone_positive false hθ
    have hM := direct_positive .lowAM hθ'
    have hSH := direct_positive .lowASH hθ'
    have hSG := direct_positive .lowASG hθ'
    have hZ := low_A_monotone_positive true hθ
    norm_num [lowDerivativeEndpoint,lowDerivativePolynomial,directReserve,directPolynomial]
      at hH hM hSH hSG hZ
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem high_numerators_positive (e : Split) {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    0<aeval θ (NH .high e) ∧ 0<aeval θ (NG e) ∧
      0<aeval θ (NB e) ∧ 0<aeval θ (NZ .high e) := by
  have hθ' := r75_high_mem hθ
  have hH := high_H_positive e hθ
  have hG := high_G_positive e hθ
  cases e
  · have hB := direct_positive .highTB hθ'
    have hZ := quadratic_positive .highTZ hθ'
    norm_num [highDerivativeEndpoint,cubicReserveValue,directReserve,directPolynomial,
      quadraticReserveValue,quadraticPolynomial] at hH hG hB hZ
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · have hB := direct_positive .highAB hθ'
    have hZ := quadratic_positive .highAZ hθ'
    norm_num [highDerivativeEndpoint,cubicReserveValue,directReserve,directPolynomial,
      quadraticReserveValue,quadraticPolynomial] at hH hG hB hZ
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

def lowAuxiliary (e : Split) : Fin 9 → ℚ[X] :=
  ![RH .low,RG .low,RB .low e,RHminus .low,RHcap,RGcap,
    C4*RH .low,C4*RG .low,C4*RB .low e]
def highAuxiliary (e : Split) : Fin 11 → ℚ[X] :=
  ![RH .high,RG .high,RB .high e,RD,RHminus .high,RGminus,RBminus e,
    C4*RH .high,C4*RG .high,C4*RB .high e,secantR]

private def r75_lowAuxS (e : Split) : Fin 9 → Scaled :=
  ![r75_RH .low,r75_RG .low,r75_RB .low e,r75_RHminus .low,r75_RHcap,r75_RGcap,
    r75_C4.nmul (r75_RH .low),r75_C4.nmul (r75_RG .low),r75_C4.nmul (r75_RB .low e)]
private theorem r75_lowAuxS_rep (e : Split) (i : Fin 9) :
    (r75_lowAuxS e i).Rep (lowAuxiliary e i) := by
  fin_cases i <;> simp only [r75_lowAuxS,lowAuxiliary,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
    Matrix.cons_val]
  · exact r75_RH_rep .low
  · exact r75_RG_rep .low
  · exact r75_RB_rep .low e
  · exact r75_RHminus_rep .low
  · exact r75_RHcap_rep
  · exact r75_RGcap_rep
  · exact r75_C4_rep.nmul (r75_RH_rep .low)
  · exact r75_C4_rep.nmul (r75_RG_rep .low)
  · exact r75_C4_rep.nmul (r75_RB_rep .low e)
private def r75_highAuxS (e : Split) : Fin 11 → Scaled :=
  ![r75_RH .high,r75_RG .high,r75_RB .high e,r75_RD,r75_RHminus .high,r75_RGminus,r75_RBminus e,
    r75_C4.nmul (r75_RH .high),r75_C4.nmul (r75_RG .high),r75_C4.nmul (r75_RB .high e),r75_secantR]
private theorem r75_highAuxS_rep (e : Split) (i : Fin 11) :
    (r75_highAuxS e i).Rep (highAuxiliary e i) := by
  fin_cases i <;> simp only [r75_highAuxS,highAuxiliary,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,
    Matrix.cons_val]
  · exact r75_RH_rep .high
  · exact r75_RG_rep .high
  · exact r75_RB_rep .high e
  · exact r75_RD_rep
  · exact r75_RHminus_rep .high
  · exact r75_RGminus_rep
  · exact r75_RBminus_rep e
  · exact r75_C4_rep.nmul (r75_RH_rep .high)
  · exact r75_C4_rep.nmul (r75_RG_rep .high)
  · exact r75_C4_rep.nmul (r75_RB_rep .high e)
  · exact r75_secantR_rep
private theorem r75_F_lowAux_atT : ∀ i : Fin 9,(r75_nrm ((r75_lowAuxS .atT i).kcenter 1 12 1 1)).s≠0 ∧ (r75_nrm ((r75_lowAuxS .atT i).kcenter 1 12 1 1)).l.length≤8+1 ∧
    37*((r75_nrm ((r75_lowAuxS .atT i).kcenter 1 12 1 1)).s*2^(r75_nrm ((r75_lowAuxS .atT i).kcenter 1 12 1 1)).l.length)<WholeIntervalPolynomial.Certificate.lowerZ 8 (fun j => (WholeIntervalPolynomial.Certificate.chebList (r75_nrm ((r75_lowAuxS .atT i).kcenter 1 12 1 1)).l).getD j 0)*50*2 := by
  decide +kernel
private theorem r75_F_highAux_atT : ∀ i : Fin 11,(r75_nrm ((r75_highAuxS .atT i).kcenter 1 30 13 8)).s≠0 ∧ (r75_nrm ((r75_highAuxS .atT i).kcenter 1 30 13 8)).l.length≤12+1 ∧
    3*((r75_nrm ((r75_highAuxS .atT i).kcenter 1 30 13 8)).s*2^(r75_nrm ((r75_highAuxS .atT i).kcenter 1 30 13 8)).l.length)<WholeIntervalPolynomial.Certificate.lowerZ 12 (fun j => (WholeIntervalPolynomial.Certificate.chebList (r75_nrm ((r75_highAuxS .atT i).kcenter 1 30 13 8)).l).getD j 0)*5*2 := by
  decide +kernel
private theorem r75_F_lowAux_atA : ∀ i : Fin 9,(r75_nrm ((r75_lowAuxS .atA i).kcenter 1 12 1 1)).s≠0 ∧ (r75_nrm ((r75_lowAuxS .atA i).kcenter 1 12 1 1)).l.length≤8+1 ∧
    37*((r75_nrm ((r75_lowAuxS .atA i).kcenter 1 12 1 1)).s*2^(r75_nrm ((r75_lowAuxS .atA i).kcenter 1 12 1 1)).l.length)<WholeIntervalPolynomial.Certificate.lowerZ 8 (fun j => (WholeIntervalPolynomial.Certificate.chebList (r75_nrm ((r75_lowAuxS .atA i).kcenter 1 12 1 1)).l).getD j 0)*50*2 := by
  decide +kernel
private theorem r75_F_highAux_atA : ∀ i : Fin 11,(r75_nrm ((r75_highAuxS .atA i).kcenter 1 30 13 8)).s≠0 ∧ (r75_nrm ((r75_highAuxS .atA i).kcenter 1 30 13 8)).l.length≤12+1 ∧
    3*((r75_nrm ((r75_highAuxS .atA i).kcenter 1 30 13 8)).s*2^(r75_nrm ((r75_highAuxS .atA i).kcenter 1 30 13 8)).l.length)<WholeIntervalPolynomial.Certificate.lowerZ 12 (fun j => (WholeIntervalPolynomial.Certificate.chebList (r75_nrm ((r75_highAuxS .atA i).kcenter 1 30 13 8)).l).getD j 0)*5*2 := by
  decide +kernel

theorem low_auxiliary_certificate (e : Split) (i : Fin 9) :
    centered 0 L (lowAuxiliary e i)=expansion 8 (centered 0 L (lowAuxiliary e i)) ∧
    (37/50:ℚ)<lowerOn 8 0 L (lowAuxiliary e i) := by
  cases e
  · exact ⟨(r75_cen_low (r75_lowAuxS_rep .atT i)).eq_expansion (r75_F_lowAux_atT i).1
      (r75_F_lowAux_atT i).2.1,
      r75_lower_lt (r75_cen_low (r75_lowAuxS_rep .atT i)) (r75_F_lowAux_atT i).1
        (r75_F_lowAux_atT i).2.1 (x:=37) (y:=50) (by norm_num) (by norm_num) (r75_F_lowAux_atT i).2.2⟩
  · exact ⟨(r75_cen_low (r75_lowAuxS_rep .atA i)).eq_expansion (r75_F_lowAux_atA i).1
      (r75_F_lowAux_atA i).2.1,
      r75_lower_lt (r75_cen_low (r75_lowAuxS_rep .atA i)) (r75_F_lowAux_atA i).1
        (r75_F_lowAux_atA i).2.1 (x:=37) (y:=50) (by norm_num) (by norm_num) (r75_F_lowAux_atA i).2.2⟩

theorem high_auxiliary_certificate (e : Split) (i : Fin 11) :
    centered L h (highAuxiliary e i)=expansion 12 (centered L h (highAuxiliary e i)) ∧
    (3/5:ℚ)<lowerOn 12 L h (highAuxiliary e i) := by
  cases e
  · exact ⟨(r75_cen_high (r75_highAuxS_rep .atT i)).eq_expansion (r75_F_highAux_atT i).1
      (r75_F_highAux_atT i).2.1,
      r75_lower_lt (r75_cen_high (r75_highAuxS_rep .atT i)) (r75_F_highAux_atT i).1
        (r75_F_highAux_atT i).2.1 (x:=3) (y:=5) (by norm_num) (by norm_num) (r75_F_highAux_atT i).2.2⟩
  · exact ⟨(r75_cen_high (r75_highAuxS_rep .atA i)).eq_expansion (r75_F_highAux_atA i).1
      (r75_F_highAux_atA i).2.1,
      r75_lower_lt (r75_cen_high (r75_highAuxS_rep .atA i)) (r75_F_highAux_atA i).1
        (r75_F_highAux_atA i).2.1 (x:=3) (y:=5) (by norm_num) (by norm_num) (r75_F_highAux_atA i).2.2⟩

theorem low_auxiliary_positive (e : Split) (i : Fin 9) {θ : ℝ}
    (hθ : θ∈Set.Icc (0:ℝ) (1/6)) : 0<aeval θ (lowAuxiliary e i) := by
  have hc := low_auxiliary_certificate e i
  have hp := positive_on_interval (by norm_num [L] : (0:ℚ)<L) hc.1 hc.2 (r75_low_mem hθ)
  norm_num at hp
  linarith

theorem high_auxiliary_positive (e : Split) (i : Fin 11) {θ : ℝ}
    (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) : 0<aeval θ (highAuxiliary e i) := by
  have hc := high_auxiliary_certificate e i
  have hp := positive_on_interval (by norm_num [L,h] : L<h) hc.1 hc.2 (r75_high_mem hθ)
  norm_num at hp
  linarith

private def r75_Z_base_low_atT : Scaled := r75_nrm (((r75_lowB .atT).nadd r75_dbar).kcenter 1 12 1 1)
private theorem r75_Z_base_low_atT_rep : r75_Z_base_low_atT.Rep (centered 0 L (lowB .atT+C dbar)) :=
  r75_cen_low ((r75_lowB_rep .atT).nadd r75_dbar_rep)
private theorem r75_F_base_low_atT : r75_Z_base_low_atT.s≠0 ∧ r75_Z_base_low_atT.l.length≤14+1 ∧
    1*(r75_Z_base_low_atT.s*2^r75_Z_base_low_atT.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 14 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_base_low_atT.l).getD j 0)*1*2 := by
  decide +kernel

private def r75_Z_base_low_atA : Scaled := r75_nrm (((r75_lowB .atA).nadd r75_dbar).kcenter 1 12 1 1)
private theorem r75_Z_base_low_atA_rep : r75_Z_base_low_atA.Rep (centered 0 L (lowB .atA+C dbar)) :=
  r75_cen_low ((r75_lowB_rep .atA).nadd r75_dbar_rep)
private theorem r75_F_base_low_atA : r75_Z_base_low_atA.s≠0 ∧ r75_Z_base_low_atA.l.length≤14+1 ∧
    1*(r75_Z_base_low_atA.s*2^r75_Z_base_low_atA.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 14 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_base_low_atA.l).getD j 0)*1*2 := by
  decide +kernel

private def r75_Z_base_high_atT : Scaled := r75_nrm (((r75_highB .atT).nsub (Scaled.ofNat 1)).kcenter 1 30 13 8)
private theorem r75_Z_base_high_atT_rep : r75_Z_base_high_atT.Rep (centered L h (highB .atT-1)) :=
  r75_cen_high ((r75_highB_rep .atT).nsub Scaled.rep_one)
private theorem r75_F_base_high_atT : r75_Z_base_high_atT.s≠0 ∧ r75_Z_base_high_atT.l.length≤14+1 ∧
    1*(r75_Z_base_high_atT.s*2^r75_Z_base_high_atT.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 14 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_base_high_atT.l).getD j 0)*1*2 := by
  decide +kernel

private def r75_Z_base_high_atA : Scaled := r75_nrm (((r75_highB .atA).nsub (Scaled.ofNat 1)).kcenter 1 30 13 8)
private theorem r75_Z_base_high_atA_rep : r75_Z_base_high_atA.Rep (centered L h (highB .atA-1)) :=
  r75_cen_high ((r75_highB_rep .atA).nsub Scaled.rep_one)
private theorem r75_F_base_high_atA : r75_Z_base_high_atA.s≠0 ∧ r75_Z_base_high_atA.l.length≤14+1 ∧
    1*(r75_Z_base_high_atA.s*2^r75_Z_base_high_atA.l.length)<WholeIntervalPolynomial.Certificate.lowerZ 14 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_base_high_atA.l).getD j 0)*1*2 := by
  decide +kernel

theorem multiplied_baseline_certificate (f : Family) (e : Split) :
    let p := if f=.low then lowB e+C dbar else highB e-1
    centered (left f) (right f) p=expansion 14 (centered (left f) (right f) p) ∧
      (1:ℚ)<lowerOn 14 (left f) (right f) p := by
  cases f <;> cases e
  · show centered 0 L (lowB .atT+C dbar)=expansion 14 (centered 0 L (lowB .atT+C dbar)) ∧
      (1:ℚ)<lowerOn 14 0 L (lowB .atT+C dbar)
    exact ⟨r75_Z_base_low_atT_rep.eq_expansion r75_F_base_low_atT.1 r75_F_base_low_atT.2.1,
      r75_lower_lt r75_Z_base_low_atT_rep r75_F_base_low_atT.1 r75_F_base_low_atT.2.1 (x:=1) (y:=1) (by norm_num) (by norm_num)
        r75_F_base_low_atT.2.2⟩
  · show centered 0 L (lowB .atA+C dbar)=expansion 14 (centered 0 L (lowB .atA+C dbar)) ∧
      (1:ℚ)<lowerOn 14 0 L (lowB .atA+C dbar)
    exact ⟨r75_Z_base_low_atA_rep.eq_expansion r75_F_base_low_atA.1 r75_F_base_low_atA.2.1,
      r75_lower_lt r75_Z_base_low_atA_rep r75_F_base_low_atA.1 r75_F_base_low_atA.2.1 (x:=1) (y:=1) (by norm_num) (by norm_num)
        r75_F_base_low_atA.2.2⟩
  · show centered L h (highB .atT-1)=expansion 14 (centered L h (highB .atT-1)) ∧
      (1:ℚ)<lowerOn 14 L h (highB .atT-1)
    exact ⟨r75_Z_base_high_atT_rep.eq_expansion r75_F_base_high_atT.1 r75_F_base_high_atT.2.1,
      r75_lower_lt r75_Z_base_high_atT_rep r75_F_base_high_atT.1 r75_F_base_high_atT.2.1 (x:=1) (y:=1) (by norm_num) (by norm_num)
        r75_F_base_high_atT.2.2⟩
  · show centered L h (highB .atA-1)=expansion 14 (centered L h (highB .atA-1)) ∧
      (1:ℚ)<lowerOn 14 L h (highB .atA-1)
    exact ⟨r75_Z_base_high_atA_rep.eq_expansion r75_F_base_high_atA.1 r75_F_base_high_atA.2.1,
      r75_lower_lt r75_Z_base_high_atA_rep r75_F_base_high_atA.1 r75_F_base_high_atA.2.1 (x:=1) (y:=1) (by norm_num) (by norm_num)
        r75_F_base_high_atA.2.2⟩

theorem multiplied_baseline_positive (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Set.Icc (left f:ℝ) (right f:ℝ)) :
    0<aeval θ (if f=.low then lowB e+C dbar else highB e-1) := by
  have hc := multiplied_baseline_certificate f e
  have hp := positive_on_interval
    (by cases f <;> norm_num [left,right,L,h] : left f<right f) hc.1 hc.2 hθ
  exact lt_trans (by norm_num) hp

private def r75_Z_qStarA : Scaled := r75_nrm ((r75_qStar.nsub (r75_c .high)).kcenter 1 30 13 8)
private theorem r75_Z_qStarA_rep : r75_Z_qStarA.Rep (centered L h (qStar-c .high)) :=
  r75_cen_high (r75_qStar_rep.nsub (r75_c_rep .high))
private theorem r75_F_qStarA : r75_Z_qStarA.s≠0 ∧ r75_Z_qStarA.l.length≤3+1 ∧
    WholeIntervalPolynomial.Certificate.lowerZ 3 (fun j => (WholeIntervalPolynomial.Certificate.chebList r75_Z_qStarA.l).getD j 0)*1000000*2=796*(r75_Z_qStarA.s*2^r75_Z_qStarA.l.length) := by
  decide +kernel

theorem qStar_A_certificate :
    centered L h (qStar-c .high)=expansion 3 (centered L h (qStar-c .high)) ∧
    lowerOn 3 L h (qStar-c .high)=(796/1000000:ℚ) := by
  refine ⟨r75_Z_qStarA_rep.eq_expansion r75_F_qStarA.1 r75_F_qStarA.2.1,?_⟩
  rw [lowerOn_eq_of_rep r75_Z_qStarA_rep r75_F_qStarA.1 r75_F_qStarA.2.1]
  have hS : (0:ℚ)<r75_Z_qStarA.s*2^r75_Z_qStarA.l.length/2 :=
    WholeIntervalPolynomial.Certificate.scale_pos r75_F_qStarA.1
  rw [div_eq_div_iff hS.ne' (by norm_num)]
  have h := congrArg (fun z : ℤ => (z:ℚ)) r75_F_qStarA.2.2
  push_cast at h
  linarith

theorem qStar_A_positive {θ : ℝ} (hθ : θ∈Set.Icc (1/6:ℝ) (7/10)) :
    0<aeval θ (qStar-c .high) := by
  have hp := (interval_bounds (by norm_num [L,h] : L<h) qStar_A_certificate.1 (r75_high_mem hθ)).1
  rw [qStar_A_certificate.2] at hp
  exact lt_of_lt_of_le (by norm_num) hp

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
