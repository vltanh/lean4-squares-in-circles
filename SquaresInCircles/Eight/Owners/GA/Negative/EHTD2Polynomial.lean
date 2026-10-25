module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2PolynomialData
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: whole-interval positivity for the negative-EH / TD2 endpoints

The two low T endpoints keep their centered quadratic (`small_quadratic_certificate`); all other
numerators use the aggregate of their coefficients. Every mass is positive on its whole native
interval (`small_mass_positive`, `far_mass_positive`). These are finite polynomial identities,
not a grid of angle evaluations.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
open WholeIntervalPolynomial ChebyshevLeadingBounds
open PositiveTD.Certificate (L h)

theorem small_interval (r : SmallCase) : smallLeft r<smallRight r := by
  cases r <;> norm_num [smallLeft,smallRight,v,L,h]
theorem far_interval (r : FarCase) : farLeft r<farRight r := by
  cases r <;> norm_num [farLeft,farRight,v,u,h]

section r78
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep lowerZ chebList toPoly)
open PositiveTD.Certificate (etaQ Rbar sigmabar cbar S5 S9 S11 C4 C10 C12 num3 num4)

/-! ### Reduced scaled lists

`Scaled.add` and `Scaled.sub` multiply the two scales.  Their reduced forms `addN` and `subN`
divide the list and the scale by their gcd, which keeps the integers of the kernel
computation short. -/

/-- The gcd of `g` and the entries of `l`. -/
private def r78zgcd : List ℤ → ℕ → ℕ
  | [],g => g
  | a :: l,g => r78zgcd l (Nat.gcd a.natAbs g)

private theorem r78zgcd_dvd : ∀ (l : List ℤ) (g : ℕ),
    r78zgcd l g ∣ g ∧ ∀ a ∈ l,(r78zgcd l g : ℤ) ∣ a
  | [],g => ⟨dvd_rfl,by simp⟩
  | a :: l,g => by
    obtain ⟨h1,h2⟩ := r78zgcd_dvd l (Nat.gcd a.natAbs g)
    refine ⟨h1.trans (Nat.gcd_dvd_right _ _),fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl|hb
    · exact Int.ofNat_dvd_left.2 (h1.trans (Nat.gcd_dvd_left _ _))
    · exact h2 b hb

/-- The list and the scale divided by `g`. -/
private def r78zdiv (g : ℕ) (S : Scaled) : Scaled := ⟨S.l.map (· / (g:ℤ)),S.s / g⟩
/-- The list and the scale divided by their gcd. -/
private def r78znorm (S : Scaled) : Scaled := r78zdiv (r78zgcd S.l S.s) S

private theorem r78z_toPoly_div {g : ℤ} : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    C (g:ℚ)*toPoly (l.map (· / g))=toPoly l
  | [],_ => by simp [toPoly]
  | a :: l,h => by
    have ih := r78z_toPoly_div l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha : ((a / g : ℤ) : ℚ)*g=a := by exact_mod_cast Int.ediv_mul_cancel (h a List.mem_cons_self)
    simp only [List.map_cons,toPoly]
    rw [mul_add,mul_left_comm,ih,← map_mul,mul_comm,ha]

private theorem r78z_toPoly_div_zero : ∀ l : List ℤ,toPoly (l.map (· / (0:ℤ)))=0
  | [] => by simp [toPoly]
  | a :: l => by rw [List.map_cons,toPoly,r78z_toPoly_div_zero l,Int.ediv_zero]; simp

private theorem r78z_rep_norm {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) : (r78znorm S).Rep p := by
  obtain ⟨h1,h2⟩ := r78zgcd_dvd S.l S.s
  unfold Scaled.Rep at *
  rw [r78znorm,r78zdiv]
  dsimp only
  generalize r78zgcd S.l S.s=g at h1 h2
  rcases Nat.eq_zero_or_pos g with rfl|hg
  · simp only [Nat.cast_zero,Nat.div_zero,map_zero,zero_mul,r78z_toPoly_div_zero]
  · have hC : C (g:ℚ)≠0 := by rw [Ne,C_eq_zero]; exact_mod_cast hg.ne'
    apply mul_left_cancel₀ hC
    have e := r78z_toPoly_div S.l h2
    push_cast at e
    rw [e,hS,← mul_assoc,← map_mul]
    congr 2
    rw [← Nat.cast_mul,Nat.mul_div_cancel' h1]

/-- `Scaled.add`, reduced. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.addN
    (a b : Scaled) : Scaled := r78znorm (a.add b)
/-- `Scaled.sub`, reduced. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.subN
    (a b : Scaled) : Scaled := r78znorm (a.sub b)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.addN
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.addN b).Rep (p+q) :=
  r78z_rep_norm (ha.add hb)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.subN
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.subN b).Rep (p-q) :=
  r78z_rep_norm (ha.sub hb)

/-! ### Kronecker substitution

An integer list is evaluated at `2 ^ k`; when every entry lies in `[-2^(k-1),2^(k-1))`, the
list is read back from the value as its balanced digits in base `2 ^ k`, by masks and shifts
(`r78z_dig_enc`). -/

/-- The list evaluated at `B`. -/
private def r78zenc (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a+B*r78zenc B l

/-- The remainder of `v` modulo `2 ^ k` in `[-2 ^ (k - 1), 2 ^ (k - 1))` and the quotient, by
masks and shifts. -/
private def r78zbsplit (k : ℕ) (v : ℤ) : ℤ × ℤ :=
  match v with
  | .ofNat n =>
    if (n &&& (2 ^ k - 1)) < 2 ^ (k - 1) then (.ofNat (n &&& (2 ^ k - 1)), .ofNat (n >>> k))
    else (.ofNat (n &&& (2 ^ k - 1)) - .ofNat (2 ^ k), .ofNat (n >>> k) + 1)
  | .negSucc n =>
    if (n &&& (2 ^ k - 1)) < 2 ^ (k - 1) then (-.ofNat (n &&& (2 ^ k - 1)) - 1, -.ofNat (n >>> k))
    else (.ofNat (2 ^ k - 1 - (n &&& (2 ^ k - 1))), -.ofNat (n >>> k) - 1)

/-- The first `n` balanced digits of `N` in base `2 ^ k`. -/
private def r78zdig (k : ℕ) : ℕ → ℤ → List ℤ
  | 0,_ => []
  | n+1,N => (r78zbsplit k N).1 :: r78zdig k n (r78zbsplit k N).2

/-- `64 w` for the number `w` of 64-bit words of `x` (at most `f`). -/
private def r78zwords : ℕ → ℕ → ℕ
  | 0,_ => 0
  | f+1,x => if x=0 then 0 else r78zwords f (x >>> 64)+64
/-- An exponent `e` with `x < 2 ^ e` for every `x` below `2 ^ 262144`. -/
private def r78zbits (x : ℕ) : ℕ := r78zwords 4096 x+1

/-- The sum of the absolute values of the entries. -/
private def r78zasum : List ℤ → ℕ
  | [] => 0
  | a :: l => a.natAbs+r78zasum l

/-- The largest absolute value of an entry. -/
private def r78zamax : List ℤ → ℕ
  | [] => 0
  | a :: l => max a.natAbs (r78zamax l)

private theorem r78z_enc_eq (B : ℤ) : ∀ l : List ℤ,(r78zenc B l : ℚ)=(toPoly l).eval (B:ℚ)
  | [] => by simp [r78zenc,toPoly]
  | a :: l => by simp [r78zenc,toPoly,r78z_enc_eq B l]

private theorem r78zbsplit_spec {k : ℕ} (hk : 1 ≤ k) (v : ℤ) :
    (r78zbsplit k v).1 + 2 ^ k * (r78zbsplit k v).2 = v ∧ -(2 ^ (k - 1) : ℤ) ≤ (r78zbsplit k v).1 ∧
      (r78zbsplit k v).1 < 2 ^ (k - 1) := by
  have hP : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hPz : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by exact_mod_cast hP
  have hP1 : (0 : ℤ) < 2 ^ (k - 1) := by positivity
  cases v with
  | ofNat n =>
    have hdm := Nat.div_add_mod n (2 ^ k)
    have hlt := Nat.mod_lt n (show 0 < 2 ^ k by positivity)
    simp only [r78zbsplit, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Int.ofNat_eq_natCast]
    generalize n % 2 ^ k = r at *
    generalize n / 2 ^ k = q at *
    have hdmz : (2 : ℤ) ^ k * (q : ℤ) + (r : ℤ) = n := by exact_mod_cast hdm
    have hltz : (r : ℤ) < 2 ^ k := by exact_mod_cast hlt
    have hr0 : (0 : ℤ) ≤ r := by positivity
    split_ifs with h
    · have h' : (r : ℤ) < 2 ^ (k - 1) := by exact_mod_cast h
      dsimp only
      refine ⟨by linarith, by linarith, h'⟩
    · have h' : (2 : ℤ) ^ (k - 1) ≤ r := by exact_mod_cast not_lt.1 h
      dsimp only
      push_cast
      refine ⟨by linarith, by linarith, by linarith⟩
  | negSucc n =>
    have hdm := Nat.div_add_mod n (2 ^ k)
    have hlt := Nat.mod_lt n (show 0 < 2 ^ k by positivity)
    simp only [r78zbsplit, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
      Int.ofNat_eq_natCast, Int.negSucc_eq]
    generalize n % 2 ^ k = r at *
    generalize n / 2 ^ k = q at *
    have hdmz : (2 : ℤ) ^ k * (q : ℤ) + (r : ℤ) = n := by exact_mod_cast hdm
    have hltz : (r : ℤ) < 2 ^ k := by exact_mod_cast hlt
    have hr0 : (0 : ℤ) ≤ r := by positivity
    split_ifs with h
    · have h' : (r : ℤ) < 2 ^ (k - 1) := by exact_mod_cast h
      dsimp only
      refine ⟨by linarith, by linarith, by linarith⟩
    · have h' : (2 : ℤ) ^ (k - 1) ≤ r := by exact_mod_cast not_lt.1 h
      have hle : r ≤ 2 ^ k - 1 := by omega
      dsimp only
      rw [Nat.cast_sub hle, Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      refine ⟨by linarith, by linarith, by linarith⟩

private theorem r78zbsplit_eq {k : ℕ} (hk : 1 ≤ k) {a w : ℤ} (ha1 : -(2 ^ (k - 1) : ℤ) ≤ a)
    (ha2 : a < 2 ^ (k - 1)) : r78zbsplit k (a + 2 ^ k * w) = (a, w) := by
  obtain ⟨h1, h2, h3⟩ := r78zbsplit_spec hk (a + 2 ^ k * w)
  have hPz : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < 2 ^ (k - 1) := by positivity
  have hw : (r78zbsplit k (a + 2 ^ k * w)).2 = w := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : (r78zbsplit k (a + 2 ^ k * w)).2 + 1 ≤ w := h
      nlinarith
    · have : w + 1 ≤ (r78zbsplit k (a + 2 ^ k * w)).2 := h
      nlinarith
  refine Prod.ext ?_ hw
  rw [hw] at h1
  linarith

private theorem r78z_dig_enc {k : ℕ} (hk : 1≤k) : ∀ (n : ℕ) (c : List ℤ),c.length≤n →
    (∀ j,-((2^k:ℕ):ℤ)≤2*c.getD j 0 ∧ 2*c.getD j 0<((2^k:ℕ):ℤ)) →
      toPoly (r78zdig k n (r78zenc ((2^k:ℕ):ℤ) c))=toPoly c
  | 0,c,hl,_ => by
    rw [List.length_eq_zero_iff.1 (by omega : c.length=0)]
    rfl
  | n+1,[],_,_ => by
    have hpos : (0 : ℤ) < 2 ^ (k - 1) := by positivity
    have h0 := r78zbsplit_eq hk (a:=0) (w:=0) (by linarith) hpos
    simp only [mul_zero,add_zero] at h0
    have ih : toPoly (r78zdig k n 0)=0 :=
      r78z_dig_enc hk n [] (by simp) (fun j => by simp)
    show toPoly (r78zdig k (n+1) 0)=0
    rw [r78zdig,h0]
    simp [toPoly,ih]
  | n+1,x :: c,hl,hb => by
    have hx := hb 0
    simp only [List.getD_cons_zero] at hx
    have hPz : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    push_cast at hx
    have h1 := r78zbsplit_eq hk (a:=x) (w:=r78zenc ((2^k:ℕ):ℤ) c) (by linarith [hx.1])
      (by linarith [hx.2])
    have ih := r78z_dig_enc hk n c (by simpa using hl) (fun j => by simpa using hb (j+1))
    have e : r78zenc ((2^k:ℕ):ℤ) (x :: c)=x+2^k*r78zenc ((2^k:ℕ):ℤ) c := by
      simp only [r78zenc]; push_cast; ring
    rw [e,r78zdig,h1]
    rw [toPoly,toPoly,ih]

private theorem r78z_getD_smul (c : ℤ) : ∀ (l : List ℤ) (j : ℕ),
    (Certificate.smul c l).getD j 0=c*l.getD j 0
  | [],j => by simp [Certificate.smul]
  | a :: l,0 => by simp [Certificate.smul]
  | a :: l,j+1 => by
    simp only [Certificate.smul,List.getD_cons_succ,r78z_getD_smul c l j]

private theorem r78z_getD_le_amax : ∀ (l : List ℤ) (j : ℕ),|l.getD j 0|≤r78zamax l
  | [],j => by simp
  | a :: l,0 => by simp only [List.getD_cons_zero,r78zamax]; push_cast; exact le_max_left _ _
  | a :: l,j+1 => by
    simp only [List.getD_cons_succ,r78zamax]
    push_cast
    exact (r78z_getD_le_amax l j).trans (le_max_right _ _)

private theorem r78z_mul_bound : ∀ (a m : List ℤ) (j : ℕ),
    |(Certificate.mul a m).getD j 0|≤r78zasum a*r78zamax m
  | [],m,j => by simp [Certificate.mul]; positivity
  | a :: l,[],j => by simp [Certificate.mul]; positivity
  | a :: l,b :: m,j => by
    rw [Certificate.mul,Certificate.getD_add,
      r78z_getD_smul]
    have h1 : |a*(b :: m).getD j 0|≤|a| * r78zamax (b :: m) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (r78z_getD_le_amax _ j) (abs_nonneg a)
    have h2 : |(0 :: Certificate.mul l (b :: m)).getD j 0|≤
        r78zasum l*r78zamax (b :: m) := by
      rcases j with _|j
      · simp only [List.getD_cons_zero,abs_zero]; positivity
      · simpa only [List.getD_cons_succ] using r78z_mul_bound l (b :: m) j
    simp only [r78zasum]
    push_cast
    calc _≤_ := abs_add_le _ _
      _≤_ := add_le_add h1 h2
      _=_ := by ring

private theorem r78z_length_add : ∀ l m : List ℤ,
    (Certificate.add l m).length=max l.length m.length
  | [],m => by simp [Certificate.add]
  | a :: l,[] => by simp [Certificate.add]
  | a :: l,b :: m => by
    simp [Certificate.add,r78z_length_add l m,Nat.succ_max_succ]

private theorem r78z_length_smul (c : ℤ) : ∀ l : List ℤ,
    (Certificate.smul c l).length=l.length
  | [] => rfl
  | a :: l => by simp [Certificate.smul,r78z_length_smul c l]

private theorem r78z_length_mul : ∀ a m : List ℤ,
    (Certificate.mul a m).length≤a.length+m.length-1
  | [],m => by simp [Certificate.mul]
  | a :: l,[] => by simp [Certificate.mul]
  | a :: l,b :: m => by
    have ih := r78z_length_mul l (b :: m)
    rw [Certificate.mul,r78z_length_add,r78z_length_smul]
    rcases l with _|⟨c,l⟩
    · simp [Certificate.mul]
    · simp only [List.length_cons] at ih ⊢
      omega

/-! ### Encoded sums and products

`r78zK` holds the value `N` at a base `B` of an integer list of at most `n` entries, each of
absolute value at most `β`, that represents `s` times a polynomial.  Sums and products act on
`N` alone, so a whole expression costs a few integer operations; `toScaled` reads the list
back as balanced digits in base `B = 2 ^ e` once `B` exceeds `2β`. -/

private structure r78zK where
  N : ℤ
  s : ℕ
  n : ℕ
  β : ℕ

private def r78zK.Rep (B : ℤ) (k : r78zK) (p : ℚ[X]) : Prop :=
  ∃ l : List ℤ,l.length≤k.n ∧ (∀ j,|l.getD j 0|≤k.β) ∧ k.N=r78zenc B l ∧ toPoly l=C (k.s:ℚ)*p

private def r78zK.add (a b : r78zK) : r78zK := ⟨a.N*b.s+b.N*a.s,a.s*b.s,max a.n b.n,a.β*b.s+b.β*a.s⟩
private def r78zK.sub (a b : r78zK) : r78zK := ⟨a.N*b.s-b.N*a.s,a.s*b.s,max a.n b.n,a.β*b.s+b.β*a.s⟩
private def r78zK.mul (a b : r78zK) : r78zK := ⟨a.N*b.N,a.s*b.s,a.n+b.n-1,a.n*a.β*b.β⟩
private def r78zK.const (q : ℚ) : r78zK := ⟨q.num,q.den,1,q.num.natAbs⟩
private def r78zK.ofScaled (B : ℤ) (S : Scaled) : r78zK := ⟨r78zenc B S.l,S.s,S.l.length,r78zamax S.l⟩
private def r78zK.toScaled (e : ℕ) (k : r78zK) : Scaled :=
  if 1≤e ∧ 2*k.β<2^e then ⟨r78zdig e k.n k.N,k.s⟩ else ⟨[],0⟩

private theorem r78z_enc_add (B : ℤ) (l m : List ℤ) :
    r78zenc B (Certificate.add l m)=r78zenc B l+r78zenc B m := by
  have e : (r78zenc B (Certificate.add l m) : ℚ)=r78zenc B l+r78zenc B m := by
    rw [r78z_enc_eq,r78z_enc_eq,r78z_enc_eq,Certificate.toPoly_add,eval_add]
  exact_mod_cast e

private theorem r78z_enc_smul (B c : ℤ) (l : List ℤ) :
    r78zenc B (Certificate.smul c l)=c*r78zenc B l := by
  have e : (r78zenc B (Certificate.smul c l) : ℚ)=c*r78zenc B l := by
    rw [r78z_enc_eq,r78z_enc_eq,Certificate.toPoly_smul,eval_mul,eval_C]
  exact_mod_cast e

private theorem r78z_enc_mul (B : ℤ) (l m : List ℤ) :
    r78zenc B (Certificate.mul l m)=r78zenc B l*r78zenc B m := by
  have e : (r78zenc B (Certificate.mul l m) : ℚ)=r78zenc B l*r78zenc B m := by
    rw [r78z_enc_eq,r78z_enc_eq,r78z_enc_eq,Certificate.toPoly_mul,eval_mul]
  exact_mod_cast e

private theorem r78z_amax_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) : r78zamax l≤β := by
  induction l generalizing β with
  | nil => simp [r78zamax]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    exact max_le h0 h1

private theorem r78z_asum_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) :
    r78zasum l≤l.length*β := by
  induction l generalizing β with
  | nil => simp [r78zasum]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    simp only [r78zasum,List.length_cons]
    nlinarith

private theorem r78zK.Rep.add {B : ℤ} {a b : r78zK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.add b).Rep B (p+q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨Certificate.add (Certificate.smul b.s la) (Certificate.smul a.s lb),?_,?_,?_,?_⟩
  · rw [r78z_length_add,r78z_length_smul,r78z_length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [Certificate.getD_add,r78z_getD_smul,r78z_getD_smul]
    calc _≤|(b.s:ℤ)*la.getD j 0|+|(a.s:ℤ)*lb.getD j 0| := abs_add_le _ _
      _≤(b.s:ℤ)*a.β+(a.s:ℤ)*b.β := by
        rw [abs_mul,abs_mul,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by simp only [r78zK.add]; push_cast; ring
  · simp only [r78zK.add,r78z_enc_add,r78z_enc_smul,hNa,hNb]
    ring
  · simp only [r78zK.add,Certificate.toPoly_add,Certificate.toPoly_smul,hpa,hpb,Int.cast_natCast,
      Nat.cast_mul,map_mul]
    ring

private theorem r78zK.Rep.sub {B : ℤ} {a b : r78zK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.sub b).Rep B (p-q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨Certificate.add (Certificate.smul b.s la) (Certificate.smul (-(a.s:ℤ)) lb),?_,?_,?_,?_⟩
  · rw [r78z_length_add,r78z_length_smul,r78z_length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [Certificate.getD_add,r78z_getD_smul,r78z_getD_smul]
    calc _≤|(b.s:ℤ)*la.getD j 0|+|(-(a.s:ℤ))*lb.getD j 0| := abs_add_le _ _
      _≤(b.s:ℤ)*a.β+(a.s:ℤ)*b.β := by
        rw [abs_mul,abs_mul,abs_neg,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by simp only [r78zK.sub]; push_cast; ring
  · simp only [r78zK.sub,r78z_enc_add,r78z_enc_smul,hNa,hNb]
    ring
  · simp only [r78zK.sub,Certificate.toPoly_add,Certificate.toPoly_smul,hpa,hpb,Int.cast_natCast,
      Int.cast_neg,Nat.cast_mul,map_mul,map_neg]
    ring

private theorem r78zK.Rep.mul {B : ℤ} {a b : r78zK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.mul b).Rep B (p*q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨Certificate.mul la lb,?_,?_,?_,?_⟩
  · have := r78z_length_mul la lb
    simp only [r78zK.mul]
    omega
  · intro j
    have h1 := r78z_mul_bound la lb j
    have h2 : r78zasum la*r78zamax lb≤a.n*a.β*b.β :=
      Nat.mul_le_mul ((r78z_asum_le hba).trans (Nat.mul_le_mul_right _ hla)) (r78z_amax_le hbb)
    simp only [r78zK.mul]
    calc _≤((r78zasum la*r78zamax lb:ℕ):ℤ) := by exact_mod_cast h1
      _≤_ := by exact_mod_cast h2
  · simp only [r78zK.mul,r78z_enc_mul,hNa,hNb]
  · simp only [r78zK.mul,Certificate.toPoly_mul,hpa,hpb,Nat.cast_mul,map_mul]
    ring

private theorem r78zK.rep_const (B : ℤ) (q : ℚ) : (r78zK.const q).Rep B (C q) := by
  refine ⟨[q.num],by simp [r78zK.const],fun j => ?_,by simp [r78zK.const,r78zenc],?_⟩
  · rcases j with _|j
    · simp only [List.getD_cons_zero,r78zK.const]
      exact (Int.abs_eq_natAbs _).le
    · simp
  · simp only [r78zK.const,toPoly,mul_zero,add_zero,← map_mul,Rat.den_mul_eq_num]

private theorem r78zK.rep_ofScaled (B : ℤ) {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) :
    (r78zK.ofScaled B S).Rep B p :=
  ⟨S.l,le_rfl,r78z_getD_le_amax S.l,rfl,hS⟩

private theorem r78zK.Rep.toScaled {e : ℕ} {k : r78zK} {p : ℚ[X]} (hk : k.Rep ((2^e:ℕ):ℤ) p) :
    (k.toScaled e).Rep p := by
  unfold r78zK.toScaled
  split_ifs with h
  · obtain ⟨l,hl,hb,hN,hp⟩ := hk
    have hβ : 2*(k.β:ℤ)<((2^e:ℕ):ℤ) := by exact_mod_cast h.2
    show toPoly (r78zdig e k.n k.N)=_
    rw [hN,r78z_dig_enc h.1 _ _ hl
      (fun j => by obtain ⟨h1,h2⟩ := abs_le.1 (hb j); constructor <;> linarith)]
    exact hp
  · show toPoly []=C ((0:ℕ):ℚ)*p
    simp [toPoly]

/-! ### Products by Kronecker substitution

`Scaled.mul` multiplies entry by entry.  `kmul` evaluates both lists at a power of two `B`,
multiplies the two values and reads the coefficients of the product back; `B` exceeds twice
the bound `n·max|aᵢ|·max|bⱼ|` on those coefficients. -/

/-- The exponent of the base of `kmul`. -/
private def r78zkmulE (a b : Scaled) : ℕ := r78zbits (2*(a.l.length*r78zamax a.l*r78zamax b.l))
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.kmul
    (a b : Scaled) : Scaled :=
  ((r78zK.ofScaled ((2^r78zkmulE a b:ℕ):ℤ) a).mul
    (r78zK.ofScaled ((2^r78zkmulE a b:ℕ):ℤ) b)).toScaled (r78zkmulE a b)
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.kmul
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.kmul b).Rep (p*q) :=
  ((r78zK.rep_ofScaled _ ha).mul (r78zK.rep_ofScaled _ hb)).toScaled
/-- The square, by `kmul`. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.ksq
    (a : Scaled) : Scaled := a.kmul a
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.ksq
    {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.ksq.Rep (p^2) := by
  rw [sq]; exact ha.kmul ha

/-! ### Composition with `s+tX` by Kronecker substitution

The entries of the composition of `L` with `s+tX` are at most `Σ|Lᵢ| (|s|+|t|+1)^(n-1)`, so they
are the balanced digits in base `B = 2 ^ e` of the value of `L` at `s+tB` for `B` above twice
that bound. -/

private theorem r78z_asum_add : ∀ l m : List ℤ,
    r78zasum (Certificate.add l m)≤r78zasum l+r78zasum m
  | [],m => by simp [Certificate.add,r78zasum]
  | a :: l,[] => by simp [Certificate.add,r78zasum]
  | a :: l,b :: m => by
    have ih := r78z_asum_add l m
    have := Int.natAbs_add_le a b
    simp only [Certificate.add,r78zasum]
    omega

private theorem r78z_asum_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    r78zasum (Certificate.affMulAux s t c z)≤
      s.natAbs*r78zasum z+t.natAbs*c.natAbs+t.natAbs*r78zasum z
  | c,[] => by simp [Certificate.affMulAux,r78zasum,Int.natAbs_mul]
  | c,x :: z => by
    have ih := r78z_asum_affMulAux s t x z
    have h1 := Int.natAbs_add_le (s*x) (t*c)
    simp only [Certificate.affMulAux,r78zasum,Int.natAbs_mul] at h1 ⊢
    nlinarith

private theorem r78z_asum_affMul (s t : ℤ) (z : List ℤ) :
    r78zasum (Certificate.affMul s t z)≤(s.natAbs+t.natAbs)*r78zasum z := by
  unfold Certificate.affMul
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    cases z with
    | nil => simp [Certificate.shiftMul,r78zasum]
    | cons x z =>
      have := r78z_asum_add (x :: z) (0 :: x :: z)
      simp only [Certificate.shiftMul]
      simp only [r78zasum] at this ⊢
      simp
      omega
  · cases z with
    | nil => simp [Certificate.affMulGen,r78zasum]
    | cons x z =>
      have := r78z_asum_affMulAux s t x z
      simp only [Certificate.affMulGen,r78zasum,Int.natAbs_mul]
      nlinarith

private theorem r78z_asum_compAff (s t : ℤ) : ∀ l : List ℤ,
    r78zasum (Certificate.compAff s t l)≤
      r78zasum l*(s.natAbs+t.natAbs+1)^(l.length-1)
  | [] => by simp [Certificate.compAff,r78zasum]
  | b :: l => by
    have h1 := r78z_asum_add [b] (Certificate.affMul s t
      (Certificate.compAff s t l))
    have h2 := r78z_asum_affMul s t (Certificate.compAff s t l)
    have hb : r78zasum [b]=b.natAbs := by simp [r78zasum]
    rw [Certificate.compAff]
    simp only [r78zasum,List.length_cons,Nat.add_sub_cancel]
    rcases l with _|⟨c,l⟩
    · simp [Certificate.compAff,Certificate.affMul,
        Certificate.shiftMul,Certificate.affMulGen,
        Certificate.add,r78zasum]
    · have ih := r78z_asum_compAff s t (c :: l)
      generalize r78zasum (Certificate.compAff s t (c :: l))=A at h1 h2 ih
      simp only [List.length_cons,Nat.add_sub_cancel] at ih ⊢
      have key : (s.natAbs+t.natAbs)*A≤r78zasum (c :: l)*(s.natAbs+t.natAbs+1)^(l.length+1) :=
        calc (s.natAbs+t.natAbs)*A≤(s.natAbs+t.natAbs+1)*A := Nat.mul_le_mul_right _ (Nat.le_succ _)
          _≤(s.natAbs+t.natAbs+1)*(r78zasum (c :: l)*(s.natAbs+t.natAbs+1)^l.length) :=
            Nat.mul_le_mul_left _ ih
          _=_ := by ring
      have hM : 1≤(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.one_le_pow _ _ (by omega)
      have hb' : b.natAbs≤b.natAbs*(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.le_mul_of_pos_right _ hM
      rw [hb] at h1
      rw [add_mul]
      omega

private theorem r78z_getD_le_asum : ∀ (l : List ℤ) (j : ℕ),(l.getD j 0).natAbs≤r78zasum l
  | [],j => by simp [r78zasum]
  | a :: l,0 => by simp [r78zasum]
  | a :: l,j+1 => by
    have := r78z_getD_le_asum l j
    simp only [List.getD_cons_succ,r78zasum]
    omega

private theorem r78z_length_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    (Certificate.affMulAux s t c z).length=z.length+1
  | c,[] => rfl
  | c,x :: z => by
    simp [Certificate.affMulAux,r78z_length_affMulAux s t x z]

private theorem r78z_length_affMul (s t : ℤ) (z : List ℤ) :
    (Certificate.affMul s t z).length≤z.length+1 := by
  unfold Certificate.affMul
  split_ifs
  · cases z with
    | nil => simp [Certificate.shiftMul]
    | cons x z =>
      rw [Certificate.shiftMul,r78z_length_add]
      simp
  · cases z with
    | nil => simp [Certificate.affMulGen]
    | cons x z =>
      simp [Certificate.affMulGen,r78z_length_affMulAux]

private theorem r78z_length_compAff (s t : ℤ) : ∀ l : List ℤ,
    (Certificate.compAff s t l).length≤l.length
  | [] => by simp [Certificate.compAff]
  | b :: l => by
    have ih := r78z_length_compAff s t l
    have h := r78z_length_affMul s t (Certificate.compAff s t l)
    rw [Certificate.compAff,r78z_length_add]
    simp only [List.length_cons,List.length_nil]
    omega

/-- The composition of `L` with `s+tX`, by one evaluation at `s+tB`, read back in a base
`B = 2 ^ e` above `2 Σ|Lᵢ| (|s|+|t|+1)^(n-1)`; the list composition if that base is too small. -/
private def r78zkcenterAux (s t : ℤ) (L : List ℤ) : List ℤ :=
  if 1≤r78zbits (2*(r78zasum L*(s.natAbs+t.natAbs+1)^(L.length-1))) ∧
      2*(r78zasum L*(s.natAbs+t.natAbs+1)^(L.length-1))<
        2^r78zbits (2*(r78zasum L*(s.natAbs+t.natAbs+1)^(L.length-1))) then
    r78zdig (r78zbits (2*(r78zasum L*(s.natAbs+t.natAbs+1)^(L.length-1)))) L.length
      (r78zenc (s+t*((2^r78zbits (2*(r78zasum L*(s.natAbs+t.natAbs+1)^(L.length-1))):ℕ):ℤ)) L)
  else Certificate.compAff s t L

private theorem r78z_toPoly_kcenterAux (s t : ℤ) (L : List ℤ) :
    toPoly (r78zkcenterAux s t L)=toPoly (Certificate.compAff s t L) := by
  rw [r78zkcenterAux]
  generalize hM : r78zasum L*(s.natAbs+t.natAbs+1)^(L.length-1)=M
  generalize r78zbits (2*M)=e
  split_ifs with hc
  · obtain ⟨he,hMe⟩ := hc
    have hE : r78zenc (s+t*((2^e:ℕ):ℤ)) L=r78zenc ((2^e:ℕ):ℤ) (Certificate.compAff s t L) := by
      have e' : (r78zenc (s+t*((2^e:ℕ):ℤ)) L : ℚ)=
          (r78zenc ((2^e:ℕ):ℤ) (Certificate.compAff s t L) : ℚ) := by
        rw [r78z_enc_eq,r78z_enc_eq,Certificate.toPoly_compAff,eval_comp]
        simp
      exact_mod_cast e'
    rw [hE]
    apply r78z_dig_enc he _ _ (r78z_length_compAff s t L)
    intro j
    have h1 := r78z_getD_le_asum (Certificate.compAff s t L) j
    have h2 := r78z_asum_compAff s t L
    rw [hM] at h2
    have h3 : ((Certificate.compAff s t L).getD j 0).natAbs≤M := h1.trans h2
    have h4 : |(Certificate.compAff s t L).getD j 0|≤(M:ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h3
    have hMe' : 2*(M:ℤ)<((2^e:ℕ):ℤ) := by exact_mod_cast hMe
    obtain ⟨h5,h6⟩ := abs_le.1 h4
    constructor <;> linarith
  · rfl

/-- `Scaled.center`, with the composition by `r78zkcenterAux`. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.kcenter
    (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨r78zkcenterAux s t (Certificate.prescale num den (c.l.length-1) 0 c.l),
    c.s*den^(c.l.length-1)⟩

private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.kcentered
    {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (c.kcenter num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  have h := hc.centered num den s t hden hm hh
  unfold Scaled.Rep at h ⊢
  show toPoly (r78zkcenterAux s t _)=_
  rw [r78z_toPoly_kcenterAux]
  exact h

private theorem r78z_rep_eq {S : Scaled} {p q : ℚ[X]} (e : q=p) (h : S.Rep q) : S.Rep p := e ▸ h

/-- `num3` on encoded lists, with `w = r1 r2`:
`2 A r0 w - R ((P0+r0²) w + ((P1+r1²) r2 + (P2+r2²) r1) r0)`. -/
private def r78num3K (A P0 P1 P2 r0 r1 r2 w : r78zK) : r78zK :=
  ((((r78zK.const 2).mul A).mul r0).mul w).sub ((r78zK.const Rbar).mul
    (((P0.add (r0.mul r0)).mul w).add
      ((((P1.add (r1.mul r1)).mul r2).add ((P2.add (r2.mul r2)).mul r1)).mul r0)))
private def r78num3B (B : ℤ) (A P0 P1 P2 r0 r1 r2 : Scaled) : r78zK :=
  r78num3K (r78zK.ofScaled B A) (r78zK.ofScaled B P0) (r78zK.ofScaled B P1) (r78zK.ofScaled B P2)
    (r78zK.ofScaled B r0) (r78zK.ofScaled B r1) (r78zK.ofScaled B r2)
    ((r78zK.ofScaled B r1).mul (r78zK.ofScaled B r2))
private def r78num3With (e : ℕ) (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  r78znorm ((r78num3B ((2^e:ℕ):ℤ) A P0 P1 P2 r0 r1 r2).toScaled e)
/-- `num3` of the lists, read back in a base `2 ^ e` above twice its coefficient bound. -/
private def r78num3 (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  r78num3With (r78zbits (2*(r78num3B 0 A P0 P1 P2 r0 r1 r2).β)) A P0 P1 P2 r0 r1 r2
private theorem r78num3With_rep (e : ℕ) {A P0 P1 P2 r0 r1 r2 : Scaled}
    {a p0 p1 p2 s0 s1 s2 : ℚ[X]} (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1)
    (h2 : P2.Rep p2) (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (r78num3With e A P0 P1 P2 r0 r1 r2).Rep (num3 a p0 p1 p2 s0 s1 s2) := by
  have kA := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) hA
  have k0 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) h0
  have k1 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) h1
  have k2 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) h2
  have j0 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) g0
  have j1 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) g1
  have j2 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) g2
  exact r78z_rep_eq (by unfold num3; ring) (r78z_rep_norm (r78zK.Rep.toScaled
    (((((r78zK.rep_const ((2^e:ℕ):ℤ) 2).mul kA).mul j0).mul (j1.mul j2)).sub ((r78zK.rep_const ((2^e:ℕ):ℤ) Rbar).mul
      (((k0.add (j0.mul j0)).mul (j1.mul j2)).add
        ((((k1.add (j1.mul j1)).mul j2).add ((k2.add (j2.mul j2)).mul j1)).mul j0))))))
private theorem r78num3_rep {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 s0 s1 s2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (r78num3 A P0 P1 P2 r0 r1 r2).Rep (num3 a p0 p1 p2 s0 s1 s2) :=
  r78num3With_rep _ hA h0 h1 h2 g0 g1 g2

/-- `num4` on encoded lists, with `u = r0 r1` and `v = r2 r3`:
`2 A u v - R (((P0+r0²) r1 + (P1+r1²) r0) v + ((P2+r2²) r3 + (P3+r3²) r2) u)`. -/
private def r78num4K (A P0 P1 P2 P3 r0 r1 r2 r3 u v : r78zK) : r78zK :=
  ((((r78zK.const 2).mul A).mul u).mul v).sub ((r78zK.const Rbar).mul
    (((((P0.add (r0.mul r0)).mul r1).add ((P1.add (r1.mul r1)).mul r0)).mul v).add
      ((((P2.add (r2.mul r2)).mul r3).add ((P3.add (r3.mul r3)).mul r2)).mul u)))
private def r78num4B (B : ℤ) (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : r78zK :=
  r78num4K (r78zK.ofScaled B A) (r78zK.ofScaled B P0) (r78zK.ofScaled B P1) (r78zK.ofScaled B P2)
    (r78zK.ofScaled B P3) (r78zK.ofScaled B r0) (r78zK.ofScaled B r1) (r78zK.ofScaled B r2)
    (r78zK.ofScaled B r3) ((r78zK.ofScaled B r0).mul (r78zK.ofScaled B r1))
    ((r78zK.ofScaled B r2).mul (r78zK.ofScaled B r3))
private def r78num4With (e : ℕ) (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  r78znorm ((r78num4B ((2^e:ℕ):ℤ) A P0 P1 P2 P3 r0 r1 r2 r3).toScaled e)
/-- `num4` of the lists, read back in a base `2 ^ e` above twice its coefficient bound. -/
private def r78num4 (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  r78num4With (r78zbits (2*(r78num4B 0 A P0 P1 P2 P3 r0 r1 r2 r3).β)) A P0 P1 P2 P3 r0 r1 r2 r3
private theorem r78num4With_rep (e : ℕ) {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (r78num4With e A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) := by
  have kA := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) hA
  have k0 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) h0
  have k1 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) h1
  have k2 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) h2
  have k3 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) h3
  have j0 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) g0
  have j1 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) g1
  have j2 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) g2
  have j3 := r78zK.rep_ofScaled ((2^e:ℕ):ℤ) g3
  exact r78z_rep_eq (by unfold num4; ring) (r78z_rep_norm (r78zK.Rep.toScaled
    (((((r78zK.rep_const ((2^e:ℕ):ℤ) 2).mul kA).mul (j0.mul j1)).mul (j2.mul j3)).sub
      ((r78zK.rep_const ((2^e:ℕ):ℤ) Rbar).mul
        (((((k0.add (j0.mul j0)).mul j1).add ((k1.add (j1.mul j1)).mul j0)).mul (j2.mul j3)).add
          ((((k2.add (j2.mul j2)).mul j3).add ((k3.add (j3.mul j3)).mul j2)).mul (j0.mul j1)))))))
private theorem r78num4_rep {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (r78num4 A P0 P1 P2 P3 r0 r1 r2 r3).Rep (num4 a p0 p1 p2 p3 s0 s1 s2 s3) :=
  r78num4With_rep _ hA h0 h1 h2 h3 g0 g1 g2 g3


/-! ### The numerators and masses as scaled integer coefficient lists

Each polynomial of the endpoint data is mirrored by a `Scaled` list built with the same
operations, and `Scaled.Rep` proves that the list represents it. The kernel evaluates
only these integer lists: sums are reduced by their gcd (`addN`, `subN`), and the numerators,
the long products and the changes of variable go through Kronecker substitution (`r78num3`,
`r78num4`, `kmul`, `ksq`, `kcenter`). -/

/-- The monomial `X^k`. -/
private def r78mono (k : ℕ) : Scaled := ⟨List.replicate k 0++[1],1⟩
private theorem r78mono_rep (k : ℕ) : (r78mono k).Rep (X^k) := by
  unfold Scaled.Rep r78mono
  simp only [Nat.cast_one,map_one,one_mul]
  induction k with
  | zero => simp [toPoly]
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,toPoly,ih,pow_succ]
    simp only [Int.cast_zero,map_zero,zero_add]
    ring

private def r78Z : Scaled := ⟨[],1⟩
private theorem r78Z_rep : r78Z.Rep 0 := Scaled.rep_zero
private def r78one : Scaled := Scaled.ofNat 1
private theorem r78one_rep : r78one.Rep 1 := Scaled.rep_one

private theorem r78_rep_ite {c : Prop} [Decidable c] {A B : Scaled} {p q : ℚ[X]}
    (hA : A.Rep p) (hB : B.Rep q) : (if c then A else B).Rep (if c then p else q) := by
  split_ifs <;> assumption

private def r78S5 : Scaled :=
  (Scaled.var.subN ((Scaled.const (1/6)).mul (r78mono 3))).addN
    ((Scaled.const (1/120)).mul (r78mono 5))
private theorem r78S5_rep : r78S5.Rep S5 :=
  (Scaled.rep_var.subN ((Scaled.rep_const _).mul (r78mono_rep 3))).addN
    ((Scaled.rep_const _).mul (r78mono_rep 5))
private def r78S9 : Scaled :=
  (r78S5.subN ((Scaled.const (1/5040)).mul (r78mono 7))).addN
    ((Scaled.const (1/362880)).mul (r78mono 9))
private theorem r78S9_rep : r78S9.Rep S9 :=
  (r78S5_rep.subN ((Scaled.rep_const _).mul (r78mono_rep 7))).addN
    ((Scaled.rep_const _).mul (r78mono_rep 9))
private def r78S11 : Scaled := r78S9.subN ((Scaled.const (1/39916800)).mul (r78mono 11))
private theorem r78S11_rep : r78S11.Rep S11 :=
  r78S9_rep.subN ((Scaled.rep_const _).mul (r78mono_rep 11))
private def r78C4 : Scaled :=
  (r78one.subN ((Scaled.const (1/2)).mul (r78mono 2))).addN
    ((Scaled.const (1/24)).mul (r78mono 4))
private theorem r78C4_rep : r78C4.Rep C4 :=
  (r78one_rep.subN ((Scaled.rep_const _).mul (r78mono_rep 2))).addN
    ((Scaled.rep_const _).mul (r78mono_rep 4))
private def r78C10 : Scaled :=
  ((r78C4.subN ((Scaled.const (1/720)).mul (r78mono 6))).addN
    ((Scaled.const (1/40320)).mul (r78mono 8))).subN
    ((Scaled.const (1/3628800)).mul (r78mono 10))
private theorem r78C10_rep : r78C10.Rep C10 :=
  ((r78C4_rep.subN ((Scaled.rep_const _).mul (r78mono_rep 6))).addN
    ((Scaled.rep_const _).mul (r78mono_rep 8))).subN
    ((Scaled.rep_const _).mul (r78mono_rep 10))
private def r78C12 : Scaled := r78C10.addN ((Scaled.const (1/479001600)).mul (r78mono 12))
private theorem r78C12_rep : r78C12.Rep C12 :=
  r78C10_rep.addN ((Scaled.rep_const _).mul (r78mono_rep 12))
private def r78C2 : Scaled := r78one.subN ((Scaled.const (1/2)).mul (r78mono 2))
private theorem r78C2_rep : r78C2.Rep C2 :=
  r78one_rep.subN ((Scaled.rep_const _).mul (r78mono_rep 2))
private def r78S3 : Scaled := Scaled.var.subN ((Scaled.const (1/6)).mul (r78mono 3))
private theorem r78S3_rep : r78S3.Rep S3 :=
  Scaled.rep_var.subN ((Scaled.rep_const _).mul (r78mono_rep 3))

/-! Composition with affine maps and evaluation at rational points. -/

private theorem r78_comp_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hab : (a+b)/2=num*s/den) (hba : (b-a)/2=num*t/den)
    {q : ℚ[X]} (hq : C ((a+b)/2)+C ((b-a)/2)*X=q) :
    (S.kcenter num den s t).Rep (p.comp q) := by
  have hc := hp.kcentered num den s t hden hab hba
  rwa [WholeIntervalPolynomial.centered,affine,hq] at hc

private theorem r78_rep_eval {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s : ℤ)
    {a : ℚ} (hden : den≠0) (ha : a=num*s/den) : (S.kcenter num den s 0).Rep (C (p.eval a)) := by
  have hc := hp.kcentered num den s 0 (a:=a) (b:=a) hden (by rw [← ha]; ring) (by simp)
  have he : WholeIntervalPolynomial.centered a a p=C (p.eval a) := by
    rw [WholeIntervalPolynomial.centered,affine,sub_self,zero_div,map_zero,zero_mul,add_zero,
      add_self_div_two,comp_C]
  rwa [he] at hc

/-- A represented constant, cut down to its constant entry. -/
private def r78head (S : Scaled) : Scaled := ⟨[S.l.getD 0 0],S.s⟩
private theorem r78head_rep {S : Scaled} {c : ℚ} (hS : S.Rep (C c)) : (r78head S).Rep (C c) := by
  unfold Scaled.Rep at *
  have h0 := congrArg (fun q => q.coeff 0) hS
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul,coeff_C_zero] at h0
  simp only [r78head,WholeIntervalPolynomial.Certificate.toPoly,mul_zero,add_zero,h0,map_mul]

/-- Composition with `X-C (1/10)`. -/
private def r78dv (S : Scaled) : Scaled := S.kcenter 1 10 (-1) 10
private theorem r78dv_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r78dv S).Rep (p.comp (X-C v)) :=
  r78_comp_rep hp 1 10 (-1) 10 (a:=-11/10) (b:=9/10) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((-11/10:ℚ)+9/10)/2=-v by norm_num [v],
      show ((9/10:ℚ)-(-11/10))/2=1 by norm_num,map_neg,map_one]; ring)
/-- Composition with `X-C (1/4)`. -/
private def r78du (S : Scaled) : Scaled := S.kcenter 1 4 (-1) 4
private theorem r78du_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r78du S).Rep (p.comp (X-C u)) :=
  r78_comp_rep hp 1 4 (-1) 4 (a:=-5/4) (b:=3/4) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((-5/4:ℚ)+3/4)/2=-u by norm_num [u],
      show ((3/4:ℚ)-(-5/4))/2=1 by norm_num,map_neg,map_one]; ring)
/-- Composition with `C (1/10)-X`. -/
private def r78dr (S : Scaled) : Scaled := S.kcenter 1 10 1 (-10)
private theorem r78dr_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) :
    (r78dr S).Rep (p.comp (C v-X)) :=
  r78_comp_rep hp 1 10 1 (-10) (a:=11/10) (b:=-9/10) (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((11/10:ℚ)+-9/10)/2=v by norm_num [v],
      show ((-9/10:ℚ)-11/10)/2=-1 by norm_num,map_neg,map_one]; ring)

/-! The negative-DE families. -/

private def r78DL : Scaled := Scaled.var.subN (Scaled.const L)
private theorem r78DL_rep : r78DL.Rep (X-C L) := Scaled.rep_var.subN (Scaled.rep_const _)
private def r78t : Scaled := (Scaled.const (15/8)).mul r78DL
private theorem r78t_rep : r78t.Rep NegativeDEPositiveTD.Certificate.t :=
  (Scaled.rep_const _).mul r78DL_rep

private def r78k : Family → Scaled
  | .low => ((Scaled.const (6708/10000)).addN ((Scaled.const (3/20)).mul r78DL)).addN
      ((Scaled.const 4).mul (r78DL.pow 2))
  | .high => ((((Scaled.const (670158/1000000)).addN ((Scaled.const (113718/1000000)).mul r78t)).addN
      ((Scaled.const (6506/1000000)).mul (r78t.pow 2))).addN
      ((Scaled.const (9026/1000000)).mul (r78t.pow 3))).addN
      ((Scaled.const (1/1000)).mul (r78t.pow 4))
private theorem r78k_rep : ∀ f, (r78k f).Rep (NegativeDEPositiveTD.Certificate.k f)
  | .low => ((Scaled.rep_const _).addN ((Scaled.rep_const _).mul r78DL_rep)).addN
      ((Scaled.rep_const _).mul (r78DL_rep.pow 2))
  | .high => ((((Scaled.rep_const _).addN ((Scaled.rep_const _).mul r78t_rep)).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 2))).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 3))).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 4))
private def r78l : Family → Scaled
  | .low => ((Scaled.const (10073/10000)).subN ((Scaled.const (17/10)).mul r78DL)).addN
      ((Scaled.const (11/5)).mul (r78DL.pow 2))
  | .high => (((Scaled.const (1005069/1000000)).subN ((Scaled.const (146411/1000000)).mul r78t)).subN
      ((Scaled.const (157739/1000000)).mul (r78t.pow 2))).addN
      ((Scaled.const (162815/1000000)).mul (r78t.pow 3))
private theorem r78l_rep : ∀ f, (r78l f).Rep (NegativeDEPositiveTD.Certificate.l f)
  | .low => ((Scaled.rep_const _).subN ((Scaled.rep_const _).mul r78DL_rep)).addN
      ((Scaled.rep_const _).mul (r78DL_rep.pow 2))
  | .high => (((Scaled.rep_const _).subN ((Scaled.rep_const _).mul r78t_rep)).subN
      ((Scaled.rep_const _).mul (r78t_rep.pow 2))).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 3))
private def r78c : Family → Scaled
  | .low => ((Scaled.const (10389/10000)).subN ((Scaled.const (69/20)).mul r78DL)).addN
      ((Scaled.const 9).mul (r78DL.pow 2))
  | .high => (((Scaled.const (1021248/1000000)).subN ((Scaled.const (168873/1000000)).mul r78t)).subN
      ((Scaled.const (165381/1000000)).mul (r78t.pow 2))).addN
      ((Scaled.const (175944/1000000)).mul (r78t.pow 3))
private theorem r78c_rep : ∀ f, (r78c f).Rep (NegativeDEPositiveTD.Certificate.c f)
  | .low => ((Scaled.rep_const _).subN ((Scaled.rep_const _).mul r78DL_rep)).addN
      ((Scaled.rep_const _).mul (r78DL_rep.pow 2))
  | .high => (((Scaled.rep_const _).subN ((Scaled.rep_const _).mul r78t_rep)).subN
      ((Scaled.rep_const _).mul (r78t_rep.pow 2))).addN
      ((Scaled.rep_const _).mul (r78t_rep.pow 3))

private def r78J0 : Scaled :=
  ((Scaled.const (1/2)).mul (r78C10.subN r78one)).addN
    ((Scaled.const (1/2-NegativeDEPositiveTD.Certificate.abar)).mul r78S9)
private theorem r78J0_rep : r78J0.Rep J0 :=
  ((Scaled.rep_const _).mul (r78C10_rep.subN r78one_rep)).addN ((Scaled.rep_const _).mul r78S9_rep)
private def r78J1 : Scaled := r78J0.subN ((Scaled.const (151/500)).mul (r78DL.pow 6))
private theorem r78J1_rep : r78J1.Rep J1 :=
  r78J0_rep.subN ((Scaled.rep_const _).mul (r78DL_rep.pow 6))

private def r78mLo : Family → Split → Scaled
  | f,.atT => (r78c f).mul (r78C10.addN ((Scaled.const etaQ).mul r78S11))
  | f,.atA => r78c f
private theorem r78mLo_rep : ∀ f e,
    (r78mLo f e).Rep (NegativeDEPositiveTD.Certificate.mLo f e)
  | f,.atT => (r78c_rep f).mul (r78C10_rep.addN ((Scaled.rep_const _).mul r78S11_rep))
  | f,.atA => r78c_rep f
private def r78mHi : Family → Split → Scaled
  | f,.atT => (r78c f).mul (r78C12.addN ((Scaled.const etaQ).mul r78S9))
  | f,.atA => r78c f
private theorem r78mHi_rep : ∀ f e,
    (r78mHi f e).Rep (NegativeDEPositiveTD.Certificate.mHi f e)
  | f,.atT => (r78c_rep f).mul (r78C12_rep.addN ((Scaled.rep_const _).mul r78S9_rep))
  | f,.atA => r78c_rep f
private def r78mu : Family → Split → Scaled
  | .low,.atT => (r78c .low).mul (r78C2.addN ((Scaled.const etaQ).mul Scaled.var))
  | .high,.atT => (r78c .high).mul (r78C4.addN ((Scaled.const etaQ).mul r78S5))
  | .low,.atA => r78c .low
  | .high,.atA => r78c .high
private theorem r78mu_rep : ∀ f e,
    (r78mu f e).Rep (NegativeDEPositiveTD.Certificate.mu f e)
  | .low,.atT => (r78c_rep .low).mul (r78C2_rep.addN ((Scaled.rep_const _).mul Scaled.rep_var))
  | .high,.atT => (r78c_rep .high).mul (r78C4_rep.addN ((Scaled.rep_const _).mul r78S5_rep))
  | .low,.atA => r78c_rep .low
  | .high,.atA => r78c_rep .high

private def r78lowE : Split → Scaled
  | .atT => (((((Scaled.const 2).mul (r78k .low)).addN ((Scaled.const 3).mul (r78l .low))).addN
      ((Scaled.const (3/2)).mul (r78mLo .low .atT))).addN (Scaled.const (5/2))).addN
      (((Scaled.const (1/2)).mul (r78c .low)).mul ((r78one.addN r78C10).addN r78S11)) |>.subN
      (((r78c .low).mul (Scaled.const sigmabar)).mul r78S9)
  | .atA => (((((Scaled.const 2).mul (r78k .low)).addN ((Scaled.const 3).mul (r78l .low))).addN
      ((Scaled.const (5/2)).mul (r78c .low))).addN (Scaled.const (5/2))).addN
      ((r78l .low).mul r78J0)
private theorem r78lowE_rep : ∀ e, (r78lowE e).Rep (NegativeDEPositiveTD.Certificate.lowE e)
  | .atT => (((((Scaled.rep_const _).mul (r78k_rep .low)).addN
      ((Scaled.rep_const _).mul (r78l_rep .low))).addN
      ((Scaled.rep_const _).mul (r78mLo_rep .low .atT))).addN (Scaled.rep_const _)).addN
      (((Scaled.rep_const _).mul (r78c_rep .low)).mul ((r78one_rep.addN r78C10_rep).addN r78S11_rep))
      |>.subN (((r78c_rep .low).mul (Scaled.rep_const _)).mul r78S9_rep)
  | .atA => (((((Scaled.rep_const _).mul (r78k_rep .low)).addN
      ((Scaled.rep_const _).mul (r78l_rep .low))).addN
      ((Scaled.rep_const _).mul (r78c_rep .low))).addN (Scaled.rep_const _)).addN
      ((r78l_rep .low).mul r78J0_rep)
private def r78lowB (e : Split) : Scaled :=
  (r78lowE e).subN ((Scaled.const cbar).mul (r78one.addN (r78c .low)))
private theorem r78lowB_rep (e : Split) : (r78lowB e).Rep (NegativeDEPositiveTD.Certificate.lowB e) :=
  (r78lowE_rep e).subN ((Scaled.rep_const _).mul (r78one_rep.addN (r78c_rep .low)))
private def r78highB : Split → Scaled
  | .atT => ((((((Scaled.const 2).mul (r78k .high)).addN ((Scaled.const 3).mul (r78l .high))).addN
      ((Scaled.const (3/2)).mul (r78mLo .high .atT))).addN
      ((Scaled.const (1/2)).mul (r78c .high))).addN (Scaled.const 3)).addN
      (((Scaled.const (1/2)).mul (r78c .high)).mul ((r78one.addN r78C10).addN r78S11)) |>.subN
      (((r78c .high).mul (Scaled.const sigmabar)).mul r78S9)
  | .atA => ((((Scaled.const 2).mul (r78k .high)).addN ((Scaled.const 3).mul (r78l .high))).addN
      ((Scaled.const 3).mul (r78c .high))).addN (Scaled.const 3) |>.addN ((r78l .high).mul r78J1)
private theorem r78highB_rep : ∀ e, (r78highB e).Rep (NegativeDEPositiveTD.Certificate.highB e)
  | .atT => ((((((Scaled.rep_const _).mul (r78k_rep .high)).addN
      ((Scaled.rep_const _).mul (r78l_rep .high))).addN
      ((Scaled.rep_const _).mul (r78mLo_rep .high .atT))).addN
      ((Scaled.rep_const _).mul (r78c_rep .high))).addN (Scaled.rep_const _)).addN
      (((Scaled.rep_const _).mul (r78c_rep .high)).mul ((r78one_rep.addN r78C10_rep).addN r78S11_rep))
      |>.subN (((r78c_rep .high).mul (Scaled.rep_const _)).mul r78S9_rep)
  | .atA => ((((Scaled.rep_const _).mul (r78k_rep .high)).addN
      ((Scaled.rep_const _).mul (r78l_rep .high))).addN
      ((Scaled.rep_const _).mul (r78c_rep .high))).addN (Scaled.rep_const _)
      |>.addN ((r78l_rep .high).mul r78J1_rep)

private def r78PH (f : Family) : Scaled := r78one.addN ((r78k f).pow 2)
private theorem r78PH_rep (f : Family) : (r78PH f).Rep (NegativeDEPositiveTD.Certificate.PH f) :=
  r78one_rep.addN ((r78k_rep f).pow 2)
private def r78PG (f : Family) : Scaled := ((r78k f).pow 2).addN ((r78l f).pow 2)
private theorem r78PG_rep (f : Family) : (r78PG f).Rep (NegativeDEPositiveTD.Certificate.PG f) :=
  ((r78k_rep f).pow 2).addN ((r78l_rep f).pow 2)
private def r78PB (f : Family) (e : Split) : Scaled := ((r78mHi f e).ksq).addN ((r78l f).pow 2)
private theorem r78PB_rep (f : Family) (e : Split) :
    (r78PB f e).Rep (NegativeDEPositiveTD.Certificate.PB f e) :=
  ((r78mHi_rep f e).ksq).addN ((r78l_rep f).pow 2)
private def r78PD (f : Family) : Scaled := r78one.addN ((r78c f).pow 2)
private theorem r78PD_rep (f : Family) : (r78PD f).Rep (NegativeDEPositiveTD.Certificate.PD f) :=
  r78one_rep.addN ((r78c_rep f).pow 2)
private def r78RH : Family → Scaled
  | .low => (Scaled.const (41/50)).addN ((Scaled.const (143/250)).mul (r78k .low))
  | .high => (Scaled.const (4/5)).addN ((Scaled.const (3/5)).mul (r78k .high))
private theorem r78RH_rep : ∀ f, (r78RH f).Rep (NegativeDEPositiveTD.Certificate.RH f)
  | .low => (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78k_rep .low))
  | .high => (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78k_rep .high))
private def r78RG : Family → Scaled
  | .low => ((Scaled.const (11/20)).mul (r78k .low)).addN ((Scaled.const (167/200)).mul (r78l .low))
  | .high => ((Scaled.const (31/50)).mul (r78k .high)).addN
      ((Scaled.const (3923/5000)).mul (r78l .high))
private theorem r78RG_rep : ∀ f, (r78RG f).Rep (NegativeDEPositiveTD.Certificate.RG f)
  | .low => ((Scaled.rep_const _).mul (r78k_rep .low)).addN ((Scaled.rep_const _).mul (r78l_rep .low))
  | .high => ((Scaled.rep_const _).mul (r78k_rep .high)).addN
      ((Scaled.rep_const _).mul (r78l_rep .high))
private def r78RB (f : Family) (e : Split) : Scaled :=
  if f=.low then ((Scaled.const (729/1000)).mul (r78mu f e)).addN
    ((Scaled.const (1369/2000)).mul (r78l f))
  else (Scaled.const (7071/10000)).mul ((r78l f).addN (r78mu f e))
private theorem r78RB_rep (f : Family) (e : Split) :
    (r78RB f e).Rep (NegativeDEPositiveTD.Certificate.RB f e) :=
  r78_rep_ite (((Scaled.rep_const _).mul (r78mu_rep f e)).addN
    ((Scaled.rep_const _).mul (r78l_rep f)))
    ((Scaled.rep_const _).mul ((r78l_rep f).addN (r78mu_rep f e)))
private def r78RD : Scaled := (Scaled.const (18/25)).addN ((Scaled.const (347/500)).mul (r78c .high))
private theorem r78RD_rep : r78RD.Rep NegativeDEPositiveTD.Certificate.RD :=
  (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78c_rep .high))
private def r78qStar : Scaled :=
  (r78l .high).addN ((Scaled.const (3/20)).mul ((Scaled.const h).subN Scaled.var))
private theorem r78qStar_rep : r78qStar.Rep NegativeDEPositiveTD.Certificate.qStar :=
  (r78l_rep .high).addN ((Scaled.rep_const _).mul ((Scaled.rep_const _).subN Scaled.rep_var))

/-! The EH gain. -/

private def r78gPoly : Scaled :=
  ((Scaled.const K).mul r78S11).addN ((Scaled.const beta).mul (r78C10.subN r78one))
private theorem r78gPoly_rep : r78gPoly.Rep gPoly :=
  ((Scaled.rep_const _).mul r78S11_rep).addN ((Scaled.rep_const _).mul (r78C10_rep.subN r78one_rep))
private def r78GPoly : Scaled := ((Scaled.const p).mul r78gPoly).subN (Scaled.const (11/50000))
private theorem r78GPoly_rep : r78GPoly.Rep GPoly :=
  ((Scaled.rep_const _).mul r78gPoly_rep).subN (Scaled.rep_const _)
private theorem r78_gStar_eval (s : ℚ) : gPoly.eval s=gStar s := by
  simp [gPoly,gStar]
private theorem r78_GStar_eval (s : ℚ) : GPoly.eval s=GStar s := by
  simp [GPoly,GStar,r78_gStar_eval]
private def r78gStarV : Scaled := r78head (r78gPoly.kcenter 1 10 1 0)
private theorem r78gStarV_rep : r78gStarV.Rep (C (gStar v)) := by
  have h := r78head_rep (r78_rep_eval r78gPoly_rep 1 10 1 (a:=v) (by norm_num) (by norm_num [v]))
  rwa [r78_gStar_eval] at h
private def r78GStarV : Scaled := r78head (r78GPoly.kcenter 1 10 1 0)
private theorem r78GStarV_rep : r78GStarV.Rep (C (GStar v)) := by
  have h := r78head_rep (r78_rep_eval r78GPoly_rep 1 10 1 (a:=v) (by norm_num) (by norm_num [v]))
  rwa [r78_GStar_eval] at h
private def r78GStarU : Scaled := r78head (r78GPoly.kcenter 1 4 1 0)
private theorem r78GStarU_rep : r78GStarU.Rep (C (GStar u)) := by
  have h := r78head_rep (r78_rep_eval r78GPoly_rep 1 4 1 (a:=u) (by norm_num) (by norm_num [u]))
  rwa [r78_GStar_eval] at h

/-! The small-error numerators. -/

private def r78smallP (r : SmallCase) (e : Split) : Fin 4 → Scaled :=
  let f := smallFamily r
  ![(r78PH f).subN (if r=.lowH ∨ r=.highH then
        ((Scaled.const 2).mul (r78k f)).mul (r78dv r78S11) else r78Z),
    (r78PG f).subN (if r=.highG then
        (((Scaled.const 2).mul (r78k f)).mul (r78l f)).mul (r78dv r78S11) else r78Z),
    (r78PB f e).subN (if r=.highB then
        (((Scaled.const 2).mul (r78l f)).mul (r78mLo f e)).kmul (r78dv r78S11) else r78Z),
    if f=.low then r78Z else r78PD f]
private theorem r78smallP_rep (r : SmallCase) (e : Split) (i : Fin 4) :
    (r78smallP r e i).Rep (smallP r e i) := by
  fin_cases i
  · exact (r78PH_rep _).subN (r78_rep_ite
      (((Scaled.rep_const _).mul (r78k_rep _)).mul (r78dv_rep r78S11_rep)) r78Z_rep)
  · exact (r78PG_rep _).subN (r78_rep_ite
      ((((Scaled.rep_const _).mul (r78k_rep _)).mul (r78l_rep _)).mul (r78dv_rep r78S11_rep)) r78Z_rep)
  · exact (r78PB_rep _ _).subN (r78_rep_ite
      ((((Scaled.rep_const _).mul (r78l_rep _)).mul (r78mLo_rep _ _)).kmul (r78dv_rep r78S11_rep))
      r78Z_rep)
  · exact r78_rep_ite r78Z_rep (r78PD_rep _)

private def r78smallMass (r : SmallCase) (e : Split) : Fin 4 → Scaled :=
  let f := smallFamily r
  ![if r=.lowH then ((Scaled.const (89/100)).mul (r78dv r78C2)).addN
        ((Scaled.const (57/125)).mul ((r78k f).subN (r78dv r78S3)))
      else if r=.highH then ((Scaled.const (93/100)).mul (r78dv r78C4)).addN
        ((Scaled.const (919/2500)).mul ((r78k f).subN (r78dv r78S5)))
      else r78RH f,
    if r=.highG then (((Scaled.const (93/100)).mul (r78l f)).mul (r78dv r78C4)).addN
        ((Scaled.const (919/2500)).mul ((r78k f).subN ((r78l f).mul (r78dv r78S5))))
      else r78RG f,
    if r=.highB then (((Scaled.const (83/100)).mul (r78l f)).mul (r78dv r78C4)).addN
        ((Scaled.const (14/25)).mul ((r78mu f e).subN ((r78l f).mul (r78dv r78S5))))
      else r78RB f e,
    if f=.low then r78one else r78RD]
private theorem r78smallMass_rep (r : SmallCase) (e : Split) (i : Fin 4) :
    (r78smallMass r e i).Rep (smallMass r e i) := by
  fin_cases i
  · exact r78_rep_ite (((Scaled.rep_const _).mul (r78dv_rep r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78k_rep _).subN (r78dv_rep r78S3_rep))))
      (r78_rep_ite (((Scaled.rep_const _).mul (r78dv_rep r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78k_rep _).subN (r78dv_rep r78S5_rep)))) (r78RH_rep _))
  · exact r78_rep_ite ((((Scaled.rep_const _).mul (r78l_rep _)).mul (r78dv_rep r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78k_rep _).subN ((r78l_rep _).mul (r78dv_rep r78S5_rep)))))
      (r78RG_rep _)
  · exact r78_rep_ite ((((Scaled.rep_const _).mul (r78l_rep _)).mul (r78dv_rep r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78mu_rep _ _).subN ((r78l_rep _).mul (r78dv_rep r78S5_rep)))))
      (r78RB_rep _ _)
  · exact r78_rep_ite r78one_rep r78RD_rep

private def r78smallB (r : SmallCase) (e : Split) : Scaled :=
  if smallFamily r=.low then r78lowB e else r78highB e
private theorem r78smallB_rep (r : SmallCase) (e : Split) : (r78smallB r e).Rep
    (if smallFamily r=.low then NegativeDEPositiveTD.Certificate.lowB e
      else NegativeDEPositiveTD.Certificate.highB e) :=
  r78_rep_ite (r78lowB_rep e) (r78highB_rep e)
private def r78smallNonrad : SmallCase → Split → Scaled
  | .lowZero,e => (r78smallB .lowZero e).addN r78gPoly
  | .lowH,e => (((r78smallB .lowH e).addN r78gStarV).addN (r78dv r78C10)).subN r78one
  | .highH,e => (((r78smallB .highH e).addN r78gStarV).addN (r78dv r78C10)).subN r78one
  | .highG,e => ((r78smallB .highG e).addN r78gStarV).addN
      ((r78l .high).mul ((r78dv r78C10).subN r78one))
  | .highB,e => ((r78smallB .highB e).addN r78gStarV).addN
      (r78qStar.mul ((r78dv r78C10).subN r78one))
private theorem r78smallNonrad_rep : ∀ r e, (r78smallNonrad r e).Rep (smallNonradical r e)
  | .lowZero,e => (r78smallB_rep .lowZero e).addN r78gPoly_rep
  | .lowH,e => (((r78smallB_rep .lowH e).addN r78gStarV_rep).addN (r78dv_rep r78C10_rep)).subN r78one_rep
  | .highH,e => (((r78smallB_rep .highH e).addN r78gStarV_rep).addN (r78dv_rep r78C10_rep)).subN r78one_rep
  | .highG,e => ((r78smallB_rep .highG e).addN r78gStarV_rep).addN
      ((r78l_rep .high).mul ((r78dv_rep r78C10_rep).subN r78one_rep))
  | .highB,e => ((r78smallB_rep .highB e).addN r78gStarV_rep).addN
      (r78qStar_rep.mul ((r78dv_rep r78C10_rep).subN r78one_rep))

private def r78smallNum (r : SmallCase) (e : Split) : Scaled :=
  if smallFamily r=.low then
    r78num3 (r78smallNonrad r e) (r78smallP r e 0) (r78smallP r e 1) (r78smallP r e 2)
      (r78smallMass r e 0) (r78smallMass r e 1) (r78smallMass r e 2)
  else r78num4 (r78smallNonrad r e) (r78smallP r e 0) (r78smallP r e 1) (r78smallP r e 2)
      (r78smallP r e 3) (r78smallMass r e 0) (r78smallMass r e 1) (r78smallMass r e 2)
      (r78smallMass r e 3)
private theorem r78smallNum_rep (r : SmallCase) (e : Split) :
    (r78smallNum r e).Rep (smallNumerator r e) :=
  r78_rep_ite
    (r78num3_rep (r78smallNonrad_rep r e) (r78smallP_rep r e 0) (r78smallP_rep r e 1)
      (r78smallP_rep r e 2) (r78smallMass_rep r e 0) (r78smallMass_rep r e 1) (r78smallMass_rep r e 2))
    (r78num4_rep (r78smallNonrad_rep r e) (r78smallP_rep r e 0) (r78smallP_rep r e 1)
      (r78smallP_rep r e 2) (r78smallP_rep r e 3) (r78smallMass_rep r e 0) (r78smallMass_rep r e 1)
      (r78smallMass_rep r e 2) (r78smallMass_rep r e 3))

/-! The remaining-error numerators. -/

private def r78farK : Family → Scaled
  | .low => Scaled.const (121/200)
  | .high => (Scaled.const (101/200)).addN ((Scaled.const (2/5)).mul Scaled.var)
private theorem r78farK_rep : ∀ f, (r78farK f).Rep (farK f)
  | .low => Scaled.rep_const _
  | .high => (Scaled.rep_const _).addN ((Scaled.rep_const _).mul Scaled.rep_var)
private def r78farL : Family → Scaled
  | .low => r78one.subN ((Scaled.const (9/25)).mul Scaled.var)
  | .high => (Scaled.const (381/400)).subN ((Scaled.const (17/100)).mul Scaled.var)
private theorem r78farL_rep : ∀ f, (r78farL f).Rep (farL f)
  | .low => r78one_rep.subN ((Scaled.rep_const _).mul Scaled.rep_var)
  | .high => (Scaled.rep_const _).subN ((Scaled.rep_const _).mul Scaled.rep_var)
private def r78farC : Family → Scaled
  | .low => (Scaled.const (111/100)).subN ((Scaled.const (77/100)).mul Scaled.var)
  | .high => (Scaled.const (1929/2000)).subN ((Scaled.const (47/250)).mul Scaled.var)
private theorem r78farC_rep : ∀ f, (r78farC f).Rep (farC f)
  | .low => (Scaled.rep_const _).subN ((Scaled.rep_const _).mul Scaled.rep_var)
  | .high => (Scaled.rep_const _).subN ((Scaled.rep_const _).mul Scaled.rep_var)
private def r78farMLo (f : Family) : Split → Scaled
  | .atT => (r78farC f).mul (r78C10.addN ((Scaled.const etaQ).mul r78S11))
  | .atA => r78farC f
private theorem r78farMLo_rep (f : Family) : ∀ e, (r78farMLo f e).Rep (farMLo f e)
  | .atT => (r78farC_rep f).mul (r78C10_rep.addN ((Scaled.rep_const _).mul r78S11_rep))
  | .atA => r78farC_rep f
private def r78farMHi (f : Family) : Split → Scaled
  | .atT => (r78farC f).mul (r78C12.addN ((Scaled.const etaQ).mul r78S9))
  | .atA => r78farC f
private theorem r78farMHi_rep (f : Family) : ∀ e, (r78farMHi f e).Rep (farMHi f e)
  | .atT => (r78farC_rep f).mul (r78C12_rep.addN ((Scaled.rep_const _).mul r78S9_rep))
  | .atA => r78farC_rep f
private def r78farMu (f : Family) : Split → Scaled
  | .atT => (r78farC f).mul (r78C4.addN ((Scaled.const etaQ).mul r78S5))
  | .atA => r78farC f
private theorem r78farMu_rep (f : Family) : ∀ e, (r78farMu f e).Rep (farMu f e)
  | .atT => (r78farC_rep f).mul (r78C4_rep.addN ((Scaled.rep_const _).mul r78S5_rep))
  | .atA => r78farC_rep f
private def r78farB (f : Family) : Split → Scaled
  | .atT => ((((((Scaled.const 2).mul (r78farK f)).addN ((Scaled.const 3).mul (r78farL f))).addN
      ((Scaled.const (3/2)).mul (r78farMLo f .atT))).addN
      ((Scaled.const (1/2)).mul (r78farC f))).addN (Scaled.const 3)).addN
      (((Scaled.const (1/2)).mul (r78farC f)).mul ((r78one.addN r78C10).addN r78S11)) |>.subN
      (((r78farC f).mul (Scaled.const sigmabar)).mul r78S9)
  | .atA => ((((Scaled.const 2).mul (r78farK f)).addN ((Scaled.const 3).mul (r78farL f))).addN
      ((Scaled.const 3).mul (r78farC f))).addN (Scaled.const 3) |>.addN
      ((r78farL f).mul (if f=.low then r78J0 else r78J1))
private theorem r78farB_rep (f : Family) : ∀ e, (r78farB f e).Rep (farB f e)
  | .atT => ((((((Scaled.rep_const _).mul (r78farK_rep f)).addN
      ((Scaled.rep_const _).mul (r78farL_rep f))).addN
      ((Scaled.rep_const _).mul (r78farMLo_rep f .atT))).addN
      ((Scaled.rep_const _).mul (r78farC_rep f))).addN (Scaled.rep_const _)).addN
      (((Scaled.rep_const _).mul (r78farC_rep f)).mul ((r78one_rep.addN r78C10_rep).addN r78S11_rep))
      |>.subN (((r78farC_rep f).mul (Scaled.rep_const _)).mul r78S9_rep)
  | .atA => ((((Scaled.rep_const _).mul (r78farK_rep f)).addN
      ((Scaled.rep_const _).mul (r78farL_rep f))).addN
      ((Scaled.rep_const _).mul (r78farC_rep f))).addN (Scaled.rep_const _)
      |>.addN ((r78farL_rep f).mul (r78_rep_ite r78J0_rep r78J1_rep))
private def r78farPH (f : Family) : Scaled := r78one.addN ((r78farK f).pow 2)
private theorem r78farPH_rep (f : Family) : (r78farPH f).Rep (farPH f) :=
  r78one_rep.addN ((r78farK_rep f).pow 2)
private def r78farPG (f : Family) : Scaled := ((r78farK f).pow 2).addN ((r78farL f).pow 2)
private theorem r78farPG_rep (f : Family) : (r78farPG f).Rep (farPG f) :=
  ((r78farK_rep f).pow 2).addN ((r78farL_rep f).pow 2)
private def r78farPB (f : Family) (e : Split) : Scaled := ((r78farMHi f e).ksq).addN ((r78farL f).pow 2)
private theorem r78farPB_rep (f : Family) (e : Split) : (r78farPB f e).Rep (farPB f e) :=
  ((r78farMHi_rep f e).ksq).addN ((r78farL_rep f).pow 2)
private def r78farPD (f : Family) : Scaled := r78one.addN ((r78farC f).pow 2)
private theorem r78farPD_rep (f : Family) : (r78farPD f).Rep (farPD f) :=
  r78one_rep.addN ((r78farC_rep f).pow 2)
private def r78farRH (f : Family) : Scaled :=
  (Scaled.const (4/5)).addN ((Scaled.const (3/5)).mul (r78farK f))
private theorem r78farRH_rep (f : Family) : (r78farRH f).Rep (farRH f) :=
  (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78farK_rep f))
private def r78farRG (f : Family) : Scaled :=
  ((Scaled.const (31/50)).mul (r78farK f)).addN ((Scaled.const (3923/5000)).mul (r78farL f))
private theorem r78farRG_rep (f : Family) : (r78farRG f).Rep (farRG f) :=
  ((Scaled.rep_const _).mul (r78farK_rep f)).addN ((Scaled.rep_const _).mul (r78farL_rep f))
private def r78farRB (f : Family) (e : Split) : Scaled :=
  (Scaled.const (7071/10000)).mul ((r78farL f).addN (r78farMu f e))
private theorem r78farRB_rep (f : Family) (e : Split) : (r78farRB f e).Rep (farRB f e) :=
  (Scaled.rep_const _).mul ((r78farL_rep f).addN (r78farMu_rep f e))
private def r78farRD (f : Family) : Scaled :=
  (Scaled.const (18/25)).addN ((Scaled.const (347/500)).mul (r78farC f))
private theorem r78farRD_rep (f : Family) : (r78farRD f).Rep (farRD f) :=
  (Scaled.rep_const _).addN ((Scaled.rep_const _).mul (r78farC_rep f))
private def r78farQStar : Scaled :=
  (r78farL .high).addN ((Scaled.const (3/20)).mul ((Scaled.const h).subN Scaled.var))
private theorem r78farQStar_rep : r78farQStar.Rep farQStar :=
  (r78farL_rep .high).addN ((Scaled.rep_const _).mul ((Scaled.rep_const _).subN Scaled.rep_var))

/-- Composition with the EH shift of each far case. -/
private def r78dfar (r : FarCase) (S : Scaled) : Scaled :=
  if r=.lowUH ∨ r=.lowUB then r78dr S
  else if r=.highHu ∨ r=.highGu ∨ r=.highBu then r78du S else r78dv S
private theorem r78dfar_rep (r : FarCase) {S : Scaled} {q : ℚ[X]} (hS : S.Rep q) :
    (r78dfar r S).Rep (q.comp (farDelta r)) := by
  cases r
  · exact r78dr_rep hS
  · exact r78dr_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78dv_rep hS
  · exact r78du_rep hS
  · exact r78du_rep hS
  · exact r78du_rep hS
private def r78farDelta (r : FarCase) : Scaled :=
  if r=.lowUH ∨ r=.lowUB then (Scaled.const v).subN Scaled.var
  else Scaled.var.subN (Scaled.const (farS r))
private theorem r78farDelta_rep (r : FarCase) : (r78farDelta r).Rep (farDelta r) :=
  r78_rep_ite ((Scaled.rep_const _).subN Scaled.rep_var) (Scaled.rep_var.subN (Scaled.rep_const _))
private def r78GStarS (r : FarCase) : Scaled :=
  if r=.highHu ∨ r=.highGu ∨ r=.highBu then r78GStarU else r78GStarV
private theorem r78GStarS_rep (r : FarCase) : (r78GStarS r).Rep (C (GStar (farS r))) := by
  cases r
  iterate 8 exact r78GStarV_rep
  iterate 3 exact r78GStarU_rep

private def r78farP (r : FarCase) (e : Split) : Fin 4 → Scaled :=
  let f := farFamily r
  ![if r=.lowUH then (r78farPH f).addN (((Scaled.const 2).mul (r78farK f)).mul (r78dfar r r78S9))
      else (r78farPH f).subN (if farNegativeH r then
        ((Scaled.const 2).mul (r78farK f)).mul (r78dfar r r78S11) else r78Z),
    (r78farPG f).subN (if farNegativeG r then
      (((Scaled.const 2).mul (r78farK f)).mul (r78farL f)).mul (r78dfar r r78S11) else r78Z),
    if r=.lowUB then (r78farPB f e).addN
        ((((Scaled.const 2).mul (r78farL f)).mul (r78farMHi f e)).kmul (r78dfar r r78S9))
      else (r78farPB f e).subN (if farNegativeB r then
        (((Scaled.const 2).mul (r78farL f)).mul (r78farMLo f e)).kmul (r78dfar r r78S11) else r78Z),
    r78farPD f]
private theorem r78farP_rep (r : FarCase) (e : Split) (i : Fin 4) :
    (r78farP r e i).Rep (farP r e i) := by
  fin_cases i
  · exact r78_rep_ite ((r78farPH_rep _).addN
        (((Scaled.rep_const _).mul (r78farK_rep _)).mul (r78dfar_rep r r78S9_rep)))
      ((r78farPH_rep _).subN (r78_rep_ite
        (((Scaled.rep_const _).mul (r78farK_rep _)).mul (r78dfar_rep r r78S11_rep)) r78Z_rep))
  · exact (r78farPG_rep _).subN (r78_rep_ite
      ((((Scaled.rep_const _).mul (r78farK_rep _)).mul (r78farL_rep _)).mul
        (r78dfar_rep r r78S11_rep)) r78Z_rep)
  · exact r78_rep_ite ((r78farPB_rep _ _).addN
        ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78farMHi_rep _ _)).kmul
          (r78dfar_rep r r78S9_rep)))
      ((r78farPB_rep _ _).subN (r78_rep_ite
        ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78farMLo_rep _ _)).kmul
          (r78dfar_rep r r78S11_rep)) r78Z_rep))
  · exact r78farPD_rep _

private def r78farMass (r : FarCase) (e : Split) : Fin 4 → Scaled :=
  let f := farFamily r
  ![if r=.lowUH then ((Scaled.const (209/250)).mul (r78dfar r r78C2)).addN
        ((Scaled.const (137/250)).mul ((r78farK f).addN (r78dfar r r78S3)))
      else if r=.lowVH then ((Scaled.const (89/100)).mul (r78dfar r r78C2)).addN
        ((Scaled.const (57/125)).mul ((r78farK f).subN (r78dfar r r78S3)))
      else if farNegativeH r then ((Scaled.const (47/50)).mul (r78dfar r r78C4)).addN
        ((Scaled.const (853/2500)).mul ((r78farK f).subN (r78dfar r r78S5)))
      else r78farRH f,
    if r=.lowVG then (((Scaled.const (89/100)).mul (r78farL f)).mul (r78dfar r r78C2)).addN
        ((Scaled.const (57/125)).mul ((r78farK f).subN ((r78farL f).mul (r78dfar r r78S3))))
      else if farNegativeG r then
        (((Scaled.const (179/200)).mul (r78farL f)).mul (r78dfar r r78C4)).addN
        ((Scaled.const (223/500)).mul ((r78farK f).subN ((r78farL f).mul (r78dfar r r78S5))))
      else r78farRG f,
    if r=.lowUB then (((Scaled.const (16/25)).mul (r78farL f)).mul (r78dfar r r78C2)).addN
        ((Scaled.const (96/125)).mul ((r78farMu f e).addN ((r78farL f).mul (r78dfar r r78S3))))
      else if farNegativeB r then
        (((Scaled.const (41/50)).mul (r78farL f)).mul (r78dfar r r78C4)).addN
        ((Scaled.const (143/250)).mul ((r78farMu f e).subN ((r78farL f).mul (r78dfar r r78S5))))
      else r78farRB f e,
    r78farRD f]
private theorem r78farMass_rep (r : FarCase) (e : Split) (i : Fin 4) :
    (r78farMass r e i).Rep (farMass r e i) := by
  fin_cases i
  · exact r78_rep_ite (((Scaled.rep_const _).mul (r78dfar_rep r r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).addN (r78dfar_rep r r78S3_rep))))
      (r78_rep_ite (((Scaled.rep_const _).mul (r78dfar_rep r r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).subN (r78dfar_rep r r78S3_rep))))
      (r78_rep_ite (((Scaled.rep_const _).mul (r78dfar_rep r r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).subN (r78dfar_rep r r78S5_rep))))
        (r78farRH_rep _)))
  · exact r78_rep_ite ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78dfar_rep r r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).subN ((r78farL_rep _).mul (r78dfar_rep r r78S3_rep)))))
      (r78_rep_ite ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78dfar_rep r r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78farK_rep _).subN ((r78farL_rep _).mul (r78dfar_rep r r78S5_rep)))))
        (r78farRG_rep _))
  · exact r78_rep_ite ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78dfar_rep r r78C2_rep)).addN
        ((Scaled.rep_const _).mul ((r78farMu_rep _ _).addN ((r78farL_rep _).mul (r78dfar_rep r r78S3_rep)))))
      (r78_rep_ite ((((Scaled.rep_const _).mul (r78farL_rep _)).mul (r78dfar_rep r r78C4_rep)).addN
        ((Scaled.rep_const _).mul ((r78farMu_rep _ _).subN ((r78farL_rep _).mul (r78dfar_rep r r78S5_rep)))))
        (r78farRB_rep _ _))
  · exact r78farRD_rep _

private def r78farNonrad (r : FarCase) (e : Split) : Scaled :=
  let f := farFamily r
  if r=.lowZero then (r78farB f e).addN r78GPoly
  else ((r78farB f e).addN (r78GStarS r)).addN
    (if r=.lowUH then ((r78farK f).mul (((r78dfar r r78C10).addN (r78dfar r r78S11)).subN r78one)).subN
        ((Scaled.const epsilon).mul (r78farDelta r))
     else if r=.lowUB then
        ((r78farL f).mul (((r78dfar r r78C10).addN (r78dfar r r78S11)).subN r78one)).subN
        ((Scaled.const epsilon).mul (r78farDelta r))
     else (if farNegativeG r then r78farL f else if farNegativeB r then r78farQStar else r78one).mul
       ((r78dfar r r78C10).subN r78one))
private theorem r78farNonrad_rep (r : FarCase) (e : Split) :
    (r78farNonrad r e).Rep (farNonradical r e) :=
  r78_rep_ite ((r78farB_rep _ e).addN r78GPoly_rep)
    (((r78farB_rep _ e).addN (r78GStarS_rep r)).addN
      (r78_rep_ite (((r78farK_rep _).mul
          (((r78dfar_rep r r78C10_rep).addN (r78dfar_rep r r78S11_rep)).subN r78one_rep)).subN
          ((Scaled.rep_const _).mul (r78farDelta_rep r)))
        (r78_rep_ite (((r78farL_rep _).mul
          (((r78dfar_rep r r78C10_rep).addN (r78dfar_rep r r78S11_rep)).subN r78one_rep)).subN
          ((Scaled.rep_const _).mul (r78farDelta_rep r)))
          ((r78_rep_ite (r78farL_rep _) (r78_rep_ite r78farQStar_rep r78one_rep)).mul
            ((r78dfar_rep r r78C10_rep).subN r78one_rep)))))

private def r78farNum (r : FarCase) (e : Split) : Scaled :=
  r78num4 (r78farNonrad r e) (r78farP r e 0) (r78farP r e 1) (r78farP r e 2) (r78farP r e 3)
    (r78farMass r e 0) (r78farMass r e 1) (r78farMass r e 2) (r78farMass r e 3)
private theorem r78farNum_rep (r : FarCase) (e : Split) :
    (r78farNum r e).Rep (farNumerator r e) :=
  r78num4_rep (r78farNonrad_rep r e) (r78farP_rep r e 0) (r78farP_rep r e 1) (r78farP_rep r e 2)
    (r78farP_rep r e 3) (r78farMass_rep r e 0) (r78farMass_rep r e 1) (r78farMass_rep r e 2)
    (r78farMass_rep r e 3)

/-! Integer forms of the two reserve comparisons. -/

private theorem r78_lt {c : Scaled} {Z : ℤ} {ρ : ℚ} (n : ℤ) (d : ℕ) (hρ : ρ=n/d) (hd : 0<d)
    (hs : c.s≠0) (h : n*((c.s*2^c.l.length:ℕ):ℤ)<2*d*Z) :
    ρ<(Z:ℚ)/(c.s*2^c.l.length/2) := by
  have hS : (0:ℚ)<c.s*2^c.l.length/2 := WholeIntervalPolynomial.Certificate.scale_pos hs
  rw [hρ,div_lt_div_iff₀ (by exact_mod_cast hd) hS]
  have h' : ((n*((c.s*2^c.l.length:ℕ):ℤ):ℤ):ℚ)<((2*d*Z:ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith


private theorem r78_quad_core {B : ℕ → ℤ} {K : ℚ} {M : ℕ} {ρ : ℚ} (cnt : ℕ) (n : ℤ) (d : ℕ)
    (hK : K=M/2) (hM : 0<M) (hρ : ρ=n/d) (hd : 0<d) (h2 : 0<B 2)
    (h : 4*B 2*n*M<d*(8*B 2*(B 0-B 2-∑ j : Fin cnt,|B (j.val+3)|)-(B 1)^2)) :
    0<(fun j => (B j:ℚ)/K) 2 ∧ ρ<quadraticReserve (fun j => (B j:ℚ)/K) cnt := by
  have hM' : (0:ℚ)<M := by exact_mod_cast hM
  have hK0 : 0<K := by rw [hK]; linarith
  have hB2 : (0:ℚ)<B 2 := by exact_mod_cast h2
  refine ⟨div_pos hB2 hK0,?_⟩
  obtain ⟨T,hT⟩ : ∃T : ℚ,T=∑ j : Fin cnt,|(B (j.val+3):ℚ)| := ⟨_,rfl⟩
  have hsum : tailNorm (fun j => (B j:ℚ)/K) 3 cnt=T/K := by
    rw [tailNorm,hT,Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [abs_div,abs_of_pos hK0]
  unfold quadraticReserve
  rw [hsum]
  have e : (B 0:ℚ)/K-B 2/K-(B 1/K)^2/(8*(B 2/K))-T/K=
      (8*B 2*(B 0-B 2-T)-(B 1)^2)/(8*B 2*K) := by
    field_simp
    ring
  show ρ<(B 0:ℚ)/K-B 2/K-(B 1/K)^2/(8*(B 2/K))-T/K
  rw [e,hρ,div_lt_div_iff₀ (by exact_mod_cast hd) (by positivity)]
  have h' : ((4*B 2*n*M:ℤ):ℚ)<((d*(8*B 2*(B 0-B 2-∑ j : Fin cnt,|B (j.val+3)|)-(B 1)^2):ℤ):ℚ) := by
    exact_mod_cast h
  push_cast at h'
  rw [← hT] at h'
  rw [hK]
  linarith

private theorem r78_series_quad (c : ℕ → ℚ) (n : ℕ) :
    series (n+2) c=C (c 0-c 2)+C (c 1)*X+C (2*c 2)*X^2+tail c 3 n := by
  rw [series,tail,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,Nat.cast_zero,
    zero_add]
  have hrest : ∀ j : Fin n,C (c (j.val+1+1+1))*
      Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+1+1+1)=
      C (c (j.val+3))*Polynomial.Chebyshev.T ℚ ((j.val:ℤ)+3) := fun j => by
    ring_nf
  simp only [hrest,Polynomial.Chebyshev.T_one,show (1:ℕ)+1=2 from rfl,show (1:ℤ)+1=2 by norm_num,
    Polynomial.Chebyshev.T_two,map_sub,map_mul,map_ofNat]
  ring

private theorem r78_I0 : (0+v:ℚ)/2=((1:ℕ):ℚ)*((1:ℤ):ℚ)/((20:ℕ):ℚ) ∧
    (v-0:ℚ)/2=((1:ℕ):ℚ)*((1:ℤ):ℚ)/((20:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_I1 : (v+L:ℚ)/2=((1:ℕ):ℚ)*((4:ℤ):ℚ)/((30:ℕ):ℚ) ∧
    (L-v:ℚ)/2=((1:ℕ):ℚ)*((1:ℤ):ℚ)/((30:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_I2 : (L+h:ℚ)/2=((1:ℕ):ℚ)*((13:ℤ):ℚ)/((30:ℕ):ℚ) ∧
    (h-L:ℚ)/2=((1:ℕ):ℚ)*((8:ℤ):ℚ)/((30:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_I3 : (v+u:ℚ)/2=((1:ℕ):ℚ)*((7:ℤ):ℚ)/((40:ℕ):ℚ) ∧
    (u-v:ℚ)/2=((1:ℕ):ℚ)*((3:ℤ):ℚ)/((40:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_I4 : (u+h:ℚ)/2=((1:ℕ):ℚ)*((19:ℤ):ℚ)/((40:ℕ):ℚ) ∧
    (h-u:ℚ)/2=((1:ℕ):ℚ)*((9:ℤ):ℚ)/((40:ℕ):ℚ) := by
  norm_num [v,u,L,h]

private theorem r78_ρ35 : (3/5:ℚ)=((3:ℤ):ℚ)/((5:ℕ):ℚ) := by norm_num

/-- One whole-interval certificate from its kernel-checked integer facts. -/
private theorem r78_cert {S : Scaled} {a b ρ : ℚ} {p : ℚ[X]} {D : ℕ} (num den : ℕ) (s t : ℤ)
    (hS : S.Rep p) (hden : den≠0) (hab : (a+b)/2=num*s/den ∧ (b-a)/2=num*t/den)
    (n : ℤ) (d : ℕ) (hρ : ρ=n/d) (hd : 0<d)
    (hk : (S.kcenter num den s t).s≠0 ∧ (S.kcenter num den s t).l.length≤D+1 ∧
      n*(((S.kcenter num den s t).s*2^(S.kcenter num den s t).l.length:ℕ):ℤ)<
        2*d*lowerZ D (fun j => (chebList (S.kcenter num den s t).l).getD j 0)) :
    centered a b p=expansion D (centered a b p) ∧ ρ<lowerOn D a b p := by
  have hc := hS.kcentered num den s t hden hab.1 hab.2
  exact ⟨hc.eq_expansion hk.1 hk.2.1,
    by rw [lowerOn_eq_of_rep hc hk.1 hk.2.1]; exact r78_lt n d hρ hd hk.1 hk.2.2⟩

/-! The kernel facts. The cases on one interval share their polynomials, so each interval is
one kernel evaluation, and the fact of each case is a projection of it. -/

set_option Elab.async false in
set_option maxRecDepth 1000000 in
private theorem r78g_S_lowZero :
    (((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l.length ≤ smallDegree .lowZero .atA+1 ∧
    (8991:ℤ)*((((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((100000:ℕ):ℤ)*lowerZ (smallDegree .lowZero .atA)
      (fun j => (chebList ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length≤32+1 ∧ 0<(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0 ∧
    4*(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0*(183947:ℤ)*((((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<
      ((10000000:ℕ):ℤ)*(8*(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0*((chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 0 0-(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0-
        ∑ j : Fin 30,|(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD (j.val+3) 0|)-((chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 1 0)^2)) := by
  decide +kernel

private theorem r78kSD_lowZero_atA : ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l.length ≤ smallDegree .lowZero .atA+1 ∧
    (8991:ℤ)*((((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((100000:ℕ):ℤ)*lowerZ (smallDegree .lowZero .atA)
      (fun j => (chebList ((r78smallNum .lowZero .atA).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.1

private theorem r78kSM_lowZero_atT_0 : ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.1

private theorem r78kSM_lowZero_atT_1 : ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.1

private theorem r78kSM_lowZero_atT_2 : ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.1

private theorem r78kSM_lowZero_atT_3 : ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atT 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.1

private theorem r78kSM_lowZero_atA_0 : ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.2.1

private theorem r78kSM_lowZero_atA_1 : ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.2.2.1

private theorem r78kSM_lowZero_atA_2 : ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.2.2.2.1

private theorem r78kSM_lowZero_atA_3 : ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).s*2^((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowZero .atA 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_S_lowZero.2.2.2.2.2.2.2.2.1

private theorem r78kSQ_lowZero : ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length≤32+1 ∧ 0<(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0 ∧
    4*(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0*(183947:ℤ)*((((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<
      ((10000000:ℕ):ℤ)*(8*(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0*((chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 0 0-(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 2 0-
        ∑ j : Fin 30,|(chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD (j.val+3) 0|)-((chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD 1 0)^2) := r78g_S_lowZero.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option maxRecDepth 1000000 in
private theorem r78g_S_lowH :
    (((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l.length ≤ smallDegree .lowH .atA+1 ∧
    (94417:ℤ)*((((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .lowH .atA)
      (fun j => (chebList ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l).getD j 0)) ∧
    (((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length≤33+1 ∧ 0<(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0 ∧
    4*(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0*(27740:ℤ)*((((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<
      ((10000000:ℕ):ℤ)*(8*(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0*((chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 0 0-(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0-
        ∑ j : Fin 31,|(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD (j.val+3) 0|)-((chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 1 0)^2)) := by
  decide +kernel

private theorem r78kSD_lowH_atA : ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l.length ≤ smallDegree .lowH .atA+1 ∧
    (94417:ℤ)*((((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .lowH .atA)
      (fun j => (chebList ((r78smallNum .lowH .atA).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.1

private theorem r78kSM_lowH_atT_0 : ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 0).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.1

private theorem r78kSM_lowH_atT_1 : ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 1).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.1

private theorem r78kSM_lowH_atT_2 : ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 2).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.1

private theorem r78kSM_lowH_atT_3 : ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atT 3).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.1

private theorem r78kSM_lowH_atA_0 : ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 0).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.2.1

private theorem r78kSM_lowH_atA_1 : ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 1).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.2.2.1

private theorem r78kSM_lowH_atA_2 : ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 2).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.2.2.2.1

private theorem r78kSM_lowH_atA_3 : ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).s*2^((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .lowH .atA 3).kcenter 1 30 (4) (1)).l).getD j 0) := r78g_S_lowH.2.2.2.2.2.2.2.2.1

private theorem r78kSQ_lowH : ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s≠0 ∧ ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length≤33+1 ∧ 0<(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0 ∧
    4*(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0*(27740:ℤ)*((((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length:ℕ):ℤ)<
      ((10000000:ℕ):ℤ)*(8*(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0*((chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 0 0-(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 2 0-
        ∑ j : Fin 31,|(chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD (j.val+3) 0|)-((chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD 1 0)^2) := r78g_S_lowH.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_S_high :
    (((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highH .atT+1 ∧
    (8161:ℤ)*((((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highH .atT)
      (fun j => (chebList ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highH .atA+1 ∧
    (7429:ℤ)*((((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highH .atA)
      (fun j => (chebList ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highG .atT+1 ∧
    (49256:ℤ)*((((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highG .atT)
      (fun j => (chebList ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highG .atA+1 ∧
    (45860:ℤ)*((((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highG .atA)
      (fun j => (chebList ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highB .atT+1 ∧
    (344132:ℤ)*((((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highB .atT)
      (fun j => (chebList ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highB .atA+1 ∧
    (923872:ℤ)*((((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highB .atA)
      (fun j => (chebList ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l).getD j 0)) ∧
    (((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l).getD j 0)) := by
  decide +kernel

private theorem r78kSD_highH_atT : ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highH .atT+1 ∧
    (8161:ℤ)*((((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highH .atT)
      (fun j => (chebList ((r78smallNum .highH .atT).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.1

private theorem r78kSD_highH_atA : ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highH .atA+1 ∧
    (7429:ℤ)*((((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highH .atA)
      (fun j => (chebList ((r78smallNum .highH .atA).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.1

private theorem r78kSD_highG_atT : ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highG .atT+1 ∧
    (49256:ℤ)*((((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highG .atT)
      (fun j => (chebList ((r78smallNum .highG .atT).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.1

private theorem r78kSD_highG_atA : ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highG .atA+1 ∧
    (45860:ℤ)*((((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highG .atA)
      (fun j => (chebList ((r78smallNum .highG .atA).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.1

private theorem r78kSD_highB_atT : ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highB .atT+1 ∧
    (344132:ℤ)*((((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highB .atT)
      (fun j => (chebList ((r78smallNum .highB .atT).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.1

private theorem r78kSD_highB_atA : ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l.length ≤ smallDegree .highB .atA+1 ∧
    (923872:ℤ)*((((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).s*2^((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (smallDegree .highB .atA)
      (fun j => (chebList ((r78smallNum .highB .atA).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.1

private theorem r78kSM_highH_atT_0 : ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.1

private theorem r78kSM_highH_atT_1 : ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atT_2 : ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atT_3 : ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atT 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atA_0 : ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atA_1 : ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atA_2 : ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highH_atA_3 : ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highH .atA 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atT_0 : ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atT_1 : ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atT_2 : ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atT_3 : ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atT 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atA_0 : ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atA_1 : ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atA_2 : ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highG_atA_3 : ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highG .atA 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atT_0 : ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atT_1 : ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atT_2 : ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atT_3 : ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atT 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atA_0 : ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 0).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atA_1 : ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 1).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atA_2 : ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 2).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kSM_highB_atA_3 : ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).s≠0 ∧ ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l.length≤12+1 ∧
    (3:ℤ)*((((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).s*2^((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78smallMass .highB .atA 3).kcenter 1 30 (13) (8)).l).getD j 0) := r78g_S_high.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_F_lowU :
    (((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUH .atT+1 ∧
    (98274:ℤ)*((((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUH .atT)
      (fun j => (chebList ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUH .atA+1 ∧
    (441112:ℤ)*((((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUH .atA)
      (fun j => (chebList ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUB .atT+1 ∧
    (145059:ℤ)*((((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUB .atT)
      (fun j => (chebList ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUB .atA+1 ∧
    (508864:ℤ)*((((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUB .atA)
      (fun j => (chebList ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l).getD j 0)) ∧
    (((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l).getD j 0)) := by
  decide +kernel

private theorem r78kFD_lowUH_atT : ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUH .atT+1 ∧
    (98274:ℤ)*((((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUH .atT)
      (fun j => (chebList ((r78farNum .lowUH .atT).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.1

private theorem r78kFD_lowUH_atA : ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUH .atA+1 ∧
    (441112:ℤ)*((((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUH .atA)
      (fun j => (chebList ((r78farNum .lowUH .atA).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.1

private theorem r78kFD_lowUB_atT : ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUB .atT+1 ∧
    (145059:ℤ)*((((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUB .atT)
      (fun j => (chebList ((r78farNum .lowUB .atT).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.1

private theorem r78kFD_lowUB_atA : ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l.length ≤ farDegree .lowUB .atA+1 ∧
    (508864:ℤ)*((((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).s*2^((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowUB .atA)
      (fun j => (chebList ((r78farNum .lowUB .atA).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.1

private theorem r78kFM_lowUH_atT_0 : ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.1

private theorem r78kFM_lowUH_atT_1 : ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.1

private theorem r78kFM_lowUH_atT_2 : ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atT_3 : ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atT 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atA_0 : ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atA_1 : ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atA_2 : ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUH_atA_3 : ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUH .atA 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atT_0 : ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atT_1 : ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atT_2 : ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atT_3 : ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atT 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atA_0 : ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 0).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atA_1 : ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 1).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atA_2 : ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 2).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowUB_atA_3 : ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).s≠0 ∧ ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).s*2^((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowUB .atA 3).kcenter 1 20 (1) (1)).l).getD j 0) := r78g_F_lowU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_F_lowV :
    (((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVH .atT+1 ∧
    (246572:ℤ)*((((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVH .atT)
      (fun j => (chebList ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVH .atA+1 ∧
    (293761:ℤ)*((((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVH .atA)
      (fun j => (chebList ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVG .atT+1 ∧
    (220630:ℤ)*((((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVG .atT)
      (fun j => (chebList ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVG .atA+1 ∧
    (165940:ℤ)*((((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVG .atA)
      (fun j => (chebList ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowZero .atT+1 ∧
    (201415:ℤ)*((((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowZero .atT)
      (fun j => (chebList ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowZero .atA+1 ∧
    (145527:ℤ)*((((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowZero .atA)
      (fun j => (chebList ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l).getD j 0)) ∧
    (((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l).getD j 0)) := by
  decide +kernel

private theorem r78kFD_lowVH_atT : ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVH .atT+1 ∧
    (246572:ℤ)*((((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVH .atT)
      (fun j => (chebList ((r78farNum .lowVH .atT).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.1

private theorem r78kFD_lowVH_atA : ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVH .atA+1 ∧
    (293761:ℤ)*((((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVH .atA)
      (fun j => (chebList ((r78farNum .lowVH .atA).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.1

private theorem r78kFD_lowVG_atT : ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVG .atT+1 ∧
    (220630:ℤ)*((((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVG .atT)
      (fun j => (chebList ((r78farNum .lowVG .atT).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.1

private theorem r78kFD_lowVG_atA : ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowVG .atA+1 ∧
    (165940:ℤ)*((((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowVG .atA)
      (fun j => (chebList ((r78farNum .lowVG .atA).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.1

private theorem r78kFD_lowZero_atT : ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowZero .atT+1 ∧
    (201415:ℤ)*((((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowZero .atT)
      (fun j => (chebList ((r78farNum .lowZero .atT).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.1

private theorem r78kFD_lowZero_atA : ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l.length ≤ farDegree .lowZero .atA+1 ∧
    (145527:ℤ)*((((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).s*2^((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .lowZero .atA)
      (fun j => (chebList ((r78farNum .lowZero .atA).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.1

private theorem r78kFM_lowVH_atT_0 : ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atT_1 : ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atT_2 : ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atT_3 : ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atT 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atA_0 : ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atA_1 : ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atA_2 : ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVH_atA_3 : ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVH .atA 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atT_0 : ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atT_1 : ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atT_2 : ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atT_3 : ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atT 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atA_0 : ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atA_1 : ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atA_2 : ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowVG_atA_3 : ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowVG .atA 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atT_0 : ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atT_1 : ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atT_2 : ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atT_3 : ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atT 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atA_0 : ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 0).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atA_1 : ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 1).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atA_2 : ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 2).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_lowZero_atA_3 : ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).s≠0 ∧ ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).s*2^((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .lowZero .atA 3).kcenter 1 40 (7) (3)).l).getD j 0) := r78g_F_lowV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_F_highV :
    (((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHv .atT+1 ∧
    (302465:ℤ)*((((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHv .atT)
      (fun j => (chebList ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHv .atA+1 ∧
    (255999:ℤ)*((((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHv .atA)
      (fun j => (chebList ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGv .atT+1 ∧
    (223385:ℤ)*((((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGv .atT)
      (fun j => (chebList ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGv .atA+1 ∧
    (155563:ℤ)*((((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGv .atA)
      (fun j => (chebList ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBv .atT+1 ∧
    (474660:ℤ)*((((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBv .atT)
      (fun j => (chebList ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBv .atA+1 ∧
    (1028199:ℤ)*((((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBv .atA)
      (fun j => (chebList ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) := by
  decide +kernel

private theorem r78kFD_highHv_atT : ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHv .atT+1 ∧
    (302465:ℤ)*((((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHv .atT)
      (fun j => (chebList ((r78farNum .highHv .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.1

private theorem r78kFD_highHv_atA : ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHv .atA+1 ∧
    (255999:ℤ)*((((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHv .atA)
      (fun j => (chebList ((r78farNum .highHv .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.1

private theorem r78kFD_highGv_atT : ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGv .atT+1 ∧
    (223385:ℤ)*((((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGv .atT)
      (fun j => (chebList ((r78farNum .highGv .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.1

private theorem r78kFD_highGv_atA : ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGv .atA+1 ∧
    (155563:ℤ)*((((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGv .atA)
      (fun j => (chebList ((r78farNum .highGv .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.1

private theorem r78kFD_highBv_atT : ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBv .atT+1 ∧
    (474660:ℤ)*((((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBv .atT)
      (fun j => (chebList ((r78farNum .highBv .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.1

private theorem r78kFD_highBv_atA : ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBv .atA+1 ∧
    (1028199:ℤ)*((((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBv .atA)
      (fun j => (chebList ((r78farNum .highBv .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.1

private theorem r78kFM_highHv_atT_0 : ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atT_1 : ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atT_2 : ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atT_3 : ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atA_0 : ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atA_1 : ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atA_2 : ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHv_atA_3 : ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atT_0 : ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atT_1 : ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atT_2 : ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atT_3 : ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atA_0 : ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atA_1 : ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atA_2 : ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGv_atA_3 : ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atT_0 : ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atT_1 : ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atT_2 : ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atT_3 : ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atA_0 : ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atA_1 : ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atA_2 : ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBv_atA_3 : ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBv .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highV.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


set_option Elab.async false in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 1000000 in
private theorem r78g_F_highU :
    (((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHu .atT+1 ∧
    (147124:ℤ)*((((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHu .atT)
      (fun j => (chebList ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHu .atA+1 ∧
    (104322:ℤ)*((((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHu .atA)
      (fun j => (chebList ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGu .atT+1 ∧
    (198910:ℤ)*((((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGu .atT)
      (fun j => (chebList ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGu .atA+1 ∧
    (132153:ℤ)*((((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGu .atA)
      (fun j => (chebList ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBu .atT+1 ∧
    (166633:ℤ)*((((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBu .atT)
      (fun j => (chebList ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBu .atA+1 ∧
    (132561:ℤ)*((((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBu .atA)
      (fun j => (chebList ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0)) ∧
    (((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l.length≤6+1 ∧
    (629:ℤ)*((((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).s*2^((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((1000000:ℕ):ℤ)*lowerZ 6
      (fun j => (chebList ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l).getD j 0)) := by
  decide +kernel

private theorem r78kFD_highHu_atT : ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHu .atT+1 ∧
    (147124:ℤ)*((((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHu .atT)
      (fun j => (chebList ((r78farNum .highHu .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.1

private theorem r78kFD_highHu_atA : ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highHu .atA+1 ∧
    (104322:ℤ)*((((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highHu .atA)
      (fun j => (chebList ((r78farNum .highHu .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.1

private theorem r78kFD_highGu_atT : ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGu .atT+1 ∧
    (198910:ℤ)*((((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGu .atT)
      (fun j => (chebList ((r78farNum .highGu .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.1

private theorem r78kFD_highGu_atA : ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highGu .atA+1 ∧
    (132153:ℤ)*((((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highGu .atA)
      (fun j => (chebList ((r78farNum .highGu .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.1

private theorem r78kFD_highBu_atT : ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBu .atT+1 ∧
    (166633:ℤ)*((((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBu .atT)
      (fun j => (chebList ((r78farNum .highBu .atT).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.1

private theorem r78kFD_highBu_atA : ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l.length ≤ farDegree .highBu .atA+1 ∧
    (132561:ℤ)*((((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).s*2^((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((10000000:ℕ):ℤ)*lowerZ (farDegree .highBu .atA)
      (fun j => (chebList ((r78farNum .highBu .atA).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.1

private theorem r78kFM_highHu_atT_0 : ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atT_1 : ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atT_2 : ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atT_3 : ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atA_0 : ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atA_1 : ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atA_2 : ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highHu_atA_3 : ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highHu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atT_0 : ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atT_1 : ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atT_2 : ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atT_3 : ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atA_0 : ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atA_1 : ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atA_2 : ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highGu_atA_3 : ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highGu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atT_0 : ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atT_1 : ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atT_2 : ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atT_3 : ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atT 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atA_0 : ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 0).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atA_1 : ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 1).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atA_2 : ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 2).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kFM_highBu_atA_3 : ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l.length≤12+1 ∧
    (3:ℤ)*((((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).s*2^((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((5:ℕ):ℤ)*lowerZ 12
      (fun j => (chebList ((r78farMass .highBu .atA 3).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem r78kQS : ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).s≠0 ∧ ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l.length≤6+1 ∧
    (629:ℤ)*((((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).s*2^((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l.length:ℕ):ℤ)<2*((1000000:ℕ):ℤ)*lowerZ 6
      (fun j => (chebList ((r78farQStar.sub (r78farMu .high .atT)).kcenter 1 40 (19) (9)).l).getD j 0) := r78g_F_highU.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2


end r78

theorem small_direct_certificate (r : SmallCase) (e : Split) (hr : smallQuadratic r e=false) :
    centered (smallLeft r) (smallRight r) (smallNumerator r e)=
      expansion (smallDegree r e) (centered (smallLeft r) (smallRight r) (smallNumerator r e)) ∧
    smallReserve r e<lowerOn (smallDegree r e) (smallLeft r) (smallRight r) (smallNumerator r e) := by
  cases r <;> cases e
  · exact absurd hr (by decide)
  · exact r78_cert 1 20 (1) (1) (r78smallNum_rep .lowZero .atA) (by decide) r78_I0 8991 100000 (by norm_num [smallReserve]) (by decide) r78kSD_lowZero_atA
  · exact absurd hr (by decide)
  · exact r78_cert 1 30 (4) (1) (r78smallNum_rep .lowH .atA) (by decide) r78_I1 94417 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_lowH_atA
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highH .atT) (by decide) r78_I2 8161 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highH_atT
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highH .atA) (by decide) r78_I2 7429 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highH_atA
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highG .atT) (by decide) r78_I2 49256 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highG_atT
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highG .atA) (by decide) r78_I2 45860 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highG_atA
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highB .atT) (by decide) r78_I2 344132 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highB_atT
  · exact r78_cert 1 30 (13) (8) (r78smallNum_rep .highB .atA) (by decide) r78_I2 923872 10000000 (by norm_num [smallReserve]) (by decide) r78kSD_highB_atA

def smallCoefficients (r : SmallCase) (e : Split) : ℕ→ℚ :=
  coefficient (smallDegree r e) (centered (smallLeft r) (smallRight r) (smallNumerator r e))

theorem small_quadratic_certificate (r : SmallCase) (e : Split) (hr : smallQuadratic r e=true) :
    centered (smallLeft r) (smallRight r) (smallNumerator r e)=
      C (smallCoefficients r e 0-smallCoefficients r e 2)+C (smallCoefficients r e 1)*X+
      C (2*smallCoefficients r e 2)*X^2+tail (smallCoefficients r e) 3 (smallDegree r e-2) ∧
    0<smallCoefficients r e 2 ∧
    smallReserve r e<quadraticReserve (smallCoefficients r e) (smallDegree r e-2) := by
  cases r <;> cases e
  · obtain ⟨hs,hl,h2,hq⟩ := r78kSQ_lowZero
    have hc := (r78smallNum_rep .lowZero .atT).kcentered 1 20 (1) (1)
      (a:=smallLeft .lowZero) (b:=smallRight .lowZero) (by decide) r78_I0.1 r78_I0.2
    have hexp := hc.eq_expansion hs hl
    have hcoef : smallCoefficients .lowZero .atT=fun j => ((WholeIntervalPolynomial.Certificate.chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD j 0:ℚ)/
        (((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length/2) :=
      WholeIntervalPolynomial.Certificate.coefficient_centered_eq hc hs hl
    refine ⟨?_,?_⟩
    · rw [hexp]
      change series 32 (smallCoefficients .lowZero .atT)=_
      exact r78_series_quad (smallCoefficients .lowZero .atT) 30
    · rw [hcoef]
      rw [show smallDegree .lowZero .atT-2=30 from rfl]
      have hK : (((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s:ℚ)*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length/2=((((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length:ℕ):ℚ)/2 := by
        push_cast; ring
      exact r78_quad_core (B:=fun j => (WholeIntervalPolynomial.Certificate.chebList ((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l).getD j 0)
        (K:=(((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s:ℚ)*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length/2) (M:=((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).s*2^((r78smallNum .lowZero .atT).kcenter 1 20 (1) (1)).l.length) (ρ:=smallReserve .lowZero .atT)
        30 183947 10000000 hK (Nat.mul_pos (Nat.pos_of_ne_zero hs) (by positivity))
        (by norm_num [smallReserve]) (by decide) h2 hq
  · exact absurd hr (by decide)
  · obtain ⟨hs,hl,h2,hq⟩ := r78kSQ_lowH
    have hc := (r78smallNum_rep .lowH .atT).kcentered 1 30 (4) (1)
      (a:=smallLeft .lowH) (b:=smallRight .lowH) (by decide) r78_I1.1 r78_I1.2
    have hexp := hc.eq_expansion hs hl
    have hcoef : smallCoefficients .lowH .atT=fun j => ((WholeIntervalPolynomial.Certificate.chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD j 0:ℚ)/
        (((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length/2) :=
      WholeIntervalPolynomial.Certificate.coefficient_centered_eq hc hs hl
    refine ⟨?_,?_⟩
    · rw [hexp]
      change series 33 (smallCoefficients .lowH .atT)=_
      exact r78_series_quad (smallCoefficients .lowH .atT) 31
    · rw [hcoef]
      rw [show smallDegree .lowH .atT-2=31 from rfl]
      have hK : (((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s:ℚ)*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length/2=((((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length:ℕ):ℚ)/2 := by
        push_cast; ring
      exact r78_quad_core (B:=fun j => (WholeIntervalPolynomial.Certificate.chebList ((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l).getD j 0)
        (K:=(((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s:ℚ)*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length/2) (M:=((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).s*2^((r78smallNum .lowH .atT).kcenter 1 30 (4) (1)).l.length) (ρ:=smallReserve .lowH .atT)
        31 27740 10000000 hK (Nat.mul_pos (Nat.pos_of_ne_zero hs) (by positivity))
        (by norm_num [smallReserve]) (by decide) h2 hq
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)
  · exact absurd hr (by decide)

theorem small_numerator_positive (r : SmallCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) : 0<aeval θ (smallNumerator r e) := by
  have hreserve : (0:ℝ)<(smallReserve r e:ℝ) := by
    cases r <;> cases e <;> norm_num [smallReserve]
  cases hr : smallQuadratic r e
  · have hc := small_direct_certificate r e hr
    exact hreserve.trans (positive_on_interval (small_interval r) hc.1 hc.2 hθ)
  · have hc := small_quadratic_certificate r e hr
    have hh := quadratic_on_interval (small_interval r) hc.1 hc.2.1 hθ
    have hq : (smallReserve r e:ℝ)<
        (quadraticReserve (smallCoefficients r e) (smallDegree r e-2):ℝ) := by
      exact_mod_cast hc.2.2
    exact (hreserve.trans hq).trans_le hh

theorem small_mass_certificate (r : SmallCase) (e : Split) (i : Fin 4) :
    centered (smallLeft r) (smallRight r) (smallMass r e i)=
      expansion 12 (centered (smallLeft r) (smallRight r) (smallMass r e i)) ∧
    (3/5:ℚ)<lowerOn 12 (smallLeft r) (smallRight r) (smallMass r e i) := by
  cases r <;> cases e <;> fin_cases i
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atT 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atT_0
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atT 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atT_1
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atT 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atT_2
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atT 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atT_3
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atA 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atA_0
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atA 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atA_1
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atA 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atA_2
  · exact r78_cert 1 20 (1) (1) (r78smallMass_rep .lowZero .atA 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kSM_lowZero_atA_3
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atT 0) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atT_0
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atT 1) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atT_1
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atT 2) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atT_2
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atT 3) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atT_3
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atA 0) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atA_0
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atA 1) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atA_1
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atA 2) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atA_2
  · exact r78_cert 1 30 (4) (1) (r78smallMass_rep .lowH .atA 3) (by decide) r78_I1 3 5 r78_ρ35 (by decide) r78kSM_lowH_atA_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atT 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atT_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atT 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atT_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atT 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atT_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atT 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atT_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atA 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atA_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atA 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atA_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atA 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atA_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highH .atA 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highH_atA_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atT 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atT_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atT 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atT_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atT 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atT_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atT 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atT_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atA 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atA_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atA 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atA_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atA 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atA_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highG .atA 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highG_atA_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atT 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atT_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atT 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atT_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atT 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atT_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atT 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atT_3
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atA 0) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atA_0
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atA 1) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atA_1
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atA 2) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atA_2
  · exact r78_cert 1 30 (13) (8) (r78smallMass_rep .highB .atA 3) (by decide) r78_I2 3 5 r78_ρ35 (by decide) r78kSM_highB_atA_3

theorem small_mass_positive (r : SmallCase) (e : Split) (i : Fin 4) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) : 0<aeval θ (smallMass r e i) := by
  have hc := small_mass_certificate r e i
  have hh := positive_on_interval (small_interval r) hc.1 hc.2 hθ
  norm_num at hh
  linarith

theorem far_certificate (r : FarCase) (e : Split) :
    centered (farLeft r) (farRight r) (farNumerator r e)=
      expansion (farDegree r e) (centered (farLeft r) (farRight r) (farNumerator r e)) ∧
    farReserve r e<lowerOn (farDegree r e) (farLeft r) (farRight r) (farNumerator r e) := by
  cases r <;> cases e
  · exact r78_cert 1 20 (1) (1) (r78farNum_rep .lowUH .atT) (by decide) r78_I0 98274 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowUH_atT
  · exact r78_cert 1 20 (1) (1) (r78farNum_rep .lowUH .atA) (by decide) r78_I0 441112 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowUH_atA
  · exact r78_cert 1 20 (1) (1) (r78farNum_rep .lowUB .atT) (by decide) r78_I0 145059 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowUB_atT
  · exact r78_cert 1 20 (1) (1) (r78farNum_rep .lowUB .atA) (by decide) r78_I0 508864 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowUB_atA
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowVH .atT) (by decide) r78_I3 246572 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowVH_atT
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowVH .atA) (by decide) r78_I3 293761 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowVH_atA
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowVG .atT) (by decide) r78_I3 220630 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowVG_atT
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowVG .atA) (by decide) r78_I3 165940 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowVG_atA
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowZero .atT) (by decide) r78_I3 201415 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowZero_atT
  · exact r78_cert 1 40 (7) (3) (r78farNum_rep .lowZero .atA) (by decide) r78_I3 145527 10000000 (by norm_num [farReserve]) (by decide) r78kFD_lowZero_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highHv .atT) (by decide) r78_I4 302465 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highHv_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highHv .atA) (by decide) r78_I4 255999 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highHv_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highGv .atT) (by decide) r78_I4 223385 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highGv_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highGv .atA) (by decide) r78_I4 155563 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highGv_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highBv .atT) (by decide) r78_I4 474660 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highBv_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highBv .atA) (by decide) r78_I4 1028199 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highBv_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highHu .atT) (by decide) r78_I4 147124 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highHu_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highHu .atA) (by decide) r78_I4 104322 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highHu_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highGu .atT) (by decide) r78_I4 198910 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highGu_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highGu .atA) (by decide) r78_I4 132153 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highGu_atA
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highBu .atT) (by decide) r78_I4 166633 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highBu_atT
  · exact r78_cert 1 40 (19) (9) (r78farNum_rep .highBu .atA) (by decide) r78_I4 132561 10000000 (by norm_num [farReserve]) (by decide) r78kFD_highBu_atA

theorem far_numerator_positive (r : FarCase) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : 0<aeval θ (farNumerator r e) := by
  have hc := far_certificate r e
  have hh := positive_on_interval (far_interval r) hc.1 hc.2 hθ
  have hr : (0:ℝ)<(farReserve r e:ℝ) := by cases r <;> cases e <;> norm_num [farReserve]
  exact hr.trans hh

theorem far_mass_certificate (r : FarCase) (e : Split) (i : Fin 4) :
    centered (farLeft r) (farRight r) (farMass r e i)=
      expansion 12 (centered (farLeft r) (farRight r) (farMass r e i)) ∧
    (3/5:ℚ)<lowerOn 12 (farLeft r) (farRight r) (farMass r e i) := by
  cases r <;> cases e <;> fin_cases i
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atT 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atT_0
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atT 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atT_1
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atT 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atT_2
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atT 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atT_3
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atA 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atA_0
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atA 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atA_1
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atA 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atA_2
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUH .atA 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUH_atA_3
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atT 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atT_0
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atT 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atT_1
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atT 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atT_2
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atT 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atT_3
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atA 0) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atA_0
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atA 1) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atA_1
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atA 2) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atA_2
  · exact r78_cert 1 20 (1) (1) (r78farMass_rep .lowUB .atA 3) (by decide) r78_I0 3 5 r78_ρ35 (by decide) r78kFM_lowUB_atA_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atT 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atT_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atT 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atT_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atT 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atT_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atT 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atT_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atA 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atA_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atA 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atA_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atA 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atA_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVH .atA 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVH_atA_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atT 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atT_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atT 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atT_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atT 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atT_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atT 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atT_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atA 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atA_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atA 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atA_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atA 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atA_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowVG .atA 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowVG_atA_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atT 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atT_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atT 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atT_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atT 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atT_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atT 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atT_3
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atA 0) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atA_0
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atA 1) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atA_1
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atA 2) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atA_2
  · exact r78_cert 1 40 (7) (3) (r78farMass_rep .lowZero .atA 3) (by decide) r78_I3 3 5 r78_ρ35 (by decide) r78kFM_lowZero_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHv .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHv_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGv .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGv_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBv .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBv_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highHu .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highHu_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highGu .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highGu_atA_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atT 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atT_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atT 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atT_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atT 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atT_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atT 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atT_3
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atA 0) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atA_0
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atA 1) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atA_1
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atA 2) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atA_2
  · exact r78_cert 1 40 (19) (9) (r78farMass_rep .highBu .atA 3) (by decide) r78_I4 3 5 r78_ρ35 (by decide) r78kFM_highBu_atA_3

theorem far_mass_positive (r : FarCase) (e : Split) (i : Fin 4) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) : 0<aeval θ (farMass r e i) := by
  have hc := far_mass_certificate r e i
  have hh := positive_on_interval (far_interval r) hc.1 hc.2 hθ
  norm_num at hh
  linarith

theorem far_qstar_T_certificate :
    centered u h (farQStar-farMu .high .atT)=
      expansion 6 (centered u h (farQStar-farMu .high .atT)) ∧
    (629/1000000:ℚ)<lowerOn 6 u h (farQStar-farMu .high .atT) := by
  exact r78_cert 1 40 (19) (9) ((r78farQStar_rep.sub (r78farMu_rep .high .atT))) (by decide) r78_I4 629 1000000 (by norm_num) (by decide) r78kQS

theorem far_qstar_T_positive {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    0<aeval θ (farQStar-farMu .high .atT) := by
  have hh := positive_on_interval (by norm_num [u,h] : u<h)
    far_qstar_T_certificate.1 far_qstar_T_certificate.2
    (show θ∈Icc (u:ℝ) (h:ℝ) by norm_num [u,h]; exact hθ)
  rw [map_sub]
  norm_num at hh
  linarith

theorem far_qstar_A_positive {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    0<aeval θ (farQStar-farC .high) := by
  norm_num [farQStar,farL,farC,h]
  linarith [hθ.2]

theorem small_domain (r : SmallCase) {θ : ℝ}
    (hθ : θ∈Icc (smallLeft r:ℝ) (smallRight r:ℝ)) :
    θ∈Icc (Explicit.left .small (smallFamily r)) (Explicit.right .small (smallFamily r)) := by
  cases r <;>
    norm_num [smallLeft,smallRight,smallFamily,Explicit.left,Explicit.right,Explicit.L,L,h,v,
      Eight.frameCap] at hθ ⊢ <;> constructor <;> linarith [hθ.1,hθ.2]

theorem far_domain (r : FarCase) {θ : ℝ}
    (hθ : θ∈Icc (farLeft r:ℝ) (farRight r:ℝ)) :
    θ∈Icc (Explicit.left .far (farFamily r)) (Explicit.right .far (farFamily r)) := by
  cases r <;>
    norm_num [farLeft,farRight,farFamily,Explicit.left,Explicit.right,Explicit.u,h,v,u,
      Eight.frameCap] at hθ ⊢ <;> constructor <;> linarith [hθ.1,hθ.2]

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
