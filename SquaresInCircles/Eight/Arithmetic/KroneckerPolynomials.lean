module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: reduced sums and Kronecker products of scaled integer lists

The certificates of `PolynomialCertificates` compute on scaled integer lists (`Scaled`). This
module adds the operations that keep those computations short.

* `Scaled.reduce` divides the list and the scale by their gcd; `Scaled.addN`, `subN`, `mulN` and
  `powN` are `add`, `sub`, `mul` and `pow` followed by `reduce`
  (`ha.addN hb : (a.addN b).Rep (p+q)`, ...).
* Kronecker substitution in base `2^e` (namespace `Kron`): a list is packed into one
  integer, its value at `2^e` (`pack`, by shifts), and read back as its balanced digits by masks
  and shifts (`unpack`) when every entry lies in `[-2^(e-1),2^(e-1))` (`unpack_pack`). Packed
  values are never divided and `Nat.log2` is not used: the kernels outside Lean divide big
  numbers bit by bit and take gcds in cubic time, but shift and mask them in linear time.
* `Kron.Packed` is the packed value of a list with its scale and bounds on its length and
  entries. `add` and `sub` act on the packed values over the least common multiple of the scales
  (a gcd of scales, not of packed values); `mul` multiplies them with the factor of fewer digits
  on the right, since con-ron multiplies in a time proportional to the size of the right factor
  times the size of the product. `Packed.eval f` reads `f e` back in a base `2^e` above twice the
  entry bound of `f 0` (`Packed.Rep.eval`).
* `Scaled.kmul` and `ksq` (products), `Scaled.kcenter` (`Scaled.center` by one evaluation at
  `s+t 2^e`), and `Scaled.num3`, `num4` (the numerators `2 A ∏ rᵢ-R ∑ (Pᵢ+rᵢ²) ∏_{j≠i} rⱼ`
  with three and four masses), each with its `Rep` lemma.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate
open Polynomial

/-! ## Reduction by the gcd -/

/-- The gcd of `g` and the entries of `l`. -/
def gcdFold : List ℤ → ℕ → ℕ
  | [],g => g
  | a :: l,g => gcdFold l (Nat.gcd a.natAbs g)

theorem gcdFold_dvd : ∀ (l : List ℤ) (g : ℕ),
    gcdFold l g ∣ g ∧ ∀ a ∈ l,(gcdFold l g : ℤ) ∣ a
  | [],g => ⟨dvd_rfl,by simp⟩
  | a :: l,g => by
    obtain ⟨h1,h2⟩ := gcdFold_dvd l (Nat.gcd a.natAbs g)
    refine ⟨h1.trans (Nat.gcd_dvd_right _ _),fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl|hb
    · exact Int.ofNat_dvd_left.2 (h1.trans (Nat.gcd_dvd_left _ _))
    · exact h2 b hb

/-- The list and the scale divided by their gcd. -/
def Scaled.reduce (S : Scaled) : Scaled :=
  ⟨S.l.map (· / ((gcdFold S.l S.s : ℕ) : ℤ)),S.s / gcdFold S.l S.s⟩

private theorem toPoly_map_div {g : ℤ} : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    C (g:ℚ)*toPoly (l.map (· / g))=toPoly l
  | [],_ => by simp [toPoly]
  | a :: l,h => by
    have ih := toPoly_map_div l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha : ((a / g : ℤ) : ℚ)*g=a := by
      exact_mod_cast Int.ediv_mul_cancel (h a List.mem_cons_self)
    simp only [List.map_cons,toPoly]
    rw [mul_add,mul_left_comm,ih,← map_mul,mul_comm,ha]

private theorem toPoly_map_div_zero : ∀ l : List ℤ,toPoly (l.map (· / (0:ℤ)))=0
  | [] => by simp [toPoly]
  | a :: l => by rw [List.map_cons,toPoly,toPoly_map_div_zero l,Int.ediv_zero]; simp

theorem Scaled.Rep.reduce {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) : S.reduce.Rep p := by
  obtain ⟨h1,h2⟩ := gcdFold_dvd S.l S.s
  unfold Scaled.Rep at *
  rw [Scaled.reduce]
  dsimp only
  generalize gcdFold S.l S.s=g at h1 h2
  rcases Nat.eq_zero_or_pos g with rfl|hg
  · simp only [Nat.cast_zero,Nat.div_zero,map_zero,zero_mul,toPoly_map_div_zero]
  · have hC : C (g:ℚ)≠0 := by rw [Ne,C_eq_zero]; exact_mod_cast hg.ne'
    apply mul_left_cancel₀ hC
    have e := toPoly_map_div S.l h2
    push_cast at e
    rw [e,hS,← mul_assoc,← map_mul]
    congr 2
    rw [← Nat.cast_mul,Nat.mul_div_cancel' h1]

/-- `Scaled.add`, reduced. -/
def Scaled.addN (a b : Scaled) : Scaled := (a.add b).reduce
/-- `Scaled.sub`, reduced. -/
def Scaled.subN (a b : Scaled) : Scaled := (a.sub b).reduce
/-- `Scaled.mul`, reduced. -/
def Scaled.mulN (a b : Scaled) : Scaled := (a.mul b).reduce
/-- `Scaled.pow`, reduced. -/
def Scaled.powN (a : Scaled) (n : ℕ) : Scaled := (a.pow n).reduce

theorem Scaled.Rep.addN {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.addN b).Rep (p+q) := (ha.add hb).reduce
theorem Scaled.Rep.subN {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.subN b).Rep (p-q) := (ha.sub hb).reduce
theorem Scaled.Rep.mulN {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.mulN b).Rep (p*q) := (ha.mul hb).reduce
theorem Scaled.Rep.powN {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (n : ℕ) :
    (a.powN n).Rep (p^n) := (ha.pow n).reduce

/-! ## Monomials, conditionals and equal polynomials -/

/-- The monomial `X^k`. -/
def Scaled.mono (k : ℕ) : Scaled := ⟨List.replicate k 0++[1],1⟩

theorem Scaled.rep_mono (k : ℕ) : (Scaled.mono k).Rep (X^k) := by
  unfold Scaled.Rep Scaled.mono
  simp only [Nat.cast_one,map_one,one_mul]
  induction k with
  | zero => simp [toPoly]
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,toPoly,ih,pow_succ]
    simp only [Int.cast_zero,map_zero,zero_add]
    ring

theorem Scaled.Rep.ite {c : Prop} [Decidable c] {A B : Scaled} {p q : ℚ[X]}
    (hA : A.Rep p) (hB : B.Rep q) : (if c then A else B).Rep (if c then p else q) := by
  split_ifs <;> assumption

theorem Scaled.Rep.of_eq {S : Scaled} {p q : ℚ[X]} (h : S.Rep q) (e : q=p) : S.Rep p := e ▸ h

/-! ## Kronecker substitution in base `2^e` -/

namespace Kron

/-- The list evaluated at `2^e`, by shifts. -/
def pack (e : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a+pack e l <<< e

theorem pack_eq (e : ℕ) : ∀ l : List ℤ,(pack e l : ℚ)=(toPoly l).eval ((2:ℚ)^e)
  | [] => by simp [pack,toPoly]
  | a :: l => by
    simp only [pack,Int.shiftLeft_eq,toPoly,eval_add,eval_C,eval_mul,eval_X]
    push_cast
    rw [pack_eq e l]
    ring

/-- The residue of `v` modulo `2^e` in `[-2^(e-1),2^(e-1))` and the quotient, by masks and
shifts. -/
def split (e : ℕ) (v : ℤ) : ℤ × ℤ :=
  match v with
  | .ofNat n =>
    if n &&& ((1 <<< e)-1)<1 <<< (e-1) then (.ofNat (n &&& ((1 <<< e)-1)),.ofNat (n >>> e))
    else (.ofNat (n &&& ((1 <<< e)-1))-.ofNat (1 <<< e),.ofNat (n >>> e)+1)
  | .negSucc n =>
    if n &&& ((1 <<< e)-1)<1 <<< (e-1) then (-.ofNat (n &&& ((1 <<< e)-1))-1,-.ofNat (n >>> e))
    else (.ofNat ((1 <<< e)-1-(n &&& ((1 <<< e)-1))),-.ofNat (n >>> e)-1)

/-- The first `n` balanced digits of `N` in base `2^e`. -/
def unpack (e : ℕ) : ℕ → ℤ → List ℤ
  | 0,_ => []
  | n+1,N =>
    match split e N with
    | (d,q) => d :: unpack e n q

theorem split_spec {e : ℕ} (he : 1≤e) (v : ℤ) :
    (split e v).1+2^e*(split e v).2=v ∧ -(2^(e-1) : ℤ)≤(split e v).1 ∧
      (split e v).1<2^(e-1) := by
  have hP : (2:ℕ)^e=2*2^(e-1) := by
    rw [← pow_succ']; congr 1; omega
  have hPz : (2:ℤ)^e=2*2^(e-1) := by exact_mod_cast hP
  have hP1 : (0:ℤ)<2^(e-1) := by positivity
  cases v with
  | ofNat n =>
    have hdm := Nat.div_add_mod n (2^e)
    have hlt := Nat.mod_lt n (show 0<2^e by positivity)
    simp only [split,Nat.one_shiftLeft,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,
      Int.ofNat_eq_natCast]
    generalize n % 2^e=r at *
    generalize n / 2^e=q at *
    have hdmz : (2:ℤ)^e*(q:ℤ)+(r:ℤ)=n := by exact_mod_cast hdm
    have hltz : (r:ℤ)<2^e := by exact_mod_cast hlt
    have hr0 : (0:ℤ)≤r := by positivity
    split_ifs with h
    · have h' : (r:ℤ)<2^(e-1) := by exact_mod_cast h
      dsimp only
      refine ⟨by linarith,by linarith,h'⟩
    · have h' : (2:ℤ)^(e-1)≤r := by exact_mod_cast not_lt.1 h
      dsimp only
      push_cast
      refine ⟨by linarith,by linarith,by linarith⟩
  | negSucc n =>
    have hdm := Nat.div_add_mod n (2^e)
    have hlt := Nat.mod_lt n (show 0<2^e by positivity)
    simp only [split,Nat.one_shiftLeft,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,
      Int.ofNat_eq_natCast,Int.negSucc_eq]
    generalize n % 2^e=r at *
    generalize n / 2^e=q at *
    have hdmz : (2:ℤ)^e*(q:ℤ)+(r:ℤ)=n := by exact_mod_cast hdm
    have hltz : (r:ℤ)<2^e := by exact_mod_cast hlt
    have hr0 : (0:ℤ)≤r := by positivity
    split_ifs with h
    · have h' : (r:ℤ)<2^(e-1) := by exact_mod_cast h
      dsimp only
      refine ⟨by linarith,by linarith,by linarith⟩
    · have h' : (2:ℤ)^(e-1)≤r := by exact_mod_cast not_lt.1 h
      have hle : r≤2^e-1 := by omega
      dsimp only
      rw [Nat.cast_sub hle,Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      refine ⟨by linarith,by linarith,by linarith⟩

theorem split_eq {e : ℕ} (he : 1≤e) {a w : ℤ} (ha1 : -(2^(e-1) : ℤ)≤a) (ha2 : a<2^(e-1)) :
    split e (a+2^e*w)=(a,w) := by
  obtain ⟨h1,h2,h3⟩ := split_spec he (a+2^e*w)
  have hPz : (2:ℤ)^e=2*2^(e-1) := by
    rw [← pow_succ']; congr 1; omega
  have hpos : (0:ℤ)<2^(e-1) := by positivity
  have hw : (split e (a+2^e*w)).2=w := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h|h
    · have : (split e (a+2^e*w)).2+1≤w := h
      nlinarith
    · have : w+1≤(split e (a+2^e*w)).2 := h
      nlinarith
  refine Prod.ext ?_ hw
  rw [hw] at h1
  linarith

theorem unpack_pack {e : ℕ} (he : 1≤e) : ∀ (n : ℕ) (c : List ℤ),c.length≤n →
    (∀ j,-(2:ℤ)^e≤2*c.getD j 0 ∧ 2*c.getD j 0<2^e) → toPoly (unpack e n (pack e c))=toPoly c
  | 0,c,hl,_ => by
    rw [List.length_eq_zero_iff.1 (by omega : c.length=0)]
    rfl
  | n+1,[],_,_ => by
    have hpos : (0:ℤ)<2^(e-1) := by positivity
    have h0 := split_eq he (a:=0) (w:=0) (by linarith) hpos
    simp only [mul_zero,add_zero] at h0
    have ih : toPoly (unpack e n 0)=0 := unpack_pack he n [] (by simp) (fun j => by simp)
    show toPoly (unpack e (n+1) 0)=0
    rw [unpack,h0]
    dsimp only
    simp [toPoly,ih]
  | n+1,x :: c,hl,hb => by
    have hx := hb 0
    simp only [List.getD_cons_zero] at hx
    have hPz : (2:ℤ)^e=2*2^(e-1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 := split_eq he (a:=x) (w:=pack e c) (by linarith [hx.1]) (by linarith [hx.2])
    have ih := unpack_pack he n c (by simpa using hl) (fun j => by simpa using hb (j+1))
    have h2 : pack e (x :: c)=x+2^e*pack e c := by
      rw [pack,Int.shiftLeft_eq,mul_comm]
    rw [h2,unpack,h1]
    dsimp only
    rw [toPoly,toPoly,ih]

/-! ### Bounds on the entries -/

/-- The sum of the absolute values of the entries. -/
def asum : List ℤ → ℕ
  | [] => 0
  | a :: l => a.natAbs+asum l

/-- The largest absolute value of an entry. -/
def amax : List ℤ → ℕ
  | [] => 0
  | a :: l => max a.natAbs (amax l)

/-- `16 w` for the number `w` of 16-bit words of `x`, counting at most `f` words. -/
def words : ℕ → ℕ → ℕ
  | 0,_ => 0
  | f+1,x => if x=0 then 0 else words f (x >>> 16)+16

/-- An exponent `e` with `x<2^(e-1)` for every `x` below `2^262144`; the readers check
`x<2^e` again. -/
def bits (x : ℕ) : ℕ := words 16384 x+1

theorem getD_smul (c : ℤ) : ∀ (l : List ℤ) (j : ℕ),(smul c l).getD j 0=c*l.getD j 0
  | [],j => by simp [smul]
  | a :: l,0 => by simp [smul]
  | a :: l,j+1 => by
    simp only [smul,List.getD_cons_succ,getD_smul c l j]

theorem getD_le_amax : ∀ (l : List ℤ) (j : ℕ),|l.getD j 0|≤amax l
  | [],j => by simp
  | a :: l,0 => by simp only [List.getD_cons_zero,amax]; push_cast; exact le_max_left _ _
  | a :: l,j+1 => by
    simp only [List.getD_cons_succ,amax]
    push_cast
    exact (getD_le_amax l j).trans (le_max_right _ _)

theorem getD_le_asum : ∀ (l : List ℤ) (j : ℕ),(l.getD j 0).natAbs≤asum l
  | [],j => by simp [asum]
  | a :: l,0 => by simp [asum]
  | a :: l,j+1 => by
    have := getD_le_asum l j
    simp only [List.getD_cons_succ,asum]
    omega

theorem mul_bound : ∀ (a m : List ℤ) (j : ℕ),
    |(Certificate.mul a m).getD j 0|≤asum a*amax m
  | [],m,j => by simp [Certificate.mul]; positivity
  | a :: l,[],j => by simp [Certificate.mul]; positivity
  | a :: l,b :: m,j => by
    rw [Certificate.mul,Certificate.getD_add,getD_smul]
    have h1 : |a*(b :: m).getD j 0|≤|a| * amax (b :: m) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (getD_le_amax _ j) (abs_nonneg a)
    have h2 : |(0 :: Certificate.mul l (b :: m)).getD j 0|≤asum l*amax (b :: m) := by
      rcases j with _|j
      · simp only [List.getD_cons_zero,abs_zero]; positivity
      · simpa only [List.getD_cons_succ] using mul_bound l (b :: m) j
    simp only [asum]
    push_cast
    calc _≤_ := abs_add_le _ _
      _≤_ := add_le_add h1 h2
      _=_ := by ring

theorem length_add : ∀ l m : List ℤ,(Certificate.add l m).length=max l.length m.length
  | [],m => by simp [Certificate.add]
  | a :: l,[] => by simp [Certificate.add]
  | a :: l,b :: m => by
    simp [Certificate.add,length_add l m,Nat.succ_max_succ]

theorem length_smul (c : ℤ) : ∀ l : List ℤ,(smul c l).length=l.length
  | [] => rfl
  | a :: l => by simp [smul,length_smul c l]

theorem length_mul : ∀ a m : List ℤ,(Certificate.mul a m).length≤a.length+m.length-1
  | [],m => by simp [Certificate.mul]
  | a :: l,[] => by simp [Certificate.mul]
  | a :: l,b :: m => by
    have ih := length_mul l (b :: m)
    rw [Certificate.mul,length_add,length_smul]
    rcases l with _|⟨c,l⟩
    · simp [Certificate.mul]
    · simp only [List.length_cons] at ih ⊢
      omega

theorem amax_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) : amax l≤β := by
  induction l generalizing β with
  | nil => simp [amax]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    exact max_le h0 h1

theorem asum_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) : asum l≤l.length*β := by
  induction l generalizing β with
  | nil => simp [asum]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    simp only [asum,List.length_cons]
    nlinarith

theorem pack_add (e : ℕ) (l m : List ℤ) : pack e (Certificate.add l m)=pack e l+pack e m := by
  have h : (pack e (Certificate.add l m) : ℚ)=pack e l+pack e m := by
    rw [pack_eq,pack_eq,pack_eq,toPoly_add,eval_add]
  exact_mod_cast h

theorem pack_smul (e : ℕ) (c : ℤ) (l : List ℤ) : pack e (smul c l)=c*pack e l := by
  have h : (pack e (smul c l) : ℚ)=c*pack e l := by
    rw [pack_eq,pack_eq,toPoly_smul,eval_mul,eval_C]
  exact_mod_cast h

theorem pack_mul (e : ℕ) (l m : List ℤ) : pack e (Certificate.mul l m)=pack e l*pack e m := by
  have h : (pack e (Certificate.mul l m) : ℚ)=pack e l*pack e m := by
    rw [pack_eq,pack_eq,pack_eq,toPoly_mul,eval_mul]
  exact_mod_cast h

/-! ### Packed sums and products -/

/-- The value `N` at `2^e` of an integer list of at most `n` entries, each of absolute value at
most `β`, that represents `s` times a polynomial (`Packed.Rep`). Sums and products act on `N`
alone. -/
structure Packed where
  N : ℤ
  s : ℕ
  n : ℕ
  β : ℕ

/-- `k` packs, at `2^e`, a list that represents `k.s` times `p`. -/
def Packed.Rep (e : ℕ) (k : Packed) (p : ℚ[X]) : Prop :=
  ∃ l : List ℤ,l.length≤k.n ∧ (∀ j,|l.getD j 0|≤k.β) ∧ k.N=pack e l ∧ toPoly l=C (k.s:ℚ)*p

/-- The sum, over the least common multiple of the scales. -/
def Packed.add (a b : Packed) : Packed :=
  ⟨a.N*(b.s/Nat.gcd a.s b.s : ℕ)+b.N*(a.s/Nat.gcd a.s b.s : ℕ),a.s*(b.s/Nat.gcd a.s b.s),
    max a.n b.n,a.β*(b.s/Nat.gcd a.s b.s)+b.β*(a.s/Nat.gcd a.s b.s)⟩
/-- The difference, over the least common multiple of the scales. -/
def Packed.sub (a b : Packed) : Packed :=
  ⟨a.N*(b.s/Nat.gcd a.s b.s : ℕ)-b.N*(a.s/Nat.gcd a.s b.s : ℕ),a.s*(b.s/Nat.gcd a.s b.s),
    max a.n b.n,a.β*(b.s/Nat.gcd a.s b.s)+b.β*(a.s/Nat.gcd a.s b.s)⟩
/-- The product; the factor with fewer digits is the right operand of `*` (con-ron multiplies in
a time proportional to the size of the right operand times the size of the product). -/
def Packed.mul (a b : Packed) : Packed :=
  ⟨if a.n<b.n then b.N*a.N else a.N*b.N,a.s*b.s,a.n+b.n-1,a.n*a.β*b.β⟩
/-- Packs `C q`. -/
def Packed.const (q : ℚ) : Packed := ⟨q.num,q.den,1,q.num.natAbs⟩
def Packed.ofScaled (e : ℕ) (S : Scaled) : Packed := ⟨pack e S.l,S.s,S.l.length,amax S.l⟩
/-- The digits of `k` in base `2^e`, when `2^e` exceeds twice the entry bound. -/
def Packed.toScaled (e : ℕ) (k : Packed) : Scaled :=
  if 1≤e ∧ 2*k.β<1 <<< e then ⟨unpack e k.n k.N,k.s⟩ else ⟨[],0⟩
/-- `f e`, read back in the base `2^e` given by the entry bound of `f 0`. -/
def Packed.eval (f : ℕ → Packed) : Scaled := (f (bits (2*(f 0).β))).toScaled (bits (2*(f 0).β))

private theorem gcd_cross (a b : ℕ) : a*(b/Nat.gcd a b)=b*(a/Nat.gcd a b) := by
  rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_right a b),← Nat.mul_div_assoc _ (Nat.gcd_dvd_left a b),
    Nat.mul_comm]

/-- The common core of `add` and `sub`: `a.s u = b.s w` is a common multiple of the scales. -/
private theorem Packed.rep_comb {e : ℕ} {a b : Packed} {p q : ℚ[X]} (ha : a.Rep e p)
    (hb : b.Rep e q) (u w : ℕ) (c : ℤ) (hc : |c|=1) (key : a.s*u=b.s*w) :
    Packed.Rep e ⟨a.N*u+c*(b.N*w),a.s*u,max a.n b.n,a.β*u+b.β*w⟩ (p+C (c:ℚ)*q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨Certificate.add (smul u la) (smul (c*w) lb),?_,?_,?_,?_⟩
  · rw [length_add,length_smul,length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [Certificate.getD_add,getD_smul,getD_smul]
    calc _≤|(u:ℤ)*la.getD j 0|+|(c*w)*lb.getD j 0| := abs_add_le _ _
      _≤(u:ℤ)*a.β+(w:ℤ)*b.β := by
        rw [abs_mul,abs_mul,abs_mul,hc,one_mul,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by push_cast; ring
  · simp only [pack_add,pack_smul,hNa,hNb]
    ring
  · have key' : (a.s:ℚ)*u=b.s*w := by exact_mod_cast key
    have hC : C ((a.s:ℚ)*u)=C ((b.s:ℚ)*w) := by rw [key']
    simp only [toPoly_add,toPoly_smul,hpa,hpb,Int.cast_natCast,Int.cast_mul,Nat.cast_mul,
      map_mul] at hC ⊢
    linear_combination (-(C (c:ℚ)*q))*hC

theorem Packed.Rep.add {e : ℕ} {a b : Packed} {p q : ℚ[X]} (ha : a.Rep e p) (hb : b.Rep e q) :
    (a.add b).Rep e (p+q) := by
  have h := Packed.rep_comb ha hb _ _ 1 (by norm_num) (gcd_cross a.s b.s)
  simp only [one_mul,Int.cast_one,map_one] at h
  exact h

theorem Packed.Rep.sub {e : ℕ} {a b : Packed} {p q : ℚ[X]} (ha : a.Rep e p) (hb : b.Rep e q) :
    (a.sub b).Rep e (p-q) := by
  have h := Packed.rep_comb ha hb _ _ (-1) (by norm_num) (gcd_cross a.s b.s)
  simp only [neg_one_mul,Int.cast_neg,Int.cast_one,map_neg,map_one,← sub_eq_add_neg] at h
  exact h

theorem Packed.Rep.mul {e : ℕ} {a b : Packed} {p q : ℚ[X]} (ha : a.Rep e p) (hb : b.Rep e q) :
    (a.mul b).Rep e (p*q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨Certificate.mul la lb,?_,?_,?_,?_⟩
  · have := length_mul la lb
    simp only [Packed.mul]
    omega
  · intro j
    have h1 := mul_bound la lb j
    have h2 : asum la*amax lb≤a.n*a.β*b.β :=
      Nat.mul_le_mul ((asum_le hba).trans (Nat.mul_le_mul_right _ hla)) (amax_le hbb)
    simp only [Packed.mul]
    calc _≤((asum la*amax lb:ℕ):ℤ) := by exact_mod_cast h1
      _≤_ := by exact_mod_cast h2
  · simp only [Packed.mul,pack_mul,hNa,hNb]
    split_ifs <;> ring
  · simp only [Packed.mul,toPoly_mul,hpa,hpb,Nat.cast_mul,map_mul]
    ring

theorem Packed.rep_const (e : ℕ) (q : ℚ) : (Packed.const q).Rep e (C q) := by
  refine ⟨[q.num],by simp [Packed.const],fun j => ?_,by simp [Packed.const,pack],?_⟩
  · rcases j with _|j
    · simp only [List.getD_cons_zero,Packed.const]
      exact (Int.abs_eq_natAbs _).le
    · simp
  · simp only [Packed.const,toPoly,mul_zero,add_zero,← map_mul,Rat.den_mul_eq_num]

theorem Packed.rep_ofScaled (e : ℕ) {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) :
    (Packed.ofScaled e S).Rep e p :=
  ⟨S.l,le_rfl,getD_le_amax S.l,rfl,hS⟩

theorem Packed.Rep.toScaled {e : ℕ} {k : Packed} {p : ℚ[X]} (hk : k.Rep e p) :
    (k.toScaled e).Rep p := by
  unfold Packed.toScaled
  split_ifs with h
  · obtain ⟨l,hl,hb,hN,hp⟩ := hk
    have hβ : 2*(k.β:ℤ)<2^e := by
      have h2 := h.2
      rw [Nat.one_shiftLeft] at h2
      exact_mod_cast h2
    show toPoly (unpack e k.n k.N)=_
    rw [hN,unpack_pack h.1 _ _ hl
      (fun j => by obtain ⟨h1,h2⟩ := abs_le.1 (hb j); constructor <;> linarith)]
    exact hp
  · show toPoly []=C ((0:ℕ):ℚ)*p
    simp [toPoly]

theorem Packed.Rep.eval {f : ℕ → Packed} {p : ℚ[X]} (h : ∀ e,(f e).Rep e p) :
    (Packed.eval f).Rep p :=
  (h _).toScaled

theorem Packed.Rep.of_eq {e : ℕ} {k : Packed} {p q : ℚ[X]} (h : k.Rep e q) (hq : q=p) :
    k.Rep e p := hq ▸ h

/-! ### Composition with `s+tX` -/

/-- `v s+v t 2^e`, the small factors on the right; the match reads `v` once. -/
def affStep (s t : ℤ) (e : ℕ) : ℤ → ℤ
  | .ofNat n => .ofNat n*s+(.ofNat n*t) <<< e
  | .negSucc n => .negSucc n*s+(.negSucc n*t) <<< e

/-- The list evaluated at `s+t 2^e`, by Horner's rule. -/
def packAff (s t : ℤ) (e : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a+affStep s t e (packAff s t e l)

theorem affStep_eq (s t : ℤ) (e : ℕ) (v : ℤ) : affStep s t e v=(s+t*2^e)*v := by
  cases v <;> simp only [affStep,Int.shiftLeft_eq] <;> ring

theorem packAff_eq (s t : ℤ) (e : ℕ) : ∀ l : List ℤ,
    (packAff s t e l : ℚ)=(toPoly l).eval ((s:ℚ)+t*2^e)
  | [] => by simp [packAff,toPoly]
  | a :: l => by
    simp only [packAff,affStep_eq,toPoly,eval_add,eval_C,eval_mul,eval_X]
    push_cast
    rw [packAff_eq s t e l]

theorem asum_add : ∀ l m : List ℤ,asum (Certificate.add l m)≤asum l+asum m
  | [],m => by simp [Certificate.add,asum]
  | a :: l,[] => by simp [Certificate.add,asum]
  | a :: l,b :: m => by
    have ih := asum_add l m
    have := Int.natAbs_add_le a b
    simp only [Certificate.add,asum]
    omega

theorem asum_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    asum (affMulAux s t c z)≤s.natAbs*asum z+t.natAbs*c.natAbs+t.natAbs*asum z
  | c,[] => by simp [affMulAux,asum,Int.natAbs_mul]
  | c,x :: z => by
    have ih := asum_affMulAux s t x z
    have h1 := Int.natAbs_add_le (s*x) (t*c)
    simp only [affMulAux,asum,Int.natAbs_mul] at h1 ⊢
    nlinarith

theorem asum_affMul (s t : ℤ) (z : List ℤ) :
    asum (Certificate.affMul s t z)≤(s.natAbs+t.natAbs)*asum z := by
  unfold Certificate.affMul
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    cases z with
    | nil => simp [shiftMul,asum]
    | cons x z =>
      have := asum_add (x :: z) (0 :: x :: z)
      simp only [shiftMul]
      simp only [asum] at this ⊢
      simp
      omega
  · cases z with
    | nil => simp [affMulGen,asum]
    | cons x z =>
      have := asum_affMulAux s t x z
      simp only [affMulGen,asum,Int.natAbs_mul]
      nlinarith

theorem asum_compAff (s t : ℤ) : ∀ l : List ℤ,
    asum (compAff s t l)≤asum l*(s.natAbs+t.natAbs+1)^(l.length-1)
  | [] => by simp [compAff,asum]
  | b :: l => by
    have h1 := asum_add [b] (Certificate.affMul s t (compAff s t l))
    have h2 := asum_affMul s t (compAff s t l)
    have hb : asum [b]=b.natAbs := by simp [asum]
    rw [compAff]
    simp only [asum,List.length_cons,Nat.add_sub_cancel]
    rcases l with _|⟨c,l⟩
    · simp [compAff,Certificate.affMul,shiftMul,affMulGen,Certificate.add,asum]
    · have ih := asum_compAff s t (c :: l)
      generalize asum (compAff s t (c :: l))=A at h1 h2 ih
      simp only [List.length_cons,Nat.add_sub_cancel] at ih ⊢
      have key : (s.natAbs+t.natAbs)*A≤asum (c :: l)*(s.natAbs+t.natAbs+1)^(l.length+1) :=
        calc (s.natAbs+t.natAbs)*A≤(s.natAbs+t.natAbs+1)*A :=
              Nat.mul_le_mul_right _ (Nat.le_succ _)
          _≤(s.natAbs+t.natAbs+1)*(asum (c :: l)*(s.natAbs+t.natAbs+1)^l.length) :=
            Nat.mul_le_mul_left _ ih
          _=_ := by ring
      have hM : 1≤(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.one_le_pow _ _ (by omega)
      have hb' : b.natAbs≤b.natAbs*(s.natAbs+t.natAbs+1)^(l.length+1) :=
        Nat.le_mul_of_pos_right _ hM
      rw [hb] at h1
      rw [add_mul]
      omega

theorem length_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    (affMulAux s t c z).length=z.length+1
  | c,[] => rfl
  | c,x :: z => by
    simp [affMulAux,length_affMulAux s t x z]

theorem length_affMul (s t : ℤ) (z : List ℤ) :
    (Certificate.affMul s t z).length≤z.length+1 := by
  unfold Certificate.affMul
  split_ifs
  · cases z with
    | nil => simp [shiftMul]
    | cons x z =>
      rw [shiftMul,length_add]
      simp
  · cases z with
    | nil => simp [affMulGen]
    | cons x z =>
      simp [affMulGen,length_affMulAux]

theorem length_compAff (s t : ℤ) : ∀ l : List ℤ,(compAff s t l).length≤l.length
  | [] => by simp [compAff]
  | b :: l => by
    have ih := length_compAff s t l
    have h := length_affMul s t (compAff s t l)
    rw [compAff,length_add]
    simp only [List.length_cons,List.length_nil]
    omega

/-- The composition of `L` with `s+tX` read back in base `2^e`, or the list composition if
`2^e` is not above twice the bound `M` on its coefficients. -/
def kcenterAt (s t : ℤ) (L : List ℤ) (M e : ℕ) : List ℤ :=
  if 1≤e ∧ 2*M<1 <<< e then unpack e L.length (packAff s t e L) else compAff s t L

/-- The composition of `L` with `s+tX`, by one evaluation at `s+t 2^e`, where `2^e` exceeds
twice the bound `Σ|Lᵢ| (|s|+|t|+1)^(n-1)` on its coefficients. -/
def kcenterAux (s t : ℤ) (L : List ℤ) : List ℤ :=
  kcenterAt s t L (asum L*(s.natAbs+t.natAbs+1)^(L.length-1))
    (bits (2*(asum L*(s.natAbs+t.natAbs+1)^(L.length-1))))

theorem toPoly_kcenterAux (s t : ℤ) (L : List ℤ) :
    toPoly (kcenterAux s t L)=toPoly (compAff s t L) := by
  rw [kcenterAux,kcenterAt]
  generalize hM : asum L*(s.natAbs+t.natAbs+1)^(L.length-1)=M
  generalize bits (2*M)=e
  split_ifs with hc
  · obtain ⟨he,hMe⟩ := hc
    rw [Nat.one_shiftLeft] at hMe
    have hE : packAff s t e L=pack e (compAff s t L) := by
      have e' : (packAff s t e L : ℚ)=(pack e (compAff s t L) : ℚ) := by
        rw [packAff_eq,pack_eq,toPoly_compAff,eval_comp]
        simp
      exact_mod_cast e'
    rw [hE]
    apply unpack_pack he _ _ (length_compAff s t L)
    intro j
    have h1 := getD_le_asum (compAff s t L) j
    have h2 := asum_compAff s t L
    rw [hM] at h2
    have h3 : ((compAff s t L).getD j 0).natAbs≤M := h1.trans h2
    have h4 : |(compAff s t L).getD j 0|≤(M:ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h3
    have hMe' : 2*(M:ℤ)<2^e := by exact_mod_cast hMe
    obtain ⟨h5,h6⟩ := abs_le.1 h4
    constructor <;> linarith
  · rfl

/-! ### Numerators -/

/-- `2 A r0 w-R ((P0+r0²) w+((P1+r1²) r2+(P2+r2²) r1) r0)` on packed values, with `w = r1 r2`. -/
def Packed.num3 (R : ℚ) (A P0 P1 P2 r0 r1 r2 w : Packed) : Packed :=
  ((((Packed.const 2).mul A).mul r0).mul w).sub ((Packed.const R).mul
    (((P0.add (r0.mul r0)).mul w).add
      ((((P1.add (r1.mul r1)).mul r2).add ((P2.add (r2.mul r2)).mul r1)).mul r0)))

/-- `2 A u v-R (((P0+r0²) r1+(P1+r1²) r0) v+((P2+r2²) r3+(P3+r3²) r2) u)` on packed values, with
`u = r0 r1` and `v = r2 r3`. -/
def Packed.num4 (R : ℚ) (A P0 P1 P2 P3 r0 r1 r2 r3 u v : Packed) : Packed :=
  ((((Packed.const 2).mul A).mul u).mul v).sub ((Packed.const R).mul
    (((((P0.add (r0.mul r0)).mul r1).add ((P1.add (r1.mul r1)).mul r0)).mul v).add
      ((((P2.add (r2.mul r2)).mul r3).add ((P3.add (r3.mul r3)).mul r2)).mul u)))

end Kron

open Kron

/-! ## Products, compositions and numerators -/

/-- The product, by one product of packed values. -/
def Scaled.kmul (a b : Scaled) : Scaled :=
  Packed.eval fun e => (Packed.ofScaled e a).mul (Packed.ofScaled e b)
/-- The square, by `kmul`. -/
def Scaled.ksq (a : Scaled) : Scaled := a.kmul a
/-- `Scaled.kmul`, reduced. -/
def Scaled.kmulN (a b : Scaled) : Scaled := (a.kmul b).reduce
/-- `Scaled.ksq`, reduced. -/
def Scaled.ksqN (a : Scaled) : Scaled := a.ksq.reduce

theorem Scaled.Rep.kmul {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.kmul b).Rep (p*q) :=
  Packed.Rep.eval fun e => (Packed.rep_ofScaled e ha).mul (Packed.rep_ofScaled e hb)
theorem Scaled.Rep.ksq {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.ksq.Rep (p^2) := by
  rw [sq]; exact ha.kmul ha
theorem Scaled.Rep.kmulN {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.kmulN b).Rep (p*q) := (ha.kmul hb).reduce
theorem Scaled.Rep.ksqN {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.ksqN.Rep (p^2) :=
  ha.ksq.reduce

/-- `Scaled.center`, with the composition by one evaluation (`Kron.kcenterAux`). -/
def Scaled.kcenter (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨kcenterAux s t (prescale num den (c.l.length-1) 0 c.l),c.s*den^(c.l.length-1)⟩

theorem Scaled.Rep.kcentered {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (c.kcenter num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  have h := hc.centered num den s t hden hm hh
  unfold Scaled.Rep at h ⊢
  show toPoly (kcenterAux s t _)=_
  rw [toPoly_kcenterAux]
  exact h

/-- The numerator with three masses, by one packed computation, reduced. -/
def Scaled.num3 (R : ℚ) (A P0 P1 P2 r0 r1 r2 : Scaled) : Scaled :=
  (Packed.eval fun e => Packed.num3 R (.ofScaled e A) (.ofScaled e P0) (.ofScaled e P1)
    (.ofScaled e P2) (.ofScaled e r0) (.ofScaled e r1) (.ofScaled e r2)
    ((Packed.ofScaled e r1).mul (.ofScaled e r2))).reduce

/-- The numerator with four masses, by one packed computation, reduced. -/
def Scaled.num4 (R : ℚ) (A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled) : Scaled :=
  (Packed.eval fun e => Packed.num4 R (.ofScaled e A) (.ofScaled e P0) (.ofScaled e P1)
    (.ofScaled e P2) (.ofScaled e P3) (.ofScaled e r0) (.ofScaled e r1) (.ofScaled e r2)
    (.ofScaled e r3) ((Packed.ofScaled e r0).mul (.ofScaled e r1))
    ((Packed.ofScaled e r2).mul (.ofScaled e r3))).reduce

theorem Scaled.Rep.num3 (R : ℚ) {A P0 P1 P2 r0 r1 r2 : Scaled} {a p0 p1 p2 s0 s1 s2 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) :
    (Scaled.num3 R A P0 P1 P2 r0 r1 r2).Rep
      (C 2*a*s0*s1*s2-C R*((p0+s0^2)*s1*s2+(p1+s1^2)*s0*s2+(p2+s2^2)*s0*s1)) := by
  refine (Packed.Rep.eval fun e => ?_).reduce
  unfold Packed.num3
  have kA := Packed.rep_ofScaled e hA
  have k0 := Packed.rep_ofScaled e h0
  have k1 := Packed.rep_ofScaled e h1
  have k2 := Packed.rep_ofScaled e h2
  have j0 := Packed.rep_ofScaled e g0
  have j1 := Packed.rep_ofScaled e g1
  have j2 := Packed.rep_ofScaled e g2
  have h := ((((Packed.rep_const e 2).mul kA).mul j0).mul (j1.mul j2)).sub
    ((Packed.rep_const e R).mul (((k0.add (j0.mul j0)).mul (j1.mul j2)).add
      ((((k1.add (j1.mul j1)).mul j2).add ((k2.add (j2.mul j2)).mul j1)).mul j0)))
  convert h using 1
  ring

theorem Scaled.Rep.num4 (R : ℚ) {A P0 P1 P2 P3 r0 r1 r2 r3 : Scaled}
    {a p0 p1 p2 p3 s0 s1 s2 s3 : ℚ[X]}
    (hA : A.Rep a) (h0 : P0.Rep p0) (h1 : P1.Rep p1) (h2 : P2.Rep p2) (h3 : P3.Rep p3)
    (g0 : r0.Rep s0) (g1 : r1.Rep s1) (g2 : r2.Rep s2) (g3 : r3.Rep s3) :
    (Scaled.num4 R A P0 P1 P2 P3 r0 r1 r2 r3).Rep
      (C 2*a*s0*s1*s2*s3-C R*
        ((p0+s0^2)*s1*s2*s3+(p1+s1^2)*s0*s2*s3+
          (p2+s2^2)*s0*s1*s3+(p3+s3^2)*s0*s1*s2)) := by
  refine (Packed.Rep.eval fun e => ?_).reduce
  unfold Packed.num4
  have kA := Packed.rep_ofScaled e hA
  have k0 := Packed.rep_ofScaled e h0
  have k1 := Packed.rep_ofScaled e h1
  have k2 := Packed.rep_ofScaled e h2
  have k3 := Packed.rep_ofScaled e h3
  have j0 := Packed.rep_ofScaled e g0
  have j1 := Packed.rep_ofScaled e g1
  have j2 := Packed.rep_ofScaled e g2
  have j3 := Packed.rep_ofScaled e g3
  have h := ((((Packed.rep_const e 2).mul kA).mul (j0.mul j1)).mul (j2.mul j3)).sub
    ((Packed.rep_const e R).mul
      (((((k0.add (j0.mul j0)).mul j1).add ((k1.add (j1.mul j1)).mul j0)).mul (j2.mul j3)).add
        ((((k2.add (j2.mul j2)).mul j3).add ((k3.add (j3.mul j3)).mul j2)).mul (j0.mul j1))))
  convert h using 1
  ring

end SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate
