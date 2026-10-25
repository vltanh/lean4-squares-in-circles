module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial

/-!
# Kernel-checked certificates for `WholeIntervalPolynomial`

`ℚ[X]` is noncomputable, so `decide` cannot evaluate `expansion`, `lowerOn` or
`upperOn` of a concrete polynomial. This module proves them instead from a
computation on integer coefficient lists that the kernel evaluates.

* `eq_expansion_of_natDegree_le : p.natDegree ≤ D → p = expansion D p` (no computation).
* `Certificate.Scaled` is an integer list `l` with a scale `s : ℕ`;
  `c.Rep p` means `Certificate.toPoly c.l = C s * p`.  Build `c` with the
  operations `Scaled.add/sub/neg/mul/pow/divX`, `Scaled.const q` (for `C q`),
  `Scaled.var` (for `X`), `Scaled.ofNat n` (for numerals), mirroring the
  definition of `p`, and prove `c.Rep p` with the matching lemmas
  `Scaled.Rep.add/sub/...`, `Scaled.rep_const/rep_var/rep_one/rep_ofNat`.
* `hc.centered num den s t hden hm hh : (c.center num den s t).Rep (centered a b p)`
  from `hc : c.Rep p`, whenever `(a+b)/2 = num*s/den` and `(b-a)/2 = num*t/den`
  (for `[0,7/10]`: `num = 7`, `den = 20`, `s = t = 1`; for `[a,b]` in general,
  `num = 1`, `den` a common denominator of `(a+b)/2` and `(b-a)/2`).  The case
  `s = t = 1` (intervals `[0,b]`) composes with additions only and is about twice
  as fast in the kernel.
* For `hq : c.Rep (centered a b p)`, `hs : c.s ≠ 0` and `hl : c.l.length ≤ D+1`:
  `hq.eq_expansion hs hl : centered a b p = expansion D (centered a b p)`,
  `lowerOn_eq_of_rep hq hs hl` and `upperOn_eq_of_rep hq hs hl` rewrite
  `lowerOn D a b p` / `upperOn D a b p` as an integer computation divided by
  `c.s * 2^c.l.length / 2`.

Typical proof of `ρ < lowerOn D a b p`:

    rw [lowerOn_eq_of_rep (hp.centered 7 20 1 1 (by norm_num) (by norm_num) (by norm_num))
      (by decide +kernel) (by decide +kernel)]
    decide +kernel

and of `centered a b p = expansion D (centered a b p)`:

    (hp.centered 7 20 1 1 (by norm_num) (by norm_num) (by norm_num)).eq_expansion
      (by decide +kernel) (by decide +kernel)

Kernel reduction only: no `native_decide`, no external data.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial
open Polynomial

/-! ## Chebyshev re-expansion of monomials

The coefficient formula `monomialCoefficient` satisfies the recurrence of
multiplication by `X` in the Chebyshev basis, so every polynomial of degree
at most `D` equals its own degree-`D` re-expansion. -/

theorem monomialCoefficient_of_lt {i j : ℕ} (h : i<j) : monomialCoefficient i j=0 := by
  unfold monomialCoefficient
  rw [ite_eq_right (by omega)]

theorem monomialCoefficient_of_even {i j k : ℕ} (h : i=j+2*k) :
    monomialCoefficient i j=(if j=0 then 1 else 2)*(i.choose k : ℚ)/2^i := by
  unfold monomialCoefficient
  rw [ite_eq_left (show j ≤ i ∧ (i-j)%2 = 0 by omega),show (i-j)/2=k by omega]

theorem monomialCoefficient_of_odd {i j k : ℕ} (h : i=j+2*k+1) : monomialCoefficient i j=0 := by
  unfold monomialCoefficient
  rw [ite_eq_right (by omega)]

theorem monomialCoefficient_succ_zero (i : ℕ) :
    monomialCoefficient (i+1) 0=monomialCoefficient i 1/2 := by
  rcases Nat.even_or_odd' i with ⟨k,rfl|rfl⟩
  · rw [monomialCoefficient_of_odd (k := k) (by omega)]
    rcases k with _|k
    · rw [monomialCoefficient_of_lt (by omega)]; norm_num
    · rw [monomialCoefficient_of_odd (k := k) (by omega)]; norm_num
  · rw [monomialCoefficient_of_even (k := k+1) (by omega),monomialCoefficient_of_even (k := k) (by omega)]
    have hc : (2*k+1+1).choose (k+1)=2*(2*k+1).choose k := by
      rw [Nat.choose_succ_succ',Nat.choose_symm_half]; ring
    rw [hc]
    push_cast
    field_simp
    ring

theorem monomialCoefficient_succ_one (i : ℕ) :
    monomialCoefficient (i+1) 1=monomialCoefficient i 0+monomialCoefficient i 2/2 := by
  rcases Nat.even_or_odd' i with ⟨k,rfl|rfl⟩
  · rw [monomialCoefficient_of_even (k := k) (by omega),monomialCoefficient_of_even (k := k) (by omega)]
    rcases k with _|k
    · rw [monomialCoefficient_of_lt (by omega)]; norm_num
    · rw [monomialCoefficient_of_even (k := k) (by omega)]
      have hc : (2*(k+1)+1).choose (k+1)=(2*(k+1)).choose (k+1)+(2*(k+1)).choose k := by
        rw [show 2*(k+1)+1=(2*(k+1))+1 by ring,Nat.choose_succ_succ']
        ring
      rw [hc]
      push_cast
      field_simp
      ring
  · rw [monomialCoefficient_of_odd (k := k) (by omega),monomialCoefficient_of_odd (k := k) (by omega)]
    rcases k with _|k
    · rw [monomialCoefficient_of_lt (by omega)]; norm_num
    · rw [monomialCoefficient_of_odd (k := k) (by omega)]; norm_num

theorem monomialCoefficient_succ_succ (i j : ℕ) :
    monomialCoefficient (i+1) (j+2)=
      (monomialCoefficient i (j+1)+monomialCoefficient i (j+3))/2 := by
  rcases Nat.lt_or_ge i (j+1) with h|h
  · rw [monomialCoefficient_of_lt (by omega),monomialCoefficient_of_lt h,monomialCoefficient_of_lt (by omega)]; norm_num
  obtain ⟨m,rfl⟩ : ∃ m,i=j+1+m := ⟨i-(j+1),by omega⟩
  rcases Nat.even_or_odd' m with ⟨k,rfl|rfl⟩
  · rw [monomialCoefficient_of_even (k := k) (by omega),monomialCoefficient_of_even (k := k) (by omega)]
    rcases k with _|k
    · rw [monomialCoefficient_of_lt (by omega)]
      simp
      field_simp
      ring
    · rw [monomialCoefficient_of_even (k := k) (by omega)]
      have hc : (j+1+2*(k+1)+1).choose (k+1)=
          (j+1+2*(k+1)).choose (k+1)+(j+1+2*(k+1)).choose k := by
        rw [Nat.choose_succ_succ']
        ring
      rw [hc]
      push_cast
      field_simp
      ring
  · rw [monomialCoefficient_of_odd (k := k) (by omega),monomialCoefficient_of_odd (k := k) (by omega)]
    rcases k with _|k
    · rw [monomialCoefficient_of_lt (by omega)]; norm_num
    · rw [monomialCoefficient_of_odd (k := k) (by omega)]; norm_num

theorem X_mul_T_succ (n : ℕ) :
    X*Chebyshev.T ℚ ((n+1:ℕ):ℤ)=
      C (1/2)*Chebyshev.T ℚ ((n+2:ℕ):ℤ)+C (1/2)*Chebyshev.T ℚ (n:ℤ) := by
  have h := Chebyshev.T_add_two ℚ (n:ℤ)
  have h2 : C (1/2:ℚ)*2=1 := by rw [← C_ofNat,← C_mul]; norm_num
  push_cast
  rw [h]
  linear_combination (-(X*Chebyshev.T ℚ ((n:ℤ)+1)))*h2

theorem sum_monomialCoefficient_mul_T (i : ℕ) :
    ∑ j ∈ Finset.range (i+1),C (monomialCoefficient i j)*Chebyshev.T ℚ (j:ℤ)=X^i := by
  induction i with
  | zero => simp [monomialCoefficient]
  | succ i ih =>
    have hT1 : Chebyshev.T ℚ ((1:ℕ):ℤ)=X := by simp
    have hT0 : Chebyshev.T ℚ ((0:ℕ):ℤ)=1 := by simp
    have hhalf : ∀ a b : ℚ,C ((a+b)/2)=C (1/2)*C a+C (1/2)*C b := by
      intro a b; rw [← map_mul,← map_mul,← map_add]; congr 1; ring
    have hg : (∑ j ∈ Finset.range i,C (monomialCoefficient i (j+1))*Chebyshev.T ℚ (j:ℤ))=
        (∑ j ∈ Finset.range i,C (monomialCoefficient i (j+3))*Chebyshev.T ℚ ((j+2:ℕ):ℤ))+
          C (monomialCoefficient i 2)*Chebyshev.T ℚ ((1:ℕ):ℤ)+
            C (monomialCoefficient i 1)*Chebyshev.T ℚ ((0:ℕ):ℤ) := by
      have hz1 : monomialCoefficient i (i+1)=0 := monomialCoefficient_of_lt (by omega)
      have hz2 : monomialCoefficient i (i+1+1)=0 := monomialCoefficient_of_lt (by omega)
      have e : (∑ j ∈ Finset.range (i+1+1),C (monomialCoefficient i (j+1))*Chebyshev.T ℚ (j:ℤ))=
          ∑ j ∈ Finset.range i,C (monomialCoefficient i (j+1))*Chebyshev.T ℚ (j:ℤ) := by
        rw [Finset.sum_range_succ,Finset.sum_range_succ,hz1,hz2]; simp
      rw [← e,Finset.sum_range_succ',Finset.sum_range_succ']
    have hL : (∑ j ∈ Finset.range i,C (monomialCoefficient (i+1) (j+2))*
          Chebyshev.T ℚ ((j+2:ℕ):ℤ))=
        C (1/2)*(∑ j ∈ Finset.range i,C (monomialCoefficient i (j+1))*Chebyshev.T ℚ ((j+2:ℕ):ℤ))+
          C (1/2)*(∑ j ∈ Finset.range i,C (monomialCoefficient i (j+3))*
            Chebyshev.T ℚ ((j+2:ℕ):ℤ)) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [monomialCoefficient_succ_succ,hhalf]
      ring
    have hR : X*(∑ j ∈ Finset.range (i+1),C (monomialCoefficient i j)*Chebyshev.T ℚ (j:ℤ))=
        C (1/2)*(∑ j ∈ Finset.range i,C (monomialCoefficient i (j+1))*Chebyshev.T ℚ ((j+2:ℕ):ℤ))+
          C (1/2)*(∑ j ∈ Finset.range i,C (monomialCoefficient i (j+1))*Chebyshev.T ℚ (j:ℤ))+
            C (monomialCoefficient i 0)*X := by
      rw [Finset.sum_range_succ',mul_add,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
        ← Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        linear_combination (C (monomialCoefficient i (j+1)))*X_mul_T_succ j
      · rw [hT0]
        ring
    rw [Finset.sum_range_succ',Finset.sum_range_succ']
    simp only [Nat.add_assoc,Nat.reduceAdd,zero_add]
    have hC : ∀ a b : ℚ,C (a+b/2)=C a+C (1/2)*C b := by
      intro a b; rw [← map_mul,← map_add]; congr 1; ring
    have hC' : ∀ a : ℚ,C (a/2)=C (1/2)*C a := by
      intro a; rw [← map_mul]; congr 1; ring
    rw [hT1,hT0] at hg
    rw [hL,pow_succ,← ih,mul_comm _ X,hR,monomialCoefficient_succ_one,monomialCoefficient_succ_zero,hT1,hT0,hC,hC' (monomialCoefficient i 1)]
    linear_combination (-C (1/2:ℚ))*hg

theorem sum_monomialCoefficient_mul_T_of_le {i D : ℕ} (h : i≤D) :
    ∑ j ∈ Finset.range (D+1),C (monomialCoefficient i j)*Chebyshev.T ℚ (j:ℤ)=X^i := by
  rw [← sum_monomialCoefficient_mul_T i]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
  intro j _ hj
  rw [Finset.mem_range,not_lt] at hj
  rw [monomialCoefficient_of_lt (by omega),map_zero,zero_mul]

/-- A polynomial of degree at most `D` equals its own degree-`D` Chebyshev
re-expansion. -/
theorem eq_expansion_of_natDegree_le {D : ℕ} {p : ℚ[X]} (hp : p.natDegree≤D) :
    p=expansion D p := by
  have hser : expansion D p=
      ∑ j ∈ Finset.range (D+1),C (coefficient D p j)*Chebyshev.T ℚ (j:ℤ) := by
    rw [Finset.sum_range_succ']
    simp only [expansion,series,Nat.cast_zero,Chebyshev.T_zero,mul_one,Nat.cast_add,
      Nat.cast_one]
    rw [add_comm,Finset.sum_range (fun j => C (coefficient D p (j+1))*Chebyshev.T ℚ ((j:ℤ)+1))]
  rw [hser]
  simp only [coefficient,map_sum,map_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc p=∑ i ∈ Finset.range (D+1),C (p.coeff i)*X^i := p.as_sum_range_C_mul_X_pow' (by omega)
    _=_ := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [← sum_monomialCoefficient_mul_T_of_le (D := D) (by simp at hi; omega),Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring


namespace Certificate

/-! ## Integer coefficient lists -/

/-- The polynomial with coefficient list `l` (constant term first). -/
def toPoly : List ℤ → ℚ[X]
  | [] => 0
  | a :: l => C (a:ℚ)+X*toPoly l

def add : List ℤ → List ℤ → List ℤ
  | [],m => m
  | a :: l,[] => a :: l
  | a :: l,b :: m => (a+b) :: add l m

def smul (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: l => (c*a) :: smul c l

def mul : List ℤ → List ℤ → List ℤ
  | [],_ => []
  | _ :: _,[] => []
  | a :: l,b :: m => add (smul a (b :: m)) (0 :: mul l (b :: m))

def pow (l : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n+1 => mul (pow l n) l

theorem toPoly_add : ∀ l m : List ℤ,toPoly (add l m)=toPoly l+toPoly m
  | [],m => by simp [add,toPoly]
  | a :: l,[] => by simp [add,toPoly]
  | a :: l,b :: m => by
    simp only [add,toPoly,toPoly_add l m,Int.cast_add,map_add]
    ring

theorem toPoly_smul (c : ℤ) : ∀ l : List ℤ,toPoly (smul c l)=C (c:ℚ)*toPoly l
  | [] => by simp [smul,toPoly]
  | a :: l => by
    simp only [smul,toPoly,toPoly_smul c l,Int.cast_mul,map_mul]
    ring

theorem toPoly_mul : ∀ l m : List ℤ,toPoly (mul l m)=toPoly l*toPoly m
  | [],m => by simp [mul,toPoly]
  | a :: l,[] => by simp [mul,toPoly]
  | a :: l,b :: m => by
    rw [mul,toPoly_add,toPoly_smul]
    simp only [toPoly,toPoly_mul l (b :: m),Int.cast_zero,map_zero]
    ring

theorem toPoly_pow (l : List ℤ) : ∀ n : ℕ,toPoly (pow l n)=toPoly l^n
  | 0 => by simp [pow,toPoly]
  | n+1 => by rw [pow,toPoly_mul,toPoly_pow l n,pow_succ]

theorem toPoly_tail : ∀ l : List ℤ,toPoly l.tail=divX (toPoly l)
  | [] => by simp [toPoly]
  | a :: l => by
    simp only [toPoly,List.tail_cons,divX_add,divX_C,zero_add]
    ext n
    rw [coeff_divX,coeff_X_mul]

theorem coeff_toPoly : ∀ (l : List ℤ) (n : ℕ),(toPoly l).coeff n=(l.getD n 0 : ℚ)
  | [],n => by simp [toPoly]
  | a :: l,0 => by simp [toPoly]
  | a :: l,n+1 => by
    simp only [toPoly,coeff_add,coeff_C,coeff_X_mul,coeff_toPoly l n]
    simp

theorem natDegree_toPoly : ∀ l : List ℤ,(toPoly l).natDegree≤l.length-1
  | [] => by simp [toPoly]
  | [a] => by simp [toPoly]
  | a :: b :: l => by
    have ih := natDegree_toPoly (b :: l)
    have h1 : (X*toPoly (b :: l)).natDegree≤(b :: l).length := by
      calc (X*toPoly (b :: l)).natDegree≤X.natDegree+(toPoly (b :: l)).natDegree :=
            natDegree_mul_le
        _≤1+((b :: l).length-1) := by
            gcongr
            exact natDegree_X_le
        _=(b :: l).length := by simp; omega
    calc (toPoly (a :: b :: l)).natDegree≤
          max (C (a:ℚ)).natDegree (X*toPoly (b :: l)).natDegree := natDegree_add_le _ _
      _≤(a :: b :: l).length-1 := by
          rw [natDegree_C]
          simp only [List.length_cons] at h1 ⊢
          omega

/-! ## Scaled lists -/

/-- An integer coefficient list `l` with a scale `s`; it represents `p` when
`toPoly l = C s * p` (`Scaled.Rep`). -/
structure Scaled where
  l : List ℤ
  s : ℕ

/-- `c` represents `p`: its integer list is `s` times the coefficients of `p`. -/
def Scaled.Rep (c : Scaled) (p : ℚ[X]) : Prop := toPoly c.l=C (c.s:ℚ)*p

def Scaled.add (a b : Scaled) : Scaled :=
  ⟨Certificate.add (smul b.s a.l) (smul a.s b.l),a.s*b.s⟩
def Scaled.sub (a b : Scaled) : Scaled :=
  ⟨Certificate.add (smul b.s a.l) (smul (-(a.s:ℤ)) b.l),a.s*b.s⟩
def Scaled.neg (a : Scaled) : Scaled := ⟨smul (-1) a.l,a.s⟩
def Scaled.mul (a b : Scaled) : Scaled := ⟨Certificate.mul a.l b.l,a.s*b.s⟩
def Scaled.pow (a : Scaled) (n : ℕ) : Scaled := ⟨Certificate.pow a.l n,a.s^n⟩
/-- Represents `C q`. -/
def Scaled.const (q : ℚ) : Scaled := ⟨[q.num],q.den⟩
/-- Represents `X`. -/
def Scaled.var : Scaled := ⟨[0,1],1⟩
/-- Represents the numeral `n`. -/
def Scaled.ofNat (n : ℕ) : Scaled := ⟨[(n:ℤ)],1⟩
def Scaled.divX (a : Scaled) : Scaled := ⟨a.l.tail,a.s⟩

theorem Scaled.Rep.add {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.add b).Rep (p+q) := by
  unfold Scaled.Rep at *
  simp only [Scaled.add,toPoly_add,toPoly_smul,ha,hb,Int.cast_natCast,Nat.cast_mul,map_mul]
  ring

theorem Scaled.Rep.sub {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.sub b).Rep (p-q) := by
  unfold Scaled.Rep at *
  simp only [Scaled.sub,toPoly_add,toPoly_smul,ha,hb,Int.cast_natCast,Int.cast_neg,
    Nat.cast_mul,map_mul,map_neg]
  ring

theorem Scaled.Rep.neg {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.neg.Rep (-p) := by
  unfold Scaled.Rep at *
  simp only [Scaled.neg,toPoly_smul,ha,Int.cast_neg,Int.cast_one,map_neg,map_one]
  ring

theorem Scaled.Rep.mul {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.mul b).Rep (p*q) := by
  unfold Scaled.Rep at *
  simp only [Scaled.mul,toPoly_mul,ha,hb,Nat.cast_mul,map_mul]
  ring

theorem Scaled.Rep.pow {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (n : ℕ) :
    (a.pow n).Rep (p^n) := by
  unfold Scaled.Rep at *
  simp only [Scaled.pow,toPoly_pow,ha,Nat.cast_pow,map_pow]
  ring

theorem Scaled.Rep.divX {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.divX.Rep p.divX := by
  unfold Scaled.Rep at *
  rw [Scaled.divX,toPoly_tail,ha,divX_C_mul]

theorem Scaled.rep_const (q : ℚ) : (Scaled.const q).Rep (C q) := by
  unfold Scaled.Rep
  simp only [Scaled.const,toPoly,mul_zero,add_zero,← map_mul,Rat.den_mul_eq_num]

theorem Scaled.rep_var : Scaled.var.Rep X := by
  unfold Scaled.Rep
  simp [Scaled.var,toPoly]

theorem Scaled.rep_zero : (⟨[],1⟩ : Scaled).Rep 0 := by
  simp [Scaled.Rep,toPoly]

theorem Scaled.rep_one : (Scaled.ofNat 1).Rep 1 := by
  unfold Scaled.Rep
  simp [Scaled.ofNat,toPoly]

theorem Scaled.rep_natCast (n : ℕ) : (Scaled.ofNat n).Rep (n:ℚ[X]) := by
  unfold Scaled.Rep
  simp [Scaled.ofNat,toPoly]

theorem Scaled.rep_ofNat (n : ℕ) [n.AtLeastTwo] :
    (Scaled.ofNat n).Rep (OfNat.ofNat n : ℚ[X]) := by
  exact Scaled.rep_natCast n

theorem Scaled.Rep.coeff {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (hs : a.s≠0) (i : ℕ) :
    p.coeff i=(a.l.getD i 0:ℚ)/a.s := by
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have h := congrArg (fun q => q.coeff i) ha
  simp only [coeff_toPoly,coeff_C_mul] at h
  rw [h]
  field_simp

theorem Scaled.Rep.natDegree_le {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (hs : a.s≠0) :
    p.natDegree≤a.l.length-1 := by
  have h : p=C ((a.s:ℚ)⁻¹)*toPoly a.l := by
    rw [ha,← mul_assoc,← map_mul,inv_mul_cancel₀ (by exact_mod_cast hs),map_one,one_mul]
  rw [h]
  exact (natDegree_C_mul_le _ _).trans (natDegree_toPoly a.l)

/-- A represented polynomial whose list has at most `D+1` entries equals its
degree-`D` Chebyshev re-expansion. -/
theorem Scaled.Rep.eq_expansion {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (hs : a.s≠0) {D : ℕ}
    (hl : a.l.length≤D+1) : p=expansion D p :=
  eq_expansion_of_natDegree_le ((ha.natDegree_le hs).trans (by omega))

/-! ## Composition with the affine map of `centered` -/

/-- The coefficients `a_k num^k den^(n-k)`, starting at index `i`. -/
def prescale (num den n : ℕ) : ℕ → List ℤ → List ℤ
  | _,[] => []
  | i,a :: l => (a*((num^i*den^(n-i):ℕ):ℤ)) :: prescale num den n (i+1) l

def affMulAux (s t : ℤ) : ℤ → List ℤ → List ℤ
  | c,[] => [t*c]
  | c,x :: z => (s*x+t*c) :: affMulAux s t x z

/-- Multiplication by `s+tX` in one pass. -/
def affMulGen (s t : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: z => (s*x) :: affMulAux s t x z

/-- Multiplication by `1+X`. -/
def shiftMul : List ℤ → List ℤ
  | [] => []
  | x :: z => add (x :: z) (0 :: x :: z)

/-- Multiplication by `s+tX`, with additions only when `s = t = 1`. -/
def affMul (s t : ℤ) (z : List ℤ) : List ℤ :=
  if s=1 ∧ t=1 then shiftMul z else affMulGen s t z

/-- Composition with `s+tX` by Horner's rule. -/
def compAff (s t : ℤ) : List ℤ → List ℤ
  | [] => []
  | b :: l => add [b] (affMul s t (compAff s t l))

/-- The coefficients of `den^n p(num (s+tX)/den)`, with `n+1` the length of `l`. -/
def centerList (num den : ℕ) (s t : ℤ) (l : List ℤ) : List ℤ :=
  compAff s t (prescale num den (l.length-1) 0 l)

def Scaled.center (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨centerList num den s t c.l,c.s*den^(c.l.length-1)⟩

theorem toPoly_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    toPoly (affMulAux s t c z)=C ((t*c:ℤ):ℚ)+(C (s:ℚ)+C (t:ℚ)*X)*toPoly z
  | c,[] => by simp [affMulAux,toPoly]
  | c,x :: z => by
    simp only [affMulAux,toPoly,toPoly_affMulAux s t x z,Int.cast_add,Int.cast_mul,map_add,
      map_mul]
    ring

theorem toPoly_affMulGen (s t : ℤ) (z : List ℤ) :
    toPoly (affMulGen s t z)=(C (s:ℚ)+C (t:ℚ)*X)*toPoly z := by
  cases z with
  | nil => simp [affMulGen,toPoly]
  | cons x z =>
    simp only [affMulGen,toPoly,toPoly_affMulAux,Int.cast_mul,map_mul]
    ring

theorem toPoly_shiftMul (z : List ℤ) : toPoly (shiftMul z)=(1+X)*toPoly z := by
  cases z with
  | nil => simp [shiftMul,toPoly]
  | cons x z =>
    rw [shiftMul,toPoly_add]
    simp only [toPoly,Int.cast_zero,map_zero]
    ring

theorem toPoly_affMul (s t : ℤ) (z : List ℤ) :
    toPoly (affMul s t z)=(C (s:ℚ)+C (t:ℚ)*X)*toPoly z := by
  unfold affMul
  split_ifs with h
  · rw [toPoly_shiftMul,h.1,h.2]
    simp
  · exact toPoly_affMulGen s t z

theorem toPoly_compAff (s t : ℤ) : ∀ l : List ℤ,
    toPoly (compAff s t l)=(toPoly l).comp (C (s:ℚ)+C (t:ℚ)*X)
  | [] => by simp [compAff,toPoly]
  | b :: l => by
    simp only [compAff,toPoly_add,toPoly_affMul,toPoly_compAff s t l,toPoly,add_comp,C_comp,
      mul_comp,X_comp,mul_zero,add_zero]

theorem toPoly_prescale {num den : ℕ} (hden : den≠0) (n : ℕ) : ∀ (l : List ℤ) (i : ℕ),
    i+l.length≤n+1 →
    C ((num:ℚ)^i*den^n)*(toPoly l).comp (C ((num:ℚ)/den)*X)=
      C ((den:ℚ)^i)*toPoly (prescale num den n i l)
  | [],i,_ => by simp [prescale,toPoly]
  | a :: l,i,h => by
    simp only [List.length_cons] at h
    have ih := toPoly_prescale (num := num) hden n l (i+1) (by omega)
    have hd : (den:ℚ)≠0 := by exact_mod_cast hden
    have hi : i≤n := by omega
    have e2 : (den:ℚ)^i*den^(n-i)=den^n := by rw [← pow_add,Nat.add_sub_cancel' hi]
    have f1 : C ((den:ℚ)^i)*C (((a*((num^i*den^(n-i):ℕ):ℤ)):ℤ):ℚ)=
        C ((num:ℚ)^i*den^n)*C (a:ℚ) := by
      rw [← map_mul,← map_mul]; congr 1; push_cast; rw [← e2]; ring
    have f2 : C ((num:ℚ)^i*den^n)*C ((num:ℚ)/den)*(toPoly l).comp (C ((num:ℚ)/den)*X)=
        C ((den:ℚ)^i)*toPoly (prescale num den n (i+1) l) := by
      have hC : (C (den:ℚ))≠0 := by simpa using hd
      apply mul_left_cancel₀ hC
      have g1 : C (den:ℚ)*(C ((num:ℚ)^i*den^n)*C ((num:ℚ)/den))=C ((num:ℚ)^(i+1)*den^n) := by
        rw [← map_mul,← map_mul]; congr 1; field_simp; ring
      have g2 : C (den:ℚ)*C ((den:ℚ)^i)=C ((den:ℚ)^(i+1)) := by
        rw [← map_mul]; congr 1; ring
      calc C (den:ℚ)*(C ((num:ℚ)^i*den^n)*C ((num:ℚ)/den)*(toPoly l).comp (C ((num:ℚ)/den)*X))=
            C ((num:ℚ)^(i+1)*den^n)*(toPoly l).comp (C ((num:ℚ)/den)*X) := by rw [← g1]; ring
        _=C ((den:ℚ)^(i+1))*toPoly (prescale num den n (i+1) l) := ih
        _=C (den:ℚ)*(C ((den:ℚ)^i)*toPoly (prescale num den n (i+1) l)) := by rw [← g2]; ring
    simp only [prescale,toPoly,add_comp,C_comp,mul_comp,X_comp]
    linear_combination (-1:ℚ[X])*f1+X*f2

/-- The centered polynomial on `[a,b]`, from a representation of `p`, when
`(a+b)/2 = num*s/den` and `(b-a)/2 = num*t/den`. -/
theorem Scaled.Rep.centered {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (c.center num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  unfold Scaled.Rep at *
  have h := toPoly_prescale (num := num) hden (c.l.length-1) c.l 0 (by omega)
  simp only [pow_zero,one_mul,map_one] at h
  have hd : (den:ℚ)≠0 := by exact_mod_cast hden
  have haff : (C ((num:ℚ)/den)*X).comp (C (s:ℚ)+C (t:ℚ)*X)=affine a b := by
    rw [affine,hm,hh,mul_comp,C_comp,X_comp,mul_add,← mul_assoc,← map_mul,← map_mul]
    congr 2 <;> ring_nf
  rw [Scaled.center,centerList,toPoly_compAff,← h,hc,WholeIntervalPolynomial.centered]
  simp only [mul_comp,C_comp,comp_assoc,haff]
  push_cast
  rw [map_mul]
  ring

/-! ## Chebyshev coefficients

Horner's rule: multiplication by `2X` maps the Chebyshev coefficients `u` to
`u_1, 2u_0+u_2, u_1+u_3, u_2+u_4, ...`. -/

def twoX : List ℤ → List ℤ
  | [] => []
  | u0 :: t => add t (0 :: (2*u0) :: t)

/-- Twice the Chebyshev coefficients of `toPoly l`, times `2^(length l)`. -/
def chebList : List ℤ → List ℤ
  | [] => []
  | a :: l => add [a*((2^l.length:ℕ):ℤ)] (twoX (chebList l))

/-- The Chebyshev coefficients of `toPoly l`. -/
def chebQ (l : List ℤ) (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range l.length,(l.getD i 0:ℚ)*monomialCoefficient i j

theorem getD_add : ∀ (l m : List ℤ) (j : ℕ),(add l m).getD j 0=l.getD j 0+m.getD j 0
  | [],m,j => by simp only [add,List.getD_nil,zero_add]
  | a :: l,[],j => by simp only [add,List.getD_nil,add_zero]
  | a :: l,b :: m,0 => by simp only [add,List.getD_cons_zero]
  | a :: l,b :: m,j+1 => by simp only [add,List.getD_cons_succ,getD_add l m j]

theorem getD_twoX_zero (u : List ℤ) : (twoX u).getD 0 0=u.getD 1 0 := by
  cases u with
  | nil => simp only [twoX,List.getD_nil]
  | cons u0 t =>
    simp only [twoX,getD_add,List.getD_cons_zero,List.getD_cons_succ,add_zero]

theorem getD_twoX_one (u : List ℤ) :
    (twoX u).getD 1 0=u.getD 2 0+2*u.getD 0 0 := by
  cases u with
  | nil => simp only [twoX,List.getD_nil]; ring
  | cons u0 t => simp only [twoX,getD_add,List.getD_cons_zero,List.getD_cons_succ]

theorem getD_twoX_succ (u : List ℤ) (k : ℕ) :
    (twoX u).getD (k+2) 0=u.getD (k+3) 0+u.getD (k+1) 0 := by
  cases u with
  | nil => simp only [twoX,List.getD_nil]; ring
  | cons u0 t => simp only [twoX,getD_add,List.getD_cons_succ]

theorem chebQ_cons (a : ℤ) (l : List ℤ) (j : ℕ) :
    chebQ (a :: l) j=a*monomialCoefficient 0 j+
      ∑ i ∈ Finset.range l.length,(l.getD i 0:ℚ)*monomialCoefficient (i+1) j := by
  rw [chebQ,List.length_cons,Finset.sum_range_succ',add_comm]
  simp

theorem chebQ_cons_zero (a : ℤ) (l : List ℤ) :
    chebQ (a :: l) 0=a+chebQ l 1/2 := by
  rw [chebQ_cons,chebQ,Finset.sum_div]
  simp only [monomialCoefficient_succ_zero]
  rw [show monomialCoefficient 0 0=1 by simp [monomialCoefficient]]
  simp only [mul_one,mul_div_assoc]

theorem chebQ_cons_one (a : ℤ) (l : List ℤ) :
    chebQ (a :: l) 1=chebQ l 0+chebQ l 2/2 := by
  rw [chebQ_cons,chebQ,chebQ,Finset.sum_div,← Finset.sum_add_distrib,
    monomialCoefficient_of_lt (by norm_num)]
  simp only [monomialCoefficient_succ_one]
  simp only [mul_zero,zero_add]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem chebQ_cons_succ (a : ℤ) (l : List ℤ) (k : ℕ) :
    chebQ (a :: l) (k+2)=(chebQ l (k+1)+chebQ l (k+3))/2 := by
  rw [chebQ_cons,chebQ,chebQ,← Finset.sum_add_distrib,Finset.sum_div,
    monomialCoefficient_of_lt (by omega)]
  simp only [monomialCoefficient_succ_succ]
  simp only [mul_zero,zero_add]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem chebList_spec : ∀ (l : List ℤ) (j : ℕ),
    2*((chebList l).getD j 0:ℚ)=2^l.length*chebQ l j
  | [],j => by simp [chebList,chebQ]
  | a :: l,j => by
    have ih := chebList_spec l
    rw [chebList]
    rcases j with _|_|k
    · rw [getD_add,getD_twoX_zero,chebQ_cons_zero]
      have h1 := ih 1
      simp only [List.getD_cons_zero,List.length_cons]
      push_cast
      linear_combination h1
    · rw [getD_add,getD_twoX_one,chebQ_cons_one]
      have h0 := ih 0
      have h2 := ih 2
      simp only [List.getD_cons_succ,List.getD_nil,List.length_cons]
      push_cast
      linear_combination h2+2*h0
    · rw [getD_add,getD_twoX_succ,chebQ_cons_succ]
      have h1 := ih (k+1)
      have h3 := ih (k+3)
      simp only [List.getD_cons_succ,List.getD_nil,List.length_cons]
      push_cast
      linear_combination h3+h1

/-- The degree-`D` Chebyshev coefficients of a represented polynomial. -/
theorem Scaled.Rep.coefficient_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) (j : ℕ) :
    coefficient D p j=((chebList c.l).getD j 0:ℚ)/(c.s*2^c.l.length/2) := by
  have hs' : (c.s:ℚ)≠0 := by exact_mod_cast hs
  have hco := hc.coeff hs
  have hsum : coefficient D p j=chebQ c.l j/c.s := by
    unfold coefficient chebQ
    rw [Finset.sum_div]
    have e : ∑ i ∈ Finset.range (D+1),p.coeff i*monomialCoefficient i j=
        ∑ i ∈ Finset.range (D+1),(c.l.getD i 0:ℚ)*monomialCoefficient i j/c.s := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hco]
      ring
    rw [e]
    symm
    apply Finset.sum_subset (Finset.range_subset_range.2 hl)
    intro k _ hk
    rw [Finset.mem_range,not_lt] at hk
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hk]
  have hspec := chebList_spec c.l j
  rw [hsum,eq_div_iff (div_ne_zero (mul_ne_zero hs' (pow_ne_zero _ two_ne_zero)) two_ne_zero)]
  field_simp
  linarith [hspec]

/-- `lower`, scaled to integers. -/
def lowerZ (D : ℕ) (B : ℕ → ℤ) : ℤ := B 0-∑ j : Fin D,|B (j.val+1)|

/-- `upper`, scaled to integers. -/
def upperZ (D : ℕ) (B : ℕ → ℤ) : ℤ := B 0+∑ j : Fin D,|B (j.val+1)|

theorem lower_div (D : ℕ) (B : ℕ → ℤ) {c : ℚ} (hc : 0<c) :
    lower D (fun j => (B j:ℚ)/c)=(lowerZ D B:ℚ)/c := by
  unfold lower lowerZ
  push_cast
  simp only [abs_div,abs_of_pos hc]
  rw [sub_div,Finset.sum_div]

theorem upper_div (D : ℕ) (B : ℕ → ℤ) {c : ℚ} (hc : 0<c) :
    upper D (fun j => (B j:ℚ)/c)=(upperZ D B:ℚ)/c := by
  unfold upper upperZ
  push_cast
  simp only [abs_div,abs_of_pos hc]
  rw [add_div,Finset.sum_div]

theorem coefficient_centered_eq {c : Scaled} {a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) :
    coefficient D (WholeIntervalPolynomial.centered a b p)=
      fun j => ((chebList c.l).getD j 0:ℚ)/(c.s*2^c.l.length/2) := by
  funext j
  exact hc.coefficient_eq hs hl j

theorem scale_pos {c : Scaled} (hs : c.s≠0) : (0:ℚ)<c.s*2^c.l.length/2 :=
  div_pos (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hs) (by positivity)) two_pos

/-- `lowerOn` of a polynomial whose centered polynomial is represented by `c`. -/
theorem lowerOn_eq_of_rep {c : Scaled} {a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) :
    lowerOn D a b p=(lowerZ D (fun j => (chebList c.l).getD j 0):ℚ)/(c.s*2^c.l.length/2) := by
  unfold lowerOn
  rw [coefficient_centered_eq hc hs hl,lower_div D _ (scale_pos hs)]

/-- `upperOn` of a polynomial whose centered polynomial is represented by `c`. -/
theorem upperOn_eq_of_rep {c : Scaled} {a b : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b p)) (hs : c.s≠0) {D : ℕ}
    (hl : c.l.length≤D+1) :
    upperOn D a b p=(upperZ D (fun j => (chebList c.l).getD j 0):ℚ)/(c.s*2^c.l.length/2) := by
  unfold upperOn
  rw [coefficient_centered_eq hc hs hl,upper_div D _ (scale_pos hs)]

end Certificate

end SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial
