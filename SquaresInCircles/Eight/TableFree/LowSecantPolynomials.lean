module

public import SquaresInCircles.Eight.TableFree.SecantGainPolynomial

/-!
# Two whole-interval low-coefficient secant comparisons

Uncompiled source draft of equations (24)--(26) in the scalar companion.
These are single polynomial bounds on the full interval. No angle grid
or stored certificate array is used; the kernel reductions are unexecuted.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.LowSecantPolynomials
open Polynomial WholeIntervalPolynomial

inductive Case where | tilted | unit

def q : Case → ℚ | .tilted => 863/1000 | .unit => 1
def a : Case → ℚ | .tilted => 8627/10000 | .unit => 4461/5000
def b : Case → ℚ | .tilted => 47/250 | .unit => 359/2000
def reserve : Case → ℚ | .tilted => 44/625 | .unit => 93/2000

def numerator (i : Case) : ℚ[X] :=
  C (q i)*(VaryingBCertificate.C10-1)+C (a i)*VaryingBCertificate.S11+
    C (b i)*VaryingBCertificate.S11^2-C (35643/50000)*X+C (1199/5000)*X^2
def certificate (i : Case) : ℚ[X] := (numerator i).divX

/-! ### Exact coefficient lists

A list of rationals, lowest degree first, names a polynomial. Sums,
products, powers and compositions of such lists are exact rational
computations, which the kernel carries out. -/

private def toPoly : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => C a+X*toPoly l

private def ladd : List ℚ → List ℚ → List ℚ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a+b) :: ladd l m

private def lsmul (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (c*a) :: lsmul c l

private def lmul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | _ :: _, [] => []
  | a :: l, b :: m => ladd (lsmul a (b :: m)) (0 :: lmul l (b :: m))

private def lpow (l : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => lmul (lpow l n) l

private def lcomp : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: l, m => ladd [a] (lmul m (lcomp l m))

private theorem toPoly_add : ∀ l m : List ℚ, toPoly (ladd l m)=toPoly l+toPoly m
  | [], m => by simp [ladd,toPoly]
  | a :: l, [] => by simp [ladd,toPoly]
  | a :: l, b :: m => by
    simp only [ladd,toPoly,toPoly_add l m,C_add]
    ring

private theorem toPoly_smul (c : ℚ) : ∀ l : List ℚ, toPoly (lsmul c l)=C c*toPoly l
  | [] => by simp [lsmul,toPoly]
  | a :: l => by
    simp only [lsmul,toPoly,toPoly_smul c l,C_mul]
    ring

private theorem toPoly_mul : ∀ l m : List ℚ, toPoly (lmul l m)=toPoly l*toPoly m
  | [], m => by simp [lmul,toPoly]
  | _ :: _, [] => by simp [lmul,toPoly]
  | a :: l, b :: m => by
    rw [lmul,toPoly_add,toPoly_smul]
    simp only [toPoly,toPoly_mul l (b :: m),C_0]
    ring

private theorem toPoly_pow (l : List ℚ) : ∀ n : ℕ, toPoly (lpow l n)=toPoly l^n
  | 0 => by simp [lpow,toPoly]
  | n+1 => by rw [lpow,toPoly_mul,toPoly_pow l n,pow_succ]

private theorem toPoly_comp : ∀ l m : List ℚ, toPoly (lcomp l m)=(toPoly l).comp (toPoly m)
  | [], m => by simp [lcomp,toPoly]
  | a :: l, m => by
    rw [lcomp,toPoly_add,toPoly_mul,toPoly_comp l m]
    simp only [toPoly,add_comp,mul_comp,C_comp,X_comp,mul_zero,add_zero]

private theorem coeff_toPoly : ∀ (l : List ℚ) (i : ℕ), (toPoly l).coeff i=l.getD i 0
  | [], i => by simp [toPoly]
  | a :: l, 0 => by simp [toPoly]
  | a :: l, i+1 => by simp [toPoly,coeff_toPoly l i]

private theorem getD_large : ∀ (l : List ℚ) (N : ℕ), l.length ≤ N → l.getD N 0=0
  | [], _, _ => rfl
  | a :: l, 0, h => by simp at h
  | a :: l, N+1, h => by
    rw [List.getD_cons_succ]
    exact getD_large l N (by simp at h; omega)

private theorem natDegree_toPoly (l : List ℚ) : (toPoly l).natDegree ≤ l.length-1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_toPoly]
  exact getD_large l N (by omega)

private theorem reify_C (a : ℚ) : C a=toPoly [a] := by simp [toPoly]
private theorem reify_X : (X : ℚ[X])=toPoly [0,1] := by simp [toPoly]
private theorem reify_one : (1 : ℚ[X])=toPoly [1] := by simp [toPoly]
private theorem reify_zero : (0 : ℚ[X])=toPoly [] := rfl
private theorem reify_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : ℚ[X]))=toPoly [OfNat.ofNat n] := by
  rw [toPoly,toPoly,mul_zero,add_zero,map_ofNat]
private theorem reify_add (l m : List ℚ) : toPoly l+toPoly m=toPoly (ladd l m) :=
  (toPoly_add l m).symm
private theorem reify_sub (l m : List ℚ) :
    toPoly l-toPoly m=toPoly (ladd l (lsmul (-1) m)) := by
  rw [toPoly_add,toPoly_smul]
  simp only [map_neg,map_one]
  ring
private theorem reify_neg (l : List ℚ) : -toPoly l=toPoly (lsmul (-1) l) := by
  rw [toPoly_smul]
  simp
private theorem reify_mul (l m : List ℚ) : toPoly l*toPoly m=toPoly (lmul l m) :=
  (toPoly_mul l m).symm
private theorem reify_pow (l : List ℚ) (n : ℕ) : toPoly l^n=toPoly (lpow l n) :=
  (toPoly_pow l n).symm
private theorem reify_comp (l m : List ℚ) :
    (toPoly l).comp (toPoly m)=toPoly (lcomp l m) :=
  (toPoly_comp l m).symm

/-- The interval map `affine a b` as a coefficient list. -/
private def laffine (a b : ℚ) : List ℚ := ladd [(a+b)/2] (lmul [(b-a)/2] [0,1])

private theorem centered_toPoly (a b : ℚ) (l : List ℚ) :
    centered a b (toPoly l)=toPoly (lcomp l (laffine a b)) := by
  rw [toPoly_comp,laffine,toPoly_add,toPoly_mul,centered,affine]
  simp [toPoly]

private def lowerL (D : ℕ) (l : List ℚ) : ℚ :=
  lower D (fun j => ∑ i ∈ Finset.range (D+1), l.getD i 0*monomialCoefficient i j)

private theorem lowerOn_toPoly (D : ℕ) (a b : ℚ) (l : List ℚ) :
    lowerOn D a b (toPoly l)=lowerL D (lcomp l (laffine a b)) := by
  rw [lowerOn,lowerL,centered_toPoly]
  congr 1
  funext j
  simp only [coefficient,coeff_toPoly]

/-! ### Chebyshev expansion of a polynomial of bounded degree -/

private def fold (i k : ℕ) : ℕ := (i-2*k)+(2*k-i)

private theorem T_fold (i k : ℕ) :
    Chebyshev.T ℚ ((i:ℤ)-2*k)=Chebyshev.T ℚ (fold i k : ℕ) := by
  unfold fold
  rcases le_total (2*k) i with h | h
  · rw [Nat.sub_eq_zero_of_le h,add_zero,Nat.cast_sub h]
    push_cast
    ring_nf
  · rw [Nat.sub_eq_zero_of_le h,zero_add,Nat.cast_sub h,← Chebyshev.T_neg]
    push_cast
    ring_nf

private theorem two_X_T (n : ℤ) :
    2*X*Chebyshev.T ℚ n=Chebyshev.T ℚ (n+1)+Chebyshev.T ℚ (n-1) := by
  rw [Chebyshev.T_add_one]
  ring

/-- `(2x)^i` in the Chebyshev basis, by the binomial recursion. -/
private theorem binomial_T (i : ℕ) :
    ∑ k ∈ Finset.range (i+1), C (i.choose k : ℚ)*Chebyshev.T ℚ ((i:ℤ)-2*k)=
      C (2^i)*X^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hA : ∑ k ∈ Finset.range (i+1), C (i.choose k : ℚ)*Chebyshev.T ℚ ((i:ℤ)-2*k+1)=
        ∑ k ∈ Finset.range i, C (i.choose (k+1) : ℚ)*Chebyshev.T ℚ ((i:ℤ)-2*k-1)+
          Chebyshev.T ℚ ((i:ℤ)+1) := by
      rw [Finset.sum_range_succ']
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        congr 2
        push_cast
        ring
      · simp
    have hB : ∑ k ∈ Finset.range (i+1), C (i.choose (k+1) : ℚ)*Chebyshev.T ℚ ((i:ℤ)-2*k-1)=
        ∑ k ∈ Finset.range i, C (i.choose (k+1) : ℚ)*Chebyshev.T ℚ ((i:ℤ)-2*k-1) := by
      rw [Finset.sum_range_succ]
      simp
    calc
      ∑ k ∈ Finset.range (i+1+1), C ((i+1).choose k : ℚ)*Chebyshev.T ℚ (((i+1:ℕ):ℤ)-2*k)
          =∑ k ∈ Finset.range (i+1), (C (i.choose k : ℚ)*Chebyshev.T ℚ ((i:ℤ)-2*k-1)+
              C (i.choose (k+1) : ℚ)*Chebyshev.T ℚ ((i:ℤ)-2*k-1))+
            Chebyshev.T ℚ ((i:ℤ)+1) := by
        rw [Finset.sum_range_succ']
        congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [Nat.choose_succ_succ,Nat.cast_add,C_add,add_mul]
          congr 2 <;> push_cast <;> ring_nf
        · simp
      _ =∑ k ∈ Finset.range (i+1), C (i.choose k : ℚ)*(2*X*Chebyshev.T ℚ ((i:ℤ)-2*k)) := by
        rw [Finset.sum_add_distrib,hB,add_assoc,← hA,← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [two_X_T]
        ring
      _ =2*X*∑ k ∈ Finset.range (i+1), C (i.choose k : ℚ)*Chebyshev.T ℚ ((i:ℤ)-2*k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      _ =C (2^(i+1))*X^(i+1) := by
        rw [ih]
        simp only [map_pow,C_ofNat]
        ring

private theorem fiber_sum (i j : ℕ) :
    ∑ k ∈ Finset.range (i+1) with fold i k=j, (i.choose k : ℚ)=
      2^i*monomialCoefficient i j := by
  unfold monomialCoefficient
  by_cases h : j ≤ i ∧ (i-j)%2=0
  · rw [ite_eq_left h]
    by_cases hj : j=0
    · subst hj
      have hs : (Finset.range (i+1)).filter (fun k => fold i k=0)={i/2} := by
        ext k
        simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
        unfold fold
        omega
      rw [hs,Finset.sum_singleton,ite_eq_left rfl]
      field_simp
      simp
    · have hs : (Finset.range (i+1)).filter (fun k => fold i k=j)={(i-j)/2,(i+j)/2} := by
        ext k
        simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_insert,
          Finset.mem_singleton]
        unfold fold
        omega
      have hne : (i-j)/2≠(i+j)/2 := by omega
      rw [hs,Finset.sum_pair hne,ite_eq_right hj,
        Nat.choose_symm_of_eq_add (show i=(i+j)/2+(i-j)/2 by omega)]
      field_simp
      ring
  · rw [ite_eq_right h,mul_zero]
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter,Finset.mem_range] at hk
    unfold fold at hk
    omega

private theorem monomial_T {i D : ℕ} (hi : i ≤ D) :
    ∑ j ∈ Finset.range (D+1), C (monomialCoefficient i j)*Chebyshev.T ℚ (j:ℤ)=X^i := by
  have h2 : (C (2^i : ℚ) : ℚ[X])≠0 := by simp
  apply mul_left_cancel₀ h2
  rw [← binomial_T,Finset.mul_sum]
  simp_rw [T_fold]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range (i+1))
    (t := Finset.range (D+1)) (g := fold i)
    (fun k hk => by simp only [Finset.mem_range] at hk ⊢; unfold fold; omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc,← C_mul,← fiber_sum,map_sum,Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [(Finset.mem_filter.1 hk).2]

/-- A polynomial of degree at most `D` equals its own expansion. -/
private theorem expansion_self {D : ℕ} {q : ℚ[X]} (hq : q.natDegree ≤ D) :
    q=expansion D q := by
  have hs : expansion D q=∑ j ∈ Finset.range (D+1),
      C (coefficient D q j)*Chebyshev.T ℚ (j:ℤ) := by
    rw [expansion,series,Finset.sum_range_succ',add_comm]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range (fun j => C (coefficient D q (j+1))*
        Chebyshev.T ℚ ((j+1:ℕ):ℤ))]
      push_cast
      rfl
    · simp
  rw [hs]
  simp only [coefficient,map_sum,map_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc,← Finset.mul_sum]
  conv_lhs => rw [as_sum_range_C_mul_X_pow' q (n := D+1) (by omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [monomial_T (Finset.mem_range_succ_iff.1 hi)]

/-- An expansion identity from a coefficient list of bounded length. -/
private theorem expansion_toPoly {D : ℕ} {a b : ℚ} {l : List ℚ}
    (hl : (lcomp l (laffine a b)).length ≤ D+1) :
    centered a b (toPoly l)=expansion D (centered a b (toPoly l)) := by
  apply expansion_self
  rw [centered_toPoly]
  exact (natDegree_toPoly _).trans (by omega)

private theorem toPoly_tail : ∀ l : List ℚ, divX (toPoly l)=toPoly l.tail
  | [] => by simp [toPoly]
  | a :: l => by
    simp only [toPoly,List.tail_cons,divX_add,divX_C,zero_add]
    ext n
    rw [coeff_divX,coeff_X_mul]

/-- Unfold the polynomials of this file into coefficient lists. -/
local macro "reify" : tactic => `(tactic| simp only [certificate,numerator,q,a,b,
  VaryingBCertificate.C10,VaryingBCertificate.S11,VaryingBCertificate.S9,
  reify_C,reify_X,reify_one,reify_zero,reify_ofNat,reify_add,
  reify_sub,reify_neg,reify_mul,reify_pow,toPoly_tail])

theorem zero_identity (i : Case) : X*certificate i=numerator i := by
  have h0 : (numerator i).coeff 0=0 := by
    cases i <;> reify <;> rw [coeff_toPoly] <;> decide +kernel
  have hh := X_mul_divX_add (numerator i)
  rw [h0,map_zero,add_zero] at hh
  exact hh

theorem expansion_identity (i : Case) :
    centered 0 (7/10) (certificate i)=expansion 21 (centered 0 (7/10) (certificate i)) := by
  cases i <;> reify <;> exact expansion_toPoly (by decide +kernel)

theorem coefficient_reserve (i : Case) :
    reserve i<lowerOn 21 0 (7/10) (certificate i) := by
  cases i <;> reify <;> rw [lowerOn_toPoly] <;> simp only [reserve] <;> decide +kernel

theorem polynomial_positive (i : Case) {s : ℝ} (hs : s∈Set.Icc 0 frameCap) :
    (reserve i:ℝ)<aeval s (certificate i) := by
  have hs' : s∈Set.Icc ((0:ℚ):ℝ) ((7/10:ℚ):ℝ) := by
    have h2 : s≤7/10 := hs.2
    push_cast
    exact ⟨hs.1,h2⟩
  exact positive_on_interval (by norm_num) (expansion_identity i) (coefficient_reserve i) hs'

theorem numerator_positive (i : Case) {s : ℝ} (hs : s∈Set.Ioc 0 frameCap) :
    0<aeval s (numerator i) := by
  have hh := congrArg (fun p : ℚ[X] => aeval s p) (zero_identity i)
  simp only [map_mul,aeval_X] at hh
  rw [← hh]
  have hr : (0:ℝ)<(reserve i:ℝ) := by cases i <;> norm_num [reserve]
  exact mul_pos hs.1 (hr.trans (polynomial_positive i (Set.Ioc_subset_Icc_self hs)))

/-- The original trigonometric quadratic minorant is strictly larger
than the secant-chord polynomial, throughout the full open-positive interval. -/
theorem trigonometric_positive (i : Case) {s : ℝ} (hs : s∈Set.Ioc 0 frameCap) :
    (35643/50000)*s-(1199/5000)*s^2<
      (q i:ℝ)*(Real.cos s-1)+(a i:ℝ)*Real.sin s+(b i:ℝ)*(Real.sin s)^2 := by
  have hp := numerator_positive i hs
  have hs0 := SecantGainPolynomial.sine11_nonneg (Set.Ioc_subset_Icc_self hs)
  have hS := HighOrderTaylor.S11_le_sin hs.1.le
  have hC := Arithmetic.cos10_le_cos hs.1.le
  have hs2 := pow_le_pow_left₀ hs0 hS 2
  have hq0 : (0:ℝ)≤(q i:ℝ) := by cases i <;> norm_num [q]
  have ha0 : (0:ℝ)≤(a i:ℝ) := by cases i <;> norm_num [a]
  have hb0 : (0:ℝ)≤(b i:ℝ) := by cases i <;> norm_num [b]
  have hcos := mul_le_mul_of_nonneg_left hC hq0
  have hsin := mul_le_mul_of_nonneg_left hS ha0
  have hsine2 := mul_le_mul_of_nonneg_left hs2 hb0
  simp only [numerator,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    VaryingBCertificate.C10_eval,VaryingBCertificate.S11_eval] at hp
  norm_num at hp
  linarith

theorem coefficient_squares (i : Case) :
    (a i:ℝ)^2*((1263/2500 : ℝ)^2+(q i:ℝ)^2)<
      qCap*(1263/2500)^2*(q i:ℝ)^2 ∧
    4*(b i:ℝ)^2*((1263/2500 : ℝ)^2+(q i:ℝ)^2)^3<
      qCap*(1263/2500)^4*(q i:ℝ)^4 := by
  cases i <;> norm_num [a,b,q,qCap]

end SquaresInCircles.Eight.TableFree.LowSecantPolynomials
