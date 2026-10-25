module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.ChebyshevLeadingBounds
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3PolynomialData

/-!
# Eight squares: six whole-interval BT3 numerator certificates

The low row decreases by one Chebyshev derivative bound. The middle
row uses its displayed centered quadratic reserve. The high row has
a positive polynomial quotient at the actual D support transition.

The kernel evaluates integer coefficient lists that mirror the polynomials. The numerator
and the affine changes of variable are one integer product or evaluation read back in a large
base (Kronecker substitution).
-/

@[expose] public section
noncomputable section
open Set Polynomial
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Certificate
open PowerTailBounds
open WholeIntervalPolynomial.Certificate (Scaled toPoly upperZ lowerZ chebList)

/-! ### Scaled integer lists for the numerators

Each polynomial of the companion is mirrored by a `Scaled` integer list built with
the operations of `PolynomialCertificates`; `Scaled.Rep` ties the list to the
polynomial, and the kernel evaluates only the integer lists. -/

private theorem r66_ite_rep {P : Prop} [Decidable P] {a b : Scaled} {p q : ℚ[X]}
    (ha : a.Rep p) (hb : b.Rep q) : (if P then a else b).Rep (if P then p else q) := by
  split_ifs <;> assumption

/-- The gcd of the scale `s` and all entries of `l`. -/
private def r66_gcd (s : ℕ) : List ℤ → ℕ
  | [] => s
  | a :: l => Nat.gcd a.natAbs (r66_gcd s l)

private theorem r66_gcd_dvd (s : ℕ) : ∀ l : List ℤ,
    r66_gcd s l ∣ s ∧ ∀ a ∈ l,((r66_gcd s l : ℕ):ℤ) ∣ a
  | [] => by simp [r66_gcd]
  | a :: l => by
    obtain ⟨h1,h2⟩ := r66_gcd_dvd s l
    refine ⟨(Nat.gcd_dvd_right _ _).trans h1,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (h2 b hb)

private theorem r66_smul_div (g : ℤ) : ∀ l : List ℤ,(∀ a ∈ l,g ∣ a) →
    WholeIntervalPolynomial.Certificate.smul g (l.map (fun a => a/g))=l
  | [],_ => rfl
  | a :: l,h => by
    simp only [List.map_cons,WholeIntervalPolynomial.Certificate.smul]
    rw [Int.mul_ediv_cancel' (h a List.mem_cons_self),
      r66_smul_div g l (fun b hb => h b (List.mem_cons_of_mem a hb))]

private theorem r66_toPoly_zero : ∀ l : List ℤ,toPoly (l.map (fun _ => (0:ℤ)))=0
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons,toPoly,r66_toPoly_zero l,Int.cast_zero,map_zero,mul_zero,add_zero]

/-- Division of a scaled list by the gcd of its entries and its scale. -/
private def r66_red (c : Scaled) : Scaled :=
  ⟨c.l.map (fun a => a/((r66_gcd c.s c.l : ℕ):ℤ)),c.s/r66_gcd c.s c.l⟩

private theorem r66_rep_red {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r66_red c).Rep p := by
  obtain ⟨h1,h2⟩ := r66_gcd_dvd c.s c.l
  set g := r66_gcd c.s c.l with hg
  have hl := r66_smul_div (g:ℤ) c.l h2
  unfold Scaled.Rep at *
  rw [← hl,WholeIntervalPolynomial.Certificate.toPoly_smul] at hc
  obtain ⟨k,hk⟩ := h1
  simp only [r66_red,← hg]
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · have hs : c.s=0 := by rw [hk,h0,zero_mul]
    have hz : ∀ a ∈ c.l,a=0 := fun a ha => by
      have := h2 a ha
      rw [h0,Nat.cast_zero] at this
      exact zero_dvd_iff.mp this
    rw [h0,hs]
    simp only [Nat.cast_zero,Int.ediv_zero,Nat.zero_div,map_zero,zero_mul]
    exact r66_toPoly_zero _
  · have hg0 : (g:ℚ)≠0 := by exact_mod_cast hpos.ne'
    rw [hk,Nat.mul_div_cancel_left k hpos]
    rw [hk] at hc
    push_cast at hc
    exact mul_left_cancel₀ (show C (g:ℚ)≠0 from C_ne_zero.mpr hg0)
      (hc.trans (by rw [map_mul,mul_assoc]))

/-- The coefficient list of the derivative. -/
private def r66_deriv : List ℤ → List ℤ
  | [] => []
  | [_] => []
  | _ :: b :: l => WholeIntervalPolynomial.Certificate.add (b :: l) (0 :: r66_deriv (b :: l))

private theorem r66_toPoly_deriv : ∀ l : List ℤ,toPoly (r66_deriv l)=derivative (toPoly l)
  | [] => by simp [r66_deriv,toPoly]
  | [a] => by simp [r66_deriv,toPoly]
  | a :: b :: l => by
    rw [r66_deriv,WholeIntervalPolynomial.Certificate.toPoly_add]
    have ih := r66_toPoly_deriv (b :: l)
    simp only [toPoly] at ih ⊢
    rw [ih]
    simp only [derivative_add,derivative_C,derivative_mul,derivative_X,Int.cast_zero,map_zero]
    ring

private def r66_derivS (c : Scaled) : Scaled := ⟨r66_deriv c.l,c.s⟩

private theorem r66_rep_deriv {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r66_derivS c).Rep (derivative p) := by
  unfold Scaled.Rep at *
  rw [r66_derivS,r66_toPoly_deriv,hc,derivative_C_mul]

/-- The monomial `X^k`, as the list it would get by `Scaled.var.pow k`. -/
private def r66_mono (k : ℕ) : Scaled := ⟨List.replicate k 0++[1],1⟩
private theorem r66_mono_rep (k : ℕ) : (r66_mono k).Rep (X^k) := by
  unfold Scaled.Rep r66_mono
  simp only [Nat.cast_one,map_one,one_mul]
  induction k with
  | zero => simp [toPoly]
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,toPoly,ih,pow_succ]
    simp only [Int.cast_zero,map_zero,zero_add]
    ring

/-! The trigonometric polynomials and the coefficient families. -/

private def r66_S : Scaled := r66_red (Scaled.var
  |>.sub ((Scaled.const (1/6)).mul (r66_mono 3))
  |>.add ((Scaled.const (1/120)).mul (r66_mono 5))
  |>.sub ((Scaled.const (1/5040)).mul (r66_mono 7))
  |>.add ((Scaled.const (1/362880)).mul (r66_mono 9))
  |>.sub ((Scaled.const (1/39916800)).mul (r66_mono 11))
  |>.add ((Scaled.const (1/6227020800)).mul (r66_mono 13))
  |>.sub ((Scaled.const (1/1307674368000)).mul (r66_mono 15)))
private theorem r66_S_rep : r66_S.Rep S := r66_rep_red (Scaled.rep_var
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 3))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 5))
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 7))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 9))
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 11))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 13))
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 15)))

private def r66_C : Scaled := r66_red (Scaled.ofNat 1
  |>.sub ((Scaled.const (1/2)).mul (r66_mono 2))
  |>.add ((Scaled.const (1/24)).mul (r66_mono 4))
  |>.sub ((Scaled.const (1/720)).mul (r66_mono 6))
  |>.add ((Scaled.const (1/40320)).mul (r66_mono 8))
  |>.sub ((Scaled.const (1/3628800)).mul (r66_mono 10))
  |>.add ((Scaled.const (1/479001600)).mul (r66_mono 12))
  |>.sub ((Scaled.const (1/87178291200)).mul (r66_mono 14))
  |>.add ((Scaled.const (1/20922789888000)).mul (r66_mono 16)))
private theorem r66_C_rep : r66_C.Rep Cstar := r66_rep_red (Scaled.rep_one
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 2))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 4))
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 6))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 8))
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 10))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 12))
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 14))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 16)))

private def r66_kfull : Scaled := r66_red (Scaled.const (65433234/100000000)
  |>.sub ((Scaled.const (6770392/100000000)).mul Scaled.var)
  |>.add ((Scaled.const (39062724/100000000)).mul (r66_mono 2))
  |>.sub ((Scaled.const (29937498/100000000)).mul (r66_mono 3))
  |>.add ((Scaled.const (35999242/100000000)).mul (r66_mono 4))
  |>.sub ((Scaled.const (29068717/100000000)).mul (r66_mono 5))
  |>.add ((Scaled.const (14649232/100000000)).mul (r66_mono 6)))
private theorem r66_kfull_rep : r66_kfull.Rep (JointNegativeAETD2.Certificate.k .full) :=
  r66_rep_red (Scaled.rep_const _
  |>.sub ((Scaled.rep_const _).mul Scaled.rep_var)
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 2))
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 3))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 4))
  |>.sub ((Scaled.rep_const _).mul (r66_mono_rep 5))
  |>.add ((Scaled.rep_const _).mul (r66_mono_rep 6)))

private def r66_k : Row → Scaled
  | .low => Scaled.const (13/20)
  | _ => r66_kfull
private theorem r66_k_rep : ∀ r,(r66_k r).Rep (k r)
  | .low => Scaled.rep_const _
  | .middle => r66_kfull_rep
  | .high => r66_kfull_rep

private def r66_eta : Row → Scaled
  | .low => Scaled.const (6373/20000)
  | _ => (Scaled.const (4973/20000)).add ((Scaled.const (7/25)).mul Scaled.var)
private theorem r66_eta_rep : ∀ r,(r66_eta r).Rep (eta r)
  | .low => Scaled.rep_const _
  | .middle => (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)
  | .high => (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)

private def r66_c : Row → Scaled
  | .low => ((Scaled.const (69/50)).sub ((Scaled.const (13/5)).mul Scaled.var)).add
      ((Scaled.const (14/5)).mul (r66_mono 2))
  | .middle => ((Scaled.ofNat 1).sub ((Scaled.const (61/50)).mul (Scaled.var.sub (Scaled.const (1/4))))).add
      ((Scaled.const (43/25)).mul ((Scaled.var.sub (Scaled.const (1/4))).pow 2))
  | .high => ((Scaled.ofNat 1).sub ((Scaled.const (67/100)).mul (Scaled.var.sub (Scaled.const (1/4))))).add
      ((Scaled.const (12/25)).mul ((Scaled.var.sub (Scaled.const (1/4))).pow 2))
private theorem r66_c_rep : ∀ r,(r66_c r).Rep (c r)
  | .low => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).add
      ((Scaled.rep_const _).mul (r66_mono_rep 2))
  | .middle => (Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.sub (Scaled.rep_const _)))).add
      ((Scaled.rep_const _).mul ((Scaled.rep_var.sub (Scaled.rep_const _)).pow 2))
  | .high => (Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.sub (Scaled.rep_const _)))).add
      ((Scaled.rep_const _).mul ((Scaled.rep_var.sub (Scaled.rep_const _)).pow 2))

private def r66_f (r : Row) : Scaled := r66_red (r66_C.add ((r66_eta r).mul r66_S))
private theorem r66_f_rep (r : Row) : (r66_f r).Rep (f r) :=
  r66_rep_red (r66_C_rep.add ((r66_eta_rep r).mul r66_S_rep))

private def r66_T (r : Row) : Scaled := r66_red
  (((Scaled.ofNat 1).add ((Scaled.const 2).mul r66_C)).add
    (((Scaled.ofNat 1).add ((Scaled.const 2).mul (r66_eta r))).mul r66_S))
private theorem r66_T_rep (r : Row) : (r66_T r).Rep (Tstar r) := r66_rep_red
  ((Scaled.rep_one.add ((Scaled.rep_const _).mul r66_C_rep)).add
    ((Scaled.rep_one.add ((Scaled.rep_const _).mul (r66_eta_rep r))).mul r66_S_rep))

private def r66_zero : Scaled := ⟨[],1⟩

private def r66_a0 (r : Row) : Scaled :=
  r66_red ((Scaled.const (1/109)).mul ((Scaled.const 91).add ((Scaled.const 60).mul (r66_k r))))
private theorem r66_a0_rep (r : Row) (e : Endpoint) : (r66_a0 r).Rep (alpha r e 0) :=
  r66_rep_red ((Scaled.rep_const _).mul ((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r66_k_rep r))))
private def r66_a1 (r : Row) : Scaled :=
  r66_red ((Scaled.const (1/29)).mul (((Scaled.const 20).mul (r66_f r)).add
    ((Scaled.const 21).mul (r66_c r))))
private theorem r66_a1_rep (r : Row) (e : Endpoint) : (r66_a1 r).Rep (alpha r e 1) :=
  r66_rep_red ((Scaled.rep_const _).mul (((Scaled.rep_const _).mul (r66_f_rep r)).add
    ((Scaled.rep_const _).mul (r66_c_rep r))))
private def r66_a2 (r : Row) (e : Endpoint) : Scaled := r66_red
  (if e=.V then (Scaled.const (1/85)).mul (((Scaled.const 36).mul ((r66_k r).sub r66_S)).add
      ((Scaled.const 77).mul r66_C))
   else (Scaled.const (1/109)).mul ((Scaled.const 91).add (((Scaled.const 60).mul (r66_k r)).mul r66_C)))
private theorem r66_a2_rep (r : Row) (e : Endpoint) : (r66_a2 r e).Rep (alpha r e 2) := r66_rep_red
  (r66_ite_rep ((Scaled.rep_const _).mul (((Scaled.rep_const _).mul ((r66_k_rep r).sub r66_S_rep)).add
      ((Scaled.rep_const _).mul r66_C_rep)))
    ((Scaled.rep_const _).mul ((Scaled.rep_const _).add (((Scaled.rep_const _).mul (r66_k_rep r)).mul r66_C_rep))))
private def r66_a3 (r : Row) : Scaled :=
  r66_red ((Scaled.const (1/42)).mul ((Scaled.const 40).add ((Scaled.const 13).mul (r66_eta r))))
private theorem r66_a3_rep (r : Row) (e : Endpoint) : (r66_a3 r).Rep (alpha r e 3) :=
  r66_rep_red ((Scaled.rep_const _).mul ((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r66_eta_rep r))))
private def r66_a4 (r : Row) : Scaled := r66_red
  (if diagonalD r then Scaled.ofNat 1
   else (Scaled.const (1/29)).mul ((Scaled.const 21).add ((Scaled.const 20).mul (r66_c r))))
private theorem r66_a4_rep (r : Row) (e : Endpoint) : (r66_a4 r).Rep (alpha r e 4) := r66_rep_red
  (r66_ite_rep Scaled.rep_one
    ((Scaled.rep_const _).mul ((Scaled.rep_const _).add ((Scaled.rep_const _).mul (r66_c_rep r)))))

private def r66_v0 (r : Row) : Scaled := r66_red ((Scaled.ofNat 1).add ((r66_k r).pow 2))
private theorem r66_v0_rep (r : Row) (e : Endpoint) : (r66_v0 r).Rep (v r e 0) :=
  r66_rep_red (Scaled.rep_one.add ((r66_k_rep r).pow 2))
private def r66_v1 (r : Row) : Scaled := r66_red (((r66_f r).pow 2).add ((r66_c r).pow 2))
private theorem r66_v1_rep (r : Row) (e : Endpoint) : (r66_v1 r).Rep (v r e 1) :=
  r66_rep_red (((r66_f_rep r).pow 2).add ((r66_c_rep r).pow 2))
private def r66_v2 (r : Row) (e : Endpoint) : Scaled := r66_red
  (if e=.V then ((Scaled.ofNat 1).add ((r66_k r).pow 2)).sub (((Scaled.const 2).mul (r66_k r)).mul r66_S)
   else (Scaled.ofNat 1).add (((r66_k r).pow 2).mul (r66_C.pow 2)))
private theorem r66_v2_rep (r : Row) (e : Endpoint) : (r66_v2 r e).Rep (v r e 2) := r66_rep_red
  (r66_ite_rep ((Scaled.rep_one.add ((r66_k_rep r).pow 2)).sub
      (((Scaled.rep_const _).mul (r66_k_rep r)).mul r66_S_rep))
    (Scaled.rep_one.add (((r66_k_rep r).pow 2).mul (r66_C_rep.pow 2))))
private def r66_v3 (r : Row) : Scaled := r66_red ((Scaled.ofNat 1).add ((r66_eta r).pow 2))
private theorem r66_v3_rep (r : Row) (e : Endpoint) : (r66_v3 r).Rep (v r e 3) :=
  r66_rep_red (Scaled.rep_one.add ((r66_eta_rep r).pow 2))
private def r66_v4 (r : Row) : Scaled := r66_red
  (if diagonalD r then r66_zero else (Scaled.ofNat 1).add ((r66_c r).pow 2))
private theorem r66_v4_rep (r : Row) (e : Endpoint) : (r66_v4 r).Rep (v r e 4) := r66_rep_red
  (r66_ite_rep Scaled.rep_zero (Scaled.rep_one.add ((r66_c_rep r).pow 2)))

private def r66_w0 (r : Row) (e : Endpoint) : Scaled :=
  r66_red (if e=.V then r66_f r else (r66_f r).mul r66_C)
private theorem r66_w0_rep (r : Row) (e : Endpoint) : (r66_w0 r e).Rep (weight r e 0) :=
  r66_rep_red (r66_ite_rep (r66_f_rep r) ((r66_f_rep r).mul r66_C_rep))
private def r66_w1 (e : Endpoint) : Scaled := if e=.V then Scaled.ofNat 1 else r66_C
private theorem r66_w1_rep (r : Row) (e : Endpoint) : (r66_w1 e).Rep (weight r e 1) :=
  r66_ite_rep Scaled.rep_one r66_C_rep
private theorem r66_w2_rep (r : Row) (e : Endpoint) : (r66_f r).Rep (weight r e 2) := r66_f_rep r
private def r66_w3 (r : Row) (e : Endpoint) : Scaled :=
  r66_red (if e=.V then (r66_c r).mul r66_S else ((r66_c r).mul r66_S).mul r66_C)
private theorem r66_w3_rep (r : Row) (e : Endpoint) : (r66_w3 r e).Rep (weight r e 3) :=
  r66_rep_red (r66_ite_rep ((r66_c_rep r).mul r66_S_rep) (((r66_c_rep r).mul r66_S_rep).mul r66_C_rep))
private def r66_w4 (r : Row) (e : Endpoint) : Scaled :=
  if diagonalD r then r66_zero else r66_w0 r e
private theorem r66_w4_rep (r : Row) (e : Endpoint) : (r66_w4 r e).Rep (weight r e 4) :=
  r66_ite_rep Scaled.rep_zero (r66_w0_rep r e)

private def r66_AV (r : Row) : Scaled :=
  ((r66_f r).mul ((((Scaled.const 2).mul (r66_k r)).add (Scaled.ofNat 5)).add r66_C)).add
    ((r66_c r).mul (r66_T r))
private theorem r66_AV_rep (r : Row) :
    (r66_AV r).Rep (f r*(C 2*k r+5+Cstar)+c r*Tstar r) :=
  ((r66_f_rep r).mul ((((Scaled.rep_const _).mul (r66_k_rep r)).add (Scaled.rep_ofNat 5)).add
    r66_C_rep)).add ((r66_c_rep r).mul (r66_T_rep r))
private def r66_AF (r : Row) : Scaled :=
  ((((r66_f r).mul (((Scaled.const 2).mul (r66_k r)).add (Scaled.ofNat 5))).add
    ((r66_c r).mul (r66_T r))).mul r66_C).add
    ((r66_f r).mul ((Scaled.ofNat 1).add ((Scaled.const (13/12)).mul r66_S)))
private theorem r66_AF_rep (r : Row) :
    (r66_AF r).Rep ((f r*(C 2*k r+5)+c r*Tstar r)*Cstar+f r*(1+C (13/12)*S)) :=
  ((((r66_f_rep r).mul (((Scaled.rep_const _).mul (r66_k_rep r)).add (Scaled.rep_ofNat 5))).add
    ((r66_c_rep r).mul (r66_T_rep r))).mul r66_C_rep).add
    ((r66_f_rep r).mul (Scaled.rep_one.add ((Scaled.rep_const _).mul r66_S_rep)))
private def r66_AD (r : Row) (e : Endpoint) : Scaled :=
  (((Scaled.const (Rplus*dPlus)).mul ((Scaled.ofNat 1).add (r66_c r))).mul (r66_f r)).mul
    (if e=.V then Scaled.ofNat 1 else r66_C)
private theorem r66_AD_rep (r : Row) (e : Endpoint) :
    (r66_AD r e).Rep (C (Rplus*dPlus)*(1+c r)*f r*(if e=.V then 1 else Cstar)) :=
  (((Scaled.rep_const _).mul (Scaled.rep_one.add (r66_c_rep r))).mul (r66_f_rep r)).mul
    (r66_ite_rep Scaled.rep_one r66_C_rep)
private def r66_A (r : Row) (e : Endpoint) : Scaled := r66_red
  ((if e=.V then r66_AV r else r66_AF r).sub (if diagonalD r then r66_AD r e else r66_zero))
private theorem r66_A_rep (r : Row) (e : Endpoint) : (r66_A r e).Rep (A r e) := r66_rep_red
  ((r66_ite_rep (r66_AV_rep r) (r66_AF_rep r)).sub (r66_ite_rep (r66_AD_rep r e) Scaled.rep_zero))

/-! ### Kronecker substitution

An integer list is evaluated at an integer `B`; when every entry lies in `[-B/2,B/2)`, the list
is read back from the value as its balanced base-`B` digits (`r66k_dec_enc`). -/

/-- The list evaluated at `B`. -/
private def r66kenc (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a+B*r66kenc B l

/-- The residue of `N` modulo `B` in `[-B/2,B/2)`. -/
private def r66kbal (B N : ℤ) : ℤ := if 2*(N % B)<B then N % B else N % B-B

/-- The first `n` balanced base-`B` digits of `N`. -/
private def r66kdec (B : ℤ) : ℕ → ℤ → List ℤ
  | 0,_ => []
  | n+1,N => r66kbal B N :: r66kdec B n ((N-r66kbal B N) / B)

/-- The sum of the absolute values of the entries. -/
private def r66kasum : List ℤ → ℕ
  | [] => 0
  | a :: l => a.natAbs+r66kasum l

/-- The largest absolute value of an entry. -/
private def r66kamax : List ℤ → ℕ
  | [] => 0
  | a :: l => max a.natAbs (r66kamax l)

private theorem r66k_enc_eq (B : ℤ) : ∀ l : List ℤ,(r66kenc B l : ℚ)=(toPoly l).eval (B:ℚ)
  | [] => by simp [r66kenc,toPoly]
  | a :: l => by simp [r66kenc,toPoly,r66k_enc_eq B l]

private theorem r66k_bal_eq {B c M : ℤ} (hc : -B≤2*c ∧ 2*c<B) : r66kbal B (c+B*M)=c := by
  have hB : 0<B := by omega
  unfold r66kbal
  rw [Int.add_mul_emod_self_left]
  rcases le_or_gt 0 c with h0|h0
  · rw [Int.emod_eq_of_lt h0 (by omega),ite_eq_left hc.2]
  · have e : c % B=c+B := by
      rw [show c=(c+B)+B*(-1) by ring,Int.add_mul_emod_self_left,Int.emod_eq_of_lt (by omega) (by omega)]
      ring
    rw [e,ite_eq_right (by omega)]
    ring

private theorem r66k_dec_enc {B : ℤ} (hB : 0<B) : ∀ (n : ℕ) (c : List ℤ),c.length≤n →
    (∀ j,-B≤2*c.getD j 0 ∧ 2*c.getD j 0<B) → toPoly (r66kdec B n (r66kenc B c))=toPoly c
  | 0,c,hl,_ => by
    rw [List.length_eq_zero_iff.1 (by omega : c.length=0)]
    rfl
  | n+1,[],_,_ => by
    have h0 : r66kbal B 0=0 := by
      simpa using r66k_bal_eq (c:=0) (M:=0) (B:=B) (by omega)
    have ih : toPoly (r66kdec B n 0)=0 := r66k_dec_enc hB n [] (by simp) (fun j => by simp; omega)
    show toPoly (r66kdec B (n+1) 0)=0
    rw [r66kdec,h0,sub_zero,Int.zero_ediv]
    simp [toPoly,ih]
  | n+1,x :: c,hl,hb => by
    have hx := hb 0
    simp only [List.getD_cons_zero] at hx
    have h1 := r66k_bal_eq (M:=r66kenc B c) hx
    have h2 : (x+B*r66kenc B c-x) / B=r66kenc B c := by
      rw [add_sub_cancel_left,Int.mul_ediv_cancel_left _ hB.ne']
    have ih := r66k_dec_enc hB n c (by simpa using hl) (fun j => by simpa using hb (j+1))
    simp only [r66kenc,r66kdec,h1,h2]
    rw [toPoly,toPoly,ih]

private theorem r66k_getD_smul (c : ℤ) : ∀ (l : List ℤ) (j : ℕ),
    (WholeIntervalPolynomial.Certificate.smul c l).getD j 0=c*l.getD j 0
  | [],j => by simp [WholeIntervalPolynomial.Certificate.smul]
  | a :: l,0 => by simp [WholeIntervalPolynomial.Certificate.smul]
  | a :: l,j+1 => by
    simp only [WholeIntervalPolynomial.Certificate.smul,List.getD_cons_succ,r66k_getD_smul c l j]

private theorem r66k_getD_le_amax : ∀ (l : List ℤ) (j : ℕ),|l.getD j 0|≤r66kamax l
  | [],j => by simp
  | a :: l,0 => by simp only [List.getD_cons_zero,r66kamax]; push_cast; exact le_max_left _ _
  | a :: l,j+1 => by
    simp only [List.getD_cons_succ,r66kamax]
    push_cast
    exact (r66k_getD_le_amax l j).trans (le_max_right _ _)

private theorem r66k_mul_bound : ∀ (a m : List ℤ) (j : ℕ),
    |(WholeIntervalPolynomial.Certificate.mul a m).getD j 0|≤r66kasum a*r66kamax m
  | [],m,j => by simp [WholeIntervalPolynomial.Certificate.mul]; positivity
  | a :: l,[],j => by simp [WholeIntervalPolynomial.Certificate.mul]; positivity
  | a :: l,b :: m,j => by
    rw [WholeIntervalPolynomial.Certificate.mul,WholeIntervalPolynomial.Certificate.getD_add,
      r66k_getD_smul]
    have h1 : |a*(b :: m).getD j 0|≤|a| * r66kamax (b :: m) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (r66k_getD_le_amax _ j) (abs_nonneg a)
    have h2 : |(0 :: WholeIntervalPolynomial.Certificate.mul l (b :: m)).getD j 0|≤
        r66kasum l*r66kamax (b :: m) := by
      rcases j with _|j
      · simp only [List.getD_cons_zero,abs_zero]; positivity
      · simpa only [List.getD_cons_succ] using r66k_mul_bound l (b :: m) j
    simp only [r66kasum]
    push_cast
    calc _≤_ := abs_add_le _ _
      _≤_ := add_le_add h1 h2
      _=_ := by ring

private theorem r66k_length_add : ∀ l m : List ℤ,
    (WholeIntervalPolynomial.Certificate.add l m).length=max l.length m.length
  | [],m => by simp [WholeIntervalPolynomial.Certificate.add]
  | a :: l,[] => by simp [WholeIntervalPolynomial.Certificate.add]
  | a :: l,b :: m => by
    simp [WholeIntervalPolynomial.Certificate.add,r66k_length_add l m,Nat.succ_max_succ]

private theorem r66k_length_smul (c : ℤ) : ∀ l : List ℤ,
    (WholeIntervalPolynomial.Certificate.smul c l).length=l.length
  | [] => rfl
  | a :: l => by simp [WholeIntervalPolynomial.Certificate.smul,r66k_length_smul c l]

private theorem r66k_length_mul : ∀ a m : List ℤ,
    (WholeIntervalPolynomial.Certificate.mul a m).length≤a.length+m.length-1
  | [],m => by simp [WholeIntervalPolynomial.Certificate.mul]
  | a :: l,[] => by simp [WholeIntervalPolynomial.Certificate.mul]
  | a :: l,b :: m => by
    have ih := r66k_length_mul l (b :: m)
    rw [WholeIntervalPolynomial.Certificate.mul,r66k_length_add,r66k_length_smul]
    rcases l with _|⟨c,l⟩
    · simp [WholeIntervalPolynomial.Certificate.mul]
    · simp only [List.length_cons] at ih ⊢
      omega

/-! ### Encoded sums and products

`r66kK` holds the value `N` at a base `B` of an integer list of at most `n` entries, each of
absolute value at most `β`, that represents `s` times a polynomial.  Sums and products act on
`N` alone, so a whole expression costs a few integer operations; `toScaled` reads the list
back as balanced base-`B` digits once `B` exceeds `2β`. -/

private structure r66kK where
  N : ℤ
  s : ℕ
  n : ℕ
  β : ℕ

private def r66kK.Rep (B : ℤ) (k : r66kK) (p : ℚ[X]) : Prop :=
  ∃ l : List ℤ,l.length≤k.n ∧ (∀ j,|l.getD j 0|≤k.β) ∧ k.N=r66kenc B l ∧ toPoly l=C (k.s:ℚ)*p

private def r66kK.add (a b : r66kK) : r66kK := ⟨a.N*b.s+b.N*a.s,a.s*b.s,max a.n b.n,a.β*b.s+b.β*a.s⟩
private def r66kK.sub (a b : r66kK) : r66kK := ⟨a.N*b.s-b.N*a.s,a.s*b.s,max a.n b.n,a.β*b.s+b.β*a.s⟩
private def r66kK.mul (a b : r66kK) : r66kK := ⟨a.N*b.N,a.s*b.s,a.n+b.n-1,a.n*a.β*b.β⟩
private def r66kK.const (q : ℚ) : r66kK := ⟨q.num,q.den,1,q.num.natAbs⟩
private def r66kK.ofScaled (B : ℤ) (S : Scaled) : r66kK := ⟨r66kenc B S.l,S.s,S.l.length,r66kamax S.l⟩
private def r66kK.toScaled (B : ℤ) (k : r66kK) : Scaled :=
  if 2*(k.β:ℤ)<B then ⟨r66kdec B k.n k.N,k.s⟩ else ⟨[],0⟩

private theorem r66k_enc_add (B : ℤ) (l m : List ℤ) :
    r66kenc B (WholeIntervalPolynomial.Certificate.add l m)=r66kenc B l+r66kenc B m := by
  have e : (r66kenc B (WholeIntervalPolynomial.Certificate.add l m) : ℚ)=r66kenc B l+r66kenc B m := by
    rw [r66k_enc_eq,r66k_enc_eq,r66k_enc_eq,WholeIntervalPolynomial.Certificate.toPoly_add,eval_add]
  exact_mod_cast e

private theorem r66k_enc_smul (B c : ℤ) (l : List ℤ) :
    r66kenc B (WholeIntervalPolynomial.Certificate.smul c l)=c*r66kenc B l := by
  have e : (r66kenc B (WholeIntervalPolynomial.Certificate.smul c l) : ℚ)=c*r66kenc B l := by
    rw [r66k_enc_eq,r66k_enc_eq,WholeIntervalPolynomial.Certificate.toPoly_smul,eval_mul,eval_C]
  exact_mod_cast e

private theorem r66k_enc_mul (B : ℤ) (l m : List ℤ) :
    r66kenc B (WholeIntervalPolynomial.Certificate.mul l m)=r66kenc B l*r66kenc B m := by
  have e : (r66kenc B (WholeIntervalPolynomial.Certificate.mul l m) : ℚ)=r66kenc B l*r66kenc B m := by
    rw [r66k_enc_eq,r66k_enc_eq,r66k_enc_eq,WholeIntervalPolynomial.Certificate.toPoly_mul,eval_mul]
  exact_mod_cast e

private theorem r66k_amax_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) : r66kamax l≤β := by
  induction l generalizing β with
  | nil => simp [r66kamax]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    exact max_le h0 h1

private theorem r66k_asum_le {l : List ℤ} {β : ℕ} (h : ∀ j,|l.getD j 0|≤β) :
    r66kasum l≤l.length*β := by
  induction l generalizing β with
  | nil => simp [r66kasum]
  | cons a l ih =>
    have h0 := h 0
    simp only [List.getD_cons_zero,Int.abs_eq_natAbs,Nat.cast_le] at h0
    have h1 := ih (fun j => by simpa using h (j+1))
    simp only [r66kasum,List.length_cons]
    nlinarith

private theorem r66kK.Rep.add {B : ℤ} {a b : r66kK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.add b).Rep B (p+q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨WholeIntervalPolynomial.Certificate.add (WholeIntervalPolynomial.Certificate.smul b.s la) (WholeIntervalPolynomial.Certificate.smul a.s lb),?_,?_,?_,?_⟩
  · rw [r66k_length_add,r66k_length_smul,r66k_length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [WholeIntervalPolynomial.Certificate.getD_add,r66k_getD_smul,r66k_getD_smul]
    calc _≤|(b.s:ℤ)*la.getD j 0|+|(a.s:ℤ)*lb.getD j 0| := abs_add_le _ _
      _≤(b.s:ℤ)*a.β+(a.s:ℤ)*b.β := by
        rw [abs_mul,abs_mul,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by simp only [r66kK.add]; push_cast; ring
  · simp only [r66kK.add,r66k_enc_add,r66k_enc_smul,hNa,hNb]
    ring
  · simp only [r66kK.add,WholeIntervalPolynomial.Certificate.toPoly_add,WholeIntervalPolynomial.Certificate.toPoly_smul,hpa,hpb,Int.cast_natCast,
      Nat.cast_mul,map_mul]
    ring

private theorem r66kK.Rep.sub {B : ℤ} {a b : r66kK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.sub b).Rep B (p-q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨WholeIntervalPolynomial.Certificate.add (WholeIntervalPolynomial.Certificate.smul b.s la) (WholeIntervalPolynomial.Certificate.smul (-(a.s:ℤ)) lb),?_,?_,?_,?_⟩
  · rw [r66k_length_add,r66k_length_smul,r66k_length_smul]
    exact max_le_max hla hlb
  · intro j
    rw [WholeIntervalPolynomial.Certificate.getD_add,r66k_getD_smul,r66k_getD_smul]
    calc _≤|(b.s:ℤ)*la.getD j 0|+|(-(a.s:ℤ))*lb.getD j 0| := abs_add_le _ _
      _≤(b.s:ℤ)*a.β+(a.s:ℤ)*b.β := by
        rw [abs_mul,abs_mul,abs_neg,Nat.abs_cast,Nat.abs_cast]
        exact add_le_add (mul_le_mul_of_nonneg_left (hba j) (by positivity))
          (mul_le_mul_of_nonneg_left (hbb j) (by positivity))
      _=_ := by simp only [r66kK.sub]; push_cast; ring
  · simp only [r66kK.sub,r66k_enc_add,r66k_enc_smul,hNa,hNb]
    ring
  · simp only [r66kK.sub,WholeIntervalPolynomial.Certificate.toPoly_add,WholeIntervalPolynomial.Certificate.toPoly_smul,hpa,hpb,Int.cast_natCast,
      Int.cast_neg,Nat.cast_mul,map_mul,map_neg]
    ring

private theorem r66kK.Rep.mul {B : ℤ} {a b : r66kK} {p q : ℚ[X]} (ha : a.Rep B p) (hb : b.Rep B q) :
    (a.mul b).Rep B (p*q) := by
  obtain ⟨la,hla,hba,hNa,hpa⟩ := ha
  obtain ⟨lb,hlb,hbb,hNb,hpb⟩ := hb
  refine ⟨WholeIntervalPolynomial.Certificate.mul la lb,?_,?_,?_,?_⟩
  · have := r66k_length_mul la lb
    simp only [r66kK.mul]
    omega
  · intro j
    have h1 := r66k_mul_bound la lb j
    have h2 : r66kasum la*r66kamax lb≤a.n*a.β*b.β :=
      Nat.mul_le_mul ((r66k_asum_le hba).trans (Nat.mul_le_mul_right _ hla)) (r66k_amax_le hbb)
    simp only [r66kK.mul]
    calc _≤((r66kasum la*r66kamax lb:ℕ):ℤ) := by exact_mod_cast h1
      _≤_ := by exact_mod_cast h2
  · simp only [r66kK.mul,r66k_enc_mul,hNa,hNb]
  · simp only [r66kK.mul,WholeIntervalPolynomial.Certificate.toPoly_mul,hpa,hpb,Nat.cast_mul,map_mul]
    ring

private theorem r66kK.rep_const (B : ℤ) (q : ℚ) : (r66kK.const q).Rep B (C q) := by
  refine ⟨[q.num],by simp [r66kK.const],fun j => ?_,by simp [r66kK.const,r66kenc],?_⟩
  · rcases j with _|j
    · simp only [List.getD_cons_zero,r66kK.const]
      exact (Int.abs_eq_natAbs _).le
    · simp
  · simp only [r66kK.const,toPoly,mul_zero,add_zero,← map_mul,Rat.den_mul_eq_num]

private theorem r66kK.rep_ofScaled (B : ℤ) {S : Scaled} {p : ℚ[X]} (hS : S.Rep p) :
    (r66kK.ofScaled B S).Rep B p :=
  ⟨S.l,le_rfl,r66k_getD_le_amax S.l,rfl,hS⟩

private theorem r66kK.Rep.toScaled {B : ℤ} {k : r66kK} {p : ℚ[X]} (hk : k.Rep B p) :
    (k.toScaled B).Rep p := by
  unfold r66kK.toScaled
  split_ifs with h
  · obtain ⟨l,hl,hb,hN,hp⟩ := hk
    have hB : 0<B := lt_of_le_of_lt (by positivity) h
    show toPoly (r66kdec B k.n k.N)=_
    rw [hN,r66k_dec_enc hB _ _ hl (fun j => by obtain ⟨h1,h2⟩ := abs_le.1 (hb j); constructor <;> linarith)]
    exact hp
  · show toPoly []=C ((0:ℕ):ℚ)*p
    simp [toPoly]


/-! ### Composition with `s+tX` by Kronecker substitution

The entries of the composition of `L` with `s+tX` are at most `Σ|Lᵢ| (|s|+|t|+1)^(n-1)`, so they
are the balanced base-`B` digits of the value of `L` at `s+tB` for `B` above twice that bound. -/

private theorem r66k_asum_add : ∀ l m : List ℤ,
    r66kasum (WholeIntervalPolynomial.Certificate.add l m)≤r66kasum l+r66kasum m
  | [],m => by simp [WholeIntervalPolynomial.Certificate.add,r66kasum]
  | a :: l,[] => by simp [WholeIntervalPolynomial.Certificate.add,r66kasum]
  | a :: l,b :: m => by
    have ih := r66k_asum_add l m
    have := Int.natAbs_add_le a b
    simp only [WholeIntervalPolynomial.Certificate.add,r66kasum]
    omega

private theorem r66k_asum_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    r66kasum (WholeIntervalPolynomial.Certificate.affMulAux s t c z)≤
      s.natAbs*r66kasum z+t.natAbs*c.natAbs+t.natAbs*r66kasum z
  | c,[] => by simp [WholeIntervalPolynomial.Certificate.affMulAux,r66kasum,Int.natAbs_mul]
  | c,x :: z => by
    have ih := r66k_asum_affMulAux s t x z
    have h1 := Int.natAbs_add_le (s*x) (t*c)
    simp only [WholeIntervalPolynomial.Certificate.affMulAux,r66kasum,Int.natAbs_mul] at h1 ⊢
    nlinarith

private theorem r66k_asum_affMul (s t : ℤ) (z : List ℤ) :
    r66kasum (WholeIntervalPolynomial.Certificate.affMul s t z)≤(s.natAbs+t.natAbs)*r66kasum z := by
  unfold WholeIntervalPolynomial.Certificate.affMul
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    cases z with
    | nil => simp [WholeIntervalPolynomial.Certificate.shiftMul,r66kasum]
    | cons x z =>
      have := r66k_asum_add (x :: z) (0 :: x :: z)
      simp only [WholeIntervalPolynomial.Certificate.shiftMul]
      simp only [r66kasum] at this ⊢
      simp
      omega
  · cases z with
    | nil => simp [WholeIntervalPolynomial.Certificate.affMulGen,r66kasum]
    | cons x z =>
      have := r66k_asum_affMulAux s t x z
      simp only [WholeIntervalPolynomial.Certificate.affMulGen,r66kasum,Int.natAbs_mul]
      nlinarith

private theorem r66k_asum_compAff (s t : ℤ) : ∀ l : List ℤ,
    r66kasum (WholeIntervalPolynomial.Certificate.compAff s t l)≤
      r66kasum l*(s.natAbs+t.natAbs+1)^(l.length-1)
  | [] => by simp [WholeIntervalPolynomial.Certificate.compAff,r66kasum]
  | b :: l => by
    have h1 := r66k_asum_add [b] (WholeIntervalPolynomial.Certificate.affMul s t
      (WholeIntervalPolynomial.Certificate.compAff s t l))
    have h2 := r66k_asum_affMul s t (WholeIntervalPolynomial.Certificate.compAff s t l)
    have hb : r66kasum [b]=b.natAbs := by simp [r66kasum]
    rw [WholeIntervalPolynomial.Certificate.compAff]
    simp only [r66kasum,List.length_cons,Nat.add_sub_cancel]
    rcases l with _|⟨c,l⟩
    · simp [WholeIntervalPolynomial.Certificate.compAff,WholeIntervalPolynomial.Certificate.affMul,
        WholeIntervalPolynomial.Certificate.shiftMul,WholeIntervalPolynomial.Certificate.affMulGen,
        WholeIntervalPolynomial.Certificate.add,r66kasum]
    · have ih := r66k_asum_compAff s t (c :: l)
      generalize r66kasum (WholeIntervalPolynomial.Certificate.compAff s t (c :: l))=A at h1 h2 ih
      simp only [List.length_cons,Nat.add_sub_cancel] at ih ⊢
      have key : (s.natAbs+t.natAbs)*A≤r66kasum (c :: l)*(s.natAbs+t.natAbs+1)^(l.length+1) :=
        calc (s.natAbs+t.natAbs)*A≤(s.natAbs+t.natAbs+1)*A := Nat.mul_le_mul_right _ (Nat.le_succ _)
          _≤(s.natAbs+t.natAbs+1)*(r66kasum (c :: l)*(s.natAbs+t.natAbs+1)^l.length) :=
            Nat.mul_le_mul_left _ ih
          _=_ := by ring
      have hM : 1≤(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.one_le_pow _ _ (by omega)
      have hb' : b.natAbs≤b.natAbs*(s.natAbs+t.natAbs+1)^(l.length+1) := Nat.le_mul_of_pos_right _ hM
      rw [hb] at h1
      rw [add_mul]
      omega

private theorem r66k_getD_le_asum : ∀ (l : List ℤ) (j : ℕ),(l.getD j 0).natAbs≤r66kasum l
  | [],j => by simp [r66kasum]
  | a :: l,0 => by simp [r66kasum]
  | a :: l,j+1 => by
    have := r66k_getD_le_asum l j
    simp only [List.getD_cons_succ,r66kasum]
    omega

private theorem r66k_length_affMulAux (s t : ℤ) : ∀ (c : ℤ) (z : List ℤ),
    (WholeIntervalPolynomial.Certificate.affMulAux s t c z).length=z.length+1
  | c,[] => rfl
  | c,x :: z => by
    simp [WholeIntervalPolynomial.Certificate.affMulAux,r66k_length_affMulAux s t x z]

private theorem r66k_length_affMul (s t : ℤ) (z : List ℤ) :
    (WholeIntervalPolynomial.Certificate.affMul s t z).length≤z.length+1 := by
  unfold WholeIntervalPolynomial.Certificate.affMul
  split_ifs
  · cases z with
    | nil => simp [WholeIntervalPolynomial.Certificate.shiftMul]
    | cons x z =>
      rw [WholeIntervalPolynomial.Certificate.shiftMul,r66k_length_add]
      simp
  · cases z with
    | nil => simp [WholeIntervalPolynomial.Certificate.affMulGen]
    | cons x z =>
      simp [WholeIntervalPolynomial.Certificate.affMulGen,r66k_length_affMulAux]

private theorem r66k_length_compAff (s t : ℤ) : ∀ l : List ℤ,
    (WholeIntervalPolynomial.Certificate.compAff s t l).length≤l.length
  | [] => by simp [WholeIntervalPolynomial.Certificate.compAff]
  | b :: l => by
    have ih := r66k_length_compAff s t l
    have h := r66k_length_affMul s t (WholeIntervalPolynomial.Certificate.compAff s t l)
    rw [WholeIntervalPolynomial.Certificate.compAff,r66k_length_add]
    simp only [List.length_cons,List.length_nil]
    omega

private def r66kkcenterWith (B s t : ℤ) (L : List ℤ) : List ℤ :=
  r66kdec B L.length (r66kenc (s+t*B) L)
/-- The composition of `L` with `s+tX`, by one evaluation at `s+tB`, read back in base
`B = 2 Σ|Lᵢ| (|s|+|t|+1)^(n-1) + 1`. -/
private def r66kkcenterAux (s t : ℤ) (L : List ℤ) : List ℤ :=
  r66kkcenterWith (2*(r66kasum L*(s.natAbs+t.natAbs+1)^(L.length-1))+1) s t L

private theorem r66k_toPoly_kcenterAux (s t : ℤ) (L : List ℤ) :
    toPoly (r66kkcenterAux s t L)=toPoly (WholeIntervalPolynomial.Certificate.compAff s t L) := by
  rw [r66kkcenterAux,r66kkcenterWith]
  generalize hB : (2*(r66kasum L*(s.natAbs+t.natAbs+1)^(L.length-1))+1 : ℤ)=B
  have hB0 : 0<B := by rw [← hB]; positivity
  have he : r66kenc (s+t*B) L=r66kenc B (WholeIntervalPolynomial.Certificate.compAff s t L) := by
    have e : (r66kenc (s+t*B) L : ℚ)=(r66kenc B (WholeIntervalPolynomial.Certificate.compAff s t L) : ℚ) := by
      rw [r66k_enc_eq,r66k_enc_eq,WholeIntervalPolynomial.Certificate.toPoly_compAff,eval_comp]
      simp
    exact_mod_cast e
  rw [he]
  apply r66k_dec_enc hB0 _ _ (r66k_length_compAff s t L)
  intro j
  have h1 := r66k_getD_le_asum (WholeIntervalPolynomial.Certificate.compAff s t L) j
  have h2 := r66k_asum_compAff s t L
  have h3 : ((WholeIntervalPolynomial.Certificate.compAff s t L).getD j 0).natAbs≤
      r66kasum L*(s.natAbs+t.natAbs+1)^(L.length-1) := h1.trans h2
  have h4 : |(WholeIntervalPolynomial.Certificate.compAff s t L).getD j 0|≤
      ((r66kasum L*(s.natAbs+t.natAbs+1)^(L.length-1) : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h3
  obtain ⟨h5,h6⟩ := abs_le.1 h4
  push_cast at h5 h6 hB
  constructor <;> linarith

/-- `Scaled.center`, with the composition by `r66kkcenterAux`. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.kcenter
    (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨r66kkcenterAux s t (WholeIntervalPolynomial.Certificate.prescale num den (c.l.length-1) 0 c.l),
    c.s*den^(c.l.length-1)⟩

private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.kcentered
    {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (c.kcenter num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  have h := hc.centered num den s t hden hm hh
  unfold Scaled.Rep at h ⊢
  show toPoly (r66kkcenterAux s t _)=_
  rw [r66k_toPoly_kcenterAux]
  exact h

private theorem r66_rep_eq {S : Scaled} {p q : ℚ[X]} (e : q=p) (h : S.Rep q) : S.Rep p := e ▸ h

/-- The numerator on encoded lists, with its sums and products written out; the partial
products `a0a1`, `a3a4`, `a0a1a2`, `a2a3a4` are shared. -/
private def r66_numKT (A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 P01 P34 P012 P234 : r66kK) :
    r66kK :=
  (((r66kK.const 2).mul A).mul (P012.mul P34)).sub ((r66kK.const Rplus).mul
    ((w0.mul (v0.add (a0.mul a0))).mul (a1.mul P234)
      |>.add ((w1.mul (v1.add (a1.mul a1))).mul (a0.mul P234))
      |>.add ((w2.mul (v2.add (a2.mul a2))).mul (P01.mul P34))
      |>.add ((w3.mul (v3.add (a3.mul a3))).mul (P012.mul a4))
      |>.add ((w4.mul (v4.add (a4.mul a4))).mul (P012.mul a3))))
private def r66_numKS (A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 P01 P34 : r66kK) : r66kK :=
  r66_numKT A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 P01 P34 (P01.mul a2) (a2.mul P34)
private def r66_numKE (A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 : r66kK) : r66kK :=
  r66_numKS A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 (a0.mul a1) (a3.mul a4)
private def r66_numKB (B : ℤ) (A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 : Scaled) :
    r66kK :=
  r66_numKE (.ofScaled B A) (.ofScaled B a0) (.ofScaled B a1) (.ofScaled B a2) (.ofScaled B a3)
    (.ofScaled B a4) (.ofScaled B w0) (.ofScaled B w1) (.ofScaled B w2) (.ofScaled B w3)
    (.ofScaled B w4) (.ofScaled B v0) (.ofScaled B v1) (.ofScaled B v2) (.ofScaled B v3)
    (.ofScaled B v4)
private def r66_numWith (B : ℤ) (A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 : Scaled) :
    Scaled :=
  (r66_numKB B A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4).toScaled B
/-- The numerator of the lists, read back in a base above twice its coefficient bound. -/
private def r66_num (A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 : Scaled) : Scaled :=
  r66_numWith (2*(r66_numKB 0 A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4).β+1)
    A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4
private theorem r66_numWith_rep (B : ℤ) {A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 : Scaled}
    {pA p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 u0 u1 u2 u3 u4 : ℚ[X]}
    (hA : A.Rep pA) (h0 : a0.Rep p0) (h1 : a1.Rep p1) (h2 : a2.Rep p2) (h3 : a3.Rep p3)
    (h4 : a4.Rep p4) (g0 : w0.Rep q0) (g1 : w1.Rep q1) (g2 : w2.Rep q2) (g3 : w3.Rep q3)
    (g4 : w4.Rep q4) (k0 : v0.Rep u0) (k1 : v1.Rep u1) (k2 : v2.Rep u2) (k3 : v3.Rep u3)
    (k4 : v4.Rep u4) :
    (r66_numWith B A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4).Rep
      (C 2*pA*((p0*p1*p2)*(p3*p4))-C Rplus*(q0*(u0+p0^2)*(p1*(p2*(p3*p4)))+
        q1*(u1+p1^2)*(p0*(p2*(p3*p4)))+q2*(u2+p2^2)*((p0*p1)*(p3*p4))+
        q3*(u3+p3^2)*((p0*p1*p2)*p4)+q4*(u4+p4^2)*((p0*p1*p2)*p3))) := by
  have jA := r66kK.rep_ofScaled B hA
  have j0 := r66kK.rep_ofScaled B h0
  have j1 := r66kK.rep_ofScaled B h1
  have j2 := r66kK.rep_ofScaled B h2
  have j3 := r66kK.rep_ofScaled B h3
  have j4 := r66kK.rep_ofScaled B h4
  have m0 := r66kK.rep_ofScaled B g0
  have m1 := r66kK.rep_ofScaled B g1
  have m2 := r66kK.rep_ofScaled B g2
  have m3 := r66kK.rep_ofScaled B g3
  have m4 := r66kK.rep_ofScaled B g4
  have n0 := r66kK.rep_ofScaled B k0
  have n1 := r66kK.rep_ofScaled B k1
  have n2 := r66kK.rep_ofScaled B k2
  have n3 := r66kK.rep_ofScaled B k3
  have n4 := r66kK.rep_ofScaled B k4
  have P01 := j0.mul j1
  have P34 := j3.mul j4
  have P012 := P01.mul j2
  have P234 := j2.mul P34
  exact r66_rep_eq (by ring) (r66kK.Rep.toScaled
    ((((r66kK.rep_const B 2).mul jA).mul (P012.mul P34)).sub ((r66kK.rep_const B Rplus).mul
      ((m0.mul (n0.add (j0.mul j0))).mul (j1.mul P234)
        |>.add ((m1.mul (n1.add (j1.mul j1))).mul (j0.mul P234))
        |>.add ((m2.mul (n2.add (j2.mul j2))).mul (P01.mul P34))
        |>.add ((m3.mul (n3.add (j3.mul j3))).mul (P012.mul j4))
        |>.add ((m4.mul (n4.add (j4.mul j4))).mul (P012.mul j3))))))
private theorem r66_num_rep {A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4 : Scaled}
    {pA p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 u0 u1 u2 u3 u4 : ℚ[X]}
    (hA : A.Rep pA) (h0 : a0.Rep p0) (h1 : a1.Rep p1) (h2 : a2.Rep p2) (h3 : a3.Rep p3)
    (h4 : a4.Rep p4) (g0 : w0.Rep q0) (g1 : w1.Rep q1) (g2 : w2.Rep q2) (g3 : w3.Rep q3)
    (g4 : w4.Rep q4) (k0 : v0.Rep u0) (k1 : v1.Rep u1) (k2 : v2.Rep u2) (k3 : v3.Rep u3)
    (k4 : v4.Rep u4) :
    (r66_num A a0 a1 a2 a3 a4 w0 w1 w2 w3 w4 v0 v1 v2 v3 v4).Rep
      (C 2*pA*((p0*p1*p2)*(p3*p4))-C Rplus*(q0*(u0+p0^2)*(p1*(p2*(p3*p4)))+
        q1*(u1+p1^2)*(p0*(p2*(p3*p4)))+q2*(u2+p2^2)*((p0*p1)*(p3*p4))+
        q3*(u3+p3^2)*((p0*p1*p2)*p4)+q4*(u4+p4^2)*((p0*p1*p2)*p3))) :=
  r66_numWith_rep _ hA h0 h1 h2 h3 h4 g0 g1 g2 g3 g4 k0 k1 k2 k3 k4

private theorem r66_numerator_eq (r : Row) (e : Endpoint) : numerator r e=
    C 2*A r e*((alpha r e 0*alpha r e 1*alpha r e 2)*(alpha r e 3*alpha r e 4))-C Rplus*
      (weight r e 0*(v r e 0+(alpha r e 0)^2)*(alpha r e 1*(alpha r e 2*(alpha r e 3*alpha r e 4)))+
      weight r e 1*(v r e 1+(alpha r e 1)^2)*(alpha r e 0*(alpha r e 2*(alpha r e 3*alpha r e 4)))+
      weight r e 2*(v r e 2+(alpha r e 2)^2)*((alpha r e 0*alpha r e 1)*(alpha r e 3*alpha r e 4))+
      weight r e 3*(v r e 3+(alpha r e 3)^2)*((alpha r e 0*alpha r e 1*alpha r e 2)*alpha r e 4)+
      weight r e 4*(v r e 4+(alpha r e 4)^2)*((alpha r e 0*alpha r e 1*alpha r e 2)*alpha r e 3)) := by
  have h0 : (Finset.univ.erase (0:Fin 5))={1,2,3,4} := by decide
  have h1 : (Finset.univ.erase (1:Fin 5))={0,2,3,4} := by decide
  have h2 : (Finset.univ.erase (2:Fin 5))={0,1,3,4} := by decide
  have h3 : (Finset.univ.erase (3:Fin 5))={0,1,2,4} := by decide
  have h4 : (Finset.univ.erase (4:Fin 5))={0,1,2,3} := by decide
  rw [numerator,Fin.prod_univ_five,Fin.sum_univ_five,h0,h1,h2,h3,h4]
  simp only [Finset.prod_insert (show (1:Fin 5)∉({2,3,4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (2:Fin 5)∉({3,4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (3:Fin 5)∉({4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (0:Fin 5)∉({2,3,4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (0:Fin 5)∉({1,3,4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (1:Fin 5)∉({3,4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (0:Fin 5)∉({1,2,4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (1:Fin 5)∉({2,4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (2:Fin 5)∉({4}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (0:Fin 5)∉({1,2,3}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (1:Fin 5)∉({2,3}:Finset (Fin 5)) by decide),
    Finset.prod_insert (show (2:Fin 5)∉({3}:Finset (Fin 5)) by decide),
    Finset.prod_singleton]
  ring

private def r66_N (r : Row) (e : Endpoint) : Scaled := r66_red
  (r66_num (r66_A r e) (r66_a0 r) (r66_a1 r) (r66_a2 r e) (r66_a3 r) (r66_a4 r)
    (r66_w0 r e) (r66_w1 e) (r66_f r) (r66_w3 r e) (r66_w4 r e)
    (r66_v0 r) (r66_v1 r) (r66_v2 r e) (r66_v3 r) (r66_v4 r))
private theorem r66_N_rep (r : Row) (e : Endpoint) : (r66_N r e).Rep (numerator r e) := by
  rw [r66_numerator_eq]
  exact r66_rep_red (r66_num_rep (r66_A_rep r e) (r66_a0_rep r e) (r66_a1_rep r e) (r66_a2_rep r e)
    (r66_a3_rep r e) (r66_a4_rep r e) (r66_w0_rep r e) (r66_w1_rep r e) (r66_w2_rep r e)
    (r66_w3_rep r e) (r66_w4_rep r e) (r66_v0_rep r e) (r66_v1_rep r e) (r66_v2_rep r e)
    (r66_v3_rep r e) (r66_v4_rep r e))



/-! ### From integer facts to the rational certificate statements -/

private theorem r66_eval_rat (p : ℚ[X]) (x : ℚ) : aeval (x:ℝ) p=((p.eval x:ℚ):ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial n a => simp

private theorem r66_centered_point (a : ℚ) (p : ℚ[X]) :
    WholeIntervalPolynomial.centered a a p=C (p.eval a) := by
  rw [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,sub_self,zero_div,map_zero,
    zero_mul,add_zero,add_self_div_two,comp_C]

private theorem r66_eval_eq {c : Scaled} {a : ℚ} {p : ℚ[X]}
    (hc : c.Rep (WholeIntervalPolynomial.centered a a p)) (hs : c.s≠0) :
    p.eval a=(c.l.getD 0 0:ℚ)/c.s := by
  have h := hc.coeff hs 0
  rwa [r66_centered_point,coeff_C_zero] at h

private theorem r66_upper_lt {U n : ℤ} {s L d : ℕ} (hs : s≠0) (hd : 0<d)
    (h : 2*U*d<n*((s:ℤ)*2^L)) : (U:ℚ)/((s:ℚ)*2^L/2)<(n:ℚ)/d := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ (by positivity) hd']
  have h' : ((2*U*d:ℤ):ℚ)<((n*((s:ℤ)*2^L):ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

private theorem r66_lower_gt {U n : ℤ} {s L d : ℕ} (hs : s≠0) (hd : 0<d)
    (h : n*((s:ℤ)*2^L)<2*U*d) : (n:ℚ)/d<(U:ℚ)/((s:ℚ)*2^L/2) := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hd' (by positivity)]
  have h' : ((n*((s:ℤ)*2^L):ℤ):ℚ)<((2*U*d:ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

private theorem r66_lt_frac {Z n : ℤ} {s d : ℕ} (hs : s≠0) (hd : 0<d)
    (h : n*(s:ℤ)<Z*d) : (n:ℚ)/d<(Z:ℚ)/s := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hd' hs']
  exact_mod_cast h

private theorem r66_abs_lt_frac {Z n : ℤ} {s d : ℕ} (hs : s≠0) (hd : 0<d)
    (h : |Z| * d<n*(s:ℤ)) : |(Z:ℚ)/s|<(n:ℚ)/d := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  rw [abs_div,abs_of_pos hs',div_lt_div_iff₀ hs' hd']
  have h' : ((|Z| * d:ℤ):ℚ)<((n*(s:ℤ)):ℤ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- `∑ |x j| (a/b)^(j+1)` over `j<n`, times `b^n`. -/
private def r66_Z (x : ℕ → ℤ) (a b : ℕ) : ℕ → ℤ
  | 0 => 0
  | n+1 => r66_Z x a b n*b+|x n| * ((a^(n+1):ℕ):ℤ)

private theorem r66_Z_eq (x : ℕ → ℤ) (a b : ℕ) (hb : b≠0) : ∀ n : ℕ,
    (∑ j : Fin n,|(x j:ℚ)| * ((a:ℚ)/b)^(j.val+1))=(r66_Z x a b n:ℚ)/(b:ℚ)^n
  | 0 => by simp [r66_Z]
  | n+1 => by
    have hb' : (b:ℚ)≠0 := by exact_mod_cast hb
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [r66_Z_eq x a b hb n]
    simp only [r66_Z]
    push_cast
    rw [div_pow,pow_succ (b:ℚ) n]
    field_simp

private theorem r66_norm_eq {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (start n a b : ℕ) (hb : b≠0) :
    PowerTailBounds.norm p start n ((a:ℚ)/b)=
      (r66_Z (fun j => c.l.getD (j+start) 0) a b n:ℚ)/((c.s:ℚ)*(b:ℚ)^n) := by
  have hs' : (c.s:ℚ)≠0 := by exact_mod_cast hs
  have h := r66_Z_eq (fun j => c.l.getD (j+start) 0) a b hb n
  unfold PowerTailBounds.norm
  simp only [hc.coeff hs,abs_div,abs_of_pos (show (0:ℚ)<c.s by positivity)]
  rw [show (∑ j : Fin n,|(c.l.getD (j.val+start) 0:ℚ)|/c.s*((a:ℚ)/b)^(j.val+1))=
      (∑ j : Fin n,|((c.l.getD (j.val+start) 0:ℤ):ℚ)| * ((a:ℚ)/b)^(j.val+1))/c.s by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring]
  rw [h]
  field_simp

private theorem r66_quad_frac {l2 Z n : ℤ} {s d B : ℕ} (hs : s≠0) (hd : 0<d) (hB : 0<B)
    (h : n*((s:ℤ)*B)<(l2*B-Z)*d) : (n:ℚ)/d<(l2:ℚ)/s-(Z:ℚ)/((s:ℚ)*B) := by
  have hs' : (0:ℚ)<s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd' : (0:ℚ)<d := by exact_mod_cast hd
  have hB' : (0:ℚ)<B := by exact_mod_cast hB
  rw [show (l2:ℚ)/s-(Z:ℚ)/((s:ℚ)*B)=(l2*B-Z)/((s:ℚ)*B) by field_simp,
    div_lt_div_iff₀ hd' (by positivity)]
  have h' : ((n*((s:ℤ)*B):ℤ):ℚ)<(((l2*B-Z)*d:ℤ):ℚ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- A polynomial of degree at most `n+2` is its quadratic part plus its tail. -/
private theorem r66_expand3 (p : ℚ[X]) (n : ℕ) (hp : p.natDegree≤n+2) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2+tail p 3 n := by
  have h := p.as_sum_range' (n+3) (by omega)
  rw [Finset.sum_range_succ',Finset.sum_range_succ',Finset.sum_range_succ'] at h
  simp only [tail]
  rw [Fin.sum_univ_eq_sum_range (fun j => C (p.coeff (j+3))*X^(j+3)) n]
  conv_lhs => rw [h]
  simp only [← C_mul_X_pow_eq_monomial,add_assoc,Nat.reduceAdd,zero_add,pow_zero,pow_one,mul_one]
  ring

/-- The quotient of a polynomial of degree at most `n` by `X` after its constant term. -/
private theorem r66_quot (p : ℚ[X]) (n : ℕ) (hp : p.natDegree≤n) :
    (∑ i : Fin n,C (p.coeff (i.val+1))*X^i.val)=divX p := by
  ext m
  simp only [finsetSum_coeff,coeff_C_mul,coeff_X_pow,coeff_divX,mul_ite,mul_one,mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i => if m=i then p.coeff (i+1) else 0) n,Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · rw [Finset.mem_range,not_lt] at hm
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-! ### Rescaling a list from `q(m X)` back to `q` -/

private theorem r66_coeff_comp_CX (q : ℚ[X]) (r : ℚ) (k : ℕ) :
    (q.comp (C r*X)).coeff k=q.coeff k*r^k := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp,coeff_add,coeff_add,hp,hq,add_mul]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial,mul_comp,C_comp,pow_comp,X_comp,mul_pow,← C_pow,← mul_assoc,
      ← map_mul,coeff_C_mul_X_pow,coeff_C_mul_X_pow]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]

private def r66_rs (u w n : ℕ) : ℕ → List ℤ → List ℤ
  | _,[] => []
  | k,a :: l => (a*((u^k*w^(n-k):ℕ):ℤ)) :: r66_rs u w n (k+1) l

private theorem r66_rs_getD (u w n : ℕ) : ∀ (l : List ℤ) (k i : ℕ),
    (r66_rs u w n k l).getD i 0=l.getD i 0*((u^(k+i)*w^(n-(k+i)):ℕ):ℤ)
  | [],k,i => by simp [r66_rs]
  | a :: l,k,0 => by simp [r66_rs]
  | a :: l,k,i+1 => by
    simp only [r66_rs,List.getD_cons_succ]
    rw [r66_rs_getD u w n l (k+1) i,show k+1+i=k+(i+1) by ring]

/-- From a list for `q(w X/u)` to a list for `q`. -/
private def r66_rescale (c : Scaled) (u w : ℕ) : Scaled :=
  ⟨r66_rs u w (c.l.length-1) 0 c.l,c.s*w^(c.l.length-1)⟩

private theorem r66_rep_rescale {c : Scaled} {q : ℚ[X]} {u w : ℕ} (hu : u≠0) (hw : w≠0)
    (hc : c.Rep (q.comp (C ((w:ℚ)/u)*X))) : (r66_rescale c u w).Rep q := by
  unfold Scaled.Rep at *
  have hu' : (u:ℚ)≠0 := by exact_mod_cast hu
  have hw' : (w:ℚ)≠0 := by exact_mod_cast hw
  ext k
  have hk := congrArg (fun p => p.coeff k) hc
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul,r66_coeff_comp_CX] at hk
  simp only [r66_rescale,WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul,
    r66_rs_getD,zero_add]
  by_cases hkn : k≤c.l.length-1
  · push_cast
    rw [hk,div_pow]
    obtain ⟨j,hj⟩ : ∃ j,c.l.length-1=k+j := ⟨c.l.length-1-k,by omega⟩
    rw [hj,show k+j-k=j by omega,pow_add]
    field_simp
  · have hz : c.l.getD k 0=0 := by
      rw [List.getD_eq_default]
      omega
    rw [hz] at hk ⊢
    push_cast at hk ⊢
    have hp : ((w:ℚ)/u)^k≠0 := pow_ne_zero _ (div_ne_zero hw' hu')
    have h1 : (c.s:ℚ)*q.coeff k=0 := by
      have := hk.symm
      rw [← mul_assoc] at this
      exact (mul_eq_zero.mp this).resolve_right hp
    linear_combination (-((w:ℚ)^(c.l.length-1)))*h1

private theorem r66_centered_comp (m : ℚ) (p : ℚ[X]) :
    WholeIntervalPolynomial.centered 0 (2*m) p=(DirectedPowerBounds.shift m p).comp (C m*X) := by
  unfold WholeIntervalPolynomial.centered WholeIntervalPolynomial.affine DirectedPowerBounds.shift
  rw [comp_assoc,add_comp,C_comp,X_comp,show (0+2*m)/2=m by ring,show (2*m-0)/2=m by ring]

/-! ### The Chebyshev bounds by one pass over the list -/

/-- `∑ j<D, |l_j|`, by one pass over `l`. -/
private def r66_asumTo : ℕ → List ℤ → ℤ
  | 0,_ => 0
  | _+1,[] => 0
  | D+1,a :: l => |a|+r66_asumTo D l

private theorem r66_asumTo_eq : ∀ (D : ℕ) (l : List ℤ),
    (∑ j : Fin D,|l.getD j.val 0|)=r66_asumTo D l
  | 0,l => by simp [r66_asumTo]
  | D+1,[] => by simp [r66_asumTo]
  | D+1,a :: l => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,List.getD_cons_zero,Fin.val_succ,List.getD_cons_succ,r66_asumTo,
      r66_asumTo_eq D l]

private theorem r66_tail_getD (L : List ℤ) (j : ℕ) : L.getD (j+1) 0=L.tail.getD j 0 := by
  cases L <;> simp

private theorem r66_lowerZ_eq (D : ℕ) (L : List ℤ) :
    lowerZ D (fun j => L.getD j 0)=L.getD 0 0-r66_asumTo D L.tail := by
  simp only [WholeIntervalPolynomial.Certificate.lowerZ,r66_tail_getD,r66_asumTo_eq]

private theorem r66_upperZ_eq (D : ℕ) (L : List ℤ) :
    upperZ D (fun j => L.getD j 0)=L.getD 0 0+r66_asumTo D L.tail := by
  simp only [WholeIntervalPolynomial.Certificate.upperZ,r66_tail_getD,r66_asumTo_eq]

/-! ### The low row: one Chebyshev derivative bound -/

private def r66_lowC (e : Endpoint) : Scaled := (r66_red (r66_derivS (r66_N .low e))).kcenter 3 40 1 1
private theorem r66_lowC_rep (e : Endpoint) : (r66_lowC e).Rep
    (WholeIntervalPolynomial.centered 0 (3/20) (numerator .low e).derivative) :=
  (r66_rep_red (r66_rep_deriv (r66_N_rep .low e))).kcentered 3 40 1 1 (by norm_num) (by norm_num)
    (by norm_num)
private def r66_lowE (e : Endpoint) : Scaled := (r66_N .low e).kcenter 3 20 1 0
private theorem r66_lowE_rep (e : Endpoint) : (r66_lowE e).Rep
    (WholeIntervalPolynomial.centered (3/20) (3/20) (numerator .low e)) :=
  (r66_N_rep .low e).kcentered 3 20 1 0 (by norm_num) (by norm_num) (by norm_num)

private theorem r66_low_facts_V :
    (r66_lowC .V).s≠0 ∧ (r66_lowC .V).l.length≤degree .low .V-1+1 ∧
    2*((chebList (r66_lowC .V).l).getD 0 0+
        r66_asumTo (degree .low .V-1) (chebList (r66_lowC .V).l).tail)*200<
      -67*(((r66_lowC .V).s:ℤ)*2^(r66_lowC .V).l.length) ∧
    (r66_lowE .V).s≠0 ∧ 37*((r66_lowE .V).s:ℤ)<(r66_lowE .V).l.getD 0 0*12500 := by
  decide +kernel

private theorem r66_low_facts_F :
    (r66_lowC .F).s≠0 ∧ (r66_lowC .F).l.length≤degree .low .F-1+1 ∧
    2*((chebList (r66_lowC .F).l).getD 0 0+
        r66_asumTo (degree .low .F-1) (chebList (r66_lowC .F).l).tail)*1000<
      -317*(((r66_lowC .F).s:ℤ)*2^(r66_lowC .F).l.length) ∧
    (r66_lowE .F).s≠0 ∧ 241*((r66_lowE .F).s:ℤ)<(r66_lowE .F).l.getD 0 0*50000 := by
  decide +kernel

theorem low_certificate (e : Endpoint) :
    WholeIntervalPolynomial.centered 0 (3/20) (numerator .low e).derivative=
      WholeIntervalPolynomial.expansion (degree .low e-1)
        (WholeIntervalPolynomial.centered 0 (3/20) (numerator .low e).derivative) ∧
    WholeIntervalPolynomial.upperOn (degree .low e-1) 0 (3/20) (numerator .low e).derivative<lowSlope e ∧
    lowValue e<(numerator .low e).eval (3/20) := by
  cases e
  · obtain ⟨hs,hl,hu,hEs,hE⟩ := r66_low_facts_V
    have hC := r66_lowC_rep .V
    refine ⟨hC.eq_expansion hs hl,?_,?_⟩
    · rw [WholeIntervalPolynomial.Certificate.upperOn_eq_of_rep hC hs hl,r66_upperZ_eq,
        show lowSlope .V=((-67:ℤ):ℚ)/((200:ℕ):ℚ) by norm_num [lowSlope]]
      exact r66_upper_lt hs (by norm_num) hu
    · rw [r66_eval_eq (r66_lowE_rep .V) hEs,
        show lowValue .V=((37:ℤ):ℚ)/((12500:ℕ):ℚ) by norm_num [lowValue]]
      exact r66_lt_frac hEs (by norm_num) hE
  · obtain ⟨hs,hl,hu,hEs,hE⟩ := r66_low_facts_F
    have hC := r66_lowC_rep .F
    refine ⟨hC.eq_expansion hs hl,?_,?_⟩
    · rw [WholeIntervalPolynomial.Certificate.upperOn_eq_of_rep hC hs hl,r66_upperZ_eq,
        show lowSlope .F=((-317:ℤ):ℚ)/((1000:ℕ):ℚ) by norm_num [lowSlope]]
      exact r66_upper_lt hs (by norm_num) hu
    · rw [r66_eval_eq (r66_lowE_rep .F) hEs,
        show lowValue .F=((241:ℤ):ℚ)/((50000:ℕ):ℚ) by norm_num [lowValue]]
      exact r66_lt_frac hEs (by norm_num) hE

theorem low_antitone (e : Endpoint) :
    AntitoneOn (fun z : ℝ => aeval z (numerator .low e)) (Icc (0:ℝ) (3/20)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun z _ => (CenteredMonomialBounds.aeval_hasDerivAt (numerator .low e) z).continuousAt.continuousWithinAt)
    (fun z _ => CenteredMonomialBounds.aeval_hasDerivAt (numerator .low e) z)
  intro z hz
  have hz' : z∈Icc ((0:ℚ):ℝ) ((3/20:ℚ):ℝ) := by
    push_cast
    exact Ioo_subset_Icc_self hz
  have hb := (WholeIntervalPolynomial.interval_bounds
    (by norm_num : (0:ℚ)<3/20) (low_certificate e).1 hz').2
  have hr : (WholeIntervalPolynomial.upperOn (degree .low e-1) 0 (3/20)
      (numerator .low e).derivative:ℝ)<(lowSlope e:ℝ) := by
    exact_mod_cast (low_certificate e).2.1
  have hs : (lowSlope e:ℝ)<0 := by cases e <;> norm_num [lowSlope]
  linarith

theorem low_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (0:ℝ) (3/20)) :
    (lowValue e:ℝ)<aeval z (numerator .low e) := by
  have hm := low_antitone e hz (show (3/20:ℝ)∈Icc (0:ℝ) (3/20) by norm_num) hz.2
  have hr : (lowValue e:ℝ)<aeval (3/20:ℝ) (numerator .low e) := by
    have hh : (lowValue e:ℝ)<(((numerator .low e).eval (3/20):ℚ):ℝ) := by
      exact_mod_cast (low_certificate e).2.2
    rw [show (3/20:ℝ)=((3/20:ℚ):ℝ) by norm_num,r66_eval_rat]
    exact hh
  exact hr.trans_le hm

/-! ### The middle row: the centered quadratic reserve -/

private def r66_midS (e : Endpoint) : Scaled :=
  r66_red (r66_rescale (r66_red ((r66_N .middle e).kcenter 47 200 1 1)) 200 47)
private theorem r66_midS_rep (e : Endpoint) : (r66_midS e).Rep (middleShift e) := by
  have h := (r66_N_rep .middle e).kcentered 47 200 1 1 (a:=0) (b:=2*(47/200))
    (by norm_num) (by norm_num) (by norm_num)
  rw [r66_centered_comp,show (47/200:ℚ)=((47:ℕ):ℚ)/((200:ℕ):ℚ) by norm_num] at h
  exact r66_rep_red (r66_rep_rescale (by norm_num) (by norm_num) (r66_rep_red h))

private theorem r66_mid_facts_V :
    (r66_midS .V).s≠0 ∧ (r66_midS .V).l.length≤degree .middle .V-2+2+1 ∧
    1829*((r66_midS .V).s:ℤ)<(r66_midS .V).l.getD 0 0*2500000 ∧
    |(r66_midS .V).l.getD 1 0| * 1000000<10111*((r66_midS .V).s:ℤ) ∧
    798*(((r66_midS .V).s:ℤ)*((200^(degree .middle .V-2):ℕ):ℤ))<
      ((r66_midS .V).l.getD 2 0*((200^(degree .middle .V-2):ℕ):ℤ)-
        r66_Z (fun j => (r66_midS .V).l.getD (j+3) 0) 17 200 (degree .middle .V-2))*625 := by
  decide +kernel

private theorem r66_mid_facts_F :
    (r66_midS .F).s≠0 ∧ (r66_midS .F).l.length≤degree .middle .F-2+2+1 ∧
    1991*((r66_midS .F).s:ℤ)<(r66_midS .F).l.getD 0 0*2500000 ∧
    |(r66_midS .F).l.getD 1 0| * 1000000<10731*((r66_midS .F).s:ℤ) ∧
    3561*(((r66_midS .F).s:ℤ)*((200^(degree .middle .F-2):ℕ):ℤ))<
      ((r66_midS .F).l.getD 2 0*((200^(degree .middle .F-2):ℕ):ℤ)-
        r66_Z (fun j => (r66_midS .F).l.getD (j+3) 0) 17 200 (degree .middle .F-2))*2500 := by
  decide +kernel

private theorem r66_middle_of_facts (e : Endpoint) {n0 n1 n2 : ℤ} {d0 d1 d2 : ℕ}
    (hd0 : 0<d0) (hd1 : 0<d1) (hd2 : 0<d2)
    (hv : middleValue e=(n0:ℚ)/d0) (hl : middleLinear e=(n1:ℚ)/d1)
    (hq : middleQuadratic e=(n2:ℚ)/d2)
    (h : (r66_midS e).s≠0 ∧ (r66_midS e).l.length≤degree .middle e-2+2+1 ∧
      n0*((r66_midS e).s:ℤ)<(r66_midS e).l.getD 0 0*d0 ∧
      |(r66_midS e).l.getD 1 0| * d1<n1*((r66_midS e).s:ℤ) ∧
      n2*(((r66_midS e).s:ℤ)*((200^(degree .middle e-2):ℕ):ℤ))<
        ((r66_midS e).l.getD 2 0*((200^(degree .middle e-2):ℕ):ℤ)-
          r66_Z (fun j => (r66_midS e).l.getD (j+3) 0) 17 200 (degree .middle e-2))*d2) :
    middleShift e=C ((middleShift e).coeff 0)+C ((middleShift e).coeff 1)*X+
      C ((middleShift e).coeff 2)*X^2+tail (middleShift e) 3 (degree .middle e-2) ∧
    middleValue e<(middleShift e).coeff 0 ∧
    |(middleShift e).coeff 1|< middleLinear e ∧
    middleQuadratic e<(middleShift e).coeff 2-
      PowerTailBounds.norm (middleShift e) 3 (degree .middle e-2) (17/200) := by
  obtain ⟨hs,hlen,h0,h1,h2⟩ := h
  have hM := r66_midS_rep e
  have hdeg := (hM.natDegree_le hs).trans (by omega : (r66_midS e).l.length-1≤degree .middle e-2+2)
  refine ⟨r66_expand3 _ _ hdeg,?_,?_,?_⟩
  · rw [hM.coeff hs,hv]
    exact r66_lt_frac hs hd0 h0
  · rw [hM.coeff hs,hl]
    exact r66_abs_lt_frac hs hd1 h1
  · rw [hM.coeff hs,hq,show (17/200:ℚ)=((17:ℕ):ℚ)/((200:ℕ):ℚ) by norm_num,
      r66_norm_eq hM hs 3 _ 17 200 (by norm_num)]
    have := r66_quad_frac (B:=200^(degree .middle e-2)) hs hd2 (by positivity) h2
    push_cast at this ⊢
    exact this

theorem middle_certificate (e : Endpoint) :
    middleShift e=C ((middleShift e).coeff 0)+C ((middleShift e).coeff 1)*X+
      C ((middleShift e).coeff 2)*X^2+tail (middleShift e) 3 (degree .middle e-2) ∧
    middleValue e<(middleShift e).coeff 0 ∧
    |(middleShift e).coeff 1|< middleLinear e ∧
    middleQuadratic e<(middleShift e).coeff 2-
      PowerTailBounds.norm (middleShift e) 3 (degree .middle e-2) (17/200) := by
  cases e
  · exact r66_middle_of_facts .V (n0:=1829) (d0:=2500000) (n1:=10111) (d1:=1000000)
      (n2:=798) (d2:=625) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [middleValue]) (by norm_num [middleLinear]) (by norm_num [middleQuadratic])
      r66_mid_facts_V
  · exact r66_middle_of_facts .F (n0:=1991) (d0:=2500000) (n1:=10731) (d1:=1000000)
      (n2:=3561) (d2:=2500) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [middleValue]) (by norm_num [middleLinear]) (by norm_num [middleQuadratic])
      r66_mid_facts_F

theorem middle_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (3/20:ℝ) (1/4)) :
    (middleReserve e:ℝ)<aeval z (numerator .middle e) := by
  obtain ⟨u,hu_def⟩ : ∃ u : ℝ,u=z-47/200 := ⟨_,rfl⟩
  have hu : |u|≤((17/200:ℚ):ℝ) := by
    apply abs_le.mpr
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hp := PowerTailBounds.quadratic_lower (middle_certificate e).1 (by norm_num) hu
  have h0 : (middleValue e:ℝ)<((middleShift e).coeff 0:ℝ) := by
    exact_mod_cast (middle_certificate e).2.1
  have h1 : |((middleShift e).coeff 1:ℝ)|<(middleLinear e:ℝ) := by
    exact_mod_cast (middle_certificate e).2.2.1
  have h2 : (middleQuadratic e:ℝ)<((middleShift e).coeff 2:ℝ)-
      (PowerTailBounds.norm (middleShift e) 3 (degree .middle e-2) (17/200):ℝ) := by
    exact_mod_cast (middle_certificate e).2.2.2
  have hlin : -(middleLinear e:ℝ)*|u|≤((middleShift e).coeff 1:ℝ)*u := by
    have hh := mul_le_mul_of_nonneg_right h1.le (abs_nonneg u)
    rw [←abs_mul] at hh
    linarith [(abs_le.mp (show |((middleShift e).coeff 1:ℝ)*u|≤(middleLinear e:ℝ)*|u| from hh)).1]
  have hquad := mul_le_mul_of_nonneg_right h2.le (sq_nonneg u)
  have hm := ChebyshevLeadingBounds.quadratic_min (a:=(middleValue e:ℝ))
    (b:=-(middleLinear e:ℝ)) (x:=|u|)
    (show 0<(middleQuadratic e:ℝ) by cases e <;> norm_num [middleQuadratic])
  have hr : (middleReserve e:ℝ)<(middleValue e:ℝ)-
      (middleLinear e:ℝ)^2/(4*(middleQuadratic e:ℝ)) := by
    cases e <;> norm_num [middleReserve,middleValue,middleLinear,middleQuadratic]
  have hid : aeval u (middleShift e)=aeval z (numerator .middle e) := by
    rw [middleShift,DirectedPowerBounds.shift_eval,hu_def,
      show ((47/200:ℚ):ℝ)+(z-47/200)=z by push_cast; ring]
  rw [hid] at hp
  rw [sq_abs,neg_sq] at hm
  have hlin' : -(middleLinear e:ℝ)*|u|≤((middleShift e).coeff 1:ℝ)*u := hlin
  linarith

/-! ### The high row: the positive quotient at the transition -/

private def r66_hiS (e : Endpoint) : Scaled :=
  r66_red (r66_rescale (r66_red ((r66_N .high e).kcenter 1 4 1 1)) 4 1)
private theorem r66_hiS_rep (e : Endpoint) : (r66_hiS e).Rep (highShift e) := by
  have h := (r66_N_rep .high e).kcentered 1 4 1 1 (a:=0) (b:=2*(1/4))
    (by norm_num) (by norm_num) (by norm_num)
  rw [r66_centered_comp,show (1/4:ℚ)=((1:ℕ):ℚ)/((4:ℕ):ℚ) by norm_num] at h
  exact r66_rep_red (r66_rep_rescale (by norm_num) (by norm_num) (r66_rep_red h))
private def r66_hiQ (e : Endpoint) : Scaled := (r66_hiS e).divX.kcenter 9 40 1 1

private theorem r66_high_facts_V :
    (r66_hiS .V).s≠0 ∧ (r66_hiS .V).l.length≤degree .high .V+1 ∧
    (r66_hiQ .V).s≠0 ∧ (r66_hiQ .V).l.length≤degree .high .V-1+1 ∧
    207*(((r66_hiQ .V).s:ℤ)*2^(r66_hiQ .V).l.length)<
      2*((chebList (r66_hiQ .V).l).getD 0 0-
          r66_asumTo (degree .high .V-1) (chebList (r66_hiQ .V).l).tail)*10000 ∧
    6209*((r66_hiS .V).s:ℤ)<(r66_hiS .V).l.getD 0 0*5000000 := by
  decide +kernel

private theorem r66_high_facts_F :
    (r66_hiS .F).s≠0 ∧ (r66_hiS .F).l.length≤degree .high .F+1 ∧
    (r66_hiQ .F).s≠0 ∧ (r66_hiQ .F).l.length≤degree .high .F-1+1 ∧
    79*(((r66_hiQ .F).s:ℤ)*2^(r66_hiQ .F).l.length)<
      2*((chebList (r66_hiQ .F).l).getD 0 0-
          r66_asumTo (degree .high .F-1) (chebList (r66_hiQ .F).l).tail)*5000 ∧
    13591*((r66_hiS .F).s:ℤ)<(r66_hiS .F).l.getD 0 0*10000000 := by
  decide +kernel

private theorem r66_high_of_facts (e : Endpoint) {n0 n1 : ℤ} {d0 d1 : ℕ}
    (hd0 : 0<d0) (hd1 : 0<d1)
    (hv : highValue e=(n0:ℚ)/d0) (hl : highSlope e=(n1:ℚ)/d1)
    (h : (r66_hiS e).s≠0 ∧ (r66_hiS e).l.length≤degree .high e+1 ∧
      (r66_hiQ e).s≠0 ∧ (r66_hiQ e).l.length≤degree .high e-1+1 ∧
      n1*(((r66_hiQ e).s:ℤ)*2^(r66_hiQ e).l.length)<
        2*((chebList (r66_hiQ e).l).getD 0 0-
            r66_asumTo (degree .high e-1) (chebList (r66_hiQ e).l).tail)*d1 ∧
      n0*((r66_hiS e).s:ℤ)<(r66_hiS e).l.getD 0 0*d0) :
    highShift e=C ((highShift e).coeff 0)+X*highQuotient e ∧
    WholeIntervalPolynomial.centered 0 (9/20) (highQuotient e)=
      WholeIntervalPolynomial.expansion (degree .high e-1)
        (WholeIntervalPolynomial.centered 0 (9/20) (highQuotient e)) ∧
    highSlope e<WholeIntervalPolynomial.lowerOn (degree .high e-1) 0 (9/20) (highQuotient e) ∧
    highValue e<(numerator .high e).eval (1/4) := by
  obtain ⟨hs,hlen,hqs,hqlen,hlow,hval⟩ := h
  have hH := r66_hiS_rep e
  have hdeg := (hH.natDegree_le hs).trans (by omega : (r66_hiS e).l.length-1≤degree .high e)
  have hquot : highQuotient e=divX (highShift e) := r66_quot _ _ hdeg
  have hQ : (r66_hiQ e).Rep (WholeIntervalPolynomial.centered 0 (9/20) (highQuotient e)) := by
    rw [hquot]
    exact hH.divX.kcentered 9 40 1 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_,hQ.eq_expansion hqs hqlen,?_,?_⟩
  · rw [hquot,add_comm]
    exact (X_mul_divX_add _).symm
  · rw [WholeIntervalPolynomial.Certificate.lowerOn_eq_of_rep hQ hqs hqlen,hl,r66_lowerZ_eq]
    exact r66_lower_gt hqs hd1 hlow
  · have he : (numerator .high e).eval (1/4)=(highShift e).coeff 0 := by
      rw [coeff_zero_eq_eval_zero,highShift,DirectedPowerBounds.shift,eval_comp]
      simp
    rw [he,hH.coeff hs,hv]
    exact r66_lt_frac hs hd0 hval

theorem high_certificate (e : Endpoint) :
    highShift e=C ((highShift e).coeff 0)+X*highQuotient e ∧
    WholeIntervalPolynomial.centered 0 (9/20) (highQuotient e)=
      WholeIntervalPolynomial.expansion (degree .high e-1)
        (WholeIntervalPolynomial.centered 0 (9/20) (highQuotient e)) ∧
    highSlope e<WholeIntervalPolynomial.lowerOn (degree .high e-1) 0 (9/20) (highQuotient e) ∧
    highValue e<(numerator .high e).eval (1/4) := by
  cases e
  · exact r66_high_of_facts .V (n0:=6209) (d0:=5000000) (n1:=207) (d1:=10000)
      (by norm_num) (by norm_num) (by norm_num [highValue]) (by norm_num [highSlope])
      r66_high_facts_V
  · exact r66_high_of_facts .F (n0:=13591) (d0:=10000000) (n1:=79) (d1:=5000)
      (by norm_num) (by norm_num) (by norm_num [highValue]) (by norm_num [highSlope])
      r66_high_facts_F

theorem high_positive (e : Endpoint) {z : ℝ} (hz : z∈Icc (1/4:ℝ) (7/10)) :
    (highValue e:ℝ)<aeval z (numerator .high e) := by
  have hu : z-1/4∈Icc ((0:ℚ):ℝ) ((9/20:ℚ):ℝ) := by
    push_cast
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hq := WholeIntervalPolynomial.positive_on_interval
    (by norm_num : (0:ℚ)<9/20) (high_certificate e).2.1 (high_certificate e).2.2.1 hu
  have hq0 : 0≤aeval (z-1/4) (highQuotient e) := by
    have hs : (0:ℝ)<(highSlope e:ℝ) := by cases e <;> norm_num [highSlope]
    linarith
  have hp := mul_nonneg (show (0:ℝ)≤z-1/4 by linarith [hz.1]) hq0
  have hi := congrArg (fun p : ℚ[X] => aeval (z-1/4) p) (high_certificate e).1
  simp only [map_add,map_mul,aeval_C,aeval_X,eq_ratCast] at hi
  have hbase : (highValue e:ℝ)<((highShift e).coeff 0:ℝ) := by
    have hh : (highValue e:ℝ)<(((numerator .high e).eval (1/4):ℚ):ℝ) := by
      exact_mod_cast (high_certificate e).2.2.2
    have he : (numerator .high e).eval (1/4)=(highShift e).coeff 0 := by
      rw [coeff_zero_eq_eval_zero,highShift,DirectedPowerBounds.shift,eval_comp]
      simp
    rwa [he] at hh
  have hz' : aeval (z-1/4) (highShift e)=aeval z (numerator .high e) := by
    rw [highShift,DirectedPowerBounds.shift_eval,
      show ((1/4:ℚ):ℝ)+(z-1/4)=z by push_cast; ring]
  rw [hz'] at hi
  linarith

theorem numerator_positive (r : Row) (e : Endpoint) {z : ℝ}
    (hz : z∈Icc (left r:ℝ) (right r:ℝ)) : (7/10000:ℝ)<aeval z (numerator r e) := by
  cases r
  · have hz' : z∈Icc (0:ℝ) (3/20) := by simpa [left,right] using hz
    have hh := low_positive e hz'
    cases e <;> norm_num [lowValue] at hh ⊢ <;> linarith
  · have hz' : z∈Icc (3/20:ℝ) (1/4) := by simpa [left,right] using hz
    have hh := middle_positive e hz'
    cases e <;> norm_num [middleReserve] at hh ⊢ <;> linarith
  · have hz' : z∈Icc (1/4:ℝ) (7/10) := by simpa [left,right] using hz
    have hh := high_positive e hz'
    cases e <;> norm_num [highValue] at hh ⊢ <;> linarith

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Certificate
