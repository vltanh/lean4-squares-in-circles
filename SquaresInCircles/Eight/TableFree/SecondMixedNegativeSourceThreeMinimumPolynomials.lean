module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreeMinimumCalculus
public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Whole-height polynomial signs for the negative-core minimum

The degree-eight denominator difference has one coefficient-norm bound
on [1.68,1.915]. The first stationary numerator uses its exact endpoint
quotient on that same interval; the second uses [1.68,1.74]. Each input
is the displayed symbolic polynomial. No target subdivision, sampled
values, or supplied coefficient table is used. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum.Polynomials
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

def q : ℚ := 9789/2500
def t : ℚ[X] := Polynomial.C (q+1)-Polynomial.C 2*X
def w : ℚ[X] := Polynomial.C q-X^2
def b : ℚ[X] := Polynomial.C 2*X^2-Polynomial.C (4*q)*X+Polynomial.C (q*(q+1))
def bd : ℚ[X] := Polynomial.C 4*X-Polynomial.C (4*q)
def a : ℚ[X] := b*X^2*t-w*(bd*X*t-b*(Polynomial.C 3*t-Polynomial.C 4*X))
def d : ℚ[X] := X^5*t^3-a
def c (h : ℚ) : ℚ[X] :=
  let s := Polynomial.C (h^2)*t-1
  Polynomial.C (3*h^2*q)*X*t^2*s-Polynomial.C (h^4)*w*X^2*t^2-Polynomial.C (4*h^2)*w*X^2*t*s+
    Polynomial.C (3*q)*t^2*s^2-Polynomial.C (6*q)*X*t*s^2+Polynomial.C 8*w*X^2*s^2
def cg : ℚ[X] := c (98439/100000)
def endpointQuotient : ℚ[X] :=
  -∑ n∈Finset.range 6,Polynomial.C (cg.coeff (n+1))*
    ∑ i∈Finset.range (n+1),Polynomial.C ((383/200:ℚ)^(n-i))*X^i

/-! The polynomials of this file as scaled integer coefficient lists. -/

private def tS : Scaled := (Scaled.const (q+1)).sub ((Scaled.const 2).mul Scaled.var)
private def wS : Scaled := (Scaled.const q).sub (Scaled.var.pow 2)
private def bS : Scaled :=
  (((Scaled.const 2).mul (Scaled.var.pow 2)).sub ((Scaled.const (4*q)).mul Scaled.var)).add
    (Scaled.const (q*(q+1)))
private def bdS : Scaled := ((Scaled.const 4).mul Scaled.var).sub (Scaled.const (4*q))
private def aS : Scaled :=
  ((bS.mul (Scaled.var.pow 2)).mul tS).sub
    (wS.mul (((bdS.mul Scaled.var).mul tS).sub
      (bS.mul (((Scaled.const 3).mul tS).sub ((Scaled.const 4).mul Scaled.var)))))
private def dS : Scaled := ((Scaled.var.pow 5).mul (tS.pow 3)).sub aS
private def cS (h : ℚ) : Scaled :=
  let sS := ((Scaled.const (h^2)).mul tS).sub (Scaled.ofNat 1)
  ((((((((Scaled.const (3*h^2*q)).mul Scaled.var).mul (tS.pow 2)).mul sS).sub
    ((((Scaled.const (h^4)).mul wS).mul (Scaled.var.pow 2)).mul (tS.pow 2))).sub
    (((((Scaled.const (4*h^2)).mul wS).mul (Scaled.var.pow 2)).mul tS).mul sS)).add
    (((Scaled.const (3*q)).mul (tS.pow 2)).mul (sS.pow 2))).sub
    ((((Scaled.const (6*q)).mul Scaled.var).mul tS).mul (sS.pow 2))).add
    ((((Scaled.const 8).mul wS).mul (Scaled.var.pow 2)).mul (sS.pow 2))

private theorem rep_t : tS.Rep t :=
  (Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)
private theorem rep_w : wS.Rep w := (Scaled.rep_const _).sub (Scaled.rep_var.pow 2)
private theorem rep_b : bS.Rep b :=
  (((Scaled.rep_const _).mul (Scaled.rep_var.pow 2)).sub
    ((Scaled.rep_const _).mul Scaled.rep_var)).add (Scaled.rep_const _)
private theorem rep_bd : bdS.Rep bd :=
  ((Scaled.rep_const _).mul Scaled.rep_var).sub (Scaled.rep_const _)
private theorem rep_a : aS.Rep a :=
  ((rep_b.mul (Scaled.rep_var.pow 2)).mul rep_t).sub
    (rep_w.mul (((rep_bd.mul Scaled.rep_var).mul rep_t).sub
      (rep_b.mul (((Scaled.rep_const _).mul rep_t).sub ((Scaled.rep_const _).mul Scaled.rep_var)))))
private theorem rep_d : dS.Rep d := ((Scaled.rep_var.pow 5).mul (rep_t.pow 3)).sub rep_a
private theorem rep_c (h : ℚ) : (cS h).Rep (c h) := by
  have hs : (((Scaled.const (h^2)).mul tS).sub (Scaled.ofNat 1)).Rep (Polynomial.C (h^2)*t-1) :=
    ((Scaled.rep_const _).mul rep_t).sub Scaled.rep_one
  exact ((((((((Scaled.rep_const _).mul Scaled.rep_var).mul (rep_t.pow 2)).mul hs).sub
    ((((Scaled.rep_const _).mul rep_w).mul (Scaled.rep_var.pow 2)).mul (rep_t.pow 2))).sub
    (((((Scaled.rep_const _).mul rep_w).mul (Scaled.rep_var.pow 2)).mul rep_t).mul hs)).add
    (((Scaled.rep_const _).mul (rep_t.pow 2)).mul (hs.pow 2))).sub
    ((((Scaled.rep_const _).mul Scaled.rep_var).mul rep_t).mul (hs.pow 2))).add
    ((((Scaled.rep_const _).mul rep_w).mul (Scaled.rep_var.pow 2)).mul (hs.pow 2))

/-- A finite sum of represented polynomials. -/
private def sumS (f : ℕ → Scaled) : ℕ → Scaled
  | 0 => ⟨[],1⟩
  | n+1 => (sumS f n).add (f n)

private theorem rep_sum {f : ℕ → Scaled} {g : ℕ → ℚ[X]} (h : ∀ n,(f n).Rep (g n)) :
    ∀ N,(sumS f N).Rep (∑ n∈Finset.range N,g n)
  | 0 => by simpa [sumS] using Scaled.rep_zero
  | N+1 => by
    rw [Finset.sum_range_succ]
    exact (rep_sum h N).add (h N)

/-- The constant `z/s`. -/
private theorem rep_div (z : ℤ) {s : ℕ} (hs : s≠0) :
    (⟨[z],s⟩ : Scaled).Rep (Polynomial.C ((z:ℚ)/s)) := by
  have hs' : (s:ℚ)≠0 := by exact_mod_cast hs
  unfold Scaled.Rep
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  field_simp

private def eqS : Scaled :=
  (sumS (fun n => (⟨[(cS (98439/100000)).l.getD (n+1) 0],(cS (98439/100000)).s⟩ : Scaled).mul
    (sumS (fun i => (⟨[383^(n-i)],200^(n-i)⟩ : Scaled).mul (Scaled.var.pow i)) (n+1))) 6).neg

private theorem rep_cg : (cS (98439/100000)).Rep cg := rep_c _

private theorem rep_endpointQuotient : eqS.Rep endpointQuotient := by
  have hs : (cS (98439/100000)).s≠0 := by decide +kernel
  have hc := rep_cg.coeff hs
  unfold endpointQuotient eqS
  refine (rep_sum (fun n => ?_) 6).neg
  rw [hc]
  refine (rep_div _ hs).mul (rep_sum (fun i => ?_) (n+1))
  refine Scaled.Rep.mul ?_ (Scaled.rep_var.pow i)
  rw [show (383/200:ℚ)^(n-i)=(((383:ℤ)^(n-i):ℤ):ℚ)/(((200:ℕ)^(n-i):ℕ):ℚ) by
    push_cast; rw [div_pow]]
  exact rep_div _ (pow_ne_zero _ (by norm_num))

/-- Synthetic division by `X-r`. -/
private theorem quotient_general (p : ℚ[X]) (r : ℚ) (N : ℕ) (hp : p.natDegree<N+1) :
    (Polynomial.C r-X)*(-∑ n∈Finset.range N,Polynomial.C (p.coeff (n+1))*
      ∑ i∈Finset.range (n+1),Polynomial.C (r^(n-i))*X^i)=p-Polynomial.C (p.eval r) := by
  have hg : ∀ n : ℕ,(∑ i∈Finset.range (n+1),Polynomial.C (r^(n-i))*X^i)*(X-Polynomial.C r)=
      X^(n+1)-Polynomial.C r^(n+1) := by
    intro n
    rw [← geom_sum₂_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_pow,mul_comm,show n+1-1-i=n-i by omega]
  have hsum := p.as_sum_range_C_mul_X_pow' hp
  have heval := eval_eq_sum_range' hp r
  rw [Finset.sum_range_succ'] at hsum heval
  have e : (Polynomial.C r-X)*(-∑ n∈Finset.range N,Polynomial.C (p.coeff (n+1))*
      ∑ i∈Finset.range (n+1),Polynomial.C (r^(n-i))*X^i)=
      ∑ n∈Finset.range N,Polynomial.C (p.coeff (n+1))*(X^(n+1)-Polynomial.C r^(n+1)) := by
    rw [mul_neg,← neg_mul,neg_sub,Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← hg n]
    ring
  rw [e]
  have hC := congrArg Polynomial.C heval
  simp only [map_add,map_sum,map_mul,map_pow,pow_zero,mul_one] at hC hsum
  simp only [mul_sub,Finset.sum_sub_distrib]
  linear_combination -hsum+hC

lemma d_evaluation (u : ℝ) : aeval u d=D0 u := by
  simp [d,a,b,bd,t,w,q,D0,A0,baseE,baseEd,Q0]

lemma c_evaluation (h : ℚ) (u : ℝ) : aeval u (c h)=Ch (h:ℝ) u := by
  simp [c,t,w,q,Ch,Q0]

theorem d_expansion : centered (42/25) (383/200) d=
    expansion 8 (centered (42/25) (383/200) d) := by
  exact (rep_d.centered 1 400 719 47 (by norm_num) (by norm_num) (by norm_num)).eq_expansion
    (by decide +kernel) (by decide +kernel)

theorem d_reserve : (27:ℚ)<lowerOn 8 (42/25) (383/200) d := by
  rw [lowerOn_eq_of_rep (rep_d.centered 1 400 719 47 (by norm_num) (by norm_num) (by norm_num))
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem quotient_identity : (Polynomial.C (383/200)-X)*endpointQuotient=cg-Polynomial.C (cg.eval (383/200)) := by
  have hs : (cS (98439/100000)).s≠0 := by decide +kernel
  have hl : (cS (98439/100000)).l.length≤6+1 := by decide +kernel
  exact quotient_general cg (383/200) 6 (Nat.lt_succ_of_le ((rep_cg.natDegree_le hs).trans (by omega)))

theorem quotient_expansion : centered (42/25) (383/200) endpointQuotient=
    expansion 5 (centered (42/25) (383/200) endpointQuotient) := by
  exact (rep_endpointQuotient.centered 1 400 719 47 (by norm_num) (by norm_num)
    (by norm_num)).eq_expansion (by decide +kernel) (by decide +kernel)

theorem quotient_reserve : (14:ℚ)<lowerOn 5 (42/25) (383/200) endpointQuotient := by
  rw [lowerOn_eq_of_rep (rep_endpointQuotient.centered 1 400 719 47 (by norm_num) (by norm_num)
    (by norm_num)) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem endpoint_reserve : (1/20:ℚ)<cg.eval (383/200) := by
  have hq := rep_cg.centered 383 200 1 0 (a := 383/200) (b := 383/200) (by norm_num)
    (by norm_num) (by norm_num)
  have he : cg.eval (383/200)=(centered (383/200) (383/200) cg).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,centered,eval_comp]
    simp [affine]
  rw [he,hq.coeff (by decide +kernel) 0]
  decide +kernel

theorem second_expansion : centered (42/25) (87/50) (c (39/40))=
    expansion 6 (centered (42/25) (87/50) (c (39/40))) := by
  exact ((rep_c _).centered 1 100 171 3 (by norm_num) (by norm_num) (by norm_num)).eq_expansion
    (by decide +kernel) (by decide +kernel)

theorem second_reserve : (2:ℚ)<lowerOn 6 (42/25) (87/50) (c (39/40)) := by
  rw [lowerOn_eq_of_rep ((rep_c _).centered 1 100 171 3 (by norm_num) (by norm_num) (by norm_num))
    (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem D0_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (383/200)) : 0<D0 u := by
  have hu' : u∈Set.Icc ((42/25:ℚ):ℝ) ((383/200:ℚ):ℝ) := by push_cast; exact hu
  have hh := positive_on_interval (by norm_num) d_expansion d_reserve hu'
  rw [d_evaluation] at hh
  push_cast at hh
  linarith

theorem Ch_first_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (383/200)) : 0<Ch g u := by
  have hu' : u∈Set.Icc ((42/25:ℚ):ℝ) ((383/200:ℚ):ℝ) := by push_cast; exact hu
  have hq := positive_on_interval (by norm_num) quotient_expansion quotient_reserve hu'
  push_cast at hq
  have hp := mul_nonneg (show 0≤(383/200:ℝ)-u by linarith [hu.2])
    (show 0≤aeval u endpointQuotient by linarith)
  have hid := congrArg (fun p : ℚ[X] => aeval u p) quotient_identity
  simp only [map_mul,map_sub,aeval_C,aeval_X,eq_ratCast] at hid
  have he : ((1/20:ℚ):ℝ)<((cg.eval (383/200):ℚ):ℝ) := Rat.cast_lt.mpr endpoint_reserve
  have he' : ((1/20:ℚ):ℝ)=1/20 := by norm_num
  have hc : aeval u cg=Ch g u := by
    simpa [cg,g,EdgeThreeAligned.gn] using c_evaluation (98439/100000) u
  rw [hc] at hid
  linarith

theorem Ch_second_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (87/50)) : 0<Ch (39/40) u := by
  have hu' : u∈Set.Icc ((42/25:ℚ):ℝ) ((87/50:ℚ):ℝ) := by push_cast; exact hu
  have hh := positive_on_interval (by norm_num) second_expansion second_reserve hu'
  rw [c_evaluation] at hh
  norm_num at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum.Polynomials
