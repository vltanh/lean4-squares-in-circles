module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2CommonBounds

/-!
# The degree-150 certificate at actual sine and cosine

Uncompiled whole-interval Taylor transfer for (22)--(25). The sine
part has degree ten in its sine input. Its exact coefficient norm,
together with a cubic power-difference bound for cosine, gives an
error smaller than the prescribed 10^-8 allowance.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary Polynomial HighOrderTaylor BoundedRadicalPerturbation

namespace Certificate
def Y : ℚ[X] := -C (13/6)*X-1-X^2+C (6323/6250)*b pHigh*
  (l2.comp (C (pHigh/(1+pHigh))*X^2))
def yNorm : ℚ := ∑i:Fin 11,|Y.coeff i.val| *i.val*2^i.val

open WholeIntervalPolynomial.Certificate (Scaled)

/-! The degree-ten polynomial `Y` as a scaled integer list (kernel-checked). -/

private def r67_q : Scaled := (Scaled.const (pHigh/(1+pHigh))).mul (Scaled.var.pow 2)
private def r67_Y : Scaled :=
  (((((Scaled.const (13/6)).neg.mul Scaled.var).sub (Scaled.ofNat 1)).sub (Scaled.var.pow 2)).add
    (((Scaled.const (6323/6250)).mul
      (((Scaled.const (1+pHigh)).mul ((Scaled.ofNat 1).add (Scaled.var.pow 2))).sub
        ((Scaled.const (2*pHigh)).mul (Scaled.var.pow 4)))).mul
      ((((Scaled.ofNat 1).add ((Scaled.const (3/2)).mul r67_q)).add
        ((Scaled.const (15/8)).mul (r67_q.pow 2))).add ((Scaled.const (35/16)).mul (r67_q.pow 3)))))

private theorem r67_Y_rep : r67_Y.Rep Y := by
  have hq : r67_q.Rep (C (pHigh/(1+pHigh))*X^2) :=
    (Scaled.rep_const _).mul (Scaled.rep_var.pow 2)
  have hl : l2.comp (C (pHigh/(1+pHigh))*X^2)=1+C (3/2)*(C (pHigh/(1+pHigh))*X^2)+
      C (15/8)*(C (pHigh/(1+pHigh))*X^2)^2+C (35/16)*(C (pHigh/(1+pHigh))*X^2)^3 := by
    simp only [l2,add_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]
  rw [Y,b,hl]
  exact ((((Scaled.rep_const _).neg.mul Scaled.rep_var).sub Scaled.rep_one).sub
    (Scaled.rep_var.pow 2)).add
    (((Scaled.rep_const _).mul
      (((Scaled.rep_const _).mul (Scaled.rep_one.add (Scaled.rep_var.pow 2))).sub
        ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4)))).mul
      (((Scaled.rep_one.add ((Scaled.rep_const _).mul hq)).add
        ((Scaled.rep_const _).mul (hq.pow 2))).add ((Scaled.rep_const _).mul (hq.pow 3))))

private theorem r67_Y_facts : r67_Y.s≠0 ∧ r67_Y.l.length≤11 ∧
    (∑i:Fin 11,|r67_Y.l.getD i.val 0| *(i.val:ℤ)*2^i.val)<1000000*(r67_Y.s:ℤ) := by
  decide +kernel

theorem Y_identity : Y=∑i:Fin 11,C (Y.coeff i.val)*X^i.val := by
  obtain ⟨hs,hl,-⟩ := r67_Y_facts
  have hd : Y.natDegree<11 := lt_of_le_of_lt (r67_Y_rep.natDegree_le hs) (by omega)
  conv_lhs => rw [Y.as_sum_range_C_mul_X_pow' hd]
  exact (Fin.sum_univ_eq_sum_range (fun i => C (Y.coeff i)*X^i) 11).symm

theorem Y_norm_bound : yNorm<(1000000:ℚ) := by
  obtain ⟨hs,-,ht⟩ := r67_Y_facts
  have hs' : (0:ℚ)<r67_Y.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have he : yNorm=((∑i:Fin 11,|r67_Y.l.getD i.val 0| *(i.val:ℤ)*2^i.val:ℤ):ℚ)/r67_Y.s := by
    unfold yNorm
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [r67_Y_rep.coeff hs,abs_div,abs_of_pos hs']
    ring
  rw [he,div_lt_iff₀ hs']
  exact_mod_cast ht
end Certificate

def jNative (x y c : ℝ) : ℝ := E2 x*c^3+aeval y Certificate.Y

theorem jNative_formula (x y c : ℝ) :
    jNative x y c=E2 x*c^3-2*K*y-1-y^2+
      (6323/6250)*shapeB (751/1000) y*L2 ((564001/1564001)*y^2) := by
  simp [jNative,Certificate.Y,Certificate.b,Certificate.l2,Certificate.pHigh,shapeB,L2,K]
  ring

theorem polynomial_J_identity (x : ℝ) :
    aeval x Certificate.J=jNative x (S15 x) (C16 x) := by
  simp [Certificate.J,jNative,Certificate.Y,Certificate.e2,Certificate.b,Certificate.l2,
    PositiveScalarPolynomials.sine_eval,PositiveScalarPolynomials.cosine_eval,E2]
  ring

theorem E2_abs {x : ℝ} (hx : x∈Icc 0 frameCap) : |E2 x|≤1 := by
  let u := x-7/20
  have hu : |u|≤(7/20:ℝ) := by
    apply abs_le.mpr
    dsimp [u]
    exact ⟨by linarith [hx.1],by norm_num [frameCap] at hx; linarith [hx.2]⟩
  have hu2 : u^2≤(7/20:ℝ)^2 := by nlinarith [(abs_le.mp hu).1,(abs_le.mp hu).2]
  have hu3 : |u^3|≤(7/20:ℝ)^3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg u) hu 3
  apply abs_le.mpr
  change -1≤-1/250+(33/25)*u-(1/10)*u^2+(19/10)*u^3 ∧
    -1/250+(33/25)*u-(1/10)*u^2+(19/10)*u^3≤1
  constructor <;> nlinarith [(abs_le.mp hu).1,(abs_le.mp hu).2,
    (abs_le.mp hu3).1,(abs_le.mp hu3).2,sq_nonneg u]

theorem power_error {u v ε : ℝ} (hu : |u|≤2) (hv : |v|≤2)
    (hε : 0≤ε) (hd : |u-v|≤ε) (n : ℕ) :
    |u^n-v^n|≤(n:ℝ)*2^n*ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hvp : |v^n|≤(2:ℝ)^n := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg v) hv n
    have hh := product_difference hu hvp hd ih
    have hpow : 0≤(2:ℝ)^n := by positivity
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    simp only [pow_succ,Nat.cast_add,Nat.cast_one] at ⊢
    rw [mul_comm (u^n) u,mul_comm (v^n) v]
    nlinarith [mul_nonneg hpow hε]

theorem Y_error {y t ε : ℝ} (hy : |y|≤2) (ht : |t|≤2)
    (hε : 0≤ε) (hd : |y-t|≤ε) :
    |aeval y Certificate.Y-aeval t Certificate.Y|≤1000000*ε := by
  have hterm (i : Fin 11) :
      |(Certificate.Y.coeff i.val:ℝ)*y^i.val-(Certificate.Y.coeff i.val:ℝ)*t^i.val|≤
        |(Certificate.Y.coeff i.val:ℝ)| *i.val*2^i.val*ε := by
    have hh := constant_product_difference (le_refl |(Certificate.Y.coeff i.val:ℝ)|)
      (power_error hy ht hε hd i.val)
    simpa only [mul_assoc] using hh
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hterm i)
  have hi := Certificate.Y_identity
  have hid (v : ℝ) : aeval v Certificate.Y=∑i:Fin 11,(Certificate.Y.coeff i.val:ℝ)*v^i.val := by
    conv_lhs => rw [hi]
    simp only [map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  rw [hid,hid,←Finset.sum_sub_distrib]
  have hsum := Finset.abs_sum_le_sum_abs (s:=Finset.univ)
    (f:=fun i:Fin 11 => (Certificate.Y.coeff i.val:ℝ)*y^i.val-(Certificate.Y.coeff i.val:ℝ)*t^i.val)
  have hnorm : (Certificate.yNorm:ℝ)<1000000 := by exact_mod_cast Certificate.Y_norm_bound
  have hnorm' : (∑i:Fin 11,|(Certificate.Y.coeff i.val:ℝ)| *i.val*2^i.val)≤1000000 := by
    have he : (Certificate.yNorm:ℝ)=∑i:Fin 11,|(Certificate.Y.coeff i.val:ℝ)| *i.val*2^i.val := by
      simp [Certificate.yNorm]
    rw [← he]
    exact hnorm.le
  have hm := mul_le_mul_of_nonneg_right hnorm' hε
  rw [Finset.sum_mul] at hm
  linarith

theorem J_error {x : ℝ} (hx : x∈Icc 0 frameCap) :
    |jNative x (Real.sin x) (Real.cos x)-aeval x Certificate.J|<(1/100000000:ℝ) := by
  have hb := Analytic.input_bounds hx
  have he := Analytic.input_errors hx
  have habs {v : ℝ} (h : v∈Icc (0:ℝ) 2) : |v|≤2 := by rw [abs_of_nonneg h.1]; exact h.2
  have hsin := habs (v:=Real.sin x) ⟨hb.1.1,by linarith [hb.1.2]⟩
  have hS := habs (v:=S15 x) ⟨hb.2.2.1.1,by linarith [hb.2.2.1.2]⟩
  have hcos := habs (v:=Real.cos x) ⟨by linarith [hb.2.1.1],by linarith [hb.2.1.2]⟩
  have hC := habs (v:=C16 x) ⟨by linarith [hb.2.2.2.1],by linarith [hb.2.2.2.2]⟩
  have hY := Y_error hsin hS (show 0≤remainder by norm_num [remainder]) he.1
  have hp := power_error hcos hC (show 0≤remainder by norm_num [remainder]) he.2 3
  have hE := constant_product_difference (E2_abs hx) hp
  have hid : jNative x (Real.sin x) (Real.cos x)-jNative x (S15 x) (C16 x)=
      (E2 x*Real.cos x^3-E2 x*C16 x^3)+
      (aeval (Real.sin x) Certificate.Y-aeval (S15 x) Certificate.Y) := by dsimp [jNative]; ring
  rw [polynomial_J_identity,hid]
  have hh := abs_add_le (E2 x*Real.cos x^3-E2 x*C16 x^3)
    (aeval (Real.sin x) Certificate.Y-aeval (S15 x) Certificate.Y)
  norm_num [remainder] at hY hE
  linarith

theorem actual_J_positive {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0<jNative x (Real.sin x) (Real.cos x) := by
  have hp := Certificate.J_positive hx
  have he := J_error hx
  have hh := (abs_lt.mp he).1
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
