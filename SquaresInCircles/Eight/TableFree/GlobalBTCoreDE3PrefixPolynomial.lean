module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Polynomial
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Exact polynomials for saturated-prefix monotonicity

The two retained-circle derivative numerators use one rational
certificate each, on the entire prefix interval.  These are the
explicit HB/HW expressions, not sampled derivative evaluations.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3.SaturatedPolynomial

open Polynomial PowerTailBounds FrameCircleArc

def a (last : Bool) : ℚ := if last then 269343/250000 else 49/50
def other (last : Bool) : ℚ := if last then 49/50 else 269343/250000
def rho (last : Bool) : ℚ := if last then 574543/500000 else 616589/500000
def U : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5
def tangent (last : Bool) : ℚ[X] :=
  C ((3/5)/rho last)+C ((2/5)*(other last)^2/(rho last)^3)*X
def P (last : Bool) : ℚ[X] :=
  if last then C (3083/2500)-C (833/2500)*X-C (3167/10000)*X^2
  else C (11491/10000)-C (1541/5000)*X-C (2931/10000)*X^2
def numerator (last : Bool) : ℚ[X] :=
  C (a last)*PrefixPolynomial.c*TailPolynomial.C6+
    C ((2/5)*a last)*TailPolynomial.S7-C (2/5)*PrefixPolynomial.c
def energy (last : Bool) : ℚ[X] :=
  C ((a last)^2)+PrefixPolynomial.c^2-
    C (2*a last)*PrefixPolynomial.c*TailPolynomial.S7
def denominator (last : Bool) : ℚ[X] := energy last+(P last)^2
def affinePart (last : Bool) : ℚ[X] :=
  (if last then C (-3/5)+C (2/5)*TailPolynomial.C6-PrefixPolynomial.c*U
    else C (-1/5)-C (49/50)*U)-C ((1979/1000)*(2/5))*tangent last
def H (last : Bool) : ℚ[X] := affinePart last*denominator last+
  C (2*(989/500))*numerator last*P last
def centered (last : Bool) : ℚ[X] := DirectedPowerBounds.shift (7/20) (H last)
def degree (last : Bool) : ℕ := if last then 14 else 13

/-! ### Kernel certificates (integer lists of `PolynomialCertificates`) -/

open WholeIntervalPolynomial.Certificate (Scaled) in
private theorem r56_shift_rep {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (num den : ℕ) (s t : ℤ)
    {m : ℚ} (hden : den≠0) (hm : m=num*s/den) (h1 : (1:ℚ)=num*t/den) :
    (S.center num den s t).Rep (DirectedPowerBounds.shift m p) := by
  have hc := hp.centered num den s t (a:=m-1) (b:=m+1) hden (by rw [← hm]; ring)
    (by rw [← h1]; ring)
  rwa [WholeIntervalPolynomial.centered,WholeIntervalPolynomial.affine,
    show (m-1+(m+1))/2=m by ring,show (m+1-(m-1))/2=1 by ring,map_one,one_mul] at hc

/-- The integer numerator of `PowerTailBounds.norm` at the radius `num/den`. -/
private def r56_normZ (l : List ℤ) (start count num den : ℕ) : ℤ :=
  ∑ j : Fin count,|l.getD (j.val+start) 0| * (num:ℤ)^(j.val+1)*(den:ℤ)^(count-(j.val+1))

open WholeIntervalPolynomial.Certificate (Scaled) in
private theorem r56_coeff_sub_norm {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (k start count num den : ℕ) (hden : den≠0) :
    p.coeff k-PowerTailBounds.norm p start count ((num:ℚ)/den)=
      ((S.l.getD k 0*(den:ℤ)^count-r56_normZ S.l start count num den:ℤ):ℚ)/
        ((S.s:ℚ)*(den:ℚ)^count) := by
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
  have hn : PowerTailBounds.norm p start count ((num:ℚ)/den)=
      (r56_normZ S.l start count num den:ℚ)/((S.s:ℚ)*(den:ℚ)^count) := by
    simp only [PowerTailBounds.norm,hp.coeff hs,r56_normZ]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : j.val+1≤count := j.isLt
    rw [abs_div,abs_of_pos hs',div_pow,
      show (den:ℚ)^count=(den:ℚ)^(j.val+1)*(den:ℚ)^(count-(j.val+1)) by
        rw [← pow_add,Nat.add_sub_cancel' hj]]
    field_simp
  rw [hn,hp.coeff hs]
  push_cast
  field_simp

open WholeIntervalPolynomial.Certificate (Scaled) in
private theorem r56_reserve_pos {S : Scaled} {p : ℚ[X]} (hp : S.Rep p) (hs : S.s≠0)
    (k start count num den : ℕ) (hden : den≠0)
    (h : 0<S.l.getD k 0*(den:ℤ)^count-r56_normZ S.l start count num den) :
    0<p.coeff k-PowerTailBounds.norm p start count ((num:ℚ)/den) := by
  rw [r56_coeff_sub_norm hp hs k start count num den hden]
  have hs' : (0:ℚ)<S.s := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hd : (0:ℚ)<den := by exact_mod_cast Nat.pos_of_ne_zero hden
  exact div_pos (by exact_mod_cast h) (by positivity)

/-- A polynomial of degree at most `n` is its constant term plus its power tail. -/
private theorem r56_constant_split {p : ℚ[X]} {n : ℕ} (hp : p.natDegree≤n) :
    p=C (p.coeff 0)+PowerTailBounds.tail p 1 n := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (n:=n+1) (Nat.lt_succ_of_le hp)]
  rw [Finset.sum_range_succ',PowerTailBounds.tail,
    ← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff (i+1))*X^(i+1)) n,pow_zero,mul_one,add_comm]


open WholeIntervalPolynomial.Certificate (Scaled)

private def r56S7 : Scaled :=
  ((Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))).sub
    ((Scaled.const (1/5040)).mul (Scaled.var.pow 7))
private theorem r56S7_rep : r56S7.Rep TailPolynomial.S7 :=
  ((Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 7))
private def r56C6 : Scaled :=
  (((Scaled.ofNat 1).sub ((Scaled.const (1/2)).mul (Scaled.var.pow 2))).add
    ((Scaled.const (1/24)).mul (Scaled.var.pow 4))).sub
    ((Scaled.const (1/720)).mul (Scaled.var.pow 6))
private theorem r56C6_rep : r56C6.Rep TailPolynomial.C6 :=
  ((Scaled.rep_one.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 4))).sub
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 6))
private def r56c : Scaled := (Scaled.const (3/5)).add ((Scaled.const (2/5)).mul Scaled.var)
private theorem r56c_rep : r56c.Rep PrefixPolynomial.c :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)
private def r56U : Scaled :=
  (Scaled.var.sub ((Scaled.const (1/6)).mul (Scaled.var.pow 3))).add
    ((Scaled.const (1/120)).mul (Scaled.var.pow 5))
private theorem r56U_rep : r56U.Rep U :=
  (Scaled.rep_var.sub ((Scaled.rep_const _).mul (Scaled.rep_var.pow 3))).add
    ((Scaled.rep_const _).mul (Scaled.rep_var.pow 5))
private def r56tangent (last : Bool) : Scaled :=
  (Scaled.const ((3/5)/rho last)).add
    ((Scaled.const ((2/5)*(other last)^2/(rho last)^3)).mul Scaled.var)
private theorem r56tangent_rep (last : Bool) : (r56tangent last).Rep (tangent last) :=
  (Scaled.rep_const _).add ((Scaled.rep_const _).mul Scaled.rep_var)
private def r56P : Bool → Scaled
  | true => ((Scaled.const (3083/2500)).sub ((Scaled.const (833/2500)).mul Scaled.var)).sub
      ((Scaled.const (3167/10000)).mul (Scaled.var.pow 2))
  | false => ((Scaled.const (11491/10000)).sub ((Scaled.const (1541/5000)).mul Scaled.var)).sub
      ((Scaled.const (2931/10000)).mul (Scaled.var.pow 2))
private theorem r56P_rep : ∀ last, (r56P last).Rep (P last)
  | true => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).sub
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))
  | false => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul Scaled.rep_var)).sub
      ((Scaled.rep_const _).mul (Scaled.rep_var.pow 2))
private def r56numerator (last : Bool) : Scaled :=
  ((((Scaled.const (a last)).mul r56c).mul r56C6).add
    ((Scaled.const ((2/5)*a last)).mul r56S7)).sub ((Scaled.const (2/5)).mul r56c)
private theorem r56numerator_rep (last : Bool) : (r56numerator last).Rep (numerator last) :=
  ((((Scaled.rep_const _).mul r56c_rep).mul r56C6_rep).add
    ((Scaled.rep_const _).mul r56S7_rep)).sub ((Scaled.rep_const _).mul r56c_rep)
private def r56denominator (last : Bool) : Scaled :=
  (((Scaled.const ((a last)^2)).add (r56c.pow 2)).sub
    (((Scaled.const (2*a last)).mul r56c).mul r56S7)).add ((r56P last).pow 2)
private theorem r56denominator_rep (last : Bool) :
    (r56denominator last).Rep (denominator last) :=
  (((Scaled.rep_const _).add (r56c_rep.pow 2)).sub
    (((Scaled.rep_const _).mul r56c_rep).mul r56S7_rep)).add ((r56P_rep last).pow 2)
private def r56affine : Bool → Scaled
  | true => (((Scaled.const (-3/5)).add ((Scaled.const (2/5)).mul r56C6)).sub (r56c.mul r56U)).sub
      ((Scaled.const ((1979/1000)*(2/5))).mul (r56tangent true))
  | false => ((Scaled.const (-1/5)).sub ((Scaled.const (49/50)).mul r56U)).sub
      ((Scaled.const ((1979/1000)*(2/5))).mul (r56tangent false))
private theorem r56affine_rep : ∀ last, (r56affine last).Rep (affinePart last)
  | true => (((Scaled.rep_const _).add ((Scaled.rep_const _).mul r56C6_rep)).sub
      (r56c_rep.mul r56U_rep)).sub ((Scaled.rep_const _).mul (r56tangent_rep true))
  | false => ((Scaled.rep_const _).sub ((Scaled.rep_const _).mul r56U_rep)).sub
      ((Scaled.rep_const _).mul (r56tangent_rep false))
private def r56H (last : Bool) : Scaled :=
  ((r56affine last).mul (r56denominator last)).add
    (((Scaled.const (2*(989/500))).mul (r56numerator last)).mul (r56P last))
private theorem r56H_rep (last : Bool) : (r56H last).Rep (H last) :=
  ((r56affine_rep last).mul (r56denominator_rep last)).add
    (((Scaled.rep_const _).mul (r56numerator_rep last)).mul (r56P_rep last))
private def r56cen (last : Bool) : Scaled := (r56H last).center 1 20 7 20
private theorem r56cen_rep (last : Bool) : (r56cen last).Rep (centered last) :=
  r56_shift_rep (r56H_rep last) 1 20 7 20 (by norm_num) (by norm_num) (by norm_num)

theorem centered_identity (last : Bool) : centered last=C ((centered last).coeff 0)+
    tail (centered last) 1 (degree last) := by
  cases last <;>
    exact r56_constant_split (((r56cen_rep _).natDegree_le (by decide +kernel)).trans
      (by decide +kernel))

theorem centered_reserve (last : Bool) :
    0<(centered last).coeff 0-norm (centered last) 1 (degree last) (7/20) := by
  have hr : (7/20:ℚ)=((7:ℕ):ℚ)/((20:ℕ):ℚ) := by norm_num
  rw [hr]
  cases last <;>
    exact r56_reserve_pos (r56cen_rep _) (by decide +kernel) 0 1 _ 7 20 (by norm_num)
      (by decide +kernel)

theorem positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) : 0<aeval p (H last) := by
  have hdom : |p-7/20|≤((7/20:ℚ):ℝ) := by
    push_cast
    exact TailPolynomial.centered_domain hp
  have hl := DirectedPowerBounds.constant_lower (centered_identity last) hdom
  have hpos : 0<((centered last).coeff 0:ℝ)-
      (norm (centered last) 1 (degree last) (7/20):ℝ) := by
    exact_mod_cast centered_reserve last
  have he : aeval (p-7/20) (centered last)=aeval p (H last) := by
    simp [centered,DirectedPowerBounds.shift_eval]
  rw [he] at hl
  linarith

theorem a_bounds (last : Bool) : (49/50:ℝ)≤(a last:ℝ) ∧ 0<(a last:ℝ) := by
  cases last <;> norm_num [a]

theorem rho_reserve (last : Bool) :
    (0:ℝ)<(rho last:ℝ) ∧ (rho last:ℝ)^2<(other last:ℝ)^2+9/25 := by
  cases last <;> norm_num [rho,other]

theorem envelope_positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p (P last) := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  dsimp [frameCap] at hp h2
  cases last <;> norm_num [P] <;> nlinarith [hp.1,hp.2]

theorem sine_polynomial_nonnegative {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0≤aeval p TailPolynomial.S7 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  have h6 := pow_le_pow_left₀ hp.1 hp.2 6
  have h4 := pow_nonneg hp.1 4
  have hfactor : 0≤1-p^2/6+p^4/120-p^6/5040 := by
    dsimp [frameCap] at h2 h6
    nlinarith only [h2,h6,h4]
  have hm := mul_nonneg hp.1 hfactor
  rw [TailPolynomial.S7_eval]
  dsimp [Arithmetic.sin7]
  nlinarith only [hm]

theorem cosine_polynomial_lower {p : ℝ} (hp : p∈Icc 0 frameCap) :
    (3/4:ℝ)<aeval p TailPolynomial.C6 := by
  have h2 := pow_le_pow_left₀ hp.1 hp.2 2
  have h6 := pow_le_pow_left₀ hp.1 hp.2 6
  have h4 := pow_nonneg hp.1 4
  rw [TailPolynomial.C6_eval]
  dsimp [frameCap] at h2 h6
  nlinarith only [h2,h6,h4]

theorem numerator_positive (last : Bool) {p : ℝ} (hp : p∈Icc 0 frameCap) :
    0<aeval p (numerator last) := by
  have ha := a_bounds last
  have hc := weight_pos hp
  have hfirst := mul_lt_mul_of_pos_left (cosine_polynomial_lower hp)
    (mul_pos ha.2 hc)
  have hs := mul_nonneg (show 0≤(2/5:ℝ)*(a last:ℝ) from mul_nonneg (by norm_num) ha.2.le)
    (sine_polynomial_nonnegative hp)
  have hgap : 0<(3/4)*(a last:ℝ)-2/5 := by linarith [ha.1]
  have hpositive := mul_pos hc hgap
  simp only [numerator,map_sub,map_add,map_mul,aeval_C,eq_ratCast,PrefixPolynomial.c_eval]
  push_cast
  nlinarith only [hfirst,hs,hpositive]

theorem tangent_nonnegative (last : Bool) {p : ℝ} (hp : 0≤p) :
    0≤aeval p (tangent last) := by
  cases last <;> norm_num [tangent,rho,other] <;> linarith

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3.SaturatedPolynomial
