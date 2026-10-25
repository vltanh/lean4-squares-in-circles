module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Owners.Flat.TStress
public import SquaresInCircles.Eight.Owners.Sole.NormGain

/-!
# Eight squares: curvature of a secant support norm

The second derivative of `√(a² + sec² s)` is at least `1/√(a² + 1)` wherever `cos s > 0`
(`normSecond_lower`), from the two terms of the chain rule. The upper bounds at short angles are
Taylor inequalities at the endpoints (`commonSecond_critical`, `commonSecond_BT`).
-/

section
/-!
## Monotonicity of the norm gain on the entire half-ratio cone

The exact squared comparison only needs
2r >= z(1+r²). On r in [1/2,1] and z in [0,.7] this follows
from a single quadratic inequality. Thus the coefficient comparison
also applies at the frame cap when r is smaller than sin(.7).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.HalfRatioNormGain
open SoleNormGain VaryingBFunctions VaryingBComparison
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope

theorem gain_nonnegative {r z : ℝ} (hr : r∈Icc (1/2:ℝ) 1)
    (hz : z∈Icc 0 frameCap) : 0≤gain r z := by
  have hS := OrdinaryCurvatureBounds.shape_pos r
  have hN := root_pos r hz
  have hS2 := OrdinaryCurvatureBounds.shape_sq r
  have hN2 := root_sq r hz
  have hz7 : z≤7/10 := hz.2
  have hr0 : 0≤r := by linarith [hr.1]
  have hr2 : r^2≤(3/2)*r-1/2 := by
    nlinarith [mul_nonneg (show 0≤r-1/2 by linarith [hr.1]) (sub_nonneg.mpr hr.2)]
  have hinner : 0≤2*r-z*(1+r^2) := by
    have hm := mul_le_mul_of_nonneg_right hz7 (show 0≤1+r^2 by positivity)
    nlinarith [hr.1]
  have hnum : 0≤1-r*z := by
    have hm := mul_le_mul hr.2 hz7 hz.1 (by norm_num : (0:ℝ)≤1)
    nlinarith
  have hp := mul_nonneg (mul_nonneg (sq_nonneg r) hz.1) hinner
  have hid : (root r z)^2-((1-r*z)*OrdinaryCurvatureBounds.shape r)^2=
      r^2*z*(2*r-z*(1+r^2)) := by
    rw [mul_pow,hS2,hN2]
    ring
  have hcomp : (1-r*z)*OrdinaryCurvatureBounds.shape r≤root r z := by
    rw [← hid] at hp
    exact (pow_le_pow_iff_left₀ (mul_nonneg hnum hS.le) hN.le two_ne_zero).1 (by linarith)
  have hdiv : (1-r*z)/root r z≤1/OrdinaryCurvatureBounds.shape r := by
    apply (div_le_div_iff₀ hN hS).2
    simpa only [one_mul] using hcomp
  dsimp [gain]
  linarith

theorem larger_monotone {R p a b s : ℝ}
    (hR : 0≤R) (hp : 0<p) (hpa : p≤a) (hab : a≤b) (hbp : b≤2*p)
    (hs : s∈Icc 0 frameCap) : normGain R p a s≤normGain R p b s := by
  have ha : 0<a := hp.trans_le hpa
  have hx (x : ℝ) (hxx : x∈Icc a b) : 0<x ∧ p/x∈Icc (1/2:ℝ) 1 := by
    have hxp : 0<x := ha.trans_le hxx.1
    refine ⟨hxp,⟨(le_div_iff₀ hxp).2 ?_,(div_le_one hxp).2 (hpa.trans hxx.1)⟩⟩
    linarith [hxx.2]
  have hmono : MonotoneOn (fun x => normGain R p x s) (Icc a b) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hxx
      exact (normGain_hasDerivAt_large hp (hx x hxx).1 hs).continuousAt.continuousWithinAt
    · intro x hxx
      exact normGain_hasDerivAt_large hp (hx x (Ioo_subset_Icc_self hxx)).1 hs
    · intro x hxx
      exact mul_nonneg hR (gain_nonnegative (hx x (Ioo_subset_Icc_self hxx)).2 (sin_mem hs))
  exact hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

end SquaresInCircles.Eight.HalfRatioNormGain
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecantNormCurvature
open Candidate PositiveAngularEnvelope FlatTStress

def secant (s : ℝ) : ℝ := 1/Real.cos s
def first (s : ℝ) : ℝ := Real.sin s/Real.cos s^2
def second (s : ℝ) : ℝ := (1+Real.sin s^2)/Real.cos s^3
def supportNorm (a s : ℝ) : ℝ := Real.sqrt (a^2+secant s^2)
def normFirst (a s : ℝ) : ℝ := secant s*first s/supportNorm a s
def normSecond (a s : ℝ) : ℝ :=
  a^2*first s^2/(supportNorm a s)^3+secant s*second s/supportNorm a s

def normalized (R a s : ℝ) : ℝ :=
  secant s-1+(13/12)*Real.tan s-R*(supportNorm a s-Real.sqrt (a^2+1))
def gainFirst (R a s : ℝ) : ℝ :=
  first s+(13/12)/Real.cos s^2-R*normFirst a s
def commonSecond (s : ℝ) : ℝ := second s+(13/6)*Real.sin s/Real.cos s^3
def gainSecond (R a s : ℝ) : ℝ := commonSecond s-R*normSecond a s

theorem secant_hasDerivAt {s : ℝ} (hc : Real.cos s≠0) :
    HasDerivAt secant (first s) s := by
  convert (hasDerivAt_const s (1:ℝ)).div (Real.hasDerivAt_cos s) hc using 1
  · rfl
  · dsimp [first]
    ring

theorem first_hasDerivAt {s : ℝ} (hc : Real.cos s≠0) :
    HasDerivAt first (second s) s := by
  have hh := (Real.hasDerivAt_sin s).div ((Real.hasDerivAt_cos s).pow 2) (pow_ne_zero 2 hc)
  convert hh using 1
  · rfl
  · dsimp [second]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq s]

theorem norm_pos {a s : ℝ} (hc : 0<Real.cos s) : 0<supportNorm a s := by
  apply Real.sqrt_pos.mpr
  dsimp [secant]
  positivity

theorem norm_sq (a s : ℝ) : (supportNorm a s)^2=a^2+secant s^2 :=
  Real.sq_sqrt (by positivity)

theorem norm_hasDerivAt {a s : ℝ} (hc : 0<Real.cos s) :
    HasDerivAt (supportNorm a) (normFirst a s) s := by
  have hh := ((hasDerivAt_const s (a^2)).add ((secant_hasDerivAt hc.ne').pow 2)).sqrt
    (show a^2+secant s^2≠0 by
      dsimp [secant]
      positivity)
  convert hh using 1
  · rfl
  · dsimp [normFirst,supportNorm]
    ring

theorem normFirst_hasDerivAt {a s : ℝ} (hc : 0<Real.cos s) :
    HasDerivAt (normFirst a) (normSecond a s) s := by
  have hn := norm_hasDerivAt (a := a) hc
  have hne := (norm_pos (a := a) hc).ne'
  have hh := ((secant_hasDerivAt hc.ne').mul (first_hasDerivAt hc.ne')).div hn hne
  convert hh using 1
  · rfl
  · dsimp only [normFirst,normSecond,Pi.mul_apply]
    field_simp [hne]
    linear_combination (-(first s^2))*norm_sq a s

theorem normalized_hasDerivAt {R a s : ℝ} (hc : 0<Real.cos s) :
    HasDerivAt (normalized R a) (gainFirst R a s) s := by
  have hh := (((secant_hasDerivAt hc.ne').sub_const 1).add
    ((Real.hasDerivAt_tan hc.ne').const_mul (13/12:ℝ))).sub
      (((norm_hasDerivAt (a := a) hc).sub_const (Real.sqrt (a^2+1))).const_mul R)
  convert hh using 1
  · rfl
  · dsimp [gainFirst]
    ring

theorem gainFirst_hasDerivAt {R a s : ℝ} (hc : 0<Real.cos s) :
    HasDerivAt (gainFirst R a) (gainSecond R a s) s := by
  have hi := (hasDerivAt_const s (13/12:ℝ)).div
    ((Real.hasDerivAt_cos s).pow 2) (pow_ne_zero 2 hc.ne')
  have hh := ((first_hasDerivAt hc.ne').add hi).sub
    ((normFirst_hasDerivAt (a := a) hc).const_mul R)
  convert hh using 1
  · rfl
  · dsimp [gainSecond,commonSecond]
    field_simp [hc.ne']
    ring

theorem charge_scale {R c : ℝ} (hc : 0<c) (a s : ℝ) :
    secantCharge R c a s=c*normalized R (a/c) s := by
  have hN := zero_norm_scale hc a (1/Real.cos s)
  have hZ := zero_norm_scale hc a 1
  simp only [mul_one,one_pow] at hZ
  have hcN : pairNorm a (c/Real.cos s) 0=c*supportNorm (a/c) s := by
    simpa only [supportNorm,secant,div_eq_mul_inv,one_mul] using hN
  dsimp [secantCharge,normalized]
  rw [hcN,hZ]
  dsimp [secant]
  ring

theorem charge_hasDerivAt {R c a s : ℝ} (hc : 0<c) (hcos : 0<Real.cos s) :
    HasDerivAt (secantCharge R c a) (c*gainFirst R (a/c) s) s := by
  have he : secantCharge R c a=(fun x => c*normalized R (a/c) x) :=
    funext (charge_scale hc a)
  rw [he]
  exact (normalized_hasDerivAt hcos).const_mul c

theorem charge_derivative_hasDerivAt {R c a s : ℝ} (hcos : 0<Real.cos s) :
    HasDerivAt (fun x => c*gainFirst R (a/c) x) (c*gainSecond R (a/c) s) s :=
  (gainFirst_hasDerivAt hcos).const_mul c

theorem secant_ge_one {s : ℝ} (hc : 0<Real.cos s) : 1≤ secant s := by
  exact (le_div_iff₀ hc).2 (by simpa using Real.cos_le_one s)

theorem second_ge_secant {s : ℝ} (hc : 0<Real.cos s) : secant s≤ second s := by
  have hid : second s-secant s=2*Real.sin s^2/Real.cos s^3 := by
    dsimp [second,secant]
    field_simp [hc.ne']
    nlinarith [Real.sin_sq_add_cos_sq s]
  have hnonneg : 0≤2*Real.sin s^2/Real.cos s^3 := by positivity
  linarith

/-- Wherever `cos s > 0`, the second derivative of the norm is at least `1/√(a² + 1)`; the radial
Hessian term and the acceleration term are both kept. -/
theorem normSecond_lower {a s : ℝ} (hc : 0<Real.cos s) :
    1/Real.sqrt (a^2+1)≤normSecond a s := by
  have hw := secant_ge_one hc
  have hn := norm_pos (a := a) hc
  have hN0 : 0<Real.sqrt (a^2+1) := Real.sqrt_pos.mpr (by positivity)
  have hN02 := Real.sq_sqrt (show 0≤a^2+1 by positivity)
  have hN2 := norm_sq a s
  have hw2 : 1≤ secant s^2 := by nlinarith
  have hprod := mul_nonneg (sq_nonneg a) (show 0≤ secant s^2-1 by linarith)
  have hsq : (secant s*Real.sqrt (a^2+1))^2-(supportNorm a s)^2=
      a^2*(secant s^2-1) := by rw [mul_pow,hN02,hN2]; ring
  have hcross : supportNorm a s≤ secant s*Real.sqrt (a^2+1) := by
    have hpos := mul_pos (show 0<secant s by linarith) hN0
    nlinarith
  have hratio : 1/Real.sqrt (a^2+1)≤ secant s/supportNorm a s := by
    apply (div_le_div_iff₀ hN0 hn).2
    simpa only [one_mul] using hcross
  have hDD : 1≤ second s := hw.trans (second_ge_secant hc)
  have hacc := mul_le_mul_of_nonneg_left hDD
    (div_nonneg (show 0≤ secant s by linarith) hn.le)
  have hrad : 0≤a^2*first s^2/(supportNorm a s)^3 := by positivity
  have hre : secant s*second s/supportNorm a s=secant s/supportNorm a s*second s := by ring
  dsimp only [normSecond]
  rw [hre]
  linarith

theorem commonSecond_eq (s : ℝ) :
    commonSecond s=(1+Real.sin s^2+(13/6)*Real.sin s)/Real.cos s^3 := by
  dsimp [commonSecond,second]
  ring

theorem commonSecond_critical {s : ℝ} (hs : s∈Icc 0 (4/25:ℝ)) :
    commonSecond s<57/40 := by
  have hb := trig_bracket (l := 0) (u := (4/25:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  have hc : (49361/50000:ℝ)<Real.cos s := by norm_num at hb; linarith [hb.2.2.1]
  have hsu : Real.sin s<(3983/25000:ℝ) := by norm_num at hb; linarith [hb.2.1]
  have hs0 : 0≤Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_gt_three])
  have hs2 := pow_le_pow_left₀ hs0 hsu.le 2
  have hc3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤49361/50000) hc.le 3
  rw [commonSecond_eq]
  apply (div_lt_iff₀ (pow_pos (by linarith : 0<Real.cos s) 3)).2
  nlinarith

theorem commonSecond_BT {s : ℝ} (hs : s∈Icc 0 (9/100:ℝ)) :
    commonSecond s<609/500 := by
  have hb := trig_bracket (l := 0) (u := (9/100:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  have hc : (19919/20000:ℝ)<Real.cos s := by norm_num at hb; linarith [hb.2.2.1]
  have hs0 : 0≤Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_gt_three])
  have hsu : Real.sin s≤9/100 := (Real.sin_le hs.1).trans hs.2
  have hs2 := pow_le_pow_left₀ hs0 hsu 2
  have hc3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19919/20000) hc.le 3
  rw [commonSecond_eq]
  apply (div_lt_iff₀ (pow_pos (by linarith : 0<Real.cos s) 3)).2
  nlinarith

end SquaresInCircles.Eight.SecantNormCurvature
end
end
end
