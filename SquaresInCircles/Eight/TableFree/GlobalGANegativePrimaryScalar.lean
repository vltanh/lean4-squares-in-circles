module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTD

/-!
# Nonpositive intermediate primary errors pay their full angular charge

The same secant multiplier treats GA3 and AB2.  The original signed
coordinate of A cancels exactly; the remaining comparison uses only
the true-core primary lower bound and the containing-circle upper
bound.  A direct cubic estimate proves the complete interval bound,
including zero, without a half-angle transition or finite sampling.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativePrimary

open Candidate Secondary

def primaryIncrement (d a b : ℝ) : ℝ :=
  l/Real.cos d*(edgeWidth d-b-a*Real.sin d)-l*(1-b)+charge*d

theorem cos_pos {d : ℝ} (hd : |d|≤frameCap) : 0<Real.cos d := by
  have hh := (transport_trig (show |d|∈Icc 0 frameCap from ⟨abs_nonneg d,hd⟩)).1
  rw [Real.cos_abs] at hh
  linarith

/-- The cubic lower bound has a positive linear reserve after the
quadratic term is bounded on the entire permitted interval. -/
theorem common_charge {s : ℝ} (hs : s∈Icc 0 frameCap) :
    charge*s*Real.cos s≤
      l*((847/800)*Real.sin s-(183/200)*(1-Real.cos s)) := by
  have hsin := Real.sin_ge_sub_cube hs.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=s)
  have hsupper : s≤7/10 := hs.2
  have hcoef : 0≤l*(183/200)-charge*s := by norm_num [l,charge]; linarith
  have hcosP := mul_le_mul_of_nonneg_left hcos hcoef
  have hsinP := mul_le_mul_of_nonneg_left hsin
    (show 0≤l*(847/800) by norm_num [l])
  have hsq : s^2≤(7/10)*s := by
    nlinarith [mul_le_mul_of_nonneg_right hsupper hs.1]
  have hcube : 0≤s^3 := pow_nonneg hs.1 3
  norm_num [l,charge] at hcosP hsinP ⊢
  nlinarith

theorem negative_gain_nonneg {s a b : ℝ}
    (hs : s∈Icc 0 frameCap) (ha : 447/800≤a) (hb : b≤283/200) :
    0≤primaryIncrement (-s) a b := by
  have ht := transport_trig hs
  have hc : 0<Real.cos s := by linarith [ht.1]
  have hs0 : 0≤Real.sin s := ht.2.2.1
  have hc1 : 0≤1-Real.cos s := sub_nonneg.mpr (Real.cos_le_one s)
  have hprimary := mul_nonneg (sub_nonneg.mpr ha) hs0
  have hbound := mul_nonneg (sub_nonneg.mpr hb) hc1
  have hh := common_charge hs
  have hnonneg : 0≤l*((a+1/2)*Real.sin s+(1/2-b)*(1-Real.cos s))-
      charge*s*Real.cos s := by
    norm_num [l,charge] at hh ⊢
    nlinarith
  have hid : primaryIncrement (-s) a b*Real.cos s=
      l*((a+1/2)*Real.sin s+(1/2-b)*(1-Real.cos s))-
        charge*s*Real.cos s := by
    rw [primaryIncrement,edgeWidth_negative_formula hs]
    simp only [Real.sin_neg,Real.cos_neg]
    field_simp [ne_of_gt hc]
    ring
  exact (mul_nonneg_iff_of_pos_right hc).1 (by rw [hid]; exact hnonneg)

theorem gain_nonneg {d a b : ℝ} (hd : d≤0) (hsmall : |d|≤frameCap)
    (ha : 447/800≤a) (hb : b≤283/200) : 0≤primaryIncrement d a b := by
  have hs : -d∈Icc 0 frameCap :=
    ⟨neg_nonneg.mpr hd,(neg_le_abs d).trans hsmall⟩
  simpa only [neg_neg] using negative_gain_nonneg hs ha hb

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativePrimary
