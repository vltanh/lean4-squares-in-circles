module

public import SquaresInCircles.Eight.TableFree.CanonicalNominalWeights

/-!
# Whole-arc flux reserves of the nominal family

Uncompiled reconstruction.  The cosine support inequality and two
explicit polynomial identities preserve the linear gains of both
canonical errors.  These estimates use one continuous weight family
over the entire actual tilt interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CanonicalNominal
open Eight.FiveCorner CanonicalNegativeStress

theorem short_trig {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    Real.sin α∈Icc 0 (3/10:ℝ) ∧ (19/20:ℝ)≤Real.cos α ∧
      Real.cos α≤1-(Real.sin α)^2/2 := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hα.1
    (by linarith [hα.2,Real.pi_gt_three])
  have hsu := (Real.sin_le hα.1).trans hα.2
  have ha2 := pow_le_pow_left₀ hα.1 hα.2 2
  have hcl : (19/20:ℝ)≤Real.cos α := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hcu : Real.cos α≤1-(Real.sin α)^2/2 := by
    nlinarith [Real.sin_sq_add_cos_sq α,sq_nonneg (1-Real.cos α)]
  exact ⟨⟨hs0,by linarith⟩,hcl,hcu⟩

theorem flux_bounds {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    0≤flux (atTilt α) α ∧ flux (atTilt α) α≤101/100 := by
  obtain ⟨hs,hcl,hcu⟩ := short_trig hα
  have hA := KA_bounds hs
  have hA0 : 0≤KA (parameters (Real.sin α)) := by linarith [hA.1]
  have hc0 : 0≤Real.cos α := by linarith
  have hlow := mul_le_mul_of_nonneg_right hA.1 hc0
  have hup := mul_le_mul_of_nonneg_left hcu hA0
  have hs3 := pow_le_pow_left₀ hs.1 hs.2 3
  have hbracket : 0≤583/144000+(15707/28800)*Real.sin α+
      (13817/288000)*(Real.sin α)^2-(533/57600)*(Real.sin α)^3 := by
    nlinarith [hs.1,sq_nonneg (Real.sin α)]
  have hprod := mul_nonneg (sq_nonneg (Real.sin α)) hbracket
  have hid : 1+(43/800)*Real.sin α-(2/5)*(Real.sin α)^2-
      (KA (parameters (Real.sin α))*(1-(Real.sin α)^2/2)-Real.sin α)=
      (Real.sin α)^2*(583/144000+(15707/28800)*Real.sin α+
        (13817/288000)*(Real.sin α)^2-(533/57600)*(Real.sin α)^3) := by
    rw [KA_polynomial hs]
    ring
  have hquad : 1+(43/800)*Real.sin α-(2/5)*(Real.sin α)^2≤101/100 := by
    nlinarith [sq_nonneg (Real.sin α-43/640)]
  change 0≤KA (parameters (Real.sin α))*Real.cos α-1*Real.sin α ∧
    KA (parameters (Real.sin α))*Real.cos α-1*Real.sin α≤101/100
  simp only [one_mul]
  constructor <;> nlinarith [hs.2]

theorem small_error_reserve {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    Real.sin α/2≤KB (atTilt α)-flux (atTilt α) α := by
  obtain ⟨hs,hcl,hcu⟩ := short_trig hα
  have hA0 : 0≤KA (parameters (Real.sin α)) := by linarith [(KA_bounds hs).1]
  have hcos := mul_le_mul_of_nonneg_left hcu hA0
  have hs4 := pow_le_pow_left₀ hs.1 hs.2 4
  have hbracket : 0≤4/75-(11363/360000)*Real.sin α-
      (3403/288000)*(Real.sin α)^4 := by
    nlinarith [hs.2]
  have hprod := mul_nonneg hs.1 hbracket
  have hid : KB (parameters (Real.sin α))-
      KA (parameters (Real.sin α))*(1-(Real.sin α)^2/2)+Real.sin α-Real.sin α/2=
      Real.sin α*(4/75-(11363/360000)*Real.sin α-(3403/288000)*(Real.sin α)^4)+
        (3333943/7200000)*(Real.sin α)^3+(779/9000)*(Real.sin α)^4 := by
    rw [KA_polynomial hs,KB_polynomial hs]
    ring
  have h3 := pow_nonneg hs.1 3
  have h4 := pow_nonneg hs.1 4
  change Real.sin α/2≤KB (parameters (Real.sin α))-
    (KA (parameters (Real.sin α))*Real.cos α-1*Real.sin α)
  simp only [one_mul]
  nlinarith

theorem secant_error_reserve {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    1/25≤(atTilt α).beta*(13/12)-flux (atTilt α) α := by
  have hb := beta_bounds (short_trig hα).1
  have hf := (flux_bounds hα).2
  change 1/25≤Nominal.beta (Real.sin α)*(13/12)-flux (atTilt α) α
  linarith [hb.1]

theorem amplitude_bounds {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    0≤Real.cos α+KA (atTilt α)*Real.sin α ∧
      Real.cos α+KA (atTilt α)*Real.sin α≤7/5 := by
  obtain ⟨hs,hc,_⟩ := short_trig hα
  have hA : KA (atTilt α)∈Icc (1:ℝ) (4/3) := KA_bounds hs
  have hp0 := mul_nonneg (show 0≤KA (atTilt α) by exact le_trans (by norm_num) hA.1) hs.1
  have hpu := mul_le_mul hA.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤4/3)
  constructor <;> linarith [Real.cos_le_one α]

end SquaresInCircles.Eight.TableFree.CanonicalNominal
