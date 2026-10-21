module

public import SquaresInCircles.Eight.TableFree.EContactCurve

/-!
# Strict concavity of the exact E contact energy

Uncompiled draft.  The apparent large cotangent terms are canceled before
estimation.  A single factorization controls the whole orientation
interval; there is no angle subdivision or fitted numerical certificate.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EContactCurve

structure Window (α z : ℝ) : Prop where
  half_cos_lower : 99/100<Real.cos (α/2)
  half_sin_upper : Real.sin (α/2)<11/100
  full_cos_lower : 4879/5000<Real.cos α
  full_sin_upper : Real.sin α<11/50
  cos_lower : Real.cos (α/2)≤Real.cos z
  double_cos_lower : Real.cos α≤Real.cos (2*z)
  sin_bounds : -Real.sin (α/2)≤Real.sin z ∧ Real.sin z≤Real.sin (α/2)
  double_sin_bounds : -Real.sin α≤Real.sin (2*z) ∧ Real.sin (2*z)≤Real.sin α

theorem window {α z : ℝ} (hα : α∈Ioo 0 (11/50 : ℝ)) (hz : |z|≤α/2) :
    Window α z := by
  have hhalf : 0≤α/2 := by linarith [hα.1]
  have hhalfup : α/2≤11/100 := by linarith [hα.2]
  have hhalfSq := pow_le_pow_left₀ hhalf hhalfup 2
  have hfullSq := pow_lt_pow_left₀ hα.1.le hα.2 (by decide : (2:ℕ)≠0)
  have hcoshalf : 99/100<Real.cos (α/2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (α/2)]
  have hcosfull : 4879/5000<Real.cos α := by
    nlinarith [Real.one_sub_sq_div_two_le_cos α]
  have hzi := abs_le.mp hz
  have hdouble : |2*z|≤α := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hdi := abs_le.mp hdouble
  have hcosz : Real.cos (α/2)≤Real.cos z := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg z)
      (by linarith [hα.2,Real.pi_gt_three]) hz
    simpa only [Real.cos_abs] using hh
  have hcosdouble : Real.cos α≤Real.cos (2*z) := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (2*z))
      (by linarith [hα.2,Real.pi_gt_three]) hdouble
    simpa only [Real.cos_abs] using hh
  have hsinzlo : -Real.sin (α/2)≤Real.sin z := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hα.2,Real.pi_gt_three])
      (by linarith [hzi.2,hα.2,Real.pi_gt_three]) hzi.1
    simpa only [Real.sin_neg] using hh
  have hsinzhi : Real.sin z≤Real.sin (α/2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hzi.1,hα.2,Real.pi_gt_three])
      (by linarith [hα.2,Real.pi_gt_three]) hzi.2
  have hsindlo : -Real.sin α≤Real.sin (2*z) := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hα.2,Real.pi_gt_three])
      (by linarith [hdi.2,hα.2,Real.pi_gt_three]) hdi.1
    simpa only [Real.sin_neg] using hh
  have hsindhi : Real.sin (2*z)≤Real.sin α :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hdi.1,hα.2,Real.pi_gt_three])
      (by linarith [hα.2,Real.pi_gt_three]) hdi.2
  exact ⟨hcoshalf,(Real.sin_le hhalf).trans_lt (by linarith [hα.2]),
    hcosfull,(Real.sin_le hα.1.le).trans_lt hα.2,hcosz,hcosdouble,
    ⟨hsinzlo,hsinzhi⟩,⟨hsindlo,hsindhi⟩⟩

/-- The factor `(c-1)*(1+4*c*(1-c²))` controls the cancellation on
the entire orientation interval.  The denominator is positive. -/
theorem cotangent_cancellation {α z : ℝ}
    (hα : α∈Ioo 0 (11/50 : ℝ)) (hz : |z|≤α/2) :
    -2*(Real.cos α/Real.sin α)*Real.cos (2*z)+
      Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2))*Real.cos z≤
        3*Real.sin (α/2) := by
  have ht := half_trig hα
  have hw := window hα hz
  have hcot : 0≤Real.cos α/Real.sin α :=
    div_nonneg (by linarith [hw.full_cos_lower]) ht.2.2.le
  have hfirst := mul_le_mul_of_nonpos_left hw.double_cos_lower
    (show -2*(Real.cos α/Real.sin α)≤0 by linarith)
  have hcoefficient : 0≤Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2)) :=
    mul_nonneg ht.2.1.le (div_nonneg ht.2.1.le ht.1.le)
  have hsecond := mul_le_mul_of_nonneg_left (Real.cos_le_one z) hcoefficient
  have hsin := Real.sin_two_mul (α/2)
  have hcos := Real.cos_two_mul (α/2)
  rw [show 2*(α/2)=α by ring] at hsin hcos
  have hformula :
      -2*(Real.cos α/Real.sin α)*Real.cos α+
        Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2))=
      (Real.cos (α/2)^3-(2*Real.cos (α/2)^2-1)^2)/
        (Real.cos (α/2)*Real.sin (α/2)) := by
    rw [hsin,hcos]
    field_simp [ht.1.ne',ht.2.1.ne']
    ring
  have hunit := Real.sin_sq_add_cos_sq (α/2)
  have hloss : 0≤1-Real.cos (α/2)^2 := by nlinarith [sq_nonneg (Real.sin (α/2))]
  have hfactor := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (Real.cos_le_one (α/2)))
    (show 0≤1+4*Real.cos (α/2)*(1-Real.cos (α/2)^2) by
      have hp := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) ht.2.1.le) hloss
      linarith)
  have hunit3 := congrArg (fun r : ℝ => 3*Real.cos (α/2)*r) hunit
  have hmax :
      -2*(Real.cos α/Real.sin α)*Real.cos α+
        Real.cos (α/2)*(Real.cos (α/2)/Real.sin (α/2))≤3*Real.sin (α/2) := by
    rw [hformula]
    apply (div_le_iff₀ (mul_pos ht.2.1 ht.1)).2
    nlinarith
  linarith

theorem scaled_second_upper {m n α z : ℝ}
    (hα : α∈Ioo 0 (11/50 : ℝ)) (hz : |z|≤α/2)
    (hm : m∈Icc (0:ℝ) 1) (hn : |n|≤1) :
    scaledSecond m n α z≤
      5*Real.sin (α/2)+2*Real.sin (α/2)^2+2*Real.sin α+2-4*Real.cos α := by
  have ht := half_trig hα
  have hw := window hα hz
  have hcancel := cotangent_cancellation hα hz
  have hcz : 0≤Real.cos z := by linarith [hw.half_cos_lower,hw.cos_lower]
  have hcot : 0≤Real.cos (α/2)/Real.sin (α/2) := div_nonneg ht.2.1.le ht.1.le
  have hcotprod := mul_nonneg hcot hcz
  have hbracket : 0≤(Real.cos (α/2)/Real.sin (α/2)+2)*Real.cos z+Real.sin z := by
    nlinarith [hw.half_cos_lower,hw.cos_lower,hw.sin_bounds.1,hw.half_sin_upper]
  have hmterm := mul_le_mul_of_nonneg_right hm.2 (mul_nonneg ht.2.1.le hbracket)
  have htwo := mul_le_mul (Real.cos_le_one (α/2)) (Real.cos_le_one z) hcz
    (by norm_num : (0:ℝ)≤1)
  have hsinpart := mul_le_mul_of_nonneg_left hw.sin_bounds.2 ht.2.1.le
  have hsinpart' := mul_le_mul_of_nonneg_right (Real.cos_le_one (α/2)) ht.1.le
  have htan0 : 0≤Real.sin (α/2)/Real.cos (α/2) := div_nonneg ht.1.le ht.2.1.le
  have htan2 : Real.sin (α/2)/Real.cos (α/2)≤2 := by
    apply (div_le_iff₀ ht.2.1).2
    linarith [hw.half_sin_upper,hw.half_cos_lower]
  have hk : |Real.sin (α/2)/Real.cos (α/2)-2|≤2 := by
    rw [abs_of_nonpos (by linarith : Real.sin (α/2)/Real.cos (α/2)-2≤0)]
    linarith
  have hsz : |Real.sin z|≤Real.sin (α/2) := abs_le.mpr hw.sin_bounds
  have hkprod : |(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z|≤2*Real.sin (α/2) := by
    rw [abs_mul]
    exact mul_le_mul hk hsz (abs_nonneg _) (by norm_num)
  have hB : |Real.cos z+(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z|≤
      1+2*Real.sin (α/2) :=
    (abs_add _ _).trans (add_le_add (Real.abs_cos_le_one z) hkprod)
  have hnprod : |n*(Real.cos z+(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z)|≤
      1+2*Real.sin (α/2) := by
    rw [abs_mul]
    simpa using mul_le_mul hn hB (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hnterm : -n*(Real.cos z+(Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z)≤
      1+2*Real.sin (α/2) := by
    have hh := (neg_le_abs (n*(Real.cos z+
      (Real.sin (α/2)/Real.cos (α/2)-2)*Real.sin z))).trans hnprod
    nlinarith
  have hnterm' := mul_le_mul_of_nonneg_left hnterm ht.1.le
  dsimp [scaledSecond]
  nlinarith [hw.double_cos_lower,hw.double_sin_bounds.1]

theorem scaled_second_negative {m n α z : ℝ}
    (hα : α∈Ioo 0 (11/50 : ℝ)) (hz : |z|≤α/2)
    (hm : m∈Icc (0:ℝ) 1) (hn : |n|≤1) :
    scaledSecond m n α z< -(889/1000 : ℝ) := by
  have hu := scaled_second_upper hα hz hm hn
  have ht := half_trig hα
  have hw := window hα hz
  have hsquare := pow_lt_pow_left₀ ht.1.le hw.half_sin_upper
    (by decide : (2:ℕ)≠0)
  nlinarith [hw.half_sin_upper,hw.full_sin_upper,hw.full_cos_lower]

theorem energyDD_upper {m n α z : ℝ}
    (hα : α∈Ioo 0 (11/50 : ℝ)) (hz : |z|≤α/2)
    (hm : m∈Icc (0:ℝ) 1) (hn : |n|≤1) :
    energyDD m n α z≤ -(4/5 : ℝ) := by
  have ht := half_trig hα
  have hnumer := scaled_second_negative hα hz hm hn
  rw [←scaled_second_identity hα m n z] at hnumer
  by_contra! hbad
  have hprod := mul_le_mul_of_nonneg_left hbad.le ht.2.2.le
  have hsin := Real.sin_le_one α
  nlinarith

/-- Every genuine interior subinterval has a strict improving endpoint.
The later geometric argument chooses the subinterval inside the original
strict sorting and positive-tangent neighborhood. -/
theorem endpoint_improves {m n α l u z : ℝ}
    (hα : α∈Ioo 0 (11/50 : ℝ))
    (hm : m∈Icc (0:ℝ) 1) (hn : |n|≤1)
    (hl : -α/2≤l) (hu : u≤α/2) (hz : z∈Ioo l u) :
    energy m n α l<energy m n α z ∨ energy m n α u<energy m n α z := by
  apply strict_endpoint_of_second_derivative (k := (4/5 : ℝ))
    (df := energyD m n α) (ddf := energyDD m n α) (by norm_num) hz
  · intro r hr
    exact energy_hasDerivAt m n α r
  · intro r hr
    exact energyD_hasDerivAt m n α r
  · intro r hr
    exact energyDD_upper hα (abs_le.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩) hm hn

end SquaresInCircles.Eight.TableFree.EContactCurve
