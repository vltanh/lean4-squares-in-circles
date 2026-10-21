module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorMarkers
public import SquaresInCircles.Eight.TableFree.GlobalQuarterSignScalar

/-!
# Whole-interval scalar costs for two-edge radial anchor rigidity

The tangent quotient is bounded directly by alternating Taylor
polynomials on the full frame interval.  Negative angle costs share
the one actual endpoint-frame budget of their consecutive path.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalOuterAnchor

def secondaryAngle (λ d : ℝ) : ℝ := d+λ*(|Real.sin d|-Real.sin d)/2
def primaryAngle (λ a d : ℝ) : ℝ := d+λ*(|Real.sin d|/2-a*Real.sin d)/Real.cos d
def negativeCost (z : ℝ) : ℝ := -z+k*Real.sin z

theorem signed_trig {d : ℝ} (hd : |d|≤frameCap) :
    19/25<Real.cos d ∧ Real.cos d≤1 ∧ |Real.sin d|<13/20 := by
  have hc := CommonQuarter.signed_cos (by simpa only [frameCap] using hd)
  have hs := CommonQuarter.signed_sin (by simpa only [frameCap] using hd)
  exact ⟨by linarith,hc.2,by linarith⟩

theorem secant_upper {d : ℝ} (hd : |d|≤frameCap) :
    0<1/Real.cos d ∧ 1≤1/Real.cos d ∧ 1/Real.cos d<25/19 := by
  have ht := signed_trig hd
  have hc : 0<Real.cos d := by linarith [ht.1]
  refine ⟨div_pos (by norm_num) hc,?_,?_⟩
  · exact (le_div_iff₀ hc).2 (by linarith [ht.2.1])
  · exact (div_lt_iff₀ hc).2 (by linarith [ht.1])

theorem sine_cosine_sum_upper (d : ℝ) : Real.sin d+Real.cos d<10/7 := by
  by_contra! hn
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤10/7) hn 2
  nlinarith [Real.sin_sq_add_cos_sq d,sq_nonneg (Real.sin d-Real.cos d)]

theorem tangent_ratio {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0≤Real.sin x/Real.cos x ∧ Real.sin x/Real.cos x≤(61/50)*x := by
  have ht := transport_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  refine ⟨div_nonneg ht.2.2.1 hc.le,?_⟩
  apply (div_le_iff₀ hc).2
  have hxU : x≤(7/10:ℝ) := by simpa only [frameCap] using hx.2
  have h2 := pow_le_pow_left₀ hx.1 hxU 2
  have h6 := pow_le_pow_left₀ hx.1 hxU 6
  norm_num at h2 h6
  have hpoly : 0≤(11/50:ℝ)-(133/300)*x^2+(17/400)*x^4-(61/36000)*x^6 := by
    nlinarith [pow_nonneg hx.1 4]
  have hprod := mul_nonneg hx.1 hpoly
  have hcos := mul_le_mul_of_nonneg_left (cos_lower_six hx.1)
    (show 0≤(61/50:ℝ)*x by positivity)
  have hsin := sin_upper_five hx.1
  nlinarith only [hprod,hcos,hsin]

theorem sine_le_ratio {x : ℝ} (hx : x∈Icc 0 frameCap) :
    Real.sin x≤Real.sin x/Real.cos x := by
  have ht := transport_trig hx
  have hc : 0<Real.cos x := by linarith [ht.1]
  apply (le_div_iff₀ hc).2
  nlinarith [mul_nonneg ht.2.2.1 (sub_nonneg.mpr (Real.cos_le_one x))]

theorem secondary_positive {λ d : ℝ} (hd : d∈Icc 0 frameCap) :
    secondaryAngle λ d=d := by
  rw [secondaryAngle,abs_of_nonneg (transport_trig hd).2.2.1]
  ring

theorem secondary_negative {λ x : ℝ} (hx : x∈Icc 0 frameCap) :
    secondaryAngle λ (-x)= -x+λ*Real.sin x := by
  rw [secondaryAngle,Real.sin_neg,abs_neg,
    abs_of_nonneg (transport_trig hx).2.2.1]
  ring

theorem primary_positive {λ a d : ℝ} (hd : d∈Icc 0 frameCap) :
    primaryAngle λ a d=d-λ*(a-1/2)*(Real.sin d/Real.cos d) := by
  rw [primaryAngle,abs_of_nonneg (transport_trig hd).2.2.1]
  ring

theorem primary_negative {λ a x : ℝ} (hx : x∈Icc 0 frameCap) :
    primaryAngle λ a (-x)= -x+λ*(a+1/2)*(Real.sin x/Real.cos x) := by
  rw [primaryAngle,Real.sin_neg,Real.cos_neg,abs_neg,
    abs_of_nonneg (transport_trig hx).2.2.1]
  ring

theorem primary_k_positive_nonneg {a d : ℝ}
    (ha : a≤283/200) (hd : d∈Icc 0 frameCap) : 0≤primaryAngle k a d := by
  have hr := tangent_ratio hd
  have h₁ := mul_le_mul_of_nonneg_right (show a-1/2≤(183/200:ℝ) by linarith) hr.1
  have h₂ := mul_le_mul_of_nonneg_left hr.2 (by norm_num : (0:ℝ)≤183/200)
  rw [primary_positive hd]
  dsimp [k]
  nlinarith [hd.1]

theorem primary_m_positive_lower {a d : ℝ}
    (ha : a≤283/200) (hd : d∈Icc 0 frameCap) :
    -(17/100:ℝ)<primaryAngle m a d := by
  have hr := tangent_ratio hd
  have h₁ := mul_le_mul_of_nonneg_right (show a-1/2≤(183/200:ℝ) by linarith) hr.1
  have h₂ := mul_le_mul_of_nonneg_left hr.2 (by norm_num : (0:ℝ)≤183/200)
  rw [primary_positive hd]
  dsimp [m,frameCap] at *
  nlinarith [hd.2]

theorem primary_k_negative_lower {a x : ℝ}
    (ha : 447/800≤a) (hx : x∈Icc 0 frameCap) :
    negativeCost x≤primaryAngle k a (-x) := by
  have hr := tangent_ratio hx
  have hprod := mul_le_mul_of_nonneg_right (show 1≤a+1/2 by linarith) hr.1
  have hs := sine_le_ratio hx
  rw [primary_negative hx]
  dsimp [negativeCost,k]
  nlinarith

theorem secondary_k_lower {d : ℝ} (hd : |d|≤frameCap) :
    negativeCost (max 0 (-d))≤secondaryAngle k d := by
  by_cases hp : 0≤d
  · rw [max_eq_left (by linarith : -d≤0),secondary_positive ⟨hp,(le_abs_self d).trans hd⟩]
    simpa [negativeCost] using hp
  · have hn : d≤0 := by linarith
    rw [max_eq_right (by linarith : 0≤ -d)]
    have hh := secondary_negative (λ:=k) (show -d∈Icc 0 frameCap from
      ⟨by linarith,(neg_le_abs d).trans hd⟩)
    simpa only [neg_neg,negativeCost] using hh.ge

theorem primary_k_lower {a d : ℝ} (ha : 447/800≤a) (hA : a≤283/200)
    (hd : |d|≤frameCap) :
    negativeCost (max 0 (-d))≤primaryAngle k a d := by
  by_cases hp : 0≤d
  · rw [max_eq_left (by linarith : -d≤0)]
    simpa [negativeCost] using primary_k_positive_nonneg hA ⟨hp,(le_abs_self d).trans hd⟩
  · rw [max_eq_right (by linarith : 0≤ -d)]
    have hh := primary_k_negative_lower ha
      (show -d∈Icc 0 frameCap from ⟨by linarith,(neg_le_abs d).trans hd⟩)
    simpa only [neg_neg] using hh

theorem negative_cost_sum {x y : ℝ} (hx : 0≤x) (hy : 0≤y)
    (hsum : x+y≤frameCap) : -(3/20:ℝ)<negativeCost x+negativeCost y := by
  have hsx := sin_lower_three hx
  have hsy := sin_lower_three hy
  have hcube := pow_le_pow_left₀ (add_nonneg hx hy) hsum 3
  have hcross := mul_nonneg (mul_nonneg hx hy) (add_nonneg hx hy)
  have hcubes : x^3+y^3≤(7/10:ℝ)^3 := by
    dsimp [frameCap] at hcube
    nlinarith
  dsimp [negativeCost,k,frameCap] at *
  nlinarith

theorem negative_cost_lower {x : ℝ} (hx : x∈Icc 0 frameCap) :
    -(3/20:ℝ)<negativeCost x := by
  have hh := negative_cost_sum hx.1 (show (0:ℝ)≤0 by norm_num)
    (by simpa only [add_zero] using hx.2)
  simpa [negativeCost] using hh

theorem negative_parts_sum {v d : ℝ} (hv : |v|≤frameCap) (hd : |d|≤frameCap)
    (hsum : |v+d|≤frameCap) : max 0 (-v)+max 0 (-d)≤frameCap := by
  by_cases hv0 : 0≤v <;> by_cases hd0 : 0≤d
  · simp only [max_eq_left (by linarith : -v≤0),max_eq_left (by linarith : -d≤0),zero_add]
    norm_num [frameCap]
  · rw [max_eq_left (by linarith : -v≤0),max_eq_right (by linarith : 0≤ -d),zero_add]
    exact (neg_le_abs d).trans hd
  · rw [max_eq_right (by linarith : 0≤ -v),max_eq_left (by linarith : -d≤0),add_zero]
    exact (neg_le_abs v).trans hv
  · rw [max_eq_right (by linarith : 0≤ -v),max_eq_right (by linarith : 0≤ -d)]
    linarith [(neg_le_abs (v+d)).trans hsum]

end SquaresInCircles.Eight.TableFree.GlobalOuterAnchor
