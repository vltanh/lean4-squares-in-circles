module

public import SquaresInCircles.Eight.TableFree.StationaryPositionComparison
public import SquaresInCircles.Eight.TableFree.CentralSegment

/-!
# Localization of the actual varying position minimizer

Uncompiled reconstruction.  Strict position convexity on the original
geometric window converts the proved comparison signs into bounds on
`minimizingPosition q t` itself.  Tilt stationarity is never used: the
result applies at every tilt in the complete terminal interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryPrimitives
open ExactFamily.FiveCornerGeometry

theorem position_gradient_strictMono {q c s : ℝ}
    (hql : (79/40:ℝ)^2≤q) (hqu : q≤9789/2500)
    (hc : 0<c) (hs : 0≤s) (hunit : c^2+s^2=1) :
    StrictMonoOn (fun u => 2*positionHalf q c s u) positionWindow := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (87/100:ℝ) (11/10))
  · intro u hu
    have hd := (window_bounds hql hqu hu).smoothDomain (by linarith)
    exact (position_second_deriv (c:=c) (s:=s) hd).continuousAt.continuousWithinAt
  · intro u hu
    have hd := (window_bounds hql hqu (interior_subset hu)).smoothDomain (by linarith)
    rw [(position_second_deriv (c:=c) (s:=s) hd).deriv]
    exact hd.positionSecond_pos hc hs hunit

theorem arctan_mem_tiltInterval {h : ℝ} (hh : h∈Icc (1/10:ℝ) (41/250)) :
    Real.arctan h∈tiltInterval := by
  exact ⟨Real.arctan_pos.mpr (by linarith [hh.1]),
    Real.arctan_strictMono (by linarith [hh.2])⟩

/-- The first localization of the actual minimum, with both strict
inequalities obtained from nonstationary comparison positions. -/
theorem minimizingPosition_rectangle {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    179/200<minimizingPosition q (Real.arctan h) ∧
      minimizingPosition q (Real.arctan h)<1-(3/5)*h := by
  have hql : (79/40:ℝ)^2≤q := by nlinarith [hq.1]
  have ht := trig_bounds hh
  have hm := position_gradient_strictMono hql hq.2 (cosine_pos h)
    (by linarith [ht.s_lower] : 0≤sine h) (unit h)
  have hu := windowMinimizer_mem q (cosine h) (sine h)
  change minimizingPosition q (Real.arctan h)∈positionWindow at hu
  have hz := minimizingPosition_root hql hq.2 (arctan_mem_tiltInterval hh)
  change 2*positionHalf q (cosine h) (sine h) (minimizingPosition q (Real.arctan h))=0 at hz
  have hlow : (179/200:ℝ)∈positionWindow := by norm_num [positionWindow]
  have hupp : 1-(3/5)*h∈positionWindow := by
    constructor <;> linarith [hh.1,hh.2]
  have hn := lower_fixed_negative hq hh
  simp only [comparison,zero_mul,sub_zero] at hn
  have hp := upper_comparison_positive hq hh
  change 0<2*positionHalf q (cosine h) (sine h) (1-(3/5)*h) at hp
  constructor
  · by_contra! hbad
    have he := hm.monotoneOn hu hlow hbad
    linarith
  · by_contra! hbad
    have he := hm.monotoneOn hupp hu hbad
    linarith

/-- The additional affine lower bound uses one further comparison on
`h≤.15`; beyond that endpoint the fixed lower bound is stronger. -/
theorem minimizingPosition_affine {q h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hh : h∈Icc (1/10:ℝ) (41/250)) :
    1-(7/10)*h<minimizingPosition q (Real.arctan h) ∧
      minimizingPosition q (Real.arctan h)<1-(3/5)*h := by
  have hb := minimizingPosition_rectangle hq hh
  refine ⟨?_,hb.2⟩
  by_cases hcut : h≤3/20
  · have hql : (79/40:ℝ)^2≤q := by nlinarith [hq.1]
    have ht := trig_bounds hh
    have hm := position_gradient_strictMono hql hq.2 (cosine_pos h)
      (by linarith [ht.s_lower] : 0≤sine h) (unit h)
    have hu := windowMinimizer_mem q (cosine h) (sine h)
    change minimizingPosition q (Real.arctan h)∈positionWindow at hu
    have hz := minimizingPosition_root hql hq.2 (arctan_mem_tiltInterval hh)
    change 2*positionHalf q (cosine h) (sine h) (minimizingPosition q (Real.arctan h))=0 at hz
    have hcmp : 1-(7/10)*h∈positionWindow := by
      constructor <;> linarith [hh.1]
    have hn := lower_comparison_negative hq ⟨hh.1,hcut⟩
    change 2*positionHalf q (cosine h) (sine h) (1-(7/10)*h)<0 at hn
    by_contra! hbad
    have he := hm.monotoneOn hu hcmp hbad
    linarith
  · have he : 1-(7/10)*h≤179/200 := by linarith
    exact he.trans_lt hb.1

theorem terminal_tangent {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    Real.tan t∈Icc (1/10:ℝ) (41/250) ∧ Real.arctan (Real.tan t)=t := by
  have htm : t∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [ht.1,ht.2,Real.pi_gt_three]
  have hc := Real.cos_pos_of_mem_Ioo htm
  have hs := Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1] : 0<t)
    (by linarith [ht.2,Real.pi_gt_three] : t<Real.pi)
  have htan : 0≤Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact (div_pos hs hc).le
  have hat := Real.arctan_tan htm.1 htm.2
  have hlow := CentralForbidden.atan_upper htan
  rw [hat] at hlow
  have ht2 := square_bounds ht (by norm_num)
  have hcos : (617/625:ℝ)≤Real.cos t := by
    nlinarith [Real.one_sub_sq_div_two_le_cos t,ht2.2]
  have hsin := Real.sin_le (show 0≤t by linarith [ht.1])
  have hu : Real.tan t≤41/250 := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ hc).2
    nlinarith [ht.2]
  exact ⟨⟨ht.1.trans hlow,hu⟩,hat⟩

/-- The reusable actual-angle API.  The position is the geometric
minimum at this `t`, rather than the position at the stationary tilt. -/
theorem minimizingPosition_terminal {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    179/200<minimizingPosition q t ∧
    1-(7/10)*Real.tan t<minimizingPosition q t ∧
    minimizingPosition q t<1-(3/5)*Real.tan t ∧
    minimizingPosition q t<47/50 := by
  obtain ⟨hh,hat⟩ := terminal_tangent ht
  have hr := minimizingPosition_rectangle hq hh
  have ha := minimizingPosition_affine hq hh
  rw [hat] at hr ha
  exact ⟨hr.1,ha.1,ha.2,by linarith [ha.2,hh.1]⟩

theorem minimizingPosition_terminal_primitives {q t : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (ht : t∈Icc (1/10:ℝ) (4/25)) :
    RadicalBounds q (minimizingPosition q t) ∧ TrigBounds (Real.tan t) ∧
      ForceBounds q (minimizingPosition q t) (Real.tan t) := by
  obtain ⟨hu,_,_,hv⟩ := minimizingPosition_terminal hq ht
  have hh := (terminal_tangent ht).1
  exact ⟨radical_bounds hq ⟨hu.le,hv.le⟩,trig_bounds hh,force_bounds hq ⟨hu.le,hv.le⟩ hh⟩

end SquaresInCircles.Eight.TableFree.StationaryPrimitives
