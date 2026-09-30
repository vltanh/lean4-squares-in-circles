import SquaresInCircles.Six.Analytic.WestPinBounds

/-!
# Western charts contain qW or qD

The region between the pins is covered uniformly by TwoPinCover. Before qW,
the single fringe estimate in WestPinBounds proves qW membership. The case
split follows the location of the primary direction relative to the pin, not
an arithmetic mesh. Both cap and OWN hypotheses are treated explicitly.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma west_wedge_local {a b t : ℝ} (h : ContainedChart a |b|)
    (hb : |b| < 1/2) (ht : -Real.pi/12 ≤ t ∧ t ≤ Real.pi/4) :
    localPin a b (-Real.pi/12-t) ∨ localPin a b (Real.pi/4-t) := by
  have hz : 0 ≤ Real.pi/12+t := by linarith
  have hv : 0 ≤ Real.pi/4-t := by linarith
  have hsum : (Real.pi/12+t)+(Real.pi/4-t)=Real.pi/3 := by ring
  have hh := two_pin_cover h hb hz hv hsum
  simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using hh

lemma west_pins_of_local {a b t : ℝ}
    (h : localPin a b (-Real.pi/12-t) ∨ localPin a b (Real.pi/4-t)) :
    openSquare (orientedSquare (Real.pi+t) a b) (pinPoint (11*Real.pi/12)) ∨
      openSquare (orientedSquare (Real.pi+t) a b) (pinPoint (5*Real.pi/4)) := by
  have hW : 11*Real.pi/12-(Real.pi+t)=-Real.pi/12-t := by ring
  have hD : 5*Real.pi/4-(Real.pi+t)=Real.pi/4-t := by ring
  simpa only [pin_mem_iff,hW,hD] using h

lemma west_fringe_local {a b t : ℝ} (h : ContainedChart a |b|)
    (hb : |b| < 1/2) (ht : -2/3 ≤ t ∧ t ≤ -Real.pi/12)
    (htrans : (9/10)*Real.sin (-Real.pi/12-t)-b < 1/2) :
    localPin a b (-Real.pi/12-t) := by
  have hd : 0 ≤ -Real.pi/12-t ∧ -Real.pi/12-t ≤ 2/3 := by
    constructor <;> linarith [ht.1,ht.2,Real.pi_pos]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd.1
    (by linarith [hd.2,Real.pi_gt_d2])
  refine ⟨pin_normal h (by rwa [abs_of_nonneg hd.1]),?_⟩
  apply abs_lt.mpr
  exact ⟨by linarith [(abs_lt.mp hb).2],htrans⟩

/-- The radial profile for the negative OWN tilt. -/
lemma west_own_negative_profile {a b t x y : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (ht0 : t ≤ 0) (hx : x ≤ c0) (hy0 : 0 ≤ y)
    (hm : 0 ≤ centralMargin .own (Real.pi+t) a b x y) :
    1/2+coreRadius*Real.cos (-t)+(1/2)*Real.sin (-t) ≤ a := by
  have hc0 : 0 ≤ Real.cos t := by linarith [(octant_trig ht).1.1]
  have hs0 := sin_nonpos_octant ht0 (abs_le.mp ht).1
  have hxc := mul_le_mul_of_nonneg_right
    (show coreRadius ≤ 1/2-x by linarith [c0_add_coreRadius]) hc0
  have hys := mul_nonneg hy0 (show 0 ≤ -Real.sin t by linarith)
  dsimp [centralMargin,centralNormal,angularWidth] at hm
  simp only [Real.cos_pi_add,Real.sin_pi_add,abs_neg] at hm
  rw [abs_of_nonneg hc0,abs_of_nonpos hs0] at hm
  rw [Real.cos_neg,Real.sin_neg]
  nlinarith

/-- OWN on the west primary axis implies one of the two western pins. -/
theorem west_own_fixed_pins {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hcore : AvoidsCore a |b|) (ht : |t| ≤ Real.pi/4)
    (hx : x ≤ c0) (hy0 : 0 ≤ y)
    (hm : 0 ≤ centralMargin .own (Real.pi+t) a b x y) :
    openSquare (orientedSquare (Real.pi+t) a b) (pinPoint (11*Real.pi/12)) ∨
      openSquare (orientedSquare (Real.pi+t) a b) (pinPoint (5*Real.pi/4)) := by
  have hb := h.u_lt_half hcore
  have htlo := own_west_lower_window h ht hx hy0 hm
  apply west_pins_of_local
  by_cases hleft : t ≤ -Real.pi/12
  · left
    apply west_fringe_local h hb ⟨htlo.le,hleft⟩
    have hv : Real.pi/12 ≤ -t ∧ -t ≤ 2/3 := ⟨by linarith,by linarith⟩
    have hprofile := west_own_negative_profile h ht
      (by linarith [Real.pi_pos]) hx hy0 hm
    have hh := own_west_fringe_transverse h hv hprofile
    have hid : -t-Real.pi/12=-Real.pi/12-t := by ring
    simpa only [hid] using hh
  · exact west_wedge_local h hb ⟨by linarith,(abs_le.mp ht).2⟩

/-- A western cardinal cap also contains one of the two western pins. -/
theorem west_cap_fixed_pins {a b t H : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi/4) (hH : coreRadius ≤ H)
    (hm : H+angularWidth t ≤ centerX t a b) :
    openSquare (orientedSquare (Real.pi+t) a b) (pinPoint (11*Real.pi/12)) ∨
      openSquare (orientedSquare (Real.pi+t) a b) (pinPoint (5*Real.pi/4)) := by
  obtain ⟨ht40,_,_,_,_,hb⟩ := signed_cap_bounds ht hH (chart_corner h) hm
  have htb := abs_lt.mp ht40
  apply west_pins_of_local
  by_cases hleft : t ≤ -Real.pi/12
  · left
    apply west_fringe_local h hb ⟨by linarith [htb.1],hleft⟩
    have hv : Real.pi/12 ≤ -t ∧ -t ≤ 2/5 := ⟨by linarith,by linarith [htb.1]⟩
    have hc : H+angularWidth (-(-t)) ≤ centerX (-(-t)) a b := by
      simpa only [neg_neg] using hm
    have hh := cap_west_fringe_transverse h hv hH hc
    have hid : -t-Real.pi/12=-Real.pi/12-t := by ring
    simpa only [hid] using hh
  · exact west_wedge_local h hb ⟨by linarith,by linarith [htb.2,Real.pi_gt_d2]⟩

end SquaresInCircles.Six.Analytic
