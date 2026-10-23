module

public import SquaresInCircles.Eight.TableFree.GlobalZeroSignSupport

/-!
# Whole-chart marker bounds for original quarter-owner signs

These estimates use the same marker selected at each original vertex
in the complete G1 pair theorem.  They cover the two core pieces and
all three outer charts, including chart ties and zero transverse
coordinates.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalQuarterSign

open FramePair ZeroPrimary GlobalZeroSign

theorem state_norm_sq (s : State) : s.a^2+s.b^2<(283/200:ℝ)^2 := by
  let r := Real.sqrt (s.a^2+s.b^2)
  have hr : 0≤r := Real.sqrt_nonneg _
  have hr2 : r^2=s.a^2+s.b^2 := Real.sq_sqrt (by positivity)
  have hsum : r≤s.a+s.b := by
    by_contra! hh
    nlinarith [s.a_pos,s.b_nonneg,mul_nonneg s.a_pos.le s.b_nonneg]
  have hc := state_circle s
  norm_num [Q0] at hc
  have hu : r<(283/200:ℝ) := by
    by_contra! hh
    nlinarith
  nlinarith

theorem rotated_projection_lt (s : State) (d : ℝ) :
    s.a*Real.cos d-s.b*Real.sin d<(283/200:ℝ) := by
  have hh := FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<283/200)
    (state_norm_sq s) (Real.pi/2+d)
  simpa [Real.sin_add,Real.cos_add] using hh

theorem marker_lt_four_fifths (s : State) : unsigned s<(4/5:ℝ) := by
  have ha := primary_lower s
  have hc := s.canonical
  cases hb : s.branch with
  | coreSide =>
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith
  | coreCorner =>
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith
  | low =>
      have hu := (coordinates s).2.1
      have ht : s.branch.type≠0 := by simp [hb,Branch.type]
      have hax := (CommonQuarter.outer_bounds (outer_data s ht)).2.1
      change s.a≤a0 at hax
      have hcut : 4*s.b≤s.a := by simpa [hb,TypeMem] using s.type_mem
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith
  | middle =>
      have hsup := state_support s (1489593/1000000) (1580219/1000000)
      have hn : Real.sqrt ((1489593/1000000:ℝ)^2+(1580219/1000000)^2)<109/50 := by
        have hh := Real.sq_sqrt (show 0≤(1489593/1000000:ℝ)^2+
          (1580219/1000000)^2 by positivity)
        have hz := Real.sqrt_nonneg ((1489593/1000000:ℝ)^2+(1580219/1000000)^2)
        nlinarith
      have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
      have hprod := (mul_lt_mul_of_pos_left hn hR).trans
        (mul_lt_mul_of_pos_right (show CommonQuarter.radius<2 by
          linarith [CommonQuarter.radius_bounds.2]) (by norm_num : (0:ℝ)<109/50))
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith
  | high =>
      have ht : s.branch.type≠0 := by simp [hb,Branch.type]
      have hbounds := CommonQuarter.outer_bounds (outer_data s ht)
      have hlo : c0≤s.a := hbounds.1
      have hhi : s.b≤c0 := hbounds.2.2.2.1
      dsimp [unsigned]
      rw [hb]
      dsimp [FramePair.label]
      linarith [pi_lt_22_over_7]

theorem marker_outer_upper (s : State) (hs : s.branch.type≠0) :
    unsigned s≤(111/100)*s.b := by
  have hh := (outer_marker_bounds s hs).2
  have ha := (CommonQuarter.outer_bounds (outer_data s hs)).2.1
  change s.a≤a0 at ha
  linarith

theorem marker_zero (s : State) (hb : s.b=0) : unsigned s=0 := by
  have hu := marker_small_upper s (by linarith)
  have hl := marker_nonneg s
  rw [hb] at hu
  linarith

theorem signed_of_nonpos (s : State) (hy : sign s.positive*s.b≤0) :
    s.signedLabel= -unsigned s := by
  change sign s.positive*unsigned s= -unsigned s
  cases hp : s.positive <;> simp [hp,FramePair.sign] at hy ⊢
  have hz : s.b=0 := le_antisymm hy s.b_nonneg
  rw [marker_zero s hz]
  ring

theorem signed_of_nonneg (s : State) (hy : 0≤sign s.positive*s.b) :
    s.signedLabel=unsigned s := by
  change sign s.positive*unsigned s=unsigned s
  cases hp : s.positive <;> simp [hp,FramePair.sign] at hy ⊢
  have hz : s.b=0 := by linarith [s.b_nonneg]
  rw [marker_zero s hz]
  ring

theorem quarter_zero_margin (s t : State) {d : ℝ} (hd : |d|≤frameCap)
    (ht : sign t.positive*t.b≤0) :
    s.Feasible t 0 (Real.pi/2+d) ↔
      (1+Real.cos d+|Real.sin d|)/2≤
        sign s.positive*s.b+t.a*Real.cos d-t.b*Real.sin d := by
  have hty := transverse_nonpos_eq t ht
  simp only [State.Feasible,forwardMargin,Real.sin_add,Real.cos_add,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul,zero_mul,zero_add,sub_zero,
    CommonQuarter.quarter_width (by simpa only [frameCap] using hd)]
  rw [show sign t.positive*t.b= -t.b from hty]
  constructor <;> intro hh <;> nlinarith

theorem quarter_one_margin (s t : State) {d : ℝ} (hd : |d|≤frameCap) :
    s.Feasible t 1 (Real.pi/2+d) ↔
      (1+Real.cos d+|Real.sin d|)/2≤
        t.a+s.a*Real.sin d+sign s.positive*s.b*Real.cos d := by
  simp only [State.Feasible,forwardMargin,Real.sin_add,Real.cos_add,
    Real.sin_pi_div_two,Real.cos_pi_div_two,one_mul,zero_mul,zero_add,sub_zero,
    CommonQuarter.quarter_width (by simpa only [frameCap] using hd)]
  constructor <;> intro hh <;> nlinarith

end SquaresInCircles.Eight.TableFree.GlobalQuarterSign
