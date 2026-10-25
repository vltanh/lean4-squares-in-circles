module

public import SquaresInCircles.Eight.Frames.Low.HighPositiveLate

/-!
# Eight squares: the original high-source primary axis in its quarter-rotated chart

The rotation is an identity for the original margin and cost.  It
does not choose a new separating owner or move either original
square.  The closed source chart includes both intrinsic cut ties.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowPrimaryGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus

def sourceDomain : Set ℝ := Icc c0 a2
def upperMargin (k : Bool) (z B x : ℝ) : ℝ :=
  z+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def upperCost (k : Bool) (z B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+G z-sign k*L B

theorem source_extended {z : ℝ} (hz : z∈sourceDomain) : z∈extendedDomain := by
  constructor <;> linarith [hz.1,hz.2,c0_bounds.1,a2_bounds.2]

theorem source_chart {b : ℝ} (hb : b∈Icc b2 c0) : A b∈sourceDomain :=
  A_high_bounds hb

theorem rotated_margin (k : Bool) (b B x : ℝ) :
    primary k b B (Real.pi/2+x)=upperMargin k (A b) B x := by
  dsimp [primary,FrameLowMidGeometry.primary,upperMargin]
  rw [FrameLowHighQuarterStrip.quarter_width]
  simp only [Real.sin_add,Real.cos_add,Real.sin_pi_div_two,Real.cos_pi_div_two,
    zero_mul,one_mul,zero_sub]
  ring

theorem rotated_cost (k : Bool) {b : ℝ} (hb : b∈Icc b2 c0) (B x : ℝ) :
    highLowCost false k b B (Real.pi/2+x)=upperCost k (A b) B x := by
  dsimp [highLowCost,upperCost,sign]
  rw [FrameLowHighQuarterStrip.quarter_charge,quarter_label hb]
  ring

theorem rotated_angle {b B x : ℝ} (k : Bool)
    (hb : b∈Icc b2 c0) (hB : B∈Icc 0 b1)
    (hx : -(34/125:ℝ)≤x) (hm : 0≤primary k b B x) :
    -(2/5:ℝ)<x-Real.pi/2 := by
  have hh := high_low_primary_cut k hb hB hx hm
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem Gd_monotone : MonotoneOn Gd extendedDomain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z hz => (Gd_deriv hz).continuousAt.continuousWithinAt
  · exact fun z hz => Gd_deriv (Ioo_subset_Icc_self hz)
  · intro z hz
    exact mul_nonneg (by norm_num [FrameHighArc.v])
      (slopeD_positive (Ioo_subset_Icc_self hz)).le

theorem source_Gd_lower {z : ℝ} (hz : z∈sourceDomain) :
    (480179/500000:ℝ)≤Gd z := by
  have hc : c0∈extendedDomain := by constructor <;> linarith [c0_bounds.1,c0_bounds.2]
  have hh := Gd_monotone hc (source_extended hz) hz.1
  simp only [Gd,FrameLowHighAligned.slope_c0] at hh ⊢
  norm_num [FrameHighArc.u,FrameHighArc.v] at hh ⊢
  linarith

theorem source_G_lower {z : ℝ} (hz : z∈sourceDomain) : Real.pi/4≤G z := by
  have hc : c0∈extendedDomain := by constructor <;> linarith [c0_bounds.1,c0_bounds.2]
  have hh := FrameLowHighQuarterCalculus.G_monotone hc (source_extended hz) hz.1
  simpa only [G_c0] using hh

theorem low_Ld_upper {B : ℝ} (hB : B∈Icc 0 b1) : Ld B<197/200 := by
  have hh := (slope_bounds hB).1
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  linarith

theorem negative_target_tail {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : (27/250:ℝ)≤x) :
    (8833/10000:ℝ)<upperCost false z B x := by
  have hc := FrameLowHighPositiveLate.charge_linear (show 0≤x by linarith)
  have hg := source_G_lower hz
  have hl := (L_bounds hB).1
  dsimp [upperCost,sign]
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem positive_target_tail {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : (23/50:ℝ)≤x) :
    (8833/10000:ℝ)<upperCost true z B x := by
  have hc := CorePairGeometry.charge_upper x
  have hg := source_G_lower hz
  have hl := (L_bounds hB).2.2
  dsimp [upperCost,sign]
  linarith [Arithmetic.pi_hand_enclosure.1,L1_precise.2]

end SquaresInCircles.Eight.FrameHighLowPrimaryGeometry
