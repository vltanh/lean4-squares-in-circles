module

public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain
public import SquaresInCircles.Eight.Frames.High.Arc

/-!
# Eight squares: marker planes of the BT exclusion

The common marker `ZeroPrimary.unsigned` lies above a plane on each chart: above
`tailMargin + tailWeight * s.b` for the BT tail (`tail_marker`) and above `(43/50) s.b` for the
return path (`marker_linear_lower`). The bounds hold on the whole charts, on both pieces of the
core, and with either marker at a junction of charts; the three tail coefficients are data of the
charts.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc FrameLowArc FrameMidArc GlobalZeroSign
open GlobalOuterAnchor

def kappa : ℝ := 49/50
def returnThreshold : ℝ := 103/40
def pathThreshold : ℝ := 16761/4520
def tailWeight : Fin 4→ℝ := ![9449/10000,9449/10000,797/1000,16/25]
def tailMargin : Fin 4→ℝ := ![0,0,229/5000,67/500]

theorem thresholds_sum : pathThreshold+returnThreshold=710/113 := by
  norm_num [pathThreshold,returnThreshold]

theorem low_tail_marker {b : ℝ} (hb : b∈Icc 0 b1) :
    (9449/10000:ℝ)*b≤L b := by
  have hend : 0≤L1-(9449/10000)*b1 := by
    dsimp [L1,FrameLowArc.u,FrameLowArc.v,b1]
    linarith [a1_precise.1,a0_bounds.2]
  have hh := label_loss_lower (lambda := (9449/10000:ℝ))
    (epsilon := 0) hb le_rfl (by simpa using hend)
  linarith

theorem middle_tail_marker {b : ℝ} (hb : b∈Icc b1 b2) :
    (229/5000:ℝ)+(797/1000)*b≤M b := by
  have hh := linear_endpoint_lower (p := p) (q := q-797/1000)
    (by norm_num [p]) b1_mem.1 b2_mem.2 hb
  have hleft : 229/5000-cM≤linear p (q-797/1000) b1 := by
    rw [linear,A_b1]
    dsimp [p,q,cM,b1]
    linarith [a1_precise.1]
  have hright : 229/5000-cM≤linear p (q-797/1000) b2 := by
    rw [linear,A_b2]
    dsimp [p,q,cM,b2]
    linarith [a2_bounds.1]
  have hm := (le_min hleft hright).trans hh
  dsimp [linear,FrameMidArc.M] at hm ⊢
  linarith

theorem high_tail_marker {b : ℝ} (hb : b∈Icc b2 c0) :
    (67/500:ℝ)+(16/25)*b≤FrameHighArc.H b := by
  have hmono : MonotoneOn (fun z => FrameHighArc.H z-(16/25)*z) (Icc b2 c0) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact ((FrameHighArc.H_deriv hz).sub
        ((hasDerivAt_id z).const_mul (16/25:ℝ))).continuousAt.continuousWithinAt
    · intro z hz
      exact (FrameHighArc.H_deriv (Ioo_subset_Icc_self hz)).sub
        ((hasDerivAt_id z).const_mul (16/25:ℝ))
    · intro z hz
      have hs := (FrameHighArc.slope_high_bounds (Ioo_subset_Icc_self hz)).1
      dsimp [FrameHighArc.Hd,FrameHighArc.u,FrameHighArc.v]
      linarith
  have hleft : (67/500:ℝ)<FrameHighArc.H b2-(16/25)*b2 := by
    rw [FrameHighArc.H_b2]
    dsimp [FrameHighArc.H2,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,b2]
    linarith [a2_bounds.2,FrameHighArc.diagonal_bounds.1,Arithmetic.pi_hand_enclosure.1]
  have hm := hmono ⟨le_rfl,b2_mem.2⟩ hb hb.1
  dsimp only at hm
  linarith

/-- The marker of a state lies above the tail plane of its chart:
`tailMargin + tailWeight * s.b ≤ unsigned s`. -/
theorem tail_marker (s : State) :
    tailMargin s.branch.type+tailWeight s.branch.type*s.b≤ZeroPrimary.unsigned s := by
  cases hs : s.branch with
  | coreSide | coreCorner =>
      have hc : s.branch.type=0 := by simp [hs,Branch.type]
      have ha := (core_bounds s hc).1
      have hb := s.b_nonneg
      simp only [ZeroPrimary.unsigned,hs,Branch.type,tailWeight,tailMargin,
        Matrix.cons_val_zero,FramePair.label]
      nlinarith
  | low =>
      have hc := state_low_chart s hs
      have hh := low_tail_marker hc.2
      simpa [ZeroPrimary.unsigned,hs,Branch.type,tailWeight,tailMargin,
        FramePair.label,L,FrameLowArc.u,FrameLowArc.v,← hc.1] using hh
  | middle =>
      have hc := state_mid_chart s hs
      have hh := middle_tail_marker hc.2
      simpa [ZeroPrimary.unsigned,hs,Branch.type,tailWeight,tailMargin,
        FramePair.label,FrameMidArc.M,p,q,cM,← hc.1] using hh
  | high =>
      have hc := FrameHighArc.state_high_chart s hs
      have hh := high_tail_marker hc.2
      dsimp [ZeroPrimary.unsigned]
      rw [hs]
      simp only [Branch.type,tailWeight,tailMargin,Matrix.cons_val]
      dsimp [FramePair.label]
      rw [hc.1]
      dsimp [FrameHighArc.H,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v] at hh
      linarith

theorem high_linear_marker (s : State) (hs : s.branch=.high) :
    (43/50:ℝ)*s.b≤ZeroPrimary.unsigned s := by
  have hp := state_support s FrameHighArc.u (43/50-FrameHighArc.v)
  have hn : Real.sqrt (FrameHighArc.u^2+(43/50-FrameHighArc.v)^2)<7379/10000 := by
    have hh := Real.sq_sqrt (show 0≤FrameHighArc.u^2+(43/50-FrameHighArc.v)^2 by positivity)
    have hz := Real.sqrt_nonneg (FrameHighArc.u^2+(43/50-FrameHighArc.v)^2)
    dsimp [FrameHighArc.u,FrameHighArc.v] at *
    nlinarith
  have hR : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hprod := (mul_lt_mul_of_pos_left hn hR).trans
    (mul_lt_mul_of_pos_right (show CommonQuarter.radius<1979/1000 by
      linarith [CommonQuarter.radius_bounds.2]) (by norm_num : (0:ℝ)<7379/10000))
  dsimp [ZeroPrimary.unsigned]
  rw [hs]
  dsimp [FramePair.label,FrameHighArc.u,FrameHighArc.v] at hp hn hprod ⊢
  linarith [FrameHighArc.diagonal_bounds.1,Arithmetic.pi_hand_enclosure.1]

theorem marker_linear_lower (s : State) : (43/50:ℝ)*s.b≤ZeroPrimary.unsigned s := by
  have ht := tail_marker s
  have hb := s.b_nonneg
  cases hs : s.branch with
  | coreSide | coreCorner | low =>
      simp [hs,Branch.type,tailWeight,tailMargin] at ht
      linarith
  | middle =>
      have hu := (state_mid_chart s hs).2.2
      have hb2 := b2_bounds.2
      simp [hs,Branch.type,tailWeight,tailMargin] at ht
      linarith
  | high => exact high_linear_marker s hs

end SquaresInCircles.Eight.GlobalBT
