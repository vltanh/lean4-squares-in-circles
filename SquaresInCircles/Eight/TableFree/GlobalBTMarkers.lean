module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorDomain
public import SquaresInCircles.Eight.TableFree.FrameHighArc

/-!
# Original marker planes for the global BT exclusion

The common G1 marker satisfies the full-chart endpoint bounds needed
by the BT tail and by its complementary return path.  Both core pieces
and every retained marker at a chart junction are included.  The three
tail coefficients are intrinsic chart data.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

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
  dsimp [linear,M] at hm ⊢
  linarith

theorem high_tail_marker {b : ℝ} (hb : b∈Icc b2 c0) :
    (67/500:ℝ)+(16/25)*b≤FrameHighArc.H b := by
  have hmono : MonotoneOn (fun z => FrameHighArc.H z-(16/25)*z) (Icc b2 c0) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact ((FrameHighArc.H_deriv hz).sub ((hasDerivAt_id z).const_mul (16/25:ℝ))).
        continuousAt.continuousWithinAt
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
  linarith

/-- The original marker, rather than a subsequently chosen envelope,
supplies each tail coefficient. -/
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
        FramePair.label,M,p,q,cM,← hc.1] using hh
  | high =>
      have hc := FrameHighArc.state_high_chart s hs
      have hh := high_tail_marker hc.2
      dsimp [ZeroPrimary.unsigned]
      rw [hs]
      simp only [Branch.type,tailWeight,tailMargin,Matrix.cons_val_three]
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

theorem low_upper_plane {b : ℝ} (hb : b∈Icc 0 b1) :
    L b≤(3/8)*(A b-a0)+(1091/1000)*b := by
  have ha := (A_low_bounds hb).2
  dsimp [L,FrameLowArc.u,FrameLowArc.v]
  nlinarith [hb.1]

theorem middle_upper_plane {b : ℝ} (hb : b∈Icc b1 b2) :
    M b≤(3/8)*(A b-a0)+(1091/1000)*b := by
  let f : ℝ→ℝ := fun z => (3/8)*(A z-a0)+(1091/1000)*z-M z
  have hmono : MonotoneOn f (Icc b1 b2) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact (((((A_hasDerivAt ⟨b1_mem.1.trans hz.1,hz.2.trans b2_mem.2⟩).
        sub_const a0).const_mul (3/8:ℝ)).add
          ((hasDerivAt_id z).const_mul (1091/1000:ℝ))).sub (M_deriv hz)).
        continuousAt.continuousWithinAt
    · intro z hz
      exact (((((A_hasDerivAt ⟨b1_mem.1.trans hz.1.le,hz.2.le.trans b2_mem.2⟩).
        sub_const a0).const_mul (3/8:ℝ)).add
          ((hasDerivAt_id z).const_mul (1091/1000:ℝ))).sub
            (M_deriv (Ioo_subset_Icc_self hz)))
    · intro z hz
      have hsl := (slope_mid_bounds (Ioo_subset_Icc_self hz)).1
      dsimp [Ad,Md,FrameLowArc.slope,p,q] at hsl ⊢
      nlinarith
  have hleft : 0<f b1 := by
    dsimp [f]
    rw [A_b1,M_b1]
    dsimp [M1,p,q,cM,b1]
    linarith [a1_precise.2,a0_bounds.2]
  have hh := hmono ⟨le_rfl,b1_lt_b2.le⟩ hb hb.1
  dsimp [f] at hleft hh
  linarith

theorem high_upper_plane {b : ℝ} (hb : b∈Icc b2 c0) :
    FrameHighArc.H b≤(3/8)*(A b-a0)+(1091/1000)*b := by
  have hh := linear_endpoint_lower
    (p := 3/8+FrameHighArc.u) (q := 1091/1000-FrameHighArc.v)
    (by norm_num [FrameHighArc.u]) b2_mem.1 le_rfl hb
  have hleft : (3/8)*a0+FrameHighArc.k≤
      linear (3/8+FrameHighArc.u) (1091/1000-FrameHighArc.v) b2 := by
    rw [linear,A_b2]
    dsimp [FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,b2]
    linarith [a2_bounds.1,a0_bounds.2,FrameHighArc.diagonal_bounds.2,
      Arithmetic.pi_hand_enclosure.2]
  have hright : (3/8)*a0+FrameHighArc.k≤
      linear (3/8+FrameHighArc.u) (1091/1000-FrameHighArc.v) c0 := by
    rw [linear,A_c0]
    dsimp [FrameHighArc.k,FrameHighArc.u,FrameHighArc.v]
    linarith [a0_bounds.2,FrameHighArc.diagonal_bounds.1,
      Arithmetic.pi_hand_enclosure.2]
  have hm := (le_min hleft hright).trans hh
  dsimp [linear,FrameHighArc.H] at hm ⊢
  linarith

theorem marker_outer_upper_plane (s : State) (hs : s.branch.type≠0) :
    ZeroPrimary.unsigned s≤(3/8)*(s.a-a0)+(1091/1000)*s.b := by
  cases hj : s.branch with
  | coreSide | coreCorner => simp [hj,Branch.type] at hs
  | low =>
      have hc := state_low_chart s hj
      simpa [ZeroPrimary.unsigned,hj,FramePair.label,L,FrameLowArc.u,
        FrameLowArc.v,← hc.1] using low_upper_plane hc.2
  | middle =>
      have hc := state_mid_chart s hj
      simpa [ZeroPrimary.unsigned,hj,FramePair.label,M,p,q,cM,← hc.1]
        using middle_upper_plane hc.2
  | high =>
      have hc := FrameHighArc.state_high_chart s hj
      have hh := high_upper_plane hc.2
      dsimp [ZeroPrimary.unsigned]
      rw [hj,hc.1]
      dsimp [FramePair.label,FrameHighArc.H,FrameHighArc.k,
        FrameHighArc.u,FrameHighArc.v] at hh ⊢
      linarith

end SquaresInCircles.Eight.TableFree.GlobalBT
