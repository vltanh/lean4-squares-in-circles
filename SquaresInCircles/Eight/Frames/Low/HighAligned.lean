module

public import SquaresInCircles.Eight.Frames.Low.HighArc
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds

/-!
# Eight squares: the aligned low/high contacts

At the angle `0`, a low state `b` and a high state `B` in contact, `b + B ≥ 1`, have markers adding
up to at least `F0` (`parallel_contact`). Along the contact the sum of the markers is
`parallel b = L b + H (1 - b)` for `b ∈ [b0, b1]`, `b0 = 1 - c0`, and, beyond the diagonal,
`quarter b = L b + G (1 - b)` for `b ∈ [0, b0]`. Both contact curves lie on their circles, and
both sums have second derivative above `1/4` on their whole intervals (`parallel_curvature`,
`quarter_curvature`). At `b0` they take the value `F0` with the small derivative
`d0 ∈ (0, 1/10000)` (`parallel_initial`, `quarter_initial`, `d0_bounds`), so `parallel ≥ F0`
(`parallel_lower`) and `quarter ≥ F0 - 2 d0²` (`quarter_lower`): the quarter contact keeps its
signed derivative at `b0` and the quadratic loss it causes, and `F0 - 2 d0²` still exceeds
`8833/10000` (`quarter_reserve`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighAligned
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc

def b0 : ℝ := 1-c0
def F0 : ℝ := L b0+Real.pi/4
def d0 : ℝ := FrameLowArc.v-FrameHighArc.u-FrameHighArc.v-FrameLowArc.u*slope b0
def parallel (b : ℝ) : ℝ := L b+H (1-b)
def parallelD (b : ℝ) : ℝ := Ld b-Hd (1-b)
def parallelDD (b : ℝ) : ℝ := -FrameLowArc.u*slopeD b+FrameHighArc.u*slopeD (1-b)
def quarter (b : ℝ) : ℝ := L b+G (1-b)
def quarterD (b : ℝ) : ℝ := Ld b-Gd (1-b)
def quarterDD (b : ℝ) : ℝ := -FrameLowArc.u*slopeD b+FrameHighArc.v*slopeD (1-b)

theorem b0_bounds : (20157/200000:ℝ)<b0 ∧ b0<50393/500000 := by
  dsimp [b0]
  constructor <;> linarith [diagonal_precise.1,diagonal_precise.2]

theorem b0_low : b0∈Icc 0 b1 := by
  constructor <;> linarith [b0_bounds.1,b0_bounds.2,b1_bounds.1]

theorem b0_shift_bounds : (1885379/1000000:ℝ)<A b0+1/2 ∧ A b0+1/2<943/500 := by
  have hb : b0∈Icc 0 c0 := ⟨b0_low.1,b0_low.2.trans b1_mem.2⟩
  have hc := A_circle hb
  have hp := A_shift_pos hb
  have hbL : (120157/200000:ℝ)≤b0+1/2 := by linarith [b0_bounds.1]
  have hbU : b0+1/2≤300393/500000 := by linarith [b0_bounds.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤120157/200000) hbL 2
  have hsU := pow_le_pow_left₀ (by linarith [hbL] : 0≤b0+1/2) hbU 2
  norm_num [Q0] at hc
  constructor
  · by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    nlinarith
  · by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤943/500) hbad 2
    nlinarith

theorem b0_slope_bounds : (637/2000:ℝ)<slope b0 ∧ slope b0<15933/50000 := by
  have hp := A_shift_pos (show b0∈Icc 0 c0 from ⟨b0_low.1,b0_low.2.trans b1_mem.2⟩)
  dsimp [FrameLowArc.slope]
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith [b0_shift_bounds.2,b0_bounds.1]
  · apply (div_lt_iff₀ hp).2
    linarith [b0_shift_bounds.1,b0_bounds.2]

theorem F0_lower : (17667339553/20000000000:ℝ)<F0 := by
  have hA := b0_shift_bounds.1
  have ha0 : a0<(176822/125000:ℝ) := by linarith [a0_precise.2]
  have hb := b0_bounds.1
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [F0,L,FrameLowArc.u,FrameLowArc.v]
  linarith

theorem d0_bounds : 0<d0 ∧ d0<1/10000 := by
  have hr := b0_slope_bounds
  dsimp [d0,FrameLowArc.u,FrameLowArc.v,FrameHighArc.u,FrameHighArc.v]
  constructor <;> linarith

theorem slope_c0 : slope c0=1 := by
  rw [FrameLowArc.slope,A_c0]
  exact div_self (by linarith [c0_bounds.1])

theorem parallel_domain {b : ℝ} (hb : b∈Icc b0 b1) :
    b∈Icc 0 b1 ∧ 1-b∈Icc b2 c0 := by
  constructor
  · exact ⟨b0_low.1.trans hb.1,hb.2⟩
  · constructor
    · linarith [hb.2,b1_bounds.2,b2_bounds.2]
    · dsimp [b0] at hb
      linarith [hb.1]

theorem parallel_deriv {b : ℝ} (hb : b∈Icc b0 b1) : HasDerivAt parallel (parallelD b) b := by
  have hd := parallel_domain hb
  have hm : HasDerivAt (fun y : ℝ => 1-y) (-1) b := (hasDerivAt_id' b).const_sub 1
  have h := (L_hasDerivAt hd.1).fun_add ((H_deriv hd.2).comp b hm)
  refine h.congr_deriv ?_
  simp only [parallelD]
  ring

theorem parallelD_deriv {b : ℝ} (hb : b∈Icc b0 b1) :
    HasDerivAt parallelD (parallelDD b) b := by
  have hd := parallel_domain hb
  have hm : HasDerivAt (fun y : ℝ => 1-y) (-1) b := (hasDerivAt_id' b).const_sub 1
  have h := (extended_Ld_deriv (low_extended hd.1)).fun_sub
    ((extended_Hd_deriv (high_extended hd.2)).comp b hm)
  refine h.congr_deriv ?_
  simp only [parallelDD]
  ring

theorem parallel_curvature {b : ℝ} (hb : b∈Icc b0 b1) : (1/4:ℝ)<parallelDD b := by
  have hd := parallel_domain hb
  have hs := low_slopeD_upper hd.1
  have hp := extended_shift_pos (high_extended hd.2)
  have hc := extended_circle (high_extended hd.2)
  have hbL : (47/40:ℝ)≤1-b+1/2 := by linarith [hb.2,b1_bounds.2]
  have hbsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤47/40) hbL 2
  have hA : A (1-b)+1/2<8/5 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8/5) hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hcube := pow_le_pow_left₀ hp.le hA.le 3
  have htarget : (19/20:ℝ)<slopeD (1-b) := by
    dsimp [slopeD]
    apply (lt_div_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at *
    nlinarith
  dsimp [parallelDD,FrameLowArc.u,FrameHighArc.u]
  linarith

theorem parallel_initial : parallel b0=F0 ∧ parallelD b0=d0 := by
  have he : 1-b0=c0 := by dsimp [b0]; ring
  constructor
  · rw [parallel,he,H_c0]
    rfl
  · rw [parallelD,he]
    dsimp [Ld,Hd,d0]
    rw [slope_c0]
    ring

theorem parallel_lower {b : ℝ} (hb : b∈Icc b0 b1) : F0≤parallel b := by
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (1/4:ℝ)) (fun z hz => parallel_deriv hz)
    (fun z hz => parallelD_deriv hz) (fun z hz => (parallel_curvature hz).le)
    (show b0∈Icc b0 b1 from ⟨le_rfl,b0_low.2⟩) hb
  rw [parallel_initial.1,parallel_initial.2] at hh
  have hd := mul_nonneg d0_bounds.1.le (sub_nonneg.mpr hb.1)
  nlinarith [sq_nonneg (b-b0)]

theorem parallel_contact {b B : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hm : 1≤b+B) : F0≤L b+H B := by
  have hb0 : b0≤b := by dsimp [b0]; linarith [hB.2]
  have hd := parallel_domain ⟨hb0,hb.2⟩
  have hmono := H_monotone hd.2 hB (by linarith : 1-b≤B)
  have hh := parallel_lower ⟨hb0,hb.2⟩
  dsimp [parallel] at hh
  linarith

theorem quarter_domain {b : ℝ} (hb : b∈Icc 0 b0) :
    b∈Icc 0 b1 ∧ 1-b∈extendedDomain ∧ c0≤1-b ∧ 1-b≤1 := by
  have hbU := hb.2.trans b0_low.2
  exact ⟨⟨hb.1,hbU⟩,⟨by linarith [hbU,b1_bounds.2],by linarith [hb.1]⟩,
    by dsimp [b0] at hb; linarith [hb.2],by linarith [hb.1]⟩

theorem quarter_deriv {b : ℝ} (hb : b∈Icc 0 b0) : HasDerivAt quarter (quarterD b) b := by
  have hd := quarter_domain hb
  have hm : HasDerivAt (fun y : ℝ => 1-y) (-1) b := (hasDerivAt_id' b).const_sub 1
  have h := (L_hasDerivAt hd.1).fun_add ((G_deriv hd.2.1).comp b hm)
  refine h.congr_deriv ?_
  simp only [quarterD]
  ring

theorem quarterD_deriv {b : ℝ} (hb : b∈Icc 0 b0) :
    HasDerivAt quarterD (quarterDD b) b := by
  have hd := quarter_domain hb
  have hm : HasDerivAt (fun y : ℝ => 1-y) (-1) b := (hasDerivAt_id' b).const_sub 1
  have h := (extended_Ld_deriv (low_extended hd.1)).fun_sub
    ((Gd_deriv hd.2.1).comp b hm)
  refine h.congr_deriv ?_
  simp only [quarterDD,Gdd]
  ring

theorem quarter_curvature {b : ℝ} (hb : b∈Icc 0 b0) : (1/4:ℝ)<quarterDD b := by
  have hd := quarter_domain hb
  have hbl : b∈Icc 0 c0 := ⟨hd.1.1,hd.1.2.trans b1_mem.2⟩
  have h0 : b0∈Icc 0 c0 := ⟨b0_low.1,b0_low.2.trans b1_mem.2⟩
  have hsourceA := A_antitone hbl h0 hb.2
  have hp := A_shift_pos hbl
  have hsourceCube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤47/25)
    (show (47/25:ℝ)≤A b+1/2 by linarith [hsourceA,b0_shift_bounds.1]) 3
  have hsource : slopeD b<3/5 := by
    dsimp [slopeD]
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at *
    nlinarith
  have hc0 : c0∈extendedDomain := by constructor <;> linarith [c0_bounds.1,c0_bounds.2]
  have htargetA := extended_A_antitone hc0 hd.2.1 hd.2.2.1
  rw [A_c0] at htargetA
  have htp := extended_shift_pos hd.2.1
  have htargetCube := pow_le_pow_left₀ htp.le
    (show A (1-b)+1/2≤7/5 by linarith [htargetA,c0_bounds.2]) 3
  have htarget : (7/5:ℝ)<slopeD (1-b) := by
    dsimp [slopeD]
    apply (lt_div_iff₀ (pow_pos htp 3)).2
    norm_num [Q0] at *
    nlinarith
  dsimp [quarterDD,FrameLowArc.u,FrameHighArc.v]
  linarith

theorem quarter_initial : quarter b0=F0 ∧ quarterD b0=d0 := by
  have he : 1-b0=c0 := by dsimp [b0]; ring
  constructor
  · rw [quarter,he,G_c0]
    rfl
  · rw [quarterD,he]
    dsimp [Ld,Gd,d0]
    rw [slope_c0]
    ring

theorem quarter_lower {b : ℝ} (hb : b∈Icc 0 b0) : F0-2*d0^2≤quarter b := by
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (1/4:ℝ)) (fun z hz => quarter_deriv hz)
    (fun z hz => quarterD_deriv hz) (fun z hz => (quarter_curvature hz).le)
    (show b0∈Icc 0 b0 from ⟨b0_low.1,le_rfl⟩) hb
  rw [quarter_initial.1,quarter_initial.2] at hh
  nlinarith [sq_nonneg (b-b0+4*d0)]

theorem quarter_reserve : (8833/10000:ℝ)<F0-2*d0^2 := by
  have hd := mul_pos (sub_pos.mpr d0_bounds.2)
    (show 0<(1/10000:ℝ)+d0 by linarith [d0_bounds.1])
  nlinarith [F0_lower]

end SquaresInCircles.Eight.FrameLowHighAligned
