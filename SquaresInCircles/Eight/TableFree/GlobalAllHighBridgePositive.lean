module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgeHigh

/-!
# Both original bridge owners at nonnegative error

The original complementary-cycle cap forces the high/low chart pair.
A Lipschitz bound for the low potential compares directly with an
aligned point on the same whole low arc.  The comparison does not
transfer the cycle cap or any other edge to that point.  Uncompiled
source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor GlobalZeroSign FrameCircleArc FrameLowArc FrameMidArc

theorem positive_chart_pair (s t : State) (hs : s.branch.type≠0) (ht : t.branch.type≠0)
    {d : ℝ} (hd : d∈Icc 0 frameCap)
    (hc : augmentedOld s t d<cap-bonus s.branch.type t.branch.type) :
    s.branch=.high ∧ t.branch=.low := by
  have hw := frameCost_nonneg (show d∈Icc 0 (Real.pi/4) from
    ⟨hd.1,by dsimp [frameCap] at hd; linarith [hd.2,Real.pi_gt_three]⟩)
  have hb := bonus_nonnegative s.branch.type t.branch.type
  have hsF := marker_outer_bounds s hs
  have htF := marker_outer_bounds t ht
  rw [augmentedOld,oldCharge,abs_of_nonneg hd.1] at hc
  constructor
  · by_contra hn
    have hh := marker_nonhigh_upper s hs hn
    dsimp [cap] at hc
    linarith [Arithmetic.pi_hand_enclosure.1,hd.1,htF.1]
  · by_contra hn
    have hh := marker_nonlow_lower t ht hn
    dsimp [cap] at hc
    linarith [Arithmetic.pi_hand_enclosure.1,hd.1,hsF.2]

theorem low_potential_deriv {b : ℝ} (hb : b∈Icc 0 b1) :
    HasDerivAt (arcPotential .low)
      ((406817/10000000)*slope b-7679969/10000000) b := by
  have hh := ((hasDerivAt_const b (rho*(FrameHighArc.k+FrameLowArc.u*a0))).sub
    ((A_hasDerivAt ⟨hb.1,hb.2.trans b1_mem.2⟩).const_mul (406817/10000000))).sub
    ((hasDerivAt_id b).const_mul (7679969/10000000))
  convert hh using 1
  · ext x
    exact arcPotential_low x
  · simp only [Ad,FrameLowArc.slope]
    ring

theorem low_potential_derivative_bounds {b : ℝ} (hb : b∈Icc 0 b1) :
    -(96/125:ℝ)≤(406817/10000000)*slope b-7679969/10000000 ∧
    (406817/10000000)*slope b-7679969/10000000≤0 := by
  have hh := slope_bounds hb
  constructor <;> linarith

theorem low_potential_antitone : AntitoneOn (arcPotential .low) (Icc 0 b1) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (low_potential_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => low_potential_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (low_potential_derivative_bounds (Ioo_subset_Icc_self hb)).2

theorem low_potential_add_monotone :
    MonotoneOn (fun b => arcPotential .low b+(96/125)*b) (Icc 0 b1) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact ((low_potential_deriv hb).add
      ((hasDerivAt_id b).const_mul (96/125))).continuousAt.continuousWithinAt
  · intro b hb
    exact (low_potential_deriv (Ioo_subset_Icc_self hb)).add
      ((hasDerivAt_id b).const_mul (96/125))
  · intro b hb
    linarith [(low_potential_derivative_bounds (Ioo_subset_Icc_self hb)).1]

/-- Either original high owner pays the same small displacement of
the target transverse coordinate. -/
theorem positive_projection_gap (s t : State)
    (hs : s.branch=.high) {d : ℝ} (hd : d∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width d≤ s.a*Real.cos d+s.b*Real.sin d+t.b ∨
      GlobalOuterAnchor.width d≤ s.a+t.a*Real.sin d+t.b*Real.cos d) :
    1-s.a-t.b≤(109/100)*d := by
  have tr := transport_trig hd
  have hsine := Real.sin_le hd.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=d)
  have hpow := mul_le_mul_of_nonneg_right hd.2 hd.1
  have hsource := FrameHighArc.state_high_chart s hs
  have hsa : 1/2≤ s.a := by
    rw [hsource.1]
    linarith [(FrameHighArc.A_high_bounds hsource.2).1,c0_precise.1]
  have hsb : s.b≤9/10 := by linarith [hsource.2.2,c0_precise.2]
  have htA := (coordinates t).2.1
  have hdrop : 0≤1-Real.cos d := sub_nonneg.mpr tr.2.1
  rw [GlobalOuterAnchor.width,abs_of_nonneg tr.2.2.1] at hm
  rcases hm with hm | hm
  · have h1 := mul_nonneg (show 0≤ s.a-1/2 by linarith) hdrop
    have h2 := mul_nonneg (show 0≤9/10-s.b by linarith) tr.2.2.1
    nlinarith only [hm,h1,h2,hsine,hd.1]
  · have h1 := mul_nonneg t.b_nonneg hdrop
    have h2 := mul_nonneg (show 0≤283/200-t.a by linarith) tr.2.2.1
    dsimp [frameCap] at hpow
    nlinarith only [hm,h1,h2,hsine,hcos,hpow]

theorem positive_charge (s t : State) (hs : s.branch.type≠0) (ht : t.branch.type≠0)
    {d : ℝ} (hd : d∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width d≤ s.a*Real.cos d+s.b*Real.sin d+t.b ∨
      GlobalOuterAnchor.width d≤ s.a+t.a*Real.sin d+t.b*Real.cos d)
    (hc : augmentedOld s t d<cap-bonus s.branch.type t.branch.type) :
    (24/25:ℝ)<charge s t d := by
  have hcharts := positive_chart_pair s t hs ht hd hc
  have hsH := hcharts.1
  have htL := hcharts.2
  have hsource := FrameHighArc.state_high_chart s hsH
  have htarget := state_low_chart t htL
  let B0 : ℝ := max 0 (1-s.a)
  have hB0 : B0∈Icc 0 b1 := by
    refine ⟨le_max_left _ _,max_le ?_ ?_⟩
    · exact b1_mem.1
    · have hsa := (FrameHighArc.A_high_bounds hsource.2).1
      rw [← hsource.1] at hsa
      linarith [c0_precise.1,b1_precise.1]
  have halign := high_low_aligned s hsH hB0
    (show 1≤ s.a+B0 by dsimp [B0]; linarith [le_max_right (0:ℝ) (1-s.a)])
  rw [charge,potential_high s hsH,potential_arc t ht,htL]
  by_cases horder : B0≤t.b
  · have hp := low_potential_antitone hB0 htarget.2 horder
    linarith [hd.1]
  · have hBlt : t.b<B0 := lt_of_not_ge horder
    have hBpos : 0<B0 := lt_of_le_of_lt t.b_nonneg hBlt
    have hB0eq : B0=1-s.a := by
      have ha : 0≤1-s.a := by
        by_contra! hn
        have hzero : B0=0 := max_eq_left hn.le
        linarith
      exact max_eq_right ha
    have hg := positive_projection_gap s t hsH hd hm
    have hp := low_potential_add_monotone htarget.2 hB0 hBlt.le
    have hgap : B0-t.b≤(109/100)*d := by rw [hB0eq]; exact hg
    have hscaled := mul_le_mul_of_nonneg_left hgap (show (0:ℝ)≤96/125 by norm_num)
    linarith [hd.1]

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge
