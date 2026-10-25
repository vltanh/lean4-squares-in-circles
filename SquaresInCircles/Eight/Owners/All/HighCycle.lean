module

public import SquaresInCircles.Eight.Owners.All.HighBridgeTransfer
public import SquaresInCircles.Eight.Owners.All.HighZeroNegative
public import SquaresInCircles.Eight.Owners.All.HighQuarter
public import SquaresInCircles.Eight.Owners.All.HighCycleComponents

/-!
# Eight squares: exclusion of the complete original all-high quarter branch

The actual DE cap, its complete owner theorem, all three repeated
quarter charges and the shared three-zero loss now telescope on one
physical cycle.  Fixed-ray expansion preserves every supplied original
weak axis, so the exclusion holds at the original radius.
-/

section
/-!
## Bridge bounds from a high source at nonpositive error

From a source on the high chart the charge at error `-z` exceeds `24/25`: for a low target on the
whole error interval (`high_low_negative`), and for a middle or high target directly when
`z ≤ 1/2` (`high_nonlow_short`). On the long interval `1/2 ≤ z` the cycle cap excludes the middle
and high targets, so the bound holds for every outer target under the cap (`high_negative`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor FrameCircleArc FrameLowArc FrameMidArc

theorem high_source_dual (s : State) (hs : s.branch=.high)
    {z lambda g targetPotential targetB lower : ℝ}
    (hz : z∈Icc 0 frameCap) (hl : lambda∈Icc 0 (151/200:ℝ))
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+targetB)
    (ht : g< -targetPotential-lambda*targetB)
    (hcut : lower<endpoint lambda g a2 b2 z)
    (hdiag : lower<endpoint lambda g c0 c0 z) :
    lower<Real.pi/2-z+kappa*s.a-targetPotential := by
  have tr := transport_trig hz
  have hcoef : 0≤kappa-lambda*Real.cos z := by
    have hh := mul_le_mul_of_nonneg_left tr.2.1 hl.1
    dsimp [kappa]
    linarith [hl.2]
  have hchart := FrameHighArc.state_high_chart s hs
  have hh := linear_endpoint_lower (p := kappa-lambda*Real.cos z)
    (q := lambda*Real.sin z) hcoef b2_mem.1 le_rfl hchart.2
  have he : lower-(Real.pi/2-z+g+lambda*GlobalOuterAnchor.width (-z))<
      min (linear (kappa-lambda*Real.cos z) (lambda*Real.sin z) b2)
        (linear (kappa-lambda*Real.cos z) (lambda*Real.sin z) c0) := by
    apply lt_min
    · rw [linear,A_b2]
      rw [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1]
      dsimp [endpoint] at hcut
      nlinarith only [hcut]
    · rw [linear,A_c0]
      rw [GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1]
      dsimp [endpoint] at hdiag
      nlinarith only [hdiag]
  have hsource := he.trans_le hh
  dsimp [linear] at hsource
  rw [← hchart.1] at hsource
  have hp := mul_le_mul_of_nonneg_left hm hl.1
  nlinarith only [hsource,hp,ht]

theorem high_low_negative (s t : State) (hs : s.branch=.high) (ht : t.branch=.low)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b) :
    (24/25:ℝ)<charge s t (-z) := by
  have htarget : (-403/250:ℝ)< -potential t-(151/200)*t.b := by
    rw [potential_arc t (by simp [ht,Branch.type]),ht]
    have h := low_target_bound (state_low_chart t ht).2
    linarith
  have hcut := cut_endpoint_bounds.1.trans_le
    (cut_endpoint_antitone (g := (-403/250:ℝ))
      (by norm_num : (151/200:ℝ)∈Icc 0 (151/200)) hz
      ⟨by norm_num [frameCap],le_rfl⟩ hz.2)
  have hh := high_source_dual s hs hz (by norm_num : (151/200:ℝ)∈Icc 0 (151/200))
    hm htarget hcut (diagonal_low_endpoint hz)
  rw [charge,potential_high s hs]
  linarith

theorem high_nonlow_short (s t : State) (hs : s.branch=.high)
    (ht : t.branch=.middle ∨ t.branch=.high) {z : ℝ} (hz : z∈Icc 0 (1/2:ℝ))
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b) :
    (24/25:ℝ)<charge s t (-z) := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have htarget : (-1999/1250:ℝ)< -potential t-(69/100)*t.b := by
    linarith [nonlow_target_bound t ht]
  have hcut := cut_endpoint_bounds.2.trans_le
    (cut_endpoint_antitone (g := (-1999/1250:ℝ))
      (by norm_num : (69/100:ℝ)∈Icc 0 (151/200)) hz'
      (by norm_num [frameCap] : (1/2:ℝ)∈Icc 0 frameCap) hz.2)
  have hh := high_source_dual s hs hz' (by norm_num : (69/100:ℝ)∈Icc 0 (151/200))
    hm htarget hcut (diagonal_nonlow_endpoint hz)
  rw [charge,potential_high s hs]
  linarith

theorem high_negative (s t : State) (hs : s.branch=.high) (ht : t.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedUnsigned s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (24/25:ℝ)<charge s t (-z) := by
  by_cases htL : t.branch=.low
  · exact high_low_negative s t hs htL hz hm
  have ht' : t.branch=.middle ∨ t.branch=.high := by
    cases hj : t.branch <;> simp [hj,Branch.type] at ht htL ⊢
  by_cases hshort : z≤1/2
  · exact high_nonlow_short s t hs ht' ⟨hz.1,hshort⟩ hm
  · exact (high_source_long_false s t hs ht' ⟨(lt_of_not_ge hshort).le,hz.2⟩ hm hc).elim

/-- The aligned comparison on the low arc: for a high source and `B ∈ [0, b1]` with
`1 ≤ s.a + B`, `π/2 + kappa * s.a - arcPotential .low B` exceeds `24/25`. -/
theorem high_low_aligned (s : State) (hs : s.branch=.high)
    {B : ℝ} (hB : B∈Icc 0 b1) (hm : 1≤ s.a+B) :
    (24/25:ℝ)<Real.pi/2+kappa*s.a-arcPotential .low B := by
  have htarget : (-403/250:ℝ)< -arcPotential .low B-(151/200)*B := by
    linarith [low_target_bound hB]
  have hcut := cut_endpoint_bounds.1.trans_le
    (cut_endpoint_antitone (g := (-403/250:ℝ))
      (by norm_num : (151/200:ℝ)∈Icc 0 (151/200))
      (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
      ⟨by norm_num [frameCap],le_rfl⟩ (by norm_num [frameCap]))
  have hp : GlobalOuterAnchor.width (-(0:ℝ))≤ s.a*Real.cos 0-s.b*Real.sin 0+B := by
    simpa [GlobalOuterAnchor.width] using hm
  have hh := high_source_dual s hs
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
    (by norm_num : (151/200:ℝ)∈Icc 0 (151/200)) hp htarget hcut
    (diagonal_low_endpoint (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap))
  simpa using hh

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end

section
/-!
## Both original bridge owners at nonnegative error

The original complementary-cycle cap forces the high/low chart pair.
A Lipschitz bound for the low potential compares directly with an
aligned point on the same whole low arc.  The comparison does not
transfer the cycle cap or any other edge to that point.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor GlobalZeroSign FrameCircleArc FrameLowArc FrameMidArc

theorem positive_chart_pair (s t : State) (hs : s.branch.type≠0) (ht : t.branch.type≠0)
    {d : ℝ} (hd : d∈Icc 0 frameCap)
    (hc : augmentedUnsigned s t d<cap-bonus s.branch.type t.branch.type) :
    s.branch=.high ∧ t.branch=.low := by
  have hw := frameCost_nonneg (show d∈Icc 0 (Real.pi/4) from
    ⟨hd.1,by dsimp [frameCap] at hd; linarith [hd.2,Real.pi_gt_three]⟩)
  have hb := bonus_nonnegative s.branch.type t.branch.type
  have hsF := marker_outer_bounds s hs
  have htF := marker_outer_bounds t ht
  rw [augmentedUnsigned,unsignedCharge,abs_of_nonneg hd.1] at hc
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
    (hc : augmentedUnsigned s t d<cap-bonus s.branch.type t.branch.type) :
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

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end

section
/-!
## The owners of a negative outer bridge

Between outer states with nonpositive transverse coordinates, a weak witness of owner `2` or `3`
gives one of two projections (`original_owner_projection`). Either projection, with the cycle cap
stated with the two markers, makes the charge exceed `957/1000` (`negative_charge`,
`owner_charge`), for every source and target chart and both signs of the error.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor GlobalZeroSign FrameCircleArc FrameLowArc FrameMidArc

theorem low_nonlow_bonus (s t : State) (hs : s.branch=.low)
    (ht : t.branch=.middle ∨ t.branch=.high) :
    (93/10000:ℝ)≤bonus s.branch.type t.branch.type := by
  rcases ht with ht | ht <;> norm_num [hs,ht,Branch.type,bonus,tau]

theorem middle_nonlow_bonus (s t : State) (hs : s.branch=.middle)
    (ht : t.branch=.middle ∨ t.branch=.high) :
    (43/2500:ℝ)≤bonus s.branch.type t.branch.type := by
  rcases ht with ht | ht <;> norm_num [hs,ht,Branch.type,bonus,tau]

theorem circleScalar_expand {z : ℝ} (hz : z∈Icc 0 frameCap)
    (mu lambda K g bonus : ℝ) :
    circleScalar mu lambda K g bonus z=
      (1+mu)*(Real.pi/2-z)-mu*(cap-bonus)+K+g+lambda*GlobalOuterAnchor.width (-z)+
        mu*(9/50)*frameCost z+(lambda/2)*(Real.cos z-Real.sin z)-R*sourceNorm mu lambda z := by
  have tr := transport_trig hz
  rw [circleScalar,circleBase,GlobalOuterAnchor.width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1]
  dsimp [frameCost]
  ring

theorem low_low_negative (s t : State) (hs : s.branch=.low) (ht : t.branch=.low)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedUnsigned s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (957/1000:ℝ)<charge s t (-z) := by
  have hdual := negative_dual s t hz (by norm_num : (0:ℝ)≤17/10)
    (by norm_num : (0:ℝ)≤59/25) hm hc
  have hsource := low_source_low_target s hs hz
  have htarget := low_dual_target t ht
  have hscalar := low_low_scalar hz
  have hb : bonus s.branch.type t.branch.type=0 := by norm_num [hs,ht,Branch.type,bonus,tau]
  rw [hb] at hdual
  dsimp [endpointScalar] at hscalar
  nlinarith only [hdual,hsource,htarget,hscalar]

theorem low_nonlow_negative (s t : State) (hs : s.branch=.low)
    (ht : t.branch=.middle ∨ t.branch=.high) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedUnsigned s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (957/1000:ℝ)<charge s t (-z) := by
  have hdual := negative_dual s t hz (by norm_num : (0:ℝ)≤5)
    (by norm_num : (0:ℝ)≤93/20) hm hc
  have hsource := low_source_nonlow_target s hs hz
  have htarget := nonlow_dual_target t ht
  have hscalar := low_nonlow_scalar hz
  have hb := low_nonlow_bonus s t hs ht
  dsimp [endpointScalar] at hscalar
  nlinarith only [hdual,hsource,htarget,hscalar,hb]

theorem middle_low_negative (s t : State) (hs : s.branch=.middle) (ht : t.branch=.low)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedUnsigned s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (957/1000:ℝ)<charge s t (-z) := by
  have hdual := negative_dual s t hz (by norm_num : (0:ℝ)≤17/10)
    (by norm_num : (0:ℝ)≤59/25) hm hc
  have hsource := middle_source_support s hs (17/10) (59/25) z
  have hconstant := dual_endpoint_constants.2.2.1
  have htarget := low_dual_target t ht
  have hscalar := middle_low_scalar hz
  rw [circleScalar_expand hz] at hscalar
  have hb : bonus s.branch.type t.branch.type=93/10000 := by
    norm_num [hs,ht,Branch.type,bonus,tau]
  rw [hb] at hdual
  nlinarith only [hdual,hsource,hconstant,htarget,hscalar]

theorem middle_nonlow_negative (s t : State) (hs : s.branch=.middle)
    (ht : t.branch=.middle ∨ t.branch=.high) {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedUnsigned s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (957/1000:ℝ)<charge s t (-z) := by
  have hdual := negative_dual s t hz (by norm_num : (0:ℝ)≤5)
    (by norm_num : (0:ℝ)≤93/20) hm hc
  have hsource := middle_source_support s hs 5 (93/20) z
  have hconstant := dual_endpoint_constants.2.2.2
  have htarget := nonlow_dual_target t ht
  have hscalar := middle_nonlow_scalar hz
  rw [circleScalar_expand hz] at hscalar
  have hb := middle_nonlow_bonus s t hs ht
  nlinarith only [hdual,hsource,hconstant,htarget,hscalar,hb]

theorem negative_charge (s t : State) (hs : s.branch.type≠0) (ht : t.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width (-z)≤ s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedUnsigned s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (957/1000:ℝ)<charge s t (-z) := by
  cases hsBr : s.branch with
  | coreSide | coreCorner => simp [hsBr,Branch.type] at hs
  | high => linarith [high_negative s t hsBr ht hz hm hc]
  | low =>
      by_cases htL : t.branch=.low
      · exact low_low_negative s t hsBr htL hz hm hc
      · have ht' : t.branch=.middle ∨ t.branch=.high := by
          cases hj : t.branch <;> simp [hj,Branch.type] at ht htL ⊢
        exact low_nonlow_negative s t hsBr ht' hz hm hc
  | middle =>
      by_cases htL : t.branch=.low
      · exact middle_low_negative s t hsBr htL hz hm hc
      · have ht' : t.branch=.middle ∨ t.branch=.high := by
          cases hj : t.branch <;> simp [hj,Branch.type] at ht htL ⊢
        exact middle_nonlow_negative s t hsBr ht' hz hm hc

theorem original_owner_projection (s t : State)
    (hsy : transverse s≤0) (hty : transverse t≤0) {j : Fin 4} {d : ℝ}
    (hj : j=2 ∨ j=3) (hd : |d|≤frameCap)
    (hm : s.Feasible t j (Real.pi/2+d)) :
    GlobalOuterAnchor.width d≤ s.a*Real.cos d+s.b*Real.sin d+t.b ∨
      GlobalOuterAnchor.width d≤ s.a+t.a*Real.sin d+t.b*Real.cos d := by
  have hty' : transverse t= -t.b := transverse_nonpos_eq t hty
  rcases hj with rfl | rfl
  · have hh := (right_margin s t false hd hsy).1 (by simpa [rightOwner] using hm)
    left
    simpa [rightProjection,hty'] using hh
  · have hh := (right_margin s t true hd hsy).1 (by simpa [rightOwner] using hm)
    right
    simpa [rightProjection,hty'] using hh

/-- A weak witness of owner `2` or `3` between outer states with nonpositive transverse
coordinates, under the cycle cap, makes the charge exceed `957/1000`. -/
theorem owner_charge (s t : State) (hs : s.branch.type≠0) (ht : t.branch.type≠0)
    (hsy : transverse s≤0) (hty : transverse t≤0) {j : Fin 4} {d : ℝ}
    (hj : j=2 ∨ j=3) (hd : |d|≤frameCap)
    (hm : s.Feasible t j (Real.pi/2+d))
    (hc : augmentedUnsigned s t d<cap-bonus s.branch.type t.branch.type) :
    (957/1000:ℝ)<charge s t d := by
  have hp := original_owner_projection s t hsy hty hj hd hm
  by_cases hdpos : 0≤d
  · have hh := positive_charge s t hs ht ⟨hdpos,(le_abs_self d).trans hd⟩ hp hc
    linarith
  · have hz : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hp2 : GlobalOuterAnchor.width (-(-d))≤ s.a*Real.cos (-d)-s.b*Real.sin (-d)+t.b := by
      rcases hp with hp | hp
      · simpa only [neg_neg,Real.cos_neg,Real.sin_neg,mul_neg,sub_neg_eq_add] using hp
      · have hcompare := negative_outer_projection_comparison s t ht hz
        have hp' : GlobalOuterAnchor.width d≤ s.a-t.a*Real.sin (-d)+t.b*Real.cos (-d) := by
          simpa only [Real.cos_neg,Real.sin_neg,mul_neg,sub_neg_eq_add] using hp
        simpa only [neg_neg] using hp'.trans hcompare
    have hh := negative_charge s t hs ht hz hp2 (by simpa only [neg_neg] using hc)
    simpa only [neg_neg] using hh

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalAllHigh

open Candidate FramePair GlobalOuterAnchor

theorem frame_DE_charge {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) :
    (957/1000:ℝ)<cycleCharge C F.theta D := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hD := GlobalQuarterOuter.frame_high_anchor F hq D (by norm_num [word,D])
    (owner D) (hhigh D (by norm_num [word,D])) (hf D)
  have hE := GlobalQuarterOuter.frame_high_anchor F hq E (by norm_num [word,E])
    (owner E) (hhigh E (by norm_num [word,E])) (hf E)
  have hDy := (state_negative_of_tangent C D hD.2).le
  have hEy := (state_negative_of_tangent C E hE.2).le
  have hcap := Bridge.original_cap F hDy hEy
  have haxis := frame_state_feasible F D (owner D) (hf D)
  have haxis' : (stateOf C D).Feasible (stateOf C E) (owner D)
      (Real.pi/2+delta F.theta D) := by
    simpa [Candidate.phi,word,D,E,next] using haxis
  have hh := Bridge.owner_charge (stateOf C D) (stateOf C E)
    (state_outer_of_kind C D hD.1) (state_outer_of_kind C E hE.1) hDy hEy
    (hhigh D (by norm_num [word,D]))
    (by simpa only [frameCap] using (F.delta_small D).le) haxis' hcap
  rw [cycleCharge_DE]
  exact hh

theorem strict_cyclic_reserve :
    Real.pi/2<6*kappa*(1-FramePair.c0)+19/20 := by
  have hc := Bridge.c0_precise.2
  have hp := Arithmetic.two_pi_lt_710_over_113
  dsimp [kappa]
  linarith

theorem ceiling_all_high_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) : False := by
  have hquarter := frame_three_quarters F owner hf hhigh
  have hzero := frame_three_zeros F owner hf hhigh
  have hDE := frame_DE_charge F owner hf hhigh
  have hsum := cycleCharge_sum C F.theta
  rw [Fin.sum_univ_seven] at hsum
  dsimp [H,G,A,B,T,D,E,gammaZero] at hquarter hzero hDE
  have hr := strict_cyclic_reserve
  linarith only [hquarter,hzero,hDE,hsum,hr]

/-- Every supplied axis survives the fixed-ray expansion.  The
contradiction therefore classifies the original witnesses at q. -/
theorem frame_all_high_false {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (hq : q∈Icc (5/2:ℝ) Q0) (owner : Vertex→Fin 4)
    (hf : ∀i,(forwardAxis (owner i)).Feasible (C.square i) (C.square (next i)))
    (hhigh : ∀i,word i=1 → owner i=2 ∨ owner i=3) : False := by
  let K := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C K := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame K := FramePhysicalTransport.candidatePushforward F hR le_rfl
  apply ceiling_all_high_false F' owner
  · intro i
    exact hR.preserves_all_axes i (forwardAxis (owner i)) (hf i)
  · exact hhigh

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end
