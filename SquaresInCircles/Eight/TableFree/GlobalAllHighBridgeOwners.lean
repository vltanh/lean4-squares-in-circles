module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgeTransfer

/-!
# The complete original negative-outer bridge owner theorem

All source and target charts, both error signs and both original high
owners are joined here.  The one cap used is stated with the original
two markers; its physical six-edge derivation is separate.  Uncompiled
source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge

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
    (hc : augmentedOld s t (-z)<cap-bonus s.branch.type t.branch.type) :
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
    (hc : augmentedOld s t (-z)<cap-bonus s.branch.type t.branch.type) :
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
    (hc : augmentedOld s t (-z)<cap-bonus s.branch.type t.branch.type) :
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
    (hc : augmentedOld s t (-z)<cap-bonus s.branch.type t.branch.type) :
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
    (hc : augmentedOld s t (-z)<cap-bonus s.branch.type t.branch.type) :
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

/-- Complete original high-owner bridge theorem.  Every marker, sign,
radial chart and weak original axis is retained. -/
theorem owner_charge (s t : State) (hs : s.branch.type≠0) (ht : t.branch.type≠0)
    (hsy : transverse s≤0) (hty : transverse t≤0) {j : Fin 4} {d : ℝ}
    (hj : j=2 ∨ j=3) (hd : |d|≤frameCap)
    (hm : s.Feasible t j (Real.pi/2+d))
    (hc : augmentedOld s t d<cap-bonus s.branch.type t.branch.type) :
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

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge
