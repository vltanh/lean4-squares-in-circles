module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgeHighSupports

/-!
# Complete high-source bridge bounds at nonpositive error

The low target is covered on the whole error interval.  Middle and
high targets have a direct short-interval bound, and their complete
long interval is excluded by the original cycle cap.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor FrameCircleArc FrameLowArc FrameMidArc

theorem high_source_dual (s : State) (hs : s.branch=.high)
    {z lambda g targetPotential targetB lower : ℝ}
    (hz : z∈Icc 0 frameCap) (hl : lambda∈Icc 0 (151/200:ℝ))
    (hm : width (-z)≤s.a*Real.cos z-s.b*Real.sin z+targetB)
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
  have he : lower-(Real.pi/2-z+g+lambda*width (-z))<
      min (linear (kappa-lambda*Real.cos z) (lambda*Real.sin z) b2)
        (linear (kappa-lambda*Real.cos z) (lambda*Real.sin z) c0) := by
    apply lt_min
    · rw [linear,A_b2]
      rw [width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1]
      dsimp [endpoint] at hcut
      nlinarith only [hcut]
    · rw [linear,A_c0]
      rw [width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg tr.2.2.1]
      dsimp [endpoint] at hdiag
      nlinarith only [hdiag]
  have hsource := he.trans_le hh
  dsimp [linear] at hsource
  rw [← hchart.1] at hsource
  have hp := mul_le_mul_of_nonneg_left hm hl.1
  nlinarith only [hsource,hp,ht]

theorem high_low_negative (s t : State) (hs : s.branch=.high) (ht : t.branch=.low)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : width (-z)≤s.a*Real.cos z-s.b*Real.sin z+t.b) :
    (24/25:ℝ)<charge s t (-z) := by
  have htarget : -(403/250:ℝ)< -potential t-(151/200)*t.b := by
    rw [potential_arc t (by simp [ht,Branch.type]),ht]
    exact low_target_bound (state_low_chart t ht).2
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
    (hm : width (-z)≤s.a*Real.cos z-s.b*Real.sin z+t.b) :
    (24/25:ℝ)<charge s t (-z) := by
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩
  have hcut := cut_endpoint_bounds.2.trans_le
    (cut_endpoint_antitone (g := (-1999/1250:ℝ))
      (by norm_num : (69/100:ℝ)∈Icc 0 (151/200)) hz'
      (by norm_num [frameCap] : (1/2:ℝ)∈Icc 0 frameCap) hz.2)
  have hh := high_source_dual s hs hz' (by norm_num : (69/100:ℝ)∈Icc 0 (151/200))
    hm (nonlow_target_bound t ht) hcut (diagonal_nonlow_endpoint hz)
  rw [charge,potential_high s hs]
  linarith

theorem high_negative (s t : State) (hs : s.branch=.high) (ht : t.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : width (-z)≤s.a*Real.cos z-s.b*Real.sin z+t.b)
    (hc : augmentedOld s t (-z)<cap-bonus s.branch.type t.branch.type) :
    (24/25:ℝ)<charge s t (-z) := by
  by_cases htL : t.branch=.low
  · exact high_low_negative s t hs htL hz hm
  have ht' : t.branch=.middle ∨ t.branch=.high := by
    cases hj : t.branch <;> simp [hj,Branch.type] at ht htL ⊢
  by_cases hshort : z≤1/2
  · exact high_nonlow_short s t hs ht' ⟨hz.1,hshort⟩ hm
  · exact (high_source_long_false s t hs ht' ⟨(lt_of_not_ge hshort).le,hz.2⟩ hm hc).elim

/-- The aligned comparison is evaluated on the actual low arc, with
no replacement state or cap assumption at that point. -/
theorem high_low_aligned (s : State) (hs : s.branch=.high)
    {B : ℝ} (hB : B∈Icc 0 b1) (hm : 1≤s.a+B) :
    (24/25:ℝ)<Real.pi/2+kappa*s.a-arcPotential .low B := by
  have htarget := low_target_bound hB
  have hcut := cut_endpoint_bounds.1.trans_le
    (cut_endpoint_antitone (g := (-403/250:ℝ))
      (by norm_num : (151/200:ℝ)∈Icc 0 (151/200))
      (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
      ⟨by norm_num [frameCap],le_rfl⟩ (by norm_num [frameCap]))
  have hp : width (-(0:ℝ))≤s.a*Real.cos 0-s.b*Real.sin 0+B := by
    simpa [width] using hm
  have hh := high_source_dual s hs
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
    (by norm_num : (151/200:ℝ)∈Icc 0 (151/200)) hp htarget hcut
    (diagonal_low_endpoint (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap))
  simpa using hh

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge
