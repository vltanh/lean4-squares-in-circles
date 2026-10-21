module

public import SquaresInCircles.Eight.TableFree.FrameLowMidEndpointScalars

/-!
# Original negative-target transverse separators

The source supports are proved on the entire original source arc.
Concavity, or monotonicity when the primary coefficient is negative,
reduces the target to the two intrinsic endpoints.  Weak separator ties
are retained throughout.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidSecondaryEndpoints
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidGeometry

theorem low_mid_negative_target (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (FrameLowMidEndpointScalars.start i) (Real.pi/2))
    (hm : 0≤secondary i false b B x) : (1801/2000:ℝ)<lowMidCost i false b B x := by
  let λ := FrameLowMidEndpointScalars.lam i
  have hλ : 0≤λ := by cases i <;> norm_num [λ,FrameLowMidEndpointScalars.lam]
  have hx0 : 0≤x := by
    have hh : 0≤FrameLowMidEndpointScalars.start i := by
      cases i <;> norm_num [FrameLowMidEndpointScalars.start]
    exact hh.trans hx.1
  have hxq : x∈Icc 0 (Real.pi/2) := ⟨hx0,hx.2⟩
  have ht := FrameLowPair.quadrant hxq
  have hs : -FrameLowMidEndpointScalars.error i≤sign i*(L b-λ*b) := by
    cases i with
    | false => simpa [λ,FrameLowMidEndpointScalars.lam,FrameLowMidEndpointScalars.error,sign]
        using low_unit_source hb
    | true => simpa [λ,FrameLowMidEndpointScalars.lam,FrameLowMidEndpointScalars.error,sign]
        using low_positive_source hb
  have hscaled := mul_nonneg hλ hm
  have hp : 0≤FrameMidArc.p-λ*Real.sin x := by
    cases i <;> dsimp [λ,FrameLowMidEndpointScalars.lam,FrameMidArc.p] <;> linarith [ht.2.1]
  have htarget := linear_endpoint_lower (p := FrameMidArc.p-λ*Real.sin x)
    (q := FrameMidArc.q-λ*Real.cos x) hp b1_mem.1 b2_mem.2 hB
  simp only [linear,A_b1,A_b2] at htarget
  dsimp [secondary] at hscaled
  rw [(first_width hxq).1] at hscaled
  have hmin : min (FrameLowMidEndpointScalars.F i false x)
      (FrameLowMidEndpointScalars.F i true x)≤lowMidCost i false b B x := by
    rcases le_total ((FrameMidArc.p-λ*Real.sin x)*a1+(FrameMidArc.q-λ*Real.cos x)*b1)
      ((FrameMidArc.p-λ*Real.sin x)*a2+(FrameMidArc.q-λ*Real.cos x)*b2) with he | he
    · rw [min_eq_left he] at htarget
      apply (min_le_left _ _).trans
      dsimp [FrameLowMidEndpointScalars.F,FrameLowMidEndpointScalars.P,
        FrameLowMidEndpointScalars.Q,FrameLowMidEndpointScalars.midA,
        FrameLowMidEndpointScalars.midB,FrameLowMidEndpointScalars.midLabel,
        lowMidCost,M,M1]
      rw [(first_width hxq).2]
      change -FrameLowMidEndpointScalars.error i≤sign i*(L b-FrameLowMidEndpointScalars.lam i*b) at hs
      dsimp [λ,sign] at hs hscaled htarget ⊢
      nlinarith
    · rw [min_eq_right he] at htarget
      apply (min_le_right _ _).trans
      dsimp [FrameLowMidEndpointScalars.F,FrameLowMidEndpointScalars.P,
        FrameLowMidEndpointScalars.Q,FrameLowMidEndpointScalars.midA,
        FrameLowMidEndpointScalars.midB,FrameLowMidEndpointScalars.midLabel,
        lowMidCost,M,M2]
      rw [(first_width hxq).2]
      change -FrameLowMidEndpointScalars.error i≤sign i*(L b-FrameLowMidEndpointScalars.lam i*b) at hs
      dsimp [λ,sign] at hs hscaled htarget ⊢
      nlinarith
  exact (lt_min (FrameLowMidEndpointScalars.F_lower i false hx)
    (FrameLowMidEndpointScalars.F_lower i true hx)).trans_le hmin

theorem low_target_endpoint {B x : ℝ} (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) :
    min (linear (FrameLowArc.u-(189/200)*Real.sin x)
      (FrameLowArc.v-(189/200)*Real.cos x) 0)
      (linear (FrameLowArc.u-(189/200)*Real.sin x)
        (FrameLowArc.v-(189/200)*Real.cos x) b1)≤
      linear (FrameLowArc.u-(189/200)*Real.sin x)
        (FrameLowArc.v-(189/200)*Real.cos x) B := by
  by_cases hp : 0≤FrameLowArc.u-(189/200)*Real.sin x
  · exact linear_endpoint_lower hp (by norm_num) b1_mem.2 hB
  · have hq : 0≤FrameLowArc.v-(189/200)*Real.cos x := by
      dsimp [FrameLowArc.v]
      linarith [Real.cos_le_one x]
    exact (min_le_left _ _).trans
      (linear_monotone (le_of_not_ge hp) hq
        ⟨le_rfl,by linarith [c0_bounds.1]⟩ ⟨hB.1,hB.2.trans b1_mem.2⟩ hB.1)

theorem mid_low_positive_negative {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (11/100:ℝ) (16/25)) (hm : 0≤secondary true false b B x) :
    (1801/2000:ℝ)<midLowCost true false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := middle_positive_source hb (show (4/5:ℝ)≤189/200 by norm_num)
  have hscaled := mul_nonneg (show (0:ℝ)≤189/200 by norm_num) hm
  have ht := low_target_endpoint hB hxq
  simp only [linear,A_zero,A_b1,mul_zero,add_zero] at ht
  dsimp [secondary] at hscaled
  rw [(first_width hxq).1] at hscaled
  norm_num [sign] at hscaled
  have hmin : min (FrameLowMidEndpointScalars.reverseF false x)
      (FrameLowMidEndpointScalars.reverseF true x)≤midLowCost true false b B x := by
    rcases le_total ((FrameLowArc.u-(189/200)*Real.sin x)*a0)
      ((FrameLowArc.u-(189/200)*Real.sin x)*a1+
        (FrameLowArc.v-(189/200)*Real.cos x)*b1) with he | he
    · rw [min_eq_left he] at ht
      apply (min_le_left _ _).trans
      dsimp [FrameLowMidEndpointScalars.reverseF,FrameLowMidEndpointScalars.reverseP,
        FrameLowMidEndpointScalars.reverseQ,FrameLowMidEndpointScalars.lowA,
        FrameLowMidEndpointScalars.lowB,FrameLowMidEndpointScalars.lowLabel,midLowCost,L]
      rw [(first_width hxq).2]
      norm_num [sign]
      nlinarith
    · rw [min_eq_right he] at ht
      apply (min_le_right _ _).trans
      dsimp [FrameLowMidEndpointScalars.reverseF,FrameLowMidEndpointScalars.reverseP,
        FrameLowMidEndpointScalars.reverseQ,FrameLowMidEndpointScalars.lowA,
        FrameLowMidEndpointScalars.lowB,FrameLowMidEndpointScalars.lowLabel,midLowCost,L,L1]
      rw [(first_width hxq).2]
      norm_num [sign]
      nlinarith
  exact (lt_min (FrameLowMidEndpointScalars.reverse_lower false hx)
    (FrameLowMidEndpointScalars.reverse_lower true hx)).trans_le hmin

end SquaresInCircles.Eight.TableFree.FrameLowMidSecondaryEndpoints
