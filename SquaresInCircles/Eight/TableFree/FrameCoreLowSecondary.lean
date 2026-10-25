module

public import SquaresInCircles.Eight.TableFree.FrameCoreLowGeometry

/-!
# The original core/low secondary witnesses

The multiplier acts on the actual weak margin.  The negative low tangent
is handled by the two arc endpoints; the positive tangent uses the whole
circle support followed by an antitone arc functional.  A low source
secondary witness has already been excluded for all original signs.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreLowSecondary
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreLowGeometry FrameCoreLowEndpoint

def negativeAxial (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-g*a0*Real.sin x+g*pairWidth x
def negativeEndpoint (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+L1-g*a1*Real.sin x-g*b1*Real.cos x+g*pairWidth x
def positiveEndpoint (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-L1-g*a1*Real.sin x+g*b1*Real.cos x+g*pairWidth x

theorem negativeAxial_lower {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    (91/100:ℝ)<negativeAxial x := by
  by_cases hq : x≤Real.pi/2
  · have hw := first_width ⟨hx.1,hq⟩
    have he : negativeAxial x=axial x := by
      dsimp [negativeAxial,axial,axialB,FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact axial_lower ⟨hx.1,hq⟩
  · have hw := second_width ⟨(lt_of_not_ge hq).le,hx.2⟩
    have he : negativeAxial x=axialSecond x := by
      dsimp [negativeAxial,axialSecond,axialB,FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact axialSecond_lower ⟨(lt_of_not_ge hq).le,hx.2⟩

theorem negativeEndpoint_lower {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    (91/100:ℝ)<negativeEndpoint x := by
  by_cases hq : x≤Real.pi/2
  · have hw := first_width ⟨hx.1,hq⟩
    have he : negativeEndpoint x=negativeCut x := by
      dsimp [negativeEndpoint,negativeCut,cutB,FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact negativeCut_lower ⟨hx.1,hq⟩
  · have hw := second_width ⟨(lt_of_not_ge hq).le,hx.2⟩
    have he : negativeEndpoint x=negativeCutSecond x := by
      dsimp [negativeEndpoint,negativeCutSecond,cutB,
        FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact negativeCutSecond_lower ⟨(lt_of_not_ge hq).le,hx.2⟩

theorem negative_target_endpoints {B x : ℝ} (hB : B∈Icc 0 b1) :
    min (linear (u-g*Real.sin x) (v-g*Real.cos x) 0)
      (linear (u-g*Real.sin x) (v-g*Real.cos x) b1)≤
        linear (u-g*Real.sin x) (v-g*Real.cos x) B := by
  by_cases hp : 0≤u-g*Real.sin x
  · exact linear_endpoint_lower hp (by norm_num) b1_mem.2 hB
  · have hq : 0≤v-g*Real.cos x := by
      have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one x) (show 0≤g by norm_num [g])
      dsimp [g,v] at *
      linarith
    exact (min_le_left _ _).trans (linear_monotone (le_of_not_ge hp) hq
      ⟨le_rfl,b1_mem.1.trans b1_mem.2⟩ ⟨hB.1,hB.2.trans b1_mem.2⟩ hB.1)

theorem core_secondary_negative (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc 0 Real.pi)
    (hm : 0≤coreLowSecondary i false a b B x) :
    (91/100:ℝ)<coreLowCost i false a b B x := by
  have hs := core_secondary_source_floor i false hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := negative_target_endpoints (x := x) hB
  have h0 := negativeAxial_lower hx
  have h1 := negativeEndpoint_lower hx
  obtain ⟨base,hbase⟩ : ∃ base : ℝ, base=x-(9/50)*periodicFrameCost x-u*a0+g*pairWidth x :=
    ⟨_,rfl⟩
  have he0 : base+linear (u-g*Real.sin x) (v-g*Real.cos x) 0=negativeAxial x := by
    rw [hbase]
    dsimp [linear,negativeAxial]
    rw [A_zero]
    ring
  have he1 : base+linear (u-g*Real.sin x) (v-g*Real.cos x) b1=negativeEndpoint x := by
    rw [hbase]
    dsimp [linear,negativeEndpoint,L1]
    rw [A_b1]
    ring
  have hmin : (91/100:ℝ)-base<
      min (linear (u-g*Real.sin x) (v-g*Real.cos x) 0)
        (linear (u-g*Real.sin x) (v-g*Real.cos x) b1) := by
    apply lt_min <;> linarith
  have hh := hmin.trans_le ht
  rw [hbase] at hh
  dsimp only [linear,coreLowCost,coreLowSecondary,L] at hh hscaled hm ⊢
  simp only [sign,Bool.false_eq_true,↓reduceIte] at hs hscaled hm ⊢
  linarith

theorem core_secondary_full_circle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc 0 (6/5:ℝ))
    (hm : 0≤coreLowSecondary i true a b B x) :
    FrameCoreLowNorm.F x≤coreLowCost i true a b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := core_secondary_source_floor i true hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-u-g*Real.sin x) (g*Real.cos x-v)
  have hn : Real.sqrt ((-u-g*Real.sin x)^2+(g*Real.cos x-v)^2)=
      FrameCoreLowNorm.N x := by
    unfold FrameCoreLowNorm.N
    congr 1
    linear_combination g^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  have hw := first_width hxq
  dsimp [coreLowSecondary,coreLowCost,FrameCoreLowNorm.F,L] at *
  simp only [sign,ite_true,one_mul] at *
  rw [hw.1] at hscaled
  rw [hw.2]
  nlinarith

theorem positive_target_antitone {x : ℝ} (hx : x∈Icc (6/5:ℝ) (41/20)) :
    AntitoneOn (linear (-u-g*Real.sin x) (g*Real.cos x-v)) (Icc 0 b1) := by
  have hs : 0≤Real.sin x := by
    linarith [FrameCoreLowCancellation.interval_sine
      (show x∈Icc (3/5:ℝ) (41/20) from ⟨by linarith [hx.1],hx.2⟩)]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤6/5)
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hcU : Real.cos x≤363/1000 := by
    linarith [FrameCoreMidScalars.trig_six_fifths.2.2.2]
  have hp : 0≤u+g*Real.sin x := by
    have hh := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hs
    dsimp [u]
    linarith
  apply antiOn_of_hasDeriv_nonpos
  · exact fun B hB => (linear_hasDerivAt ⟨hB.1,hB.2.trans b1_mem.2⟩ _
      _).continuousAt.continuousWithinAt
  · exact fun B hB => linear_hasDerivAt ⟨hB.1.le,hB.2.le.trans b1_mem.2⟩ _ _
  · intro B hB
    have hr := slope_bounds (Ioo_subset_Icc_self hB)
    have hm := mul_le_mul_of_nonneg_left hr.2.le hp
    have hsin := mul_le_mul_of_nonneg_left (Real.sin_le_one x)
      (show (0:ℝ)≤(23/50)*g by norm_num [g])
    have hcos := mul_le_mul_of_nonneg_left hcU (show (0:ℝ)≤g by norm_num [g])
    have hAd : Ad B=-FrameLowArc.slope B := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp only [u,v,g] at hm hsin hcos ⊢
    linarith

theorem core_secondary_endpoint (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc (6/5:ℝ) (41/20))
    (hm : 0≤coreLowSecondary i true a b B x) :
    positiveEndpoint x≤coreLowCost i true a b B x := by
  have hs := core_secondary_source_floor i true hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := positive_target_antitone hx hB ⟨b1_mem.1,le_rfl⟩ hB.2
  dsimp [linear] at ht
  rw [A_b1] at ht
  dsimp [positiveEndpoint,coreLowCost,coreLowSecondary,L,L1] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

theorem positiveEndpoint_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (41/20)) :
    (91/100:ℝ)<positiveEndpoint x := by
  by_cases hq : x≤Real.pi/2
  · have hw := first_width ⟨by linarith [hx.1],hq⟩
    have he : positiveEndpoint x=positiveCut x := by
      dsimp [positiveEndpoint,positiveCut,cutB,
        FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact positiveCut_lower ⟨hx.1,hq⟩
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hq).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hw := second_width hxq
    have he : positiveEndpoint x=positiveCutSecond x := by
      dsimp [positiveEndpoint,positiveCutSecond,cutB,
        FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
      rw [hw.1,hw.2]
      ring
    rw [he]
    exact positiveCutSecond_lower hxq

theorem core_secondary_positive (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc 0 (41/20:ℝ))
    (hm : 0≤coreLowSecondary i true a b B x) :
    (91/100:ℝ)<coreLowCost i true a b B x := by
  by_cases hcut : x≤6/5
  · have hdom : x∈Icc 0 (6/5:ℝ) := ⟨hx.1,hcut⟩
    exact (FrameCoreLowNorm.full_circle_lower hdom).trans_le
      (core_secondary_full_circle i hc hB hdom hm)
  · have hdom : x∈Icc (6/5:ℝ) (41/20) := ⟨(lt_of_not_ge hcut).le,hx.2⟩
    exact (positiveEndpoint_lower hdom).trans_le (core_secondary_endpoint i hc hB hdom hm)

theorem core_secondary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : x∈Icc (-(3/10:ℝ)) (41/20))
    (hm : 0≤coreLowSecondary i k a b B x) :
    (91/100:ℝ)<coreLowCost i k a b B x := by
  have hx0 := core_secondary_angle i k hc hB hx.1 hm
  cases k with
  | false =>
    exact core_secondary_negative i hc hB
      ⟨hx0.le,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm
  | true => exact core_secondary_positive i hc hB ⟨hx0.le,hx.2⟩ hm

end SquaresInCircles.Eight.TableFree.FrameCoreLowSecondary
