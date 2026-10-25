module

public import SquaresInCircles.Eight.TableFree.FrameCoreMidGeometry

/-!
# Both orientations of the original core/middle transverse axis

The nonnegative multiplier is applied to the actual weak separating
margin.  The complete middle arc is retained in each support.  Both
signed core tangents, including the zero tie, remain in the conclusion.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreMidTransverse
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidScalars FrameCoreMidGeometry

theorem core_secondary_negative (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) Real.pi)
    (hm : 0≤coreMidSecondary i false a b B x) :
    (1801/2000:ℝ)<coreMidCost i false a b B x := by
  have hs := core_secondary_source_floor i false hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have hh : negativeMid B x≤coreMidCost i false a b B x := by
    dsimp only [negativeMid,coreMidCost,coreMidSecondary] at hscaled ⊢
    rw [show sign false=-1 from rfl] at hscaled ⊢
    linarith
  exact (lt_trans (by norm_num) (negativeMid_lower hB hx)).trans_le hh

theorem core_secondary_full_circle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc 0 (153/100:ℝ))
    (hm : 0≤coreMidSecondary i true a b B x) :
    FrameCoreMidFullCircle.F x≤coreMidCost i true a b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := core_secondary_source_floor i true hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    (-p-g*Real.sin x) (g*Real.cos x-q)
  have hn : Real.sqrt ((-p-g*Real.sin x)^2+(g*Real.cos x-q)^2)=
      FrameCoreMidFullCircle.N x := by
    unfold FrameCoreMidFullCircle.N
    congr 1
    linear_combination g^2*(Real.sin_sq_add_cos_sq x)
  rw [hn] at ht
  have hw := first_width hxq
  dsimp [coreMidSecondary,coreMidCost,FrameCoreMidFullCircle.F,M] at *
  simp only [sign,ite_true,one_mul] at *
  rw [hw.1] at hscaled
  rw [hw.2]
  nlinarith

theorem positive_target_antitone {x : ℝ}
    (hx : x∈Icc (153/100:ℝ) (109/50)) :
    AntitoneOn (linear (-p-g*Real.sin x) (g*Real.cos x-q)) (Icc b1 b2) := by
  have htrig := high_angle_trig hx
  have hp : 0≤p+g*Real.sin x := by
    have hm := mul_nonneg (show (0:ℝ)≤g by norm_num [g])
      (show 0≤Real.sin x by linarith [htrig.1])
    dsimp [p] at *
    linarith
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (linear_hasDerivAt ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩ _
      _).continuousAt.continuousWithinAt
  · intro B hB
    exact linear_hasDerivAt
      ⟨b1_mem.1.trans hB.1.le,hB.2.le.trans b2_mem.2⟩ _ _
  · intro B hB
    have hr := slope_mid_bounds (Ioo_subset_Icc_self hB)
    have hm := mul_le_mul_of_nonneg_left hr.2.le hp
    have hs := mul_le_mul_of_nonneg_left (Real.sin_le_one x)
      (show (0:ℝ)≤(597/1000)*g by norm_num [g])
    have hcos := mul_le_mul_of_nonneg_left htrig.2.le
      (show (0:ℝ)≤g by norm_num [g])
    have hAd : Ad B=-FrameLowArc.slope B := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp only [p,q,g] at hm hs hcos ⊢
    linarith

def positiveMidEndpoint (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-M2-g*a2*Real.sin x+g*b2*Real.cos x+g*pairWidth x

theorem core_secondary_endpoint (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (153/100:ℝ) (109/50))
    (hm : 0≤coreMidSecondary i true a b B x) :
    positiveMidEndpoint x≤coreMidCost i true a b B x := by
  have hs := core_secondary_source_floor i true hc hB hm
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have ht := positive_target_antitone hx hB ⟨b1_lt_b2.le,le_rfl⟩ hB.2
  dsimp [linear] at ht
  rw [A_b2] at ht
  dsimp [positiveMidEndpoint,coreMidCost,coreMidSecondary,M,M2] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

theorem positiveMidEndpoint_lower {x : ℝ}
    (hx : x∈Icc (153/100:ℝ) (109/50)) :
    (4503/5000:ℝ)<positiveMidEndpoint x := by
  by_cases hq : x≤Real.pi/2
  · have hwidth := first_width
      (show x∈Icc 0 (Real.pi/2) from ⟨by linarith [hx.1],hq⟩)
    have he : positiveMidEndpoint x=positiveMidFirst x := by
      dsimp [positiveMidEndpoint,positiveMidFirst,trigAffine,ap,cp]
      rw [hwidth.1,hwidth.2]
      ring
    rw [he]
    exact positiveMidFirst_lower ⟨hx.1,hq⟩
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hq).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
    have hwidth := second_width hxq
    have he : positiveMidEndpoint x=positiveMidSecond x := by
      dsimp [positiveMidEndpoint,positiveMidSecond,trigAffine,ap,cp]
      rw [hwidth.1,hwidth.2]
      ring
    rw [he]
    exact positiveMidSecond_lower hxq

theorem core_secondary_positive (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤coreMidSecondary i true a b B x) :
    (1801/2000:ℝ)<coreMidCost i true a b B x := by
  have hx0 := core_secondary_positive_cut i hc hB hx.1 hm
  by_cases hcut : x≤153/100
  · have hdom : x∈Icc 0 (153/100:ℝ) := ⟨by linarith,hcut⟩
    exact (lt_trans (by norm_num) (FrameCoreMidFullCircle.lower hdom)).trans_le
      (core_secondary_full_circle i hc hB hdom hm)
  · have hdom : x∈Icc (153/100:ℝ) (109/50) := ⟨(lt_of_not_ge hcut).le,hx.2⟩
    exact (lt_trans (by norm_num) (positiveMidEndpoint_lower hdom)).trans_le
      (core_secondary_endpoint i hc hB hdom hm)

theorem core_secondary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤coreMidSecondary i k a b B x) :
    (1801/2000:ℝ)<coreMidCost i k a b B x := by
  cases k with
  | false =>
    exact core_secondary_negative i hc hB
      ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm
  | true => exact core_secondary_positive i hc hB hx hm

theorem middle_secondary_negative {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : x∈Icc (-(54/125:ℝ)) Real.pi)
    (hm : 0≤ midCoreSecondary true false b a B x) :
    (1801/2000:ℝ)< midCoreCost true false b a B x := by
  have hs := loss_antitone (show (449/500:ℝ)≤g by norm_num [g])
    hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  simp only [M_b2] at hs
  have hscaled := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hm
  have hsin := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x)
    (show (0:ℝ)≤g by norm_num [g])
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x)
    (show (0:ℝ)≤g by norm_num [g])
  have ht := positive_support (r := g*Real.sin x) (z := g*Real.cos x) hc
    (by dsimp only [K,g] at hsin ⊢; linarith) (by linarith)
  have hh : negativeCore x≤ midCoreCost true false b a B x := by
    dsimp only [negativeCore,midCoreCost,midCoreSecondary,ac] at hscaled ⊢
    rw [show sign true=1 from rfl,show sign false=-1 from rfl] at hscaled ⊢
    linarith
  exact (lt_trans (by norm_num) (negativeCore_lower hx)).trans_le hh

theorem middle_secondary_positive {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤ midCoreSecondary true true b a B x) :
    (1801/2000:ℝ)< midCoreCost true true b a B x := by
  have hcut := mid_secondary_positive_cut hb hc hx.1 hm
  have hs := loss_antitone (show (449/500:ℝ)≤1 by norm_num)
    hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
  simp only [M_b2,one_mul] at hs
  have ht := negative_support (x := x) hc
  have hh : positiveCore x≤ midCoreCost true true b a B x := by
    dsimp only [positiveCore,midCoreCost,midCoreSecondary] at hm ⊢
    rw [show sign true=1 from rfl] at hm ⊢
    linarith
  have hdom : x∈Icc (6/5:ℝ) Real.pi :=
    ⟨hcut.le,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  exact (lt_trans (by norm_num) (positiveCore_lower hdom)).trans_le hh

theorem middle_secondary (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b1 b2) (hc : CoreState a B)
    (hx : x∈Icc (-(54/125:ℝ)) (109/50))
    (hm : 0≤ midCoreSecondary i k b a B x) :
    (1801/2000:ℝ)< midCoreCost i k b a B x := by
  have hi := mid_secondary_source_positive i k hb hc hm
  subst i
  cases k with
  | false =>
    exact middle_secondary_negative hb hc
      ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm
  | true => exact middle_secondary_positive hb hc hx hm

end SquaresInCircles.Eight.TableFree.FrameCoreMidTransverse
