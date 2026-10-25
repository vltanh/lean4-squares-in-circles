module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighGeometry

/-!
# Every original core-source primary witness against a high state

The actual weak margin either forces a large positive target marker or
restricts the target to a low-marker part of its original circle.  Both
source signs and every tie are retained throughout.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighCorePrimary
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (b2)
open FrameCoreHighGeometry

theorem trig_endpoints :
    (63/200:ℝ)<Real.cos (5/4:ℝ) ∧
      (637/1000:ℝ)<Real.sin (49/20:ℝ) ∧
        -(771/1000:ℝ)<Real.cos (49/20:ℝ) ∧
          (299/500:ℝ)<Real.sin (5/2:ℝ) ∧
            -(401/500:ℝ)<Real.cos (5/2:ℝ) := by
  have h0 := cos_lower_six (show (0:ℝ)≤5/4 by norm_num)
  have h1 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤49/20 by norm_num)
  have h2 := Arithmetic.cos10_le_cos (show (0:ℝ)≤49/20 by norm_num)
  have h3 := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤5/2 by norm_num)
  have h4 := Arithmetic.cos10_le_cos (show (0:ℝ)≤5/2 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith

theorem negative_target_large_marker {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : x∈Icc (6/5:ℝ) (5/4))
    (hm : 0≤coreHighPrimary false a B x) : (7/10:ℝ)<H B := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hB
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi hxq.1
    (by linarith [FrameLowPair.pi_lower] : (5/4:ℝ)≤Real.pi) hx.2
  have hA := mul_le_mul_of_nonneg_right
    (show (1399/1000:ℝ)≤A B+1/2 by linarith [hhigh.2.2.1]) ht.2.2.1
  have hBs := mul_le_mul_of_nonneg_left ht.2.1
    (show 0≤B-1/2 by linarith [hhigh.1])
  have hBl : (17/20:ℝ)<B := by
    dsimp [coreHighPrimary,sign] at hm
    rw [(first_width hxq).1] at hm
    nlinarith [trig_endpoints.1]
  have hcircle := A_circle ⟨FrameMidArc.b2_mem.1.trans hB.1,hB.2⟩
  have hAu : A B<1 := by
    have hp : 0≤A B := by linarith [hhigh.2.2.1]
    norm_num [Q0] at hcircle
    nlinarith
  dsimp [H,u,v]
  linarith [k_bounds.1]

theorem core_primary_negative (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : (6/5:ℝ)≤x)
    (hm : 0≤coreHighPrimary false a B x) :
    (8833/10000:ℝ)<coreHighCost i false a b B x := by
  have hsource := (FrameCoreArc.signed_label_bounds i hc).1
  have hch := CorePairGeometry.charge_upper x
  by_cases hlarge : (5/4:ℝ)≤x
  · have htarget := (H_bounds hB).1
    dsimp [coreHighCost,sign] at hsource ⊢
    linarith [H2_bounds.1]
  · have htarget := negative_target_large_marker hc hB ⟨hx,(lt_of_not_ge hlarge).le⟩ hm
    dsimp [coreHighCost,sign] at hsource ⊢
    linarith

theorem positive_target_cut {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : (6/5:ℝ)≤x)
    (hm : 0≤coreHighPrimary true a B x) : (49/20:ℝ)<x := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hB
  by_contra! hsmall
  by_cases hfirst : x≤Real.pi/2
  · have ht := FrameLowPair.quadrant ⟨by linarith [hx],hfirst⟩
    have hA := mul_nonneg (by linarith [hhigh.2.2.1] : 0≤A B) ht.2.2.1
    have hBsin := mul_nonneg (by linarith [hhigh.1] : 0≤B) ht.1
    have hw := width_one_le x
    dsimp [coreHighPrimary,sign] at hm
    linarith
  · have hxq : x∈Icc (Real.pi/2) Real.pi :=
      ⟨(lt_of_not_ge hfirst).le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := second_signs hxq
    have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
      (by linarith [FrameLowPair.pi_lower] : (49/20:ℝ)≤Real.pi)
      (show x∈Icc (Real.pi/2) (49/20:ℝ) from ⟨hxq.1,hsmall⟩)
      (by rw [Real.sin_pi_div_two]; norm_num : (637/1000:ℝ)<Real.sin (Real.pi/2))
      trig_endpoints.2.1
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith [hx] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hsmall
    have hd : -Real.cos x<(771/1000:ℝ) := by linarith [trig_endpoints.2.2.1]
    have hA := mul_le_mul_of_nonneg_right
      (show A B-1/2≤7/10 by linarith [hhigh.2.2.2]) (neg_nonneg.mpr ht.2)
    have hBsin := mul_le_mul_of_nonneg_right
      (show (10139/10000:ℝ)≤B+1/2 by linarith [hhigh.1]) ht.1
    dsimp [coreHighPrimary,sign] at hm
    rw [(second_width hxq).1] at hm
    nlinarith

theorem positive_target_small_marker {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (49/20:ℝ) (5/2)) (hm : 0≤coreHighPrimary true a B x) :
    H B<(27/50:ℝ) := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hB
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := second_signs hxq
  have hs := sin_endpoint_lower (by norm_num : (0:ℝ)≤49/20)
    (by linarith [FrameLowPair.pi_lower] : (5/2:ℝ)≤Real.pi) hx
    (by linarith [trig_endpoints.2.1] : (299/500:ℝ)<Real.sin (49/20:ℝ))
    trig_endpoints.2.2.2.1
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1] : 0≤x) (by linarith [FrameLowPair.pi_lower]) hx.2
  have hd : -Real.cos x<(401/500:ℝ) := by linarith [trig_endpoints.2.2.2.2]
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤7/10 by linarith [hhigh.2.2.2]) (neg_nonneg.mpr ht.2)
  have hBsin := mul_le_mul_of_nonneg_left hs.le (show 0≤B+1/2 by linarith [hhigh.1])
  have hBu : B<(3/5:ℝ) := by
    dsimp [coreHighPrimary,sign] at hm
    rw [(second_width hxq).1] at hm
    nlinarith
  have hcircle := A_circle ⟨FrameMidArc.b2_mem.1.trans hB.1,hB.2⟩
  have hAl : (57/50:ℝ)<A B := by
    have hB2 := pow_le_pow_left₀ (show 0≤B+1/2 by linarith [hhigh.1])
      (show B+1/2≤11/10 by linarith) 2
    have hp : 0≤A B := by linarith [hhigh.2.2.1]
    norm_num [Q0] at hcircle
    nlinarith
  dsimp [H,u,v]
  linarith [k_bounds.2.1]

theorem core_primary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2)) (hm : 0≤coreHighPrimary k a B x) :
    (8833/10000:ℝ)<coreHighCost i k a b B x := by
  have hcut := core_primary_angle k hc hB hx.1 hm
  cases k with
  | false => exact core_primary_negative i hc hB hcut.le hm
  | true =>
      have hcut' := positive_target_cut hc hB hcut.le hm
      have htarget := positive_target_small_marker hc hB ⟨hcut'.le,hx.2⟩ hm
      have hsource := (FrameCoreArc.signed_label_bounds i hc).1
      have hch := CorePairGeometry.charge_upper x
      dsimp [coreHighCost,sign] at hsource ⊢
      linarith

end SquaresInCircles.Eight.TableFree.FrameCoreHighCorePrimary
