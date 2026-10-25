module

public import SquaresInCircles.Eight.TableFree.FrameMidMidScalars

/-!
# The two actual middle/middle primary target signs

All source signs are retained through the actual whole-arc source floor.
The negative target uses its two genuine arc endpoints; the positive
target uses the complete second-quadrant norm support.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidMidPrimary
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidGeometry FrameMidMidGeometry FrameMidMidScalars

theorem primary_angle_pos (k : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : -(1/20:ℝ)≤x) (hm : 0≤primary k b B x) : 0<x := by
  by_contra! hneg
  have hs := middle_bounds hb
  have ht := middle_bounds hB
  have hsign := negative_signed_sin_le k (x := x) (show 0≤B by linarith [ht.1])
  have habs : |x|≤1/20 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hsin := (Real.abs_sin_le_abs (x := x)).trans habs
  have hsquare := pow_le_pow_left₀ (abs_nonneg x) habs 2
  rw [sq_abs] at hsquare
  have hcos : (799/800:ℝ)≤Real.cos x := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hco0 : 0≤Real.cos x := by linarith
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [ht.2.2.1]) hco0
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤7/500 by linarith [ht.2.1]) (abs_nonneg (Real.sin x))
  dsimp [primary,pairWidth] at hm
  rw [abs_of_nonneg hco0] at hm
  linarith

theorem primary_negative_cut {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : -(1/20:ℝ)≤x) (hm : 0≤primary false b B x) :
    (21/20:ℝ)<x := by
  have hx0 := primary_angle_pos false hb hB hx hm
  by_contra! hsmall
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx0.le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
  have hq := FrameLowPair.quadrant hxq
  have hs := middle_bounds hb
  have ht := middle_bounds hB
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx0.le
    (by linarith [FrameLowPair.pi_lower] : (21/20:ℝ)≤Real.pi) hsmall
  have hcos := cos_lower_six (show (0:ℝ)≤21/20 by norm_num)
  norm_num at hcos
  have hco : (49/100:ℝ)<Real.cos x := by linarith
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [ht.2.2.1]) hq.2.2.1
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤7/500 by linarith [ht.2.1]) hq.1
  dsimp [primary,sign] at hm
  rw [(first_width hxq).1] at hm
  nlinarith [hq.2.1]

theorem primary_positive_quadrant_false {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤primary true b B x) : False := by
  have hs := middle_bounds hb
  have ht := middle_bounds hB
  have hq := FrameLowPair.quadrant hx
  have hw := (first_width hx).1
  have hsc : 1≤Real.sin x+Real.cos x := by linarith [width_one_le x]
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [ht.2.2.1]) hq.2.2.1
  have hB' := mul_le_mul_of_nonneg_right
    (show (4123/5000:ℝ)≤B+1/2 by linarith [ht.1]) hq.1
  dsimp [primary,sign] at hm
  rw [hw] at hm
  nlinarith

def lowEndpoint (x : ℝ) : ℝ :=
  x+59/100+mP+M1+(41/100-b1)*Real.sin x+(41/100+a1)*Real.cos x
def highEndpoint (x : ℝ) : ℝ :=
  x+59/100+mP+M2+(41/100-b2)*Real.sin x+(41/100+a2)*Real.cos x

theorem endpoint_trig {x : ℝ} (hx : x∈Icc (21/20:ℝ) (109/100)) :
    0≤Real.sin x ∧ Real.sin x≤1 ∧ (23/50:ℝ)<Real.cos x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hxq.1
    (by linarith [FrameLowPair.pi_lower] : (109/100:ℝ)≤Real.pi) hx.2
  have hcos := cos_lower_six (show (0:ℝ)≤109/100 by norm_num)
  norm_num at hcos
  exact ⟨ht.1,ht.2.1,by linarith⟩

theorem lowEndpoint_lower {x : ℝ} (hx : x∈Icc (21/20:ℝ) (109/100)) :
    (107/100:ℝ)<lowEndpoint x := by
  have ht := endpoint_trig hx
  have hsin := mul_nonneg (show 0≤41/100-b1 by linarith [b1_bounds.2]) ht.1
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.le
    (show 0≤41/100+a1 by linarith [a1_precise.1])
  dsimp [lowEndpoint,mP]
  nlinarith [hx.1,M_endpoints.1,a1_precise.1]

theorem highEndpoint_lower {x : ℝ} (hx : x∈Icc (21/20:ℝ) (109/100)) :
    (107/100:ℝ)<highEndpoint x := by
  have ht := endpoint_trig hx
  have hsin := mul_le_mul_of_nonpos_left ht.2.1
    (show 41/100-b2≤0 by linarith [b2_bounds.1])
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.le
    (show 0≤41/100+a2 by linarith [a2_bounds.1])
  dsimp [highEndpoint,mP]
  nlinarith [hx.1,M_endpoints.2.2.1,a2_bounds.1,b2_bounds.2]

theorem primary_negative_short (i : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (21/20:ℝ) (109/100)) (hm : 0≤primary false b B x) :
    (557/625:ℝ)<cost i false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := primary_source_lower i hb
  have ht := linear_endpoint_lower (p := p+Real.cos x) (q := q-Real.sin x)
    (by dsimp [p]; linarith [(FrameLowPair.quadrant hxq).2.2.1])
    b1_mem.1 b2_mem.2 hB
  dsimp [linear] at ht
  rw [A_b1,A_b2] at ht
  have hh : min (lowEndpoint x) (highEndpoint x)≤cost i false b B x := by
    rcases le_total ((p+Real.cos x)*a1+(q-Real.sin x)*b1)
      ((p+Real.cos x)*a2+(q-Real.sin x)*b2) with h | h
    · rw [min_eq_left h] at ht
      apply (min_le_left _ _).trans
      have hw := first_width hxq
      simp only [lowEndpoint,cost,primary,M,M1,sign,Bool.false_eq_true,↓reduceIte,hw.1,hw.2]
        at hm hs ⊢
      linarith
    · rw [min_eq_right h] at ht
      apply (min_le_right _ _).trans
      have hw := first_width hxq
      simp only [highEndpoint,cost,primary,M,M2,sign,Bool.false_eq_true,↓reduceIte,hw.1,hw.2]
        at hm hs ⊢
      linarith
  have hlow := (lt_min (lowEndpoint_lower hx) (highEndpoint_lower hx)).trans_le hh
  linarith

theorem primary_negative (i : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : -(1/20:ℝ)≤x) (hm : 0≤primary false b B x) :
    (557/625:ℝ)<cost i false b B x := by
  by_cases htail : (109/100:ℝ)≤x
  · exact (same_tail false hb hB htail).trans_le (weaken_source i false hb)
  · exact primary_negative_short i hb hB
      ⟨(primary_negative_cut hb hB hx hm).le,(lt_of_not_ge htail).le⟩ hm

theorem primary_circle_support (i : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) (hm : 0≤primary true b B x) :
    primaryF x≤cost i true b B x := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := primary_source_lower i hb
  have ht := circle_linear_lower
    (A_circle ⟨b1_mem.1.trans hB.1,hB.2.trans b2_mem.2⟩)
    (-p+Real.cos x) (-q+Real.sin x)
  have hn : Real.sqrt ((-p+Real.cos x)^2+(-q+Real.sin x)^2)=NP x := by
    dsimp [NP,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination Real.sin_sq_add_cos_sq x
  rw [hn] at ht
  dsimp [primaryF,cost,primary,KP,M] at *
  simp only [sign,ite_true,one_mul] at *
  rw [(second_width hxq).1] at hm
  rw [(second_width hxq).2]
  nlinarith

theorem primary_positive (i : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : -(1/20:ℝ)≤x) (hm : 0≤primary true b B x) :
    (557/625:ℝ)<cost i true b B x := by
  by_cases htail : (37/20:ℝ)≤x
  · exact (negative_positive_tail hb hB htail).trans_le (weaken_source i true hb)
  · have hx0 := primary_angle_pos true hb hB hx hm
    have hxq : Real.pi/2<x := by
      by_contra! hfirst
      exact primary_positive_quadrant_false hb hB ⟨hx0.le,hfirst⟩ hm
    have hdom : x∈Icc (Real.pi/2) (37/20:ℝ) := ⟨hxq.le,(lt_of_not_ge htail).le⟩
    exact (primary_lower hdom).trans_le (primary_circle_support i hb hB hdom hm)

end SquaresInCircles.Eight.TableFree.FrameMidMidPrimary
