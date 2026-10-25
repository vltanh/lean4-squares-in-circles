module

public import SquaresInCircles.Eight.TableFree.FrameCoreLowSecondary

/-!
# The original core-source primary axis against a low state

The negative tangent is charged by the actual low coordinate forced by
separation.  For the positive tangent, the full-circle norm is controlled
by the unit-speed chord inequality on one complete interval.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreLowCorePrimary
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g K)
open FrameCoreLowGeometry

theorem radius_upper : R<(1979/1000:ℝ) := by
  have hR := R_sq
  have hp := R_pos
  norm_num [Q0] at hR
  nlinarith

theorem trig_seven_fourths :
    (49/50:ℝ)<Real.sin (7/4:ℝ) ∧ -(37/200:ℝ)<Real.cos (7/4:ℝ) := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤7/4 by norm_num)
  have hc := Arithmetic.cos10_le_cos (show (0:ℝ)≤7/4 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
    Arithmetic.cos8] at *
  constructor <;> linarith

theorem trig_nineteen_tenths :
    (473/500:ℝ)<Real.sin (19/10:ℝ) ∧ Real.sin (19/10:ℝ)<947/1000 ∧
      -(81/250:ℝ)<Real.cos (19/10:ℝ) ∧ Real.cos (19/10:ℝ)< -(8/25) := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤19/10 by norm_num)
  have hsU := Arithmetic.sin_le_sin9 (show (0:ℝ)≤19/10 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤19/10 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤19/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem negative_target_coordinate {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (Real.pi/2) (7/4:ℝ)) (hm : 0≤coreLowPrimary false a B x) :
    (28487/117600:ℝ)<B := by
  have hcore := core_bounds hc
  have hlow := low_bounds hB
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := second_signs hxq
  have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (7/4:ℝ)≤Real.pi) hx
    (by rw [Real.sin_pi_div_two]; norm_num : (49/50:ℝ)<Real.sin (Real.pi/2))
    trig_seven_fourths.1
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (7/4:ℝ)≤Real.pi) hx.2
  have hd : -Real.cos x<(37/200:ℝ) := by linarith [trig_seven_fourths.2]
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤183/200 by linarith [hlow.2.2.2]) (neg_nonneg.mpr ht.2)
  have hAd : (A B-1/2)*(-Real.cos x)<(183/200:ℝ)*(37/200) := by linarith
  have hBs := mul_le_mul_of_nonneg_left hs.le
    (show 0≤1/2-B by linarith [hlow.2.1])
  have hsf : sign false= -1 := by simp [sign]
  dsimp only [coreLowPrimary] at hm
  rw [hsf,(second_width hxq).1] at hm
  linarith [hcore.2.1]

theorem core_primary_negative (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hx : Real.pi/2≤x) (hm : 0≤coreLowPrimary false a B x) :
    (91/100:ℝ)<coreLowCost i false a b B x := by
  have hsource := (FrameCoreArc.signed_label_bounds i hc).1
  have htarget := L_bounds hB
  have hch := CorePairGeometry.charge_upper x
  have hsf : sign false= -1 := by simp [sign]
  dsimp only [coreLowCost]
  rw [hsf]
  by_cases hlarge : (7/4:ℝ)≤x
  · linarith
  · have hBmin := negative_target_coordinate hc hB ⟨hx,(lt_of_not_ge hlarge).le⟩ hm
    have hlabel := (low_label_linear hB).1
    have hpi : (6283/2000:ℝ)<Real.pi := by linarith [Arithmetic.pi_hand_enclosure.1]
    have huv : (0:ℝ)≤v-u := by norm_num [u,v]
    have hm2 := mul_le_mul_of_nonneg_left hBmin.le huv
    norm_num [u,v] at hm2 hlabel
    linarith

theorem positive_target_cut {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : Real.pi/2≤x)
    (hm : 0≤coreLowPrimary true a B x) : (19/10:ℝ)<x := by
  by_contra! hsmall
  have hcore := core_bounds hc
  have hlow := low_bounds hB
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx,by linarith [hsmall,FrameLowPair.pi_lower]⟩
  have ht := second_signs hxq
  have hs := sin_endpoint_lower (by positivity : 0≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (19/10:ℝ)≤Real.pi) ⟨hx,hsmall⟩
    (by rw [Real.sin_pi_div_two]; norm_num : (9/10:ℝ)<Real.sin (Real.pi/2))
    (by linarith [trig_nineteen_tenths.1] : (9/10:ℝ)<Real.sin (19/10:ℝ))
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower] : (19/10:ℝ)≤Real.pi) hsmall
  have hd : -Real.cos x<(1/3:ℝ) := by linarith [trig_nineteen_tenths.2.2.1]
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤183/200 by linarith [hlow.2.2.2]) (neg_nonneg.mpr ht.2)
  have hBsin := mul_nonneg hB.1 ht.1
  have hst : sign true=1 := by simp [sign]
  dsimp only [coreLowPrimary] at hm
  rw [hst,(second_width hxq).1] at hm
  linarith [hcore.2.1]

def N (x : ℝ) : ℝ := Real.sqrt ((u-Real.cos x)^2+(v-Real.sin x)^2)

theorem N_nonneg (x : ℝ) : 0≤N x := Real.sqrt_nonneg _
theorem N_sq (x : ℝ) : (N x)^2=(u-Real.cos x)^2+(v-Real.sin x)^2 :=
  Real.sq_sqrt (by positivity)

/-- The exact chord bound gives the unit-speed estimate for the actual norm. -/
theorem N_growth {x y : ℝ} (hxy : y≤x) : N x≤N y+(x-y) := by
  let dx : ℝ := Real.cos y-Real.cos x
  let dy : ℝ := Real.sin y-Real.sin x
  let dot : ℝ := (u-Real.cos y)*dx+(v-Real.sin y)*dy
  have hdist : dx^2+dy^2≤(x-y)^2 := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := x-y)
    rw [Real.cos_sub] at hc
    dsimp [dx,dy]
    nlinarith [Real.sin_sq_add_cos_sq x,Real.sin_sq_add_cos_sq y]
  have hid : (N y)^2*(dx^2+dy^2)-dot^2=
      ((u-Real.cos y)*dy-(v-Real.sin y)*dx)^2 := by
    rw [N_sq]
    dsimp [dot]
    ring
  have hh := mul_le_mul_of_nonneg_left hdist (sq_nonneg (N y))
  have hdotsq : dot^2≤(N y*(x-y))^2 := by
    rw [mul_pow]
    linarith [sq_nonneg ((u-Real.cos y)*dy-(v-Real.sin y)*dx)]
  have hp := mul_nonneg (N_nonneg y) (sub_nonneg.mpr hxy)
  have hdot : dot≤N y*(x-y) := (abs_le_of_sq_le_sq' hdotsq hp).2
  have hsum : (N x)^2=(N y)^2+2*dot+dx^2+dy^2 := by
    rw [N_sq,N_sq]
    dsimp [dot,dx,dy]
    ring
  have hnonneg : 0≤N y+(x-y) := add_nonneg (N_nonneg y) (sub_nonneg.mpr hxy)
  refine le_of_pow_le_pow_left₀ two_ne_zero hnonneg ?_
  rw [hsum]
  linarith

theorem N_start : N (19/10)<(3/4:ℝ) := by
  have hs := sin_lower_seven (show (0:ℝ)≤19/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤19/10 by norm_num)
  have hN := N_sq (19/10)
  have ht := Real.sin_sq_add_cos_sq (19/10:ℝ)
  norm_num at hs hc
  dsimp only [u,v] at hN
  refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
  rw [hN]
  linarith

theorem norm_support_lower {x : ℝ} (hx : x∈Icc (19/10:ℝ) (41/20)) :
    (51/50:ℝ)<x-Real.cos x+345707/800000-R*N x := by
  have hN := (N_growth hx.1).trans_lt (by linarith [N_start] :
    N (19/10)+(x-19/10)<3/4+(x-19/10))
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤19/10)
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hcU : Real.cos x< -(8/25:ℝ) := hc.trans_lt trig_nineteen_tenths.2.2.2
  have hRN : R*N x<(1979/1000)*(3/4+(x-19/10)) :=
    mul_lt_mul'' radius_upper hN R_pos.le (N_nonneg x)
  linarith [hx.2]

theorem core_primary_circle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (19/10:ℝ) (41/20)) (hm : 0≤coreLowPrimary true a B x) :
    x-Real.cos x+345707/800000-R*N x<coreLowCost i true a b B x := by
  have hsource : -coreLabel a b≤ sign i*coreLabel a b := by
    have hp := (label_bounds hc).1
    cases i <;> norm_num [sign] <;> linarith
  have hdiag := diagonal_support (X := K-1) (Y := -g) hc
    (by norm_num [K]) (by norm_num [g])
  have hdiagState : CoreState diagonal diagonal := by
    right
    exact ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl,
      by nlinarith [CoreAngleEndpoint.diagonal_sq]⟩
  have hdiagLabel := (label_bounds hdiagState).2
  have htarget := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (Real.cos x-u) (Real.sin x-v)
  have he : Real.sqrt ((Real.cos x-u)^2+(Real.sin x-v)^2)=N x := by
    unfold N
    congr 1
    ring
  rw [he] at htarget
  have hch := CorePairGeometry.charge_upper x
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨by linarith [hx.1,Arithmetic.pi_hand_enclosure.2],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hw := (second_width hxq).1
  dsimp [coreLowCost,coreLowPrimary,coreLabel,L,sign] at *
  rw [hw] at hm
  have hu := mul_lt_mul_of_pos_left a0_bounds.1 (show 0<u by norm_num [u])
  dsimp [u,v,K,g] at *
  nlinarith [CoreAngleEndpoint.diagonal_bounds.2]

theorem core_primary (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (-(3/10:ℝ)) (41/20)) (hm : 0≤coreLowPrimary k a B x) :
    (91/100:ℝ)<coreLowCost i k a b B x := by
  have hcut := core_primary_angle k hc hB hx.1 hm
  cases k with
  | false => exact core_primary_negative i hc hB hcut.le hm
  | true =>
      have hcut' := positive_target_cut hc hB hcut.le hm
      have hdom : x∈Icc (19/10:ℝ) (41/20) := ⟨hcut'.le,hx.2⟩
      exact (lt_trans (by norm_num) (norm_support_lower hdom)).trans
        (core_primary_circle i hc hB hdom hm)

end SquaresInCircles.Eight.TableFree.FrameCoreLowCorePrimary
