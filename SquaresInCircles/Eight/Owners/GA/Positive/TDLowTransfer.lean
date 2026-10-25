module

public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds
public import SquaresInCircles.Eight.Owners.GA.Positive.TDLowPolynomial
public import SquaresInCircles.Eight.Owners.GA.TD2LowEnvelope

/-!
# Eight squares: the four low TD2 scalar inequalities at the explicit weights

The original trigonometric force norms are bounded
by the exact polynomials, and the four whole-interval reserves are
transferred through positive auxiliary masses.  The D support is its
actual sorted-circle formula throughout this coefficient interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PositiveTD.Certificate
open Polynomial Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

@[simp] theorem ch_cast : (ch:ℝ)=aeval frameCap C10 := by
  norm_num [ch,h,C10,C4,frameCap]
@[simp] theorem Ch_cast : (Ch:ℝ)=aeval frameCap C12 := by
  norm_num [Ch,h,C12,C10,C4,frameCap]
@[simp] theorem sh_cast : (sh:ℝ)=aeval frameCap S11 := by
  norm_num [sh,h,S11,S9,S5,frameCap]

theorem low_frame_domain {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) : z∈Icc 0 frameCap :=
  ⟨hz.1,by dsimp [frameCap]; linarith [hz.2]⟩

theorem low_nonradical_lower {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    aeval z lowA≤lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
      Real.cos z-1 ∧
    aeval z lowAstar≤lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
      (109/200)*tilted (Explicit.lowC z) z*(frameCap-z) := by
  have hz' := low_frame_domain hz
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have hc : 0<Explicit.lowC z := by linarith
  have ht := taylor_bounds hz'
  have hm := tilted_polynomial_bounds (c:=lowC) hz' (by simpa using hc)
  simp only [lowC_eval] at hm
  have hD := mul_le_mul_of_nonneg_left diagonal_le_cbar
    (show 0≤1+Explicit.lowC z by linarith)
  have hs := sigma_sine_upper hz' hc.le
  have hW0 := mul_le_mul_of_nonneg_left
    (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
  have hW : Explicit.lowC z/2*(1+aeval z C10+aeval z S11)≤
      Explicit.lowC z*edgeWidth z := by
    rw [edgeWidth_positive_formula hz']
    nlinarith only [hW0]
  have hsep := mul_le_mul_of_nonneg_right hm.2.2 (sub_nonneg.mpr hz'.2)
  rw [show (cbar:ℝ)=449607033/500000000 by norm_num [cbar]] at hD
  rw [show (sigmabar:ℝ)=1415477291/1000000000 by norm_num [sigmabar]] at hs
  constructor
  · norm_num only [lowA,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,lowK_eval,lowL_eval,lowC_eval]
    dsimp [lowNonradical]
    nlinarith only [hm.2.1,ht.2.2.2.2.1,hD,hs,hW]
  · norm_num only [lowAstar,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,aeval_X,
      lowK_eval,lowL_eval,lowC_eval,h]
    dsimp [lowNonradical,frameCap] at hsep ⊢
    nlinarith only [hm.2.1,hD,hs,hW,hsep]

theorem low_norm_bounds {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    (pairNorm (Explicit.lowK z) 1 (-z))^2≤aeval z lowPH ∧
    (pairNorm (Explicit.lowK z) (Explicit.lowL z) 0)^2≤aeval z lowPG ∧
    (pairNorm (Explicit.lowL z) (tilted (Explicit.lowC z) z) 0)^2≤aeval z lowPB ∧
    (pairNorm (Explicit.lowK z) 1 (-frameCap))^2≤aeval z lowPHh ∧
    (pairNorm (Explicit.lowK z) 1 0)^2≤aeval z lowPH0 ∧
    (pairNorm (Explicit.lowK z) (Explicit.lowL z) (-frameCap))^2≤aeval z lowPGh := by
  have hz' := low_frame_domain hz
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have hk : 0<Explicit.lowK z := by linarith
  have hl : 0<Explicit.lowL z := by linarith
  have hc : 0<Explicit.lowC z := by linarith
  have hm := tilted_polynomial_bounds (c:=lowC) hz' (by simpa using hc)
  simp only [lowC_eval] at hm
  have hm0 : 0<tilted (Explicit.lowC z) z := tilted_pos hc hz'
  have hm2 : (tilted (Explicit.lowC z) z)^2≤(aeval z (mPlus lowC))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.2.2)
      (show 0≤aeval z (mPlus lowC)+tilted (Explicit.lowC z) z by linarith [hm.2.2])]
  have hzcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hs := (taylor_bounds hz').2.1
  have hscap := (taylor_bounds hzcap).2.1
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hz' hs
    norm_num only [lowPH,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,eq_ratCast,lowK_eval]
    nlinarith only [hh]
  · rw [zero_norm_sq]
    simp [lowPG]
  · rw [zero_norm_sq]
    simp only [lowPB,map_add,map_pow,lowL_eval]
    linarith
  · have hh := negative_norm_sq_le (q:=1) hk (by norm_num) hzcap hscap
    norm_num only [lowPHh,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,eq_ratCast,
      lowK_eval,Rat.cast_mul,sh_cast]
    nlinarith only [hh]
  · rw [zero_norm_sq]
    simp [lowPH0,add_comm]
  · have hh := negative_norm_sq_le hk hl hzcap hscap
    norm_num only [lowPGh,map_add,map_sub,map_mul,map_pow,aeval_C,eq_ratCast,
      lowK_eval,lowL_eval,Rat.cast_mul,sh_cast]
    nlinarith only [hh]

theorem low_J_lower {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    aeval z lowJ≤Explicit.lowK z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
      Explicit.lowL z*(Real.cos frameCap-Real.cos z) := by
  have hz' := low_frame_domain hz
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have ht := taylor_bounds hz'
  have htcap := taylor_bounds (show frameCap∈Icc 0 frameCap by
    exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hs : 0≤Real.sin z := (transport_trig hz').2.2.1
  have hc : 0≤Real.cos z := by linarith [(transport_trig hz').1]
  have hsum : (ch:ℝ)+(sh:ℝ)≤Real.cos frameCap+Real.sin frameCap := by
    rw [ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.1]
  have hsum0 : 0≤Real.cos frameCap+Real.sin frameCap := by
    have tt := transport_trig (show frameCap∈Icc 0 frameCap by
      exact ⟨by norm_num [frameCap],le_rfl⟩)
    linarith [tt.1,tt.2.2.1]
  have hprod := mul_le_mul hsum ht.2.2.2.2.1
    (show 0≤aeval z C10 by linarith [ht.2.2.2.1]) hsum0
  have hdiff : Real.cos frameCap-Real.sin frameCap≤(Ch:ℝ)-(sh:ℝ) := by
    rw [Ch_cast,sh_cast]
    linarith [htcap.2.1,htcap.2.2.2.2.2]
  have hdiff0 : 0≤(Ch:ℝ)-(sh:ℝ) := by
    have tt := transport_trig (show frameCap∈Icc 0 frameCap by
      exact ⟨by norm_num [frameCap],le_rfl⟩)
    linarith [tt.2.2.2.2]
  have hprod' := mul_le_mul hdiff ht.2.2.1 hs hdiff0
  have hphi : PositiveAngularEnvelope.phi (frameCap-z)=
      (Real.cos frameCap+Real.sin frameCap)*Real.cos z-
        (Real.cos frameCap-Real.sin frameCap)*Real.sin z := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  have hphiLower : ((ch:ℝ)+(sh:ℝ))*aeval z C10-
      ((Ch:ℝ)-(sh:ℝ))*aeval z S9≤PositiveAngularEnvelope.phi (frameCap-z) := by
    rw [hphi]
    linarith
  have hkprod := mul_le_mul_of_nonneg_left (sub_le_sub_right hphiLower 1)
    (show 0≤Explicit.lowK z by linarith)
  have hcos : (ch:ℝ)-aeval z C12≤Real.cos frameCap-Real.cos z := by
    rw [ch_cast]
    linarith [htcap.2.2.2.2.1,ht.2.2.2.2.2]
  have hlprod := mul_le_mul_of_nonneg_left hcos
    (show 0≤Explicit.lowL z by linarith)
  norm_num only [lowJ,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,lowK_eval,lowL_eval,
    Rat.cast_add,Rat.cast_sub]
  linarith only [hkprod,hlprod]

theorem lowPM_num3 :
    lowPM=num3 (lowA+lowJ) lowPH lowPG lowPB lowRH lowRG lowRB := by
  dsimp [lowPM,lowP,lowDen,num3]
  ring

theorem low_H_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
      V R (Explicit.lowK z) 1 z := by
  have hr := low_masses_positive hz
  have hn := low_norm_bounds hz
  have h := num3_transfer hr.1 hr.2.1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.1 (low_nonradical_lower hz).1 (lowP_positive hz)
  have hc : 1≤Explicit.lowC z := by
    have hh := Explicit.low_ranges hz
    linarith [hh.2.2.1,hh.2.2.2.1]
  rw [low_H_identity hc]
  exact h

theorem low_M_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
      V R (Explicit.lowK z) 1 z+Explicit.lowK z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
        Explicit.lowL z*(Real.cos frameCap-Real.cos z) := by
  have hr := low_masses_positive hz
  have hn := low_norm_bounds hz
  have hA : aeval z (lowA+lowJ)≤
      lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
        Real.cos z-1+(Explicit.lowK z*(PositiveAngularEnvelope.phi (frameCap-z)-1)+
          Explicit.lowL z*(Real.cos frameCap-Real.cos z)) := by
    simpa only [map_add] using add_le_add (low_nonradical_lower hz).1 (low_J_lower hz)
  have hp : 0<aeval z (num3 (lowA+lowJ) lowPH lowPG lowPB lowRH lowRG lowRB) := by
    rw [← lowPM_num3]
    exact lowPM_positive hz
  have h := num3_transfer hr.1 hr.2.1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.1 hn.2.1 hn.2.2.1 hA hp
  have hc : 1≤Explicit.lowC z := by
    have hh := Explicit.low_ranges hz
    linarith [hh.2.2.1,hh.2.2.2.1]
  rw [low_H_identity hc]
  linarith only [h]

theorem low_SH_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
      (109/200)*tilted (Explicit.lowC z) z*(frameCap-z)+V R (Explicit.lowK z) 1 frameCap := by
  have hr := low_masses_positive hz
  have hn := low_norm_bounds hz
  have htcap := taylor_bounds (show frameCap∈Icc 0 frameCap by
    exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hA : aeval z (lowAstar+C (ch-1))≤
      lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
        (109/200)*tilted (Explicit.lowC z) z*(frameCap-z)+Real.cos frameCap-1 := by
    have hh := (low_nonradical_lower hz).2
    norm_num only [map_add,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,ch_cast]
    linarith [htcap.2.2.2.2.1]
  have h := num3_transfer (show 0<aeval z (C (77/100):ℚ[X]) by norm_num)
    hr.2.1 hr.2.2 (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.1 hn.2.1 hn.2.2.1 hA (lowPSH_positive hz)
  have hc : 1≤Explicit.lowC z := by
    have hh := Explicit.low_ranges hz
    linarith [hh.2.2.1,hh.2.2.2.1]
  have he := low_H_identity (k:=Explicit.lowK z) (l:=Explicit.lowL z)
    (c:=Explicit.lowC z) (z:=z) (t:=frameCap) hc
  linarith only [h,he]

theorem low_SG_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
      (109/200)*tilted (Explicit.lowC z) z*(frameCap-z)+
        V R (Explicit.lowK z) (Explicit.lowL z) frameCap := by
  have hr := low_masses_positive hz
  have hn := low_norm_bounds hz
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have hr0 : 0<aeval z lowRHzero := by
    norm_num only [lowRHzero,map_add,map_mul,aeval_C,eq_ratCast,lowK_eval]
    linarith
  have hr1 : 0<aeval z lowRGcap := by
    norm_num only [lowRGcap,map_mul,aeval_C,eq_ratCast,lowL_eval]
    linarith
  have htcap := taylor_bounds (show frameCap∈Icc 0 frameCap by
    exact ⟨by norm_num [frameCap],le_rfl⟩)
  have hcos : (ch:ℝ)-1≤Real.cos frameCap-1 := by
    rw [ch_cast]
    linarith [htcap.2.2.2.2.1]
  have hp := mul_le_mul_of_nonneg_left hcos (show 0≤Explicit.lowL z by linarith)
  have hA : aeval z (lowAstar+lowL*C (ch-1))≤
      lowNonradical (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z-
        (109/200)*tilted (Explicit.lowC z) z*(frameCap-z)+
          Explicit.lowL z*(Real.cos frameCap-1) := by
    have hh := (low_nonradical_lower hz).2
    norm_num only [map_add,map_mul,aeval_C,eq_ratCast,Rat.cast_sub,Rat.cast_one,lowL_eval]
    linarith only [hh,hp]
  have h := num3_transfer hr0 hr1 hr.2.2
    (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _) (pairNorm_nonneg _ _ _)
    hn.2.2.2.2.1 hn.2.2.2.2.2 hn.2.2.1 hA (lowPSG_positive hz)
  have he := low_G_identity (k:=Explicit.lowK z) (l:=Explicit.lowL z)
    (c:=Explicit.lowC z) (z:=z) (t:=frameCap) (by linarith : 1≤Explicit.lowC z)
  linarith only [h,he]

/-- Concrete positivity for every intrinsic alternative on the whole
low interval, with no residual scalar premise. -/
theorem low_endpoint_positive {z : ℝ} (hz : z∈Icc 0 (1/6:ℝ)) (i j : Fin 4) :
    0<baseline (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z+
      endpoint (Explicit.lowK z) (Explicit.lowL z) (Explicit.lowC z) z i j := by
  obtain ⟨hklo,hkhi,hllo,hlc,hchi,hlk⟩ := Explicit.low_ranges hz
  have hm := Explicit.low_tilted hz
  exact low_scalars_positive ⟨hklo.le,by linarith⟩ ⟨hllo.le,hlk.le⟩
    ⟨hm.1,hm.2.le⟩ hz (low_H_positive hz) (low_M_positive hz)
    (low_SH_positive hz) (low_SG_positive hz) i j

end SquaresInCircles.Eight.GlobalGA.PositiveTD.Certificate
