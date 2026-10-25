module

public import SquaresInCircles.Eight.TableFree.FrameLowMidContact

/-!
# Both endpoint continuations for middle-to-low transverse pairs

After the exact positive contact, the target support is decreasing on
the entire low arc and therefore reaches its minimum at the intrinsic
upper endpoint.  For the two negative tangents it is increasing on that
arc and reaches its minimum at the axial endpoint.  Harmonic derivative
bounds control the complete remaining angle intervals.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidSecondaryContinuation
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidGeometry

def lam : ℝ := 797/1000
def half : ℝ := (lam-9/50)/2
def P : ℝ := lam*a1-half
def Q : ℝ := half+lam*b1
def base : ℝ := (lam+9/50)/2+M1-L1-lam*b1
def F (x : ℝ) : ℝ := x+base-P*Real.sin x+Q*Real.cos x

theorem coefficient_bounds : 0≤P ∧ P≤727/1000 ∧ 0≤Q ∧ Q≤71/125 := by
  dsimp [P,Q,half,lam]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith [a1_precise.1,a1_precise.2,FrameLowMidArc.b1_precise.1,FrameLowMidArc.b1_precise.2]

theorem coefficient_norm : P^2+Q^2<1 := by
  have hb := coefficient_bounds
  have hp := pow_le_pow_left₀ hb.1 hb.2.1 2
  have hq := pow_le_pow_left₀ hb.2.2.1 hb.2.2.2 2
  nlinarith

theorem F_deriv (x : ℝ) : HasDerivAt F (1-P*Real.cos x-Q*Real.sin x) x := by
  refine (((hasDerivAt_id x).add_const base).sub
    ((Real.hasDerivAt_sin x).const_mul P)).add
      ((Real.hasDerivAt_cos x).const_mul Q) |>.congr_deriv ?_
  ring

theorem F_monotone : MonotoneOn F (Icc (79/100:ℝ) (19/20)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv x
  · intro x hx
    have hh := harmonic_projection_lt_one (A := Q) (B := P) (x := x)
      (by nlinarith [coefficient_norm])
    linarith

theorem F_endpoint : (4503/5000:ℝ)<F (79/100:ℝ) := by
  have ht := FrameLowMidContact.endpoint_trig
  have hb := coefficient_bounds
  have hPu : P≤lam*(1298747249/1000000000)-half := by
    dsimp [P,lam]
    linarith [a1_precise.2]
  have hQl : half+lam*(1298747247/4000000000)≤Q := by
    dsimp [Q,lam]
    linarith [FrameLowMidArc.b1_precise.1]
  have hPupos : 0≤lam*(1298747249/1000000000)-half := by norm_num [lam,half]
  have hQpos : 0≤half+lam*(1298747247/4000000000) := by norm_num [lam,half]
  have hP := mul_le_mul hPu ht.2.1.le (by linarith [ht.1] : 0≤Real.sin (79/100:ℝ)) hPupos
  have hQ := mul_le_mul hQl ht.2.2.1.le (by norm_num : (0:ℝ)≤1759613289/2500000000) hb.2.2.1
  have hbase : (lam+9/50)/2+1523/5000-30683/100000-
      lam*(1298747249/4000000000)≤base := by
    dsimp [base,lam]
    linarith [M_endpoints.1,L1_precise.2,FrameLowMidArc.b1_precise.2]
  dsimp [F]
  norm_num [lam,half] at hP hQ hbase
  linarith

theorem F_lower {x : ℝ} (hx : x∈Icc (79/100:ℝ) (19/20)) : (1801/2000:ℝ)<F x := by
  have hh := F_monotone ⟨le_rfl,by norm_num⟩ hx hx.1
  linarith [F_endpoint]

theorem target_antitone {x : ℝ} (hx : x∈Icc (79/100:ℝ) (19/20)) :
    AntitoneOn (linear (-FrameLowArc.u-lam*Real.sin x)
      (lam*Real.cos x-FrameLowArc.v)) (Icc 0 b1) := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos] : -(Real.pi/2)≤x)
    (by linarith [FrameLowPair.pi_lower] : (19/20:ℝ)≤Real.pi/2) hx.2
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤79/100) (by linarith [hxq.2,Real.pi_pos]) hx.1
  have hsE := sin_upper_five (show (0:ℝ)≤19/20 by norm_num)
  have hcE := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤79/100 by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hcE
  norm_num at hsE
  have hsU : Real.sin x≤407/500 := by linarith
  have hcU : Real.cos x≤88/125 := by linarith
  have hp : 0≤FrameLowArc.u+lam*Real.sin x := by
    dsimp [FrameLowArc.u,lam]
    linarith [ht.1]
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (linear_hasDerivAt ⟨hB.1,hB.2.trans b1_mem.2⟩ _ _).continuousAt.continuousWithinAt
  · intro B hB
    exact linear_hasDerivAt ⟨hB.1.le,hB.2.le.trans b1_mem.2⟩ _ _
  · intro B hB
    have hratio := slope_bounds (Ioo_subset_Icc_self hB)
    have hh := mul_le_mul_of_nonneg_left hratio.2.le hp
    have hAd : Ad B= -FrameLowArc.slope B := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp [FrameLowArc.u,FrameLowArc.v,lam] at hh ⊢
    linarith

theorem positive_weak_separator {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (79/100:ℝ) (19/20)) (hm : 0≤ secondary true true b B x) :
    (1801/2000:ℝ)< midLowCost true true b B x := by
  have hs := middle_small_source hb
  have ht := target_antitone hx hB ⟨b1_mem.1,le_rfl⟩ hB.2
  dsimp [linear] at ht
  rw [A_b1] at ht
  have hscaled := mul_nonneg (show (0:ℝ)≤lam by norm_num [lam]) hm
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hF : F x≤ midLowCost true true b B x := by
    dsimp [secondary] at hscaled
    rw [(first_width hxq).1] at hscaled
    dsimp [F,base,P,Q,half,midLowCost,L,L1]
    rw [(first_width hxq).2]
    norm_num [sign] at hscaled ⊢
    dsimp [lam] at ht hscaled ⊢
    nlinarith
  exact (F_lower hx).trans_le hF

def axialP : ℝ := a0-41/100
def axialF (x : ℝ) : ℝ :=
  x+59/100-M1+b1-axialP*Real.sin x+(41/100)*Real.cos x

theorem axial_norm : 0≤axialP ∧ axialP≤201/200 ∧
    axialP^2+(41/100:ℝ)^2<(109/100:ℝ)^2 := by
  have hp : 0≤axialP ∧ axialP≤201/200 := by
    dsimp [axialP]
    constructor <;> linarith [a0_precise.1,a0_precise.2]
  have hs := pow_le_pow_left₀ hp.1 hp.2 2
  exact ⟨hp.1,hp.2,by nlinarith⟩

theorem axial_deriv (x : ℝ) :
    HasDerivAt axialF (1-axialP*Real.cos x-(41/100)*Real.sin x) x := by
  refine (((((hasDerivAt_id x).add_const (59/100)).sub_const M1).add_const b1).sub
    ((Real.hasDerivAt_sin x).const_mul axialP)).add
      ((Real.hasDerivAt_cos x).const_mul (41/100)) |>.congr_deriv ?_
  ring

theorem axial_corrected_monotone :
    MonotoneOn (fun x => axialF x+(9/100)*x) (Icc (19/25:ℝ) (7/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact ((axial_deriv x).add ((hasDerivAt_id x).const_mul (9/100))).continuousAt.continuousWithinAt
  · exact fun x hx => (axial_deriv x).add ((hasDerivAt_id x).const_mul (9/100))
  · intro x hx
    have hh := FrameCoreArc.projection_lt (a := (41/100:ℝ)) (b := axialP)
      (x := x) (show (0:ℝ)<109/100 by norm_num) (by nlinarith [axial_norm.2.2])
    linarith

theorem axial_endpoint : (97/100:ℝ)<axialF (19/25:ℝ) := by
  have hs := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤19/25 by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤19/25 by norm_num)
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hc
  have hsU : Real.sin (19/25:ℝ)≤689/1000 := by linarith
  have hcL : (453/625:ℝ)≤Real.cos (19/25:ℝ) := by linarith
  have hs0 : 0≤Real.sin (19/25:ℝ) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by norm_num) (by linarith [FrameLowPair.pi_lower])
  have hp := mul_le_mul axial_norm.2.1 hsU hs0 (by norm_num : (0:ℝ)≤201/200)
  dsimp [axialF]
  linarith [M_endpoints.2.1,FrameLowMidArc.b1_precise.1]

theorem axial_lower {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) :
    (1801/2000:ℝ)<axialF x := by
  have hh := axial_corrected_monotone ⟨le_rfl,by norm_num⟩ hx hx.1
  linarith [axial_endpoint,hx.2]

theorem negative_weak_separator {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (19/25:ℝ) (7/5)) (hm : 0≤ secondary false false b B x) :
    (1801/2000:ℝ)< midLowCost false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hsL := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(19/25:ℝ)) hxq.2 hx.1
  have hsE := Real.sin_ge_sub_cube (show (0:ℝ)≤19/25 by norm_num)
  norm_num at hsE
  have hp : FrameLowArc.u-Real.sin x≤0 := by dsimp [FrameLowArc.u]; linarith
  have hq : 0≤FrameLowArc.v-Real.cos x := by dsimp [FrameLowArc.v]; linarith [Real.cos_le_one x]
  have ht := linear_monotone hp hq ⟨le_rfl,by linarith [c0_bounds.1]⟩
    ⟨hB.1,hB.2.trans b1_mem.2⟩ hB.1
  dsimp [linear] at ht
  rw [A_zero] at ht
  have hs := middle_negative_source hb (show (1:ℝ)≤1 by norm_num)
  have hF : axialF x≤ midLowCost false false b B x := by
    dsimp [secondary] at hm
    rw [(first_width hxq).1] at hm
    dsimp [axialF,axialP,midLowCost,L]
    rw [(first_width hxq).2]
    norm_num [sign] at hm ⊢
    nlinarith
  exact (axial_lower hx).trans_le hF

end SquaresInCircles.Eight.TableFree.FrameLowMidSecondaryContinuation
