module

public import SquaresInCircles.Eight.Frames.Core.HighHighPrimary
public import SquaresInCircles.Eight.Frames.Core.HighHighSecondaryScalars
public import SquaresInCircles.Eight.Frames.Core.LowPair
public import SquaresInCircles.Eight.Frames.Core.HighSecondaryNorm

/-!
# Eight squares: the complete original core/high frame-pair inequality

Both orientations, both original tangent signs and every weak forward
separating axis are included.  The angle restrictions used internally
are derived from the original exterior gap and the original witnesses.
No concentrated frame, selected owner or strict separation is assumed.
-/

section
/-!
## Whole-interval circle supports for a core-source transverse witness

The negative high tangent has a concave support up to angle `6/5`.
The positive high tangent has concave supports on both sides of the
quarter turn, meeting at the exact previously established quarter value.
All radical bounds are consequences of the actual rotating norms.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighSecondaryScalars
open FramePair FrameCircleArc FrameHighArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreMidScalars (ap cp)
open FrameCoreHighSecondaryNorm

def Cminus : ℝ := ap+(u-v)/2+k
def Cplus : ℝ := ap-(u-v)/2-k
def Fminus (x : ℝ) : ℝ :=
  x+Cminus+(g-9/100)*(Real.sin x+Real.cos x)-R*N false x
def FminusD (x : ℝ) : ℝ :=
  1+(g-9/100)*(Real.cos x-Real.sin x)-R*Nd false x
def FminusDD (x : ℝ) : ℝ :=
  -(g-9/100)*(Real.sin x+Real.cos x)-R*Ndd false x
def FplusFirst (x : ℝ) : ℝ :=
  x+Cplus+(g-9/100)*Real.sin x-(9/100)*Real.cos x-R*N true x
def FplusFirstD (x : ℝ) : ℝ :=
  1+(g-9/100)*Real.cos x+(9/100)*Real.sin x-R*Nd true x
def FplusFirstDD (x : ℝ) : ℝ :=
  -(g-9/100)*Real.sin x+(9/100)*Real.cos x-R*Ndd true x
def FplusSecond (x : ℝ) : ℝ :=
  x+Cplus+(g-9/100)*(Real.sin x-Real.cos x)-R*N true x
def FplusSecondD (x : ℝ) : ℝ :=
  1+(g-9/100)*(Real.cos x+Real.sin x)-R*Nd true x
def FplusSecondDD (x : ℝ) : ℝ :=
  (g-9/100)*(Real.cos x-Real.sin x)-R*Ndd true x

theorem Fminus_deriv (x : ℝ) : HasDerivAt Fminus (FminusD x) x := by
  have h := (((hasDerivAt_id' x).add_const Cminus).fun_add
    (((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul (g-9/100))).fun_sub
      ((N_deriv false x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FminusD]; ring

theorem FminusD_deriv (x : ℝ) : HasDerivAt FminusD (FminusDD x) x := by
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (g-9/100)).const_add 1).fun_sub ((Nd_deriv false x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FminusDD]; ring

theorem FplusFirst_deriv (x : ℝ) : HasDerivAt FplusFirst (FplusFirstD x) x := by
  have h := ((((hasDerivAt_id' x).add_const Cplus).fun_add
    ((Real.hasDerivAt_sin x).const_mul (g-9/100))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (9/100))).fun_sub
        ((N_deriv true x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FplusFirstD]; ring

theorem FplusFirstD_deriv (x : ℝ) : HasDerivAt FplusFirstD (FplusFirstDD x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (g-9/100)).const_add 1).fun_add
    ((Real.hasDerivAt_sin x).const_mul (9/100))).fun_sub
      ((Nd_deriv true x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FplusFirstDD]; ring

theorem FplusSecond_deriv (x : ℝ) : HasDerivAt FplusSecond (FplusSecondD x) x := by
  have h := (((hasDerivAt_id' x).add_const Cplus).fun_add
    (((Real.hasDerivAt_sin x).fun_sub (Real.hasDerivAt_cos x)).const_mul (g-9/100))).fun_sub
      ((N_deriv true x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FplusSecondD]; ring

theorem FplusSecondD_deriv (x : ℝ) : HasDerivAt FplusSecondD (FplusSecondDD x) x := by
  have h := ((((Real.hasDerivAt_cos x).fun_add (Real.hasDerivAt_sin x)).const_mul
    (g-9/100)).const_add 1).fun_sub ((Nd_deriv true x).const_mul R)
  convert h using 1
  · rfl
  · simp only [FplusSecondDD]; ring

theorem Fminus_concave : ConcaveOn ℝ (Icc (0:ℝ) (6/5)) Fminus := by
  apply concave_of_deriv2 (fun x _ => Fminus_deriv x) (fun x _ => FminusD_deriv x)
  intro x hx
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hxq).1] at hw
  have hh := curvature_work false x
  dsimp [FminusDD,g] at *
  linarith

theorem FplusFirst_concave :
    ConcaveOn ℝ (Icc (7/5:ℝ) (Real.pi/2)) FplusFirst := by
  apply concave_of_deriv2 (fun x _ => FplusFirst_deriv x)
    (fun x _ => FplusFirstD_deriv x)
  intro x hx
  have ht := positive_first_trig hx
  have hh := mul_pos R_pos (positive_norm_curvature hx)
  dsimp [FplusFirstDD,g] at *
  linarith

theorem FplusSecond_concave :
    ConcaveOn ℝ (Icc (Real.pi/2) (5/2:ℝ)) FplusSecond := by
  apply concave_of_deriv2 (fun x _ => FplusSecond_deriv x)
    (fun x _ => FplusSecondD_deriv x)
  intro x hx
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hw := FrameCoreArc.width_one_le x
  rw [(second_width hxq).1] at hw
  have hh := curvature_work true x
  dsimp [FplusSecondDD,g] at *
  linarith

theorem minus_endpoints :
    (221/250:ℝ)<Fminus 0 ∧ (51/50:ℝ)<Fminus (6/5) := by
  have hR0 : R*N false 0<radiusUpper*(223/250) :=
    mul_lt_mul'' radius_bound norm_endpoints.1 R_pos.le (N_pos false 0).le
  have hR1 : R*N false (6/5)<radiusUpper*(63/40) :=
    mul_lt_mul'' radius_bound norm_endpoints.2.1 R_pos.le (N_pos false (6/5)).le
  have hk := k_bounds.1
  have ht := FrameCoreMidScalars.trig_six_fifths
  constructor
  · dsimp [Fminus,Cminus,ap,g,u,v,radiusUpper] at hR0 hk ⊢
    simp only [Real.sin_zero,Real.cos_zero]
    linarith
  · dsimp [Fminus,Cminus,ap,g,u,v,radiusUpper] at hR1 hk ⊢
    linarith [ht.1,ht.2.2.1]

theorem positive_start : (221/250:ℝ)<FplusFirst (7/5) := by
  have hR : R*N true (7/5)<radiusUpper*(67/125) :=
    mul_lt_mul'' radius_bound norm_endpoints.2.2.1 R_pos.le (N_pos true (7/5)).le
  have ht := trig_seven_fifths
  have hk := k_bounds.2.1
  dsimp [FplusFirst,Cplus,ap,g,u,v,radiusUpper] at hR hk ⊢
  linarith [ht.1,ht.2.2.2]

theorem quarter_first :
    FplusFirst (Real.pi/2)=FrameCoreHighPrimaryContinuation.quarterValue := by
  dsimp [FplusFirst,Cplus,ap,FrameCoreHighPrimaryContinuation.quarterValue,k]
  rw [positive_quarter_norm]
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,sub_zero]
  ring

theorem quarter_second :
    FplusSecond (Real.pi/2)=FrameCoreHighPrimaryContinuation.quarterValue := by
  dsimp [FplusSecond,Cplus,ap,FrameCoreHighPrimaryContinuation.quarterValue,k]
  rw [positive_quarter_norm]
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,sub_zero]
  ring

theorem positive_end : (97/100:ℝ)<FplusSecond (5/2) := by
  have hR : R*N true (5/2)<radiusUpper*(63/50) :=
    mul_lt_mul'' radius_bound norm_endpoints.2.2.2 R_pos.le (N_pos true (5/2)).le
  have hs := FrameCoreHighCorePrimary.trig_endpoints.2.2.2.1
  have hc := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤5/2 by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hc
  have hk := k_bounds.2.1
  dsimp [FplusSecond,Cplus,ap,g,u,v,radiusUpper] at hR hk ⊢
  linarith

theorem minus_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) :
    (8833/10000:ℝ)<Fminus x :=
  concave_gt_of_endpoints Fminus_concave hx
    (by linarith [minus_endpoints.1]) (by linarith [minus_endpoints.2])

theorem positive_first_lower {x : ℝ} (hx : x∈Icc (7/5:ℝ) (Real.pi/2)) :
    (8833/10000:ℝ)<FplusFirst x := by
  apply concave_gt_of_endpoints FplusFirst_concave hx
  · linarith [positive_start]
  · rw [quarter_first]
    linarith [FrameCoreHighPrimaryContinuation.quarter_lower]

theorem positive_second_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (5/2:ℝ)) :
    (8833/10000:ℝ)<FplusSecond x := by
  apply concave_gt_of_endpoints FplusSecond_concave hx
  · rw [quarter_second]
    linarith [FrameCoreHighPrimaryContinuation.quarter_lower]
  · linarith [positive_end]

end SquaresInCircles.Eight.FrameCoreHighSecondaryScalars
end
end
end

section
/-!
## The secondary axis of a core source against a high target

A core state and a high state `B` separated along the secondary axis of the core square, at a
frame angle `x ∈ [-203/250, 5/2]`, have the cost of the pair above `8833/10000`, for both signs
of the source and of the target (`core_secondary`). The weak margin leaves a nonnegative core
residual, so the cost is at least `common j x` plus a linear function of the target state
(`support`). That function is bounded by its values at the two ends of the high arc where its
derivative has a sign (`positive_target_small_angle`, `negative_target_negative_angle`,
`negative_target_large_angle`), and otherwise by the support of the whole circle
(`fullCircle_support`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighCoreSecondary
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (g a2 b2 b2_mem A_b2)
open FrameLowArc (slope)
open FrameCoreHighGeometry FrameCoreHighSecondaryScalars FrameCoreHighSecondaryEndpoints

def P (j : Bool) (x : ℝ) : ℝ := sign j*u-g*Real.sin x
def Q (j : Bool) (x : ℝ) : ℝ := sign j*(g*Real.cos x-v)
def common (j : Bool) (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-sign j*k+g*pairWidth x
def fullCircle (j : Bool) (x : ℝ) : ℝ :=
  common j x-R*FrameCoreHighSecondaryNorm.N j x-(P j x+Q j x)/2
def positiveEndpoint (r : Bool) (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x-endpointH r-g*endpointA r*Real.sin x+
    g*endpointB r*Real.cos x+g*pairWidth x
def slopePulse (x : ℝ) : ℝ :=
  g*((149/250)*Real.sin x+Real.cos x)-(149/250)*u-v

theorem support (i j : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hm : 0≤coreHighSecondary i j a b B x) :
    common j x+linear (P j x) (Q j x) B≤coreHighCost i j a b B x := by
  have hf := core_secondary_source_floor i j hc hB hm
  have hh := mul_nonneg (show 0≤g by norm_num [g]) hm
  dsimp [common,linear,P,Q,coreHighCost,coreHighSecondary,H] at *
  nlinarith

theorem norm_identity (j : Bool) (x : ℝ) :
    Real.sqrt ((P j x)^2+(Q j x)^2)=FrameCoreHighSecondaryNorm.N j x := by
  dsimp [FrameCoreHighSecondaryNorm.N,CircularNorm.norm,CircularNorm.energy,
    FrameCoreHighSecondaryNorm.E,FrameCoreHighSecondaryNorm.B,FrameCoreHighSecondaryNorm.C,P,Q]
  congr 1
  have ht := congrArg (fun z : ℝ => g^2*z) (Real.sin_sq_add_cos_sq x)
  cases j <;> dsimp [sign] <;> nlinarith

theorem fullCircle_support (i j : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hm : 0≤coreHighSecondary i j a b B x) :
    fullCircle j x≤coreHighCost i j a b B x := by
  have hs := support i j hc hB hm
  have hh := circle_linear_lower (A_circle ⟨b2_mem.1.trans hB.1,hB.2⟩) (P j x) (Q j x)
  rw [norm_identity] at hh
  change -R*FrameCoreHighSecondaryNorm.N j x-(P j x+Q j x)/2≤linear (P j x) (Q j x) B at hh
  dsimp [fullCircle]
  linarith

theorem circle_minus {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    fullCircle false x=Fminus x := by
  dsimp [fullCircle,common,P,Q,sign,Fminus,Cminus,FrameCoreMidScalars.ap]
  rw [(first_width hx).1,(first_width hx).2]
  ring

theorem circle_positive_first {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    fullCircle true x=FplusFirst x := by
  dsimp [fullCircle,common,P,Q,sign,FplusFirst,Cplus,FrameCoreMidScalars.ap]
  rw [(first_width hx).1,(first_width hx).2]
  ring

theorem circle_positive_second {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    fullCircle true x=FplusSecond x := by
  dsimp [fullCircle,common,P,Q,sign,FplusSecond,Cplus,FrameCoreMidScalars.ap]
  rw [(second_width hx).1,(second_width hx).2]
  ring

theorem negative_target_linear {z B : ℝ}
    (hz : z∈Icc (0:ℝ) (203/250)) (hB : B∈Icc b2 c0) :
    linear (-u+g*Real.sin z) (v-g*Real.cos z) c0≤
      linear (-u+g*Real.sin z) (v-g*Real.cos z) B := by
  have hzq : z∈Icc 0 (Real.pi/2) :=
    ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hz.1
    (by linarith [FrameLowPair.pi_lower] : (203/250:ℝ)≤Real.pi) hz.2
  have hq : v-g*Real.cos z<0 := by
    have he := trig_negative_end.2
    dsimp [g,v]
    linarith
  have hsum := width_one_le z
  rw [(first_width hzq).1] at hsum
  have hm : AntitoneOn (linear (-u+g*Real.sin z) (v-g*Real.cos z)) (Icc b2 c0) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun t ht =>
        (linear_hasDerivAt ⟨b2_mem.1.trans ht.1,ht.2⟩ _ _).continuousAt.continuousWithinAt
    · exact fun t ht => linear_hasDerivAt ⟨b2_mem.1.trans ht.1.le,ht.2.le⟩ _ _
    · intro t ht
      have ht' := Ioo_subset_Icc_self ht
      by_cases hp : 0≤-u+g*Real.sin z
      · have hh := mul_nonpos_of_nonneg_of_nonpos hp
          (Ad_nonpos ⟨b2_mem.1.trans ht'.1,ht'.2⟩)
        linarith
      · have hmul := mul_le_mul_of_nonneg_left (slope_high_bounds ht').2
          (show 0≤-(-u+g*Real.sin z) by linarith)
        have he : (-u+g*Real.sin z)*Ad t+(v-g*Real.cos z)=
            (-(-u+g*Real.sin z))*FrameLowArc.slope t+(v-g*Real.cos z) := by
          dsimp [Ad,FrameLowArc.slope]; ring
        rw [he]
        dsimp [g,u,v] at *
        linarith
  exact hm hB ⟨b2_mem.2,le_rfl⟩ hB.2

theorem negative_target_negative_angle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(203/250:ℝ)) 0)
    (hm : 0≤coreHighSecondary i false a b B x) :
    (8833/10000:ℝ)<coreHighCost i false a b B x := by
  have hz : -x∈Icc (0:ℝ) (203/250) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hl := negative_target_linear hz hB
  simp only [Real.sin_neg,Real.cos_neg] at hl
  have hs := support i false hc hB hm
  have he : common false x+linear (P false x) (Q false x) c0=negativeDiagonal (-x) := by
    dsimp [common,linear,P,Q,sign,negativeDiagonal,FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
    rw [A_c0,(FrameCoreHighGeometry.negative_width hx).1,
      (FrameCoreHighGeometry.negative_width hx).2,Real.sin_neg,Real.cos_neg]
    dsimp [k]
    ring
  have hlinear : linear (P false x) (Q false x) c0≤linear (P false x) (Q false x) B := by
    simpa [P,Q,sign,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hl
  have hbound := negativeDiagonal_lower hz
  rw [← he] at hbound
  linarith

theorem negative_target_large_angle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : x∈Icc (6/5:ℝ) (5/2))
    (hm : 0≤coreHighSecondary i false a b B x) :
    (8833/10000:ℝ)<coreHighCost i false a b B x := by
  have hs0 : 0≤Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hx.1]) (by linarith [hx.2,FrameLowPair.pi_lower])
  have hcU := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤6/5)
    (by linarith [hx.2,FrameLowPair.pi_lower]) hx.1
  have hp : P false x≤0 := by dsimp [P,sign,u,g]; linarith
  have hq : 0≤Q false x := by
    have ht := FrameCoreMidScalars.trig_six_fifths.2.2.2
    dsimp [Q,sign,v,g]
    linarith
  have hl := linear_monotone hp hq b2_mem ⟨b2_mem.1.trans hB.1,hB.2⟩ hB.1
  have hs := support i false hc hB hm
  have he : common false x+linear (P false x) (Q false x) b2=negativeCut x := by
    dsimp [common,linear,P,Q,sign,negativeCut,H2]
    rw [A_b2]
    ring
  have hbnd := negativeCut_lower hx
  rw [← he] at hbnd
  linarith

theorem slopePulse_concave : ConcaveOn ℝ (Icc (0:ℝ) (7/5)) slopePulse := by
  apply concave_of_deriv2
    (f' := fun x => g*((149/250)*Real.cos x-Real.sin x))
    (f'' := fun x => -g*((149/250)*Real.sin x+Real.cos x))
  · intro x _
    have h := (((((Real.hasDerivAt_sin x).const_mul (149/250)).fun_add
      (Real.hasDerivAt_cos x)).const_mul g).sub_const ((149/250)*u)).sub_const v
    convert h using 1
    funext y; simp only [slopePulse]
  · intro x _
    convert ((((Real.hasDerivAt_cos x).const_mul (149/250)).fun_sub
      (Real.hasDerivAt_sin x)).const_mul g) using 1
    ring
  · intro x hx
    have ht := FrameLowPair.quadrant
      (show x∈Icc 0 (Real.pi/2) from ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
    norm_num [g]
    linarith [ht.1,ht.2.2.1]

theorem slopePulse_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/5)) : 0<slopePulse x := by
  apply concave_gt_of_endpoints slopePulse_concave hx
  · norm_num [slopePulse,g,u,v]
  · have ht := FrameCoreHighSecondaryNorm.trig_seven_fifths
    dsimp [slopePulse,g,u,v]
    linarith

theorem positive_target_linear {x B : ℝ}
    (hx : x∈Icc (-(203/250:ℝ)) (7/5)) (hB : B∈Icc b2 c0) :
    min (linear (P true x) (Q true x) b2) (linear (P true x) (Q true x) c0)≤
      linear (P true x) (Q true x) B := by
  by_cases hp : 0≤P true x
  · exact linear_endpoint_lower hp b2_mem.1 le_rfl hB
  · have hx0 : 0≤x := by
      by_contra! hn
      have ht := negative_trig ⟨hx.1,hn.le⟩
      dsimp [P,sign,g,u] at hp
      linarith
    have hpulse := slopePulse_positive ⟨hx0,hx.2⟩
    have hm : MonotoneOn (linear (P true x) (Q true x)) (Icc b2 c0) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun t ht => (linear_hasDerivAt ⟨b2_mem.1.trans ht.1,ht.2⟩
          (P true x) (Q true x)).continuousAt.continuousWithinAt
      · exact fun t ht => linear_hasDerivAt ⟨b2_mem.1.trans ht.1.le,ht.2.le⟩ (P true x) (Q true x)
      · intro t ht
        have hr := (slope_high_bounds (Ioo_subset_Icc_self ht)).1
        have hmul := mul_le_mul_of_nonneg_left hr.le
          (show 0≤-P true x by linarith)
        have he : P true x*Ad t+Q true x=(-P true x)*FrameLowArc.slope t+Q true x := by
          dsimp [Ad,FrameLowArc.slope]
          ring
        rw [he]
        dsimp [P,Q,sign,slopePulse] at *
        linarith
    exact (min_le_left _ _).trans (hm ⟨le_rfl,b2_mem.2⟩ hB hB.1)

theorem positiveEndpoint_first (r : Bool) {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    positiveEndpoint r x=positiveFirst r x := by
  dsimp [positiveEndpoint,positiveFirst,FrameCoreMidScalars.trigAffine,D,B,
    FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
  rw [(first_width hx).1,(first_width hx).2]
  ring

theorem positiveEndpoint_negative (r : Bool) {x : ℝ}
    (hx : x∈Icc (-(203/250:ℝ)) 0) :
    positiveEndpoint r x=negativeFirst r (-x) := by
  dsimp [positiveEndpoint,negativeFirst,FrameCoreMidScalars.trigAffine,D,C,
    FrameCoreMidScalars.ap,FrameCoreMidScalars.cp]
  rw [(FrameCoreHighGeometry.negative_width hx).1,(FrameCoreHighGeometry.negative_width hx).2,
    Real.sin_neg,Real.cos_neg]
  ring

theorem positiveEndpoint_lower (r : Bool) {x : ℝ}
    (hx : x∈Icc (-(203/250:ℝ)) (7/5)) : (9/10:ℝ)<positiveEndpoint r x := by
  by_cases hn : x≤0
  · rw [positiveEndpoint_negative r ⟨hx.1,hn⟩]
    exact negativeFirst_lower r ⟨by linarith,by linarith [hx.1]⟩
  · rw [positiveEndpoint_first r
      ⟨(lt_of_not_ge hn).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩]
    exact positiveFirst_lower r ⟨(lt_of_not_ge hn).le,hx.2⟩

theorem positive_target_small_angle (i : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(203/250:ℝ)) (7/5))
    (hm : 0≤coreHighSecondary i true a b B x) :
    (8833/10000:ℝ)<coreHighCost i true a b B x := by
  have hmin := positive_target_linear hx hB
  have hs := support i true hc hB hm
  have he0 : positiveEndpoint false x=common true x+linear (P true x) (Q true x) b2 := by
    dsimp [positiveEndpoint,common,linear,P,Q,sign,endpointA,endpointB,endpointH,H2]
    rw [A_b2]
    ring
  have he1 : positiveEndpoint true x=common true x+linear (P true x) (Q true x) c0 := by
    dsimp [positiveEndpoint,common,linear,P,Q,sign,endpointA,endpointB,endpointH,k]
    rw [A_c0]
    ring
  have h0 := positiveEndpoint_lower false hx
  have h1 := positiveEndpoint_lower true hx
  rw [he0] at h0
  rw [he1] at h1
  have hh : (9/10:ℝ)-common true x<
      min (linear (P true x) (Q true x) b2) (linear (P true x) (Q true x) c0) :=
    lt_min (by linarith) (by linarith)
  linarith

/-- The secondary axis of a core source against a high target: for both signs and every frame
angle in `[-203/250, 5/2]`, a weak margin gives a cost above `8833/10000`. -/
theorem core_secondary (i j : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2))
    (hm : 0≤coreHighSecondary i j a b B x) :
    (8833/10000:ℝ)<coreHighCost i j a b B x := by
  cases j with
  | false =>
      by_cases hn : x≤0
      · exact negative_target_negative_angle i hc hB ⟨hx.1,hn⟩ hm
      · by_cases hl : (6/5:ℝ)≤x
        · exact negative_target_large_angle i hc hB ⟨hl,hx.2⟩ hm
        · have hs := fullCircle_support i false hc hB hm
          rw [circle_minus ⟨(lt_of_not_ge hn).le,
            by linarith [lt_of_not_ge hl,FrameLowPair.pi_lower]⟩] at hs
          exact (minus_lower ⟨(lt_of_not_ge hn).le,(lt_of_not_ge hl).le⟩).trans_le hs
  | true =>
      by_cases hl : x≤(7/5:ℝ)
      · exact positive_target_small_angle i hc hB ⟨hx.1,hl⟩ hm
      · have hs := fullCircle_support i true hc hB hm
        by_cases hq : x≤Real.pi/2
        · rw [circle_positive_first ⟨by linarith [lt_of_not_ge hl],hq⟩] at hs
          exact (positive_first_lower ⟨(lt_of_not_ge hl).le,hq⟩).trans_le hs
        · rw [circle_positive_second
            ⟨(lt_of_not_ge hq).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩] at hs
          exact (positive_second_lower ⟨(lt_of_not_ge hq).le,hx.2⟩).trans_le hs

end SquaresInCircles.Eight.FrameCoreHighCoreSecondary
end
end
end

section
/-!
## Every original high-source transverse witness against a core state

The actual weak margin excludes the negative source sign.  Each remaining
multiplier is proved nonnegative and is applied to that unchanged margin.
The negative-angle continuation keeps its exact cosine multiplier.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighHighSecondary
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (b2 g K)
open FrameCoreHighGeometry FrameCoreHighHighSecondaryScalars

theorem negative_core_nonnegative {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : x∈Icc 0 Real.pi)
    (hm : 0≤highCoreSecondary true false b a B x) :
    (8833/10000:ℝ)<highCoreCost true false b a B x := by
  have hsource := FrameHighArc.loss_antitone (lambda := g)
    (by norm_num [u,v,g]) hb ⟨FrameMidArc.b2_mem.2,le_rfl⟩ hb.2
  simp only [H_c0] at hsource
  have hscaled := mul_nonneg (show 0≤g by norm_num [g]) hm
  have hsin := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x) (show 0≤g by norm_num [g])
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x) (show 0≤g by norm_num [g])
  have htarget := positive_support (r := g*Real.sin x) (z := g*Real.cos x) hc
    (by dsimp [K,g] at *; linarith) (by linarith)
  have hh : negativeCore x≤highCoreCost true false b a B x := by
    dsimp [negativeCore,highCoreCost,highCoreSecondary,sign] at *
    linarith
  exact (lt_trans (by norm_num) (negativeCore_lower hx)).trans_le hh

theorem negative_core_negative {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : x∈Icc (-(203/250:ℝ)) 0)
    (hm : 0≤highCoreSecondary true false b a B x) :
    (8833/10000:ℝ)<highCoreCost true false b a B x := by
  have ht := negative_trig hx
  have hc0 : 0<Real.cos x := by linarith [ht.2]
  obtain ⟨lambda,hl⟩ : ∃ l : ℝ, l=g/Real.cos x := ⟨_,rfl⟩
  have hlam0 : 0≤lambda := hl ▸ div_nonneg (by norm_num [g]) hc0.le
  have hlamL : g≤lambda := hl ▸ (le_div_iff₀ hc0).2
    (mul_le_of_le_one_right (by norm_num [g] : 0≤g) (Real.cos_le_one x))
  have hlamU : lambda<2 := hl ▸ (div_lt_iff₀ hc0).2 (by dsimp [g]; linarith [ht.2])
  have hsource := FrameHighArc.loss_antitone (lambda := lambda)
    (by norm_num [u,v,g] at hlamL ⊢; linarith) hb ⟨FrameMidArc.b2_mem.2,le_rfl⟩ hb.2
  simp only [H_c0] at hsource
  have hscaled := mul_nonneg hlam0 hm
  have hsin := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin x) hlam0
  have hcan : lambda*Real.cos x=g := by rw [hl]; exact div_mul_cancel₀ _ hc0.ne'
  have htarget := positive_support (r := lambda*Real.sin x)
    (z := lambda*Real.cos x) hc (by dsimp [K]; linarith) (by rw [hcan])
  have hsupport : x-(9/50)*periodicFrameCost x+lambda*pairWidth x+
      Real.pi/4-lambda*c0-lambda*(7/12)*Real.sin x≤highCoreCost true false b a B x := by
    dsimp [highCoreCost,highCoreSecondary,sign] at *
    linarith
  have he : x-(9/50)*periodicFrameCost x+lambda*pairWidth x+
      Real.pi/4-lambda*c0-lambda*(7/12)*Real.sin x=negativeAngle (-x) := by
    rw [hl]
    dsimp only [negativeAngle]
    rw [(FrameCoreHighGeometry.negative_width hx).1,
      (FrameCoreHighGeometry.negative_width hx).2,Real.sin_neg,Real.cos_neg]
    field_simp
    ring
  rw [he] at hsupport
  have hscalar := negativeAngle_lower
    (show -x∈Icc (0:ℝ) (203/250) from ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  exact (lt_trans (by norm_num) hscalar).trans_le hsupport

theorem positive_core {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2))
    (hm : 0≤highCoreSecondary true true b a B x) :
    (8833/10000:ℝ)<highCoreCost true true b a B x := by
  have hcut := high_secondary_positive_angle hb hc hx.1 hm
  have hsource := FrameHighArc.loss_antitone (lambda := (1:ℝ))
    (by norm_num [u,v]) hb ⟨FrameMidArc.b2_mem.2,le_rfl⟩ hb.2
  simp only [H_c0] at hsource
  have htarget := negative_support (x := x) hc
  have hh : positiveCore x≤highCoreCost true true b a B x := by
    dsimp [positiveCore,highCoreCost,highCoreSecondary,sign] at *
    linarith
  have hscalar := positiveCore_lower
    (show x∈Icc (9/20:ℝ) Real.pi from
      ⟨hcut.le,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  exact (lt_trans (by norm_num) hscalar).trans_le hh

theorem high_secondary (i j : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B)
    (hx : x∈Icc (-(203/250:ℝ)) (5/2))
    (hm : 0≤highCoreSecondary i j b a B x) :
    (8833/10000:ℝ)<highCoreCost i j b a B x := by
  have hi := high_secondary_source_positive i j hb hc hm
  subst i
  cases j with
  | false =>
      by_cases hn : x≤0
      · exact negative_core_negative hb hc ⟨hx.1,hn⟩ hm
      · exact negative_core_nonnegative hb hc
          ⟨(lt_of_not_ge hn).le,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm
  | true => exact positive_core hb hc hx hm

end SquaresInCircles.Eight.FrameCoreHighHighSecondary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighPair
open FramePair FrameCircleArc FrameHighArc FrameCoreArc
open FrameCoreHighGeometry

theorem pair_angle_lower (s t : FramePair.State) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) : -(203/250:ℝ)<x := by
  have hs := s.offset_range
  have ht := t.offset_range
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem positive_target_angle (s t : FramePair.State) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (ht : t.positive=true) : -(13/500:ℝ)<x := by
  have hs := s.offset_range.2
  have hratio : 0≤t.b/t.a := div_nonneg t.b_nonneg t.a_pos.le
  have hangle : 0≤Real.arctan (t.b/t.a) := by
    simpa using Real.arctan_mono hratio
  have htarget : 0≤t.offset := by simpa [State.offset,ht,sign] using hangle
  dsimp [State.gap] at hgap
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem state_core_high_cost (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.high) (x : ℝ) :
    s.cost t x=coreHighCost s.positive t.positive s.a s.b t.b x := by
  rw [State.cost,state_core_label s hs,state_high_label t ht]
  rfl

theorem state_high_core_cost (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch.type=0) (x : ℝ) :
    s.cost t x=highCoreCost s.positive t.positive s.b t.a t.b x := by
  rw [State.cost,state_high_label s hs,state_core_label t ht]
  rfl

theorem state_core_high_secondary (s t : FramePair.State)
    (ht : t.branch=.high) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤coreHighSecondary s.positive t.positive s.a s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_high_chart t ht).1]
  rfl

theorem state_core_high_primary (s t : FramePair.State)
    (ht : t.branch=.high) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤coreHighPrimary t.positive s.a t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_high_chart t ht).1]
  rfl

theorem state_high_core_secondary (s t : FramePair.State) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤highCoreSecondary s.positive t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero]
  rfl

theorem state_high_core_primary (s t : FramePair.State)
    (hs : s.branch=.high) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤highCorePrimary t.positive s.b t.a t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_high_chart s hs).1]
  rfl

theorem source_core_secondary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hc := state_core_chart s hs
  have hH := (state_high_chart t ht).2
  rw [state_core_high_cost s t hs ht]
  by_cases hlarge : (5/2:ℝ)≤x
  · exact core_high_tail s.positive t.positive hc hH hlarge
  · exact FrameCoreHighCoreSecondary.core_secondary s.positive t.positive hc hH
      ⟨(pair_angle_lower s t hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_high_secondary s t ht x).mp hm)

theorem source_core_primary (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.high) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hc := state_core_chart s hs
  have hH := (state_high_chart t ht).2
  rw [state_core_high_cost s t hs ht]
  by_cases hlarge : (5/2:ℝ)≤x
  · exact core_high_tail s.positive t.positive hc hH hlarge
  · exact FrameCoreHighCorePrimary.core_primary s.positive t.positive hc hH
      ⟨(pair_angle_lower s t hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_core_high_primary s t ht x).mp hm)

theorem source_high_secondary (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hH := (state_high_chart s hs).2
  have hc := state_core_chart t ht
  rw [state_high_core_cost s t hs ht]
  by_cases hlarge : (5/2:ℝ)≤x
  · exact high_core_tail s.positive t.positive hH hc hlarge
  · exact FrameCoreHighHighSecondary.high_secondary s.positive t.positive hH hc
      ⟨(pair_angle_lower s t hgap).le,(lt_of_not_ge hlarge).le⟩
      ((state_high_core_secondary s t x).mp hm)

theorem source_high_primary (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch.type=0) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (8833/10000:ℝ)<s.cost t x := by
  have hH := (state_high_chart s hs).2
  have hc := state_core_chart t ht
  rw [state_high_core_cost s t hs ht]
  by_cases hlarge : (5/2:ℝ)≤x
  · exact high_core_tail s.positive t.positive hH hc hlarge
  · exact FrameCoreHighHighPrimary.high_primary s.positive t.positive hH hc
      ⟨(pair_angle_lower s t hgap).le,(lt_of_not_ge hlarge).le⟩
      (fun hj => (positive_target_angle s t hgap hj).le)
      ((state_high_core_primary s t hs x).mp hm)

/-- Every original weak axis in the core-to-high orientation. -/
theorem core_high_pair (s t : FramePair.State)
    (hs : s.branch.type=0) (ht : t.branch=.high) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(8833/10000:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_core_secondary s t hs ht hgap hm
  · have hh := source_high_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_high_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_core_primary s t hs ht hgap hm

/-- Every original weak axis in the high-to-core orientation. -/
theorem high_core_pair (s t : FramePair.State)
    (hs : s.branch=.high) (ht : t.branch.type=0) (j : Fin 4) {x : ℝ}
    (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(8833/10000:ℝ) := by
    rw [hs,ht]
    norm_num [Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_high_secondary s t hs ht hgap hm
  · have hh := source_core_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_core_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_high_primary s t hs ht hgap hm

theorem core_high_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : (branchOf C i).type=0) (hj : branchOf C (next i)=.high)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact core_high_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

theorem high_core_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.high) (hj : (branchOf C (next i)).type=0)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact high_core_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameCoreHighPair
end
end
end
