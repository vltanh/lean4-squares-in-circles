module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighSecondaryEndpoints

/-!
# Every original core-source transverse witness against the high arc

The original weak separating margin supplies the nonnegative core
residual.  The target support is minimized on its actual high arc or
bounded by its full circle, according to the proved derivative signs.
Both original tangent signs and the complete angle interval are retained.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighCoreSecondary
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

/-- Complete original core-source secondary axis, with all weak ties. -/
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

end SquaresInCircles.Eight.TableFree.FrameCoreHighCoreSecondary
