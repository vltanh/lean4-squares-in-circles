module

public import SquaresInCircles.Eight.TableFree.FrameHighLowAxialScalars

/-!
# Exact high/low secondary contact surface

The target coordinate is explicit, including the short analytic
extension used by the diagonal boundary.  Partial derivatives and all
circle-domain bounds are proved on the complete target rectangle.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowContactSurface
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus

def lowDomain : Set ℝ := Icc (-(3/1000:ℝ)) b1
def height (x B : ℝ) : ℝ :=
  (1+Real.sin x+Real.cos x)/2-A B*Real.sin x-B*Real.cos x
def D (x B : ℝ) : ℝ := Real.cos x-slope B*Real.sin x
def F (x B : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x+Real.cos x-1)+H (height x B)+L B
def FB (x B : ℝ) : ℝ := Ld B-Hd (height x B)*D x B
def FBB (x B : ℝ) : ℝ :=
  FrameHighArc.u*slopeD (height x B)*(D x B)^2+
    Hd (height x B)*slopeD B*Real.sin x-FrameLowArc.u*slopeD B

theorem low_extended {B : ℝ} (hB : B∈lowDomain) : B∈extendedDomain :=
  ⟨by linarith [hB.1],by linarith [hB.2,b1_bounds.2]⟩

theorem low_bounds {B : ℝ} (hB : B∈lowDomain) :
    0<slope B ∧ slope B<23/50 ∧ 0<slopeD B ∧ slopeD B<27/40 := by
  have he := low_extended hB
  have hp := extended_shift_pos he
  have hr0 : 0<slope B := div_pos (by linarith [hB.1]) hp
  have hb1 : b1∈Icc 0 b1 := ⟨b1_mem.1,le_rfl⟩
  have hcmp := extended_slope_monotone he (FrameLowHighArc.low_extended hb1) hB.2
  have hA := extended_A_antitone he (FrameLowHighArc.low_extended hb1) hB.2
  rw [A_b1] at hA
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤899/500)
    (show (899/500:ℝ)≤A B+1/2 by linarith [a1_precise.1]) 3
  refine ⟨hr0,hcmp.trans_lt (slope_bounds hb1).2,slopeD_positive he,?_⟩
  dsimp [slopeD]
  apply (div_lt_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem D_bounds {x B : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain) (hB : B∈lowDomain) :
    (17/25:ℝ)<D x B ∧ D x B≤1 := by
  have ht := FrameLowPair.quadrant (FrameHighLowAxialGeometry.quadrant hx)
  have hr := low_bounds hB
  have hs := Real.sin_le_self hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hm := mul_le_mul hr.2.1.le (show Real.sin x≤23/50 by linarith [hx.2]) ht.1
    (by norm_num : (0:ℝ)≤23/50)
  have hpos := mul_nonneg hr.1.le ht.1
  dsimp [D]
  constructor <;> nlinarith [ht.2.2.2]

theorem D_short_lower {x B : ℝ} (hx : x∈Icc (0:ℝ) (1/5)) (hB : B∈lowDomain) :
    (111/125:ℝ)≤D x B := by
  have ht := FrameLowPair.quadrant (show x∈Icc 0 (Real.pi/2) from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hr := low_bounds hB
  have hs := Real.sin_le_self hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hm := mul_le_mul hr.2.1.le (show Real.sin x≤1/5 by linarith [hx.2]) ht.1
    (by norm_num : (0:ℝ)≤23/50)
  dsimp [D]
  nlinarith

theorem height_deriv {B : ℝ} (hB : B∈lowDomain) (x : ℝ) :
    HasDerivAt (height x) (-D x B) B := by
  convert (((extended_A_deriv (low_extended hB)).const_mul (-Real.sin x)).const_add
    ((1+Real.sin x+Real.cos x)/2)).sub ((hasDerivAt_id B).const_mul (Real.cos x)) using 1
  all_goals dsimp [height,D,Ad,slope]; ring

theorem D_deriv {B : ℝ} (hB : B∈lowDomain) (x : ℝ) :
    HasDerivAt (D x) (-slopeD B*Real.sin x) B := by
  convert ((slope_deriv (low_extended hB)).const_mul (-Real.sin x)).const_add (Real.cos x)
    using 1 <;> dsimp [D] <;> ring

theorem height_antitone {x : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain) :
    AntitoneOn (height x) lowDomain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun B hB => (height_deriv hB x).continuousAt.continuousWithinAt
  · exact fun B hB => height_deriv (Ioo_subset_Icc_self hB) x
  · intro B hB
    linarith [(D_bounds hx (Ioo_subset_Icc_self hB)).1]

theorem height_between {x l B u : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain)
    (hl : l∈lowDomain) (hu : u∈lowDomain) (hB : B∈Icc l u) :
    height x u≤height x B ∧ height x B≤height x l := by
  have hb : B∈lowDomain := ⟨hl.1.trans hB.1,hB.2.trans hu.2⟩
  exact ⟨height_antitone hx hb hu hB.2,height_antitone hx hl hb hB.1⟩

@[simp] theorem height_zero (x : ℝ) : height x 0=FrameHighLowAxialGeometry.Z x := by
  rw [height,A_zero]
  dsimp [FrameHighLowAxialGeometry.Z]
  ring

theorem height_diagonal {x : ℝ} (hx : x∈FrameHighLowDiagonalCurve.domain) :
    height x (FrameHighLowDiagonalCurve.z x)=c0 := by
  have hh := FrameHighLowDiagonalCurve.contact hx
  rw [(first_width (FrameHighLowDiagonalCurve.quadrant hx)).1] at hh
  dsimp [height]
  linarith

theorem F_deriv {x B : ℝ} (hB : B∈lowDomain) (hz : height x B∈Icc b2 c0) :
    HasDerivAt (F x) (FB x B) B := by
  convert (((extended_H_deriv (high_extended hz)).comp B (height_deriv hB x)).const_add
    (x-(9/100)*(Real.sin x+Real.cos x-1))).add (extended_L_deriv (low_extended hB)) using 1
  all_goals dsimp [F,FB]; ring

theorem FB_deriv {x B : ℝ} (hB : B∈lowDomain) (hz : height x B∈Icc b2 c0) :
    HasDerivAt (FB x) (FBB x B) B := by
  convert (extended_Ld_deriv (low_extended hB)).sub
    (((extended_Hd_deriv (high_extended hz)).comp B (height_deriv hB x)).mul (D_deriv hB x)) using 1
  all_goals dsimp [FB,FBB]; ring

theorem curvature_positive {x B : ℝ} (hx : x∈Icc (0:ℝ) (1/5))
    (hB : B∈lowDomain) (hz : height x B∈Icc b2 c0) : (2/25:ℝ)<FBB x B := by
  have ht := FrameLowPair.quadrant (show x∈Icc 0 (Real.pi/2) from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hD := D_short_lower hx hB
  have hD2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤111/125) hD 2
  have hH := high_Hdd_lower hz
  have hh := mul_le_mul hH.le hD2 (by norm_num : (0:ℝ)≤(111/125)^2)
    (by linarith : 0≤FrameHighArc.u*slopeD (height x B))
  have hr := low_bounds hB
  have hmiddle : 0≤Hd (height x B)*slopeD B*Real.sin x :=
    mul_nonneg (mul_nonneg (by linarith [high_Hd_lower hz]) hr.2.2.1.le) ht.1
  dsimp [FBB,FrameLowArc.u]
  nlinarith [hr.2.2.2]

theorem height_le_source {b B x : ℝ} (hx : x∈FrameHighLowAxialGeometry.domain)
    (hm : 0≤FrameLowHighGeometry.secondary true false b B x) : height x B≤b := by
  dsimp [FrameLowHighGeometry.secondary,FrameLowMidGeometry.secondary,sign] at hm
  rw [(first_width (FrameHighLowAxialGeometry.quadrant hx)).1] at hm
  dsimp [height]
  linarith

end SquaresInCircles.Eight.TableFree.FrameHighLowContactSurface
