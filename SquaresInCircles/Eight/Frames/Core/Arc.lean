module

public import SquaresInCircles.Eight.Words.Core.AngleEndpoint
public import SquaresInCircles.Eight.Frames.Mid.Arc

/-!
# Eight squares: the core curve in the frame pairs

On the core curve, its side `a = 7/12` and its rounded corner, the label is
`coreLabel a b = K (7/12 - a) + g b`. A core state has `diagonal ≤ a ≤ 7/12` and
`0 ≤ b ≤ diagonal` (`core_bounds`); its label lies in `[0, 393/500)` and equals `g b` on the side
(`label_bounds`, `label_side`, `signed_label_bounds`). The affine supports of the core curve
follow from its equation, the order `b ≤ a` and the diagonal endpoint (`diagonal_support`,
`positive_support`, `negative_support`). The states of the core type are core states
(`state_core_chart`, `state_core_label`), and in every direction the projections of core and
middle states are below `4/5` and `67/50` (`core_projection_lt`, `middle_projection_lt`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreArc
open FramePair FrameCircleArc FrameMidArc

abbrev CoreState := CorePairGeometry.CoreState
abbrev diagonal : ℝ := CoreAngleEndpoint.diagonal
def coreLabel (a b : ℝ) : ℝ := K*(7/12-a)+g*b

theorem core_bounds {a b : ℝ} (hc : CoreState a b) :
    diagonal≤a ∧ a≤7/12 ∧ 0≤b ∧ b≤diagonal := by
  have hh := CoreAngleEndpoint.state_bounds hc
  refine ⟨?_,hh.2.1,hh.2.2.1,hh.2.2.2.2⟩
  rcases hc with ⟨rfl,_,_⟩ | ⟨hb,hab,hcircle⟩
  · linarith [CoreAngleEndpoint.diagonal_bounds.2]
  · exact (CoreAngleEndpoint.corner_diagonal hb hab hcircle).2

theorem label_bounds {a b : ℝ} (hc : CoreState a b) :
    0≤coreLabel a b ∧ coreLabel a b<(393/500:ℝ) := by
  have hh := core_bounds hc
  have hlow := mul_nonneg (show 0≤K by norm_num [K]) (sub_nonneg.mpr hh.2.1)
  have hB := mul_nonneg (show 0≤g by norm_num [g]) hh.2.2.1
  have hA := mul_le_mul_of_nonneg_left hh.1 (show 0≤K by norm_num [K])
  have hBU := mul_le_mul_of_nonneg_left hh.2.2.2 (show 0≤g by norm_num [g])
  dsimp [coreLabel,K,g] at *
  constructor <;> nlinarith [CoreAngleEndpoint.diagonal_bounds.1]

theorem label_side {a b : ℝ} (hc : CoreState a b) (hb : b<1/2) :
    a=7/12 ∧ coreLabel a b=g*b := by
  rcases hc with ⟨rfl,_,_⟩ | ⟨hb',_,_⟩
  · constructor
    · rfl
    · dsimp [coreLabel]; ring
  · linarith

theorem label_residual {a b : ℝ} (hc : CoreState a b) : 0≤coreLabel a b-g*b := by
  have hh := (core_bounds hc).2.1
  have hm := mul_nonneg (show 0≤K by norm_num [K]) (sub_nonneg.mpr hh)
  dsimp [coreLabel]
  linarith

theorem diagonal_support {a b X Y : ℝ} (hc : CoreState a b)
    (hX : 0≤X) (hY : Y≤0) : (X+Y)*diagonal≤X*a+Y*b := by
  have hh := core_bounds hc
  have hA := mul_le_mul_of_nonneg_left hh.1 hX
  have hB := mul_le_mul_of_nonpos_left hh.2.2.2 hY
  nlinarith

theorem positive_support {a b r z : ℝ} (hc : CoreState a b)
    (hr : 0≤K+r) (hz : z≤g) :
    -r*(7/12)≤coreLabel a b-r*a-z*b := by
  have hh := core_bounds hc
  have hA := mul_nonneg hr (sub_nonneg.mpr hh.2.1)
  have hB := mul_nonneg (sub_nonneg.mpr hz) hh.2.2.1
  dsimp [coreLabel]
  nlinarith

theorem negative_support {a b x : ℝ} (hc : CoreState a b) :
    -coreLabel diagonal diagonal+diagonal*(Real.cos x-Real.sin x)≤
      -coreLabel a b-a*Real.sin x+b*Real.cos x := by
  have hX : 0≤K-Real.sin x := by dsimp [K]; linarith [Real.sin_le_one x]
  have hY : Real.cos x-g≤0 := by dsimp [g]; linarith [Real.cos_le_one x]
  have hh := diagonal_support hc hX hY
  dsimp [coreLabel] at *
  nlinarith

theorem signed_label_bounds (i : Bool) {a b : ℝ} (hc : CoreState a b) :
    -(393/500:ℝ)<sign i*coreLabel a b ∧ sign i*coreLabel a b<393/500 := by
  have hh := label_bounds hc
  cases i <;> norm_num [sign] <;> constructor <;> linarith

theorem state_core_chart (s : FramePair.State) (hs : s.branch.type=0) :
    CoreState s.a s.b := by
  have he := s.a_eq
  have hb := s.b_mem
  cases hbr : s.branch with
  | coreSide =>
      left
      simpa [hbr,radialA,Branch.lower,Branch.upper] using And.intro he hb
  | coreCorner =>
      right
      have hb0 : 1/2 ≤ s.b := by simpa [hbr,Branch.lower] using hb.1
      have hbU : s.b≤14/25 := by simpa [hbr,Branch.upper] using hb.2
      have hsq := pow_le_pow_left₀ (show 0 ≤ s.b-1/2 by linarith)
        (show s.b-1/2≤3/50 by linarith) 2
      have hr : 0≤(1/12:ℝ)^2-(s.b-1/2)^2 := by nlinarith
      have hsqrt := Real.sq_sqrt hr
      simp only [hbr,radialA] at he
      exact ⟨hb0,s.canonical,by rw [he,add_sub_cancel_left,hsqrt]; ring⟩
  | low | middle | high => simp [hbr,Branch.type] at hs

theorem state_core_label (s : FramePair.State) (hs : s.branch.type=0) :
    s.signedLabel=sign s.positive*coreLabel s.a s.b := by
  cases hbr : s.branch <;> simp [hbr,Branch.type] at hs
  all_goals simp [State.signedLabel,hbr,label,coreLabel,K,g]

theorem width_one_le (x : ℝ) : 1≤pairWidth x := by
  have hh := one_le_abs_cos_add_abs_sin x
  dsimp [pairWidth]
  linarith

theorem projection_lt {a b r : ℝ} (hr : 0<r) (hc : a^2+b^2<r^2) (x : ℝ) :
    a*Real.sin x+b*Real.cos x<r := by
  have hid : (a*Real.sin x+b*Real.cos x)^2+
      (a*Real.cos x-b*Real.sin x)^2=a^2+b^2 := by
    linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq x)
  by_contra! hbad
  have hh := pow_le_pow_left₀ hr.le hbad 2
  nlinarith [sq_nonneg (a*Real.cos x-b*Real.sin x)]

theorem core_projection_lt (i : Bool) {a b : ℝ} (hc : CoreState a b) (x : ℝ) :
    a*Real.sin x-sign i*b*Real.cos x<(4/5:ℝ) := by
  have hh := CorePairGeometry.core_radius_sq hc
  cases i
  · have hp := projection_lt (b := b) (by norm_num : (0:ℝ)<4/5)
      (by nlinarith : a^2+b^2<(4/5:ℝ)^2) x
    simp only [sign]
    norm_num
    linarith
  · have he : a^2+(-b)^2<(4/5:ℝ)^2 := by nlinarith
    have hp := projection_lt (b := -b) (by norm_num : (0:ℝ)<4/5) he x
    simp only [sign]
    norm_num
    linarith

theorem middle_projection_lt (i : Bool) {b : ℝ} (hb : b∈Icc FrameLowArc.b1 b2) (x : ℝ) :
    A b*Real.sin x-sign i*b*Real.cos x<(67/50:ℝ) := by
  have hh := middle_norm_sq hb
  cases i
  · have hp := projection_lt (b := b) (by norm_num : (0:ℝ)<67/50) hh x
    simp only [sign]
    norm_num
    linarith
  · have he : (A b)^2+(-b)^2<(67/50:ℝ)^2 := by nlinarith
    have hp := projection_lt (b := -b) (by norm_num : (0:ℝ)<67/50) he x
    simp only [sign]
    norm_num
    linarith

end SquaresInCircles.Eight.FrameCoreArc
