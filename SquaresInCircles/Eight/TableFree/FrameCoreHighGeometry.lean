module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighPrimaryCurvature
public import SquaresInCircles.Eight.TableFree.FrameCoreLowGeometry

/-!
# Original core/high geometry and feasible-angle cuts

The four signed source margins are kept in their original coordinates.
All coarse cuts below follow directly from those weak margins and the
exact state arcs; no concentrated frame interval is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighGeometry
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (a2 b2 g K)
open FrameCoreMidGeometry (signed_le negative_signed_sin_le)

def coreHighCost (i k : Bool) (a b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*coreLabel a b-sign k*H B
def highCoreCost (i k : Bool) (b a B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*H b-sign k*coreLabel a B
def coreHighSecondary (i k : Bool) (a b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def coreHighPrimary (k : Bool) (a B x : ℝ) : ℝ :=
  a-A B*Real.cos x-sign k*B*Real.sin x-pairWidth x
def highCoreSecondary (i k : Bool) (b a B x : ℝ) : ℝ :=
  sign i*b+a*Real.sin x-sign k*B*Real.cos x-pairWidth x
def highCorePrimary (k : Bool) (b a B x : ℝ) : ℝ :=
  A b-a*Real.cos x-sign k*B*Real.sin x-pairWidth x

theorem negative_trig {x : ℝ} (hx : x∈Icc (-(203/250:ℝ)) 0) :
    Real.sin x≤0 ∧ (86/125:ℝ)<Real.cos x := by
  have hz : -x∈Icc 0 (203/250:ℝ) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,FrameLowPair.pi_lower])
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hz.1
    (by linarith [FrameLowPair.pi_lower] : (203/250:ℝ)≤Real.pi) hz.2
  have hc0 := cos_lower_six (show (0:ℝ)≤203/250 by norm_num)
  norm_num at hc0
  simp only [Real.sin_neg,Real.cos_neg] at hs hc
  exact ⟨by linarith,by linarith⟩

theorem negative_width {x : ℝ} (hx : x∈Icc (-(203/250:ℝ)) 0) :
    pairWidth x=(1-Real.sin x+Real.cos x)/2 ∧
      periodicFrameCost x=(-Real.sin x+Real.cos x-1)/2 := by
  have ht := negative_trig hx
  have hs : |Real.sin x|= -Real.sin x := abs_of_nonpos ht.1
  have hc : |Real.cos x|=Real.cos x := abs_of_nonneg (by linarith [ht.2])
  constructor <;> simp only [pairWidth,periodicFrameCost,hs,hc] <;> ring

theorem high_projection_lt (i : Bool) {b : ℝ} (hb : b∈Icc b2 c0) (x : ℝ) :
    A b*Real.sin x-sign i*b*Real.cos x<(4/3:ℝ) := by
  have hh := (high_norm_sq hb).2
  cases i
  · have h := projection_lt (b := b) (by norm_num : (0:ℝ)<4/3) hh x
    simp only [sign,Bool.false_eq_true,↓reduceIte]
    linarith
  · have he : (A b)^2+(-b)^2<(4/3:ℝ)^2 := by nlinarith
    have h := projection_lt (b := -b) (by norm_num : (0:ℝ)<4/3) he x
    simp only [sign,↓reduceIte]
    linarith

theorem core_high_tail (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : (5/2:ℝ)≤x) :
    (8833/10000:ℝ)<coreHighCost i k a b B x := by
  have hs := (FrameCoreArc.signed_label_bounds i hc).1
  have ht := (FrameHighArc.signed_label_bounds k hB).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [coreHighCost]
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem high_core_tail (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : (5/2:ℝ)≤x) :
    (8833/10000:ℝ)<highCoreCost i k b a B x := by
  have hs := (FrameHighArc.signed_label_bounds i hb).1
  have ht := (FrameCoreArc.signed_label_bounds k hc).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [highCoreCost]
  linarith [Arithmetic.pi_hand_enclosure.2]

theorem core_secondary_source_floor (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0)
    (hm : 0≤coreHighSecondary i k a b B x) :
    0≤ sign i*(coreLabel a b-g*b) := by
  cases i with
  | true => simpa [sign] using label_residual hc
  | false =>
      have hproj := high_projection_lt k hB x
      have hw := width_one_le x
      have hsf : sign false= -1 := by simp [sign]
      have hb : b<1/2 := by
        dsimp only [coreHighSecondary] at hm
        rw [hsf] at hm
        linarith
      rw [(label_side hc hb).2]
      simp

theorem high_secondary_source_positive (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B)
    (hm : 0≤highCoreSecondary i k b a B x) : i=true := by
  cases i with
  | true => rfl
  | false =>
      exfalso
      have hp := core_projection_lt k hc x
      have hw := width_one_le x
      have hb0 := (high_bounds hb).1
      have hsf : sign false= -1 := by simp [sign]
      dsimp only [highCoreSecondary] at hm
      rw [hsf] at hm
      linarith

theorem core_primary_angle (k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc b2 c0) (hx : -(203/250:ℝ)≤x)
    (hm : 0≤coreHighPrimary k a B x) : (6/5:ℝ)<x := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hB
  by_contra! hsmall
  have habs : |x|≤6/5 := abs_le.mpr ⟨by linarith,hsmall⟩
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
    (by linarith [FrameLowPair.pi_lower] : (6/5:ℝ)≤Real.pi) habs
  rw [Real.cos_abs] at hcos
  have hc0 := FrameCoreMidScalars.trig_six_fifths.2.2.1
  have hcpos : 0≤Real.cos x := by linarith
  have hsg := negative_signed_sin_le k (x := x) (by linarith [hhigh.1] : 0≤B)
  have hA := mul_le_mul_of_nonneg_right
    (show (1399/1000:ℝ)≤A B+1/2 by linarith [hhigh.2.2.1]) hcpos
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤2/5 by linarith [hhigh.2.1]) (abs_nonneg (Real.sin x))
  dsimp only [coreHighPrimary,pairWidth] at hm
  rw [abs_of_nonneg hcpos] at hm
  linarith [Real.abs_sin_le_one x,hcore.2.1]

theorem high_secondary_positive_angle {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : -(203/250:ℝ)≤x)
    (hm : 0≤highCoreSecondary true true b a B x) : (9/20:ℝ)<x := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hb
  have hst : sign true=1 := by simp [sign]
  dsimp only [highCoreSecondary] at hm
  rw [hst] at hm
  by_contra! hsmall
  by_cases hn : x≤0
  · have ht := negative_trig ⟨hx,hn⟩
    have hA := mul_nonpos_of_nonneg_of_nonpos
      (by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1] : 0≤a) ht.1
    have hB := mul_nonneg hcore.2.2.1 (by linarith [ht.2] : 0≤Real.cos x)
    have hw := width_one_le x
    linarith [hhigh.2.1]
  · have hxq : x∈Icc 0 (Real.pi/2) :=
      ⟨(lt_of_not_ge hn).le,by linarith [hsmall,FrameLowPair.pi_lower]⟩
    have ht := FrameLowPair.quadrant hxq
    have hs := Real.sin_le hxq.1
    have hcL := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hxq.1 hsmall 2
    have hA := mul_le_mul_of_nonneg_right
      (show a-1/2≤1/12 by linarith [hcore.2.1]) ht.1
    have hB := mul_nonneg hcore.2.2.1 ht.2.2.1
    rw [(first_width hxq).1] at hm
    linarith [hhigh.2.1]

theorem high_primary_angle (k : Bool) {b a B x : ℝ}
    (hb : b∈Icc b2 c0) (hc : CoreState a B) (hx : -(203/250:ℝ)≤x)
    (hpositive : k=true → -(13/500:ℝ)≤x)
    (hm : 0≤highCorePrimary k b a B x) : (3/4:ℝ)<x := by
  have hcore := core_bounds hc
  have hhigh := high_bounds hb
  have ha : (5589/10000:ℝ)≤a := by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]
  have hxlower : -(3/4:ℝ)≤x := by
    cases k with
    | true => linarith [hpositive rfl]
    | false =>
        by_contra! hnegative
        have ht := negative_trig ⟨hx,by linarith⟩
        have hA := mul_le_mul_of_nonneg_right ha
          (by linarith [ht.2] : 0≤Real.cos x)
        have hB := mul_nonpos_of_nonneg_of_nonpos hcore.2.2.1 ht.1
        have hw := width_one_le x
        have hsf : sign false= -1 := by simp [sign]
        dsimp only [highCorePrimary] at hm
        rw [hsf] at hm
        linarith [hhigh.2.2.2,ht.2]
  by_contra! hsmall
  have habs : |x|≤3/4 := abs_le.mpr ⟨hxlower,hsmall⟩
  have hsU := (Real.abs_sin_le_abs (x := x)).trans habs
  have hx2 : x^2≤(3/4:ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) habs 2
    rwa [sq_abs] at h
  have hcL : (23/32:ℝ)≤Real.cos x := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hsg := negative_signed_sin_le k (x := x) hcore.2.2.1
  have hA := mul_le_mul_of_nonneg_right
    (show (529/500:ℝ)≤a+1/2 by linarith)
    (by linarith : 0≤Real.cos x)
  have hB' := mul_le_mul_of_nonneg_right
    (show B-1/2≤3/50 by linarith [hcore.2.2.2,CoreAngleEndpoint.diagonal_bounds.2])
    (abs_nonneg (Real.sin x))
  dsimp only [highCorePrimary,pairWidth] at hm
  rw [abs_of_nonneg (by linarith : 0≤Real.cos x)] at hm
  linarith [hhigh.2.2.2]

end SquaresInCircles.Eight.TableFree.FrameCoreHighGeometry
