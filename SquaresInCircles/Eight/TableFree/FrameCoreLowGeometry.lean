module

public import SquaresInCircles.Eight.TableFree.FrameCoreLowCancellation
public import SquaresInCircles.Eight.TableFree.FrameCoreMidGeometry

/-!
# Original core/low geometry and actual feasible-angle cuts

All cuts are derived from a weak physical margin on the original points.
The entire low arc and rounded core are retained, with both tangent signs.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreLowGeometry
open FramePair FrameCircleArc FrameLowArc FrameCoreArc FramePairCalculus
open FrameMidArc (g K)
open FrameCoreMidGeometry (signed_le negative_signed_sin_le nonpositive_signs)

def coreLowCost (i k : Bool) (a b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*coreLabel a b-sign k*L B
def lowCoreCost (i k : Bool) (b a B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*L b-sign k*coreLabel a B
def coreLowSecondary (i k : Bool) (a b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def coreLowPrimary (k : Bool) (a B x : ℝ) : ℝ :=
  a-A B*Real.cos x-sign k*B*Real.sin x-pairWidth x
def lowCoreSecondary (i k : Bool) (b a B x : ℝ) : ℝ :=
  sign i*b+a*Real.sin x-sign k*B*Real.cos x-pairWidth x
def lowCorePrimary (k : Bool) (b a B x : ℝ) : ℝ :=
  A b-a*Real.cos x-sign k*B*Real.sin x-pairWidth x

theorem low_bounds {b : ℝ} (hb : b∈Icc 0 b1) :
    0≤b ∧ b<(13/40:ℝ) ∧ (12987/10000:ℝ)<A b ∧ A b<283/200 := by
  have ha := A_low_bounds hb
  exact ⟨hb.1,by linarith [hb.2,b1_bounds.2],
    by linarith [ha.1,a1_bounds.1],by linarith [ha.2,a0_bounds.2]⟩

theorem low_coordinate_sum {b : ℝ} (hb : b∈Icc 0 b1) : a0≤A b+b := by
  have hh := linear_endpoint_lower (p := (1:ℝ)) (q := (1:ℝ))
    (by norm_num) (by norm_num : (0:ℝ)≤0) b1_mem.2 hb
  have he : a0≤a1+b1 := by linarith [a0_bounds.2,a1_bounds.1,b1_bounds.1]
  simpa [linear,A_zero,A_b1,min_eq_left he] using hh

theorem low_label_linear {b : ℝ} (hb : b∈Icc 0 b1) :
    (v-u)*b≤L b ∧ L b≤v*b := by
  have hlo := mul_le_mul_of_nonneg_left (low_coordinate_sum hb)
    (show (0:ℝ)≤u by norm_num [u])
  have hhi := mul_le_mul_of_nonneg_left (A_low_bounds hb).2
    (show (0:ℝ)≤u by norm_num [u])
  dsimp [L]
  constructor <;> nlinarith

theorem low_norm_sq {b : ℝ} (hb : b∈Icc 0 b1) :
    (A b)^2+b^2<(283/200:ℝ)^2 := by
  have hc := A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hc0 := A_circle (show (0:ℝ)∈Icc 0 c0 from ⟨le_rfl,b1_mem.1.trans b1_mem.2⟩)
  rw [A_zero] at hc0
  have hsum := low_coordinate_sum hb
  have ha := a0_bounds
  have ha2 : a0^2<(283/200:ℝ)^2 := by nlinarith
  nlinarith

theorem low_projection_lt (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) (x : ℝ) :
    A b*Real.sin x-sign i*b*Real.cos x<(283/200:ℝ) := by
  have hh := low_norm_sq hb
  cases i
  · simpa [sign] using projection_lt (b := b) (by norm_num : (0:ℝ)<283/200) hh x
  · have he : (A b)^2+(-b)^2<(283/200:ℝ)^2 := by nlinarith
    simpa [sign] using projection_lt (b := -b) (by norm_num : (0:ℝ)<283/200) he x

theorem core_low_tail (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : (41/20:ℝ)≤x) :
    (91/100:ℝ)<coreLowCost i k a b B x := by
  have hs := (FrameCoreArc.signed_label_bounds i hc).1
  have ht := (FrameLowPair.signed_label_bounds k hB).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [coreLowCost]
  linarith [L1_bounds.2]

theorem low_core_tail (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hx : (41/20:ℝ)≤x) :
    (91/100:ℝ)<lowCoreCost i k b a B x := by
  have hs := (FrameLowPair.signed_label_bounds i hb).1
  have ht := (FrameCoreArc.signed_label_bounds k hc).2
  have hch := CorePairGeometry.charge_upper x
  dsimp [lowCoreCost]
  linarith [L1_bounds.2]

theorem low_secondary_false (i k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B)
    (hm : 0≤lowCoreSecondary i k b a B x) : False := by
  have hcore := core_bounds hc
  have hlow := low_bounds hb
  have hsb := signed_le i hb.1
  have ha0 : 0≤a := by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1]
  have hsin := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin x)) ha0
  have hA := mul_le_mul_of_nonneg_right hcore.2.1 (abs_nonneg (Real.sin x))
  have hB := mul_le_mul_of_nonneg_right
    (show B≤7/12 by linarith [hcore.2.2.2,CoreAngleEndpoint.diagonal_bounds.2])
    (abs_nonneg (Real.cos x))
  have hcos : -sign k*B*Real.cos x≤B*|Real.cos x| := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self (Real.cos x)) hcore.2.2.1
    have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (Real.cos x)) hcore.2.2.1
    cases k <;> norm_num [sign] <;> nlinarith
  have hsum := CorePairGeometry.charge_upper x
  dsimp [periodicFrameCost] at hsum
  dsimp [lowCoreSecondary,pairWidth] at hm
  nlinarith

theorem core_secondary_source_floor (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1)
    (hm : 0≤coreLowSecondary i k a b B x) :
    0≤sign i*(coreLabel a b-g*b) := by
  cases i with
  | true => simpa [sign] using label_residual hc
  | false =>
      have hproj := low_projection_lt k hB x
      have hw := width_one_le x
      have hb : b<1/2 := by dsimp [coreLowSecondary,sign] at hm; linarith
      rw [(label_side hc hb).2]
      simp

theorem core_secondary_angle (i k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : -(3/10:ℝ)≤x)
    (hm : 0≤coreLowSecondary i k a b B x) : 0<x := by
  have hcore := core_bounds hc
  have hlow := low_bounds hB
  have hsb := signed_le i hcore.2.2.1
  by_contra! hneg
  have ht := nonpositive_signs ⟨by linarith,hneg⟩
  have hA := mul_nonpos_of_nonneg_of_nonpos (by linarith [hlow.2.2.1] : 0≤A B) ht.1
  have hBcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hB.1
  have hcos : -sign k*B*Real.cos x≤B := by
    have hnonneg := mul_nonneg hB.1 ht.2
    cases k <;> norm_num [sign] <;> nlinarith
  have hw := width_one_le x
  dsimp [coreLowSecondary] at hm
  linarith [CoreAngleEndpoint.diagonal_bounds.2]

theorem core_primary_angle (k : Bool) {a b B x : ℝ}
    (hc : CoreState a b) (hB : B∈Icc 0 b1) (hx : -(3/10:ℝ)≤x)
    (hm : 0≤coreLowPrimary k a B x) : Real.pi/2<x := by
  have hcore := core_bounds hc
  have hlow := low_bounds hB
  by_contra! hsmall
  have hcos : 0≤Real.cos x := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [FrameLowPair.pi_lower],hsmall⟩
  have hA := mul_nonneg (by linarith [hlow.2.2.1] : 0≤A B) hcos
  have hsb := negative_signed_sin_le k hB.1
  have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) hB.1
  have hw := width_one_le x
  dsimp [coreLowPrimary] at hm
  nlinarith

theorem low_primary_angle (k : Bool) {b a B x : ℝ}
    (hb : b∈Icc 0 b1) (hc : CoreState a B) (hx : -(3/10:ℝ)≤x)
    (hm : 0≤lowCorePrimary k b a B x) : (3/10:ℝ)<x := by
  have hcore := core_bounds hc
  have hlow := low_bounds hb
  by_contra! hsmall
  have habs : |x|≤3/10 := abs_le.mpr ⟨hx,hsmall⟩
  have hsU := (Real.abs_sin_le_abs (x := x)).trans habs
  have hx2 : x^2≤(3/10:ℝ)^2 := by
    nlinarith [sq_abs x,pow_le_pow_left₀ (abs_nonneg x) habs 2]
  have hcL : (191/200:ℝ)≤Real.cos x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hsg := negative_signed_sin_le k hcore.2.2.1
  have hA := mul_le_mul_of_nonneg_right
    (show (529/500:ℝ)≤a+1/2 by linarith [hcore.1,CoreAngleEndpoint.diagonal_bounds.1])
    (by linarith : 0≤Real.cos x)
  have hB := mul_le_mul_of_nonneg_right
    (show B-1/2≤3/50 by linarith [hcore.2.2.2,CoreAngleEndpoint.diagonal_bounds.2])
    (abs_nonneg (Real.sin x))
  dsimp [lowCorePrimary,pairWidth] at hm
  rw [abs_of_nonneg (by linarith : 0≤Real.cos x)] at hm
  nlinarith

end SquaresInCircles.Eight.TableFree.FrameCoreLowGeometry
