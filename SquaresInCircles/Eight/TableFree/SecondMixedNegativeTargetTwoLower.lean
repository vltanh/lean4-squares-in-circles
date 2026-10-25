module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeTargetTwoSide
public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeTargetTwoCorner
public import SquaresInCircles.Eight.TableFree.SecondMixedTransverseSupportWide
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreTwoData

/-!
# Both complete lower owners of the negative target row

A whole-interval transverse support handles angles through 1.5. At
later angles, small source coordinates have a direct bound; large
source coordinates convert the original secondary separator to the
already closed primary separator at exactly the same two points.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)
open MixedTransverseSupport

def support (φ : ℝ) : ℝ := lower (1909/2000) (853/1000) (e-1239/50000) φ

lemma support_left : (97/100:ℝ)<support lowerAngle := by
  have ht := MixedAffine.left_trig
  have hn := lower_sq_wide (g := (1909/2000:ℝ)) (p := (853/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num) lowerAngle
  have hp : 0<lowerN (1909/2000) (853/1000) lowerAngle := CircularNorm.norm_pos
    (lower_domain_wide (by norm_num) (by norm_num) (by norm_num) lowerAngle)
  have hN : lowerN (1909/2000) (853/1000) lowerAngle<(96/125:ℝ) := by nlinarith [ht.2.2.1]
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<96/125))
  have hL : lowerAngle=Real.pi/2-7/10 := rfl
  dsimp only [support,lower,e]
  linarith [ht.1,pi_hand_enclosure.1]

lemma support_right : (907/1000:ℝ)<support (3/2) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (3/2:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (3/2:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  have hn := lower_sq_wide (g := (1909/2000:ℝ)) (p := (853/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (3/2)
  have hp : 0<lowerN (1909/2000) (853/1000) (3/2) := CircularNorm.norm_pos
    (lower_domain_wide (by norm_num) (by norm_num) (by norm_num) (3/2))
  have hN : lowerN (1909/2000) (853/1000) (3/2)<(12343/10000:ℝ) := by nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<12343/10000))
  dsimp [support,lower,e]
  linarith

lemma support_lower {φ : ℝ} (hφ : φ∈Icc lowerAngle (3/2)) : γ<support φ := by
  have hc : ConcaveOn ℝ (Icc lowerAngle (3/2)) support :=
    concave_of_deriv2
      (fun x _ => lower_hasDerivAt_wide (by norm_num) (by norm_num) (by norm_num) (e-1239/50000) x)
      (fun x _ => lowerD_hasDerivAt_wide (by norm_num) (by norm_num) (by norm_num) x)
      (fun x hx => (lower_curvature_wide (by norm_num) (by norm_num) (by norm_num)
        (show Lower x from ⟨hx.1,by linarith [hx.2,pi_hand_enclosure.1]⟩)).le)
  exact concave_gt_of_endpoints hc hφ
    (by dsimp [γ]; linarith [support_left]) (by dsimp [γ]; linarith [support_right])

theorem lower_primary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) : γ<value b A B φ := by
  rcases ht with ⟨rfl,hB,hBu⟩ | ⟨hB,hBA,hcircle⟩
  · exact Side.original_primary hs ⟨hB,hBu⟩ hφ hsep
  · exact Corner.original_primary hs hB hBA hcircle hφ hsep

theorem lower_secondary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ+B) : γ<value b A B φ := by
  by_cases he : φ≤3/2
  · have hP := P_chord (NegativeTwo.source_mem hs)
    have hcore := core_affine ht
    have hc := outer_circle_lower (X := -(1909/2000)*Real.sin φ)
      (Y := (1909/2000)*Real.cos φ-853/1000) hs
    have hnorm : Real.sqrt ((-(1909/2000)*Real.sin φ)^2+
        ((1909/2000)*Real.cos φ-853/1000)^2)=lowerN (1909/2000) (853/1000) φ := by
      dsimp [lowerN,CircularNorm.norm,CircularNorm.energy]
      congr 1
      linear_combination (1909/2000:ℝ)^2*(Real.sin_sq_add_cos_sq φ)
    rw [hnorm] at hc
    have hh := support_lower ⟨hφ.1,he⟩
    dsimp [support,lower,value] at *
    nlinarith
  · by_cases hb : b≤7/10
    · have hP := MixedTwo.PositiveCore.P_seven_chord ⟨hs.1,hb⟩
      have hcore := core_minimum ht
      dsimp [value,e,γ] at *
      linarith
    · have htφ := lower_trig hφ
      have hEnd : Lower (3/2:ℝ) := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
        by linarith [pi_hand_enclosure.1]⟩
      have hsm := PositiveThree.lower_sin_monotone hEnd hφ (by linarith)
      have hsref := HighOrderTaylor.S15_le_sin (x := (3/2:ℝ)) (by norm_num)
      norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7] at hsref
      have hsin : (997/1000:ℝ)<Real.sin φ := by linarith
      have hA := (CoreAngleEndpoint.state_bounds ht).2.1
      have ha : 0≤a-1/2 := by linarith [(NegativeTwo.primary_mem hs).1,fine_outer_endpoint_bounds.2]
      have hac := mul_nonneg ha htφ.2.2.1
      have hbs := mul_le_mul (show (6/5:ℝ)≤b+1/2 by linarith) hsin.le
        (by norm_num : (0:ℝ)≤997/1000) (by linarith [hs.1] : 0≤b+1/2)
      have hreserve : 0≤(a-1/2)*Real.cos φ+(b+1/2)*Real.sin φ-A-1/2 := by nlinarith
      have hp := mul_nonneg htφ.2.2.1 hreserve
      have hpaid := mul_le_mul_of_nonneg_right hsep (by linarith [htφ.1] : 0≤Real.sin φ)
      have hid : a-A*Real.cos φ+B*Real.sin φ-(1+Real.sin φ+Real.cos φ)/2-
          Real.sin φ*(a*Real.sin φ-b*Real.cos φ+B-(1+Real.sin φ+Real.cos φ)/2)=
        Real.cos φ*((a-1/2)*Real.cos φ+(b+1/2)*Real.sin φ-A-1/2) := by
        linear_combination (-(a-1/2))*(Real.sin_sq_add_cos_sq φ)
      exact lower_primary hs ht hφ (by nlinarith)

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget
