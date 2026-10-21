module

public import SquaresInCircles.Eight.TableFree.SecondMixedEdgeTwoLabels
public import SquaresInCircles.Eight.TableFree.SecondMixedAffineScalars
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeLowerFourth

/-!
# Whole-angle affine scalars for the negative core role-two family

The primary costs share one harmonic scalar whose derivative loses
less than .02.  The secondary cost has a uniformly positive derivative.
Both are controlled on the entire lower quarter half from its left
endpoint.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

def value (b B φ : ℝ) : ℝ := φ-c-g*b+T B
def third (φ : ℝ) : ℝ :=
  φ+167/10000-c-g*(559/1000)+(609/1000)*
    (1/2+Real.cos φ/2-Real.sin φ/12+(559/1000)*Real.cos φ)
def thirdD (φ : ℝ) : ℝ :=
  1-(609/1000)*(1059/1000)*Real.sin φ-(609/12000)*Real.cos φ

lemma first_left : (997/1000:ℝ)<MixedAffine.first g lowerAngle ∧
    -(1/50:ℝ)<MixedAffine.firstD g lowerAngle := by
  have ht := MixedAffine.left_trig
  have hk := MixedAffine.κ_bounds
  have hs : MixedAffine.κ*Real.sin lowerAngle<(183/200)*(15297/20000) :=
    (mul_lt_mul_of_pos_right hk.2 (by linarith [ht.1] : 0<Real.sin lowerAngle)).trans
      (mul_lt_mul_of_pos_left ht.2.1 (by norm_num : (0:ℝ)<183/200))
  have hc : MixedAffine.κ*Real.cos lowerAngle<(183/200)*(32211/50000) :=
    (mul_lt_mul_of_pos_right hk.2 (by linarith [ht.2.2.1] : 0<Real.cos lowerAngle)).trans
      (mul_lt_mul_of_pos_left ht.2.2.2 (by norm_num : (0:ℝ)<183/200))
  dsimp [MixedAffine.first,MixedAffine.firstD,g,lowerAngle]
  constructor <;> nlinarith [ht.2.2.1,ht.2.1,pi_hand_enclosure.1]

lemma first_lower {φ : ℝ} (hφ : Lower φ) : (49/50:ℝ)<MixedAffine.first g φ := by
  have hleft : Lower lowerAngle := MixedAffine.left_mem
  have hder (x : ℝ) (hx : Lower x) : 0<MixedAffine.firstD g x+1/50 := by
    have hh := MixedAffine.firstD_monotone (show (0:ℝ)≤g by norm_num [g]) hleft hx hx.1
    linarith [first_left.2]
  have hm : MonotoneOn (fun x => MixedAffine.first g x+x/50) (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => ((MixedAffine.first_hasDerivAt g x).add ((hasDerivAt_id x).div_const 50)).continuousAt.continuousWithinAt)
      (fun x _ => (MixedAffine.first_hasDerivAt g x).add ((hasDerivAt_id x).div_const 50))
      (fun x hx => (hder x (Ioo_subset_Icc_self hx)).le)
  have hh := hm hleft hφ hφ.1
  have hgap : φ-lowerAngle≤7/10 := by dsimp [lowerAngle]; linarith [hφ.2]
  linarith [first_left.1]

lemma third_hasDerivAt (φ : ℝ) : HasDerivAt third (thirdD φ) φ := by
  convert ((((hasDerivAt_id φ).add_const (167/10000)).sub_const c).sub_const (g*(559/1000))).add
    (((((Real.hasDerivAt_cos φ).div_const 2).const_add (1/2)).sub
      ((Real.hasDerivAt_sin φ).div_const 12)).add
        ((Real.hasDerivAt_cos φ).const_mul (559/1000))).const_mul (609/1000))
    using 1 <;> dsimp [third,thirdD] <;> ring

lemma thirdD_positive (φ : ℝ) : 0<thirdD φ := by
  dsimp [thirdD]
  linarith [Real.sin_le_one φ,Real.cos_le_one φ]

lemma third_left : (49/50:ℝ)<third lowerAngle := by
  have ht := MixedAffine.left_trig
  dsimp [third,g,c,lowerAngle]
  nlinarith [ht.2.2.1,ht.2.1,pi_hand_enclosure.1]

lemma third_lower {φ : ℝ} (hφ : Lower φ) : (49/50:ℝ)<third φ := by
  have hm : MonotoneOn third (Icc lowerAngle (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun x _ => (third_hasDerivAt x).continuousAt.continuousWithinAt)
      (fun x _ => third_hasDerivAt x)
      (fun x _ => (thirdD_positive x).le)
  exact third_left.trans_le (hm MixedAffine.left_mem hφ hφ.1)

lemma target_affine {A B : ℝ} (ht : OuterState A B) :
    167/10000+(609/1000)*B≤T B := by
  have hh := T_increment_lower outer_zero_mem (NegativeTwo.source_mem ht) ht.1
  rw [T_zero] at hh
  linarith

lemma target_axial_chord {A B : ℝ} (ht : OuterState A B) :
    A≤outerAxial-(261/1000)*B := by
  have hA := (NegativeTwo.primary_mem ht).2
  have hdelta : 0≤outerAxial-A := sub_nonneg.mpr hA
  have hcircle := ht.2.2
  have haxial := axial_circle
  have hraw : B≤(2*outerAxial+1)*(outerAxial-A) := by
    nlinarith [sq_nonneg (A-outerAxial),sq_nonneg B]
  have hfactor := mul_le_mul_of_nonneg_right
    (show 2*outerAxial+1≤383/100 by linarith [outer_endpoint_bounds.2.1]) hdelta
  nlinarith

lemma core_norm_reserve {a b φ : ℝ} (hs : CoreState a b) (hφ : Lower φ) :
    0<a+1/2-Real.sin φ/2-MixedAffine.κ*Real.cos φ := by
  have ht := lower_trig hφ
  have hk := MixedAffine.κ_bounds
  have hsq : (MixedAffine.κ)^2<(183/200:ℝ)^2 := by nlinarith [hk.1,hk.2]
  have he : (Real.sin φ/2+MixedAffine.κ*Real.cos φ)^2+
      (Real.cos φ/2-MixedAffine.κ*Real.sin φ)^2=1/4+(MixedAffine.κ)^2 := by
    linear_combination (1/4+(MixedAffine.κ)^2)*(Real.sin_sq_add_cos_sq φ)
  have hbound : Real.sin φ/2+MixedAffine.κ*Real.cos φ<(1043/1000:ℝ) := by
    nlinarith [sq_nonneg (Real.cos φ/2-MixedAffine.κ*Real.sin φ)]
  linarith [core_primary_lower hs,CoreAngleEndpoint.diagonal_bounds.1]

lemma fourth_early_trig {φ : ℝ} (hφ : Lower φ) (hcut : φ≤123/100) :
    Real.sin φ<(943/1000:ℝ) ∧ (167/500:ℝ)<Real.cos φ := by
  have href : Lower (123/100:ℝ) :=
    ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by linarith [pi_hand_enclosure.1]⟩
  have hs := HighOrderTaylor.sin_le_S13 (x := (123/100:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (123/100:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,
    HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  have hsin := PositiveThree.lower_sin_monotone hφ href hcut
  have hcos := PositiveThree.lower_cos_antitone hφ href hcut
  constructor <;> linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeCore
