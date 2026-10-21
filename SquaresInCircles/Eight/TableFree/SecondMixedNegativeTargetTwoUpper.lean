module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeTargetTwoSide
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreTwoUpper

/-!
# All upper owners by an original-source aligned comparison

The core side coordinate max(0,1-a) is physical and aligned-feasible
at the unchanged outer source. The original upper separators allow
only .4x or .53x of coordinate loss. The target label slope bound pays
that finite loss on the entire upper half, including zero coordinates.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget
open CommonQuarter CorePairGeometry Arithmetic

def base (a : ℝ) : ℝ := max 0 (1-a)
def side (B : ℝ) : ℝ := e+g*B-z*B^2

lemma side_label (B : ℝ) : MixedThree.negativeCore (7/12) B=side B := by
  dsimp [MixedThree.negativeCore,side,e,g,z]
  ring

lemma core_side_lower {A B : ℝ} (ht : CoreState A B) : side B≤MixedThree.negativeCore A B := by
  have hh := (CoreAngleEndpoint.state_bounds ht).2.1
  dsimp [side,e,g,z,MixedThree.negativeCore]
  linarith

lemma base_bounds {a b : ℝ} (hs : OuterState a b) : 0≤base a ∧ base a≤(101/1000:ℝ) := by
  have ha := (NegativeTwo.primary_mem hs).1
  exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith [fine_outer_endpoint_bounds.2])⟩

lemma aligned_base {a b : ℝ} (hs : OuterState a b) : γ<Real.pi/2-P b+side (base a) := by
  have hb := base_bounds hs
  have hc : 1≤a+base a := by have hh := le_max_right (0:ℝ) (1-a); dsimp [base]; linarith
  have hh := Side.original_primary hs
    (show base a∈Icc (0:ℝ) (1/2) from ⟨hb.1,by linarith [hb.2]⟩)
    (show PositiveThree.Lower (Real.pi/2) from ⟨by dsimp [PositiveThree.lowerAngle]; linarith,le_rfl⟩)
    (by norm_num; linarith)
  simpa [value,side_label] using hh

lemma upper_displacement_cost {a b A B x ρ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : 0≤x) (hρ : ρ∈Icc (0:ℝ) (53/100)) (hdisp : 1-a-ρ*x≤B) :
    γ<value b A B (Real.pi/2+x) := by
  have hb := base_bounds hs
  have hB := core_transverse ht
  have hρx := mul_nonneg hρ.1 hx
  have hbase : base a≤B+ρ*x := max_le (by linarith [hB.1]) (by linarith)
  have hcore := core_side_lower ht
  have hcost : side (base a)-g*ρ*x≤MixedThree.negativeCore A B := by
    by_cases he : base a≤B
    · have hprod := mul_nonneg (sub_nonneg.mpr he)
        (show 0≤g-z*(B+base a) by dsimp [g,z]; linarith [hB.2,hb.2])
      have hp := mul_nonneg (show 0≤g by norm_num [g]) hρx
      dsimp [side] at hcore ⊢
      nlinarith
    · have hsq : B^2≤(base a)^2 := pow_le_pow_left₀ hB.1 (le_of_not_ge he) 2
      have hp := mul_le_mul_of_nonneg_left hbase (show 0≤g by norm_num [g])
      dsimp [side,z] at hcore ⊢
      nlinarith
  have hpay := mul_nonneg (show 0≤1-g*ρ by dsimp [g]; linarith [hρ.1,hρ.2]) hx
  have hh := aligned_base hs
  dsimp [value]
  nlinarith

theorem upper_secondary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.cos x+b*Real.sin x+B) :
    γ<value b A B (Real.pi/2+x) := by
  have hcut : -B≤OppositeTwo.upperCut a b x := by dsimp [OppositeTwo.upperCut]; nlinarith
  have hh := OppositeTwo.upper_secondary_displacement hs hx
  exact upper_displacement_cost hs ht hx.1 (ρ := (2/5:ℝ)) (by norm_num) (by linarith)

theorem upper_primary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x+B*Real.cos x) :
    γ<value b A B (Real.pi/2+x) := by
  have htr := positive_trig hx
  have hcos : 0<Real.cos x := by linarith [htr.1]
  have hA := mul_le_mul_of_nonneg_right (CoreAngleEndpoint.state_bounds ht).2.1 htr.2.2.1
  have hz : 0≤1-Real.cos x := by linarith [htr.2.1]
  have haxial := mul_le_mul_of_nonneg_right
    (show a-1/2≤183/200 by linarith [(NegativeTwo.primary_mem hs).2,outer_endpoint_bounds.2.1]) hz
  have hprod := mul_nonneg hx.1 (show 0≤7/10-x by linarith [hx.2])
  have hzbound : 1-Real.cos x≤(7/20)*x := by nlinarith [Real.one_sub_sq_div_two_le_cos x]
  have hzpaid := mul_le_mul_of_nonneg_left hzbound (by norm_num : (0:ℝ)≤183/200)
  have hspaid := mul_le_mul_of_nonneg_left htr.2.2.2.2.1 (by norm_num : (0:ℝ)≤1/12)
  have hcpay := mul_le_mul_of_nonneg_left htr.1.le (mul_nonneg (by norm_num : (0:ℝ)≤53/100) hx.1)
  have hdisp : -B≤a-1+(53/100)*x := by
    apply (mul_le_mul_right hcos).mp
    nlinarith
  exact upper_displacement_cost hs ht hx.1 (ρ := (53/100:ℝ)) (by norm_num) (by linarith)

theorem upper_second {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.sin x-b*Real.cos x+A) :
    γ<value b A B (Real.pi/2+x) := by
  by_cases he : (167/100:ℝ)≤Real.pi/2+x
  · exact tail hs ht he
  · have hxsmall : x<(1/10:ℝ) := by linarith [pi_hand_enclosure.1]
    have htφ := positive_trig hx
    have hwidth : (1:ℝ)≤(1+Real.cos x+Real.sin x)/2 := by linarith [htφ.2.2.2.2.2]
    have hsin := htφ.2.2.2.2.1.trans hxsmall.le
    have ha := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
    have has := mul_le_mul_of_nonneg_right ha.le htφ.2.2.1
    have hbc := mul_nonneg hs.1 (by linarith [htφ.1] : 0≤Real.cos x)
    have hA := (CoreAngleEndpoint.state_bounds ht).2.1
    nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget
