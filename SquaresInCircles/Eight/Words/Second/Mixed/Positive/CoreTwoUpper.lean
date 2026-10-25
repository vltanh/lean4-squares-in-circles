module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreTwoData

/-!
# Eight squares: complete upper owners by finite original-coordinate comparison

The secondary and primary separators permit at most .4*x and .53*x
of displacement from alignment.  The already proved P-label bounds
pay these losses on the entire upper half, including zero coordinates
and the aligned endpoint.  Both core pieces remain in the domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic

lemma upper_primary_displacement {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    B≤a-1+(53/100)*x := by
  have htr := positive_trig hx
  have hcos : 0<Real.cos x := by linarith [htr.1]
  have hA := mul_le_mul_of_nonneg_right (CoreAngleEndpoint.state_bounds ht).2.1 htr.2.2.1
  have hz : 0≤1-Real.cos x := by linarith [htr.2.1]
  have haxial := mul_le_mul_of_nonneg_right
    (show a-1/2≤183/200 by linarith [(NegativeTwo.primary_mem hs).2,outer_endpoint_bounds.2.1]) hz
  have hprod := mul_nonneg hx.1 (show 0≤7/10-x by linarith [hx.2])
  have hzbound : 1-Real.cos x≤(7/20)*x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hzpaid := mul_le_mul_of_nonneg_left hzbound (by norm_num : (0:ℝ)≤183/200)
  have hspaid := mul_le_mul_of_nonneg_left htr.2.2.2.2.1 (by norm_num : (0:ℝ)≤1/12)
  have hcpay := mul_le_mul_of_nonneg_left htr.1.le
    (mul_nonneg (by norm_num : (0:ℝ)≤53/100) hx.1)
  apply (mul_le_mul_iff_left₀ hcos).mp
  linarith

theorem upper_secondary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.cos x+b*Real.sin x-B) :
    γ<value b B (Real.pi/2+x) := by
  have hcut : B≤OppositeTwo.upperCut a b x := by
    dsimp [OppositeTwo.upperCut]
    nlinarith
  have hdisp := OppositeTwo.upper_secondary_displacement hs hx
  have hh := upper_displacement_cost hs (CoreAngleEndpoint.state_bounds ht).2.2.1 hx.1
    (k := (2/5:ℝ)) (by norm_num) (by norm_num) (by linarith)
  dsimp [γ]
  linarith

theorem upper_primary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    γ<value b B (Real.pi/2+x) := by
  have hh := upper_displacement_cost hs (CoreAngleEndpoint.state_bounds ht).2.2.1 hx.1
    (k := (53/100:ℝ)) (by norm_num) le_rfl (upper_primary_displacement hs ht hx hsep)
  dsimp [γ]
  linarith

theorem upper_second {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.sin x-b*Real.cos x+A) :
    γ<value b B (Real.pi/2+x) := by
  have htr := positive_trig hx
  have hA := (CoreAngleEndpoint.state_bounds ht).2.1
  have ha : a<(283/200:ℝ) := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
  have has := mul_le_mul_of_nonneg_right ha.le htr.2.2.1
  have hbc := mul_nonneg hs.1 (by linarith [htr.1] : 0≤Real.cos x)
  have hxlo : (2/5:ℝ)<x := by
    by_contra hn
    have hsin : Real.sin x≤(2/5:ℝ) := htr.2.2.2.2.1.trans (le_of_not_gt hn)
    have hs2 := pow_le_pow_left₀ htr.2.2.1 hsin 2
    have hcos : (229/250:ℝ)<Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x,htr.1]
    nlinarith
  have hb : b<(2/5:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left htr.1.le hs.1
    nlinarith [htr.2.2.2.1]
  have hB : B<(559/1000:ℝ) :=
    (CoreAngleEndpoint.state_bounds ht).2.2.2.2.trans_lt
      (by linarith [CoreAngleEndpoint.diagonal_bounds.2])
  have hP := P_chord (NegativeTwo.source_mem hs)
  dsimp [value,e,g,γ]
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
