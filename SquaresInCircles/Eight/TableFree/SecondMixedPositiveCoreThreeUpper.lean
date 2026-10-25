module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreThreePrimary

/-!
# All upper owners from the original aligned relaxation

The relaxed aligned bound holds on the entire outer arc. The exact
finite displacement bounds of the two feasible owners therefore pay
their target-coordinate losses on the complete closed upper half.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic

lemma upper_displacement_cost {a b B x k : ℝ} (hs : OuterState a b) (hx : 0≤x)
    (hk : k≤53/100) (hdisp : B≤a-1+k*x) : γ<value b B (Real.pi/2+x) := by
  have hh := aligned_lower (NegativeTwo.source_mem hs)
  dsimp [aligned] at hh
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hh
  have hp := mul_le_mul_of_nonneg_left hdisp (show 0≤g by norm_num [g])
  have hgk : 0≤1-g*k := by dsimp [g]; linarith
  have hpay := mul_nonneg hgk hx
  dsimp [value,γ]
  nlinarith

theorem upper_secondary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.cos x+b*Real.sin x-B) :
    γ<value b B (Real.pi/2+x) := by
  have hcut : B≤OppositeTwo.upperCut a b x := by
    dsimp [OppositeTwo.upperCut]
    nlinarith
  have hh := OppositeTwo.upper_secondary_displacement hs hx
  exact upper_displacement_cost hs hx.1 (k := (2/5:ℝ)) (by norm_num) (by linarith)

theorem upper_primary {a b A B x : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    γ<value b B (Real.pi/2+x) :=
  upper_displacement_cost hs hx.1 (k := (53/100:ℝ)) le_rfl
    (MixedTwo.PositiveCore.upper_primary_displacement hs ht hx hsep)

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
  have hT := MixedTEnvelope.upper (NegativeTwo.source_mem hs)
  dsimp [MixedTEnvelope.k,MixedTEnvelope.q] at hT
  dsimp [value,c,g,γ]
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.PositiveCore
