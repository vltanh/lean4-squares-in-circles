module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveOuterTwoData

/-!
# Complete primary supports for negative core to positive outer

The lower expression is positive by one square completion on the full
closed interval.  The upper expression is strictly concave there and
positive at its two endpoints.  No local enclosure is assumed.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic

lemma primary_gain :
    (359583/1000000:ℝ)<MixedPrimarySupport.gain g p ∧
      MixedPrimarySupport.gain g p<(44948/125000:ℝ) := by
  have hp := MixedPrimarySupport.N_positive (p := p) (x := 0)
    (show 0<g by norm_num [g])
  constructor
  · apply (lt_div_iff₀ (by positivity : 0<2*MixedPrimarySupport.N g p 0)).2
    have hR := radius_fine.1
    have hN := primary_norm_zero.2
    norm_num [g,p] at *
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0<2*MixedPrimarySupport.N g p 0)).2
    have hR := radius_fine.2
    have hN := primary_norm_zero.1
    norm_num [g,p] at *
    nlinarith

theorem lower_primary_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) :
    0<MixedPrimarySupport.minus g p K x := by
  apply MixedPrimarySupport.minus_positive
    (α := 6323/50000) (β := 1379/4000) (ε := 5059/20000)
    (by norm_num [g]) (by linarith [K_bounds.1])
  · linarith [K_bounds.2,primary_gain.1]
  · norm_num [g]
  · norm_num [g]
  · linarith [primary_zero]
  · norm_num [MixedPrimarySupport.linearCoefficient,g]
  · dsimp [MixedPrimarySupport.quadraticCoefficient]
    linarith [K_bounds.2,primary_gain.1]
  · dsimp [MixedPrimarySupport.cubicCoefficient]
    norm_num [g]
    linarith [K_bounds.1,K_bounds.2,primary_gain.2]
  · norm_num
  · norm_num
  · exact hx

lemma upper_primary_concave :
    ConcaveOn ℝ (Icc (0:ℝ) (7/10)) (MixedPrimarySupport.plus g p K) := by
  apply MixedPrimarySupport.plus_concave
    (by norm_num [g]) (by linarith [K_bounds.1])
  · norm_num [g,p]
    linarith [radius_bounds.2,K_bounds.1]
  · norm_num [g,p]
    linarith [radius_bounds.2,K_bounds.2]

lemma upper_primary_right : (3/10:ℝ)<MixedPrimarySupport.plus g p K (7/10) := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin11,sin9,sin7,cos10,cos8,cos12] at ht
  have hs : Real.sin (7/10)<(1289/2000:ℝ) := by linarith [ht.1.2]
  have hc : (1529/2000:ℝ)<Real.cos (7/10) ∧ Real.cos (7/10)<(153/200:ℝ) :=
    ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩
  have hn := MixedPrimarySupport.N_sq (p := p) (x := (7/10:ℝ))
    (show 0<g by norm_num [g])
  have hp := MixedPrimarySupport.N_positive (p := p) (x := (7/10:ℝ))
    (show 0<g by norm_num [g])
  have hN : MixedPrimarySupport.N g p (7/10)<(2319/2000:ℝ) := by
    have hh := pow_le_pow_left₀ (by linarith [hc.1] : 0≤Real.cos (7/10)) hc.2.le 2
    norm_num [g,p] at hn
    nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<2319/2000))
  have hK : (2108657/1000000:ℝ)<K+7/10 := by linarith [K_bounds.1]
  have hprod := (mul_lt_mul_of_pos_left hc.1
    (by norm_num : (0:ℝ)<2108657/1000000)).trans
      (mul_lt_mul_of_pos_right hK (by linarith [hc.1] : 0<Real.cos (7/10)))
  dsimp [MixedPrimarySupport.plus,g]
  nlinarith

theorem upper_primary_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) :
    0<MixedPrimarySupport.plus g p K x := by
  have hz : MixedPrimarySupport.plus g p K 0=MixedPrimarySupport.minus g p K 0 := by
    simp [MixedPrimarySupport.plus,MixedPrimarySupport.minus]
  exact concave_gt_of_endpoints upper_primary_concave hx
    (by rw [hz]; linarith [primary_zero]) (by linarith [upper_primary_right])

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveOuter
