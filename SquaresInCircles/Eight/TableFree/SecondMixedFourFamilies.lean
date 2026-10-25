module

public import SquaresInCircles.Eight.TableFree.SecondMixedAffineOwners
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoCycle

/-!
# Four complete original mixed edge-three families

The negative-core to negative-outer pair and the positive-outer to
positive-core pair use one affine all-owner theorem.  The two
positive-to-negative radial orders have direct whole-domain bounds.
Both core pieces, every weak owner, and both closed angle endpoints
are included.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree
open CommonQuarter CorePairGeometry Arithmetic

theorem negative_core_negative_outer {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (91/100:ℝ)<cost 3 kind .outer false false a b A B φ := by
  let d : ℝ := 11021/50000-(8623/25000)*(7/12)-K 0
  have hd : d≤321/5000 := by dsimp [d]; linarith [K_zero_bounds.1]
  have hh := MixedAffine.original (g := (98439/100000:ℝ)) (d := d)
    hs ht hφ (by norm_num) hd j hm
  have hchord := K_chord (NegativeTwo.source_mem ht)
  have hcore := negative_core_upper hs
  rw [core_outer_negative_negative hk ht]
  dsimp [MixedAffine.value,d] at hh
  linarith

theorem positive_outer_positive_core {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (91/100:ℝ)<cost 3 .outer kind true true a b A B φ := by
  let d : ℝ := 497/10000-V 0
  have hd : d≤321/5000 := by dsimp [d]; linarith [V_zero_bounds.1]
  have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) (-1) φ := by
    rw [show (-1:ℝ)= -(1:ℝ) by ring,margin_reflection]
    exact hm
  have hh := MixedAffine.original (g := (94831/100000:ℝ)) (d := d)
    ht hs hφ (by norm_num) hd (reflectedOwner j) hrev
  have hchord := V_chord (NegativeTwo.source_mem hs)
  rw [outer_core_positive_positive hk hs]
  dsimp [MixedAffine.value,d] at hh
  linarith [hs.1]

lemma positive_core_early_trig {φ : ℝ} (hφ : PositiveThree.Lower φ)
    (hearly : φ≤19/20) : (29/50:ℝ)<Real.cos φ ∧ Real.sin φ<(41/50:ℝ) := by
  have href : PositiveThree.Lower (19/20:ℝ) := by
    constructor
    · dsimp [PositiveThree.lowerAngle]
      linarith [pi_hand_enclosure.2]
    · linarith [pi_hand_enclosure.1]
  have ht := PointProducts.trig (show (0:ℝ)≤19/20 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hc := PositiveThree.lower_cos_antitone hφ href hearly
  have hs := PositiveThree.lower_sin_monotone hφ href hearly
  exact ⟨by linarith [ht.2.1],by linarith [ht.1.2]⟩

theorem positive_core_negative_outer {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 (-1) φ) :
    (9/10:ℝ)<cost 3 kind .outer true false a b A B φ := by
  let d : ℝ := 1449/100000-K 0
  have hd : d<(4439/100000:ℝ) := by dsimp [d]; linarith only [K_zero_bounds.1]
  have hcore := CoreAngleEndpoint.state_bounds hs
  have hcost : φ-d+(7/10)*(b+B)≤cost 3 kind .outer true false a b A B φ := by
    rw [core_outer_positive_negative hk ht]
    have hh := K_chord (NegativeTwo.source_mem ht)
    dsimp [d]
    linarith [hcore.2.2.1]
  by_cases hlate : (19/20:ℝ)≤φ
  · linarith only [hcost,hlate,hd,hcore.2.2.1,ht.1]
  have hlower : PositiveThree.Lower φ :=
    ⟨by dsimp [PositiveThree.lowerAngle]; linarith only [(abs_le.mp hφ).1],
      by linarith only [hlate,pi_hand_enclosure.1]⟩
  have htr := PositiveThree.lower_trig hlower
  have hsine : 0<Real.sin φ := by linarith only [htr.1]
  have hphi : (87079/100000:ℝ)<φ := by
    dsimp [PositiveThree.Lower,PositiveThree.lowerAngle] at hlower
    linarith only [hlower.1,pi_hand_enclosure.1]
  have hg : (7/10:ℝ)∈Icc (7/10) (197/200) := by norm_num
  fin_cases j
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ+B*Real.cos φ := by
      norm_num [Eight.forwardMargin,PositiveThree.lower_width hlower] at hm
      linarith only [hm]
    have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).2 hsine.le
    have hBc := mul_le_mul_of_nonneg_left (Real.cos_le_one φ) ht.1
    have hcompare : MixedAffine.first (7/10) φ-d≤φ-d+(7/10)*(b+B) := by
      dsimp [MixedAffine.first,MixedAffine.κ]
      linarith only [hsep,hA,hBc]
    linarith only [MixedAffine.first_lower hg hlower,hcompare,hcost,hd]
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤-a*Real.cos φ+b*Real.sin φ+A := by
      norm_num [Eight.forwardMargin,PositiveThree.lower_width hlower] at hm
      linarith only [hm]
    have ha := mul_le_mul_of_nonneg_right hcore.1.le htr.2.2.1
    have hb : (Real.cos φ-MixedAffine.κ)/Real.sin φ≤b-1/2 := by
      apply (div_le_iff₀ hsine).2
      dsimp [MixedAffine.κ]
      linarith only [hsep,ha,(NegativeTwo.primary_mem ht).2]
    have hcompare : MixedAffine.second (7/10) φ-d≤φ-d+(7/10)*(b+B) := by
      dsimp [MixedAffine.second]
      rw [mul_div_assoc]
      linarith only [hb,ht.1]
    linarith only [MixedAffine.second_lower hg hlower,hcompare,hcost,hd]
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ+b*Real.cos φ+B := by
      norm_num [Eight.forwardMargin,PositiveThree.lower_width hlower] at hm
      linarith only [hm]
    have ha := mul_le_mul_of_nonneg_right hcore.2.1 hsine.le
    have hb := mul_le_mul_of_nonneg_left (Real.cos_le_one φ) hcore.2.2.1
    have hsum : (5/12:ℝ)≤b+B := by linarith only [hsep,ha,hb,htr.2.1,htr.2.2.1]
    linarith only [hsum,hcost,hd,hphi]
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ := by
      norm_num [Eight.forwardMargin,PositiveThree.lower_width hlower] at hm
      linarith only [hm]
    have hearly := positive_core_early_trig hlower (le_of_not_ge hlate)
    have hA : (899/1000:ℝ)≤A := by
      linarith only [(NegativeTwo.primary_mem ht).1,fine_outer_endpoint_bounds.2]
    have hB : B≤9/10 := (NegativeTwo.source_mem ht).2.trans outer_endpoint_bounds.2.2.2.le
    have hac := mul_le_mul hA hearly.1.le (by norm_num : (0:ℝ)≤29/50)
      (by linarith only [hA] : 0≤A)
    have hbs := mul_le_mul hB hearly.2.le hsine.le (by norm_num : (0:ℝ)≤9/10)
    have hwidth : 1≤(1+Real.sin φ+Real.cos φ)/2 := by linarith only [htr.2.2.2.2]
    linarith only [hsep,hac,hbs,hwidth,hcore.2.1]

theorem positive_outer_negative_core {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) :
    (1:ℝ)<cost 3 .outer kind true false a b A B φ := by
  rw [outer_core_positive_negative hk hs]
  have hv := V_lower (NegativeTwo.source_mem hs)
  have hb := (CoreAngleEndpoint.state_bounds ht).2.2.1
  linarith [(abs_le.mp hφ).1,pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree
