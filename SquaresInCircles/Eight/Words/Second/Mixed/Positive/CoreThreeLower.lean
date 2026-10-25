module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreePrimary
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreeZeroContact

/-!
# Eight squares: lower owner exclusions at edge three

The early secondary owner uses the two tangents on the whole interval (`lower_secondary`). High
source coordinates move monotonically to the same fixed rational coordinate in the relaxed
contact expression (`secondary_high_monotone`, `primary_high_monotone`); the target reached there
need not be physical. The early primary owner is closed by the exact zero-contact minimum
(`lower_primary`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open PositiveThree (Lower lowerAngle lower_trig)

lemma secondary_support {a b B φ G q e : ℝ} (hs : OuterState a b)
    (hB : 0≤B) (hG : g≤G) (hT : T b≤e+q*b)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ-B) :
    MixedTransverseSupport.lower G q (-c-e) φ≤value b B φ := by
  have hc := outer_circle_lower (X := -G*Real.sin φ) (Y := G*Real.cos φ-q) hs
  have he : Real.sqrt ((-G*Real.sin φ)^2+(G*Real.cos φ-q)^2)=
      MixedTransverseSupport.lowerN G q φ := by
    dsimp [MixedTransverseSupport.lowerN,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination G^2*(Real.sin_sq_add_cos_sq φ)
  rw [he] at hc
  have hsepG := mul_le_mul_of_nonneg_left hsep (show 0≤G by norm_num [g] at hG; linarith)
  have hgap := mul_nonneg (sub_nonneg.mpr hG) hB
  dsimp [value,MixedTransverseSupport.lower]
  nlinarith

lemma secondary_relaxed_support {b φ q e : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hT : T b≤e+q*b) :
    MixedTransverseSupport.lower g q (-c-e) φ≤ secondaryContact b φ := by
  have hc := outer_circle_lower (X := -g*Real.sin φ) (Y := g*Real.cos φ-q)
    (ShortOuterOne.SameContact.arc_state hb)
  have he : Real.sqrt ((-g*Real.sin φ)^2+(g*Real.cos φ-q)^2)=
      MixedTransverseSupport.lowerN g q φ := by
    dsimp [MixedTransverseSupport.lowerN,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination g^2*(Real.sin_sq_add_cos_sq φ)
  rw [he] at hc
  dsimp [secondaryContact,secondaryCut,MixedTwo.PositiveCore.secondaryCut,MixedTransverseSupport.lower]
  nlinarith

lemma secondary_contact_hasDerivAt {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (fun b => secondaryContact b φ)
      (g*(ratio b*Real.sin φ+Real.cos φ)-TLabel.d1 b) b := by
  have hT : HasDerivAt T (TLabel.d1 b) b := TLabel.outer_hasDerivAt (outer_domain hb)
  have hd := ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).sub_const (1/2)).mul_const
    (Real.sin φ)).sub (((hasDerivAt_id' b).add_const (1/2)).mul_const (Real.cos φ))).sub_const (1/2)
  have h := (hT.const_sub (φ-c)).sub (hd.const_mul g)
  exact h.congr_deriv (by ring)

lemma secondary_high_monotone {φ : ℝ} (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) :
    MonotoneOn (fun b => secondaryContact b φ) (Icc (7/10:ℝ) outerDiagonal) := by
  have hfull : Lower φ := ⟨by dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],hφ.2⟩
  have ht := lower_trig hfull
  have hsine := PositiveThree.lower_sin_monotone
    (show Lower (7/5:ℝ) from ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
      by linarith [pi_hand_enclosure.1]⟩) hfull hφ.1
  have hsin : (197/200:ℝ)<Real.sin φ := by linarith [PrimaryZero.terminal_trig.1]
  have hdom {b : ℝ} (hb : b∈Icc (7/10:ℝ) outerDiagonal) : b∈Icc 0 outerDiagonal :=
    ⟨by linarith [hb.1],hb.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (secondary_contact_hasDerivAt (φ := φ) (hdom hb)).continuousAt.continuousWithinAt)
    (fun b hb => secondary_contact_hasDerivAt (φ := φ) (hdom (Ioo_subset_Icc_self hb)))
  intro b hb
  have hr := (outer_ratio_bounds (hdom (Ioo_subset_Icc_self hb))).1
  have hT := high_ratio (Ioo_subset_Icc_self hb)
  have hp := mul_nonneg (show 0≤ratio b by linarith) (show 0≤g*Real.sin φ-17/20 by norm_num [g]; linarith)
  have hc := mul_nonneg (show 0≤g by norm_num [g]) ht.2.2.1
  nlinarith

lemma late_secondary_relaxed {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) : γ<secondaryContact b φ := by
  have low {y : ℝ} (hy : y∈Icc (0:ℝ) (7/10)) : γ<secondaryContact y φ := by
    have hT := MixedTSmall.upper hy
    have hs := secondary_relaxed_support (φ := φ)
      (show y∈Icc 0 outerDiagonal from ⟨hy.1,hy.2.trans MixedTSmall.seven_mem.2⟩) hT.le
    exact (late_lower hφ).trans_le hs
  by_cases he : b≤7/10
  · exact low ⟨hb.1,he⟩
  · have hm := secondary_high_monotone hφ
      (show (7/10:ℝ)∈Icc (7/10:ℝ) outerDiagonal from ⟨le_rfl,MixedTSmall.seven_mem.2⟩)
      (show b∈Icc (7/10:ℝ) outerDiagonal from ⟨by linarith,hb.2⟩) (by linarith)
    exact (low (show (7/10:ℝ)∈Icc (0:ℝ) (7/10) by norm_num)).trans_le hm

lemma primary_contact_hasDerivAt {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (fun b => primaryContact b φ)
      (g*ratio b/Real.sin φ-TLabel.d1 b) b := by
  have hT : HasDerivAt T (TLabel.d1 b) b := TLabel.outer_hasDerivAt (outer_domain hb)
  have hd := ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).sub_const (1/2)).sub_const
    ((13/12)*Real.cos φ)).div_const (Real.sin φ)).sub_const (1/2)
  have h := (hT.const_sub (φ-c)).sub (hd.const_mul g)
  exact h.congr_deriv (by ring)

lemma primary_high_monotone {φ : ℝ} (hφ : Lower φ) :
    MonotoneOn (fun b => primaryContact b φ) (Icc (7/10:ℝ) outerDiagonal) := by
  have ht := lower_trig hφ
  have hsin : 0<Real.sin φ := by linarith [ht.1]
  have hdom {b : ℝ} (hb : b∈Icc (7/10:ℝ) outerDiagonal) : b∈Icc 0 outerDiagonal :=
    ⟨by linarith [hb.1],hb.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (primary_contact_hasDerivAt (φ := φ) (hdom hb)).continuousAt.continuousWithinAt)
    (fun b hb => primary_contact_hasDerivAt (φ := φ) (hdom (Ioo_subset_Icc_self hb)))
  intro b hb
  have hr := (outer_ratio_bounds (hdom (Ioo_subset_Icc_self hb))).1
  have hT := high_ratio (Ioo_subset_Icc_self hb)
  have hpay : g*ratio b≤g*ratio b/Real.sin φ := by
    apply (le_div_iff₀ hsin).2
    have hh := mul_le_mul_of_nonneg_left ht.2.1
      (mul_nonneg (show 0≤g by norm_num [g]) (show 0≤ratio b by linarith))
    simpa using hh
  dsimp [g] at *
  nlinarith

lemma late_primary_relaxed {b φ : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hφ : φ∈Icc (7/5:ℝ) (Real.pi/2)) : γ<primaryContact b φ := by
  have hfull : Lower φ := ⟨by dsimp [lowerAngle]; linarith [hφ.1,pi_hand_enclosure.2],hφ.2⟩
  have ht := lower_trig hfull
  have hsin : 0<Real.sin φ := by linarith [ht.1]
  have low {y : ℝ} (hy : y∈Icc (0:ℝ) (7/10)) : γ<primaryContact y φ := by
    have hT := mul_le_mul_of_nonneg_right (MixedTSmall.upper hy).le hsin.le
    have hc := outer_circle_lower (X := -g) (Y := -p*Real.sin φ)
      (ShortOuterOne.SameContact.arc_state
        (show y∈Icc 0 outerDiagonal from ⟨hy.1,hy.2.trans MixedTSmall.seven_mem.2⟩))
    have he : Real.sqrt ((-g)^2+(-p*Real.sin φ)^2)=Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by
      congr 1
      ring
    rw [he] at hc
    have hpos := primary_positive
      (show Real.pi/2-φ∈Icc (0:ℝ) (171/1000) from ⟨by linarith [hφ.2],
        by linarith [hφ.1,pi_hand_enclosure.2]⟩)
    have heq : MixedPrimarySupport.minus g p K (Real.pi/2-φ)=
        (φ-c-k+(g+p)/2-γ)*Real.sin φ+g*(1+(13/12)*Real.cos φ)-
          CommonQuarter.radius*Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by
      simp only [MixedPrimarySupport.minus,MixedPrimarySupport.N,K,Real.sin_sub,Real.cos_sub,
        Real.sin_pi_div_two,Real.cos_pi_div_two,zero_mul,one_mul,sub_zero]
      ring
    rw [heq] at hpos
    have hcut : primaryCut (arc y) φ*Real.sin φ=
        arc y-1/2-(13/12)*Real.cos φ-Real.sin φ/2 := by
      dsimp [primaryCut,MixedTwo.PositiveCore.primaryCut]
      field_simp [hsin.ne']
    have hp : 0<(primaryContact y φ-γ)*Real.sin φ := by
      dsimp [primaryContact,g,p,k,MixedTSmall.k,MixedTEnvelope.k,MixedTSmall.q] at *
      nlinarith
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (show primaryContact y φ-γ≤0 by linarith) hsin.le
    linarith
  by_cases he : b≤7/10
  · exact low ⟨hb.1,he⟩
  · have hm := primary_high_monotone hfull
      (show (7/10:ℝ)∈Icc (7/10:ℝ) outerDiagonal from ⟨le_rfl,MixedTSmall.seven_mem.2⟩)
      (show b∈Icc (7/10:ℝ) outerDiagonal from ⟨by linarith,hb.2⟩) (by linarith)
    exact (low (show (7/10:ℝ)∈Icc (0:ℝ) (7/10) by norm_num)).trans_le hm

lemma secondary_angle_lower {a b B φ : ℝ} (hs : OuterState a b) (hB : 0≤B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ-B) : (1:ℝ)<φ := by
  by_contra hn
  have hOne : Lower (1:ℝ) := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
    by linarith [pi_hand_enclosure.1]⟩
  have hsine := PositiveThree.lower_sin_monotone hφ hOne (le_of_not_gt hn)
  have hcos := PositiveThree.lower_cos_antitone hφ hOne (le_of_not_gt hn)
  have hsu := PointProducts.trig (show (0:ℝ)≤1 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at hsu
  have ht := lower_trig hφ
  have ha := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
  have hp := mul_le_mul_of_nonneg_right ha.le (by linarith [ht.1] : 0≤Real.sin φ)
  have hb := mul_nonneg hs.1 ht.2.2.1
  nlinarith [hsu.1.2,one_trig.2]

lemma secondary_source_small {a b B φ : ℝ} (hs : OuterState a b) (hB : 0≤B)
    (hφ : Lower φ) (hφu : φ≤7/5)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ-B) : b<(3/5:ℝ) := by
  by_contra hn
  have hb : (3/5:ℝ)≤b := le_of_not_gt hn
  have hc := hs.2.2
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤11/10)
    (show (11/10:ℝ)≤b+1/2 by linarith) 2
  have ha : a<(229/200:ℝ) := by
    norm_num [Q0] at hc
    nlinarith [hs.1,hs.2.1]
  have hEnd : Lower (7/5:ℝ) := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
    by linarith [pi_hand_enclosure.1]⟩
  have hsu := PositiveThree.lower_sin_monotone hφ hEnd hφu
  have hcl := PositiveThree.lower_cos_antitone hφ hEnd hφu
  have ht := lower_trig hφ
  have hAs := mul_le_mul_of_nonneg_right (show a-1/2≤129/200 by linarith)
    (by linarith [ht.1] : 0≤Real.sin φ)
  have hBc := mul_le_mul_of_nonneg_right (show (11/10:ℝ)≤b+1/2 by linarith) ht.2.2.1
  nlinarith [PrimaryZero.terminal_trig.2.1,PrimaryZero.terminal_trig.2.2.1]

theorem lower_secondary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ-B) : γ<value b B φ := by
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
  by_cases he : φ≤7/5
  · have hb : b∈Icc (0:ℝ) (3/5) := ⟨hs.1,(secondary_source_small hs hB hφ he hsep).le⟩
    have hlo := secondary_angle_lower hs hB hφ hsep
    by_cases hmid : φ≤123/100
    · exact (early_lower ⟨hlo.le,hmid⟩).trans_le
        (secondary_support hs hB (by norm_num [g]) (MixedTSmall.first_tangent hb) hsep)
    · exact (middle_lower ⟨by linarith,he⟩).trans_le
        (secondary_support hs hB le_rfl (MixedTSmall.second_tangent hb) hsep)
  · have hcut : B≤ secondaryCut a b φ := by
      dsimp [secondaryCut,MixedTwo.PositiveCore.secondaryCut]
      nlinarith
    have hp := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    have hh := late_secondary_relaxed (NegativeTwo.source_mem hs) ⟨by linarith,hφ.2⟩
    dsimp [secondaryContact] at hh
    rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hh
    dsimp [value]
    linarith

theorem lower_primary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ-B*Real.sin φ) : γ<value b B φ := by
  have htr := lower_trig hφ
  have hsin : 0<Real.sin φ := by linarith [htr.1]
  have hA : A=(7/12:ℝ) := by
    rcases ht with ⟨rfl,_,_⟩ | ⟨hB,hBA,_⟩
    · rfl
    · have hAc := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤A by linarith) htr.2.2.1
      have hBs := mul_le_mul_of_nonneg_right hB hsin.le
      have ha := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
      nlinarith [htr.2.2.2.2]
  rw [hA] at hsep
  by_cases he : φ≤7/5
  · exact early_primary hs (CoreAngleEndpoint.state_bounds ht).2.2.1 hφ he hsep
  · have hcutEq : primaryCut a φ*Real.sin φ=
        a-1/2-(13/12)*Real.cos φ-Real.sin φ/2 := by
      dsimp [primaryCut,MixedTwo.PositiveCore.primaryCut]
      field_simp [hsin.ne']
    have hcut : B≤primaryCut a φ := by
      apply (mul_le_mul_iff_left₀ hsin).mp
      nlinarith
    have hp := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    have hh := late_primary_relaxed (NegativeTwo.source_mem hs) ⟨by linarith,hφ.2⟩
    dsimp [primaryContact] at hh
    rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hh
    dsimp [value]
    linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
