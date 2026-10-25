module

public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial
public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreeUpper
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreeZeroContact
public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.SourceThreeLateShape
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle

/-!
# Eight squares: every early positive-core transverse owner

A single quadratic tangent controls the whole initial target interval.
The fixed harmonic coefficient cages transfer to the proved rational
whole-angle polynomial. Concavity of the target derivative handles all
remaining targets at once.
-/

section
/-!
## Lower owner exclusions at edge three

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
end
end
end

section
/-!
## All original role-three negative-outer to positive-core owners

The four weak physical axes are exhausted on the full closed quarter
window.  The estimates keep the original circle point, radius and
core piece, and require no separately supplied strip theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width)

theorem original {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) : γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds ht
  have hrad := core_radius_sq ht
  by_cases hlo : φ≤Real.pi/2
  · have hlow : Lower φ := ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],hlo⟩
    have htr := lower_trig hlow
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    fin_cases j
    · have hlarge : 1≤A*Real.sin φ-B*Real.cos φ := by
        norm_num [Eight.forwardMargin,lower_width hlow] at hm
        linarith [hs.1]
      have he : (A*Real.sin φ-B*Real.cos φ)^2+
          (A*Real.cos φ+B*Real.sin φ)^2=A^2+B^2 := by
        linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (A*Real.cos φ+B*Real.sin φ)]
    · have hac := mul_nonneg (show 0≤a by linarith [hs.1,hs.2.1]) htr.2.2.1
      have hbs := mul_nonneg hs.1 (by linarith [htr.1] : 0≤Real.sin φ)
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      nlinarith [hcore.2.1]
    · apply lower_secondary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    · apply lower_primary hs ht hlow
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
  · let x := φ-Real.pi/2
    have hx : x∈Icc (0:ℝ) (7/10) := ⟨by dsimp [x]; linarith,
      by dsimp [x]; exact (abs_le.mp hφ).2⟩
    have hφeq : φ=Real.pi/2+x := by dsimp [x]; ring
    rw [hφeq] at hm ⊢
    have htr := positive_trig hx
    have hwidth : (1:ℝ)≤(1+Real.cos x+Real.sin x)/2 := by linarith [htr.2.2.2.2.2]
    fin_cases j
    · have hlarge : 1≤A*Real.cos x+B*Real.sin x := by
        norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
        linarith [hs.1]
      have he : (A*Real.cos x+B*Real.sin x)^2+
          (A*Real.sin x-B*Real.cos x)^2=A^2+B^2 := by
        linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq x)
      have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
      nlinarith [sq_nonneg (A*Real.sin x-B*Real.cos x)]
    · apply upper_second hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_secondary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith
    · apply upper_primary hs ht hx
      norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,NegativeTwo.upper_width hx] at hm
      linarith

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    SecondWord.threshold 3<cost 3 .outer kind false true a b A B φ := by
  rw [threshold_value,outer_core_negative_positive hk hs]
  have h := original hs ht hφ j hm
  simp only [γ,value,c,g] at h
  linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
end
end
end

section
/-!
## Physical-cycle adapters for the complete positive-core role-three row

The exact original owner is preserved, including ties.  Reflection
carries the literal role-three cost to role five.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Role (i : Vertex) (source target : RadialKind) (σ τ : Bool) : Prop :=
  (i=3 ∧ source=.outer ∧ target≠.outer ∧ σ=false ∧ τ=true) ∨
  (i=5 ∧ source≠.outer ∧ target=.outer ∧ σ=false ∧ τ=true)

theorem original_role {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hrole : Role i source target σ τ)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    SecondWord.threshold i<cost i source target σ τ a b A B φ := by
  rcases hrole with ⟨rfl,rfl,hk,rfl,rfl⟩ | ⟨rfl,hk,rfl,rfl,rfl⟩
  · exact literal hk (by simpa [State] using hs) (by simpa [State,hk] using ht)
      hφ j (by simpa [WordProblems.sign] using hm)
  · have hs' : CoreState a b := by simpa [State,hk] using hs
    have ht' : OuterState A B := by simpa [State] using ht
    have heq := margin_reflection j a b A B (-1) 1 φ
    have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) 1 φ := by
      norm_num at heq
      rw [heq]
      simpa [WordProblems.sign] using hm
    have hh := literal hk ht' hs' hφ (reflectedOwner j) hrev
    have he := cost_reflection (3:Vertex) .outer source false true A B a b φ
    norm_num [reverseEdge] at he
    rw [←he] at hh
    simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)))
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  exact original_role hrole (actual_state C i) (actual_state C (next i)) hφ j
    (original_margin C F hgap i j howner)

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : Role i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))) :
    SecondWord.threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole j howner

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
end
end
end

section
/-!
## One whole-angle polynomial for the early positive mixed contact

`lowerPoly` is a rational lower polynomial for the quadratic reference envelope of the early
positive mixed contact, built from Taylor polynomials of sine and cosine and the coefficient
cages `C ≥ -.204013`, `A ≥ -.638364`, `B ≥ 1.347384`, `D ≤ -.159078`, `E ≥ -.153197`.

On the whole interval `[.87,1.3]` the polynomial exceeds `.00099` (`lower`): its Bernstein
coefficients there are positive, the smallest being its value at the right endpoint.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SecondWord.PositiveEarlyPolynomial
open Polynomial WholeIntervalPolynomial

def S13 : ℚ[X] :=
  X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7+
    C (1/362880)*X^9-C (1/39916800)*X^11+C (1/6227020800)*X^13

def C12 : ℚ[X] :=
  1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+
    C (1/40320)*X^8-C (1/3628800)*X^10+C (1/479001600)*X^12

def C14 : ℚ[X] := C12-C (1/87178291200)*X^14

/-- The rational Taylor lower expression, with the required .89765
already subtracted. -/
def lowerPoly : ℚ[X] :=
  X-C (204013/1000000)-C (638364/1000000)*S13+
    C (1347384/1000000)*C14-
    C (159078/1000000)*(C12.comp (C 2*X))-
    C (153197/1000000)*(S13.comp (C 2*X))-C (17953/20000)

/-- The early angle interval has a strict polynomial reserve above `.00099`: on `[.87, 1.3]` the
polynomial `lowerPoly - 99/100000` has positive Bernstein coefficients of degree `14` (the last is
its value at the right endpoint), a positive combination that `linarith` finds. -/
theorem lower {x : ℝ} (hx : x∈Set.Icc (87/100:ℝ) (13/10)) :
    (99/100000:ℝ)<aeval x lowerPoly := by
  have h0 : 0≤x-87/100 := sub_nonneg.2 hx.1
  have h1 : 0≤13/10-x := sub_nonneg.2 hx.2
  have hb (i j : ℕ) : 0≤(x-87/100)^i*(13/10-x)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  simp only [lowerPoly,S13,C14,C12,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,
    aeval_comp,eq_ratCast]
  push_cast
  linarith [hb 14 0,hb 13 1,hb 12 2,hb 11 3,hb 10 4,hb 9 5,hb 8 6,hb 7 7,hb 6 8,hb 5 9,hb 4 10,
    hb 3 11,hb 2 12,hb 1 13,hb 0 14]

end SquaresInCircles.Eight.SecondWord.PositiveEarlyPolynomial
end
end
end

section
/-!
## Exact references for the early transverse quadratic

The reference target is B=.24. Its actual radical, label and slope
determine all five harmonic coefficients of the quadratic minimum.
Every coefficient cage is proved from that fixed physical circle point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Early
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open PositiveThree (Lower lowerAngle lower_trig)
open StationaryPrimitives (Interval)
open OppositeThree.ReferenceAlgebra

def r : ℝ := 6/25
def m : ℝ := 143/100
def G (φ : ℝ) : ℝ := F r φ-(FB r φ)^2/(2*m)
def c0 : ℝ := -e+g/2-L r-g^2*(1+(ratio r)^2)/(4*m)-(LLabel.d1 r)^2/(2*m)
def cSin : ℝ := g*(1-U r)+g*LLabel.d1 r*ratio r/m
def cCos : ℝ := g*(r+1/2)+g*LLabel.d1 r/m
def cTwo : ℝ := -g^2*(1-(ratio r)^2)/(4*m)
def cMix : ℝ := -g^2*ratio r/(2*m)

lemma harmonic (φ : ℝ) : G φ=φ+c0+cSin*Real.sin φ+cCos*Real.cos φ+
    cTwo*Real.cos (2*φ)+cMix*Real.sin (2*φ) := by
  dsimp [G,F,source,FB,c0,cSin,cCos,cTwo,cMix,U,m]
  rw [Real.cos_two_mul,Real.sin_two_mul]
  linear_combination -(50/143)*g^2*(ratio r)^2*(Real.sin_sq_add_cos_sq φ)

private lemma r35_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r35_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

/-! Endpoint equations for each enclosure, used to evaluate the enclosures by rewriting
instead of unfolding the definitions (which carry their membership proofs). -/

private lemma r35_shifted_eq {y : ℝ} : U y = Real.sqrt (Q0-(y+1/2)^2) := by dsimp [U,arc]; ring
private lemma r35_shifted_lo {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).lo = (rootThree (radicand Y) s hs hr).lo :=
  r35_mpr_lo r35_shifted_eq (congrArg _ r35_shifted_eq) _
private lemma r35_shifted_hi {y : ℝ} (Y : Interval y) (s : ℝ) (hs : 0<s)
    (hr : 0≤(radicand Y).lo) :
    (shifted Y s hs hr).hi = (rootThree (radicand Y) s hs hr).hi :=
  r35_mpr_hi r35_shifted_eq (congrArg _ r35_shifted_eq) _

private lemma r35_coordinate_eq {y : ℝ} : arc y = U y-1/2 := by dsimp [U]; ring
private lemma r35_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r35_mpr_lo r35_coordinate_eq (congrArg _ r35_coordinate_eq) _
private lemma r35_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r35_mpr_hi r35_coordinate_eq (congrArg _ r35_coordinate_eq) _

private lemma r35_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(arc y)+H.q*y+H.r*y^2+H.s*(arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r35_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r35_mpr_lo (r35_label_eq H) (congrArg _ (r35_label_eq H)) _
private lemma r35_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r35_mpr_hi (r35_label_eq H) (congrArg _ (r35_label_eq H)) _

private lemma r35_ratioBox_lo {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioBox Y X hX).lo = ((Y.add (Interval.point (1/2))).div X hX).lo := rfl
private lemma r35_ratioBox_hi {y : ℝ} (Y : Interval y) (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioBox Y X hX).hi = ((Y.add (Interval.point (1/2))).div X hX).hi := rfl
private lemma r35_ratioDBox_lo {y : ℝ} (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDBox X hX).lo = ((Interval.point Q0).div X.cube (Interval.cube_lo_pos hX)).lo := rfl
private lemma r35_ratioDBox_hi {y : ℝ} (X : Interval (U y)) (hX : 0<X.lo) :
    (ratioDBox X hX).hi = ((Interval.point Q0).div X.cube (Interval.cube_lo_pos hX)).hi := rfl
private lemma r35_firstBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) :
    (firstBox H Y X hX).lo = ((((Interval.point H.q).add ((Interval.point (2*H.r)).mul Y)).add
      ((Interval.point H.s).mul (coordinate X))).sub
        (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioBox Y X hX))).lo := rfl
private lemma r35_firstBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) :
    (firstBox H Y X hX).hi = ((((Interval.point H.q).add ((Interval.point (2*H.r)).mul Y)).add
      ((Interval.point H.s).mul (coordinate X))).sub
        (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioBox Y X hX))).hi := rfl
private lemma r35_secondBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) :
    (secondBox H Y X hX).lo = (((Interval.point (2*H.r)).sub
      ((Interval.point (2*H.s)).mul (ratioBox Y X hX))).sub
        (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDBox X hX))).lo := rfl
private lemma r35_secondBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y))
    (hX : 0<X.lo) :
    (secondBox H Y X hX).hi = (((Interval.point (2*H.r)).sub
      ((Interval.point (2*H.s)).mul (ratioBox Y X hX))).sub
        (((Interval.point H.p).add ((Interval.point H.s).mul Y)).mul (ratioDBox X hX))).hi := rfl

private lemma r35_rootStep_lo {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootStep X s hs hX).lo = X.lo/((s+X.hi/s)/2) := rfl
private lemma r35_rootStep_hi {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootStep X s hs hX).hi = (s+X.hi/s)/2 := rfl
private lemma r35_rootThree_lo {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootThree X s hs hX).lo = (rootStep X _
      (rootStep_hi_pos X _ (rootStep_hi_pos X s hs hX) hX) hX).lo := rfl
private lemma r35_rootThree_hi {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo) :
    (rootThree X s hs hX).hi = (rootStep X _
      (rootStep_hi_pos X _ (rootStep_hi_pos X s hs hX) hX) hX).hi := rfl
private lemma r35_radicand_lo {y : ℝ} (Y : Interval y) :
    (radicand Y).lo = ((Interval.point Q0).sub ((Y.add (Interval.point (1/2))).square)).lo := rfl
private lemma r35_radicand_hi {y : ℝ} (Y : Interval y) :
    (radicand Y).hi = ((Interval.point Q0).sub ((Y.add (Interval.point (1/2))).square)).hi := rfl

private lemma r35_mul_lo {x y : ℝ} (X : Interval x) (Y : Interval y) :
    (X.mul Y).lo = min (min (X.lo*Y.lo) (X.lo*Y.hi)) (min (X.hi*Y.lo) (X.hi*Y.hi)) := rfl
private lemma r35_mul_hi {x y : ℝ} (X : Interval x) (Y : Interval y) :
    (X.mul Y).hi = max (max (X.lo*Y.lo) (X.lo*Y.hi)) (max (X.hi*Y.lo) (X.hi*Y.hi)) := rfl
private lemma r35_square_lo {x : ℝ} (X : Interval x) : X.square.lo = (X.mul X).lo := rfl
private lemma r35_square_hi {x : ℝ} (X : Interval x) : X.square.hi = (X.mul X).hi := rfl
private lemma r35_cube_lo {x : ℝ} (X : Interval x) : X.cube.lo = (X.square.mul X).lo := rfl
private lemma r35_cube_hi {x : ℝ} (X : Interval x) : X.cube.hi = (X.square.mul X).hi := rfl
private lemma r35_inv_lo {x : ℝ} (X : Interval x) (h : 0<X.lo) : (X.inv h).lo = 1/X.hi := rfl
private lemma r35_inv_hi {x : ℝ} (X : Interval x) (h : 0<X.lo) : (X.inv h).hi = 1/X.lo := rfl
private lemma r35_div_lo {x y : ℝ} (X : Interval x) (Y : Interval y) (h : 0<Y.lo) :
    (X.div Y h).lo = (X.mul (Y.inv h)).lo := rfl
private lemma r35_div_hi {x y : ℝ} (X : Interval x) (Y : Interval y) (h : 0<Y.lo) :
    (X.div Y h).hi = (X.mul (Y.inv h)).hi := rfl
private lemma r35_add_lo {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.add Y).lo = X.lo+Y.lo := rfl
private lemma r35_add_hi {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.add Y).hi = X.hi+Y.hi := rfl
private lemma r35_sub_lo {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.sub Y).lo = X.lo-Y.hi := rfl
private lemma r35_sub_hi {x y : ℝ} (X : Interval x) (Y : Interval y) : (X.sub Y).hi = X.hi-Y.lo := rfl
private lemma r35_point_lo (x : ℝ) : (Interval.point x).lo = x := rfl
private lemma r35_point_hi (x : ℝ) : (Interval.point x).hi = x := rfl

local macro "expand_reference" : tactic => `(tactic|
  simp only [r35_shifted_lo,r35_shifted_hi,r35_coordinate_lo,r35_coordinate_hi,r35_labelBox_lo,
    r35_labelBox_hi,r35_ratioBox_lo,r35_ratioBox_hi,r35_ratioDBox_lo,r35_ratioDBox_hi,
    r35_firstBox_lo,r35_firstBox_hi,r35_secondBox_lo,r35_secondBox_hi,
    r35_radicand_lo,r35_radicand_hi,r35_rootThree_lo,r35_rootThree_hi,r35_rootStep_lo,
    r35_rootStep_hi,r35_mul_lo,r35_mul_hi,r35_square_lo,r35_square_hi,r35_cube_lo,r35_cube_hi,
    r35_inv_lo,r35_inv_hi,r35_div_lo,r35_div_hi,r35_add_lo,r35_add_hi,r35_sub_lo,r35_sub_hi,
    r35_point_lo,r35_point_hi])

local macro "eval_reference" : tactic => `(tactic|
  norm_num [r,m,g,e,EdgeThreeAligned.gp,EdgeThreeAligned.ep,LLabel,Q0])

local macro "coefficient_reference" : tactic => `(tactic|
  (expand_reference; eval_reference))

lemma coefficients :
    -(204013/1000000:ℝ)<c0 ∧ -(159591/250000:ℝ)<cSin ∧
    (168423/125000:ℝ)<cCos ∧ cTwo< -(79539/500000:ℝ) ∧
    -(153197/1000000:ℝ)<cMix := by
  let X := shifted (Interval.point r) (9/5) (by norm_num) (by coefficient_reference)
  have hXlo : X.lo=266866018209/145414339285 := by dsimp only [X]; coefficient_reference
  have hXhi : X.hi=29082867857/15847150725 := by dsimp only [X]; coefficient_reference
  have hX : 0<X.lo := by rw [hXlo]; norm_num
  let R := ratioBox (Interval.point r) X hX
  let J := labelBox LLabel (Interval.point r) X
  let D := firstBox LLabel (Interval.point r) X hX
  let C₀ := (((Interval.point (-e+g/2)).sub J).sub
    (((Interval.point (g^2)).mul ((Interval.point 1).add R.square)).div
      (Interval.point (4*m)) (by norm_num [Interval.point,m]))).sub
        (D.square.div (Interval.point (2*m)) (by norm_num [Interval.point,m]))
  let C₁ := ((Interval.point g).mul ((Interval.point 1).sub X)).add
    ((((Interval.point g).mul D).mul R).div (Interval.point m) (by norm_num [Interval.point,m]))
  let C₂ := (Interval.point (g*(r+1/2))).add
    (((Interval.point g).mul D).div (Interval.point m) (by norm_num [Interval.point,m]))
  let C₃ := ((Interval.point (-g^2)).mul ((Interval.point 1).sub R.square)).div
    (Interval.point (4*m)) (by norm_num [Interval.point,m])
  let C₄ := ((Interval.point (-g^2)).mul R).div
    (Interval.point (2*m)) (by norm_num [Interval.point,m])
  have h0 : -(204013/1000000:ℝ)<C₀.lo := by
    dsimp only [C₀,D,J,R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h1 : -(159591/250000:ℝ)<C₁.lo := by
    dsimp only [C₁,D,R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h2 : (168423/125000:ℝ)<C₂.lo := by
    dsimp only [C₂,D]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h3 : C₃.hi< -(79539/500000:ℝ) := by
    dsimp only [C₃,R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h4 : -(153197/1000000:ℝ)<C₄.lo := by
    dsimp only [C₄,R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  exact ⟨h0.trans_le C₀.mem.1,h1.trans_le C₁.mem.1,h2.trans_le C₂.mem.1,
    C₃.mem.2.trans_lt h3,h4.trans_le C₄.mem.1⟩

lemma trig_13 : (9635581/10000000:ℝ)<Real.sin (13/10) ∧
    (2674988/10000000:ℝ)<Real.cos (13/10) := by
  have hs := HighOrderTaylor.S15_le_sin (x := (13/10:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (13/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hc
  exact ⟨by linarith,by linarith⟩

lemma reference_31 :
    (2243/5000:ℝ)<ratio (31/100) ∧ (133/200:ℝ)<ratioD (31/100) ∧
    LLabel.d1 (31/100)<(1793/2500:ℝ) ∧ LLabel.d2 (31/100)< -(113/125:ℝ) := by
  let X := shifted (Interval.point (31/100:ℝ)) (9/5) (by norm_num) (by coefficient_reference)
  have hXlo : X.lo=25455775424175432/14099731360386005 := by dsimp only [X]; coefficient_reference
  have hXhi : X.hi=2819946272077201/1561943575651200 := by dsimp only [X]; coefficient_reference
  have hX : 0<X.lo := by rw [hXlo]; norm_num
  let R := ratioBox (Interval.point (31/100:ℝ)) X hX
  let R₁ := ratioDBox X hX
  let D := firstBox LLabel (Interval.point (31/100:ℝ)) X hX
  let D₁ := secondBox LLabel (Interval.point (31/100:ℝ)) X hX
  have h0 : (2243/5000:ℝ)<R.lo := by
    dsimp only [R]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h1 : (133/200:ℝ)<R₁.lo := by
    dsimp only [R₁]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h2 : D.hi<(1793/2500:ℝ) := by
    dsimp only [D]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  have h3 : D₁.hi< -(113/125:ℝ) := by
    dsimp only [D₁]; expand_reference; simp only [hXlo,hXhi]; eval_reference
  exact ⟨h0.trans_le R.mem.1,h1.trans_le R₁.mem.1,D.mem.2.trans_lt h2,D₁.mem.2.trans_lt h3⟩

lemma derivative_references : 0<FB (31/100) (13/10) ∧ 0<FB outerDiagonal (13/10) := by
  have hh := reference_31
  have ht := trig_13
  have hp := mul_le_mul hh.1.le ht.1.le (by norm_num : (0:ℝ)≤9635581/10000000)
    (by linarith [hh.1] : 0≤ratio (31/100))
  constructor
  · dsimp [FB,g,EdgeThreeAligned.gp]
    nlinarith [hh.2.2.1,ht.2]
  · rw [FB,ratio_diagonal,L_first_diagonal]
    dsimp [g,EdgeThreeAligned.gp]
    linarith [ht.1,ht.2,fine_outer_endpoint_bounds.2]

lemma curvature_reference : m<g*ratioD (31/100)*(19121/25000)-LLabel.d2 (31/100) := by
  have hh := reference_31
  dsimp [m,g,EdgeThreeAligned.gp]
  linarith [hh.2.1,hh.2.2.2]

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Early
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Early
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratioD)
open PositiveThree (Lower lowerAngle lower_trig)

def angles : Set ℝ := Icc lowerAngle (13/10)

lemma lower_mem {φ : ℝ} (hφ : φ∈angles) : Lower φ :=
  ⟨hφ.1,by linarith [hφ.2,pi_hand_enclosure.1]⟩

lemma polynomial_evaluation (φ : ℝ) : Polynomial.aeval φ PositiveEarlyPolynomial.lowerPoly=
    φ-204013/1000000-(159591/250000)*HighOrderTaylor.S13 φ+
      (168423/125000)*HighOrderTaylor.C14 φ-
      (79539/500000)*HighOrderTaylor.C12 (2*φ)-
      (153197/1000000)*HighOrderTaylor.S13 (2*φ)-γ := by
  norm_num [PositiveEarlyPolynomial.lowerPoly,PositiveEarlyPolynomial.S13,
    PositiveEarlyPolynomial.C12,PositiveEarlyPolynomial.C14,Polynomial.aeval_comp,
    HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8,γ,EdgeThreeAligned.threshold]
  ring

lemma scalar_lower {φ : ℝ} (hφ : φ∈angles) : γ<G φ := by
  have ht := lower_trig (lower_mem hφ)
  have hφ0 : 0≤φ := by dsimp [angles,lowerAngle] at hφ; linarith [pi_hand_enclosure.1,hφ.1]
  have hs : 0≤Real.sin φ := by linarith [ht.1]
  have hc := ht.2.2.1
  have hs2 : 0≤Real.sin (2*φ) := by rw [Real.sin_two_mul]; positivity
  have hc2 : Real.cos (2*φ)≤0 := by
    rw [Real.cos_two_mul]
    have hcsq := pow_le_pow_left₀ hc ht.2.2.2.1.le 2
    nlinarith
  have ha := mul_le_mul_of_nonneg_right coefficients.2.1.le hs
  have hb := mul_le_mul_of_nonneg_right coefficients.2.2.1.le hc
  have hd := mul_le_mul_of_nonpos_right coefficients.2.2.2.1.le hc2
  have he := mul_le_mul_of_nonneg_right coefficients.2.2.2.2.le hs2
  have hS := HighOrderTaylor.sin_le_S13 hφ0
  have hC := HighOrderTaylor.C14_le_cos hφ0
  have hS2 := HighOrderTaylor.sin_le_S13 (show 0≤2*φ by linarith)
  have hC2 := HighOrderTaylor.cos_le_C12 (show 0≤2*φ by linarith)
  have hp := PositiveEarlyPolynomial.lower
    (show φ∈Icc (87/100:ℝ) (13/10) from
      ⟨by have h1 := hφ.1; dsimp only [lowerAngle] at h1; linarith [pi_hand_enclosure.1],hφ.2⟩)
  rw [polynomial_evaluation] at hp
  rw [harmonic]
  linarith [coefficients.1]

lemma curvature_lower {B φ : ℝ} (hB : B∈Icc (0:ℝ) (31/100)) (hφ : angles φ) : m≤FBB B φ := by
  have hcut : (31/100:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hBf : B∈Icc 0 outerDiagonal := ⟨hB.1,hB.2.trans hcut.2⟩
  have hm := FBB_antitone φ hBf hcut hB.2
  have ht := lower_trig (lower_mem hφ)
  have hd := (outer_ratio_bounds hcut).2.2.1
  have hp := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤g*ratioD (31/100) by dsimp [g,EdgeThreeAligned.gp]; linarith)
  dsimp only [FBB] at hm ⊢
  linarith [curvature_reference]

lemma initial_target {B φ : ℝ} (hB : B∈Icc (0:ℝ) (31/100)) (hφ : φ∈angles) : γ<F B φ := by
  have hcut : (31/100:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hdom {y : ℝ} (hy : y∈Icc (0:ℝ) (31/100)) : y∈Icc 0 outerDiagonal :=
    ⟨hy.1,hy.2.trans hcut.2⟩
  have ht := curvature_tangent (f := fun y => F y φ) (d := fun y => FB y φ)
    (dd := fun y => FBB y φ) (κ := m) hB
    (show r∈Icc (0:ℝ) (31/100) by norm_num [r])
    (fun y hy => F_hasDerivAt (hdom hy)) (fun y hy => FB_hasDerivAt (hdom hy))
    (fun y hy => curvature_lower hy hφ)
  have hh := scalar_lower hφ
  have hs := sq_nonneg (m*(B-r)+FB r φ)
  dsimp only [G,m] at *
  rw [show FB r φ^2/(2*(143/100:ℝ))=50/143*FB r φ^2 by ring] at hh
  linarith

lemma later_derivative {B φ : ℝ} (hB : B∈Icc (31/100:ℝ) outerDiagonal) (hφ : φ∈angles) :
    0<FB B φ := by
  have hcut : (31/100:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hterminal : Lower (13/10:ℝ) := ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],
    by linarith [pi_hand_enclosure.1]⟩
  have hl := FB_angle_antitone hcut (lower_mem hφ) hterminal hφ.2
  have hr := FB_angle_antitone hd (lower_mem hφ) hterminal hφ.2
  have hm := (FB_concave φ).min_le_of_mem_Icc hcut hd hB
  exact (lt_min (derivative_references.1.trans_le hl) (derivative_references.2.trans_le hr)).trans_le hm

lemma all_targets {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : φ∈angles) : γ<F B φ := by
  by_cases he : B≤31/100
  · exact initial_target ⟨hB.1,he⟩ hφ
  · have hdom {y : ℝ} (hy : y∈Icc (31/100:ℝ) outerDiagonal) : y∈Icc 0 outerDiagonal :=
      ⟨by linarith [hy.1],hy.2⟩
    have hm : MonotoneOn (fun y => F y φ) (Icc (31/100:ℝ) outerDiagonal) :=
      monoOn_of_hasDeriv_nonneg
        (fun y hy => (F_hasDerivAt (φ := φ) (hdom hy)).continuousAt.continuousWithinAt)
        (fun y hy => F_hasDerivAt (φ := φ) (hdom (Ioo_subset_Icc_self hy)))
        (fun y hy => (later_derivative (Ioo_subset_Icc_self hy) hφ).le)
    exact (initial_target (show (31/100:ℝ)∈Icc (0:ℝ) (31/100) by norm_num) hφ).trans_le
      (hm ⟨le_rfl,(Asymmetric.rational_outer_mem (by norm_num : (31/100:ℝ)∈Icc 0 (899/1000))).2⟩
        ⟨by linarith,hB.2⟩ (by linarith))

theorem original {b A B φ : ℝ} (ht : OuterState A B) (hφ : φ∈angles)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ) : γ<value b B φ :=
  (all_targets (NegativeTwo.source_mem ht) hφ).trans_le (PositiveSource.original_lower ht hsep)

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveSource.Early
end
end
end
