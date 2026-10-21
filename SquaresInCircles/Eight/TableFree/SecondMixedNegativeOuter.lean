module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeOuterCorner

/-!
# Every original owner for the negative outer to negative core family

The first two early owners are impossible at the actual core point.
The transverse owner uses the whole-circle support; the primary owner
uses the whole side support or the complete corner contact theorem.
The direct late estimate includes the complete upper quarter half.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedOuterNegative
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

lemma late_value {a b B φ : ℝ} (hs : OuterState a b) (hB : 0≤B)
    (hφ : (1409/1000:ℝ)≤φ) : γ<value b B φ := by
  have hT := T_upper (NegativeTwo.source_mem hs)
  have hg := mul_nonneg (show (0:ℝ)≤g by norm_num [g]) hB
  dsimp [value,c₀,γ]
  linarith

lemma late_corner_value {a b B φ : ℝ} (hs : OuterState a b) (hB : 1/2≤B)
    (hφ : (549/500:ℝ)≤φ) : γ<value b B φ := by
  have hT := T_upper (NegativeTwo.source_mem hs)
  have hg := mul_le_mul_of_nonneg_left hB (show (0:ℝ)≤g by norm_num [g])
  dsimp [value,c₀,g,γ] at *
  linarith

lemma transverse_original {a b B φ : ℝ} (hs : OuterState a b)
    (hφ : φ∈Icc lowerAngle (1409/1000))
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ+B) :
    γ<value b B φ := by
  have hT := MixedTEnvelope.upper (NegativeTwo.source_mem hs)
  have hsupp := outer_circle_lower (X := -g*Real.sin φ) (Y := g*Real.cos φ-q) hs
  have he : Real.sqrt ((-g*Real.sin φ)^2+(g*Real.cos φ-q)^2)=N φ := by
    dsimp [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination (g^2)*(Real.sin_sq_add_cos_sq φ)
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hcompare : transverse φ<value b B φ := by
    dsimp [transverse,value]
    nlinarith
  have hlow := transverse_lower hφ
  dsimp [γ]
  linarith

lemma side_original {a b B φ : ℝ} (hs : OuterState a b) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-(7/12)*Real.cos φ+B*Real.sin φ) :
    γ<value b B φ := by
  have ht := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [ht.1]
  have hT := mul_lt_mul_of_pos_right (MixedTEnvelope.upper (NegativeTwo.source_mem hs)) hsine
  have hsupp := outer_circle_lower (X := -g) (Y := -q*Real.sin φ) hs
  have he : Real.sqrt ((-g)^2+(-q*Real.sin φ)^2)=Real.sqrt (g^2+q^2*(Real.sin φ)^2) := by
    congr 1
    ring
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hside := side_positive (lower_deviation hφ)
  have heq : side (Real.pi/2-φ)=
      (φ+c₀-k+(g+q)/2-γ)*Real.sin φ+g*(1+(13/12)*Real.cos φ)-
        radius*Real.sqrt (g^2+q^2*(Real.sin φ)^2) := by
    simp only [side,sideK,sideN,Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,
      Real.cos_pi_div_two,zero_mul,one_mul,zero_sub,sub_zero,neg_neg]
    ring
  rw [heq] at hside
  have hpositive : 0<(value b B φ-γ)*Real.sin φ := by
    dsimp [value]
    nlinarith
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg (show value b B φ-γ≤0 by linarith) hsine.le
  linarith

lemma corner_original {a b A B φ : ℝ} (hs : OuterState a b)
    (hB : 1/2≤B) (hBA : B≤A) (hc : (A-1/2)^2+(B-1/2)^2=(1/12:ℝ)^2)
    (hφ : φ∈earlyAngles)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ) :
    γ<value b B φ := by
  obtain ⟨hdom,hA⟩ := MixedCorner.actual hB hBA hc
  have hcut : contactPrimary B φ≤a := by
    dsimp [contactPrimary]
    rw [←hA]
    nlinarith
  have hm := NegativeThree.primary_monotone
    (primaryRange_subset (contact_range hdom hφ)) (NegativeTwo.primary_mem hs) hcut
  rw [NegativeThree.primary_actual hs] at hm
  have hh := corner_lower hdom hφ
  dsimp [cornerCost,value,γ] at *
  linarith

theorem original {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    γ<value b B φ := by
  have hcore := CoreAngleEndpoint.state_bounds ht
  by_cases hlate : (1409/1000:ℝ)≤φ
  · exact late_value hs hcore.2.2.1 hlate
  have hlow : Lower φ :=
    ⟨by dsimp [lowerAngle]; linarith [(abs_le.mp hφ).1],
      by linarith [pi_hand_enclosure.1]⟩
  have htr := lower_trig hlow
  have hsine : 0≤Real.sin φ := by linarith [htr.1]
  have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
  fin_cases j
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ+B*Real.cos φ := by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    have he : (A*Real.sin φ+B*Real.cos φ)^2+
        (A*Real.cos φ-B*Real.sin φ)^2=A^2+B^2 := by
      linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
    have hlarge : 1≤A*Real.sin φ+B*Real.cos φ := by linarith [hs.1]
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlarge 2
    have hrad := core_radius_sq ht
    nlinarith [sq_nonneg (A*Real.cos φ-B*Real.sin φ)]
  · have hac := mul_nonneg (show 0≤a by linarith [hs.1,hs.2.1]) htr.2.2.1
    have hbs := mul_nonneg hs.1 hsine
    norm_num [Eight.forwardMargin,lower_width hlow] at hm
    nlinarith [hcore.2.1]
  · apply transverse_original hs ⟨hlow.1,by linarith⟩
    norm_num [Eight.forwardMargin,lower_width hlow] at hm
    linarith
  · have hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ+B*Real.sin φ := by
      norm_num [Eight.forwardMargin,lower_width hlow] at hm
      linarith
    rcases ht with ⟨rfl,hB,hBu⟩ | ⟨hB,hBA,hcircle⟩
    · exact side_original hs hlow hsep
    · by_cases hlate' : (549/500:ℝ)≤φ
      · exact late_corner_value hs hB hlate'
      · exact corner_original hs hB hBA hcircle ⟨hlow.1,by linarith⟩ hsep

theorem literal {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    SecondWord.threshold 3<cost 3 .outer kind false false a b A B φ := by
  rw [threshold_value,MixedThree.outer_core_negative_negative hk hs]
  have hh := original hs ht hφ j hm
  simpa [γ,value,g,c₀] using hh

end SquaresInCircles.Eight.TableFree.SecondWord.MixedOuterNegative
