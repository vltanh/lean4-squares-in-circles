module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveOuterTwoPrimary
public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveOuterTwoTransverse
public import SquaresInCircles.Eight.TableFree.SecondOuterPositiveThreeLowerFourth

/-!
# Original weak-owner joins for negative core to positive outer

The separator multiplier in the early transverse case is paid for by
the nonnegative original core coordinate.  The primary case retains
the actual core side or corner; the lower corner is geometrically
impossible.  No point or radius is changed.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

lemma core_transverse_upper {a b : ℝ} (hs : CoreState a b) : b<(559/1000:ℝ) :=
  (CoreAngleEndpoint.state_bounds hs).2.2.2.2.trans_lt
    (by linarith [CoreAngleEndpoint.diagonal_bounds.2])

lemma first_angle_lower {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ-B*Real.cos φ) :
    (1:ℝ)<φ := by
  by_contra hn
  have htr := lower_trig hφ
  have href : Lower (1:ℝ) :=
    ⟨by dsimp [lowerAngle]; linarith [pi_hand_enclosure.2],by linarith [pi_hand_enclosure.1]⟩
  have htaylor := PointProducts.trig (show (0:ℝ)≤1 by norm_num)
  norm_num [sin11,sin9,sin7,cos10,cos8,cos12] at htaylor
  have hsin : Real.sin φ<(1683/2000:ℝ) :=
    (PositiveThree.lower_sin_monotone hφ href (le_of_not_gt hn)).trans_lt
      (by linarith [htaylor.1.2])
  have hcos : (5403/10000:ℝ)<Real.cos φ :=
    (show (5403/10000:ℝ)<Real.cos 1 by linarith [htaylor.2.1]).trans_le
      (PositiveThree.lower_cos_antitone hφ href (le_of_not_gt hn))
  have hA := mul_le_mul_of_nonneg_right (NegativeTwo.primary_mem ht).2
    (by linarith [htr.1] : 0≤Real.sin φ)
  have hB := mul_nonneg ht.1 htr.2.2.1
  have hκ := (mul_lt_mul_of_pos_right MixedAffine.κ_bounds.2
    (by linarith [htr.1] : 0<Real.sin φ)).trans
      (mul_lt_mul_of_pos_left hsin (by norm_num : (0:ℝ)<183/200))
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  dsimp [MixedAffine.κ] at hκ
  nlinarith

lemma first_support {a b A B φ λ q η : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hλ : 0≤λ) (hgλ : g≤λ) (henv : V B≤η+q*B)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ-B*Real.cos φ) :
    MixedTransverseSupport.lower λ q (-c-η) φ≤value b B φ := by
  have hsupp := outer_circle_lower (X := -λ*Real.sin φ) (Y := λ*Real.cos φ-q) ht
  have he : Real.sqrt ((-λ*Real.sin φ)^2+(λ*Real.cos φ-q)^2)=
      MixedTransverseSupport.lowerN λ q φ := by
    dsimp [MixedTransverseSupport.lowerN,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination λ^2*(Real.sin_sq_add_cos_sq φ)
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep hλ
  have hpaid := mul_nonneg (sub_nonneg.mpr hgλ) (CoreAngleEndpoint.state_bounds hs).2.2.1
  dsimp [MixedTransverseSupport.lower,value]
  nlinarith

theorem lower_first {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -b+A*Real.sin φ-B*Real.cos φ) :
    γ<value b B φ := by
  by_cases hearly : φ≤6/5
  · have hh := first_support hs ht (λ := (7/5:ℝ)) (q := (1061/1000:ℝ))
      (η := (-1449/100000:ℝ)) (by norm_num) (by norm_num [g])
      (zero_tangent_upper (NegativeTwo.source_mem ht)) hsep
    have hl := early_lower ⟨(first_angle_lower hs ht hφ hsep).le,hearly⟩
    change early φ≤value b B φ at hh
    norm_num [γ]
    linarith
  · have hh := first_support hs ht (λ := g) (q := p) (η := k)
      (by norm_num [g]) le_rfl (tangent_upper (NegativeTwo.source_mem ht)) hsep
    exact (late_lower ⟨by linarith,hφ.2⟩).trans_le hh

theorem lower_primary {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤ -a*Real.cos φ-b*Real.sin φ+A) :
    γ<value b B φ := by
  have htr := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [htr.1]
  have ha : a=(7/12:ℝ) := by
    rcases hs with ⟨rfl,_,_⟩ | ⟨hb,hba,_⟩
    · rfl
    · have hac := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤a by linarith) htr.2.2.1
      have hbs := mul_le_mul_of_nonneg_right hb hsine.le
      have hA := (NegativeTwo.primary_mem ht).2
      have ha0 := outer_endpoint_bounds.2.1
      nlinarith [htr.2.2.2.2]
  rw [ha] at hsep
  have hV := mul_le_mul_of_nonneg_right (tangent_upper (NegativeTwo.source_mem ht)) hsine.le
  have hsupp := outer_circle_lower (X := -g) (Y := -p*Real.sin φ) ht
  have he : Real.sqrt ((-g)^2+(-p*Real.sin φ)^2)=
      Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by congr 1; ring
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hpos := lower_primary_positive (lower_deviation hφ)
  have heq : MixedPrimarySupport.minus g p K (Real.pi/2-φ)=
      (φ-c-k+(g+p)/2-γ)*Real.sin φ+g*(1+(13/12)*Real.cos φ)-
        radius*Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by
    simp only [MixedPrimarySupport.minus,MixedPrimarySupport.N,K,
      Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
      zero_mul,one_mul,zero_sub,sub_zero,neg_neg]
    ring
  rw [heq] at hpos
  have hpositive : 0<(value b B φ-γ)*Real.sin φ := by
    dsimp [value]
    nlinarith
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg (show value b B φ-γ≤0 by linarith) hsine.le
  linarith

theorem upper_first {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤ -b+A*Real.cos x+B*Real.sin x) :
    γ<value b B (Real.pi/2+x) := by
  have hV := tangent_upper (NegativeTwo.source_mem ht)
  have hsupp := outer_circle_lower (X := -g*Real.cos x) (Y := -g*Real.sin x-p) ht
  have he : Real.sqrt ((-g*Real.cos x)^2+(-g*Real.sin x-p)^2)=
      MixedTransverseSupport.upperN g p x := by
    dsimp [MixedTransverseSupport.upperN,CircularNorm.norm,CircularNorm.energy]
    congr 1
    linear_combination g^2*(Real.sin_sq_add_cos_sq x)
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hh := upper_lower hx
  dsimp [upperTransverse,MixedTransverseSupport.upper,value] at *
  nlinarith

theorem upper_primary {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a*Real.sin x-b*Real.cos x+A) :
    γ<value b B (Real.pi/2+x) := by
  have htr := positive_trig hx
  have hcos : 0<Real.cos x := by linarith [htr.1]
  have ha := mul_le_mul_of_nonneg_right (CoreAngleEndpoint.state_bounds hs).2.1 htr.2.2.1
  have hV := mul_le_mul_of_nonneg_right (tangent_upper (NegativeTwo.source_mem ht)) hcos.le
  have hsupp := outer_circle_lower (X := -g) (Y := -p*Real.cos x) ht
  have he : Real.sqrt ((-g)^2+(-p*Real.cos x)^2)=MixedPrimarySupport.N g p x := by
    dsimp [MixedPrimarySupport.N]
    congr 1
    ring
  rw [he] at hsupp
  have hmargin := mul_le_mul_of_nonneg_left hsep (show (0:ℝ)≤g by norm_num [g])
  have hcore := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤g by norm_num [g])
  have hpos := upper_primary_positive hx
  have hpositive : 0<(value b B (Real.pi/2+x)-γ)*Real.cos x := by
    dsimp [MixedPrimarySupport.plus,K,value] at *
    nlinarith
  by_contra hn
  have hh := mul_nonpos_of_nonpos_of_nonneg
    (show value b B (Real.pi/2+x)-γ≤0 by linarith) hcos.le
  linarith

lemma late_value {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : (213/100:ℝ)≤φ) : γ<value b B φ := by
  have hV := (V_monotone (NegativeTwo.source_mem ht)
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)
    (NegativeTwo.source_mem ht).2).trans_lt V_diagonal_bounds.2
  have hb := core_transverse_upper hs
  dsimp [value,c,g,γ]
  linarith

theorem upper_fourth {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (7/10))
    (hsep : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x-B*Real.cos x) :
    γ<value b B (Real.pi/2+x) := by
  by_cases hlate : (213/100:ℝ)≤Real.pi/2+x
  · exact late_value hs ht hlate
  have htr := positive_trig hx
  have ha := (CoreAngleEndpoint.state_bounds hs).2.1
  have hA : A<(283/200:ℝ) := (NegativeTwo.primary_mem ht).2.trans_lt outer_endpoint_bounds.2.1
  have hAs := mul_le_mul_of_nonneg_right hA.le htr.2.2.1
  have hBc := mul_nonneg ht.1 (by linarith [htr.1] : 0≤Real.cos x)
  have hxlo : (2/5:ℝ)<x := by
    by_contra hn
    have hsin : Real.sin x≤(2/5:ℝ) := htr.2.2.2.2.1.trans (le_of_not_gt hn)
    have hs2 := pow_le_pow_left₀ htr.2.2.1 hsin 2
    have hcos : (229/250:ℝ)<Real.cos x := by
      nlinarith [Real.sin_sq_add_cos_sq x,htr.1]
    nlinarith
  have hxhi : x<(14/25:ℝ) := by linarith [pi_hand_enclosure.1]
  have hsin : Real.sin x≤(14/25:ℝ) := htr.2.2.2.2.1.trans hxhi.le
  have hs2 := pow_le_pow_left₀ htr.2.2.1 hsin 2
  have hcos : (207/250:ℝ)<Real.cos x := by
    nlinarith [Real.sin_sq_add_cos_sq x,htr.1]
  have hB : B<(23/100:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hcos.le ht.1
    nlinarith
  have hV := zero_tangent_upper (NegativeTwo.source_mem ht)
  have hb := core_transverse_upper hs
  dsimp [value,c,g,γ]
  linarith [pi_hand_enclosure.1]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveOuter
