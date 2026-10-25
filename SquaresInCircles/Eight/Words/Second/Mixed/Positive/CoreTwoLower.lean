module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreTwoScalars

/-!
# Eight squares: lower owners for negative outer to positive core

The low-source regimes use the two supports on the whole angle interval. In each high-source
regime a relaxed contact cost decreases all the way to alignment at the same original outer point
(`secondaryContact_antitone`, `primaryContact_antitone`). The two owners are `lower_secondary`
and `lower_primary`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower lower_trig lower_width lower_deviation)

def secondaryCut (a b φ : ℝ) : ℝ :=
  (a-1/2)*Real.sin φ-(b+1/2)*Real.cos φ-1/2
def secondaryCutD (a b φ : ℝ) : ℝ :=
  (a-1/2)*Real.cos φ+(b+1/2)*Real.sin φ
def secondaryContact (a b φ : ℝ) : ℝ := φ+e-P b-g*secondaryCut a b φ
def primaryCut (a φ : ℝ) : ℝ :=
  ((a-1/2)-(13/12)*Real.cos φ)/Real.sin φ-1/2
def primaryCutD (a φ : ℝ) : ℝ :=
  (13/12-(a-1/2)*Real.cos φ)/(Real.sin φ)^2
def primaryContact (a b φ : ℝ) : ℝ := φ+e-P b-g*primaryCut a φ

lemma harmonic_reserve {φ : ℝ} (hφ : Lower φ) :
    1≤Real.sin φ+Real.cos φ/2 := by
  have ht := lower_trig hφ
  have hp := mul_nonneg ht.2.2.1
    (show 0≤1-(5/4)*Real.cos φ by linarith [ht.2.2.2.1])
  by_contra hn
  have hs := mul_pos (show 0<1-Real.sin φ-Real.cos φ/2 by linarith)
    (show 0<1+Real.sin φ-Real.cos φ/2 by linarith [ht.1,ht.2.2.2.1])
  nlinarith [Real.sin_sq_add_cos_sq φ]

lemma secondaryCut_hasDerivAt (a b φ : ℝ) :
    HasDerivAt (secondaryCut a b) (secondaryCutD a b φ) φ := by
  convert (((Real.hasDerivAt_sin φ).const_mul (a-1/2)).sub
    ((Real.hasDerivAt_cos φ).const_mul (b+1/2))).sub_const (1/2) using 1
  · funext x
    simp only [secondaryCut,Pi.sub_apply]
  · dsimp [secondaryCutD]
    ring

lemma secondaryContact_hasDerivAt (a b φ : ℝ) :
    HasDerivAt (secondaryContact a b) (1-g*secondaryCutD a b φ) φ := by
  convert (((hasDerivAt_id φ).add_const e).sub_const (P b)).sub
    ((secondaryCut_hasDerivAt a b φ).const_mul g) using 1
  funext x
  simp only [secondaryContact,Pi.sub_apply,id]

lemma secondaryContact_antitone {a b : ℝ} (ha : 1≤a) (hb : 1/2≤b) :
    AntitoneOn (secondaryContact a b) (Icc lowerAngle (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ _ => (secondaryContact_hasDerivAt a b φ).continuousAt.continuousWithinAt)
    (fun φ _ => secondaryContact_hasDerivAt a b φ)
  intro φ hφ
  have ht := lower_trig (Ioo_subset_Icc_self hφ)
  have hac := mul_nonneg (show 0≤a-1 by linarith) ht.2.2.1
  have hbs := mul_nonneg (show 0≤b-1/2 by linarith) (by linarith [ht.1] : 0≤Real.sin φ)
  have hd : 1≤ secondaryCutD a b φ := by
    dsimp [secondaryCutD]
    nlinarith [harmonic_reserve (Ioo_subset_Icc_self hφ)]
  have hh := mul_le_mul_of_nonneg_left hd (show 0≤g by norm_num [g])
  norm_num [g] at *
  linarith

lemma primaryCut_hasDerivAt (a : ℝ) {φ : ℝ} (hφ : Lower φ) :
    HasDerivAt (primaryCut a) (primaryCutD a φ) φ := by
  have hs : Real.sin φ≠0 := ne_of_gt (by linarith [(lower_trig hφ).1])
  convert ((((Real.hasDerivAt_cos φ).const_mul (13/12)).const_sub (a-1/2)).div
    (Real.hasDerivAt_sin φ) hs).sub_const (1/2) using 1
  · rfl
  · dsimp [primaryCutD]
    field_simp [hs]
    nlinarith [Real.sin_sq_add_cos_sq φ]

lemma primaryContact_hasDerivAt (a b : ℝ) {φ : ℝ} (hφ : Lower φ) :
    HasDerivAt (primaryContact a b) (1-g*primaryCutD a φ) φ := by
  convert (((hasDerivAt_id φ).add_const e).sub_const (P b)).sub
    ((primaryCut_hasDerivAt a hφ).const_mul g) using 1
  funext x
  simp only [primaryContact,Pi.sub_apply,id]

lemma primaryContact_antitone {a b : ℝ} (ha : a≤537/500) :
    AntitoneOn (primaryContact a b) (Icc lowerAngle (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun φ hφ => (primaryContact_hasDerivAt a b hφ).continuousAt.continuousWithinAt)
    (fun φ hφ => primaryContact_hasDerivAt a b (Ioo_subset_Icc_self hφ))
  intro φ hφ
  have ht := lower_trig (Ioo_subset_Icc_self hφ)
  have hsine : 0<Real.sin φ := by linarith [ht.1]
  have hm := mul_le_mul_of_nonneg_right
    (show a-1/2≤287/500 by linarith) ht.2.2.1
  have hpaid := mul_le_mul_of_nonneg_left hm (show 0≤g by norm_num [g])
  have hnum : (Real.sin φ)^2<g*(13/12-(a-1/2)*Real.cos φ) := by
    have hh := sq_nonneg (Real.cos φ-g*(287/500)/2)
    dsimp [g] at *
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have he : g*primaryCutD a φ=
      g*(13/12-(a-1/2)*Real.cos φ)/(Real.sin φ)^2 := by dsimp [primaryCutD]; ring
  have hd : 1<g*primaryCutD a φ := by
    rw [he]
    exact (one_lt_div (sq_pos_of_pos hsine)).2 hnum
  linarith

theorem lower_secondary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a*Real.sin φ-b*Real.cos φ-B) :
    γ<value b B φ := by
  by_cases hb : b≤1/2
  · have hP := P_half_chord ⟨hs.1,hb⟩
    have hsupp := outer_circle_lower (X := -g*Real.sin φ) (Y := g*Real.cos φ-q) hs
    have he : Real.sqrt ((-g*Real.sin φ)^2+(g*Real.cos φ-q)^2)=
        MixedTransverseSupport.lowerN g q φ := by
      dsimp [MixedTransverseSupport.lowerN,CircularNorm.norm,CircularNorm.energy]
      congr 1
      linear_combination g^2*(Real.sin_sq_add_cos_sq φ)
    rw [he] at hsupp
    have hmargin := mul_le_mul_of_nonneg_left hsep (show 0≤g by norm_num [g])
    have hh := transverse_lower hφ
    dsimp [transverse,MixedTransverseSupport.lower,value,q,c,e,γ] at *
    nlinarith
  · have htr := lower_trig hφ
    have hwidth : (1:ℝ)≤(1+Real.sin φ+Real.cos φ)/2 := by linarith [htr.2.2.2.2]
    have hbcos := mul_nonneg hs.1 htr.2.2.1
    have haSin := mul_le_mul_of_nonneg_left (Real.sin_le_one φ)
      (show 0≤a by linarith [hs.1,hs.2.1])
    have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
    have ha : 1≤a := by linarith
    have hcut : B ≤ secondaryCut a b φ := by dsimp only [secondaryCut]; linarith
    have hweight := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    have hm := secondaryContact_antitone ha (show 1/2≤b by linarith)
      hφ (show Lower (Real.pi/2) from ⟨by dsimp [lowerAngle]; linarith,le_rfl⟩) hφ.2
    have he : secondaryContact a b (Real.pi/2)=aligned a b := by
      simp only [secondaryContact,secondaryCut,aligned,Real.sin_pi_div_two,Real.cos_pi_div_two]
      ring
    rw [he] at hm
    have hh := aligned_lower hs ha
    dsimp only [secondaryContact,value,γ] at hm ⊢
    linarith

theorem lower_primary {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤a-A*Real.cos φ-B*Real.sin φ) :
    γ<value b B φ := by
  have htr := lower_trig hφ
  have hsine : 0<Real.sin φ := by linarith [htr.1]
  have hA : A=(7/12:ℝ) := by
    rcases ht with ⟨rfl,_,_⟩ | ⟨hB,hBA,_⟩
    · rfl
    · have hAc := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤A by linarith) htr.2.2.1
      have hBs := mul_le_mul_of_nonneg_right hB hsine.le
      have ha := (NegativeTwo.primary_mem hs).2.trans_lt outer_endpoint_bounds.2.1
      exfalso
      linarith [htr.2.2.2.2]
  rw [hA] at hsep
  by_cases hb : b≤7/10
  · have hP := mul_le_mul_of_nonneg_right (P_seven_chord ⟨hs.1,hb⟩) hsine.le
    have hsupp := outer_circle_lower (X := -g) (Y := -p*Real.sin φ) hs
    have he : Real.sqrt ((-g)^2+(-p*Real.sin φ)^2)=Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by
      congr 1
      ring
    rw [he] at hsupp
    have hmargin := mul_le_mul_of_nonneg_left hsep (show 0≤g by norm_num [g])
    have hpos := primary_positive (lower_deviation hφ)
    have heq : MixedPrimarySupport.minus g p K (Real.pi/2-φ)=
        (φ-c+(g+p)/2-γ)*Real.sin φ+g*(1+(13/12)*Real.cos φ)-
          CommonQuarter.radius*Real.sqrt (g^2+p^2*(Real.sin φ)^2) := by
      simp only [MixedPrimarySupport.minus,MixedPrimarySupport.N,K,
        Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,Real.cos_pi_div_two,
        zero_mul,one_mul,sub_zero,zero_add]
      ring
    rw [heq] at hpos
    have hpositive : 0<(value b B φ-γ)*Real.sin φ := by
      dsimp only [value,c,e,p] at hP hpos hsupp ⊢
      linarith
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (show value b B φ-γ≤0 by linarith) hsine.le
    linarith
  · have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
    have hBc := mul_nonneg hB hsine.le
    have ha : 1≤a := by linarith [htr.2.2.1,htr.2.2.2.2]
    have hb2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤6/5)
      (show 6/5≤b+1/2 by linarith) 2
    have haHi : a≤537/500 := by
      have hc := hs.2.2
      norm_num [Q0] at hc
      by_contra hn
      have hsq := mul_lt_mul'' (lt_of_not_ge hn) (lt_of_not_ge hn) (by norm_num) (by norm_num)
      linarith
    have hcutEq : primaryCut a φ*Real.sin φ=
        a-1/2-(13/12)*Real.cos φ-Real.sin φ/2 := by
      dsimp [primaryCut]
      field_simp [hsine.ne']
    have hcut : B≤primaryCut a φ := by
      apply (mul_le_mul_iff_left₀ hsine).mp
      linarith
    have hweight := mul_le_mul_of_nonneg_left hcut (show 0≤g by norm_num [g])
    have hm := primaryContact_antitone (b := b) haHi hφ
      (show Lower (Real.pi/2) from ⟨by dsimp [lowerAngle]; linarith,le_rfl⟩) hφ.2
    have he : primaryContact a b (Real.pi/2)=aligned a b := by
      simp only [primaryContact,primaryCut,aligned,Real.sin_pi_div_two,Real.cos_pi_div_two]
      ring
    rw [he] at hm
    have hh := aligned_lower hs ha
    dsimp only [primaryContact,value,γ] at hm ⊢
    linarith

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveCore
