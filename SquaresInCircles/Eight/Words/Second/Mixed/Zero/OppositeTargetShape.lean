module

public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetLabelReferences

/-!
# Eight squares: whole-interval label shapes in the negative target proof

The shapes of the labels on the whole interval: the derivative bounds of J on the band
(`J_second_upper`, `J_first_bounds`), the chord of the third derivative of P (`P_third_chord`)
and the logarithmic-derivative inequality of L (`logarithmic_derivative`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.Shape
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratioD ratioDD)

def band : Set ℝ := Icc (diagonal 0) (9/10)

lemma band_domain {B : ℝ} (hB : B∈band) : B∈Labels.domain :=
  ⟨by linarith [hB.1,(diagonal_bounds (show (0:ℝ)∈angles by norm_num [angles,cap])).1],hB.2⟩

lemma diagonal_band {x : ℝ} (hx : x∈angles) : diagonal x∈band :=
  ⟨diagonal_monotone (by norm_num) (angle_subset hx) hx.1,(diagonal_bounds hx).2.le⟩

lemma J_third_negative {B : ℝ} (hB : B∈band) : JLabel.d3 B<0 := by
  have hb := (diagonal_bounds (show (0:ℝ)∈angles by norm_num [angles,cap])).1
  have hr := Labels.ratio_signs (band_domain hB)
  have hp : 0< -(13/50000:ℝ)+(17627/100000)*B := by linarith [hB.1]
  have hm := mul_pos hp hr.2.2.1
  norm_num [RoleLabel.d3,JLabel]
  nlinarith [hr.2.1]

lemma J_second_antitone : AntitoneOn JLabel.d2 band :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (JLabel.d2_hasDerivAt (Labels.chart_domain (band_domain hB))).continuousAt.continuousWithinAt)
    (fun B hB => JLabel.d2_hasDerivAt (Labels.chart_domain (band_domain (Ioo_subset_Icc_self hB))))
    (fun B hB => (J_third_negative (Ioo_subset_Icc_self hB)).le)

lemma J_second_upper {B : ℝ} (hB : B∈band) : JLabel.d2 B< -(97/200:ℝ) := by
  have hz : diagonal 0∈band := ⟨le_rfl,(diagonal_bounds (by norm_num [angles,cap])).2.le⟩
  exact (J_second_antitone hz hB hB.1).trans_lt LabelReferences.initial.2.2.1

lemma J_first_antitone : AntitoneOn JLabel.d1 band :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (JLabel.d1_hasDerivAt (Labels.chart_domain (band_domain hB))).continuousAt.continuousWithinAt)
    (fun B hB => JLabel.d1_hasDerivAt (Labels.chart_domain (band_domain (Ioo_subset_Icc_self hB))))
    (fun B hB => by linarith [J_second_upper (Ioo_subset_Icc_self hB)])

lemma J_first_bounds {B : ℝ} (hB : B∈band) : (3/5:ℝ)<JLabel.d1 B ∧ JLabel.d1 B<181/200 := by
  have hz : diagonal 0∈band := ⟨le_rfl,(diagonal_bounds (by norm_num [angles,cap])).2.le⟩
  have hu : (9/10:ℝ)∈band := ⟨hz.2,le_rfl⟩
  exact ⟨LabelReferences.nine.2.1.trans_le (J_first_antitone hB hu hB.2),
    (J_first_antitone hz hB hB.1).trans_lt LabelReferences.initial.2.1⟩

lemma P_third_chord {B : ℝ} (hB : B∈Icc (1/2:ℝ) (9/10)) :
    PLabel.d3 B<153/500+(297/250)*(B-1/2) := by
  have hd {t : ℝ} (ht : t∈Icc (1/2:ℝ) (9/10)) : t∈Labels.domain :=
    ⟨by linarith [ht.1],ht.2⟩
  have hc : ConcaveOn ℝ (Icc (1/2:ℝ) (9/10))
      (fun t => 153/500+(297/250)*(t-1/2)-PLabel.d3 t) :=
    concave_of_deriv2 (f' := fun t => 297/250-PLabel.d4 t) (f'' := fun t => -PLabel.d5 t)
      (fun t ht => (((((hasDerivAt_id' (x:=t)).sub_const (1/2)).const_mul (297/250)).const_add
        (153/500)).fun_sub (PLabel.d3_hasDerivAt (Labels.chart_domain (hd ht)))).congr_deriv
          (by ring))
      (fun t ht => (PLabel.d4_hasDerivAt (Labels.chart_domain (hd ht))).const_sub (297/250))
      (fun t ht => neg_nonpos.mpr (Labels.P_fifth_positive (hd ht)).le)
  have hh := concave_gt_of_endpoints (c:=0) hc hB
    (show 0<(153/500:ℝ)+(297/250)*((1/2:ℝ)-1/2)-PLabel.d3 (1/2) by
      linarith [LabelReferences.P_half.2.2.2])
    (show 0<(153/500:ℝ)+(297/250)*((9/10:ℝ)-1/2)-PLabel.d3 (9/10) by
      linarith [LabelReferences.nine.1])
  linarith

lemma L_first_positive {B : ℝ} (hB : B∈Labels.domain) : (3/5:ℝ)<LLabel.d1 B := by
  have hh := curvature_tangent (κ := (0:ℝ)) hB
    (show (1/2:ℝ)∈Labels.domain by norm_num [Labels.domain])
    (fun t ht => LLabel.d1_hasDerivAt (Labels.chart_domain ht))
    (fun t ht => LLabel.d2_hasDerivAt (Labels.chart_domain ht))
    (fun t ht => (Labels.L_third_positive ht).le)
  have hval := L_first_lower_strong
    (show (1/2:ℝ)∈Icc 0 outerDiagonal from Asymmetric.rational_outer_mem (by norm_num))
  have hs := L_half_second
  have hp : -(8/625:ℝ)≤LLabel.d2 (1/2)*(B-1/2) := by
    by_cases ht : 1/2≤B
    · have h1 := mul_le_mul_of_nonneg_right hs.1.le (sub_nonneg.mpr ht)
      have h2 := mul_le_mul_of_nonpos_left (show B-1/2≤(2/5:ℝ) by linarith [hB.2])
        (by norm_num : (-4/125:ℝ)≤0)
      nlinarith
    · have hm := mul_nonneg_of_nonpos_of_nonpos hs.2.le (by linarith : B-1/2≤0)
      linarith
  nlinarith

def lam : ℝ := 144/13
def D (B : ℝ) : ℝ := lam*(B-1/2)*LLabel.d1 B-LLabel.d2 B
def D₁ (B : ℝ) : ℝ := lam*LLabel.d1 B+lam*(B-1/2)*LLabel.d2 B-LLabel.d3 B
def D₂ (B : ℝ) : ℝ := 2*lam*LLabel.d2 B+lam*(B-1/2)*LLabel.d3 B-LLabel.d4 B
def D₃ (B : ℝ) : ℝ := 3*lam*LLabel.d3 B+lam*(B-1/2)*LLabel.d4 B-LLabel.d5 B

lemma D_hasDerivAt {B : ℝ} (hB : B∈Labels.domain) : HasDerivAt D (D₁ B) B := by
  have hb := Labels.chart_domain hB
  have h : HasDerivAt D _ B :=
    ((((hasDerivAt_id' (x:=B)).sub_const (1/2)).const_mul lam).fun_mul
      (LLabel.d1_hasDerivAt hb)).fun_sub (LLabel.d2_hasDerivAt hb)
  exact h.congr_deriv (by simp only [D₁]; ring)

lemma D₁_hasDerivAt {B : ℝ} (hB : B∈Labels.domain) : HasDerivAt D₁ (D₂ B) B := by
  have hb := Labels.chart_domain hB
  have h : HasDerivAt D₁ _ B :=
    (((LLabel.d1_hasDerivAt hb).const_mul lam).fun_add
      ((((hasDerivAt_id' (x:=B)).sub_const (1/2)).const_mul lam).fun_mul
        (LLabel.d2_hasDerivAt hb))).fun_sub (LLabel.d3_hasDerivAt hb)
  exact h.congr_deriv (by simp only [D₂]; ring)

lemma D₂_hasDerivAt {B : ℝ} (hB : B∈Labels.domain) : HasDerivAt D₂ (D₃ B) B := by
  have hb := Labels.chart_domain hB
  have h : HasDerivAt D₂ _ B :=
    (((LLabel.d2_hasDerivAt hb).const_mul (2*lam)).fun_add
      ((((hasDerivAt_id' (x:=B)).sub_const (1/2)).const_mul lam).fun_mul
        (LLabel.d3_hasDerivAt hb))).fun_sub (LLabel.d4_hasDerivAt hb)
  exact h.congr_deriv (by simp only [D₃]; ring)

lemma D_third_lower {B : ℝ} (hB : B∈Icc (1/2:ℝ) (9/10)) : 60<D₃ B := by
  have hd : B∈Labels.domain := ⟨by linarith [hB.1],hB.2⟩
  have h3 := LabelReferences.L_half.1.trans_le (Labels.L_third_monotone
    (by norm_num [Labels.domain]) hd hB.1)
  have hp := mul_nonneg (sub_nonneg.mpr hB.1) (Labels.L_fourth_positive hd).le
  have h5 := Labels.L_fifth_upper hd
  dsimp [D₃,lam]
  nlinarith

lemma D_first_lower {B : ℝ} (hB : B∈Icc (1/2:ℝ) (9/10)) : (201/200:ℝ)<D₁ B := by
  have hd {t : ℝ} (ht : t∈Icc (1/2:ℝ) (9/10)) : t∈Labels.domain :=
    ⟨by linarith [ht.1],ht.2⟩
  have hh := curvature_tangent (κ := (60:ℝ)) (t := 1/2) hB (by norm_num)
    (fun t ht => D₁_hasDerivAt (hd ht))
    (fun t ht => D₂_hasDerivAt (hd ht)) (fun t ht => (D_third_lower ht).le)
  have e1 : D₁ (1/2)=(144/13)*LLabel.d1 (1/2)-LLabel.d3 (1/2) := by
    simp only [D₁,lam]; ring
  have e2 : D₂ (1/2)=(288/13)*LLabel.d2 (1/2)-LLabel.d4 (1/2) := by
    simp only [D₂,lam]; ring
  have h1 : (42/25:ℝ)<D₁ (1/2) := by
    rw [e1]; exact LabelReferences.L_half.2.2.2.1
  have h2 : |D₂ (1/2)|<9 := by rw [e2]; exact LabelReferences.L_half.2.2.2.2
  have hp := mul_nonneg (show 0≤D₂ (1/2)+9 by linarith [(abs_lt.mp h2).1])
    (sub_nonneg.mpr hB.1)
  nlinarith [sq_nonneg (B-1/2-3/20)]

lemma logarithmic_derivative {B : ℝ} (hB : B∈Icc (1/2:ℝ) (9/10)) :
    LLabel.d2 B<(144/13)*(B-1/2)*LLabel.d1 B := by
  have hd {t : ℝ} (ht : t∈Icc (1/2:ℝ) (9/10)) : t∈Labels.domain :=
    ⟨by linarith [ht.1],ht.2⟩
  have hm : MonotoneOn D (Icc (1/2:ℝ) (9/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (D_hasDerivAt (hd ht)).continuousAt.continuousWithinAt)
      (fun t ht => D_hasDerivAt (hd (Ioo_subset_Icc_self ht)))
      (fun t ht => by linarith [D_first_lower (Ioo_subset_Icc_self ht)])
  have hz : 0<D (1/2) := by
    dsimp [D]
    linarith [LabelReferences.L_half.2.1]
  have hh := hz.trans_le (hm (by norm_num) hB hB.1)
  dsimp [D,lam] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.Shape
