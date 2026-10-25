module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroAlignedPJ

/-!
# Both asymmetric negative-angle orders

Uncompiled source draft of Sections 8--9.  The P order increases to
alignment.  The J order is concave up to the source diagonal; the
explicit diagonal circle has concave target coordinate, so its inverse
chord is bounded by .702 times the target displacement.  The original
P slope .773 pays that displacement.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.NegativePJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma halfsixteen_exit : outerDiagonal< minus outerDiagonal (14/25) := by
  have hs := sin_lower_seven (show (0:ℝ)≤14/25 by norm_num)
  have hc := cos_le_cos8 (show (0:ℝ)≤14/25 by norm_num)
  have ht := positive_trig (show (14/25:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs' : (531/1000:ℝ)<Real.sin (14/25) := by norm_num at hs; linarith
  have hc' : Real.cos (14/25)<(106/125:ℝ) := by norm_num [cos8] at hc; linarith
  have hm := mul_le_mul
    (show outerDiagonal-1/2≤(2/5:ℝ) by linarith [diagonal_fine.2]) hc'.le
    (by linarith [ht.1] : 0≤Real.cos (14/25)) (by norm_num)
  have hp := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [diagonal_fine.1]) hs'.le
    (by norm_num) (by linarith [diagonal_fine.1] : 0≤outerDiagonal+1/2)
  norm_num [minus,ShortOuterOne.SameContact.arc_diagonal]
  nlinarith [diagonal_fine.2]

lemma angle_before {B x : ℝ} (hd : MinusDomain B x) : x<(14/25:ℝ) := by
  by_contra! hn
  have ht := minus_target_antitone (show (14/25:ℝ)∈Icc 0 (7/10) by norm_num)
    hd.1 (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩) hd.1.2
  have ha := minus_angle_monotone hd.1 (by norm_num : (14/25:ℝ)∈Icc 0 (7/10)) hd.2.1 hn
  linarith [halfsixteen_exit,hd.2.2.2]

lemma domain_before {B x y : ℝ} (hd : MinusDomain B x) (hy : y∈Icc 0 x) :
    MinusDomain B y := by
  have hyi : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hd.2.1.2⟩
  have hlo := minus_aligned_le hd.1 hyi
  have hhi := minus_angle_monotone hd.1 hyi hd.2.1 hy.2
  exact ⟨hd.1,hyi,⟨by linarith [hd.1.2,outer_endpoint_bounds.2.2.2],hhi.trans hd.2.2.2⟩⟩

lemma P_positive {B x : ℝ} (hd : MinusDomain B x) : 0< minusFirst PLabel B x := by
  have hp := (P_first_bounds hd.2.2).1
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hz := minus_z_bound hd
  have hn := minus_norm hd.1 x
  have hv2 : Q0-9/5-4/25<(minusSpeed B x)^2 := by
    have hz2 : (minus B x-1/2)^2<(2/5:ℝ)^2 := sq_lt_sq' hz.1 hz.2
    linarith [hd.1.2,outer_endpoint_bounds.2.2.2]
  have hp2 : (773/1000:ℝ)^2<(PLabel.d1 (minus B x))^2 :=
    pow_lt_pow_left₀ hp (by norm_num) (by norm_num)
  have hprod := mul_lt_mul hp2 hv2.le
    (by norm_num [Q0] : (0:ℝ)<Q0-9/5-4/25) (sq_nonneg _)
  have hnonneg := mul_nonneg (by linarith : 0≤PLabel.d1 (minus B x)) hv.le
  have hsq : (1:ℝ)^2<(PLabel.d1 (minus B x)*minusSpeed B x)^2 := by
    rw [mul_pow]
    norm_num [Q0] at hprod ⊢
    linarith
  have h1 := lt_of_pow_lt_pow_left₀ 2 hnonneg hsq
  dsimp only [minusFirst]
  linarith

theorem P_lower {B x : ℝ} (hd : MinusDomain B x) :
    (44889/50000:ℝ)< minusCost PLabel JLabel B x := by
  have hm : MonotoneOn (minusCost PLabel JLabel B) (Icc 0 x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (minusCost_hasDerivAt PLabel JLabel
        (domain_before hd ht)).continuousAt.continuousWithinAt)
      (fun t ht => minusCost_hasDerivAt PLabel JLabel
        (domain_before hd (Ioo_subset_Icc_self ht)))
      (fun t ht => (P_positive (domain_before hd (Ioo_subset_Icc_self ht))).le)
  have hh := hm ⟨le_rfl,hd.2.1.1⟩ ⟨hd.2.1.1,le_rfl⟩ hd.2.1.1
  have hm0 : minus B 0=1-B := by simp only [minus,Real.cos_zero,Real.sin_zero]; ring
  have hzero := (domain_before hd ⟨le_rfl,hd.2.1.1⟩).2.2
  rw [hm0] at hzero
  have hlow := AlignedPJ.original hzero hd.1 (by ring)
  have h0 : minusCost PLabel JLabel B 0=PLabel.outer (1-B)+JLabel.outer B := by
    simp only [minusCost,hm0]; ring
  linarith

lemma J_negative {B x : ℝ} (hd : MinusDomain B x) : minusSecond JLabel B x<0 := by
  have hJ := J_first_bounds hd.2.2
  have hJ2 := J_second_upper hd.2.2
  have hz := minus_z_bound hd
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hn := minus_norm hd.1 x
  have hv2 : Q0-9/5-4/25<(minusSpeed B x)^2 := by
    have hz2 : (minus B x-1/2)^2<(4/25:ℝ) := by nlinarith
    linarith [hd.1.2,outer_endpoint_bounds.2.2.2]
  have h1 := mul_lt_mul_of_pos_right hJ2 (sq_pos_of_pos hv)
  have h2 := mul_le_mul_of_nonneg_left hz.1.le (by linarith [hJ.1] : 0≤JLabel.d1 (minus B x))
  have h3 := mul_le_mul_of_nonneg_right hJ.2.le (by norm_num : (0:ℝ)≤2/5)
  dsimp [minusSecond]
  norm_num [Q0] at hv2
  nlinarith

lemma diagonal_original {B x : ℝ} (hd : MinusDomain B x) (he : minus B x=outerDiagonal) :
    NegativeTwo.PrimaryDiagonal.height x=B := by
  have hZ : NegativeTwo.PrimaryDiagonal.Z x=W B*Real.cos x-U B*Real.sin x := by
    dsimp only [minus,U,W] at he
    dsimp only [NegativeTwo.PrimaryDiagonal.Z,NegativeTwo.PrimaryDiagonal.offset,U,W]
    linarith
  have hY : NegativeTwo.PrimaryDiagonal.Y x=U B*Real.cos x+W B*Real.sin x := by
    have hc := UW_circle (outer_domain hd.1)
    have hr := (NegativeTwo.PrimaryDiagonal.radical_data hd.2.1).2.2.2.2
    have hp : 0<U B*Real.cos x+W B*Real.sin x := by
      have h1 := mul_pos (U_positive (outer_domain hd.1))
        (by linarith [(positive_trig hd.2.1).1] : 0<Real.cos x)
      have h2 := mul_nonneg (by dsimp only [W]; linarith [hd.1.1] : 0≤W B)
        (positive_trig hd.2.1).2.2.1
      linarith
    rw [hZ] at hr
    have heq : (U B*Real.cos x+W B*Real.sin x)^2+
        (W B*Real.cos x-U B*Real.sin x)^2=Q0 := by
      linear_combination hc+((U B)^2+(W B)^2)*(Real.sin_sq_add_cos_sq x)
    have hy := (NegativeTwo.PrimaryDiagonal.radical_data hd.2.1).2.2.1
    exact (pow_left_inj₀ (by linarith) hp.le two_ne_zero).mp (by linarith)
  dsimp only [NegativeTwo.PrimaryDiagonal.height,NegativeTwo.PrimaryDiagonal.vertical]
  rw [hZ,hY]
  dsimp only [W]
  linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

lemma diagonal_chord {B x : ℝ} (hd : MinusDomain B x) (he : minus B x=outerDiagonal) :
    x≤(351/500)*(B-(1-outerDiagonal)) := by
  let H := NegativeTwo.PrimaryDiagonal.height
  have hxB : H x=B := diagonal_original hd he
  have hH0 : H 0=1-outerDiagonal := NegativeTwo.PrimaryDiagonal.height_zero
  have hH56 : outerDiagonal<H (14/25) := by
    have hr := NegativeTwo.PrimaryDiagonal.radical_data
      (show (14/25:ℝ)∈Icc 0 (7/10) by norm_num)
    have hs := sin_lower_seven (show (0:ℝ)≤14/25 by norm_num)
    have hc := cos_lower_six (show (0:ℝ)≤14/25 by norm_num)
    have hc' := cos_le_cos8 (show (0:ℝ)≤14/25 by norm_num)
    norm_num [cos8] at hs hc hc'
    have hd := diagonal_fine
    have hZlo : (448/1000:ℝ)<NegativeTwo.PrimaryDiagonal.Z (14/25) := by
      dsimp only [NegativeTwo.PrimaryDiagonal.Z,NegativeTwo.PrimaryDiagonal.offset]
      linarith only [hc,hd.2]
    have hZhi : NegativeTwo.PrimaryDiagonal.Z (14/25)<4481/10000 := by
      dsimp only [NegativeTwo.PrimaryDiagonal.Z,NegativeTwo.PrimaryDiagonal.offset]
      linarith only [hc',hd.1]
    have hZ2 := pow_lt_pow_left₀ hZhi (by linarith only [hZlo]) (n := 2) (by norm_num)
    have hY : (1927/1000:ℝ)<NegativeTwo.PrimaryDiagonal.Y (14/25) :=
      lt_of_pow_lt_pow_left₀ 2 (by linarith only [hr.2.2.1])
        (by have h5 := hr.2.2.2.2; norm_num [Q0] at h5 hZ2 ⊢; linarith only [h5,hZ2])
    have h1 := mul_le_mul hY.le hs (by norm_num) (by linarith only [hr.2.2.1])
    have h2 := mul_le_mul hZlo.le hc (by norm_num) (by linarith only [hZlo])
    dsimp only [H,NegativeTwo.PrimaryDiagonal.height,NegativeTwo.PrimaryDiagonal.vertical]
    linarith only [h1,h2,hd.2]
  have hcont : ContinuousOn H (Icc 0 (14/25)) := fun y hy =>
    (NegativeTwo.PrimaryDiagonal.height_hasDerivAt
      ⟨hy.1,by linarith [hy.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hte⟩ := intermediate_value_Icc (show (0:ℝ)≤14/25 by norm_num)
    hcont (show outerDiagonal∈Icc (H 0) (H (14/25)) by
      rw [hH0]; exact ⟨by linarith [diagonal_fine.1],hH56.le⟩)
  have htp : 0<t := by
    by_contra! hn
    have htz : t=0 := le_antisymm hn ht.1
    rw [htz,hH0] at hte
    linarith [diagonal_fine.1]
  have hxt : x≤t := by
    by_contra! hn
    have hh : H t-t/2≤H x-x/2 := NegativeTwo.PrimaryDiagonal.height_half_monotone
      ⟨ht.1,by linarith [ht.2]⟩ hd.2.1 hn.le
    rw [hte,hxB] at hh
    linarith [hd.1.2]
  have hc : ConcaveOn ℝ (Icc (0:ℝ) t) H :=
    concave_of_deriv2
      (fun y hy => NegativeTwo.PrimaryDiagonal.height_hasDerivAt ⟨hy.1,by linarith [hy.2,ht.2]⟩)
      (fun y hy => NegativeTwo.PrimaryDiagonal.speed_hasDerivAt ⟨hy.1,by linarith [hy.2,ht.2]⟩)
      (fun y hy => (NegativeTwo.PrimaryDiagonal.acceleration_negative
        ⟨hy.1,by linarith [hy.2,ht.2]⟩).le)
  have hweight : x/t∈Icc (0:ℝ) 1 := ⟨div_nonneg hd.2.1.1 htp.le,(div_le_one htp).2 hxt⟩
  have hchord := hc.2 (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,htp.le⟩)
    (show t∈Icc 0 t from ⟨htp.le,le_rfl⟩)
    (by linarith [hweight.2] : 0≤1-x/t) hweight.1 (by ring : (1-x/t)+x/t=1)
  have harg : (1-x/t)*0+(x/t)*t=x := by field_simp; ring
  simp only [smul_eq_mul] at hchord
  rw [harg,hH0,hte,hxB] at hchord
  have hh : x*(2*outerDiagonal-1)≤t*(B-(1-outerDiagonal)) := by
    have hh := mul_le_mul_of_nonneg_right hchord htp.le
    have e : ((1-x/t)*(1-outerDiagonal)+x/t*outerDiagonal)*t=
        (t-x)*(1-outerDiagonal)+x*outerDiagonal := by field_simp
    linarith
  have hB : 0≤B-(1-outerDiagonal) := sub_nonneg.mpr (minus_target_lower hd)
  have hmul := mul_le_mul_of_nonneg_right ht.2 hB
  have hratio : (14/25:ℝ)<(351/500)*(2*outerDiagonal-1) := by linarith [diagonal_fine.1]
  by_contra! hn
  have hpos : 0<2*outerDiagonal-1 := by linarith [diagonal_fine.1]
  have h1 := mul_lt_mul_of_pos_right hn hpos
  have h2 := mul_le_mul_of_nonneg_right hratio.le hB
  nlinarith

theorem J_diagonal_lower {B x : ℝ} (hd : MinusDomain B x) (he : minus B x=outerDiagonal) :
    (44889/50000:ℝ)< minusCost JLabel PLabel B x := by
  have hchord := diagonal_chord hd he
  have hB0 : 1-outerDiagonal∈Icc 0 outerDiagonal := by
    constructor <;> linarith [diagonal_fine.1,diagonal_fine.2]
  have hm : MonotoneOn (fun t => PLabel.outer t-(773/1000)*t) (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => ((PLabel.outer_hasDerivAt (outer_domain ht)).sub
        ((hasDerivAt_id t).const_mul (773/1000))).continuousAt.continuousWithinAt)
      (fun t ht => (PLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht))).sub
        ((hasDerivAt_id t).const_mul (773/1000)))
      (fun t ht => by linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1])
  have hh := hm hB0 hd.1 (minus_target_lower hd)
  have hl := AlignedPJ.original hB0 ⟨outer_zero_mem.2,le_rfl⟩ (by ring)
  dsimp [minusCost]
  rw [he]
  linarith [minus_target_lower hd]

theorem J_lower {B x : ℝ} (hd : MinusDomain B x) :
    (44889/50000:ℝ)< minusCost JLabel PLabel B x := by
  have hexit : minus outerDiagonal (14/25) ≤ minus B (14/25) := minus_target_antitone
    (show (14/25:ℝ)∈Icc 0 (7/10) by norm_num) hd.1 ⟨outer_zero_mem.2,le_rfl⟩ hd.1.2
  have hc : Continuous (minus B) :=
    continuous_iff_continuousAt.2 fun y => (minus_hasDerivAt B y).continuousAt
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (angle_before hd).le hc.continuousOn
    (show outerDiagonal∈Icc (minus B x) (minus B (14/25)) from
      ⟨hd.2.2.2,(halfsixteen_exit.trans_le hexit).le⟩)
  have htd : MinusDomain B t := ⟨hd.1,⟨hd.2.1.1.trans ht.1,by linarith [ht.2]⟩,
    by rw [he]; exact ⟨outer_zero_mem.2,le_rfl⟩⟩
  have hconc : ConcaveOn ℝ (Icc 0 t) (minusCost JLabel PLabel B) :=
    concave_of_deriv2
      (fun y hy => minusCost_hasDerivAt JLabel PLabel (domain_before htd hy))
      (fun y hy => minusFirst_hasDerivAt JLabel (domain_before htd hy))
      (fun y hy => (J_negative (domain_before htd hy)).le)
  have hm0 : minus B 0=1-B := by simp only [minus,Real.cos_zero,Real.sin_zero]; ring
  have hz := (domain_before htd ⟨le_rfl,htd.2.1.1⟩).2.2
  rw [hm0] at hz
  have halign := AlignedPJ.original hd.1 hz (by ring)
  apply concave_gt_of_endpoints hconc ⟨hd.2.1.1,ht.1⟩
  · have h0 : minusCost JLabel PLabel B 0=JLabel.outer (1-B)+PLabel.outer B := by
      simp only [minusCost,hm0]; ring
    rw [h0]
    linarith
  · exact J_diagonal_lower htd he

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.NegativePJ
