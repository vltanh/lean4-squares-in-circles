module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroLShape
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroNegativePJ

/-!
# Where the negative-angle symmetric cost can fail to increase

Uncompiled transcription of Sections 7--8 of the symmetric whole-angle
hand proof. The exact circle speed is retained. A nonpositive angular
derivative forces B > .67, b < .66, and b < .56 when B <= .7.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic

lemma product_gt_one {p v l q : ℝ} (hp : 0<p) (hv : 0<v)
    (hl : 0≤l) (hq : 0<q) (hpl : l<p) (hqv : q≤v^2)
    (hreserve : 1<l^2*q) : 1<p*v := by
  have hp2 : l^2<p^2 := by nlinarith
  have hmul := mul_lt_mul hp2 hqv hq (sq_nonneg p)
  have hprod := mul_pos hp hv
  nlinarith

lemma target_location {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) : (67/100:ℝ)<B := by
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hp : 0<LLabel.d1 (minus B x) := by linarith [first_strong_lower hd.2.2]
  have hn := minus_norm hd.1 x
  have hz := minus_z_bound hd
  have hproduct : LLabel.d1 (minus B x)*minusSpeed B x≤1 := by
    dsimp [minusFirst] at hfirst
    linarith
  by_contra! hB
  by_cases hmiddle : minus B x∈Icc (2/5:ℝ) (3/5)
  · have hz2 : (minus B x-1/2)^2≤(1/100:ℝ) := by
      nlinarith [hmiddle.1,hmiddle.2]
    have hrad : Q0-67/50-1/100≤(minusSpeed B x)^2 := by nlinarith
    have hh := product_gt_one hp hv (by norm_num : (0:ℝ)≤1249/2000)
      (by norm_num [Q0] : 0<Q0-67/50-1/100) (first_strong_lower hd.2.2)
      hrad (by norm_num [Q0])
    linarith
  · have hout : minus B x≤2/5 ∨ 3/5≤minus B x := by
      by_contra! h
      exact hmiddle ⟨h.1.le,h.2.le⟩
    have hlabel := first_outside_lower hd.2.2 hout
    have hz2 : (minus B x-1/2)^2<(4/25:ℝ) := by nlinarith [hz.1,hz.2]
    have hrad : Q0-67/50-4/25≤(minusSpeed B x)^2 := by nlinarith
    have hh := product_gt_one hp hv (by norm_num : (0:ℝ)≤649/1000)
      (by norm_num [Q0] : 0<Q0-67/50-4/25) hlabel hrad (by norm_num [Q0])
    linarith

def speedAt (B b : ℝ) : ℝ := Real.sqrt (Q0-2*B-(b-1/2)^2)
def workAt (B b : ℝ) : ℝ := LLabel.d1 b*speedAt B b
def workAtD (B b : ℝ) : ℝ :=
  (LLabel.d2 b*(speedAt B b)^2-LLabel.d1 b*(b-1/2))/speedAt B b

lemma speedAt_data {B b : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hb : b∈Icc (1/2:ℝ) outerDiagonal) :
    0<speedAt B b ∧ (speedAt B b)^2=Q0-2*B-(b-1/2)^2 ∧
      Q0-9/5-4/25<(speedAt B b)^2 := by
  have hz : (b-1/2)^2<(4/25:ℝ) := by
    nlinarith [hb.1,hb.2,outer_endpoint_bounds.2.2.2]
  have hr : Q0-9/5-4/25<Q0-2*B-(b-1/2)^2 := by
    linarith [hB.2,outer_endpoint_bounds.2.2.2]
  have hr0 : 0<Q0-2*B-(b-1/2)^2 := by norm_num [Q0] at hr; linarith
  exact ⟨Real.sqrt_pos.mpr hr0,Real.sq_sqrt hr0.le,by
    dsimp [speedAt]
    rw [Real.sq_sqrt hr0.le]
    exact hr⟩

lemma speedAt_hasDerivAt {B b : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hb : b∈Icc (1/2:ℝ) outerDiagonal) :
    HasDerivAt (speedAt B) (-(b-1/2)/speedAt B b) b := by
  have hs := speedAt_data hB hb
  have hr : Q0-2*B-(b-1/2)^2≠0 := by nlinarith [sq_pos_of_pos hs.1,hs.2.1]
  convert ((((hasDerivAt_id b).sub_const (1/2)).pow 2).const_sub (Q0-2*B)).sqrt hr
    using 1 <;> dsimp [speedAt] <;> field_simp [hs.1.ne'] <;> ring

lemma workAt_hasDerivAt {B b : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hb : b∈Icc (1/2:ℝ) outerDiagonal) : HasDerivAt (workAt B) (workAtD B b) b := by
  have hs := (speedAt_data hB hb).1
  convert (LLabel.d1_hasDerivAt (outer_domain ⟨by linarith [hb.1],hb.2⟩)).mul
    (speedAt_hasDerivAt hB hb) using 1 <;> dsimp [workAt,workAtD] <;>
    field_simp [hs.ne'] <;> ring

lemma workAt_actual {B x : ℝ} (hd : MinusDomain B x) (hb : 1/2≤minus B x) :
    workAt B (minus B x)=LLabel.d1 (minus B x)*minusSpeed B x := by
  have hs := speedAt_data hd.1 ⟨hb,hd.2.2.2⟩
  have hv := (positive_data hd.1 hd.2.1).2.1
  have hn := minus_norm hd.1 x
  have he : speedAt B (minus B x)=minusSpeed B x := by nlinarith [hs.1,hs.2.1]
  rw [workAt,he]

lemma workAt_monotone {B a k M : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (ha : a∈Icc (1/2:ℝ) outerDiagonal) (hcap : B≤M)
    (hk : 0<k) (hka : k≤LLabel.d2 a)
    (hreserve : 0<k*(Q0-2*M-4/25)-(147/125)*(2/5)) :
    MonotoneOn (workAt B) (Icc a outerDiagonal) := by
  have hdom {b : ℝ} (hb : b∈Icc a outerDiagonal) : b∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨ha.1.trans hb.1,hb.2⟩
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (workAt_hasDerivAt hB (hdom hb)).continuousAt.continuousWithinAt)
    (fun b hb => workAt_hasDerivAt hB (hdom (Ioo_subset_Icc_self hb)))
  intro b hb
  have hbi : b∈Icc 0 outerDiagonal := ⟨by linarith [ha.1,hb.1],hb.2.le⟩
  have hs := speedAt_data hB (hdom (Ioo_subset_Icc_self hb))
  have hD := hka.trans (L_second_monotone ⟨by linarith [ha.1],ha.2⟩ hbi hb.1.le)
  have hz : b-1/2∈Icc (0:ℝ) (2/5) :=
    ⟨by linarith [ha.1,hb.1],by linarith [hb.2,outer_endpoint_bounds.2.2.2]⟩
  have hz2 : (b-1/2)^2≤(4/25:ℝ) := by nlinarith [hz.1,hz.2]
  have hrad : Q0-2*M-4/25≤(speedAt B b)^2 := by nlinarith [hs.2.1]
  have h1 := mul_le_mul_of_nonneg_right hD (sq_nonneg (speedAt B b))
  have h2 := mul_le_mul_of_nonneg_left hrad hk.le
  have h3 := mul_le_mul (L_first_upper hbi).le hz.2 hz.1
    (by norm_num : (0:ℝ)≤147/125)
  dsimp [workAtD]
  exact div_nonneg (by nlinarith) hs.1.le

lemma work_56 {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (hcap : B≤7/10) :
    1<workAt B (14/25) := by
  have ha : (14/25:ℝ)∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hs := speedAt_data hB ha
  have hr : Q0-7/5-(3/50)^2≤(speedAt B (14/25))^2 := by
    nlinarith [hs.2.1]
  exact product_gt_one (by linarith [L_56_first]) hs.1
    (by norm_num : (0:ℝ)≤15817/25000)
    (by norm_num [Q0] : 0<Q0-7/5-(3/50)^2) L_56_first hr (by norm_num [Q0])

lemma work_66 {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 1<workAt B (33/50) := by
  have ha : (33/50:ℝ)∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hs := speedAt_data hB ha
  have hr : Q0-9/5-(4/25)^2≤(speedAt B (33/50))^2 := by
    nlinarith [hs.2.1,hB.2,outer_endpoint_bounds.2.2.2]
  exact product_gt_one (by linarith [L_66_first]) hs.1
    (by norm_num : (0:ℝ)≤6933/10000)
    (by norm_num [Q0] : 0<Q0-9/5-(4/25)^2) L_66_first hr (by norm_num [Q0])

lemma source_below_56 {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) (hcap : B≤7/10) : minus B x<(14/25:ℝ) := by
  by_contra! hb
  have ha : (14/25:ℝ)∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hm := workAt_monotone hd.1 ha hcap (by norm_num : (0:ℝ)<29/100)
    L_56_second.le (by norm_num [Q0])
  have hh := hm ⟨le_rfl,ha.2⟩ ⟨hb,hd.2.2.2⟩ hb
  have hl := work_56 hd.1 hcap
  rw [workAt_actual hd (by linarith)] at hh
  dsimp [minusFirst] at hfirst
  linarith

lemma source_below_66 {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) : minus B x<(33/50:ℝ) := by
  by_contra! hb
  have ha : (33/50:ℝ)∈Icc (1/2:ℝ) outerDiagonal :=
    ⟨by norm_num,(Asymmetric.rational_outer_mem (by norm_num)).2⟩
  have hm := workAt_monotone hd.1 ha
    (show B≤(9/10:ℝ) by linarith [hd.1.2,outer_endpoint_bounds.2.2.2])
    (by norm_num : (0:ℝ)<93/100) L_66_second.le (by norm_num [Q0])
  have hh := hm ⟨le_rfl,ha.2⟩ ⟨hb,hd.2.2.2⟩ hb
  have hl := work_66 hd.1
  rw [workAt_actual hd (by linarith)] at hh
  dsimp [minusFirst] at hfirst
  linarith

theorem nonpositive_angular_location {B x : ℝ} (hd : MinusDomain B x)
    (hfirst : minusFirst LLabel B x≤0) :
    (67/100:ℝ)<B ∧ minus B x<(33/50:ℝ) ∧
      (B≤7/10 → minus B x<(14/25:ℝ)) :=
  ⟨target_location hd hfirst,source_below_66 hd hfirst,source_below_56 hd hfirst⟩

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Symmetric
