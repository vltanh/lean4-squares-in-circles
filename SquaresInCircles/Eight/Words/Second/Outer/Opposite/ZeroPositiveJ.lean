module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveSpeeds

/-!
# Eight squares: the remaining J positive-angle interval

On [.5,.7] the actual angular
work J'(b)K decreases with target coordinate.  On target zero it
increases with angle and remains below .993 at the final angle.
Both monotonicity statements are proved on their full feasible arcs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.PositivePJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

def work (B x : ℝ) : ℝ := JLabel.d1 (plus B x)*plusSpeed B x
def workTarget (B x : ℝ) : ℝ :=
  -JLabel.d2 (plus B x)*plusSpeed B x*plusK B x-
    JLabel.d1 (plus B x)*(ratio B*Real.cos x+Real.sin x)
def workAngle (B x : ℝ) : ℝ :=
  -JLabel.d2 (plus B x)*(plusSpeed B x)^2+JLabel.d1 (plus B x)*(plus B x-1/2)

lemma late_source_upper {B x : ℝ} (hd : PlusDomain B x) (hx : 1/2≤x) :
    plus B x<(501/1000:ℝ) := by
  have h1 := plus_target_antitone hd.2.1 outer_zero_mem hd.1 hd.1.1
  have h2 := plus_angle_antitone outer_zero_mem (by norm_num) hd.2.1 hx
  linarith [Reference.plus_references.2.2.1]

lemma late_target_domain {B x C : ℝ} (hd : PlusDomain B x) (hx : 1/2≤x)
    (hC : C∈Icc 0 B) : PlusDomain C x := by
  have hCi : C∈Icc 0 outerDiagonal := ⟨hC.1,hC.2.trans hd.1.2⟩
  have hlo := plus_target_antitone hd.2.1 hCi hd.1 hC.2
  have h0 := plus_target_antitone hd.2.1 outer_zero_mem hCi hC.1
  have h1 := plus_angle_antitone outer_zero_mem (by norm_num) hd.2.1 hx
  exact ⟨hCi,hd.2.1,⟨hd.2.2.1.trans hlo,by
    linarith [Reference.plus_references.2.2.1,fine_outer_endpoint_bounds.2]⟩⟩

lemma late_projections {B x : ℝ} (hd : PlusDomain B x) (hx : 1/2≤x) :
    plusK B x<(753/1000:ℝ) ∧ (679/1000:ℝ)<ratio B*Real.cos x+Real.sin x := by
  have hr := outer_ratio_bounds hd.1
  have ht := positive_trig hd.2.1
  have hs := sin_mono (by norm_num : (1/2:ℝ)∈Icc 0 (7/10)) hd.2.1 hx
  have hc := cos_anti (by norm_num : (1/2:ℝ)∈Icc 0 (7/10)) hd.2.1 hx
  have hsref := HighOrderTaylor.S15_le_sin (show (0:ℝ)≤1/2 by norm_num)
  have hcref := HighOrderTaylor.cos_le_C16 (show (0:ℝ)≤1/2 by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8] at hsref hcref
  have hs' : (23971/50000:ℝ)<Real.sin x := by linarith
  have hc' : Real.cos x<(87759/100000:ℝ) := by linarith
  have h1 := mul_le_mul hr.1.le hs'.le (by norm_num)
    (by linarith [hr.1] : 0≤ratio B)
  have h2 := mul_le_mul hr.1.le ht.1.le (by norm_num)
    (by linarith [hr.1] : 0≤ratio B)
  dsimp [plusK]
  constructor <;> nlinarith

lemma workTarget_hasDerivAt {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (fun C => work C x) (workTarget B x) B := by
  have hs : HasDerivAt (fun C => plusSpeed C x) (-ratio B*Real.cos x-Real.sin x) B := by
    have h : HasDerivAt (fun C => (arc C-1/2)*Real.cos x-(C-1/2)*Real.sin x)
        ((-ratio B)*Real.cos x-1*Real.sin x) B :=
      (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hd.1)).sub_const
        (1/2)).mul_const (Real.cos x)).sub (((hasDerivAt_id' B).sub_const (1/2)).mul_const
          (Real.sin x))
    exact h.congr_deriv (by ring)
  have h := ((JLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp B
    (plus_target_hasDerivAt hd.1 x)).fun_mul hs
  exact h.congr_deriv (by simp only [workTarget,Function.comp_apply]; ring)

lemma work_target_negative {B x : ℝ} (hd : PlusDomain B x) (hx : 1/2≤x) : workTarget B x<0 := by
  have hb := late_source_upper hd hx
  have h501 := Asymmetric.rational_outer_mem (by norm_num : (501/1000:ℝ)∈Icc 0 (899/1000))
  have hJ := J_first_antitone hd.2.2 h501 hb.le
  have hJ2 := J_second_antitone hd.2.2 h501 hb.le
  have hlow : (437/500:ℝ)<JLabel.d1 (plus B x) := Reference.J_501.1.trans_le hJ
  have hcurv : -JLabel.d2 (plus B x)<257/500 := by linarith [Reference.J_501.2]
  have hcurv0 : 0≤-JLabel.d2 (plus B x) := by linarith [J_second_upper hd.2.2]
  have hspeed := speed_upper hd.1 hd.2.1
  have hproj := late_projections hd hx
  have hdata := positive_data hd.1 hd.2.1
  have h1 := mul_lt_mul hcurv hspeed.le hdata.1 (by norm_num)
  have h2 := mul_lt_mul h1 hproj.1.le hdata.2.2.1 (by norm_num)
  have h3 := mul_lt_mul hlow hproj.2.le (by norm_num)
    (by linarith [hlow] : 0≤JLabel.d1 (plus B x))
  dsimp [workTarget]
  norm_num at h2 h3
  nlinarith

lemma zero_late_domain {x : ℝ} (hx : x∈Icc (1/2:ℝ) (7/10)) :
    PlusDomain 0 x ∧ (293/1000:ℝ)<plus 0 x := by
  have hxi : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have he : plus 0 x=SameZero.b 0 x := by dsimp [plus,SameZero.b]; ring
  have hlo : (293/1000:ℝ)<plus 0 x := by rw [he]; exact SameZero.b_lower outer_zero_mem hxi
  have hhi := plus_angle_antitone outer_zero_mem (by norm_num) hxi hx.1
  exact ⟨⟨outer_zero_mem,hxi,⟨by linarith,by
    linarith [Reference.plus_references.2.2.1,fine_outer_endpoint_bounds.2]⟩⟩,hlo⟩

lemma zero_late_speed {x : ℝ} (hx : x∈Icc (1/2:ℝ) (7/10)) : (51/50:ℝ)<plusSpeed 0 x := by
  have hc : ConcaveOn ℝ (Icc (1/2:ℝ) (7/10)) (plusSpeed 0) :=
    concave_of_deriv2
      (fun t _ => plusSpeed_hasDerivAt 0 t)
      (fun t _ => (plus_hasDerivAt 0 t).sub_const (1/2))
      (fun t ht => neg_nonpos.mpr (positive_data outer_zero_mem
        ⟨by linarith [ht.1],ht.2⟩).1.le)
  exact concave_gt_of_endpoints hc hx Reference.zero_speed_references.2.1
    Reference.zero_speed_references.2.2.1

lemma workAngle_hasDerivAt {B x : ℝ} (hd : PlusDomain B x) :
    HasDerivAt (work B) (workAngle B x) x := by
  have h := ((JLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp x (plus_hasDerivAt B x)).fun_mul
    (plusSpeed_hasDerivAt B x)
  exact h.congr_deriv (by simp only [workAngle,Function.comp_apply]; ring)

lemma zero_work_increasing : MonotoneOn (work 0) (Icc (1/2:ℝ) (7/10)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun t ht => (workAngle_hasDerivAt (zero_late_domain ht).1).continuousAt.continuousWithinAt)
    (fun t ht => workAngle_hasDerivAt (zero_late_domain (Ioo_subset_Icc_self ht)).1)
  intro t ht
  have hd := zero_late_domain (Ioo_subset_Icc_self ht)
  have hspeed := zero_late_speed (Ioo_subset_Icc_self ht)
  have hJ2 := J_second_upper hd.1.2.2
  have hJ := (J_first_antitone (Asymmetric.rational_outer_mem (by norm_num)) hd.1.2.2 hd.2.le).trans_lt Reference.J_293
  have hJ0 : 0<JLabel.d1 (plus 0 t) := by linarith [(J_first_bounds hd.1.2.2).1]
  have h1 := mul_lt_mul_of_pos_right hJ2 (sq_pos_of_pos (by linarith : 0<plusSpeed 0 t))
  have h2 := mul_le_mul_of_nonneg_left
    (show -(207/1000:ℝ)≤plus 0 t-1/2 by linarith [hd.2]) hJ0.le
  have h3 := mul_le_mul_of_nonneg_right hJ.le (by norm_num : (0:ℝ)≤207/1000)
  dsimp [workAngle]
  nlinarith

lemma J_late {B x : ℝ} (hd : PlusDomain B x) (hx : 1/2≤x) : 0<plusFirst JLabel B x := by
  have hanti : AntitoneOn (fun C => work C x) (Icc 0 B) :=
    antiOn_of_hasDeriv_nonpos
      (fun C hC => (workTarget_hasDerivAt (late_target_domain hd hx hC)).continuousAt.continuousWithinAt)
      (fun C hC => workTarget_hasDerivAt (late_target_domain hd hx (Ioo_subset_Icc_self hC)))
      (fun C hC => (work_target_negative (late_target_domain hd hx (Ioo_subset_Icc_self hC)) hx).le)
  have h1 := hanti ⟨le_rfl,hd.1.1⟩ ⟨hd.1.1,le_rfl⟩ hd.1.1
  have h2 := zero_work_increasing ⟨hx,hd.2.1.2⟩ (by norm_num) hd.2.1.2
  have h3 := Reference.zero_speed_references.2.2.2
  dsimp [work,plusFirst] at *
  linarith

theorem J_positive {B x : ℝ} (hd : PlusDomain B x) : 0<plusFirst JLabel B x := by
  rcases le_total x (1/2) with hx | hx
  · exact J_early hd hx
  · exact J_late hd hx

end SquaresInCircles.Eight.SecondWord.OppositeZero.PositivePJ
