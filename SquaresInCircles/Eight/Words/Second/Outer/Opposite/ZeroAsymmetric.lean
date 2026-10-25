module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoLowerStripContact
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroData
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroNegativePJ
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPlusDiagonalBoundary
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveSpeeds
public import SquaresInCircles.Eight.Words.Second.WordData

/-!
# Eight squares: the original asymmetric opposite zero-quarter pair

Positive contacts decrease in angle to alignment or to the source diagonal (`plus_lower`). A weak
original separator lowers its source, or its target after the source reaches zero, to a contact
(`original_positive`). Negative contacts lower only their source (`minus_lower`,
`original_negative`). Both P/J orders are covered throughout (`original`).
-/

section
/-!
## Strict concavity of the actual lower-angle circle support

The norm is differentiated from its defining radical.  The single
quintic proves the sign of the exact second derivative on the whole
angle interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerSupport

open CommonQuarter CorePairGeometry Arithmetic

def R : ℝ := Real.sqrt Q0
def norm (x : ℝ) : ℝ := Real.sqrt (g^2+h^2-2*g*h*Real.sin x)
def value (x : ℝ) : ℝ :=
  Real.pi/2-x-P 0-V 0-R*norm x+h*Real.cos x+(g+h)/2
def first (x : ℝ) : ℝ := -1+R*g*h*Real.cos x/norm x-h*Real.sin x
def second (x : ℝ) : ℝ :=
  -h*Real.cos x-R*g*h*Real.sin x/norm x+
    R*g^2*h^2*(Real.cos x)^2/(norm x)^3

lemma R_data : 0<R ∧ R^2=Q0 ∧ R<4947/2500 := by
  have hp : 0<Q0 := by norm_num [Q0]
  have hpos := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  exact ⟨hpos,hsq,(Real.sqrt_lt' (by norm_num)).mpr (by norm_num [Q0])⟩

lemma norm_data {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<norm x ∧ (norm x)^2=g^2+h^2-2*g*h*Real.sin x := by
  have hs := (positive_trig hx).2.2.2.1
  have hrad : 0<g^2+h^2-2*g*h*Real.sin x := by
    norm_num [g,h]
    linarith
  exact ⟨Real.sqrt_pos.mpr hrad,Real.sq_sqrt hrad.le⟩

lemma norm_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt norm (-(g*h*Real.cos x)/norm x) x := by
  have hd := norm_data hx
  have hrad : g^2+h^2-2*g*h*Real.sin x≠0 := by nlinarith [sq_pos_of_pos hd.1]
  have hne := hd.1.ne'
  exact ((((Real.hasDerivAt_sin x).const_mul (2*g*h)).const_sub
    (g^2+h^2)).sqrt hrad).congr_deriv (by dsimp only [norm] at hne ⊢; field_simp)

lemma value_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt value (first x) x := by
  have hn := norm_hasDerivAt hx
  exact (((((((hasDerivAt_id x).const_sub (Real.pi/2)).sub_const (P 0)).sub_const
    (V 0)).sub (hn.const_mul R)).add ((Real.hasDerivAt_cos x).const_mul h)).add_const
      ((g+h)/2)).congr_deriv (by dsimp only [first]; ring)

lemma first_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt first (second x) x := by
  have hn := norm_data hx
  have hquot := ((Real.hasDerivAt_cos x).const_mul (R*g*h)).div
    (norm_hasDerivAt hx) hn.1.ne'
  have hne := hn.1.ne'
  exact ((hquot.const_add (-1)).sub ((Real.hasDerivAt_sin x).const_mul h)).congr_deriv
    (by dsimp only [second]; field_simp; ring)

lemma second_identity {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (second x+h*Real.cos x)*(norm x)^3=
      R*g*h*(g-h*Real.sin x)*(h-g*Real.sin x) := by
  have hn := norm_data hx
  have ht := Real.sin_sq_add_cos_sq x
  calc
    _= -R*g*h*Real.sin x*(norm x)^2+R*g^2*h^2*(Real.cos x)^2 := by
      dsimp [second]
      field_simp [hn.1.ne']
      ring
    _=R*g*h*(g-h*Real.sin x)*(h-g*Real.sin x) := by
      rw [hn.2]
      linear_combination R*g^2*h^2*ht

lemma squared_comparison {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (R*g*(g-h*Real.sin x)*(h-g*Real.sin x))^2<
      (Real.cos x*(norm x)^3)^2 := by
  have hn := norm_data hx
  have hcos : (Real.cos x)^2=1-(Real.sin x)^2 := by
    linarith [Real.sin_sq_add_cos_sq x]
  have hn6 : (norm x)^6=(g^2+h^2-2*g*h*Real.sin x)^3 := by
    calc
      (norm x)^6=((norm x)^2)^3 := by ring
      _=(g^2+h^2-2*g*h*Real.sin x)^3 := by rw [hn.2]
  have he : (Real.cos x*(norm x)^3)^2-
      (R*g*(g-h*Real.sin x)*(h-g*Real.sin x))^2=polynomial (Real.sin x) := by
    calc
      _=(Real.cos x)^2*(norm x)^6-
          R^2*g^2*(g-h*Real.sin x)^2*(h-g*Real.sin x)^2 := by ring
      _=polynomial (Real.sin x) := by rw [hcos,hn6,R_data.2.1]; rfl
  have hp := polynomial_positive
    (show Real.sin x∈Icc 0 (129/200) from
      ⟨(positive_trig hx).2.2.1,by linarith [(positive_trig hx).2.2.2.1]⟩)
  linarith

theorem second_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : second x<0 := by
  have hn := norm_data hx
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hs := (positive_trig hx).2.2.2.1
  have hp : 0<g-h*Real.sin x ∧ 0<h-g*Real.sin x := by
    norm_num [g,h]
    constructor <;> linarith
  have hleft : 0<R*g*(g-h*Real.sin x)*(h-g*Real.sin x) := by
    have hg : 0<g := by norm_num [g]
    exact mul_pos (mul_pos (mul_pos R_data.1 hg) hp.1) hp.2
  have hright : 0<Real.cos x*(norm x)^3 := mul_pos hc (pow_pos hn.1 3)
  have hcompare : R*g*(g-h*Real.sin x)*(h-g*Real.sin x)<Real.cos x*(norm x)^3 := by
    nlinarith [squared_comparison hx]
  have hmul := mul_lt_mul_of_pos_left hcompare (show 0<h by norm_num [h])
  have he := second_identity hx
  have hnorm := pow_pos hn.1 3
  nlinarith

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerSupport
end
end
end

section
/-!
## The actual weak lower target-secondary owner on the full angle tail

The source chord follows directly from the original circle and
primary height at least one.  The target tangent is integrated from
its true derivative.  A single circle support then gives the exact
concave scalar; two fixed endpoint comparisons cover [.01,.7].
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerSupport

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma small_norm : norm (1/100)<134561/100000 := by
  have hn := norm_data (show (1/100:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs := sin_lower_seven (show (0:ℝ)≤1/100 by norm_num)
  norm_num at hs
  norm_num [g,h] at hn
  nlinarith

lemma cap_norm : norm (7/10)<82613/100000 := by
  have hn := norm_data (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hs := ShortOuterOne.FiveSame.cap_fine.1
  norm_num [g,h] at hn
  nlinarith

lemma zero_label : V 0< -(1449/100000:ℝ) := by
  norm_num [V,RoleLabel.outer,RoleLabel.eval,VLabel,ShortOuterOne.SameContact.arc_zero]
  linarith [ShortOuterZero.fine_axial_bounds.1]

lemma small_value : (4491/5000:ℝ)<value (1/100) := by
  have hn := norm_data (show (1/100:ℝ)∈Icc 0 (7/10) by norm_num)
  have hprod := mul_le_mul R_data.2.2.le small_norm.le hn.1.le (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := 1/100)
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have hV := zero_label
  norm_num [value,g,h,P,RoleLabel.outer,RoleLabel.eval,PLabel] at hc ⊢
  nlinarith

lemma cap_value : (493/500:ℝ)<value (7/10) := by
  have hn := norm_data (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hprod := mul_le_mul R_data.2.2.le cap_norm.le hn.1.le (by norm_num)
  have hc := ShortOuterOne.FiveSame.cap_fine.2.2.1
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have hV := zero_label
  norm_num [value,g,h,P,RoleLabel.outer,RoleLabel.eval,PLabel]
  nlinarith

theorem value_lower {x : ℝ} (hx : x∈Icc (1/100) (7/10)) :
    (44889/50000:ℝ)<value x := by
  have hmem {y : ℝ} (hy : y∈Icc (1/100) (7/10)) : y∈Icc 0 (7/10) :=
    ⟨by linarith [hy.1],hy.2⟩
  have hc : ConcaveOn ℝ (Icc (1/100) (7/10)) value :=
    concave_of_deriv2 (fun y hy => value_hasDerivAt (hmem hy))
      (fun y hy => first_hasDerivAt (hmem hy))
      (fun y hy => (second_negative (hmem hy)).le)
  exact concave_gt_of_endpoints hc hx
    (by linarith [small_value]) (by linarith [cap_value])

lemma source_chord {b : ℝ} (hb : b∈Icc 0 bOne) : P b≤P 0+g*b := by
  have hB : b∈Icc 0 outerDiagonal := ⟨hb.1,hb.2.trans bOne_mem.2⟩
  have harc := ShortOuterOne.SameContact.arc_antitone (outer_domain hB)
    (outer_domain bOne_mem) hb.2
  rw [bOne_arc] at harc
  have hprod := mul_le_mul_of_nonneg_right harc hb.1
  have hquad := mul_nonneg hb.1 (show 0≤bOne-b by linarith [hb.2])
  have hcoef : (8196/10000:ℝ)+(2363/100000)*bOne<g := by
    dsimp [g]
    linarith [bOne_bounds.2]
  have hlast := mul_le_mul_of_nonneg_right hcoef.le hb.1
  norm_num [P,RoleLabel.outer,RoleLabel.eval,PLabel]
  nlinarith

lemma target_linear {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : V B≤V 0+h*B := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun s => h*s-V s) (h-VLabel.d1 t) t := by
    exact (((hasDerivAt_id t).const_mul h).sub
      (VLabel.outer_hasDerivAt (outer_domain ht))).congr_deriv (by ring)
  have hm : MonotoneOn (fun s => h*s-V s) (Icc 0 outerDiagonal) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (hd ht).continuousAt.continuousWithinAt
    · exact fun t ht => hd (Ioo_subset_Icc_self ht)
    · intro t ht
      dsimp [h]
      linarith [V_first_upper (Ioo_subset_Icc_self ht)]
  have hh := hm outer_zero_mem hB hB.1
  nlinarith

lemma circle_support {b x : ℝ} (hb : b∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    h*Real.cos x*U b+(g-h*Real.sin x)*W b≤R*norm x := by
  have hc := UW_circle (outer_domain hb)
  have hn := norm_data hx
  have ht := Real.sin_sq_add_cos_sq x
  have hn2 : (h*Real.cos x)^2+(g-h*Real.sin x)^2=(norm x)^2 := by
    rw [hn.2]
    linear_combination h^2*ht
  have hid : Q0*((h*Real.cos x)^2+(g-h*Real.sin x)^2)-
      (h*Real.cos x*U b+(g-h*Real.sin x)*W b)^2=
      (h*Real.cos x*W b-(g-h*Real.sin x)*U b)^2 := by
    linear_combination -((h*Real.cos x)^2+(g-h*Real.sin x)^2)*hc
  rw [hn2,←R_data.2.1] at hid
  have hprod := mul_pos R_data.1 hn.1
  have hs := sq_nonneg (h*Real.cos x*W b-(g-h*Real.sin x)*U b)
  nlinarith

lemma actual_support {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hcut : B≤lowerCut a b x) :
    value x≤OppositeTwo.value b B (Real.pi/2-x) := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2⟩
  have hA : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have ha : 1≤a := by linarith [LowerSecondary.cut_upper hs hx,ht.1]
  have hbone := ShortOuterOne.SameContact.arc_antitone (primary_domain primary_one_mem)
    (primary_domain hA) ha
  rw [(ShortOuterOne.SameContact.actual_arc hs).2] at hbone
  change b≤bOne at hbone
  have hP := source_chord ⟨hs.1,hbone⟩
  have hV := target_linear hB
  have htarget := mul_le_mul_of_nonneg_left hcut (show 0≤h by norm_num [h])
  have hcircle := circle_support hb hx
  dsimp [U,W] at hcircle
  rw [(ShortOuterOne.SameContact.actual_arc hs).1] at hcircle
  dsimp [value,OppositeTwo.value,lowerCut] at *
  nlinarith

theorem original_tail {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (1/100) (7/10))
    (hm : 0≤forwardMargin 2 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<OppositeTwo.value b B (Real.pi/2-x) := by
  have hangle : x∈Icc 0 (7/10) := ⟨by linarith [hx.1],hx.2⟩
  have hcut : B≤lowerCut a b x := by
    have hw := lower_width hangle
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [lowerCut]
    linarith
  exact (value_lower hx).trans_le (actual_support hs ht hangle hcut)

end SquaresInCircles.Eight.SecondWord.OppositeTwo.LowerSupport
end
end
end

section
/-!
## The remaining J positive-angle interval

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Asymmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def F (reverse : Bool) : RoleLabel := if reverse then JLabel else PLabel
def G (reverse : Bool) : RoleLabel := if reverse then PLabel else JLabel

lemma label_monotone (reverse : Bool) : MonotoneOn (F reverse).outer (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun t ht => ((F reverse).outer_hasDerivAt (outer_domain ht)).continuousAt.continuousWithinAt)
    (fun t ht => (F reverse).outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht)))
  intro t ht
  cases reverse <;> dsimp [F] <;>
    first | linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1] |
      linarith [(J_first_bounds (Ioo_subset_Icc_self ht)).1]

lemma positive_derivative (reverse : Bool) {B x : ℝ} (hd : PlusDomain B x) :
    0<plusFirst (F reverse) B x := by
  cases reverse
  · exact PositivePJ.P_positive hd
  · exact PositivePJ.J_positive hd

theorem plus_lower (reverse : Bool) {B x : ℝ} (hd : PlusDomain B x) :
    (44889/50000:ℝ)<plusCost (F reverse) (G reverse) B x := by
  have hplus0 : plus B 0=1-B := by simp only [plus,Real.cos_zero,Real.sin_zero]; ring
  have hexists : ∃y∈Icc 0 x, PlusDomain B y ∧ (y=0 ∨ plus B y=outerDiagonal) := by
    by_cases hz : 1-B≤outerDiagonal
    · refine ⟨0,⟨le_rfl,hd.2.1.1⟩,⟨hd.1,by norm_num,?_⟩,Or.inl rfl⟩
      rw [hplus0]
      exact ⟨by linarith [hd.1.2,outer_endpoint_bounds.2.2.2],hz⟩
    · have hc : Continuous (plus B) :=
        continuous_iff_continuousAt.2 fun y => (plus_hasDerivAt B y).continuousAt
      obtain ⟨y,hy,he⟩ := intermediate_value_Icc hd.2.1.1 hc.neg.continuousOn
        (show -outerDiagonal∈Icc (-plus B 0) (-plus B x) by
          rw [hplus0]; constructor <;> linarith [hd.2.2.2])
      have hcontact : plus B y=outerDiagonal := by rw [Pi.neg_apply] at he; linarith
      have hyd : PlusDomain B y := ⟨hd.1,⟨hy.1,hy.2.trans hd.2.1.2⟩,
        by rw [hcontact]; exact ⟨outer_zero_mem.2,le_rfl⟩⟩
      exact ⟨y,hy,hyd,Or.inr hcontact⟩
  obtain ⟨y,hy,hyd,hexit⟩ := hexists
  have hdom : ∀t∈Icc y x,PlusDomain B t := by
    intro t ht
    have hti : t∈Icc 0 (7/10) := ⟨hyd.2.1.1.trans ht.1,ht.2.trans hd.2.1.2⟩
    exact ⟨hd.1,hti,⟨hd.2.2.1.trans (plus_angle_antitone hd.1 hti hd.2.1 ht.2),
      (plus_angle_antitone hd.1 hyd.2.1 hti ht.1).trans hyd.2.2.2⟩⟩
  have hmono : MonotoneOn (plusCost (F reverse) (G reverse) B) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (plusCost_hasDerivAt _ _ (hdom t ht)).continuousAt.continuousWithinAt)
      (fun t ht => plusCost_hasDerivAt _ _ (hdom t (Ioo_subset_Icc_self ht)))
      (fun t ht => (positive_derivative reverse (hdom t (Ioo_subset_Icc_self ht))).le)
  have hbetter := hmono ⟨le_rfl,hy.2⟩ ⟨hy.2,le_rfl⟩ hy.2
  have hlower : (44889/50000:ℝ)<plusCost (F reverse) (G reverse) B y := by
    rcases hexit with rfl | he
    · have hsource := hyd.2.2
      rw [hplus0] at hsource
      have h0 : plusCost (F reverse) (G reverse) B 0=(F reverse).outer (1-B)+(G reverse).outer B := by
        simp only [plusCost,hplus0]; ring
      rw [h0]
      cases reverse
      · exact AlignedPJ.original hsource hd.1 (by ring)
      · have hh := AlignedPJ.original hd.1 hsource (by ring)
        simp only [F,G,↓reduceIte]
        linarith
    · obtain ⟨hbranch,hB⟩ := PlusDiagonal.original hyd he
      have hh := PlusDiagonal.lower reverse hbranch
      have he' : plusCost (F reverse) (G reverse) B y=PlusDiagonal.cost
          (if reverse then JLabel else PLabel) (if reverse then PLabel else JLabel) y := by
        simp only [plusCost,PlusDiagonal.cost,he,hB,F,G]
      rw [he']
      exact hh
  exact hlower.trans_le hbetter

theorem minus_lower (reverse : Bool) {B x : ℝ} (hd : MinusDomain B x) :
    (44889/50000:ℝ)< minusCost (F reverse) (G reverse) B x := by
  cases reverse
  · exact NegativePJ.P_lower hd
  · exact NegativePJ.J_lower hd

theorem original_positive (reverse : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (44889/50000:ℝ)<x+(F reverse).eval a b+(G reverse).eval A B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hm' : plus B x≤b := by
    have hw := signed_width (show |x|≤7/10 from abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)
    rw [abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin] at hm
    rw [hw] at hm
    dsimp only [plus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have htargetMono : MonotoneOn (G reverse).outer (Icc 0 outerDiagonal) := by
    cases reverse
    · exact label_monotone true
    · exact label_monotone false
  have hcontact : ∃C, C∈Icc 0 B ∧ PlusDomain C x ∧ plus C x≤b := by
    by_cases hp : 0≤plus B x
    · exact ⟨B,⟨hB.1,le_rfl⟩,⟨hB,hx,⟨hp,hm'.trans hb.2⟩⟩,hm'⟩
    · have hzero : 0<plus 0 x := by
        have hh := SameZero.b_lower outer_zero_mem hx
        have he : plus 0 x=SameZero.b 0 x := by dsimp only [plus,SameZero.b]; ring
        linarith
      have hc : ContinuousOn (fun C => plus C x) (Icc 0 B) := fun C hC =>
        (plus_target_hasDerivAt ⟨hC.1,hC.2.trans hB.2⟩ x).continuousAt.continuousWithinAt
      obtain ⟨C,hC,he⟩ := intermediate_value_Icc hB.1 hc.neg
        (show (0:ℝ)∈Icc (-plus 0 x) (-plus B x) by constructor <;> linarith)
      have hplus : plus C x=0 := by rw [Pi.neg_apply] at he; linarith
      refine ⟨C,hC,⟨⟨hC.1,hC.2.trans hB.2⟩,hx,?_⟩,?_⟩
      · rw [hplus]; exact outer_zero_mem
      · rw [hplus]; exact hb.1
  obtain ⟨C,hC,hd,hbC⟩ := hcontact
  have h1 := label_monotone reverse hd.2.2 hb hbC
  have h2 := htargetMono hd.1 hB hC.2
  have hh := plus_lower reverse hd
  rw [(F reverse).outer_actual hs] at h1
  rw [(G reverse).outer_actual ht] at h2
  dsimp only [plusCost] at hh
  linarith

theorem original_negative (reverse : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) (-x)) :
    (44889/50000:ℝ)< -x+(F reverse).eval a b+(G reverse).eval A B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hm' : minus B x≤b := by
    have hw := signed_width (show |-x|≤7/10 by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin,Real.sin_neg,Real.cos_neg] at hm
    rw [hw] at hm
    dsimp [minus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hd : MinusDomain B x := ⟨hB,hx,⟨by
    linarith [minus_aligned_le hB hx,hB.2,outer_endpoint_bounds.2.2.2],hm'.trans hb.2⟩⟩
  have h1 := label_monotone reverse hd.2.2 hb hm'
  rw [(F reverse).outer_actual hs] at h1
  have hh := minus_lower reverse hd
  dsimp [minusCost] at hh
  rw [(G reverse).outer_actual ht] at hh
  linarith

theorem original (reverse : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (44889/50000:ℝ)<x+(F reverse).eval a b+(G reverse).eval A B := by
  rcases le_total 0 x with hpos | hneg
  · exact original_positive reverse hs ht ⟨hpos,(abs_le.mp hx).2⟩ hm
  · have hxn : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa only [neg_neg] using original_negative reverse hs ht hxn (by simpa using hm)

end SquaresInCircles.Eight.SecondWord.OppositeZero.Asymmetric
end
end
end
