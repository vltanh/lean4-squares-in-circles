module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighHighPrimary

/-!
# The two high-source transverse scalar supports

The negative core tangent is controlled by the same parallel value on
both sides of zero.  On the negative interval the derivative numerator
is positive by one completed square.  The positive core tangent has a
strictly increasing affine trigonometric support in both quadrants.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighHighSecondaryScalars
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (g K)
open FrameCoreMidScalars (ap cp trigAffine trigAffine_monotone)

def parallelValue : ℝ := Real.pi/4+g*(1-c0)
def negativeCore (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+g*pairWidth x+Real.pi/4-g*c0-g*(7/12)*Real.sin x
def negativeAngle (z : ℝ) : ℝ :=
  -z-(9/100)*(Real.sin z+Real.cos z-1)+Real.pi/4+g/2+
    g*((1/2-c0)+(13/12)*Real.sin z)/Real.cos z
def negativeAngleD (z : ℝ) : ℝ :=
  -1-(9/100)*(Real.cos z-Real.sin z)+
    g*((13/12)+(1/2-c0)*Real.sin z)/(Real.cos z)^2
def positiveCore (x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+pairWidth x+Real.pi/4-c0-
    coreLabel FrameCoreArc.diagonal FrameCoreArc.diagonal+
      FrameCoreArc.diagonal*(Real.cos x-Real.sin x)

theorem parallel_lower : (8939/10000:ℝ)<parallelValue := by
  have hd := FrameHighArc.diagonal_bounds.2
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [parallelValue,g]
  linarith

theorem negativeCore_lower {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    (8939/10000:ℝ)<negativeCore x := by
  let C : ℝ := ap+Real.pi/4-g*c0
  let b : ℝ := cp-g*(7/12)
  have hb : -(1/5:ℝ)<b ∧ b<0 := by norm_num [b,cp,g]
  have hfirst : MonotoneOn (trigAffine 1 C cp b) (Icc (0:ℝ) (Real.pi/2)) :=
    trigAffine_monotone (by norm_num) (by norm_num [cp,g,b])
  have hsecond : MonotoneOn (trigAffine 1 C (-cp) b) (Icc (Real.pi/2) Real.pi) :=
    trigAffine_monotone (by norm_num) (by norm_num [cp,g,b])
  have he1 {t : ℝ} (ht : t∈Icc 0 (Real.pi/2)) :
      negativeCore t=trigAffine 1 C cp b t := by
    dsimp [negativeCore,trigAffine,C,b,ap,cp]
    rw [(first_width ht).1,(first_width ht).2]
    ring
  have he2 {t : ℝ} (ht : t∈Icc (Real.pi/2) Real.pi) :
      negativeCore t=trigAffine 1 C (-cp) b t := by
    dsimp [negativeCore,trigAffine,C,b,ap,cp]
    rw [(second_width ht).1,(second_width ht).2]
    ring
  have he0 : negativeCore 0=parallelValue := by
    simp [negativeCore,parallelValue,pairWidth,periodicFrameCost]
    ring
  by_cases hq : x≤Real.pi/2
  · have hh := hfirst ⟨le_rfl,by positivity⟩ ⟨hx.1,hq⟩ hx.1
    rw [← he1 ⟨le_rfl,by positivity⟩,← he1 ⟨hx.1,hq⟩,he0] at hh
    exact parallel_lower.trans_le hh
  · have h1 := hfirst ⟨le_rfl,by positivity⟩ ⟨by positivity,le_rfl⟩ (by positivity)
    have h2 := hsecond ⟨le_rfl,by linarith [Real.pi_pos]⟩
      ⟨(lt_of_not_ge hq).le,hx.2⟩ (lt_of_not_ge hq).le
    rw [← he1 ⟨le_rfl,by positivity⟩,← he1 ⟨by positivity,le_rfl⟩,he0] at h1
    rw [← he2 ⟨le_rfl,by linarith [Real.pi_pos]⟩,
      ← he2 ⟨(lt_of_not_ge hq).le,hx.2⟩] at h2
    exact parallel_lower.trans_le (h1.trans h2)

theorem negativeAngle_deriv {z : ℝ} (hc : Real.cos z≠0) :
    HasDerivAt negativeAngle (negativeAngleD z) z := by
  have hbase := (((((hasDerivAt_id' z).neg).fun_sub
    ((((Real.hasDerivAt_sin z).fun_add (Real.hasDerivAt_cos z)).sub_const 1).const_mul
      (9/100))).add_const (Real.pi/4)).add_const (g/2))
  have hquot := ((((Real.hasDerivAt_sin z).const_mul (13/12)).const_add (1/2-c0)).const_mul
    g).fun_div (Real.hasDerivAt_cos z) hc
  convert hbase.fun_add hquot using 1
  · rfl
  · dsimp [negativeAngleD]
    field_simp
    linear_combination (-2600*g)*Real.sin_sq_add_cos_sq z

theorem negativeAngleD_positive {z : ℝ} (hz : z∈Icc (0:ℝ) (203/250)) :
    0<negativeAngleD z := by
  have hq := FrameLowPair.quadrant
    (show z∈Icc 0 (Real.pi/2) from ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩)
  have hcL := Real.cos_le_cos_of_nonneg_of_le_pi hz.1
    (by linarith [FrameLowPair.pi_lower] : (203/250:ℝ)≤Real.pi) hz.2
  have hc0 := cos_lower_six (show (0:ℝ)≤203/250 by norm_num)
  norm_num at hc0
  have hcpos : 0<Real.cos z := by linarith
  have hcs : Real.cos z-Real.sin z≤1 := by linarith [hq.1,hq.2.2.2]
  have hprod := mul_le_mul_of_nonneg_right hcs (sq_nonneg (Real.cos z))
  have hd := mul_le_mul_of_nonneg_right FrameHighArc.diagonal_bounds.2.le hq.1
  have hsquare := sq_nonneg ((109/100)*Real.sin z-g/5)
  have he : negativeAngleD z*(Real.cos z)^2=
      (-1-(9/100)*(Real.cos z-Real.sin z))*(Real.cos z)^2+
        g*((13/12)+(1/2-c0)*Real.sin z) := by
    dsimp [negativeAngleD]
    field_simp [hcpos.ne']
  have hnum : 0<negativeAngleD z*(Real.cos z)^2 := by
    dsimp [g] at *
    nlinarith [Real.sin_sq_add_cos_sq z]
  exact (mul_pos_iff_of_pos_right (pow_pos hcpos 2)).mp hnum

theorem negativeAngle_lower {z : ℝ} (hz : z∈Icc (0:ℝ) (203/250)) :
    (8939/10000:ℝ)<negativeAngle z := by
  have hcos {t : ℝ} (ht : t∈Icc (0:ℝ) (203/250)) : Real.cos t≠0 := by
    have hh := FrameCoreHighGeometry.negative_trig
      (show -t∈Icc (-(203/250:ℝ)) 0 from ⟨by linarith [ht.2],by linarith [ht.1]⟩)
    rw [Real.cos_neg] at hh
    linarith [hh.2]
  have hm : MonotoneOn negativeAngle (Icc (0:ℝ) (203/250)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (negativeAngle_deriv (hcos ht)).continuousAt.continuousWithinAt
    · exact fun t ht => negativeAngle_deriv (hcos (Ioo_subset_Icc_self ht))
    · exact fun t ht => (negativeAngleD_positive (Ioo_subset_Icc_self ht)).le
  have hh := hm ⟨le_rfl,by norm_num⟩ hz hz.1
  have he : negativeAngle 0=parallelValue := by simp [negativeAngle,parallelValue]; ring
  rw [he] at hh
  exact parallel_lower.trans_le hh

theorem core_diagonal_state : CoreState FrameCoreArc.diagonal FrameCoreArc.diagonal := by
  right
  exact ⟨by linarith [CoreAngleEndpoint.diagonal_bounds.1],le_rfl,
    by nlinarith [CoreAngleEndpoint.diagonal_sq]⟩

theorem positiveCore_lower {x : ℝ} (hx : x∈Icc (9/20:ℝ) Real.pi) :
    (47/50:ℝ)<positiveCore x := by
  let C : ℝ := 59/100+Real.pi/4-c0-
    coreLabel FrameCoreArc.diagonal FrameCoreArc.diagonal
  let a : ℝ := 41/100+FrameCoreArc.diagonal
  let b : ℝ := 41/100-FrameCoreArc.diagonal
  have ha : (121/125:ℝ)<a ∧ a<97/100 := by
    dsimp [a]
    constructor <;> linarith [CoreAngleEndpoint.diagonal_bounds.1,CoreAngleEndpoint.diagonal_bounds.2]
  have hb : -(3/20:ℝ)<b ∧ b<0 := by
    dsimp [b]
    constructor <;> linarith [CoreAngleEndpoint.diagonal_bounds.1,CoreAngleEndpoint.diagonal_bounds.2]
  have hamp : a^2+b^2<(1:ℝ)^2 := by nlinarith
  have hamp2 : (-b)^2+b^2<(1:ℝ)^2 := by nlinarith
  have hm1 : MonotoneOn (trigAffine 1 C a b) (Icc (9/20:ℝ) (Real.pi/2)) :=
    trigAffine_monotone (by norm_num) hamp
  have hm2 : MonotoneOn (trigAffine 1 C (-b) b) (Icc (Real.pi/2) Real.pi) :=
    trigAffine_monotone (by norm_num) hamp2
  have he1 {t : ℝ} (ht : t∈Icc 0 (Real.pi/2)) :
      positiveCore t=trigAffine 1 C a b t := by
    dsimp [positiveCore,trigAffine,C,a,b]
    rw [(first_width ht).1,(first_width ht).2]
    ring
  have he2 {t : ℝ} (ht : t∈Icc (Real.pi/2) Real.pi) :
      positiveCore t=trigAffine 1 C (-b) b t := by
    dsimp [positiveCore,trigAffine,C,a,b]
    rw [(second_width ht).1,(second_width ht).2]
    ring
  have hstart : (47/50:ℝ)<positiveCore (9/20) := by
    rw [he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩]
    have hc := Real.one_sub_sq_div_two_le_cos (x := (9/20:ℝ))
    have hs := Real.sin_le (show (0:ℝ)≤9/20 by norm_num)
    have ht := FrameLowPair.quadrant
      (show (9/20:ℝ)∈Icc 0 (Real.pi/2) by constructor <;> linarith [FrameLowPair.pi_lower])
    have hA := mul_le_mul_of_nonneg_right ha.1.le ht.2.2.1
    have hB := mul_le_mul_of_nonneg_right hb.1.le ht.1
    have hlabel := (label_bounds core_diagonal_state).2
    dsimp [trigAffine,C]
    nlinarith [FrameHighArc.diagonal_bounds.2,Arithmetic.pi_hand_enclosure.1]
  by_cases hq : x≤Real.pi/2
  · have hh := hm1 ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩ ⟨hx.1,hq⟩ hx.1
    rw [← he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩,
      ← he1 ⟨by linarith [hx.1],hq⟩] at hh
    exact hstart.trans_le hh
  · have h1 := hm1 ⟨le_rfl,by linarith [FrameLowPair.pi_lower]⟩
      ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ (by linarith [FrameLowPair.pi_lower])
    have h2 := hm2 ⟨le_rfl,by linarith [Real.pi_pos]⟩
      ⟨(lt_of_not_ge hq).le,hx.2⟩ (lt_of_not_ge hq).le
    rw [← he1 ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩,
      ← he1 ⟨by positivity,le_rfl⟩] at h1
    rw [← he2 ⟨le_rfl,by linarith [Real.pi_pos]⟩,
      ← he2 ⟨(lt_of_not_ge hq).le,hx.2⟩] at h2
    exact hstart.trans_le (h1.trans h2)

end SquaresInCircles.Eight.TableFree.FrameCoreHighHighSecondaryScalars
