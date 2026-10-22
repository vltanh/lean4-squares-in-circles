module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterPositiveInterior

/-!
# One aligned circle tangent over the entire upper half

Uncompiled transcription of section 2.4. The source multiplier is the
maximum of the target slope and the tangent at primary coordinate one.
The core support is the minimum of two increasing smooth functions;
this retains the support kink and both core pieces without an angle
partition. Its aligned value is exactly K(0) or the interior F(0).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
open CommonQuarter CorePairGeometry Arithmetic

def alignedLam (r : Row) : ℝ := max (ocG r) (Md r (3/2))
def circleSupport (r : Row) (w : ℝ) : ℝ :=
  (w-ocP r+ocQ r)/2-radius*Real.sqrt ((w-ocP r)^2+(ocQ r)^2)
def upperBase (r : Row) (x : ℝ) : ℝ := Real.pi/2+x+ocC r+circleSupport r (alignedLam r)+
  alignedLam r/2+(alignedLam r/2)*Real.cos x-(alignedLam r/12)*Real.sin x
def upperActive (r : Row) (x : ℝ) : ℝ :=
  upperBase r x-CoreAngleEndpoint.diagonal*(ocG r-alignedLam r*Real.cos x)
def G (r : Row) (x : ℝ) : ℝ :=
  upperBase r x-CoreAngleEndpoint.diagonal*max 0 (ocG r-alignedLam r*Real.cos x)
def upperBaseD (r : Row) (x : ℝ) : ℝ :=
  1-(alignedLam r/2)*Real.sin x-(alignedLam r/12)*Real.cos x
def upperActiveD (r : Row) (x : ℝ) : ℝ :=
  1-alignedLam r*(CoreAngleEndpoint.diagonal+1/2)*Real.sin x-(alignedLam r/12)*Real.cos x

theorem alignedLam_bounds (r : Row) (hr : Rows r) :
    0<alignedLam r ∧ ocG r≤alignedLam r ∧ alignedLam r<57/50 :=
  ⟨(coefficients r hr).2.2.2.1.trans_le (le_max_left _ _),le_max_left _ _,
    Reference.aligned_multiplier r hr⟩

theorem upperBase_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (upperBase r) (upperBaseD r x) x := by
  have hh := (((((hasDerivAt_id x).const_add (Real.pi/2)).add_const (ocC r)).
    add_const (circleSupport r (alignedLam r))).add_const (alignedLam r/2)).
      add ((Real.hasDerivAt_cos x).const_mul (alignedLam r/2))
  convert hh.sub ((Real.hasDerivAt_sin x).const_mul (alignedLam r/12)) using 1 <;>
    dsimp [upperBase,upperBaseD] <;> ring

theorem upperActive_hasDerivAt (r : Row) (x : ℝ) :
    HasDerivAt (upperActive r) (upperActiveD r x) x := by
  have hh := (upperBase_hasDerivAt r x).sub
    ((((Real.hasDerivAt_cos x).const_mul (alignedLam r)).const_sub (ocG r)).
      const_mul CoreAngleEndpoint.diagonal)
  convert hh using 1 <;> dsimp [upperActive,upperActiveD,upperBaseD] <;> ring

theorem upper_derivatives_positive (r : Row) (hr : Rows r) {x : ℝ}
    (hx : x∈Icc 0 (7/10)) : 0<upperBaseD r x ∧ 0<upperActiveD r x := by
  have hw := alignedLam_bounds r hr
  have tr := positive_trig hx
  have hk : 0≤Real.cos x := by linarith [tr.1]
  have hd0 : 0≤CoreAngleEndpoint.diagonal+1/2 := by linarith [CoreAngleEndpoint.diagonal_bounds.1]
  have hd1 : CoreAngleEndpoint.diagonal+1/2≤1059/1000 := by linarith [CoreAngleEndpoint.diagonal_bounds.2]
  have hws := mul_le_mul hw.2.2.le tr.2.2.2.1.le tr.2.2.1 (by norm_num : (0:ℝ)≤57/50)
  have hwk := mul_le_mul hw.2.2.le (Real.cos_le_one x) hk (by norm_num : (0:ℝ)≤57/50)
  have hwd := mul_le_mul hw.2.2.le hd1 hd0 (by norm_num : (0:ℝ)≤57/50)
  have hwds := mul_le_mul hwd tr.2.2.2.1.le tr.2.2.1
    (by norm_num : (0:ℝ)≤(57/50)*(1059/1000))
  constructor <;> dsimp [upperBaseD,upperActiveD] <;> nlinarith

theorem G_eq_min (r : Row) (x : ℝ) : G r x=min (upperBase r x) (upperActive r x) := by
  have hd : 0≤CoreAngleEndpoint.diagonal := by linarith [CoreAngleEndpoint.diagonal_bounds.1]
  by_cases ht : 0≤ocG r-alignedLam r*Real.cos x
  · rw [G,max_eq_right ht,min_eq_right]
    · rfl
    · dsimp [upperActive]
      exact sub_le_self _ (mul_nonneg hd ht)
  · have ht' : ocG r-alignedLam r*Real.cos x≤0 := (lt_of_not_ge ht).le
    rw [G,max_eq_left ht',mul_zero,sub_zero,min_eq_left]
    dsimp [upperActive]
    have hh := mul_nonpos_of_nonneg_of_nonpos hd ht'
    linarith

theorem G_monotone (r : Row) (hr : Rows r) : MonotoneOn (G r) (Icc 0 (7/10)) := by
  have hb : MonotoneOn (upperBase r) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
    (fun x _ => (upperBase_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => upperBase_hasDerivAt r x)
    (fun x hx => (upper_derivatives_positive r hr (Ioo_subset_Icc_self hx)).1.le)
  have ha : MonotoneOn (upperActive r) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
    (fun x _ => (upperActive_hasDerivAt r x).continuousAt.continuousWithinAt)
    (fun x _ => upperActive_hasDerivAt r x)
    (fun x hx => (upper_derivatives_positive r hr (Ioo_subset_Icc_self hx)).2.le)
  intro x hx y hy hxy
  rw [G_eq_min,G_eq_min]
  exact min_le_min (hb hx hy hxy) (ha hx hy hxy)

theorem G_zero_formula (r : Row) :
    G r 0=Real.pi/2+ocC r+circleSupport r (alignedLam r)+alignedLam r := by
  have hh : ocG r-alignedLam r≤0 := sub_nonpos.mpr (le_max_left _ _)
  simp only [G,upperBase,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero,add_zero]
  rw [max_eq_left hh]
  ring

theorem G_zero_lower (r : Row) (hr : Rows r) : (449/500:ℝ)<G r 0 := by
  rw [G_zero_formula]
  by_cases hg : ocG r≤Md r (3/2)
  · have hw : alignedLam r=Md r (3/2) := max_eq_right hg
    have hs := circle_tangent r hr (show (3/2:ℝ)∈coordinateDomain by norm_num [coordinateDomain]) rfl
    change circleSupport r (Md r (3/2))=M r (3/2)-Md r (3/2)*(3/2-1/2) at hs
    rw [hw,hs]
    have hK := axial_lower r hr (show (0:ℝ)∈angleDomain by norm_num [angleDomain,cap])
    simp only [K,U,Real.sin_zero,Real.cos_zero,mul_zero,add_zero,sub_zero] at hK
    linarith
  · have hg' : Md r (3/2)<ocG r := lt_of_not_ge hg
    have hw : alignedLam r=ocG r := max_eq_left hg'.le
    have hi : Interior r := by
      by_contra hn
      have hh := (Reference.initial_event r hr).2 hn
      simp only [H,U,Real.sin_zero,Real.cos_zero,mul_zero,add_zero,mul_one] at hh
      norm_num at hh
      linarith
    rw [hw]
    have hh := Reference.aligned_interior r hr hi
    dsimp [Reference.alignedInterior,circleSupport] at hh ⊢
    linarith

theorem original_ge_upper (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle true x)) :
    G r x≤outerCoreCost r a b A B (angle true x) := by
  have hw := alignedLam_bounds r hr
  have tr := positive_trig hx
  obtain ⟨hA0,hA,hB0,hBA,hB⟩ := CoreAngleEndpoint.state_bounds ht
  have hsep := hm
  rw [sourcePrimary,angle_width true hx,angle_cos,angle_sin,targetSign_positive hr.2] at hsep
  dsimp [direction] at hsep
  have hp := mul_le_mul_of_nonneg_left hsep hw.1.le
  have hcircle := outer_circle_lower (X:=ocP r-alignedLam r) (Y:=-(ocQ r)) hs
  have hnorm : (ocP r-alignedLam r)^2+(-(ocQ r))^2=
      (alignedLam r-ocP r)^2+(ocQ r)^2 := by ring
  rw [hnorm] at hcircle
  have hAcost := mul_le_mul_of_nonneg_right hA (mul_nonneg hw.1.le tr.2.2.1)
  have hm0 : 0≤max 0 (ocG r-alignedLam r*Real.cos x) := le_max_left _ _
  have hBm := mul_le_mul_of_nonneg_right hB hm0
  have hcoef := mul_le_mul_of_nonneg_right (le_max_right 0 (ocG r-alignedLam r*Real.cos x)) hB0
  have hBcost : -CoreAngleEndpoint.diagonal*max 0 (ocG r-alignedLam r*Real.cos x)≤
      (alignedLam r*Real.cos x-ocG r)*B := by nlinarith only [hBm,hcoef]
  dsimp [G,upperBase,circleSupport,outerCoreCost,angle,direction,sourceSign,targetSign,WordProblems.sign]
  rw [hr.1,hr.2]
  nlinarith only [hp,hcircle,hAcost,hBcost]

theorem original_upper (r : Row) (hr : Rows r) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : sourcePrimary r a b A B (angle true x)) :
    (449/500:ℝ)<outerCoreCost r a b A B (angle true x) :=
  (G_zero_lower r hr).trans_le
    (((G_monotone r hr) (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hx hx.1).trans
      (original_ge_upper r hr hs ht hx hm))

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterPositive
