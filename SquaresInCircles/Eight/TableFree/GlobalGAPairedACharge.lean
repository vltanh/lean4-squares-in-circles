module

public import SquaresInCircles.Eight.TableFree.GlobalGATwoPositiveASupport

/-!
# Combining the two original A-primary errors

Uncompiled transcription of Sections 1 and 2 of
`HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md`. The errors may have
opposite signs. Their signed sum is the argument of the already established
single-primary support charge; no original witness is replaced here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PairedA
open Candidate Secondary PositiveAngularEnvelope TwoPositive.ASupport

def lowerWork (A b u v : ℝ) : ℝ :=
  edgeWidth u+edgeWidth v-2-A*(Real.sin u+Real.sin v)-
    b*|Real.cos v-Real.cos u|

def endpoint (A b a : ℝ) : ℝ :=
  edgeWidth a-1-A*Real.sin a-b*(1-Real.cos a)

def sameSign (A b a d : ℝ) : ℝ :=
  (Real.cos (a/2)+Real.sin (a/2)-2*A*Real.sin (a/2))*Real.cos d-
    2*b*Real.sin (a/2)*Real.sin d-1

def oppositeSign (A b a d : ℝ) : ℝ :=
  (Real.cos (a/2)-2*A*Real.sin (a/2))*Real.cos d+
    (Real.cos (a/2)-2*b*Real.sin (a/2))*Real.sin d-1

theorem half_reserves {a : ℝ} (ha : a∈Icc 0 frameCap) :
    (939/1000:ℝ)<Real.cos (a/2) ∧
      0≤Real.sin (a/2) ∧ Real.sin (a/2)<343/1000 := by
  have hh := trig_bracket (l:=(0:ℝ)) (u:=(7/20:ℝ)) (x:=a/2)
    (by norm_num) (by linarith [Real.pi_gt_three])
    (by constructor <;> dsimp [frameCap] at ha ⊢ <;> linarith [ha.1,ha.2])
  norm_num at hh
  exact ⟨by linarith [hh.2.2.1],by linarith [hh.1],by linarith [hh.2.1]⟩

theorem sameSign_antitone {A b a : ℝ}
    (hA : 0≤A ∧ A<283/200) (hb : 0≤b) (ha : a∈Icc 0 frameCap) :
    AntitoneOn (sameSign A b a) (Icc 0 (a/2)) := by
  obtain ⟨hC,hS0,hS⟩ := half_reserves ha
  have hcoef : 0<Real.cos (a/2)+Real.sin (a/2)-2*A*Real.sin (a/2) := by
    have hm := mul_le_mul_of_nonneg_right hA.2.le hS0
    nlinarith
  apply antiOn_of_hasDeriv_nonpos (by dsimp [sameSign]; fun_prop)
  · intro d hd
    convert (((Real.hasDerivAt_cos d).const_mul
      (Real.cos (a/2)+Real.sin (a/2)-2*A*Real.sin (a/2))).sub
      ((Real.hasDerivAt_sin d).const_mul (2*b*Real.sin (a/2)))).sub_const 1
      using 1 <;> dsimp [sameSign] <;> ring
  · intro d hd
    have hd' : d∈Icc 0 frameCap := by
      constructor <;> dsimp [frameCap] at ha ⊢ <;> linarith [hd.1,hd.2,ha.2]
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hd'
    have h₁ := mul_nonneg hcoef.le hs0
    have h₂ := mul_nonneg (mul_nonneg (by linarith : 0≤2*b) hS0) hc.le
    linarith

theorem oppositeSign_monotone {A b a : ℝ}
    (hb : 0≤b ∧ b<9/10) (hAb : b≤A) (ha : a∈Icc 0 frameCap) :
    MonotoneOn (oppositeSign A b a) (Icc 0 frameCap) := by
  obtain ⟨hC,hS0,hS⟩ := half_reserves ha
  have hcoef : 0<Real.cos (a/2)-2*b*Real.sin (a/2) := by
    have hm := mul_le_mul_of_nonneg_right hb.2.le hS0
    nlinarith
  apply monoOn_of_hasDeriv_nonneg (by dsimp [oppositeSign]; fun_prop)
  · intro d hd
    convert (((Real.hasDerivAt_cos d).const_mul
      (Real.cos (a/2)-2*A*Real.sin (a/2))).add
      ((Real.hasDerivAt_sin d).const_mul
        (Real.cos (a/2)-2*b*Real.sin (a/2)))).sub_const 1
      using 1 <;> dsimp [oppositeSign] <;> ring
  · intro d hd
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ⟨hd.1.le,hd.2.le⟩
    have h₁ := mul_nonneg hcoef.le (sub_nonneg.mpr hsc.le)
    have h₂ := mul_nonneg (mul_nonneg (by linarith : 0≤2*(A-b)) hS0) hs0
    nlinarith only [h₁,h₂]

theorem sameSign_endpoint {A b a : ℝ} (ha : a∈Icc 0 frameCap) :
    sameSign A b a (a/2)=endpoint A b a := by
  have hh := double_angle a
  rw [endpoint,edgeWidth_positive_formula ha]
  dsimp [sameSign]
  nlinarith [Real.sin_sq_add_cos_sq (a/2)]

theorem oppositeSign_endpoint {A b a : ℝ} (ha : a∈Icc 0 frameCap) :
    oppositeSign A b a (a/2)=endpoint A b a := by
  have hh := double_angle a
  rw [endpoint,edgeWidth_positive_formula ha]
  dsimp [oppositeSign]
  nlinarith [Real.sin_sq_add_cos_sq (a/2)]

theorem signed_sum_identities (u v : ℝ) :
    Real.sin u+Real.sin v=2*Real.sin ((u+v)/2)*Real.cos ((u-v)/2) ∧
    Real.cos v-Real.cos u=2*Real.sin ((u+v)/2)*Real.sin ((u-v)/2) ∧
    Real.cos u+Real.cos v=2*Real.cos ((u+v)/2)*Real.cos ((u-v)/2) ∧
    Real.sin u-Real.sin v=2*Real.cos ((u+v)/2)*Real.sin ((u-v)/2) := by
  have hu : u=(u+v)/2+(u-v)/2 := by ring
  have hv : v=(u+v)/2-(u-v)/2 := by ring
  have hsu := (congrArg Real.sin hu).trans (Real.sin_add _ _)
  have hsv := (congrArg Real.sin hv).trans (Real.sin_sub _ _)
  have hcu := (congrArg Real.cos hu).trans (Real.cos_add _ _)
  have hcv := (congrArg Real.cos hv).trans (Real.cos_sub _ _)
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem ordered_lower {A b u v : ℝ}
    (hA : 0≤A ∧ A<283/200) (hb : 0≤b ∧ b<9/10) (hAb : b≤A)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (ha : u+v∈Icc 0 frameCap) (hvu : v≤u) :
    endpoint A b (u+v)≤lowerWork A b u v := by
  let a := u+v
  let d := (u-v)/2
  have ha' : a∈Icc 0 frameCap := ha
  have hd : d∈Icc 0 frameCap := by
    dsimp [d]
    have huu := (abs_le.mp hu).2
    have hvl := (abs_le.mp hv).1
    constructor <;> linarith
  have hu0 : 0≤u := by linarith [ha.1]
  have huc : u∈Icc 0 frameCap := ⟨hu0,(abs_le.mp hu).2⟩
  have hhalf : a/2∈Icc 0 frameCap := by
    constructor <;> dsimp [frameCap] at ha' ⊢ <;> linarith [ha'.1,ha'.2]
  obtain ⟨hsum,hdiff,hcos,hsdiff⟩ := signed_sum_identities u v
  have hsign : 0≤Real.cos v-Real.cos u := by
    rw [hdiff]
    exact mul_nonneg (mul_nonneg (by norm_num) (half_trig ha).1)
      (transport_trig hd).2.2.1
  rw [lowerWork,abs_of_nonneg hsign]
  by_cases hv0 : 0≤v
  · have hvc : v∈Icc 0 frameCap := ⟨hv0,(abs_le.mp hv).2⟩
    have hda : d≤a/2 := by dsimp [a,d]; linarith
    have hm := sameSign_antitone hA hb.1 ha'
      ⟨hd.1,hda⟩ ⟨by linarith [ha'.1],le_rfl⟩ hda
    rw [sameSign_endpoint ha'] at hm
    rw [edgeWidth_positive_formula huc,edgeWidth_positive_formula hvc]
    have hid : (1+Real.cos u+Real.sin u)/2+
        (1+Real.cos v+Real.sin v)/2-2-A*(Real.sin u+Real.sin v)-
        b*(Real.cos v-Real.cos u)=sameSign A b a d := by
      dsimp [sameSign,a,d]
      nlinarith only [hsum,hdiff,hcos]
    rw [hid]
    exact hm
  · have hvc : -v∈Icc 0 frameCap :=
      ⟨by linarith,by linarith [(abs_le.mp hv).1]⟩
    have had : a/2≤d := by dsimp [a,d]; linarith
    have hm := oppositeSign_monotone hb hAb ha' hhalf hd had
    rw [oppositeSign_endpoint ha'] at hm
    have hwv : edgeWidth v=(1+Real.cos v-Real.sin v)/2 := by
      have hh := edgeWidth_negative_formula hvc
      simpa only [neg_neg,Real.cos_neg,Real.sin_neg] using hh
    rw [edgeWidth_positive_formula huc,hwv]
    have hid : (1+Real.cos u+Real.sin u)/2+
        (1+Real.cos v-Real.sin v)/2-2-A*(Real.sin u+Real.sin v)-
        b*(Real.cos v-Real.cos u)=oppositeSign A b a d := by
      dsimp [oppositeSign,a,d]
      nlinarith only [hsdiff,hdiff,hcos,hsum]
    rw [hid]
    exact hm

theorem lowerWork_symm (A b u v : ℝ) : lowerWork A b u v=lowerWork A b v u := by
  simp only [lowerWork,abs_sub_comm (Real.cos v) (Real.cos u)]
  ring

/-- The local endpoint comparison, prior to the circle support bound. -/
theorem endpoint_lower {A b u v : ℝ}
    (hA : 0≤A ∧ A<283/200) (hb : 0≤b ∧ b<9/10) (hAb : b≤A)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (ha : u+v∈Icc 0 frameCap) :
    endpoint A b (u+v)≤lowerWork A b u v := by
  rcases le_total v u with h | h
  · exact ordered_lower hA hb hAb hu hv ha h
  · rw [lowerWork_symm]
    simpa [add_comm] using ordered_lower hA hb hAb hv hu (by simpa [add_comm] using ha) h

def work (P : SignedPoint) (u v : ℝ) : ℝ :=
  edgeWidth u+edgeWidth v-2-P.a*(Real.sin u+Real.sin v)-
    P.y*(Real.cos v-Real.cos u)

/-- The stronger comparison retained by the hand argument before support. -/
theorem actual_endpoint_lower {q u v : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (ha : u+v∈Icc 0 frameCap) :
    endpoint P.a |P.y| (u+v)≤work P u v := by
  let P' : SignedPoint := ⟨P.a,|P.y|⟩
  have hs' : P'.Sorted := by simpa [P',SignedPoint.Sorted] using hs
  have hc' : P'.Contained q := by
    simpa [P',SignedPoint.Contained,SignedPoint.circle] using hc
  have hb := actual_coordinate_bounds hs' (abs_nonneg P.y) hc' hq
  have hpair := endpoint_lower
    ⟨hs.1.le,by linarith [hb.1,axial_bounds.2]⟩
    ⟨abs_nonneg P.y,by linarith [hb.2.1,diagonal_bounds.2]⟩ hs.2 hu hv ha
  have hsigned : P.y*(Real.cos v-Real.cos u)≤|P.y|*|Real.cos v-Real.cos u| := by
    calc
      _ ≤ |P.y*(Real.cos v-Real.cos u)| := le_abs_self _
      _ = _ := abs_mul _ _
  dsimp [lowerWork,work] at *
  linarith

/-- Equation (4), with both original signed errors and the actual A state. -/
theorem actual_charge {q u v : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (ha : u+v∈Icc 0 frameCap) :
    TwoPositive.ASupport.charge (u+v)≤work P u v := by
  let P' : SignedPoint := ⟨P.a,|P.y|⟩
  have hs' : P'.Sorted := by simpa [P',SignedPoint.Sorted] using hs
  have hc' : P'.Contained q := by
    simpa [P',SignedPoint.Contained,SignedPoint.circle] using hc
  have hb := actual_coordinate_bounds hs' (abs_nonneg P.y) hc' hq
  have hpair := endpoint_lower
    ⟨hs.1.le,by linarith [hb.1,axial_bounds.2]⟩
    ⟨abs_nonneg P.y,by linarith [hb.2.1,diagonal_bounds.2]⟩ hs.2 hu hv ha
  have hsupport := TwoPositive.ASupport.actual_charge hs' hc' hq ha true
  have hsigned : P.y*(Real.cos v-Real.cos u)≤|P.y|*|Real.cos v-Real.cos u| := by
    calc
      _ ≤ |P.y*(Real.cos v-Real.cos u)| := le_abs_self _
      _ = _ := abs_mul _ _
  dsimp [P',endpoint,lowerWork,work] at *
  simp only [if_true] at hsupport
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.PairedA
