module

public import SquaresInCircles.Eight.Owners.GA.HybridConcentration
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveASupport

/-!
# Eight squares: the two original E-primary errors with nonnegative signed total

Both multipliers
are equal. The same original E point receives both signed forces;
only their angular arguments are deleted in the analytic comparison.
The single DE and EH endpoints retain their different tangent signs.
-/

section
/-!
## Combining the two A-primary errors

The errors may have opposite signs. Their signed sum is the argument of the single-primary support
charge `TwoPositive.ASupport.charge` (`actual_charge`); no witness changes.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.PairedA
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
  have hder (d : ℝ) : HasDerivAt (sameSign A b a)
      (-(Real.cos (a/2)+Real.sin (a/2)-2*A*Real.sin (a/2))*Real.sin d-
        2*b*Real.sin (a/2)*Real.cos d) d := by
    have hh := (((Real.hasDerivAt_cos d).const_mul
      (Real.cos (a/2)+Real.sin (a/2)-2*A*Real.sin (a/2))).fun_sub
      ((Real.hasDerivAt_sin d).const_mul (2*b*Real.sin (a/2)))).sub_const 1
    exact (show HasDerivAt (sameSign A b a) _ d from hh).congr_deriv (by ring)
  apply antiOn_of_hasDeriv_nonpos (fun d _ => (hder d).continuousAt.continuousWithinAt)
    (fun d _ => hder d)
  · intro d hd
    have hd' : d∈Icc 0 frameCap := by
      have := ha.2
      simp only [frameCap] at this ⊢
      constructor <;> linarith [hd.1,hd.2]
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hd'
    have h₁ := mul_nonneg hcoef.le hs0
    have h₂ := mul_nonneg (mul_nonneg (by linarith : 0≤2*b) hS0) (by linarith : 0≤Real.cos d)
    linarith

theorem oppositeSign_monotone {A b a : ℝ}
    (hb : 0≤b ∧ b<9/10) (hAb : b≤A) (ha : a∈Icc 0 frameCap) :
    MonotoneOn (oppositeSign A b a) (Icc 0 frameCap) := by
  obtain ⟨hC,hS0,hS⟩ := half_reserves ha
  have hcoef : 0<Real.cos (a/2)-2*b*Real.sin (a/2) := by
    have hm := mul_le_mul_of_nonneg_right hb.2.le hS0
    nlinarith
  have hder (d : ℝ) : HasDerivAt (oppositeSign A b a)
      (-(Real.cos (a/2)-2*A*Real.sin (a/2))*Real.sin d+
        (Real.cos (a/2)-2*b*Real.sin (a/2))*Real.cos d) d := by
    have hh := (((Real.hasDerivAt_cos d).const_mul
      (Real.cos (a/2)-2*A*Real.sin (a/2))).fun_add
      ((Real.hasDerivAt_sin d).const_mul
        (Real.cos (a/2)-2*b*Real.sin (a/2)))).sub_const 1
    exact (show HasDerivAt (oppositeSign A b a) _ d from hh).congr_deriv (by ring)
  apply monoOn_of_hasDeriv_nonneg (fun d _ => (hder d).continuousAt.continuousWithinAt)
    (fun d _ => hder d)
  · intro d hd
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ⟨hd.1.le,hd.2.le⟩
    have h₁ := mul_nonneg hcoef.le (sub_nonneg.mpr hsc.le)
    have h₂ := mul_nonneg (mul_nonneg (by linarith : 0≤2*(A-b)) hS0) hs0
    linarith only [h₁,h₂]

theorem sameSign_endpoint {A b a : ℝ} (ha : a∈Icc 0 frameCap) :
    sameSign A b a (a/2)=endpoint A b a := by
  have hh := double_angle a
  rw [endpoint,edgeWidth_positive_formula ha]
  dsimp only [sameSign]
  linear_combination (A-1/2)*hh.1+(1/2+b)*hh.2+Real.sin_sq_add_cos_sq (a/2)

theorem oppositeSign_endpoint {A b a : ℝ} (ha : a∈Icc 0 frameCap) :
    oppositeSign A b a (a/2)=endpoint A b a := by
  have hh := double_angle a
  rw [endpoint,edgeWidth_positive_formula ha]
  dsimp only [oppositeSign]
  linear_combination (A-1/2)*hh.1+(1/2+b)*hh.2+Real.sin_sq_add_cos_sq (a/2)

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
  have hd : (u-v)/2∈Icc 0 frameCap := by
    have huu := (abs_le.mp hu).2
    have hvl := (abs_le.mp hv).1
    simp only [frameCap] at huu hvl ⊢
    constructor <;> linarith
  have hu0 : 0≤u := by linarith [ha.1]
  have huc : u∈Icc 0 frameCap := ⟨hu0,(abs_le.mp hu).2⟩
  have hhalf : (u+v)/2∈Icc 0 frameCap := by
    have h1 := ha.1
    have h2 := ha.2
    simp only [frameCap] at h2 ⊢
    constructor <;> linarith
  obtain ⟨hsum,hdiff,hcos,hsdiff⟩ := signed_sum_identities u v
  have hsign : 0≤Real.cos v-Real.cos u := by
    rw [hdiff]
    exact mul_nonneg (mul_nonneg (by norm_num) (half_trig ha).1)
      (transport_trig hd).2.2.1
  rw [lowerWork,abs_of_nonneg hsign]
  by_cases hv0 : 0≤v
  · have hvc : v∈Icc 0 frameCap := ⟨hv0,(abs_le.mp hv).2⟩
    have hda : (u-v)/2≤(u+v)/2 := by linarith
    have hm := sameSign_antitone hA hb.1 ha
      ⟨hd.1,hda⟩ ⟨by linarith [ha.1],le_rfl⟩ hda
    rw [sameSign_endpoint ha] at hm
    rw [edgeWidth_positive_formula huc,edgeWidth_positive_formula hvc]
    have hid : (1+Real.cos u+Real.sin u)/2+
        (1+Real.cos v+Real.sin v)/2-2-A*(Real.sin u+Real.sin v)-
        b*(Real.cos v-Real.cos u)=sameSign A b (u+v) ((u-v)/2) := by
      dsimp only [sameSign]
      linear_combination (1/2)*hcos+(1/2-A)*hsum-b*hdiff
    rw [hid]
    exact hm
  · have hvc : -v∈Icc 0 frameCap :=
      ⟨by linarith,by linarith [(abs_le.mp hv).1]⟩
    have had : (u+v)/2≤(u-v)/2 := by linarith
    have hm := oppositeSign_monotone hb hAb ha hhalf hd had
    rw [oppositeSign_endpoint ha] at hm
    have hwv : edgeWidth v=(1+Real.cos v-Real.sin v)/2 := by
      have hh := edgeWidth_negative_formula hvc
      rw [neg_neg,Real.cos_neg,Real.sin_neg] at hh
      rw [hh]
      ring
    rw [edgeWidth_positive_formula huc,hwv]
    have hid : (1+Real.cos u+Real.sin u)/2+
        (1+Real.cos v-Real.sin v)/2-2-A*(Real.sin u+Real.sin v)-
        b*(Real.cos v-Real.cos u)=oppositeSign A b (u+v) ((u-v)/2) := by
      dsimp only [oppositeSign]
      linear_combination (1/2)*hcos+(1/2)*hsdiff-A*hsum-b*hdiff
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

/-- The stronger comparison, made before the support bound. -/
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
  have hsigned : P.y*(Real.cos v-Real.cos u)≤|P.y| *|Real.cos v-Real.cos u| := by
    calc
      _ ≤ |P.y*(Real.cos v-Real.cos u)| := le_abs_self _
      _ = _ := abs_mul _ _
  dsimp [lowerWork,work] at *
  linarith

/-- The support charge of the sum `u + v` is at most `work P u v`, with both signed errors and the
state `P` of A. -/
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
  simp only [↓reduceIte] at hsupport
  have hsigned : P.y*(Real.cos v-Real.cos u)≤|P.y| * |Real.cos v-Real.cos u| := by
    calc
      _ ≤ |P.y*(Real.cos v-Real.cos u)| := le_abs_self _
      _ = _ := abs_mul _ _
  dsimp only [P',endpoint,lowerWork,work] at hpair hsupport hsigned ⊢
  linarith

end SquaresInCircles.Eight.GlobalGA.PairedA
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.PairedE
open Candidate Secondary

def selected (p : Bool) (d : ℝ) : ℝ := if p then d else 0
def total (de eh : Bool) (u v : ℝ) : ℝ := selected de u+selected eh v

def primaryGain (P : SignedPoint) (de eh : Bool) (u v : ℝ) : ℝ :=
  (if de then edgeWidth u-1-(P.a*Real.sin u+P.y*(1-Real.cos u)) else 0)+
  (if eh then edgeWidth v-1-(P.a*Real.sin v+P.y*(Real.cos v-1)) else 0)

theorem paired_identity (P : SignedPoint) (u v : ℝ) :
    primaryGain P true true u v=PairedA.work P u v := by
  simp only [primaryGain,ite_true,PairedA.work]
  ring

/-- Equation (6), applied to the actual signed E state. It includes
opposite individual signs and zero signed total. -/
theorem paired_charge {q u v : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap) (he : u+v∈Icc 0 frameCap) :
    TwoPositive.ASupport.charge (u+v)≤primaryGain P true true u v := by
  rw [paired_identity]
  exact PairedA.actual_charge hs hc hq hu hv he

/-- All three designated primary cases, and the empty case, have the
same lower charge at their selected signed total. -/
theorem selected_charge {q u v : ℝ} {P : SignedPoint} (de eh : Bool)
    (hs : P.Sorted) (hc : P.Contained q) (hq : q≤qCap)
    (hu : |u|≤frameCap) (hv : |v|≤frameCap)
    (he : total de eh u v∈Icc 0 frameCap) :
    TwoPositive.ASupport.charge (total de eh u v)≤primaryGain P de eh u v := by
  cases de <;> cases eh
  · simp [total,selected,primaryGain]
  · have ht : v∈Icc 0 frameCap := by simpa [total,selected] using he
    simpa [total,selected,primaryGain] using
      TwoPositive.ASupport.actual_charge hs hc hq ht false
  · have ht : u∈Icc 0 frameCap := by simpa [total,selected] using he
    simpa [total,selected,primaryGain] using
      TwoPositive.ASupport.actual_charge hs hc hq ht true
  · exact paired_charge hs hc hq hu hv (by simpa [total,selected] using he)

theorem charge_ge_circle {e : ℝ} (he : e∈Icc 0 frameCap) :
    TwoPositive.ASupport.circleCharge e≤TwoPositive.ASupport.charge e := by
  by_cases hcut : e≤TwoPositive.ASupport.alpha
  · have hh := TwoPositive.ASupport.charge_difference e
    have hp := mul_nonneg
      (mul_nonneg (show 0≤2*R by linarith [radius_bounds.1])
        (TwoPositive.ASupport.half_trig he).1)
      (sub_nonneg.mpr (Real.cos_le_one ((e-TwoPositive.ASupport.alpha)/2)))
    simp only [TwoPositive.ASupport.charge,hcut,↓reduceIte]
    linarith
  · simp [TwoPositive.ASupport.charge,hcut]

/-- The exact Taylor reserve in (17), on the whole interval. -/
theorem charge_linear_reserve {e : ℝ} (he : e∈Icc 0 frameCap) :
    -(1021/1000)*e+(3138807/6400000000)*e≤TwoPositive.ASupport.charge e := by
  have hR : R≤1979/1000 := by linarith [radius_bounds.2]
  have hs := Real.sin_ge_sub_cube he.1
  have hhalf := sin_upper_five (show 0≤e/2 by linarith [he.1])
  have hRp := mul_le_mul_of_nonneg_right hR (TwoPositive.ASupport.half_trig he).1
  have hupper := mul_le_mul_of_nonneg_left hhalf
    (show (0:ℝ)≤2*(1979/1000) by norm_num)
  have hpoly : (1-(1979/1000))*e+
      ((1979/1000)/24-1/6)*e^3-((1979/1000)/1920)*e^5≤
      TwoPositive.ASupport.circleCharge e := by
    dsimp [TwoPositive.ASupport.circleCharge]
    nlinarith only [hs,hRp,hupper]
  have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ he.1 he.2 2) he.1
  have h4 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ he.1 he.2 4) he.1
  have hbound : -(1021/1000)*e+(3138807/6400000000)*e≤
      (1-(1979/1000))*e+((1979/1000)/24-1/6)*e^3-
        ((1979/1000)/1920)*e^5 := by
    norm_num [frameCap] at h2 h4
    nlinarith only [h2,h4]
  exact hbound.trans (hpoly.trans (charge_ge_circle he))

theorem charge_linear {e : ℝ} (he : e∈Icc 0 frameCap) :
    -(1021/1000)*e≤TwoPositive.ASupport.charge e := by
  have hh := charge_linear_reserve he
  have hp := mul_nonneg (by norm_num : (0:ℝ)≤3138807/6400000000) he.1
  linarith

theorem selected_positive_le (p : Bool) (d : ℝ) :
    positivePart (selected p d)≤positivePart d := by
  cases p
  · simpa [selected] using positivePart_nonneg d
  · simp [selected]

theorem selected_negative_le (p : Bool) (d : ℝ) :
    negativePart (selected p d)≤negativePart d := by
  cases p
  · simpa [selected] using negativePart_nonneg d
  · simp [selected]

theorem total_bounds {u v : ℝ} (de eh : Bool)
    (hp : positivePart u+positivePart v≤frameCap)
    (hn : negativePart u+negativePart v≤frameCap)
    (he : 0≤total de eh u v) : total de eh u v∈Icc 0 frameCap := by
  have hpe := (add_le_add (selected_positive_le de u) (selected_positive_le eh v)).trans hp
  have hne := (add_le_add (selected_negative_le de u) (selected_negative_le eh v)).trans hn
  have hb := (pair_error_bounds hpe hne).2.2
  exact ⟨he,(le_abs_self _).trans hb⟩

def cycleTotal (C : SignedCycle) (de eh : Bool) : ℝ :=
  total de eh (delta C.theta D) (delta C.theta E)

theorem cycle_total_bounds {C : SignedCycle} (de eh : Bool)
    (hvar : positiveVariation C.theta≤frameCap) (he : 0≤cycleTotal C de eh) :
    cycleTotal C de eh∈Icc 0 frameCap := by
  have hn : negativeVariation C.theta≤frameCap := by rw [← variations_equal]; exact hvar
  have hb := original_pair_budgets (i:=D) (j:=E) hvar hn (by norm_num [D,E])
  exact total_bounds de eh hb.1 hb.2 he

end SquaresInCircles.Eight.GlobalGA.PairedE
end
end
end
