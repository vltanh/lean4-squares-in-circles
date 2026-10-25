module

public import SquaresInCircles.Eight.Owners.GA.ActualPairs
public import SquaresInCircles.Eight.Owners.GA.Paired.ACharge

/-!
# Eight squares: the two original E-primary errors with nonnegative signed total

Both multipliers
are equal. The same original E point receives both signed forces;
only their angular arguments are deleted in the analytic comparison.
The single DE and EH endpoints retain their different tangent signs.
-/

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
