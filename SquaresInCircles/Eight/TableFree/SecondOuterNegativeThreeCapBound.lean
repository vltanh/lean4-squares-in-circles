module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeCapValues
public import SquaresInCircles.Eight.TableFree.SecondOuterConcaveSlope

/-!
# The complete sharp angle-cap contact bound

One tangent parabola proves the cost bound on `[0,.4]`.  Thereafter the
first derivative is concave and starts positive, so only the two true
endpoint costs can minimize the value.  The physical source interval
and its diagonal-target end are constructed by the original contact.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Cap

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.CapCurve (height Domain before target_mem)

lemma early_curvature {b : ℝ} (hb : b∈Icc 0 (2/5)) : (6/25:ℝ)≤ second b := by
  have hh := second_antitone four_domain hb (show (2/5:ℝ)∈Icc 0 (2/5) by norm_num) hb.2
  exact four_second.le.trans hh

lemma early_value {b : ℝ} (hb : b∈Icc 0 (2/5)) : (44889/50000:ℝ)<cost b := by
  have hr : reference∈Icc 0 (2/5) := by norm_num [reference]
  have ht := curvature_tangent (κ := (6/25:ℝ)) hb hr
    (fun t ht => cost_hasDerivAt (before four_domain ht))
    (fun t ht => first_hasDerivAt (before four_domain ht))
    (fun t ht => early_curvature ht)
  have hd := abs_lt.mp reference_first
  have hsq : (first reference)^2<(1/1000000000000:ℝ) := by nlinarith
  have hc := sq_nonneg ((6/25)*(b-reference)+first reference)
  nlinarith [reference_value]

theorem cost_lower {b : ℝ} (hb : Domain b) : (44889/50000:ℝ)<cost b := by
  rcases le_total b (2/5) with h | h
  · exact early_value ⟨hb.1.1,h⟩
  · obtain ⟨e,he,hc⟩ := true_endpoint
    have hed := endpoint_domain he hc
    have hbe := source_bounded_by_end hb he hc
    have hdom (t : ℝ) (ht : t∈Icc (2/5) e) : Domain t :=
      before hed ⟨by linarith [ht.1],ht.2⟩
    have hm := MinimumCalculus.endpoint_minimum_of_third_nonpos
      (show b∈Icc (2/5) e from ⟨h,hbe⟩)
      (fun t ht => cost_hasDerivAt (hdom t ht))
      (fun t ht => first_hasDerivAt (hdom t ht))
      (fun t ht => second_hasDerivAt (hdom t ht))
      (fun t ht => by linarith [third_upper (hdom t ht)])
      (show 0<first (2/5) by linarith [four_first])
    exact (lt_min (early_value (by norm_num)) (by linarith [endpoint_value he hc])).trans_le hm

theorem original_contact {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hc : NegativeTwo.TargetContact.B b (7/10)=B) :
    (44889/50000:ℝ)<value b B (Real.pi/2-7/10) := by
  have hd : Domain b := ⟨hb,by simpa only [height,hc] using hB.2⟩
  simpa only [cost,height,hc] using cost_lower hd

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Cap
