module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoCapValues
public import SquaresInCircles.Eight.TableFree.SecondOuterMinimumCalculus

/-!
# The entire endpoint-angle contact has a strict scalar reserve

The whole-curve fourth derivative controls the initial concavity and
the later increasing curvature.  One tangent parabola at `.72365`
bounds the entire final interval, including its unknown feasible end.
The theorem below retains the actual original contact equation.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic

lemma early_second {b : ℝ} (hb : b∈Icc 0 (1/5)) : second b<0 := by
  have hh := concave_gt_of_endpoints (negative_second_concave two_domain) hb
    (show (0:ℝ)< -second 0 by linarith [zero_second])
    (show (0:ℝ)< -second (1/5) by linarith [two_second])
  linarith

lemma early_value {b : ℝ} (hb : b∈Icc 0 (1/5)) : (9/10:ℝ)<cost b := by
  have hc := concave_of_deriv2
    (fun t ht => cost_hasDerivAt (before two_domain ht))
    (fun t ht => first_hasDerivAt (before two_domain ht))
    (fun t ht => (early_second ht).le)
  exact concave_gt_of_endpoints hc hb zero_value two_value

lemma tail_second_monotone {b : ℝ} (hb : Domain b) (hstart : (1/5:ℝ)≤b) :
    MonotoneOn second (Icc (1/5) b) := by
  have hdom (t : ℝ) (ht : t∈Icc (1/5) b) : Domain t :=
    before hb ⟨by linarith [ht.1],ht.2⟩
  have hthird (t : ℝ) (ht : t∈Icc (1/5) b) : 0<third t := by
    have hm := third_monotone hb (show (1/5:ℝ)∈Icc 0 b by exact ⟨by norm_num,hstart⟩)
      (show t∈Icc 0 b from ⟨by linarith [ht.1],ht.2⟩) ht.1
    linarith [two_third]
  exact monoOn_of_hasDeriv_nonneg
    (fun t ht => (second_hasDerivAt (hdom t ht)).continuousAt.continuousWithinAt)
    (fun t ht => second_hasDerivAt (hdom t (Ioo_subset_Icc_self ht)))
    (fun t ht => (hthird t (Ioo_subset_Icc_self ht)).le)

lemma middle_value {b : ℝ} (hb : b∈Icc (1/5) (3/5)) : (9/10:ℝ)<cost b := by
  have hdom (t : ℝ) (ht : t∈Icc (1/5) (3/5)) : Domain t :=
    before six_domain ⟨by linarith [ht.1],ht.2⟩
  have hthird (t : ℝ) (ht : t∈Icc (1/5) (3/5)) : 0≤third t := by
    have hm := third_monotone six_domain
      (show (1/5:ℝ)∈Icc 0 (3/5) by norm_num)
      (show t∈Icc 0 (3/5) from ⟨by linarith [ht.1],ht.2⟩) ht.1
    linarith [two_third]
  have hm := MinimumCalculus.endpoint_minimum hb
    (fun t ht => cost_hasDerivAt (hdom t ht))
    (fun t ht => first_hasDerivAt (hdom t ht))
    (fun t ht => second_hasDerivAt (hdom t ht))
    hthird six_first
  have hends : (9/10:ℝ)< min (cost (1/5)) (cost (3/5)) :=
    lt_min two_value (by linarith [six_value])
  exact hends.trans_le hm

lemma final_value {b : ℝ} (hb : Domain b) (hsix : (3/5:ℝ)≤b) :
    (44889/50000:ℝ)<cost b := by
  let u : ℝ := max b (14473/20000)
  have hu : Domain u := by
    rcases le_total b (14473/20000) with h | h
    · simpa only [u,max_eq_right h] using reference_domain
    · simpa only [u,max_eq_left h] using hb
  have hum : (3/5:ℝ)≤u := hsix.trans (le_max_left _ _)
  have hx : b∈Icc (3/5) u := ⟨hsix,le_max_left _ _⟩
  have ht : (14473/20000:ℝ)∈Icc (3/5) u := ⟨by norm_num,le_max_right _ _⟩
  have hdom (t : ℝ) (ht : t∈Icc (3/5) u) : Domain t :=
    before hu ⟨by linarith [ht.1],ht.2⟩
  have hcurv (t : ℝ) (ht : t∈Icc (3/5) u) : (13/20:ℝ)≤ second t := by
    have hm := tail_second_monotone hu (by linarith : (1/5:ℝ)≤u)
      (show (3/5:ℝ)∈Icc (1/5) u from ⟨by norm_num,hum⟩)
      (show t∈Icc (1/5) u from ⟨by linarith [ht.1],ht.2⟩) ht.1
    exact six_second.le.trans hm
  have htan := curvature_tangent (κ := (13/20:ℝ)) hx ht
    (fun t ht => cost_hasDerivAt (hdom t ht))
    (fun t ht => first_hasDerivAt (hdom t ht)) hcurv
  have hsmall := abs_lt.mp reference_first
  have hsq : (first (14473/20000))^2<(1/1000000000000:ℝ) := by
    nlinarith
  have hcomplete := sq_nonneg ((13/20)*(b-14473/20000)+first (14473/20000))
  nlinarith [reference_value]

theorem cost_lower {b : ℝ} (hb : Domain b) : (44889/50000:ℝ)<cost b := by
  rcases le_total b (1/5) with htwo | htwo
  · have hh := early_value ⟨hb.1.1,htwo⟩
    linarith
  · rcases le_total b (3/5) with hsix | hsix
    · have hh := middle_value ⟨htwo,hsix⟩
      linarith
    · exact final_value hb hsix

theorem original_contact {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hc : TargetContact.B b (7/10)=B) :
    (44889/50000:ℝ)<value b B (Real.pi/2-7/10) := by
  have hd : Domain b := ⟨hb,by simpa only [height,hc] using hB.2⟩
  simpa only [cost,height,hc] using cost_lower hd

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.CapCurve
