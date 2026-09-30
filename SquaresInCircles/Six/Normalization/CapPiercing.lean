module
public import SquaresInCircles.Six.Normalization.CapGeometry
public import SquaresInCircles.Six.Normalization.PiercingPolynomial

@[expose] public section

/-!
# K4: a common open piercing point for every square in a deep cap

The theorem uses actual square membership, not a bounding-box surrogate. Its
negative-angle case is a local reflection of one cap and its piercing point;
no global normalized packing, marker order, or reflection budget is changed.
The uniqueness corollary uses the original `InteriorDisjoint` predicate.

All source proof bodies remain pending compiler validation.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- K4 in a nonnegative nearest side frame. -/
theorem cap_piercing_nonneg {a b h t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hdisk : ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0, 0) R0 p)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1) :
    openSquare (orientedSquare t a b) (h + 1 / 2, 0) := by
  obtain ⟨ht', hab, hdepth, haR, hbU, hbhalf⟩ :=
    deep_cap_chart_bounds ht0 ht hh hdisk hcap
  have htr := small_cap_trig ht0 ht'.le
  have hh0 : 77 / 200 ≤ h := by linarith [coreRadius_gt_77_200]
  have hh' : h ≤ 5 / 8 := by linarith [rho0_upper]
  have ha0 : 0 ≤ a := by linarith
  have hZ : 0 ≤ h + 1 / 2 := by linarith
  have hnormal_lower := mul_le_mul
    (show (177 : ℝ) / 200 ≤ h + 1 / 2 by linarith)
    htr.1 (by norm_num : (0 : ℝ) ≤ 23 / 25) hZ
  have hnormal_upper := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hZ
  have htrans_upper := piercing_transverse_upper hh0 hh' (Real.cos_le_one t)
    htr.2.1 htr.2.2.1 hdepth
    (by simpa only [abs_of_nonneg ha0] using orientedSquare_containment hdisk)
    (orientedSquare_cap_support hcap)
  have htrans_nonneg := mul_nonneg hZ htr.2.1
  have hblo := (abs_le.mp hbU).1
  unfold openSquare
  rw [orientedSquare_localX, orientedSquare_localY]
  dsimp only
  constructor
  · apply abs_lt.mpr
    constructor <;> nlinarith [rho0_upper]
  · apply abs_lt.mpr
    constructor <;> nlinarith [U0_lt_half]

lemma orientedSquare_reflect_localX (t a b : ℝ) (p : Point) :
    localX (orientedSquare (-t) a (-b)) p =
      localX (orientedSquare t a b) (p.1, -p.2) := by
  simp only [orientedSquare_localX, Real.cos_neg, Real.sin_neg]
  ring

lemma orientedSquare_reflect_localY (t a b : ℝ) (p : Point) :
    localY (orientedSquare (-t) a (-b)) p =
      -localY (orientedSquare t a b) (p.1, -p.2) := by
  simp only [orientedSquare_localY, Real.cos_neg, Real.sin_neg]
  ring

lemma orientedSquare_reflect_closed (t a b : ℝ) (p : Point) :
    closedSquare (orientedSquare (-t) a (-b)) p ↔
      closedSquare (orientedSquare t a b) (p.1, -p.2) := by
  simp only [closedSquare, orientedSquare_reflect_localX,
    orientedSquare_reflect_localY, abs_neg]

lemma orientedSquare_reflect_open (t a b : ℝ) (p : Point) :
    openSquare (orientedSquare (-t) a (-b)) p ↔
      openSquare (orientedSquare t a b) (p.1, -p.2) := by
  simp only [openSquare, orientedSquare_reflect_localX,
    orientedSquare_reflect_localY, abs_neg]

lemma reflect_y_inDisk (p : Point) :
    inDisk (0, 0) R0 (p.1, -p.2) ↔ inDisk (0, 0) R0 p := by
  simp only [inDisk, normSq, sub, sub_zero, neg_sq]

/-- K4 with either sign of the nearest-frame angle; all hypotheses are geometric. -/
theorem cap_piercing {a b h t : ℝ}
    (ht : |t| ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hdisk : ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0, 0) R0 p)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1) :
    openSquare (orientedSquare t a b) (h + 1 / 2, 0) := by
  by_cases ht0 : 0 ≤ t
  · exact cap_piercing_nonneg ht0 ((le_abs_self t).trans ht) hh hdisk hcap
  · have htneg : t < 0 := lt_of_not_ge ht0
    have ht' : -t ≤ Real.pi / 4 := by simpa only [abs_of_neg htneg] using ht
    have hdisk' : ∀ p, closedSquare (orientedSquare (-t) a (-b)) p →
        inDisk (0, 0) R0 p := by
      intro p hp
      exact (reflect_y_inDisk p).mp
        (hdisk (p.1, -p.2) ((orientedSquare_reflect_closed t a b p).mp hp))
    have hcap' : ∀ p, closedSquare (orientedSquare (-t) a (-b)) p → h ≤ p.1 := by
      intro p hp
      exact hcap (p.1, -p.2) ((orientedSquare_reflect_closed t a b p).mp hp)
    have hp := cap_piercing_nonneg (show 0 ≤ -t by linarith) ht' hh hdisk' hcap'
    have hr := (orientedSquare_reflect_open t a b (h + 1 / 2, 0)).mp hp
    simpa only [neg_zero] using hr

/-- Two squares in one deep cap cannot have disjoint interiors.
Both squares are in nearest side frames, and no pin inclusion is assumed. -/
theorem cap_squares_overlap {a b t A B T h : ℝ}
    (ht : |t| ≤ Real.pi / 4) (hT : |T| ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hdisk : ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0, 0) R0 p)
    (hcap : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1)
    (hDisk : ∀ p, closedSquare (orientedSquare T A B) p → inDisk (0, 0) R0 p)
    (hCap : ∀ p, closedSquare (orientedSquare T A B) p → h ≤ p.1) :
    ∃ p, openSquare (orientedSquare t a b) p ∧ openSquare (orientedSquare T A B) p :=
  ⟨(h + 1 / 2, 0), cap_piercing ht hh hdisk hcap, cap_piercing hT hh hDisk hCap⟩

/-- The one-helper-per-side deduction in a cap's local frame. -/
theorem cap_helper_unique {ι : Type*} {S : ι → UnitSquare} (hd : InteriorDisjoint S)
    {i j : ι} {a b t A B T h : ℝ}
    (hi : S i = orientedSquare t a b) (hj : S j = orientedSquare T A B)
    (ht : |t| ≤ Real.pi / 4) (hT : |T| ≤ Real.pi / 4) (hh : coreRadius ≤ h)
    (hdisk : ∀ p, closedSquare (S i) p → inDisk (0, 0) R0 p)
    (hcap : ∀ p, closedSquare (S i) p → h ≤ p.1)
    (hDisk : ∀ p, closedSquare (S j) p → inDisk (0, 0) R0 p)
    (hCap : ∀ p, closedSquare (S j) p → h ≤ p.1) : i = j := by
  have hdisk' : ∀ p, closedSquare (orientedSquare t a b) p → inDisk (0, 0) R0 p := by
    simpa only [hi] using hdisk
  have hcap' : ∀ p, closedSquare (orientedSquare t a b) p → h ≤ p.1 := by
    simpa only [hi] using hcap
  have hDisk' : ∀ p, closedSquare (orientedSquare T A B) p → inDisk (0, 0) R0 p := by
    simpa only [hj] using hDisk
  have hCap' : ∀ p, closedSquare (orientedSquare T A B) p → h ≤ p.1 := by
    simpa only [hj] using hCap
  by_contra hij
  obtain ⟨p, hp, hP⟩ := cap_squares_overlap ht hT hh hdisk' hcap' hDisk' hCap'
  exact hd i j hij p ⟨by simpa only [hi] using hp, by simpa only [hj] using hP⟩

end SquaresInCircles.Six.Normalization
