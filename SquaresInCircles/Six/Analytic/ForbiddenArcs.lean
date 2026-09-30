module
public import SquaresInCircles.Six.Analytic.CoreLargeQuadrants

@[expose] public section

/-!
# Complete analytic forbidden arcs for Proposition A

Small cy uses (-pi/2+2/3, pi/2-3/8); large cy uses (-27/50, pi/2).
Both widths exceed 2*pi/3 by explicit rational comparisons with pi. The
partition is into the geometric E/N/S/W quadrants, not a numerical grid.
The modular lemma checks every representative of the marker, not only its
chosen real lift.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

 def smallArcLeft : ℝ := -Real.pi/2+2/3
 def smallArcRight : ℝ := Real.pi/2-3/8

lemma small_arc_length : 2*Real.pi/3 < smallArcRight-smallArcLeft := by
  dsimp [smallArcLeft,smallArcRight]
  linarith [Real.pi_gt_d2]

lemma large_arc_length : 2*Real.pi/3 < Real.pi/2-(-(27:ℝ)/50) := by
  linarith [Real.pi_lt_d2]

lemma small_arc_near_east : -Real.pi/2 ≤ smallArcLeft ∧ smallArcRight ≤ Real.pi/2 := by
  dsimp [smallArcLeft,smallArcRight]
  constructor <;> linarith

lemma large_arc_near_east : -Real.pi/2 ≤ -(27:ℝ)/50 := by linarith [Real.pi_gt_d2]

/-- A1: no source or sign remains inside the small-center forbidden arc. -/
theorem small_core_marker_outside {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hx : c0 < x) (hx1 : x < 1/2) (hy0 : 0 ≤ y) (hy : y ≤ c0)
    (hsep : ∃ k, 0 ≤ centralMargin k t a b x y) :
    liftedMarker t a b ≤ smallArcLeft ∨ smallArcRight ≤ liftedMarker t a b := by
  have hm := liftedMarker_bounds (t := t) h.seven_admissible
  by_cases hSW : t ≤ -3*Real.pi/4
  · left
    dsimp [smallArcLeft]
    linarith [hm.2]
  by_cases hS : t ≤ -Real.pi/4
  · have ht : |t+Real.pi/2| ≤ Real.pi/4 := by
      apply abs_le.mpr
      constructor <;> linarith
    have he : -Real.pi/2+(t+Real.pi/2)=t := by ring
    have hs : ∃ k, 0 ≤ centralMargin k (-Real.pi/2+(t+Real.pi/2)) a b x y := by
      simpa only [he] using hsep
    have hb := south_small_marker h ht hx hx1 hy0 hy hs
    left
    simpa only [he,smallArcLeft] using hb.le
  by_cases hE : t ≤ Real.pi/4
  · have ht : |t| ≤ Real.pi/4 := abs_le.mpr ⟨by linarith,hE⟩
    exact False.elim (east_small_impossible h ht hx hx1 hy0 hy hsep)
  by_cases hN : t ≤ 3*Real.pi/4
  · have ht : |t-Real.pi/2| ≤ Real.pi/4 := by
      apply abs_le.mpr
      constructor <;> linarith
    have he : Real.pi/2+(t-Real.pi/2)=t := by ring
    have hs : ∃ k, 0 ≤ centralMargin k (Real.pi/2+(t-Real.pi/2)) a b x y := by
      simpa only [he] using hsep
    have hb := north_small_marker h ht hx hx1 hy0
      (show y ≤ 1/2 by linarith [c0_lt_23_200]) hs
    right
    simpa only [he,smallArcRight] using hb.le
  · right
    dsimp [smallArcRight]
    linarith [hm.1]

/-- A2: the whole ordered large-center region, with no central-grid partition. -/
theorem large_core_marker_outside {a b t x y : ℝ} (h : ContainedChart a |b|)
    (hy : c0 < y) (hxy : y ≤ x) (hx1 : x < 1/2)
    (hsep : ∃ k, 0 ≤ centralMargin k t a b x y) :
    liftedMarker t a b ≤ -27/50 ∨ Real.pi/2 ≤ liftedMarker t a b := by
  have hx : c0 < x := hy.trans_le hxy
  have hy0 : 0 ≤ y := (c0_pos.trans hy).le
  have hm := liftedMarker_bounds (t := t) h.seven_admissible
  by_cases hSW : t ≤ -3*Real.pi/4
  · left
    linarith [hm.2,Real.pi_gt_d2]
  by_cases hS : t ≤ -Real.pi/4
  · have ht : |t+Real.pi/2| ≤ Real.pi/4 := by
      apply abs_le.mpr
      constructor <;> linarith
    have he : -Real.pi/2+(t+Real.pi/2)=t := by ring
    have hs : ∃ k, 0 ≤ centralMargin k (-Real.pi/2+(t+Real.pi/2)) a b x y := by
      simpa only [he] using hsep
    have hb := south_large_marker h ht hx hx1 hy0 hxy hs
    exact Or.inl (by simpa only [he] using hb.le)
  by_cases hE : t ≤ Real.pi/4
  · have ht : |t| ≤ Real.pi/4 := abs_le.mpr ⟨by linarith,hE⟩
    exact Or.inl (east_large_marker h ht hx hx1 hy0 hxy hsep).le
  by_cases hN : t ≤ 3*Real.pi/4
  · have ht : |t-Real.pi/2| ≤ Real.pi/4 := by
      apply abs_le.mpr
      constructor <;> linarith
    have he : Real.pi/2+(t-Real.pi/2)=t := by ring
    have hs : ∃ k, 0 ≤ centralMargin k (Real.pi/2+(t-Real.pi/2)) a b x y := by
      simpa only [he] using hsep
    have hb := north_large_marker h ht hy hxy hx1 hs
    exact Or.inr (by simpa only [he] using hb)
  · right
    linarith [hm.1]

/-- Real lift exclusion gives genuine circular-arc exclusion. -/
theorem marker_no_representative {a b t l u v : ℝ} (h : ContainedChart a |b|)
    (ht : |t| ≤ Real.pi) (hl : -Real.pi/2 ≤ l) (hu : u ≤ Real.pi/2)
    (hout : liftedMarker t a b ≤ l ∨ u ≤ liftedMarker t a b)
    (hv : l < v ∧ v < u)
    (he : (v:Direction)=(liftedMarker t a b:Direction)) : False := by
  have hm := liftedMarker_bounds (t := t) h.seven_admissible
  have htb := abs_le.mp ht
  obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  have hup : v-liftedMarker t a b < 2*Real.pi := by
    linarith [hm.1,htb.1,hv.2,Real.pi_pos]
  have hlo : -(2*Real.pi) < v-liftedMarker t a b := by
    linarith [hm.2,htb.2,hv.1,Real.pi_pos]
  rw [hk] at hup hlo
  have hpi : 0 < 2*Real.pi := by positivity
  have hku : (k:ℝ) < 1 := (mul_lt_mul_left hpi).mp (by simpa using hup)
  have hkl : (-1:ℝ) < (k:ℝ) := (mul_lt_mul_left hpi).mp (by simpa using hlo)
  have hku' : k < 1 := by exact_mod_cast hku
  have hkl' : (-1:ℤ) < k := by exact_mod_cast hkl
  have hk0 : k=0 := by omega
  have hvEq : v=liftedMarker t a b := by simpa only [hk0,Int.cast_zero,mul_zero,sub_eq_zero] using hk
  rw [hvEq] at hv
  rcases hout with h | h <;> linarith [hv.1,hv.2]

end SquaresInCircles.Six.Analytic
