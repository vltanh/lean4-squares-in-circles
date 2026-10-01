import SquaresInCircles.Six.Normalization.Markers
import SquaresInCircles.Seven.MarkerSeparation
import SquaresInCircles.Common.Angles

/-!
# Strict marker separation

Two disjoint exterior squares with `φ ≤ Q0` have markers more than `π/3` apart:
by the pair theorem of `Seven.MarkerSeparation` they are at least `π/3` apart,
and at exactly `π/3` their states would form a contact, which needs the side
state `(1, 1/2)`, with `φ = 13/4 > Q0`. Five directions pairwise more than
`π/3` apart do not all avoid an open arc longer than `2π/3`.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- Two states with `φ ≤ Q0` form no contact. -/
lemma no_Seven_contact_below_ceiling {a u A v : ℝ} {s t : Seven.TransverseSign}
    (h : phi a u ≤ Q0) (h' : phi A v ≤ Q0)
    (hc : Seven.OrderedContact a u A v s t) : False := by
  rcases hc with ⟨_, _, ⟨ha, hu⟩, _⟩ | ⟨_, ⟨ha, hu⟩, _⟩ | ⟨_, _, ⟨hA, hv⟩⟩
  · rw [ha, hu] at h
    norm_num [phi, Q0] at h
  · rw [ha, hu] at h
    norm_num [phi, Q0] at h
  · rw [hA, hv] at h'
    norm_num [phi, Q0] at h'

lemma ordered_marker_gap_gt {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : Seven.Admissible C.a C.b) (hD : Seven.Admissible D.a D.b)
    (hpC : phi C.a C.b ≤ Q0) (hpD : phi D.a D.b ≤ Q0)
    {g : ℝ} (hg0 : 0 ≤ g)
    (hang : (g : Direction) = Seven.chartMarker D - Seven.chartMarker C)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) : Real.pi / 3 < g := by
  by_contra! hg
  rcases lt_or_eq_of_le hg with hlt | heq
  · exact Seven.ordered_gap_not_below C D hC hD ⟨hg0, hlt⟩ hang hd
  · have hc := Seven.ordered_chart_contact C D hC hD
      (by simpa only [heq, Seven.gap] using hang) hd
    exact no_Seven_contact_below_ceiling hpC hpD hc

/-- Disjoint exterior squares with admissible states and `φ ≤ Q0` have markers
more than `π/3` apart. -/
theorem strict_marker_separation {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : Seven.Admissible C.a C.b) (hD : Seven.Admissible D.a D.b)
    (hpC : phi C.a C.b ≤ Q0) (hpD : phi D.a D.b ≤ Q0)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    Real.pi / 3 < dist (Seven.chartMarker C) (Seven.chartMarker D) := by
  let g := (Seven.chartMarker D - Seven.chartMarker C).toReal
  have hg : (g : Direction) = Seven.chartMarker D - Seven.chartMarker C :=
    Real.Angle.coe_toReal _
  have he : dist (Seven.chartMarker C) (Seven.chartMarker D) = |g| := by
    rw [dist_comm, direction_dist]
  rw [he]
  by_cases h0 : 0 ≤ g
  · rw [abs_of_nonneg h0]
    exact ordered_marker_gap_gt C D hC hD hpC hpD h0 hg hd
  · rw [abs_of_neg (lt_of_not_ge h0)]
    have hrev : ((-g : ℝ) : Direction) = Seven.chartMarker C - Seven.chartMarker D := by
      rw [Real.Angle.coe_neg, hg]
      abel
    exact ordered_marker_gap_gt D C hD hC hpD hpC (by linarith) hrev
      (fun p hp => hd p ⟨hp.2, hp.1⟩)

/-- The representative of `m` in `[a, a + 2π)`. -/
def liftFrom (a : ℝ) (m : Direction) : ℝ :=
  let r := (m - (a : Direction)).toReal
  a + if r < 0 then r + 2 * Real.pi else r

lemma liftFrom_spec (a : ℝ) (m : Direction) :
    a ≤ liftFrom a m ∧ liftFrom a m < a + 2 * Real.pi ∧
      (liftFrom a m : Direction) = m := by
  have hl := (m - (a : Direction)).neg_pi_lt_toReal
  have hu := (m - (a : Direction)).toReal_le_pi
  dsimp only [liftFrom]
  split_ifs with h
  · refine ⟨by linarith [Real.pi_pos], by linarith, ?_⟩
    simp only [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero,
      Real.Angle.coe_toReal]
    abel
  · refine ⟨by linarith, by linarith [Real.pi_pos], ?_⟩
    simp only [Real.Angle.coe_add, Real.Angle.coe_toReal]
    abel

/-- Five directions pairwise more than `π/3` apart do not all avoid an open arc
`(l, u)` longer than `2π/3`: their representatives in `[u, l + 2π]`, an interval
shorter than `4π/3`, would have four successive gaps of more than `π/3`. -/
theorem no_empty_long_arc (m : Fin 5 → Direction)
    (hsep : ∀ i j, i ≠ j → Real.pi / 3 < dist (m i) (m j))
    {l u : ℝ} (hlen : 2 * Real.pi / 3 < u - l)
    (hempty : ∀ i t, l < t → t < u → (t : Direction) ≠ m i) : False := by
  classical
  let r : Fin 5 → ℝ := fun i => liftFrom u (m i)
  have hrep (i : Fin 5) : (r i : Direction) = m i := (liftFrom_spec u (m i)).2.2
  have hrange (i : Fin 5) : u ≤ r i ∧ r i ≤ l + 2 * Real.pi := by
    refine ⟨(liftFrom_spec u (m i)).1, ?_⟩
    by_contra! hh
    have hup := (liftFrom_spec u (m i)).2.1
    have he : ((r i - 2 * Real.pi : ℝ) : Direction) = m i := by
      simp only [Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero, hrep]
    exact hempty i (r i - 2 * Real.pi) (by linarith) (by linarith) he
  let σ := Tuple.sort r
  let p : Fin 5 → ℝ := fun i => r (σ i)
  have hm : Monotone p := Tuple.monotone_sort r
  have hp {i j : Fin 5} (hij : i < j) : Real.pi / 3 < p j - p i := by
    have h := hsep (σ j) (σ i) (σ.injective.ne hij.ne')
    rw [← hrep (σ j), ← hrep (σ i), dist_eq_norm, ← Real.Angle.coe_sub] at h
    have hn := direction_coe_norm_le (p j - p i)
    rw [abs_of_nonneg (sub_nonneg.mpr (hm hij.le))] at hn
    exact h.trans_le hn
  have h01 := hp (show (0 : Fin 5) < 1 by decide)
  have h12 := hp (show (1 : Fin 5) < 2 by decide)
  have h23 := hp (show (2 : Fin 5) < 3 by decide)
  have h34 := hp (show (3 : Fin 5) < 4 by decide)
  have hleft : u ≤ p 0 := (hrange (σ 0)).1
  have hright : p 4 ≤ l + 2 * Real.pi := (hrange (σ 4)).2
  linarith

end SquaresInCircles.Six.Normalization
