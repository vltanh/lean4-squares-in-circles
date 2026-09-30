module
public import SquaresInCircles.Six.Normalization.Markers
public import SquaresInCircles.Seven.MarkerSeparation
public import SquaresInCircles.Common.Angles

@[expose] public section

/-!
# N7 and the finite step of Proposition A

Strict separation below Q0 is derived from Seven's equality-contact theorem:
every equality contact contains a SideState whose far corner has squared
radius 13/4. The empty-arc argument is then a five-point counting argument,
not a numerical certificate or a pin/sector assumption.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

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

/-- Strict pairwise separation at the candidate's rational ceiling. -/
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

def successiveGaps (p : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![p 1 - p 0, p 2 - p 1, p 3 - p 2, p 4 - p 3,
    2 * Real.pi + p 0 - p 4]

/-- N7, including the often-used strict UPPER bound on every cyclic gap. -/
theorem five_marker_gaps (m : Fin 5 → Direction)
    (hsep : ∀ i j, i ≠ j → Real.pi / 3 < dist (m i) (m j)) :
    ∃ (σ : Equiv.Perm (Fin 5)) (p : Fin 5 → ℝ),
      (∀ i, (p i : Direction) = m (σ i)) ∧ Monotone p ∧
      (∀ i, Real.pi / 3 < successiveGaps p i ∧
        successiveGaps p i < 2 * Real.pi / 3) ∧
      (∑ i, successiveGaps p i) = 2 * Real.pi := by
  classical
  let r : Fin 5 → ℝ := fun i => (m i).toReal
  let σ := Tuple.sort r
  let p : Fin 5 → ℝ := fun i => r (σ i)
  have hmono : Monotone p := Tuple.monotone_sort r
  have hrepr (i : Fin 5) : (p i : Direction) = m (σ i) := Real.Angle.coe_toReal _
  have hpair {i j : Fin 5} (hij : i < j) :
      Real.pi / 3 < p j - p i ∧ Real.pi / 3 < 2 * Real.pi - (p j - p i) := by
    have hdist := hsep (σ j) (σ i) (σ.injective.ne hij.ne')
    rw [← hrepr j, ← hrepr i, dist_eq_norm, ← Real.Angle.coe_sub] at hdist
    have h0 : 0 ≤ p j - p i := sub_nonneg.mpr (hmono hij.le)
    have hnorm := direction_coe_norm_le (p j - p i)
    have hwrap := direction_norm_wrapped (t := p j - p i) (by
      rw [abs_of_nonneg h0]
      dsimp [p, r]
      linarith [(m (σ i)).neg_pi_lt_toReal, (m (σ j)).toReal_le_pi])
    rw [abs_of_nonneg h0] at hnorm hwrap
    exact ⟨hdist.trans_le hnorm, hdist.trans_le hwrap⟩
  have hlo (i : Fin 5) : Real.pi / 3 < successiveGaps p i := by
    fin_cases i
    · exact (hpair (show (0 : Fin 5) < 1 by decide)).1
    · exact (hpair (show (1 : Fin 5) < 2 by decide)).1
    · exact (hpair (show (2 : Fin 5) < 3 by decide)).1
    · exact (hpair (show (3 : Fin 5) < 4 by decide)).1
    · have hh := (hpair (show (0 : Fin 5) < 4 by decide)).2
      dsimp [successiveGaps]
      linarith
  have hsum : (∑ i, successiveGaps p i) = 2 * Real.pi := by
    simp only [successiveGaps, Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num
    ring
  have hhi (i : Fin 5) : successiveGaps p i < 2 * Real.pi / 3 := by
    have h0 := hlo 0
    have h1 := hlo 1
    have h2 := hlo 2
    have h3 := hlo 3
    have h4 := hlo 4
    fin_cases i <;> dsimp [successiveGaps] at * <;> linarith
  exact ⟨σ, p, hrepr, hmono, fun i => ⟨hlo i, hhi i⟩, hsum⟩

/-- A representative in the half-open interval [a,a+2pi). -/
def liftFrom (a : ℝ) (m : Direction) : ℝ :=
  let r := (m - (a : Direction)).toReal
  a + if r < 0 then r + 2 * Real.pi else r

lemma liftFrom_spec (a : ℝ) (m : Direction) :
    a ≤ liftFrom a m ∧ liftFrom a m < a + 2 * Real.pi ∧
      (liftFrom a m : Direction) = m := by
  have hl := (m - (a : Direction)).neg_pi_lt_toReal
  have hu := (m - (a : Direction)).toReal_le_pi
  unfold liftFrom
  split_ifs with h
  · refine ⟨by linarith [Real.pi_pos], by linarith, ?_⟩
    simp only [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero,
      Real.Angle.coe_toReal]
    abel
  · refine ⟨by linarith, by linarith [Real.pi_pos], ?_⟩
    simp only [Real.Angle.coe_add, Real.Angle.coe_toReal]
    abel

/-- Five separated directions cannot all avoid an open arc longer than 2pi/3.
The proof sorts representatives in the complementary interval and adds its
four strict consecutive-distance inequalities. This is the N7 counting step. -/
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
