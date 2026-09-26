import SquaresInCircles.Seven.MarkerSeparation
import SquaresInCircles.Common.Angles

/-!
# Seven squares: the lower bound

`Seven.optimality` is the lower bound for arbitrary packings, with every square
rotated independently and an arbitrary disk centre. The sliding packings of
`Seven/Construction.lean` attain it.

Of seven squares with disjoint interiors at most one contains the disk centre,
so six of them avoid it. In a disk with `R^2 < 13/4` their markers are pairwise
more than `π/3` apart (`marker_separation`). Six directions pairwise at least
`π/3` apart form a regular hexagon, whose neighbours are exactly `π/3` apart, so
this is impossible (`six_markers_impossible`).
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma packing_reindex {m n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (e : Fin m ↪ Fin n) : Packing (fun i => S (e i)) o R :=
  ⟨hp.1,fun i => hp.2.1 (e i),fun i j hij => hp.2.2 (e i) (e j) (e.injective.ne hij)⟩

/-- Boundary points count as exterior: only membership in an open square is omitted. -/
theorem six_exterior_indices (S : Fin 7 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) :
    ∃ e : Fin 6 ↪ Fin 7, ∀ i, ¬ openSquare (S (e i)) o := by
  by_cases h : ∃ k, openSquare (S k) o
  · obtain ⟨k,hk⟩ := h
    exact ⟨k.succAboveEmb,fun i hi => hd _ k (k.succAbove_ne i) o ⟨hi,hk⟩⟩
  · exact ⟨Fin.succAboveEmb 0,fun i hi => h ⟨_,hi⟩⟩

/-- Six directions pairwise at least `π/3` apart form a regular hexagon. -/
theorem six_directions_hexagon (c : Fin 6 → Direction)
    (hsep : ∀ i j, i ≠ j → gap ≤ dist (c i) (c j)) :
    ∃ (φ : Direction) (σ : Equiv.Perm (Fin 6)),
      ∀ i, c (σ i) = φ+(((i.val : ℝ)*gap : ℝ) : Direction) :=
  regular_polygon c (by unfold gap; push_cast; ring) hsep

def next (i : Fin 6) : Fin 6 := i+1

lemma next_ne (i : Fin 6) : next i ≠ i := by fin_cases i <;> decide

lemma hexagon_successor {c : Fin 6 → Direction} {φ : Direction}
    (h : ∀ i, c i = φ+(((i.val : ℝ)*gap : ℝ) : Direction)) (i : Fin 6) :
    (gap : Direction) = c (next i)-c i := by
  rw [h,h,add_sub_add_left_eq_sub,←Real.Angle.coe_sub,Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  exact ⟨if i = 5 then 1 else 0,by fin_cases i <;> norm_num [next,gap] <;> ring⟩

/-- Six points cannot all have pairwise circular distances strictly above pi/3. -/
theorem six_markers_impossible (c : Fin 6 → Direction)
    (hsep : Pairwise (fun i j => Real.pi/3 < dist (c i) (c j))) : False := by
  obtain ⟨φ,σ,hc⟩ := six_directions_hexagon c (fun i j hij => (hsep hij).le)
  have hd : Real.pi/3 < dist (c (σ (next 0))) (c (σ 0)) :=
    hsep (σ.injective.ne (next_ne 0))
  rw [dist_eq_norm,← hexagon_successor hc 0] at hd
  exact hd.not_ge ((direction_coe_norm_le gap).trans_eq (abs_of_pos (by unfold gap; positivity)))

/-- Six squares that avoid the disk centre already need `R^2 ≥ 13/4`. -/
theorem six_exterior_squared_lower (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hext : ∀ i, ¬ openSquare (S i) o) : (13:ℝ)/4 ≤ R^2 := by
  by_contra hn
  have hphi (i : Fin 6) : phi (alpha (S i) o) (beta (S i) o) < targetSq :=
    (hp.phi_le i).trans_lt (lt_of_not_ge hn)
  choose C hsort using fun i => sorted_square_chart (S i) o
  exact six_markers_impossible (fun i => chartMarker (C i)) fun i j hij =>
    marker_separation (C i) (C j) (hsort i) (hsort j) (hext i) (hext j) (hphi i) (hphi j)
      (hp.disjoint i j hij)

theorem squared_lower (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (13:ℝ)/4 ≤ R^2 := by
  obtain ⟨e,hext⟩ := six_exterior_indices S o hp.disjoint
  exact six_exterior_squared_lower (fun i => S (e i)) o R (packing_reindex hp e) hext

/-- The geometric lower bound; `Packing` carries no marker, support or separator
assumption. -/
theorem optimality (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : radius ≤ R :=
  le_of_sq_le_sq (by rw [radius_sq]; exact squared_lower S o R hp) hp.1

end SquaresInCircles.Seven
