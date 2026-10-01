import SquaresInCircles.Six.Containing
import SquaresInCircles.Six.Candidate
import SquaresInCircles.Six.Normalization.ChartInterop
import Mathlib.Data.Fin.Embedding

/-!
# The central square and the five markers

In a packing of six squares in a disk of squared radius at most `Q0`, one square
contains the disk centre `o`. The other five are exterior; each has a sorted
chart with `φ(a, b) ≤ Q0` and an admissible state, and their markers are
pairwise more than `π/3` apart. So every open arc of length more than `2π/3`
contains a marker.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization

/-- A square containing `o`, and sorted charts of the other five squares, which
are exterior, contained and admissible, with markers more than `π/3` apart. -/
structure ExteriorInput (S : Fin 6 → UnitSquare) (o : Point) where
  central : Fin 6
  central_inside : openSquare (S central) o
  chart : (i : Fin 5) → SquareChart (S (central.succAbove i)) o
  sorted : ∀ i, (chart i).b ≤ (chart i).a
  exterior : ∀ i, ¬ openSquare (S (central.succAbove i)) o
  contained : ∀ i, phi (chart i).a (chart i).b ≤ Q0
  admissible : ∀ i, Seven.Admissible (chart i).a (chart i).b
  separated : ∀ i j, i ≠ j →
    Real.pi / 3 < dist (Seven.chartMarker (chart i)) (Seven.chartMarker (chart j))

namespace ExteriorInput
variable {S : Fin 6 → UnitSquare} {o : Point}

/-- The marker of the `i`-th exterior square. -/
def markers (D : ExteriorInput S o) (i : Fin 5) : Direction := Seven.chartMarker (D.chart i)

/-- Every open arc of length more than `2π/3` contains a marker. -/
lemma no_empty_arc (D : ExteriorInput S o) {l u : ℝ}
    (hlen : 2 * Real.pi / 3 < u - l)
    (hempty : ∀ i t, l < t → t < u → (t : Direction) ≠ D.markers i) : False :=
  no_empty_long_arc D.markers D.separated hlen hempty

end ExteriorInput

/-- A packing of six squares in a disk of squared radius at most `Q0` has a
square containing the disk centre and five exterior squares with separated
markers. -/
theorem exterior_input_of_ceiling {S : Fin 6 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (hQ : R ^ 2 ≤ Q0) : Nonempty (ExteriorInput S o) := by
  classical
  obtain ⟨k, hk, _⟩ := Six.exists_unique_containing_of_ceiling hp hQ
  have hout := Six.remaining_exterior hp hk
  choose C hC using fun i : Fin 5 => sorted_square_chart (S (k.succAbove i)) o
  have hc (i : Fin 5) : phi (C i).a (C i).b ≤ Q0 :=
    chart_phi (C i) ((hp.phi_le (k.succAbove i)).trans hQ)
  have ha (i : Fin 5) : Seven.Admissible (C i).a (C i).b :=
    ⟨(C i).nonneg.2, hC i, (C i).exterior (hC i) (hout i),
      (hc i).trans Q0_lt_thirteen_fourths.le⟩
  refine ⟨⟨k, hk, C, hC, hout, hc, ha, ?_⟩⟩
  intro i j hij
  apply strict_marker_separation (C i) (C j) (ha i) (ha j) (hc i) (hc j)
  exact hp.disjoint _ _ (Fin.succAbove_right_injective.ne hij)

end SquaresInCircles.Six.Normalization
