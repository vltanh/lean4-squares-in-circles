module
public import SquaresInCircles.One.Construction
public import SquaresInCircles.Common.Optimum

@[expose] public section

/-!
# One square: uniqueness

At the optimal radius both coordinates of a chart of the square vanish, so the
square sits at the origin of the chart's frame.

The file ends with `optimum`: the case as an `Optimum`, which also gives the
lower bound.
-/
noncomputable section
namespace SquaresInCircles.One

/-- The farthest vertex of a square is at least half a diagonal away, and
farther unless the centre is at the disk centre. -/
lemma half_add_le_phi (a b : ℝ) : 1/2+a+b ≤ phi a b := by
  unfold phi
  nlinarith [sq_nonneg a,sq_nonneg b]

/-- At the optimal radius the square is centred at the disk centre. -/
theorem uniqueness (S : Fin 1 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : Congruent S o model := by
  obtain ⟨C⟩ := square_chart (S 0) o
  have h := (half_add_le_phi C.a C.b).trans (chart_phi C (hp.phi_le 0))
  rw [radius_sq] at h
  obtain ⟨ha,hb⟩ := C.nonneg
  have hc : (C.a,C.signedB)=centers 0 := by
    simp [centers,SquareChart.signedB,show C.a=0 by linarith,show C.b=0 by linarith]
  apply congruent_of_slots (φ := C.phase) hp.disjoint
  intro i
  rw [Subsingleton.elim i 0]
  exact ⟨0,hc ▸ chart_represents C⟩

/-- The optimum for one square: `radius`, attained only by the configurations
congruent to `model`. -/
def optimum : Optimum 1 :=
  .ofUnique model model_packing
    ⟨0,(1/2,1/2),(axisSquare_closed _ _).2 (by norm_num [centers,closedAxisSquare]),by norm_num [normSq,radius_sq]⟩
    uniqueness

end SquaresInCircles.One
