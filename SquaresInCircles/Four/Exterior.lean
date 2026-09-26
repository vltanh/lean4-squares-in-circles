import SquaresInCircles.Common.RectangleArcs

/-!
# Four squares: exterior arcs

The tangent to `phi = 2` at `(1/2, 1/2)` is the diamond `a + b ≤ 1`, and it
touches `phi = 2` only there. On the circle of radius `1/2`, every exterior
square in the closed disk of radius `sqrt 2` holds an arc of at least 90
degrees, strictly more unless its centre is on the diamond's edge.
-/
noncomputable section
namespace SquaresInCircles.Four

/-- The diamond: `phi a b ≤ 2` gives `a + b ≤ 1`, with equality only at
`(1/2, 1/2)`, a vertex of the square at the disk centre. -/
lemma diamond {a b : ℝ} (h : phi a b ≤ 2) : a+b ≤ 1 ∧ (1 ≤ a+b → a=1/2 ∧ b=1/2) := by
  have he : phi a b-2=2*(a+b-1)+(a-1/2)^2+(b-1/2)^2 := by unfold phi; ring
  have hx := sq_nonneg (a-1/2)
  have hy := sq_nonneg (b-1/2)
  refine ⟨by linarith,fun hs => ⟨?_,?_⟩⟩ <;> nlinarith

/-- On the circle of radius `1/2` an exterior square holds an arc of at least
90 degrees, and more unless its centre is on the diamond's edge `a + b = 1`. -/
lemma exterior_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o) (hφ : phi C.a C.b ≤ 2) :
    ∃ A : OpenArc o (1/2) {p | openSquare S p}, Real.pi/4 ≤ A.halfWidth ∧
      (C.a+C.b < 1 → Real.pi/4 < A.halfWidth) := by
  have ha := C.exterior hsort hout
  have hsum := (diamond hφ).1
  have ha' : C.a < 5/6 := by
    unfold phi at hφ
    nlinarith [sq_nonneg C.b,C.nonneg.2]
  obtain ⟨W,hW,-⟩ := C.cap_arc (r := 1/2) (by norm_num) le_rfl ha (by linarith) (by linarith)
  have hA : Real.pi/4 < capA (1/2) C.a := by
    refine lt_of_not_ge fun h => ?_
    have h' := Real.arccos_le_pi_div_four.mp h
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg 2]
  have hAV (hlt : C.a+C.b ≤ 1) : Real.pi/2-capA (1/2) C.a ≤ capV (1/2) C.b := by
    rw [capA,Real.arccos_eq_pi_div_two_sub_arcsin,sub_sub_cancel]
    exact Real.arcsin_le_arcsin (by linarith)
  refine ⟨W,?_,fun hs => ?_⟩
  · have hm := le_min (show Real.pi/2-capA (1/2) C.a ≤ capA (1/2) C.a by linarith) (hAV hsum)
    linarith
  · have hV : Real.pi/2-capA (1/2) C.a < capV (1/2) C.b := by
      rw [capA,Real.arccos_eq_pi_div_two_sub_arcsin,sub_sub_cancel]
      exact Real.arcsin_lt_arcsin (by linarith) (by linarith) (by linarith [C.nonneg.2])
    have hm := lt_min (show Real.pi/2-capA (1/2) C.a < capA (1/2) C.a by linarith) hV
    linarith

end SquaresInCircles.Four
