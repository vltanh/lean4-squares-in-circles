module

public import SquaresInCircles.Common.Charts

/-!
# Four squares: the containing square

A square whose closed square contains the disk centre holds the quarter of the
circle of radius `1/2` between its two edges at the vertex nearest the disk
centre, centred on the direction `vertexMid` of that vertex.
-/

@[expose] public section

noncomputable section
open Set
namespace SquaresInCircles.Four

/-- The middle of the quarter circle between the two edges of a square at its
vertex nearest the disk centre. -/
def vertexMid {S : UnitSquare} {o : Point} (C : SquareChart S o) : Direction :=
  chartAngle C.phase C.reversed (Real.pi/4)

/-- If the closed square contains the disk centre, the square holds the quarter
of the circle of radius `1/2` between the chart angles `0` and `π/2`. -/
lemma quarter_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a ≤ 1/2) (hb : C.b ≤ 1/2) :
    ∃ A : OpenArc o (1/2) {p | openSquare S p}, A.halfWidth=Real.pi/4 ∧ A.center=vertexMid C := by
  obtain ⟨A,hA,hc⟩ := C.arc (1/2) 0 (Real.pi/2) (by positivity) (by linarith [Real.pi_pos]) (by
    intro t ht
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
    have hu := Real.sin_sq_add_cos_sq t
    have hs1 : Real.sin t < 1 := by nlinarith
    have hc1 : Real.cos t < 1 := by nlinarith
    have := C.nonneg
    exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩⟩)
  exact ⟨A,by rw [hA]; ring,by rw [hc,vertexMid]; congr 1; ring⟩

end SquaresInCircles.Four
