import SquaresInCircles.Two.Optimality
import SquaresInCircles.Common.Angles
import SquaresInCircles.Common.Optimum

/-!
# Two squares: uniqueness

At the optimal radius both centres are exactly `1/2` from the disk centre, so
each square sits at `(1/2, 0)` in its sorted chart and holds the half of a small
circle about `o` around its phase. Disjoint half circles are opposite, so a half
turn puts both squares in one frame, at `(1/2, 0)` and `(-1/2, 0)`.

The file ends with `optimum`: the case as an `Optimum`.
-/
noncomputable section
namespace SquaresInCircles.Two

/-- At the optimal radius the two squares form the rectangle. -/
theorem uniqueness (S : Fin 2 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : HasNormalForm S o centers := by
  have hφ (i : Fin 2) : phi (alpha (S i) o) (beta (S i) o) ≤ 5/4 := radius_sq ▸ hp.phi_le i
  have hhalf := centers_at_half S o hp.disjoint hφ
  -- so each square sits at `(1/2, 0)` in its sorted chart
  have hC (i : Fin 2) : ∃ C : SquareChart (S i) o, C.a=1/2 ∧ C.b=0 := by
    obtain ⟨C,hs⟩ := sorted_square_chart (S i) o
    have h1 := chart_phi C (hφ i)
    have h2 := C.transfer (fun a b => a^2+b^2=1/4) (fun h => by linarith) (hhalf i)
    obtain ⟨ha,hb⟩ := C.nonneg
    unfold phi at h1
    exact ⟨C,by nlinarith,by nlinarith⟩
  choose C ha hb using hC
  -- and holds a half circle about its phase; disjoint half circles are opposite
  obtain ⟨A,hA,hAc⟩ := (C 0).half_arc (r := 1/2) (by norm_num) (ha 0) (by rw [hb 0]; norm_num)
  obtain ⟨B,hB,hBc⟩ := (C 1).half_arc (r := 1/2) (by norm_num) (ha 1) (by rw [hb 1]; norm_num)
  have hanti := A.opposite B (hp.disjoint.pairwise (by decide)) hA hB
  rw [hAc,hBc] at hanti
  have r1 := chart_represents (C 1)
  rw [hanti,show (Real.pi:Direction)=quarterShift 2 from rfl] at r1
  apply normal_form_of_slots (φ := (C 0).phase) hp.disjoint
  intro i
  fin_cases i
  · exact ⟨1,by simpa [centers,SquareChart.signedB,ha,hb] using chart_represents (C 0)⟩
  · exact ⟨0,by simpa [centers,turnPoint,SquareChart.signedB,ha,hb,neg_div] using
      represents_quarter 2 r1⟩

/-- The optimum for two squares: `radius`, attained only by the normal forms
of `centers`. -/
def optimum : Optimum 2 :=
  .ofUnique centers optimality model_packing uniqueness

end SquaresInCircles.Two
