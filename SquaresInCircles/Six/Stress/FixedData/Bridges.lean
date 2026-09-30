module
public import SquaresInCircles.Six.Stress.FixedRow

@[expose] public section

/-!
# Source-independent survivor bridge rows

These three C/W/D/S stresses are used after the candidate D-edge graph is
known. They were replayed locally with the exact-dyadic audit backend at the
larger R0 radius and conservative c0 central box before being promoted here.
-/

namespace SquaresInCircles.Six.Stress.FixedData

private def q (r : ℚ) : PiBound := ⟨r,0⟩
private def p (r : ℚ) : PiBound := ⟨0,r⟩
private def mk (key : String) (wc sc : Bool) (weight : Fin 5 → ℚ)
    (w s : PiBound × PiBound) : FixedRow :=
  ⟨key,⟨weight,wc,sc,2,6⟩,![w,s,(q (1/2),p (1/4))],true⟩

/-- BR17 and the two G27-3 tails, evaluated with the exact support. -/
def bridgeRows : Fin 3 → FixedRow :=
  ![
  mk "BR17-WcSc" true true ![277/1000,319/1000,1/250,193/1000,207/1000]
    (q (-2/5),q (2/5)) (q (1/6),q (3/10)),
  mk "G27-3-low" true false ![271/1000,63/200,1/100,203/1000,201/1000]
    (q (-1/6),q (2/5)) (p (-1/4),q (-2/25)),
  mk "G27-3-high" true false ![111/500,491/1000,19/1000,137/1000,131/1000]
    (q (-1/6),q (2/5)) (q (11/25),p (1/4))
  ]

theorem bridgeRows_valid (i : Fin 3) : (bridgeRows i).spec.valid := by
  fin_cases i <;> decide

end SquaresInCircles.Six.Stress.FixedData
