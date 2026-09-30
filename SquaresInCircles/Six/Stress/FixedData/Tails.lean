module
public import SquaresInCircles.Six.Stress.FixedData.Default

@[expose] public section

namespace SquaresInCircles.Six.Stress.FixedData

private def q (r : ℚ) : PiBound := ⟨r,0⟩
private def p (r : ℚ) : PiBound := ⟨0,r⟩
private def mk (key : String) (weight : Fin 5 → ℚ)
    (w s : PiBound × PiBound) : FixedRow :=
  ⟨key,⟨weight,false,false,2,6⟩,![w,s,(q (1/2),p (1/4))],true⟩

/-- These are exact-support tails, not the invalid dominance-selected cap proofs. -/
def tailsRows : Fin 3 → FixedRow :=
  ![
  mk "A23C3" ![2/5,283/1000,0,83/500,151/1000]
    (q (-2/3),q (-21/50)) (q (-1/6),q (1/2)),
  mk "P29C2-neg" ![299/1000,77/250,0,197/1000,49/250]
    (q (-21/50),q (2/25)) (q (-1/6),q (-2/25)),
  mk "P29C2-pos" ![251/1000,433/1000,0,4/25,39/250]
    (q (-21/50),q (2/25)) (q (21/50),q (1/2))
  ]

theorem tailsRows_valid (i : Fin 3) : (tailsRows i).spec.valid := by
  fin_cases i <;> decide

end SquaresInCircles.Six.Stress.FixedData
