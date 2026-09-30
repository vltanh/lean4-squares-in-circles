module
public import SquaresInCircles.Six.Stress.FixedData.Default
public import SquaresInCircles.Six.Stress.FixedData.Hard
public import SquaresInCircles.Six.Stress.FixedData.Tails
public import SquaresInCircles.Six.Stress.FixedData.AppendixC
public import SquaresInCircles.Six.Stress.FixedData.Bridges

@[expose] public section

/-!
# The fixed-row arithmetic proof bodies

The source proofs use ordinary kernel `decide`, never native_decide or an
external success flag. Their mathematical inequalities have an independent
exact-dyadic replay at the larger R0 radius. The inventory is 217 rows:
59 default, 53 hard, 3 original tails, 99 Appendix-C, and 3 survivor bridges.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SquaresInCircles.Six.Stress.FixedData

theorem defaultRows_checked (i : Fin 59) : (defaultRows i).check=true := by
  fin_cases i <;> decide

theorem hardRows_checked (i : Fin 53) : (hardRows i).check=true := by
  fin_cases i <;> decide

theorem tailsRows_checked (i : Fin 3) : (tailsRows i).check=true := by
  fin_cases i <;> decide

theorem appendixcRows_checked (i : Fin 99) : (appendixcRows i).check=true := by
  fin_cases i <;> decide

theorem bridgeRows_checked (i : Fin 3) : (bridgeRows i).check=true := by
  fin_cases i <;> decide

/-- Stable namespaces prevent row-number confusion across inventories. -/
inductive RowId where
  | main : Fin 59 → RowId
  | hard : Fin 53 → RowId
  | tail : Fin 3 → RowId
  | app : Fin 99 → RowId
  | bridge : Fin 3 → RowId
  deriving DecidableEq, Fintype

namespace RowId

def row : RowId → FixedRow
  | .main i => defaultRows i
  | .hard i => hardRows i
  | .tail i => tailsRows i
  | .app i => appendixcRows i
  | .bridge i => bridgeRows i

lemma valid (i : RowId) : i.row.spec.valid := by
  cases i with
  | main j => exact defaultRows_valid j
  | hard j => exact hardRows_valid j
  | tail j => exact tailsRows_valid j
  | app j => exact appendixcRows_valid j
  | bridge j => exact bridgeRows_valid j

lemma checked (i : RowId) : i.row.check=true := by
  cases i with
  | main j => exact defaultRows_checked j
  | hard j => exact hardRows_checked j
  | tail j => exact tailsRows_checked j
  | app j => exact appendixcRows_checked j
  | bridge j => exact bridgeRows_checked j

noncomputable section

/-- Exported arithmetic statements contain no caller-supplied numerical premise. -/
theorem positive (i : RowId) {w s d : ℝ} (h : i.row.InDomain w s d) :
    0<i.row.spec.defect w s d := i.row.positive i.checked h

/-- Every realized row in its exact domain contradicts actual packing. -/
theorem excludes (i : RowId) {R : ℝ} (P : Normalization.NormalizedPacking R)
    (hs : i.row.spec.Realized P)
    (hd : i.row.InDomain (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle) : False :=
  i.row.excludes i.valid i.checked P hs hd

end
end RowId
end SquaresInCircles.Six.Stress.FixedData
