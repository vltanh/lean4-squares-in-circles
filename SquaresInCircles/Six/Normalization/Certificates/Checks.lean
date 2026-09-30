module
public import SquaresInCircles.Six.Normalization.Certificates.Model

@[expose] public section

/-!
# Concrete arithmetic proof terms

Every declaration below closes a specified finite Boolean computation with
`decide`, which reduces in Lean's kernel. No native-decide axiom, external
certificate flag, Python log, or assumed arithmetic truth is used. The exact
rational mirror has completed these same checks during source development;
Lean compilation/execution is deferred at the user's request.

The 36 coneA2 instances use the same closed central staircase as the supplied
certificate. Their geometric application still needs the strict premise
cx>c0 before dropping CE and the east-quadrant OWN alternative.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SquaresInCircles.Six.Normalization.Certificates
open ProofTools

theorem pinCover_checked : certify pinCoverFormula (fun _ => 1) 0 64 baseRoot = true := by
  decide

theorem window_checked (i : Fin 5) :
    certify (windowFormula i) (fun _ => 1) 0 64 (windowRoot i) = true := by
  fin_cases i <;> decide

theorem coneA1_checked : certify coneA1Formula (fun _ => 1) 0 64 baseRoot = true := by
  decide

theorem coneA2_checked (i j : Fin 8) (hji : j ≤ i) :
    certify (coneA2Formula i j) (fun _ => 1) 0 64 baseRoot = true := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (by omega)
    | decide

theorem moving_checked : certify movingFormula (fun _ => 1) 0 64 movingRoot = true := by
  decide

theorem wd_checked : certify wdFormula ![1,2,1,1,2,1] 0 64 wdRoot = true := by
  decide

end SquaresInCircles.Six.Normalization.Certificates
