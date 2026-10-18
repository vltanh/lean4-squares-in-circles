module

public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula
public import SquaresInCircles.Eight.ExactFamily.CompactRootCover

/-!
# Stationary localization without an expanded proof forest

This uses the original dyadic precision, split weights and depth ceiling.
An exact-rational Python reconstruction of the old generator visits 22,601
nodes, including 11,141 exclusion leaves, 160 inclusion leaves and 11,300
splits; its maximum depth is 41. This is diagnostic evidence, not a Lean proof.
The ordinary decision below and its soundness proof remain uncompiled.
-/

@[expose] public section
namespace SquaresInCircles.Eight.ExactFamily.Generated
open Arithmetic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stationary_cover_checked :
    CompactRootCover.certify stationaryTargets localBox 48 initialBox = true := by
  decide

noncomputable section

theorem stationary_localization (env : Fin 3 → ℝ)
    (he : initialBox.Mem env) (hz : SimultaneousZeros stationaryTargets env) :
    localBox.Mem env :=
  CompactRootCover.sound stationaryTargets localBox 48 initialBox
    stationary_cover_checked env he hz

end SquaresInCircles.Eight.ExactFamily.Generated
