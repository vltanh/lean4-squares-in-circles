module

public import SquaresInCircles.Eight.ExactFamily.StationaryExpressions

/-!
# The stationary bracket and local box

The equations and derivatives are named in `StationaryExpressions.lean`.
This module supplies the rational trial point, radius bracket and local box used by
`LocalStationaryBounds.lean`, plus the formula indices used by that checker.
Written by `scripts/eight/generate_stationary.py`.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000

namespace SquaresInCircles.Eight.ExactFamily.Generated
open Arithmetic


abbrev formula55 : Formula 3 := FFormula
abbrev formula113 : Formula 3 := FyFormula
abbrev formula138 : Formula 3 := FzFormula

/-- The box of `(q, y, z)`: `q` in `[qMinus, Q0]` and `(y, z)` in the rectangle `poseBox`
of `ExactFamily/Analysis.lean`. -/
noncomputable def localBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
/-- Refined trial position, used for the numerical bracket (`sharpPose_close`). -/
noncomputable def trialY : ℝ := -0.92065667800760613175
/-- Refined half-angle tangent, used only for the numerical bracket. -/
noncomputable def trialZ : ℝ := 0.0618974110076603597
/-- The lower end of the bracket of `qStar` (`qStar_bracket`). -/
noncomputable def sharpLower : ℝ := 3.91553413751747512652
/-- The upper end of the bracket of `qStar`. -/
noncomputable def sharpUpper : ℝ := 3.91553413751747542652

end SquaresInCircles.Eight.ExactFamily.Generated
