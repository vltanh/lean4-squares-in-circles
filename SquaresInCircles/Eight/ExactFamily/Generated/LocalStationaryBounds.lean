module

public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula
public import SquaresInCircles.Eight.ExactFamily.FixedEval

/-!
# Eight squares: interval bounds near the stationary point

Bounds on the formulas of `StationaryFormula.lean`, each decided by the kernel with the
fixed-point interval evaluation of `ExactFamily/FixedEval.lean`, at 100 to 200 bits. At the trial
point `F_y` and `F_z` are small for every radius of
`localBox` (`trialFy_bound`, `trialFz_bound`); `F` is positive at `q = qMinus` and negative at
`q = Q0` (`lowerTest_bound`, `upperTest_bound`), and likewise at the two ends of the bracket of
`qStar` (`sharpLowF_bound`, `sharpHighF_bound`); and on the bracket `|F_y|` and `|F_z|` are at
most `10⁻¹⁵` (`sharpTrialFy_bound`, ...). `ExactFamily/Analysis.lean` and
`ExactFamily/Stationary.lean` use these derivative bounds. The coordinate bounds are proved
directly from circle equations and half-angle formulas in `Coordinates.lean` and `Stationary.lean`.
The Hessian and radius-slope bounds follow from circle derivatives and a sheared quadratic form in
`CriticalHessian.lean`; `Analysis.lean` identifies the geometric and symbolic derivatives. Written by `scripts/eight/generate_stationary.py`.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000

namespace SquaresInCircles.Eight.ExactFamily.Generated
open Arithmetic

/-- A fixed-point enclosure gives a bound with real endpoints. -/
private theorem bound_of_bounded {p : ℕ} {B : QBox 3} {f : Formula 3} (l h : ℚ) {lr hr : ℝ}
    (hb : FixedEval.bounded p B f l h = true) (hlr : (l : ℝ) = lr) (hhr : (h : ℝ) = hr)
    {env : Fin 3 → ℝ} (he : B.Mem env) : lr ≤ f.eval env ∧ f.eval env ≤ hr := by
  obtain ⟨h1, h2⟩ := FixedEval.bounded_sound hb he
  exact ⟨hlr ▸ h1, hhr ▸ h2⟩

/-- Rational endpoints as real numerals. -/
local macro "rat_cast" : tactic =>
  `(tactic| simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero])

noncomputable def trialFyBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-46033/50000),(-46033/50000)⟩, ⟨(619/10000),(619/10000)⟩]
theorem trialFy_bound (env : Fin 3 → ℝ) (he : trialFyBox.Mem env) :
    ((-1/5000):ℝ) ≤ formula113.eval env ∧ formula113.eval env ≤ (1/5000) := by
  -- on each half of the radius interval the enclosure lies inside the bound
  rcases le_total (env 0) ((78311/20000 : ℚ) : ℝ) with h | h
  · exact bound_of_bounded (p := 100) (-1/5000) (1/5000)
      (by decide +kernel) (by rat_cast) (by rat_cast) (QBox.mem_left he h)
  · exact bound_of_bounded (p := 100) (-1/5000) (1/5000)
      (by decide +kernel) (by rat_cast) (by rat_cast) (QBox.mem_right he h)

noncomputable def trialFzBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-46033/50000),(-46033/50000)⟩, ⟨(619/10000),(619/10000)⟩]
theorem trialFz_bound (env : Fin 3 → ℝ) (he : trialFzBox.Mem env) :
    ((-1/2500):ℝ) ≤ formula138.eval env ∧ formula138.eval env ≤ (1/2500) := by
  -- on each half of the radius interval the enclosure lies inside the bound
  rcases le_total (env 0) ((78311/20000 : ℚ) : ℝ) with h | h
  · exact bound_of_bounded (p := 100) (-1/2500) (1/2500)
      (by decide +kernel) (by rat_cast) (by rat_cast) (QBox.mem_left he h)
  · exact bound_of_bounded (p := 100) (-1/2500) (1/2500)
      (by decide +kernel) (by rat_cast) (by rat_cast) (QBox.mem_right he h)

noncomputable def lowerTestBox : QBox 3 := ![⟨(7831/2000),(7831/2000)⟩, ⟨(-46033/50000),(-46033/50000)⟩, ⟨(619/10000),(619/10000)⟩]
theorem lowerTest_bound (env : Fin 3 → ℝ) (he : lowerTestBox.Mem env) :
    ((1/8000):ℝ) ≤ formula55.eval env ∧ formula55.eval env ≤ (1/7000) :=
  bound_of_bounded (p := 160) (1/8000) (1/7000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def upperTestBox : QBox 3 := ![⟨(9789/2500),(9789/2500)⟩, ⟨(-46033/50000),(-46033/50000)⟩, ⟨(619/10000),(619/10000)⟩]
theorem upperTest_bound (env : Fin 3 → ℝ) (he : upperTestBox.Mem env) :
    ((-1/4000):ℝ) ≤ formula55.eval env ∧ formula55.eval env ≤ (-1/5000) :=
  bound_of_bounded (p := 160) (-1/4000) (-1/5000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpLowFBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936878163/25000000000000000000)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem sharpLowF_bound (env : Fin 3 → ℝ) (he : sharpLowFBox.Mem env) :
    ((7/10000000000000000):ℝ) ≤ formula55.eval env ∧ formula55.eval env ≤ (1/1250000000000000) :=
  bound_of_bounded (p := 200) (7/10000000000000000) (1/1250000000000000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpLowFyBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936878163/25000000000000000000)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem sharpLowFy_bound (env : Fin 3 → ℝ) (he : sharpLowFyBox.Mem env) :
    ((-1/1000000000000000):ℝ) ≤ formula113.eval env ∧ formula113.eval env ≤ (1/1000000000000000) :=
  bound_of_bounded (p := 200) (-1/1000000000000000) (1/1000000000000000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpLowFzBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936878163/25000000000000000000)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem sharpLowFz_bound (env : Fin 3 → ℝ) (he : sharpLowFzBox.Mem env) :
    ((-1/1000000000000000):ℝ) ≤ formula138.eval env ∧ formula138.eval env ≤ (1/1000000000000000) :=
  bound_of_bounded (p := 200) (-1/1000000000000000) (1/1000000000000000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpHighFBox : QBox 3 := ![⟨(97888353437936885663/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem sharpHighF_bound (env : Fin 3 → ℝ) (he : sharpHighFBox.Mem env) :
    ((-1/2500000000000000):ℝ) ≤ formula55.eval env ∧ formula55.eval env ≤ (-3/10000000000000000) :=
  bound_of_bounded (p := 200) (-1/2500000000000000) (-3/10000000000000000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpTrialFyBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem sharpTrialFy_bound (env : Fin 3 → ℝ) (he : sharpTrialFyBox.Mem env) :
    ((-1/1000000000000000):ℝ) ≤ formula113.eval env ∧ formula113.eval env ≤ (1/1000000000000000) :=
  bound_of_bounded (p := 200) (-1/1000000000000000) (1/1000000000000000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpTrialFzBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem sharpTrialFz_bound (env : Fin 3 → ℝ) (he : sharpTrialFzBox.Mem env) :
    ((-1/1000000000000000):ℝ) ≤ formula138.eval env ∧ formula138.eval env ≤ (1/1000000000000000) := by
  -- on each half of the radius interval the enclosure lies inside the bound
  rcases le_total (env 0) ((97888353437936881913/25000000000000000000 : ℚ) : ℝ) with h | h
  · exact bound_of_bounded (p := 200) (-1/1000000000000000) (1/1000000000000000)
      (by decide +kernel) (by rat_cast) (by rat_cast) (QBox.mem_left he h)
  · exact bound_of_bounded (p := 200) (-1/1000000000000000) (1/1000000000000000)
      (by decide +kernel) (by rat_cast) (by rat_cast) (QBox.mem_right he h)

end SquaresInCircles.Eight.ExactFamily.Generated
