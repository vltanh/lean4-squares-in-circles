module

public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula
public import SquaresInCircles.Eight.ExactFamily.FixedEval

/-! Interval certificates near the stationary point: regularity of `F`, `F_y` and `F_z` on
`localBox`, bounds there on `F_q`, `F_yy`, the coordinates of the chain and the determinant of the
shifted Hessian, and the values of `F` and its first derivatives at the trial point and at the ends
of the bracket of `qStar`. Every bound is decided in the kernel by fixed-point interval evaluation
(`FixedEval`). -/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option linter.all false

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

noncomputable def fullFBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem fullF_regular (env : Fin 3 → ℝ) (he : fullFBox.Mem env) :
    formula55.RegularAt env :=
  FixedEval.regular_sound (p := 80) (by decide +kernel) he

noncomputable def fullFyBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem fullFy_regular (env : Fin 3 → ℝ) (he : fullFyBox.Mem env) :
    formula113.RegularAt env :=
  FixedEval.regular_sound (p := 80) (by decide +kernel) he

noncomputable def fullFzBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem fullFz_regular (env : Fin 3 → ℝ) (he : fullFzBox.Mem env) :
    formula138.RegularAt env :=
  FixedEval.regular_sound (p := 80) (by decide +kernel) he

noncomputable def fullFqBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem fullFq_bound (env : Fin 3 → ℝ) (he : fullFqBox.Mem env) :
    (-4:ℝ) ≤ formula87.eval env ∧ formula87.eval env ≤ -3 :=
  bound_of_bounded (p := 80) (-4) (-3)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def fullFyyBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem fullFyy_bound (env : Fin 3 → ℝ) (he : fullFyyBox.Mem env) :
    (6:ℝ) ≤ formula195.eval env ∧ formula195.eval env ≤ 9 :=
  bound_of_bounded (p := 80) (6) (9)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def localXOneBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem localXOne_bound (env : Fin 3 → ℝ) (he : localXOneBox.Mem env) :
    ((4357/2500):ℝ) ≤ formula10.eval env ∧ formula10.eval env ≤ (17649/10000) :=
  bound_of_bounded (p := 80) (4357/2500) (17649/10000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def localXTwoBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem localXTwo_bound (env : Fin 3 → ℝ) (he : localXTwoBox.Mem env) :
    ((8207/5000):ℝ) ≤ formula15.eval env ∧ formula15.eval env ≤ (16691/10000) :=
  bound_of_bounded (p := 80) (8207/5000) (16691/10000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def localYThreeBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem localYThree_bound (env : Fin 3 → ℝ) (he : localYThreeBox.Mem env) :
    ((14387/10000):ℝ) ≤ formula21.eval env ∧ formula21.eval env ≤ (14643/10000) :=
  bound_of_bounded (p := 80) (14387/10000) (14643/10000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def localXFourBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem localXFour_bound (env : Fin 3 → ℝ) (he : localXFourBox.Mem env) :
    ((-19049/10000):ℝ) ≤ formula28.eval env ∧ formula28.eval env ≤ (-9487/5000) :=
  bound_of_bounded (p := 80) (-19049/10000) (-9487/5000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def localHOneBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem localHOne_bound (env : Fin 3 → ℝ) (he : localHOneBox.Mem env) :
    ((-14263/10000):ℝ) ≤ formula42.eval env ∧ formula42.eval env ≤ (-6599/5000) :=
  bound_of_bounded (p := 80) (-14263/10000) (-6599/5000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def localHTwoBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-179/200)⟩, ⟨(1/20),(81/1000)⟩]
theorem localHTwo_bound (env : Fin 3 → ℝ) (he : localHTwoBox.Mem env) :
    ((-3829/2500):ℝ) ≤ formula50.eval env ∧ formula50.eval env ≤ (-6601/5000) :=
  bound_of_bounded (p := 80) (-3829/2500) (-6601/5000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det00Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-1853/2000)⟩, ⟨(1/20),(231/4000)⟩]
theorem det00_bound (env : Fin 3 → ℝ) (he : det00Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det01Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-1853/2000)⟩, ⟨(231/4000),(131/2000)⟩]
theorem det01_bound (env : Fin 3 → ℝ) (he : det01Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det02Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-1853/2000)⟩, ⟨(131/2000),(293/4000)⟩]
theorem det02_bound (env : Fin 3 → ℝ) (he : det02Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det03Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-937/1000),(-1853/2000)⟩, ⟨(293/4000),(81/1000)⟩]
theorem det03_bound (env : Fin 3 → ℝ) (he : det03Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det10Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-1853/2000),(-229/250)⟩, ⟨(1/20),(231/4000)⟩]
theorem det10_bound (env : Fin 3 → ℝ) (he : det10Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det11Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-1853/2000),(-229/250)⟩, ⟨(231/4000),(131/2000)⟩]
theorem det11_bound (env : Fin 3 → ℝ) (he : det11Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det12Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-1853/2000),(-229/250)⟩, ⟨(131/2000),(293/4000)⟩]
theorem det12_bound (env : Fin 3 → ℝ) (he : det12Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det13Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-1853/2000),(-229/250)⟩, ⟨(293/4000),(81/1000)⟩]
theorem det13_bound (env : Fin 3 → ℝ) (he : det13Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det20Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-229/250),(-1811/2000)⟩, ⟨(1/20),(231/4000)⟩]
theorem det20_bound (env : Fin 3 → ℝ) (he : det20Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det21Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-229/250),(-1811/2000)⟩, ⟨(231/4000),(131/2000)⟩]
theorem det21_bound (env : Fin 3 → ℝ) (he : det21Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det22Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-229/250),(-1811/2000)⟩, ⟨(131/2000),(293/4000)⟩]
theorem det22_bound (env : Fin 3 → ℝ) (he : det22Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det23Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-229/250),(-1811/2000)⟩, ⟨(293/4000),(81/1000)⟩]
theorem det23_bound (env : Fin 3 → ℝ) (he : det23Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det30Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-1811/2000),(-179/200)⟩, ⟨(1/20),(231/4000)⟩]
theorem det30_bound (env : Fin 3 → ℝ) (he : det30Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det31Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-1811/2000),(-179/200)⟩, ⟨(231/4000),(131/2000)⟩]
theorem det31_bound (env : Fin 3 → ℝ) (he : det31Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det32Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-1811/2000),(-179/200)⟩, ⟨(131/2000),(293/4000)⟩]
theorem det32_bound (env : Fin 3 → ℝ) (he : det32Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def det33Box : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-1811/2000),(-179/200)⟩, ⟨(293/4000),(81/1000)⟩]
theorem det33_bound (env : Fin 3 → ℝ) (he : det33Box.Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 :=
  bound_of_bounded (p := 80) (10) (100)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def determinantBoxes : Fin 4 → Fin 4 → QBox 3 :=
  ![![det00Box, det01Box, det02Box, det03Box], ![det10Box, det11Box, det12Box, det13Box], ![det20Box, det21Box, det22Box, det23Box], ![det30Box, det31Box, det32Box, det33Box]]

theorem determinant_bound (i j : Fin 4) (env : Fin 3 → ℝ)
    (he : (determinantBoxes i j).Mem env) :
    (10:ℝ) ≤ formula258.eval env ∧ formula258.eval env ≤ 100 := by
  fin_cases i <;> fin_cases j
  · exact det00_bound env he
  · exact det01_bound env he
  · exact det02_bound env he
  · exact det03_bound env he
  · exact det10_bound env he
  · exact det11_bound env he
  · exact det12_bound env he
  · exact det13_bound env he
  · exact det20_bound env he
  · exact det21_bound env he
  · exact det22_bound env he
  · exact det23_bound env he
  · exact det30_bound env he
  · exact det31_bound env he
  · exact det32_bound env he
  · exact det33_bound env he

theorem determinant_cover (env : Fin 3 → ℝ) (he : localBox.Mem env) :
    ∃ i j : Fin 4, (determinantBoxes i j).Mem env := by
  have hq := he 0; have hy := he 1; have hz := he 2
  by_cases hy0 : env 1 ≤ ((-1853/2000 : ℚ) : ℝ)
  ·
    by_cases hz0 : env 2 ≤ ((231/4000 : ℚ) : ℝ)
    ·
      refine ⟨0, 0, fun k => ?_⟩
      fin_cases k
      exacts [hq, ⟨hy.1, hy0⟩, ⟨hz.1, hz0⟩]
    ·
      by_cases hz1 : env 2 ≤ ((131/2000 : ℚ) : ℝ)
      ·
        refine ⟨0, 1, fun k => ?_⟩
        fin_cases k
        exacts [hq, ⟨hy.1, hy0⟩, ⟨le_of_lt (lt_of_not_ge hz0), hz1⟩]
      ·
        by_cases hz2 : env 2 ≤ ((293/4000 : ℚ) : ℝ)
        ·
          refine ⟨0, 2, fun k => ?_⟩
          fin_cases k
          exacts [hq, ⟨hy.1, hy0⟩, ⟨le_of_lt (lt_of_not_ge hz1), hz2⟩]
        ·
          refine ⟨0, 3, fun k => ?_⟩
          fin_cases k
          exacts [hq, ⟨hy.1, hy0⟩, ⟨le_of_lt (lt_of_not_ge hz2), hz.2⟩]
  ·
    by_cases hy1 : env 1 ≤ ((-229/250 : ℚ) : ℝ)
    ·
      by_cases hz0 : env 2 ≤ ((231/4000 : ℚ) : ℝ)
      ·
        refine ⟨1, 0, fun k => ?_⟩
        fin_cases k
        exacts [hq, ⟨le_of_lt (lt_of_not_ge hy0), hy1⟩, ⟨hz.1, hz0⟩]
      ·
        by_cases hz1 : env 2 ≤ ((131/2000 : ℚ) : ℝ)
        ·
          refine ⟨1, 1, fun k => ?_⟩
          fin_cases k
          exacts [hq, ⟨le_of_lt (lt_of_not_ge hy0), hy1⟩, ⟨le_of_lt (lt_of_not_ge hz0), hz1⟩]
        ·
          by_cases hz2 : env 2 ≤ ((293/4000 : ℚ) : ℝ)
          ·
            refine ⟨1, 2, fun k => ?_⟩
            fin_cases k
            exacts [hq, ⟨le_of_lt (lt_of_not_ge hy0), hy1⟩, ⟨le_of_lt (lt_of_not_ge hz1), hz2⟩]
          ·
            refine ⟨1, 3, fun k => ?_⟩
            fin_cases k
            exacts [hq, ⟨le_of_lt (lt_of_not_ge hy0), hy1⟩, ⟨le_of_lt (lt_of_not_ge hz2), hz.2⟩]
    ·
      by_cases hy2 : env 1 ≤ ((-1811/2000 : ℚ) : ℝ)
      ·
        by_cases hz0 : env 2 ≤ ((231/4000 : ℚ) : ℝ)
        ·
          refine ⟨2, 0, fun k => ?_⟩
          fin_cases k
          exacts [hq, ⟨le_of_lt (lt_of_not_ge hy1), hy2⟩, ⟨hz.1, hz0⟩]
        ·
          by_cases hz1 : env 2 ≤ ((131/2000 : ℚ) : ℝ)
          ·
            refine ⟨2, 1, fun k => ?_⟩
            fin_cases k
            exacts [hq, ⟨le_of_lt (lt_of_not_ge hy1), hy2⟩, ⟨le_of_lt (lt_of_not_ge hz0), hz1⟩]
          ·
            by_cases hz2 : env 2 ≤ ((293/4000 : ℚ) : ℝ)
            ·
              refine ⟨2, 2, fun k => ?_⟩
              fin_cases k
              exacts [hq, ⟨le_of_lt (lt_of_not_ge hy1), hy2⟩, ⟨le_of_lt (lt_of_not_ge hz1), hz2⟩]
            ·
              refine ⟨2, 3, fun k => ?_⟩
              fin_cases k
              exacts [hq, ⟨le_of_lt (lt_of_not_ge hy1), hy2⟩, ⟨le_of_lt (lt_of_not_ge hz2), hz.2⟩]
      ·
        by_cases hz0 : env 2 ≤ ((231/4000 : ℚ) : ℝ)
        ·
          refine ⟨3, 0, fun k => ?_⟩
          fin_cases k
          exacts [hq, ⟨le_of_lt (lt_of_not_ge hy2), hy.2⟩, ⟨hz.1, hz0⟩]
        ·
          by_cases hz1 : env 2 ≤ ((131/2000 : ℚ) : ℝ)
          ·
            refine ⟨3, 1, fun k => ?_⟩
            fin_cases k
            exacts [hq, ⟨le_of_lt (lt_of_not_ge hy2), hy.2⟩, ⟨le_of_lt (lt_of_not_ge hz0), hz1⟩]
          ·
            by_cases hz2 : env 2 ≤ ((293/4000 : ℚ) : ℝ)
            ·
              refine ⟨3, 2, fun k => ?_⟩
              fin_cases k
              exacts [hq, ⟨le_of_lt (lt_of_not_ge hy2), hy.2⟩, ⟨le_of_lt (lt_of_not_ge hz1), hz2⟩]
            ·
              refine ⟨3, 3, fun k => ?_⟩
              fin_cases k
              exacts [hq, ⟨le_of_lt (lt_of_not_ge hy2), hy.2⟩, ⟨le_of_lt (lt_of_not_ge hz2), hz.2⟩]

noncomputable def trialFyBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem trialFy_bound (env : Fin 3 → ℝ) (he : trialFyBox.Mem env) :
    ((-1/5000):ℝ) ≤ formula113.eval env ∧ formula113.eval env ≤ (1/5000) :=
  bound_of_bounded (p := 100) (-1/5000) (1/5000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def trialFzBox : QBox 3 := ![⟨(7831/2000),(9789/2500)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem trialFz_bound (env : Fin 3 → ℝ) (he : trialFzBox.Mem env) :
    ((-1/2500):ℝ) ≤ formula138.eval env ∧ formula138.eval env ≤ (1/2500) :=
  bound_of_bounded (p := 100) (-1/2500) (1/2500)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def lowerTestBox : QBox 3 := ![⟨(7831/2000),(7831/2000)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
theorem lowerTest_bound (env : Fin 3 → ℝ) (he : lowerTestBox.Mem env) :
    ((1/8000):ℝ) ≤ formula55.eval env ∧ formula55.eval env ≤ (1/7000) :=
  bound_of_bounded (p := 160) (1/8000) (1/7000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def upperTestBox : QBox 3 := ![⟨(9789/2500),(9789/2500)⟩, ⟨(-3682626712030424527/4000000000000000000),(-3682626712030424527/4000000000000000000)⟩, ⟨(618974110076603597/10000000000000000000),(618974110076603597/10000000000000000000)⟩]
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

noncomputable def sharpBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]

noncomputable def sharpXOneBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]
theorem sharpXOne_bound (env : Fin 3 → ℝ) (he : sharpXOneBox.Mem env) :
    ((10947/6250):ℝ) ≤ formula10.eval env ∧ formula10.eval env ≤ (175159/100000) :=
  bound_of_bounded (p := 160) (10947/6250) (175159/100000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpXTwoBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]
theorem sharpXTwo_bound (env : Fin 3 → ℝ) (he : sharpXTwoBox.Mem env) :
    ((165843/100000):ℝ) ≤ formula15.eval env ∧ formula15.eval env ≤ (41463/25000) :=
  bound_of_bounded (p := 160) (165843/100000) (41463/25000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpYThreeBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]
theorem sharpYThree_bound (env : Fin 3 → ℝ) (he : sharpYThreeBox.Mem env) :
    ((29091/20000):ℝ) ≤ formula21.eval env ∧ formula21.eval env ≤ (18183/12500) :=
  bound_of_bounded (p := 160) (29091/20000) (18183/12500)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpXFourBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]
theorem sharpXFour_bound (env : Fin 3 → ℝ) (he : sharpXFourBox.Mem env) :
    ((-95107/50000):ℝ) ≤ formula28.eval env ∧ formula28.eval env ≤ (-190211/100000) :=
  bound_of_bounded (p := 160) (-95107/50000) (-190211/100000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpCosineBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]
theorem sharpCosine_bound (env : Fin 3 → ℝ) (he : sharpCosineBox.Mem env) :
    ((99231/100000):ℝ) ≤ formula34.eval env ∧ formula34.eval env ≤ (49621/50000) :=
  bound_of_bounded (p := 160) (99231/100000) (49621/50000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpSineBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]
theorem sharpSine_bound (env : Fin 3 → ℝ) (he : sharpSineBox.Mem env) :
    ((12327/100000):ℝ) ≤ formula36.eval env ∧ formula36.eval env ≤ (6169/50000) :=
  bound_of_bounded (p := 160) (12327/100000) (6169/50000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpHOneBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]
theorem sharpHOne_bound (env : Fin 3 → ℝ) (he : sharpHOneBox.Mem env) :
    ((-136797/100000):ℝ) ≤ formula42.eval env ∧ formula42.eval env ≤ (-34187/25000) :=
  bound_of_bounded (p := 160) (-136797/100000) (-34187/25000)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

noncomputable def sharpHTwoBox : QBox 3 := ![⟨(97888353437936878163/25000000000000000000),(97888353437936885663/25000000000000000000)⟩, ⟨(-3682626712034424527/4000000000000000000),(-3682626712026424527/4000000000000000000)⟩, ⟨(618974110066603597/10000000000000000000),(618974110086603597/10000000000000000000)⟩]
theorem sharpHTwo_bound (env : Fin 3 → ℝ) (he : sharpHTwoBox.Mem env) :
    ((-71511/50000):ℝ) ≤ formula50.eval env ∧ formula50.eval env ≤ (-4468/3125) :=
  bound_of_bounded (p := 160) (-71511/50000) (-4468/3125)
    (by decide +kernel) (by rat_cast) (by rat_cast) he

end SquaresInCircles.Eight.ExactFamily.Generated
