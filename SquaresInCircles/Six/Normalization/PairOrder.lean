import SquaresInCircles.Six.Normalization.CardinalWindows
import SquaresInCircles.Seven.SeparatingAxes

/-!
# D4 and N18: actual pair separation implies the primary order

All four axes of both squares are retained. Their real-coordinate formulas
are proved from the repository's SAT theorem before applying the concrete
W/D arithmetic check. No centre-distance or bounding-box surrogate replaces
interior-disjointness.
-/

noncomputable section
namespace SquaresInCircles.Six.Normalization
open Certificates ProofTools

lemma oriented_relativeC (t a b T A B : ℝ) :
    relativeC (orientedSquare t a b) (orientedSquare T A B) = Real.cos (T-t) := by
  simp only [relativeC,orientedSquare,Real.cos_sub]
  ring

lemma oriented_relativeS (t a b T A B : ℝ) :
    relativeS (orientedSquare t a b) (orientedSquare T A B) = Real.sin (T-t) := by
  simp only [relativeS,orientedSquare,Real.sin_sub]
  ring

lemma oriented_pair_threshold (t a b T A B : ℝ) :
    Seven.SAT.threshold (orientedSquare t a b) (orientedSquare T A B) =
      1/2+angularWidth (T-t) := by
  rw [Seven.SAT.threshold,oriented_relativeC,oriented_relativeS]
  dsimp [angularWidth]
  ring

lemma pair_frameX_left (t a b T A B : ℝ) :
    frameX (orientedSquare t a b)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center) =
      A*Real.cos (T-t)-B*Real.sin (T-t)-a := by
  dsimp [frameX,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination -a*(Real.sin_sq_add_cos_sq t)

lemma pair_frameY_left (t a b T A B : ℝ) :
    frameY (orientedSquare t a b)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center) =
      A*Real.sin (T-t)+B*Real.cos (T-t)-b := by
  dsimp [frameY,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination -b*(Real.sin_sq_add_cos_sq t)

lemma pair_frameX_right (t a b T A B : ℝ) :
    frameX (orientedSquare T A B)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center) =
      A-a*Real.cos (T-t)-b*Real.sin (T-t) := by
  dsimp [frameX,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination A*(Real.sin_sq_add_cos_sq T)

lemma pair_frameY_right (t a b T A B : ℝ) :
    frameY (orientedSquare T A B)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center) =
      B+a*Real.sin (T-t)-b*Real.cos (T-t) := by
  dsimp [frameY,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination B*(Real.sin_sq_add_cos_sq T)

def pairMargin (i : Fin 4) (t a b T A B : ℝ) : ℝ :=
  let d := T-t
  let h := 1/2+angularWidth d
  ![|A*Real.cos d-B*Real.sin d-a|-h,
    |A*Real.sin d+B*Real.cos d-b|-h,
    |A-a*Real.cos d-b*Real.sin d|-h,
    |B+a*Real.sin d-b*Real.cos d|-h] i

lemma pair_separators_complete {t a b T A B : ℝ}
    (hd : ∀ p, ¬ (openSquare (orientedSquare t a b) p ∧
      openSquare (orientedSquare T A B) p)) :
    ∃ i : Fin 4, 0 ≤ pairMargin i t a b T A B := by
  have h := Seven.SAT.separating_axes (orientedSquare t a b) (orientedSquare T A B) hd
  rw [oriented_pair_threshold,pair_frameX_left,pair_frameY_left,
    pair_frameX_right,pair_frameY_right] at h
  rcases h with h | h | h | h
  · exact ⟨0,by dsimp [pairMargin]; linarith⟩
  · exact ⟨1,by dsimp [pairMargin]; linarith⟩
  · exact ⟨2,by dsimp [pairMargin]; linarith⟩
  · exact ⟨3,by dsimp [pairMargin]; linarith⟩

@[simp] lemma denote_pairMarginE {n : ℕ} (x : Fin n → ℝ)
    (i : Fin 4) (t a b T A B : Expr n) :
    Expr.denote (pairMarginE i t a b T A B) x =
      pairMargin i (Expr.denote t x) (Expr.denote a x) (Expr.denote b x)
        (Expr.denote T x) (Expr.denote A x) (Expr.denote B x) := by
  fin_cases i <;> simp [pairMarginE,pairMargin,widthE,angularWidth,
    Expr.denote,div_eq_mul_inv,sub_eq_add_neg]

lemma wdRoot_mem {R : ℝ} (P : PinPacking R) (hD : P.phase 3 ≤ 5*Real.pi/4) :
    wdRoot.Mem ![P.phase 2,P.radial 2,P.transverse 2,
      P.phase 3,P.radial 3,P.transverse 3] := by
  have hw := P.window 2
  have hd := P.window 3
  norm_num [phaseCenter,windowLower,windowUpper] at hw hd
  have aw := (P.contained 2).a_le_rho0
  have ad := (P.contained 3).a_le_rho0
  have bw := (P.contained 2).bounds (P.avoidsCore 2)
  have bd := (P.contained 3).bounds (P.avoidsCore 3)
  have uw := abs_lt.mp bw.2.2
  have ud := abs_lt.mp bd.2.2
  intro i
  fin_cases i <;> norm_num [wdRoot,RInterval.Mem] <;> constructor <;>
    linarith [hw.1,hw.2,hd.1,hD,aw,ad,bw.1,bd.1,uw.1,uw.2,ud.1,ud.2,
      rho0_upper,Real.pi_gt_d4,Real.pi_lt_d4]

/-- D4, now using the actual pair's disjoint interiors and all four axes. -/
theorem PinPacking.west_before_diagonal {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) : P.phase 2 < P.phase 3 := by
  let x : Fin 6 → ℝ := ![P.phase 2,P.radial 2,P.transverse 2,
    P.phase 3,P.radial 3,P.transverse 3]
  have hcert := certify_sound wdFormula ![1,2,1,1,2,1] 0 64 wd_checked (wdRoot_mem P hD)
  have hW := exists_upper_of_actual P.box.1 P.box.2 (P.separator 2)
  have hD' := exists_upper_of_actual P.box.1 P.box.2 (P.separator 3)
  have hBW : Formula.Holds (basicE (.var 0) (.var 1) (.var 2) 0 c0E 0 c0E) x := by
    apply basicE_holds
    · simpa [x,Expr.denote] using P.contained 2
    · simpa [x,Expr.denote] using hW
  have hBD : Formula.Holds (basicE (.var 3) (.var 4) (.var 5) 0 c0E 0 c0E) x := by
    apply basicE_holds
    · simpa [x,Expr.denote] using P.contained 3
    · simpa [x,Expr.denote] using hD'
  have hpW : Formula.Holds
      (.lt 0 (pinMarginE (.var 0) (.var 1) (.var 2) (pinE 2).1 (pinE 2).2)) x := by
    simpa [x,Formula.Holds,Expr.denote] using pinMargin_pos_iff.mpr (P.pin 2)
  have hpD : Formula.Holds
      (.lt 0 (pinMarginE (.var 3) (.var 4) (.var 5) (pinE 3).1 (pinE 3).2)) x := by
    simpa [x,Formula.Holds,Expr.denote] using pinMargin_pos_iff.mpr (P.pin 3)
  obtain ⟨i,hi⟩ := pair_separators_complete (P.exterior_disjoint 2 3 (by decide))
  have hpairs : Formula.Holds
      (.any ((List.finRange 4).map (fun j => .le 0
        (pairMarginE j (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))))) x := by
    apply (Formula.holds_any_map x _ _).mpr
    exact ⟨i,by simp,by simpa [x,Formula.Holds,Expr.denote] using hi⟩
  rcases hcert with h | h
  · simpa [x,Formula.Holds,Expr.denote] using h
  · apply False.elim
    apply h
    exact ⟨hBW,hBD,hpW,hpD,hpairs,True.intro⟩

/-- The normalized D window needed by the retained Appendix A and A2. -/
lemma PinPacking.diagonal_deviation {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    -2/5 < P.phase 3-Real.pi ∧ P.phase 3-Real.pi ≤ Real.pi/4 := by
  have h := P.window 3
  norm_num [windowLower,windowUpper,phaseCenter] at h
  constructor <;> linarith [h.1,h.2,Real.pi_gt_d2]

/-- N18, with every link of the cyclic primary order accounted for. -/
theorem PinPacking.cyclic_primary_order {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    P.phase 0 < P.phase 1 ∧ P.phase 1 < P.phase 2 ∧
      P.phase 2 < P.phase 3 ∧ P.phase 3 < P.phase 4 ∧ P.phase 4 < P.phase 0+2*Real.pi := by
  have he := P.window 0
  have hn := P.window 1
  have hw := P.window 2
  have hs := P.window 4
  norm_num [windowLower,windowUpper,phaseCenter] at he hn hw hs
  exact ⟨by linarith [he.2,hn.1,Real.pi_gt_d2],
    by linarith [hn.2,hw.1,Real.pi_gt_d2],P.west_before_diagonal hD,
    by linarith [hs.1,Real.pi_gt_d2],by linarith [hs.2,he.1,Real.pi_gt_d2]⟩

end SquaresInCircles.Six.Normalization
