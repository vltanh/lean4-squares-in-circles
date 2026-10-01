import SquaresInCircles.Six.Analytic.MixedSecondaryDepth
import SquaresInCircles.Six.Analytic.DoubleSecondaryOwn

/-!
# The stress of a double separation at D

In a double separation at D, W–D and D–S are both separated along the
secondary axis of D. With weight one on these two edges and on C–W and C–S,
where W and S are separated from C along their own axes or along the matching
sides of C, the two forces on D cancel. The weighted sum of the four separating
inequalities then says that `doubleSecondaryGap` is nonpositive.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def wingBaseX (own : Bool) (t : ℝ) : ℝ := if own then 1 else Real.cos t
def wingBaseY (own : Bool) (t : ℝ) : ℝ := if own then 0 else -Real.sin t

/-- The threshold sum minus the works of the forces on W, S and C; `wo` and
`so` record whether W and S are separated from C along their own axes. -/
def doubleSecondaryGap (wo so : Bool) (w s d aw bw aS bS cx cy : ℝ) : ℝ :=
  2+angularWidth w+angularWidth s+angularWidth (d-w)+angularWidth (Real.pi/2+s-d)-
    ((wingBaseX wo w+Real.sin (d-w))*aw+(wingBaseY wo w-Real.cos (d-w))*bw)-
    ((wingBaseX so s+Real.sin (Real.pi/2+s-d))*aS+
      (wingBaseY so s+Real.cos (Real.pi/2+s-d))*bS)-
    (((if wo then Real.cos w else 1)-(if so then Real.sin s else 0))*cx+
      ((if wo then Real.sin w else 0)+(if so then Real.cos s else 1))*cy)

/-- The gap is nonpositive, whichever separators W and S have from C. -/
lemma double_secondary_frozen_nonpositive (wo so : Bool) {w s d aw bw ad bd aS bS cx cy : ℝ}
    (hCW : 0≤centralMargin (if wo then .own else .west) (Real.pi+w) aw bw cx cy)
    (hCS : 0≤centralMargin (if so then .own else .south) (3*Real.pi/2+s) aS bS cx cy)
    (hWD : Seven.SAT.threshold (orientedSquare (Real.pi+w) aw bw)
        (orientedSquare (Real.pi+d) ad bd)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (Real.pi+d) ad bd).center
          (orientedSquare (Real.pi+w) aw bw).center))
    (hDS : Seven.SAT.threshold (orientedSquare (Real.pi+d) ad bd)
        (orientedSquare (3*Real.pi/2+s) aS bS)≤
      dot (normalY (orientedSquare (Real.pi+d) ad bd))
        (sub (orientedSquare (3*Real.pi/2+s) aS bS).center
          (orientedSquare (Real.pi+d) ad bd).center)) :
    doubleSecondaryGap wo so w s d aw bw aS bS cx cy≤0 := by
  have e1 : Real.cos (Real.pi+w)=-Real.cos w := by rw [add_comm]; exact Real.cos_add_pi w
  have e2 : Real.sin (Real.pi+w)=-Real.sin w := by rw [add_comm]; exact Real.sin_add_pi w
  have e3 : Real.cos (3*Real.pi/2+s)=Real.sin s := by
    rw [Real.cos_add,south_cos,south_sin]; ring
  have e4 : Real.sin (3*Real.pi/2+s)=-Real.cos s := by
    rw [Real.sin_add,south_cos,south_sin]; ring
  have hw : angularWidth (Real.pi+w)=angularWidth w := by
    simp [angularWidth,e1,e2,abs_neg]
  have hs : angularWidth (3*Real.pi/2+s)=angularWidth s := by
    simp [angularWidth,Real.cos_add,Real.sin_add,south_cos,south_sin,abs_neg,add_comm]
  change Seven.SAT.threshold (orientedSquare (Real.pi+w) aw bw)
      (orientedSquare (Real.pi+d) ad bd)≤
    frameY (orientedSquare (Real.pi+d) ad bd)
      (sub (orientedSquare (Real.pi+d) ad bd).center
        (orientedSquare (Real.pi+w) aw bw).center) at hWD
  change Seven.SAT.threshold (orientedSquare (Real.pi+d) ad bd)
      (orientedSquare (3*Real.pi/2+s) aS bS)≤
    frameY (orientedSquare (Real.pi+d) ad bd)
      (sub (orientedSquare (3*Real.pi/2+s) aS bS).center
        (orientedSquare (Real.pi+d) ad bd).center) at hDS
  rw [oriented_pair_threshold,pair_frameY_right,
    show (Real.pi+d)-(Real.pi+w)=d-w by ring] at hWD
  rw [oriented_pair_threshold,pair_frameY_left,
    show (3*Real.pi/2+s)-(Real.pi+d)=Real.pi/2+s-d by ring] at hDS
  cases wo <;> cases so
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,centralMargin,centralNormal,
    centerX,centerY,hw,hs,e1,e2,e3,e4] at hCW hCS
  all_goals dsimp [doubleSecondaryGap,wingBaseX,wingBaseY]
  all_goals nlinarith only [hCW,hCS,hWD,hDS]

lemma south_relative_width (s d : ℝ) : angularWidth (Real.pi/2+s-d)=angularWidth (d-s) := by
  rw [show Real.pi/2+s-d=Real.pi/2-(d-s) by ring]
  simp [angularWidth,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,add_comm]

lemma high_diagonal_width (d : ℝ) (hd : 1/2≤d ∧ d≤Real.pi/4) :
    angularWidth d=(Real.cos d+Real.sin d)/2 := by
  have hc := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤d by linarith [hd.1]) (by linarith [hd.2,Real.pi_pos])
  rw [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs]

end SquaresInCircles.Six.Analytic
