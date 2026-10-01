import SquaresInCircles.Six.Analytic.PinDirectedAxes

/-!
# The W and D pins have the same transverse order in both frames

The pins are separated by pi/3. Subtracting their transverse projections gives
(9/10) cos(13*pi/12 - t), which is positive on both relevant primary windows.
This explains the orientation exclusion in the W/D proof without numerical
pin coordinates or a table of permitted directions.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

def polarPin (r t : ℝ) : Point := (r*Real.cos t,r*Real.sin t)

lemma polar_transverse_projection (r q t a b : ℝ) :
    dot (normalY (orientedSquare t a b)) (polarPin r q) = r*Real.sin (q-t) := by
  dsimp [dot,normalY,orientedSquare,polarPin]
  rw [Real.sin_sub]
  ring

lemma west_diagonal_projection_difference (t a b : ℝ) :
    dot (normalY (orientedSquare t a b)) (polarPin (9/10) (5*Real.pi/4))-
      dot (normalY (orientedSquare t a b)) (polarPin (9/10) (11*Real.pi/12)) =
      (9/10)*Real.cos (13*Real.pi/12-t) := by
  rw [polar_transverse_projection,polar_transverse_projection]
  have hD : 5*Real.pi/4-t=(13*Real.pi/12-t)+Real.pi/6 := by ring
  have hW : 11*Real.pi/12-t=(13*Real.pi/12-t)-Real.pi/6 := by ring
  rw [hD,hW,Real.sin_add,Real.sin_sub (13*Real.pi/12-t) (Real.pi/6),Real.sin_pi_div_six]
  ring

lemma west_diagonal_pin_order {t a b : ℝ}
    (ht0 : Real.pi-2/3 ≤ t) (ht1 : t ≤ 5*Real.pi/4) :
    dot (normalY (orientedSquare t a b)) (polarPin (9/10) (11*Real.pi/12)) <
      dot (normalY (orientedSquare t a b)) (polarPin (9/10) (5*Real.pi/4)) := by
  have hcos : 0 < Real.cos (13*Real.pi/12-t) :=
    Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith [ht0,ht1,Real.pi_gt_d2])
  have hpos := mul_pos (show (0:ℝ) < 9/10 by norm_num) hcos
  rw [← west_diagonal_projection_difference t a b] at hpos
  exact sub_pos.mp hpos

end SquaresInCircles.Six.Analytic
