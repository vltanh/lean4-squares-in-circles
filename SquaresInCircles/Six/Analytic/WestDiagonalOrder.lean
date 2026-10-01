import SquaresInCircles.Six.Analytic.PairProjectionBounds
import SquaresInCircles.Six.Analytic.PinProjections

/-!
# Analytic W/D order

Assume the primary directions were reversed and write e=t-T. The broad windows
imply 0 <= e <= 41/40. The elementary cosine lower bound rules out both primary
axes. The sixty-degree pin identity forces both transverse separators to point
from W to D, but their forward projections are strictly below the threshold.
Thus none of the four actual separating axes can separate the squares.

The stated chart bounds, pins and broad windows are ordinary hypotheses. Their
construction for every packing is not assumed to be analytic by this lemma.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

theorem west_before_diagonal {t a b T A B : ℝ}
    (hW : ContainedChart a |b|) (hD : ContainedChart A |B|)
    (ha : 177/200 ≤ a) (hA : 177/200 ≤ A)
    (hb : |b| ≤ 117/250) (hB : |B| ≤ 117/250)
    (ht : Real.pi-2/3 ≤ t ∧ t ≤ Real.pi+5/8)
    (hT : Real.pi-2/5 ≤ T ∧ T ≤ 5*Real.pi/4)
    (hpW : openSquare (orientedSquare t a b) (polarPin (9/10) (11*Real.pi/12)))
    (hpD : openSquare (orientedSquare T A B) (polarPin (9/10) (5*Real.pi/4)))
    (hd : ∀ p, ¬ (openSquare (orientedSquare t a b) p ∧
      openSquare (orientedSquare T A B) p)) : t < T := by
  by_contra! hrev
  let e := t-T
  have he : 0 ≤ e ∧ e ≤ 41/40 := by
    dsimp [e]
    constructor <;> linarith [ht.2,hT.1]
  obtain ⟨hc,hs,hunit⟩ := reversed_phase_trig he
  have hc0 : 0 ≤ Real.cos e := by linarith
  have hdif : T-t= -e := by dsimp [e]; ring
  have hwidth : 1/2+angularWidth (T-t) = 1/2+(Real.cos e+Real.sin e)/2 := by
    rw [hdif]
    simp only [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg,
      abs_of_nonneg hc0,abs_of_nonneg hs]
  have hpinW := west_diagonal_pin_order (a := a) (b := b) ht.1
    (show t ≤ 5*Real.pi/4 by linarith [ht.2,Real.pi_gt_d2])
  have hpinD := west_diagonal_pin_order (a := A) (b := B)
    (show Real.pi-2/3 ≤ T by linarith [hT.1]) hT.2
  have hleftX :
      |frameX (orientedSquare t a b)
        (sub (orientedSquare T A B).center (orientedSquare t a b).center)| <
      Seven.SAT.threshold (orientedSquare t a b) (orientedSquare T A B) := by
    rw [pair_frameX_left,oriented_pair_threshold,hwidth,hdif,Real.cos_neg,Real.sin_neg]
    have h := primary_projection_bound hD hA
      (show |B| ≤ 1/2 by linarith) ha hW.a_le_rho0 hc hunit
    simpa only [mul_neg,sub_neg_eq_add,abs_of_nonneg hs] using h
  have hrightX :
      |frameX (orientedSquare T A B)
        (sub (orientedSquare T A B).center (orientedSquare t a b).center)| <
      Seven.SAT.threshold (orientedSquare t a b) (orientedSquare T A B) := by
    rw [pair_frameX_right,oriented_pair_threshold,hwidth,hdif,Real.cos_neg,Real.sin_neg]
    have hunit' : (Real.cos e)^2+(-Real.sin e)^2=1 := by
      simpa only [neg_sq] using hunit
    have h := primary_projection_bound hW ha
      (show |b| ≤ 1/2 by linarith) hA hD.a_le_rho0 hc hunit'
    have hid : A-a*Real.cos e-b*(-Real.sin e) =
        -(a*Real.cos e+b*(-Real.sin e)-A) := by ring
    rw [hid,abs_neg]
    simpa only [abs_neg,abs_of_nonneg hs] using h
  have hleftY :
      frameY (orientedSquare t a b)
        (sub (orientedSquare T A B).center (orientedSquare t a b).center) <
      Seven.SAT.threshold (orientedSquare t a b) (orientedSquare T A B) := by
    rw [pair_frameY_left,oriented_pair_threshold,hwidth,hdif,Real.cos_neg,Real.sin_neg]
    have h := forward_transverse_bound (show 0 ≤ A by linarith) hB hb hc0 hs
    nlinarith only [h]
  have hrightY :
      frameY (orientedSquare T A B)
        (sub (orientedSquare T A B).center (orientedSquare t a b).center) <
      Seven.SAT.threshold (orientedSquare t a b) (orientedSquare T A B) := by
    rw [pair_frameY_right,oriented_pair_threshold,hwidth,hdif,Real.cos_neg,Real.sin_neg]
    have h := forward_transverse_bound (A := a) (B := -b) (b := -B)
      (show 0 ≤ a by linarith) (by simpa only [abs_neg] using hb)
      (by simpa only [abs_neg] using hB) hc0 hs
    nlinarith only [h]
  rcases Seven.SAT.separating_axes (orientedSquare t a b) (orientedSquare T A B) hd with
    h | h | h | h
  · linarith only [h,hleftX]
  · have hf := left_secondary_forward hpW hpD hpinW h
    linarith only [hf,hleftY]
  · linarith only [h,hrightX]
  · have hf := right_secondary_forward hpW hpD hpinD h
    linarith only [hf,hrightY]

end SquaresInCircles.Six.Analytic
