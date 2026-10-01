import SquaresInCircles.Six.Analytic.PairCoordinates
import SquaresInCircles.Six.Analytic.PairProjectionBounds

/-!
# Only two forward secondary axes can separate W and a west-cardinal D

On 0 <= u-t <= 16/15 the degree-six cosine bound is greater than 12/25.
The common primary projection inequality rules out both primary axes, with
both signs retained. Short transverse coordinates rule out the two reversed
secondary directions. These are the four geometric SAT axes, not an inventory
of numerically certified stresses.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization

lemma west_difference_trig {d:ℝ} (hd:0≤d ∧ d≤16/15) :
    12/25≤Real.cos d ∧ 0≤Real.sin d ∧ Real.cos d^2+Real.sin d^2=1 := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hd.1
    (show (16:ℝ)/15≤Real.pi by linarith [Real.pi_gt_d2]) hd.2
  have hl := Seven.cos_lower_six (x:=(16:ℝ)/15) (by norm_num)
  norm_num at hl
  refine ⟨by linarith,?_,?_⟩
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hd.1
      (by linarith [hd.2,Real.pi_gt_d2])
  · nlinarith [Real.sin_sq_add_cos_sq d]

private lemma forward_of_abs {H x:ℝ} (h:H≤|x|) (hn:-x<H) : H≤x := by
  by_cases hx:0≤x
  · simpa only [abs_of_nonneg hx] using h
  · rw [abs_of_neg (lt_of_not_ge hx)] at h
    linarith

/-- Under the actual normalization bounds, disjointness leaves only the
positive W-secondary or positive D-secondary normal. -/
theorem west_secondary_axes {t u a b A B:ℝ}
    (hW:ContainedChart a |b|) (hD:ContainedChart A |B|)
    (hWcore:AvoidsCore a |b|) (hDcore:AvoidsCore A |B|)
    (ht:-2/3≤t) (hu:u≤2/5) (htu:t≤u)
    (hd:∀ p,¬(openSquare (orientedSquare (Real.pi+t) a b) p ∧
      openSquare (orientedSquare (Real.pi+u) A B) p)) :
    (1/2+angularWidth (u-t)≤dot (normalY (orientedSquare (Real.pi+t) a b))
      (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center)) ∨
    (1/2+angularWidth (u-t)≤dot (normalY (orientedSquare (Real.pi+u) A B))
      (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center)) := by
  have hδ : 0≤u-t ∧ u-t≤16/15 := ⟨by linarith,by linarith⟩
  have htr := west_difference_trig hδ
  have hcos : 0≤Real.cos (u-t) := by linarith [htr.1]
  have hw := hW.bounds hWcore
  have hd' := hD.bounds hDcore
  have hprimaryW0 := primary_projection_bound hD hd'.1.le
    (hD.u_lt_half hDcore).le hw.1.le hW.a_le_rho0
    (c:=Real.cos (u-t)) (s:=-Real.sin (u-t)) (by linarith [htr.1])
    (by simpa only [neg_sq] using htr.2.2)
  have hprimaryW : |A*Real.cos (u-t)-B*Real.sin (u-t)-a|<
      1/2+(Real.cos (u-t)+Real.sin (u-t))/2 := by
    rw [abs_neg,abs_of_nonneg htr.2.1,mul_neg,← sub_eq_add_neg] at hprimaryW0
    exact hprimaryW0
  have hprimaryD := primary_projection_bound hW hw.1.le (hW.u_lt_half hWcore).le
    hd'.1.le hD.a_le_rho0 (c:=Real.cos (u-t)) (s:=Real.sin (u-t))
    (by linarith [htr.1]) htr.2.2
  rw [abs_of_nonneg htr.2.1] at hprimaryD
  have hreverseW := forward_transverse_bound
    (A:=A) (B:=-B) (b:=-b) (c:=Real.cos (u-t)) (s:=Real.sin (u-t))
    (by linarith [hD.half_le]) (by simpa only [abs_neg] using hd'.2.2.le)
    (by simpa only [abs_neg] using hw.2.2.le) hcos htr.2.1
  have hreverseD := forward_transverse_bound
    (A:=a) (B:=b) (b:=B) (c:=Real.cos (u-t)) (s:=Real.sin (u-t))
    (by linarith [hW.half_le]) hw.2.2.le hd'.2.2.le hcos htr.2.1
  have hs := Seven.SAT.separating_axes (orientedSquare (Real.pi+t) a b)
    (orientedSquare (Real.pi+u) A B) hd
  rw [oriented_pair_threshold,pair_frameX_left,pair_frameY_left,
    pair_frameX_right,pair_frameY_right] at hs
  have hdiff : (Real.pi+u)-(Real.pi+t)=u-t := by ring
  rw [hdiff] at hs
  have hwidth : angularWidth (u-t)=(Real.cos (u-t)+Real.sin (u-t))/2 := by
    simp only [angularWidth,abs_of_nonneg hcos,abs_of_nonneg htr.2.1]
  rw [hwidth] at hs
  rcases hs with h | h | h | h
  · linarith
  · left
    change 1/2+angularWidth (u-t)≤frameY (orientedSquare (Real.pi+t) a b)
      (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center)
    rw [pair_frameY_left,hdiff,hwidth]
    exact forward_of_abs h (by nlinarith only [hreverseW])
  · have he : |A-a*Real.cos (u-t)-b*Real.sin (u-t)|=
        |a*Real.cos (u-t)+b*Real.sin (u-t)-A| := by
      rw [show A-a*Real.cos (u-t)-b*Real.sin (u-t)=
        -(a*Real.cos (u-t)+b*Real.sin (u-t)-A) by ring,abs_neg]
    rw [he] at h
    linarith
  · right
    change 1/2+angularWidth (u-t)≤frameY (orientedSquare (Real.pi+u) A B)
      (sub (orientedSquare (Real.pi+u) A B).center (orientedSquare (Real.pi+t) a b).center)
    rw [pair_frameY_right,hdiff,hwidth]
    exact forward_of_abs h (by nlinarith only [hreverseD])

end SquaresInCircles.Six.Analytic
