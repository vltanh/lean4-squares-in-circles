import SquaresInCircles.Six.Normalization.Pins
import SquaresInCircles.Six.Normalization.DirectedAxes

/-!
# Six squares: the pair W, D

Two disjoint contained squares that avoid the core, the second turned from the
first by `d ∈ [0, 16/15]`, are separated along the secondary axis of one of
them, from the first to the second (`turned_pair_secondary`): `cos d ≥ 12/25`
keeps the projections on the primary axes below the threshold
`1/2 + angularWidth d`, by the distance bound of a centre, and the short
transverse coordinates keep the backward projections below it. The pins of W
and D, `π/3` apart, order the secondary axes of squares near the west from W to
D; so W comes before D (`west_before_diagonal`).
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-! ### Pins orient the secondary axes -/

lemma dot_normalY (S : UnitSquare) (v : Point) : dot (normalY S) v=frameY S v := by
  dsimp [dot,normalY,frameY]

lemma polar_transverse_projection (r q t a b : ℝ) :
    dot (normalY (orientedSquare t a b)) (polar r q) = r*Real.sin (q-t) := by
  dsimp [dot,normalY,orientedSquare,polar]
  rw [Real.sin_sub]
  ring

lemma west_diagonal_projection_difference (t a b : ℝ) :
    dot (normalY (orientedSquare t a b)) (polar (9/10) (5*Real.pi/4))-
      dot (normalY (orientedSquare t a b)) (polar (9/10) (11*Real.pi/12)) =
      (9/10)*Real.cos (13*Real.pi/12-t) := by
  rw [polar_transverse_projection,polar_transverse_projection]
  have hD : 5*Real.pi/4-t=(13*Real.pi/12-t)+Real.pi/6 := by ring
  have hW : 11*Real.pi/12-t=(13*Real.pi/12-t)-Real.pi/6 := by ring
  rw [hD,hW,Real.sin_add,Real.sin_sub (13*Real.pi/12-t) (Real.pi/6),Real.sin_pi_div_six]
  ring

lemma west_diagonal_pin_order {t a b : ℝ}
    (ht0 : Real.pi-2/3 ≤ t) (ht1 : t ≤ 5*Real.pi/4) :
    dot (normalY (orientedSquare t a b)) (polar (9/10) (11*Real.pi/12)) <
      dot (normalY (orientedSquare t a b)) (polar (9/10) (5*Real.pi/4)) := by
  have hcos : 0 < Real.cos (13*Real.pi/12-t) :=
    Real.cos_pos_of_mem_Ioo (by
      constructor <;> linarith [ht0,ht1,Real.pi_gt_d2])
  have hpos := mul_pos (show (0:ℝ) < 9/10 by norm_num) hcos
  rw [← west_diagonal_projection_difference t a b] at hpos
  exact sub_pos.mp hpos

/-! ### Two squares turned by less than `16/15` -/

/-- The primary projection of a centre on the axis of the other square stays
within the threshold: `(A + 1/2) cos d ≥ (11/8)(12/25)` exceeds `ρ0 - 1/2`. -/
lemma primary_projection_bound {A B a c s : ℝ}
    (hchart : ContainedChart A |B|)
    (hA : 7/8 ≤ A) (hB : |B| ≤ 1/2)
    (ha0 : 7/8 ≤ a) (ha1 : a ≤ rho0)
    (hc : 12/25 ≤ c) (hunit : c^2+s^2=1) :
    |A*c+B*s-a| < 1/2+(c+|s|)/2 := by
  have hc0 : 0 ≤ c := by linarith
  have hp := projection_abs_le_rho0 hchart.center_sq_le hunit
  have hpu := (abs_le.mp hp).2
  have hBs : -(|B| *|s|) ≤ B*s := by
    have h := neg_le_abs (B*s)
    rw [abs_mul] at h
    linarith
  have hBu := mul_le_mul_of_nonneg_right hB (abs_nonneg s)
  have hAc := mul_le_mul_of_nonneg_right
    (show (11:ℝ)/8 ≤ A+1/2 by linarith) hc0
  apply abs_lt.mpr
  constructor
  · nlinarith only [hBs,hBu,hAc,hc,ha1,rho0_bounds.2]
  · nlinarith only [hpu,ha0,rho0_bounds.2,hc0,abs_nonneg s]

lemma forward_transverse_bound {A B b c s : ℝ}
    (hA : 0 ≤ A) (hB : |B| ≤ 1/2) (hb : |b| < 1/2)
    (hc : 0 ≤ c) (hs : 0 ≤ s) :
    -A*s+B*c-b < 1/2+(c+s)/2 := by
  have hAv := mul_nonneg hA hs
  have hBc := mul_le_mul_of_nonneg_right ((le_abs_self B).trans hB) hc
  have hbm := (neg_le_abs b).trans_lt hb
  nlinarith only [hAv,hBc,hbm,hc,hs]

lemma west_difference_trig {d:ℝ} (hd:0≤d ∧ d≤16/15) :
    12/25≤Real.cos d ∧ 0≤Real.sin d ∧ Real.cos d^2+Real.sin d^2=1 := by
  obtain ⟨hs,-,hc,-⟩ := trig_bracket le_rfl (by linarith [Real.pi_gt_d2]) hd
  norm_num at hs hc
  exact ⟨by linarith,hs,Real.cos_sq_add_sin_sq d⟩

private lemma forward_of_abs {H x:ℝ} (h:H≤|x|) (hn:-x<H) : H≤x := by
  by_cases hx:0≤x
  · simpa only [abs_of_nonneg hx] using h
  · rw [abs_of_neg (lt_of_not_ge hx)] at h
    linarith

/-- Two disjoint contained squares that avoid the core, the second turned from
the first by `d ∈ [0, 16/15]`, are separated along the positive secondary axis
of one of them: the primary axes and the backward secondary axes fall short of
the threshold. -/
theorem turned_pair_secondary {t T a b A B:ℝ}
    (hW:ContainedChart a |b|) (hD:ContainedChart A |B|)
    (hWcore:AvoidsCore a |b|) (hDcore:AvoidsCore A |B|)
    (hd0:0≤T-t) (hd1:T-t≤16/15)
    (hd:∀ p,¬(openSquare (orientedSquare t a b) p ∧ openSquare (orientedSquare T A B) p)) :
    (1/2+angularWidth (T-t)≤frameY (orientedSquare t a b)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)) ∨
    (1/2+angularWidth (T-t)≤frameY (orientedSquare T A B)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)) := by
  have htr := west_difference_trig ⟨hd0,hd1⟩
  have hcos : 0≤Real.cos (T-t) := by linarith [htr.1]
  have hw := hW.bounds hWcore
  have hd' := hD.bounds hDcore
  have hprimaryW0 := primary_projection_bound hD hd'.1.le
    hd'.2.le hw.1.le hW.a_le_rho0
    (c:=Real.cos (T-t)) (s:=-Real.sin (T-t)) (by linarith [htr.1])
    (by simpa only [neg_sq] using htr.2.2)
  have hprimaryW : |A*Real.cos (T-t)-B*Real.sin (T-t)-a|<
      1/2+(Real.cos (T-t)+Real.sin (T-t))/2 := by
    rw [abs_neg,abs_of_nonneg htr.2.1,mul_neg,← sub_eq_add_neg] at hprimaryW0
    exact hprimaryW0
  have hprimaryD := primary_projection_bound hW hw.1.le hw.2.le
    hd'.1.le hD.a_le_rho0 (c:=Real.cos (T-t)) (s:=Real.sin (T-t))
    (by linarith [htr.1]) htr.2.2
  rw [abs_of_nonneg htr.2.1] at hprimaryD
  have hreverseW := forward_transverse_bound
    (A:=A) (B:=-B) (b:=-b) (c:=Real.cos (T-t)) (s:=Real.sin (T-t))
    (by linarith [hD.half_le]) (by simpa only [abs_neg] using hd'.2.le)
    (by simpa only [abs_neg] using hw.2) hcos htr.2.1
  have hreverseD := forward_transverse_bound
    (A:=a) (B:=b) (b:=B) (c:=Real.cos (T-t)) (s:=Real.sin (T-t))
    (by linarith [hW.half_le]) hw.2.le hd'.2 hcos htr.2.1
  have hs := oriented_separating_axes hd
  have hwidth : angularWidth (T-t)=(Real.cos (T-t)+Real.sin (T-t))/2 := by
    simp only [angularWidth,abs_of_nonneg hcos,abs_of_nonneg htr.2.1]
  rw [hwidth] at hs
  rcases hs with h | h | h | h
  · linarith
  · left
    rw [pair_frameY_left,hwidth]
    exact forward_of_abs h (by nlinarith only [hreverseW])
  · have he : |A-a*Real.cos (T-t)-b*Real.sin (T-t)|=
        |a*Real.cos (T-t)+b*Real.sin (T-t)-A| := by
      rw [show A-a*Real.cos (T-t)-b*Real.sin (T-t)=
        -(a*Real.cos (T-t)+b*Real.sin (T-t)-A) by ring,abs_neg]
    rw [he] at h
    linarith
  · right
    rw [pair_frameY_right,hwidth]
    exact forward_of_abs h (by nlinarith only [hreverseD])

/-- Two disjoint squares in the disk and outside the core, at phases `π + t` and
`π + u` with `-2/3 ≤ t ≤ u ≤ 2/5`, are separated along the positive secondary
axis of one of them. -/
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
  have hdiff : (Real.pi+u)-(Real.pi+t)=u-t := by ring
  have h := turned_pair_secondary hW hD hWcore hDcore (by linarith) (by linarith) hd
  rw [hdiff] at h
  simpa only [dot_normalY] using h

/-- Two disjoint squares near the west, holding the pins of W and D and with
phases in their windows, have the phase of W below that of D: otherwise, turned
by at most `41/40` from D, the square of W would be separated from it along a
secondary axis from D to W, against the order of the pins. -/
theorem west_before_diagonal {t a b T A B : ℝ}
    (hW : ContainedChart a |b|) (hD : ContainedChart A |B|)
    (hWcore : AvoidsCore a |b|) (hDcore : AvoidsCore A |B|)
    (ht : Real.pi-2/3 ≤ t ∧ t ≤ Real.pi+5/8)
    (hT : Real.pi-2/5 ≤ T ∧ T ≤ 5*Real.pi/4)
    (hpW : openSquare (orientedSquare t a b) (polar (9/10) (11*Real.pi/12)))
    (hpD : openSquare (orientedSquare T A B) (polar (9/10) (5*Real.pi/4)))
    (hd : ∀ p, ¬ (openSquare (orientedSquare t a b) p ∧
      openSquare (orientedSquare T A B) p)) : t < T := by
  by_contra! hrev
  have hpinW := west_diagonal_pin_order (a := a) (b := b) ht.1
    (show t ≤ 5*Real.pi/4 by linarith [ht.2,Real.pi_gt_d2])
  have hpinD := west_diagonal_pin_order (a := A) (b := B)
    (show Real.pi-2/3 ≤ T by linarith [hT.1]) hT.2
  have hthr := oriented_pair_threshold T A B t a b
  rcases turned_pair_secondary hD hW hDcore hWcore (by linarith) (by linarith [ht.2,hT.1])
    (fun p hp => hd p ⟨hp.2,hp.1⟩) with h | h
  · have hp := axis_points_to_pin _ _ hpD hpW 2 (by rw [hthr]; exact h)
    change 0 < dot (normalY _) _ at hp
    rw [dot_sub_right] at hp
    linarith
  · have hp := axis_points_to_pin _ _ hpD hpW 6 (by rw [hthr]; exact h)
    change 0 < dot (normalY _) _ at hp
    rw [dot_sub_right] at hp
    linarith

end SquaresInCircles.Six
