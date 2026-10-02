import research.seven.lean.MarkerAlgebra
import research.seven.lean.StateBounds
import SquaresInCircles.Seven.MarkerArc

/-!
K: production is imported for its definitions and differentiation lemmas only.
No use is made of its curvature sign, arcEnvelope_bound, or marker endpoint
inequalities. The replacement internal bound is 353/648, not 5443/10000.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Human

lemma arcEnvelopeSecond_le_neg_eighth {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    Seven.arcEnvelopeSecond x ≤ -(1/8 : ℝ) := by
  have hd := marker_domains hx
  let R := Real.sqrt (markerA x)
  let S := Real.sqrt (markerH x/4)
  have hR : 0 < R := Real.sqrt_pos.mpr hd.1
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hR2 : R^2 = markerA x := Real.sq_sqrt hd.1.le
  have hS2 : S^2 = markerH x/4 := Real.sq_sqrt (by positivity)
  have hRle : R ≤ 1 := by nlinarith [hd.2.1]
  have hR3 : 0 < R^3 := pow_pos hR 3
  have hS3 : 0 < S^3 := pow_pos hS 3
  have hR3le : R^3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hR.le hRle 3
  have hpoly := reserved_curvature_squared hx
  have hsquare : (3*(x+1/8)*S^3)^2 < ((13/4)*R^3)^2 := by
    have hleft : (3*(x+1/8)*S^3)^2 =
        (9*(x+1/8)^2*(markerH x)^3)/64 := by
      calc
        _ = 9*(x+1/8)^2*(S^2)^3 := by ring
        _ = 9*(x+1/8)^2*(markerH x/4)^3 := by rw [hS2]
        _ = _ := by ring
    have hright : ((13/4)*R^3)^2 = (169/16)*(markerA x)^3 := by
      calc
        _ = (169/16)*(R^2)^3 := by ring
        _ = _ := by rw [hR2]
    rw [hleft,hright]
    linarith
  have hleft0 : 0 ≤ 3*(x+1/8)*S^3 := by
    have hx0 : 0 ≤ x+1/8 := by linarith [hx.1]
    positivity
  have hright0 : 0 < (13/4 : ℝ)*R^3 := by positivity
  have hroot : 3*(x+1/8)*S^3 < (13/4)*R^3 := by nlinarith
  have hfrac : (x+1/8)/R^3 < (13/4)/(3*S^3) := by
    apply (div_lt_div_iff₀ hR3 (mul_pos (by norm_num) hS3)).mpr
    nlinarith
  have heps : (1/8 : ℝ) ≤ (1/8)/R^3 := by
    apply (le_div_iff₀ hR3).mpr
    nlinarith
  have hsplit : (x+1/8)/R^3 = x/R^3+(1/8)/R^3 := by ring
  have hrad : targetSq-(x+1)^2 = markerH x/4 := by
    dsimp [targetSq,markerH]
    ring
  unfold Seven.arcEnvelopeSecond
  rw [hrad]
  change x/R^3-(13/4)/(3*S^3) ≤ -(1/8 : ℝ)
  rw [hsplit] at hfrac
  linarith

lemma arc_origin_value : Seven.arcEnvelope 0 = Real.pi/6+13/24 := by
  have hs : Real.sqrt (9/4 : ℝ) = 3/2 := by
    have he := Real.sq_sqrt (show (0 : ℝ) ≤ 9/4 by norm_num)
    nlinarith [Real.sqrt_nonneg (9/4 : ℝ)]
  norm_num [Seven.arcEnvelope,targetSq,hs]

lemma arc_origin_slope : Seven.arcEnvelopeDeriv 0 = (1 : ℝ)/36 := by
  have hs : Real.sqrt (9/4 : ℝ) = 3/2 := by
    have he := Real.sq_sqrt (show (0 : ℝ) ≤ 9/4 by norm_num)
    nlinarith [Real.sqrt_nonneg (9/4 : ℝ)]
  norm_num [Seven.arcEnvelopeDeriv,targetSq,hs]

lemma arc_envelope_parabola {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    Seven.arcEnvelope x ≤ Real.pi/6+353/648-(x-2/9)^2/16 := by
  have ht := Seven.curvature_tangent
    (f := fun y => -Seven.arcEnvelope y)
    (d := fun y => -Seven.arcEnvelopeDeriv y)
    (dd := fun y => -Seven.arcEnvelopeSecond y)
    (κ := (1 : ℝ)/8) (l := (0 : ℝ)) (u := (3 : ℝ)/4) (t := (0 : ℝ)) hx
    (by constructor <;> norm_num)
    (fun y hy => (Seven.arcEnvelope_hasDeriv hy).neg)
    (fun y hy => (Seven.arcEnvelopeDeriv_hasDeriv hy).neg)
    (fun y hy => by linarith [arcEnvelopeSecond_le_neg_eighth hy])
  dsimp only at ht
  rw [arc_origin_value,arc_origin_slope] at ht
  nlinarith

/-- The sufficient internal bound; intentionally not the old 5443/10000 bound. -/
theorem arc_envelope_bound {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    Seven.arcEnvelope x ≤ Real.pi/6+(353 : ℝ)/648 := by
  have ht := arc_envelope_parabola hx
  nlinarith [sq_nonneg (x-2/9)]

/-- The production marker half-width is unchanged. -/
theorem marker_vertical_endpoint {a u : ℝ} (h : Admissible a u) :
    label a u+(801 : ℝ)/1600 < Real.arccos (a-1/2) := by
  let x : ℝ := a-1/2
  have hx : 0 ≤ x ∧ x ≤ 3/4 := by
    dsimp [x]
    constructor <;> linarith [h.half_le,h.a_lt_five_fourths]
  have hrad : 0 ≤ targetSq-(x+1)^2 := by
    have hh := (marker_domains hx).2.2
    dsimp [targetSq,markerH] at *
    nlinarith
  have hs := Real.sq_sqrt hrad
  have hroot := Real.sqrt_nonneg (targetSq-(x+1)^2)
  have hu : u+1/2 ≤ Real.sqrt (targetSq-(x+1)^2) := by
    have hd := state_disk h
    dsimp [x,targetSq] at *
    nlinarith [h.u_nonneg]
  have henv : side a u+Real.arcsin x ≤ Seven.arcEnvelope x := by
    dsimp [side,Seven.arcEnvelope,x] at *
    linarith
  have hb := arc_envelope_bound hx
  have hl := h.label_le_side
  change label a u+(801 : ℝ)/1600 < Real.arccos x
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith [pi_lower]

/-- Optional drop-in replacement for the original polynomial interface A. -/
theorem arc_curvature_polynomial_pos {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 3/4) :
    0 < Seven.arcCurvaturePolynomial x := by
  change 0 < markerP x
  exact marker_polynomial_pos hx

end SquaresInCircles.Seven.Human
