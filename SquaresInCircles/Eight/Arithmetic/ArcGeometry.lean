module

public import SquaresInCircles.Eight.Arithmetic.AffineTableData

/-!
# From tangent arcs to support domains

These lemmas supply the analytic part of row preparation: a tangent interval
on either circular branch maps to a closed interval in b, with the positive
root branch retained. They are independent of a particular finite table.
-/

@[expose] public section
open Set

namespace SquaresInCircles.Eight.Arithmetic

def outerEndpointA (Q u : ℝ) : ℝ :=
  (-(u+1)+Real.sqrt ((u+1)^2+4*(1+u^2)*(Q-1/2)))/(2*(1+u^2))

def coreEndpointA (u : ℝ) : ℝ :=
  (u+1+Real.sqrt ((u+1)^2-(1+u^2)*(71/36)))/(2*(1+u^2))

theorem outerEndpoint_facts {Q u : ℝ} (hQ : 1/2 < Q) (hu : 0 ≤ u ∧ u ≤ 1) :
    0 < outerEndpointA Q u ∧ 0 ≤ u*outerEndpointA Q u ∧
    u*outerEndpointA Q u ≤ outerEndpointA Q u ∧
    (outerEndpointA Q u+1/2)^2+(u*outerEndpointA Q u+1/2)^2=Q := by
  let d := (u+1)^2+4*(1+u^2)*(Q-1/2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hs : (Real.sqrt d)^2=d := Real.sq_sqrt hd.le
  have hroot : u+1 < Real.sqrt d := by
    have hp : 0 < 4*(1+u^2)*(Q-1/2) := by positivity
    dsimp [d] at hs
    nlinarith [Real.sqrt_nonneg d]
  have hden : 0 < 2*(1+u^2) := by positivity
  have ha : 0 < outerEndpointA Q u := div_pos (by linarith) hden
  refine ⟨ha,mul_nonneg hu.1 ha.le,?_,?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) ha.le]
  · have hid : outerEndpointA Q u*(2*(1+u^2)) = -(u+1)+Real.sqrt d := by
      dsimp [outerEndpointA,d]
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    have hquad : (1+u^2)*(outerEndpointA Q u)^2+(u+1)*outerEndpointA Q u+1/2-Q=0 := by
      have hsq := congrArg (fun x : ℝ => x^2) hid
      dsimp [d] at hs
      have hid2 : 4*(1+u^2)*((1+u^2)*(outerEndpointA Q u)^2+
          (u+1)*outerEndpointA Q u+1/2-Q)=0 := by nlinarith
      exact (mul_eq_zero.mp hid2).resolve_left (by positivity)
    nlinarith only [hquad]

theorem coreEndpoint_facts {u : ℝ} (hu : 6/7 ≤ u ∧ u ≤ 1) :
    1/2 < coreEndpointA u ∧ 1/2 ≤ u*coreEndpointA u ∧
    u*coreEndpointA u ≤ coreEndpointA u ∧
    (coreEndpointA u-1/2)^2+(u*coreEndpointA u-1/2)^2=(1/12 : ℝ)^2 := by
  let d := (u+1)^2-(1+u^2)*(71/36)
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hfactor : 0 ≤ (7*u-6)*(6-5*u) := mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hs := Real.sq_sqrt hd.le
  have hr := Real.sqrt_pos.mpr hd
  have hden : 0 < 2*(1+u^2) := by positivity
  have ha : 1/2 < coreEndpointA u := by
    apply (lt_div_iff₀ hden).mpr
    dsimp [d] at hr
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu.2)]
  have hb : 1/2 ≤ u*coreEndpointA u := by
    have hsq : (1-u)^2 ≤ (u*Real.sqrt d)^2 := by
      have hp := mul_nonneg (show 0 ≤ 1+u^2 by positivity) hfactor
      have he : (u*Real.sqrt d)^2-(1-u)^2=(1+u^2)*(7*u-6)*(6-5*u)/36 := by
        rw [mul_pow,hs]
        dsimp [d]
        ring
      linarith
    have hroot : 1-u ≤ u*Real.sqrt d := by nlinarith [mul_nonneg hu0 hr.le]
    unfold coreEndpointA
    rw [mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  refine ⟨ha,hb,?_,?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ coreEndpointA u by linarith)]
  · have hid : coreEndpointA u*(2*(1+u^2)) = u+1+Real.sqrt d := by
      dsimp [coreEndpointA,d]
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    have hquad : (1+u^2)*(coreEndpointA u)^2-(u+1)*coreEndpointA u+71/144=0 := by
      have hsq := congrArg (fun x : ℝ => x^2) hid
      dsimp [d] at hs
      have hid2 : 4*(1+u^2)*((1+u^2)*(coreEndpointA u)^2-
          (u+1)*coreEndpointA u+71/144)=0 := by nlinarith
      exact (mul_eq_zero.mp hid2).resolve_left (by positivity)
    nlinarith only [hquad]

theorem circle_branch {v ρ a b : ℝ} (ha : v < a)
    (hc : (a-v)^2+(b-v)^2=ρ^2) : a = circleX v ρ b := by
  have he : ρ^2-(b-v)^2=(a-v)^2 := by nlinarith only [hc]
  rw [circleX,he,Real.sqrt_sq (sub_pos.mpr ha).le]
  ring

theorem circle_tangent_lower {v ρ a b a₀ b₀ t : ℝ}
    (ha : 0 < a) (ha₀ : 0 < a₀) (haV : v < a) (ha₀V : v < a₀)
    (hbV : v ≤ b) (hb₀V : v ≤ b₀) (ht : 0 ≤ t)
    (hpoint : b₀=t*a₀) (hl : t ≤ b/a)
    (hc : (a-v)^2+(b-v)^2=ρ^2) (hc₀ : (a₀-v)^2+(b₀-v)^2=ρ^2) :
    b₀ ≤ b := by
  have hcross : t*a ≤ b := (le_div_iff₀ ha).mp hl
  by_contra hh
  have hbb : b < b₀ := lt_of_not_ge hh
  have haa : a₀ ≤ a := by
    have hp := mul_nonneg (sub_pos.mpr hbb).le (show 0 ≤ b₀+b-2*v by linarith)
    nlinarith [hc,hc₀]
  have hm := mul_le_mul_of_nonneg_left haa ht
  rw [← hpoint] at hm
  linarith

theorem circle_tangent_upper {v ρ a b a₁ b₁ t : ℝ}
    (ha : 0 < a) (ha₁ : 0 < a₁) (haV : v < a) (ha₁V : v < a₁)
    (hbV : v ≤ b) (hb₁V : v ≤ b₁) (ht : 0 ≤ t)
    (hpoint : b₁=t*a₁) (hu : b/a ≤ t)
    (hc : (a-v)^2+(b-v)^2=ρ^2) (hc₁ : (a₁-v)^2+(b₁-v)^2=ρ^2) :
    b ≤ b₁ := by
  have hcross : b ≤ t*a := (div_le_iff₀ ha).mp hu
  by_contra hh
  have hbb : b₁ < b := lt_of_not_ge hh
  have haa : a ≤ a₁ := by
    have hp := mul_nonneg (sub_pos.mpr hbb).le (show 0 ≤ b+b₁-2*v by linarith)
    nlinarith [hc,hc₁]
  have hm := mul_le_mul_of_nonneg_left haa ht
  rw [← hpoint] at hm
  linarith

theorem circle_arc_radicand_positive {v ρ l u aU : ℝ}
    (hl : v ≤ l) (ha : v < aU)
    (hc : (aU-v)^2+(u-v)^2=ρ^2) :
    ∀ b ∈ Icc l u, 0 < ρ^2-(b-v)^2 := by
  intro b hb
  have hp := mul_nonneg (sub_nonneg.mpr hb.2) (show 0 ≤ u+b-2*v by linarith [hb.1])
  have hsq := sq_pos_of_pos (sub_pos.mpr ha)
  nlinarith

/-- Generic circle endpoint support directly from tangent-domain geometry. -/
theorem tangent_arc_endpoints_lower {v ρ a b a₀ b₀ a₁ b₁ t₀ t₁ X Y m : ℝ}
    (ha : 0 < a) (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (haV : v < a) (ha₀V : v < a₀) (ha₁V : v < a₁)
    (hbV : v ≤ b) (hb₀V : v ≤ b₀) (hb₁V : v ≤ b₁)
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁)
    (he₀ : b₀=t₀*a₀) (he₁ : b₁=t₁*a₁)
    (ht : t₀ ≤ b/a ∧ b/a ≤ t₁)
    (hc : (a-v)^2+(b-v)^2=ρ^2)
    (hc₀ : (a₀-v)^2+(b₀-v)^2=ρ^2)
    (hc₁ : (a₁-v)^2+(b₁-v)^2=ρ^2)
    (hX : 0 ≤ X) (h₀ : m ≤ X*a₀+Y*b₀) (h₁ : m ≤ X*a₁+Y*b₁) :
    m ≤ X*a+Y*b := by
  have hlo := circle_tangent_lower ha ha₀ haV ha₀V hbV hb₀V ht₀ he₀ ht.1 hc hc₀
  have hhi := circle_tangent_upper ha ha₁ haV ha₁V hbV hb₁V ht₁ he₁ ht.2 hc hc₁
  have hpos := circle_arc_radicand_positive hb₀V ha₁V hc₁
  have he := circle_branch haV hc
  have he₀' := circle_branch ha₀V hc₀
  have he₁' := circle_branch ha₁V hc₁
  rw [he] at ⊢
  exact circle_endpoints_lower hX hpos ⟨hlo,hhi⟩
    (by simpa [← he₀'] using h₀) (by simpa [← he₁'] using h₁)

end SquaresInCircles.Eight.Arithmetic
