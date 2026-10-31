module

public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Common.Charts
public import Mathlib.Tactic

/-!
# Rectangle support for forbidden directions

Radial projection turns a supporting point of a rectangle into a whole interval of
forbidden directions for a transverse segment. The constants are its distance `L`,
half-length `c` and squared endpoint radius `radiusSq = L²+c²`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CentralForbidden

def L : ℝ := 11/12
def c : ℝ := 7/20
def radiusSq : ℝ := 1733/1800

def C8 (x : ℝ) := 1-x^2/2+x^4/24-x^6/720+x^8/40320
def S9 (x : ℝ) := x-x^3/6+x^5/120-x^7/5040+x^9/362880
def C10 (x : ℝ) := C8 x-x^10/3628800
lemma cos_le_C8 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ C8 x := by
  have h := nonneg_of_deriv_nonneg (fun t => C8 t-Real.cos t)
    (by unfold C8; fun_prop) (by norm_num [C8]) (fun t ht => by
      simp (disch := fun_prop) only [C8, deriv_fun_sub, deriv_fun_add, deriv_const',
        deriv_div_const, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'',
        mul_one, zero_sub, Real.deriv_cos', sub_neg_eq_add]
      linarith only [sin_lower_seven ht, ht]) hx
  linarith only [h]
lemma sin_le_S9 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ S9 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S9 t-Real.sin t)
    (by unfold S9; fun_prop) (by norm_num [S9]) (fun t ht => by
      simp (disch := fun_prop) only [S9, deriv_fun_sub, deriv_fun_add, deriv_id'', deriv_div_const,
        deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one, mul_one, Real.deriv_sin, sub_nonneg]
      have hh := cos_le_C8 ht
      dsimp [C8] at hh
      linarith only [hh]) hx
  linarith only [h]
lemma C10_le_cos {x : ℝ} (hx : 0 ≤ x) : C10 x ≤ Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C10 t)
    (by unfold C10 C8; fun_prop) (by norm_num [C10,C8]) (fun t ht => by
      simp (disch := fun_prop) only [C10, C8, deriv_fun_sub, Real.deriv_cos', deriv_fun_add,
        deriv_const', deriv_div_const, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
        deriv_id'', mul_one, zero_sub, sub_nonneg, tsub_le_iff_right, le_neg_add_iff_add_le]
      have hh := sin_le_S9 ht
      dsimp [S9] at hh
      linarith only [hh]) hx
  linarith only [h]
def Rectangle (A d : ℝ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ A ∧ 0 ≤ p.2 ∧ p.2 ≤ d

/-- Radial projection joins the axial direction to the directions supported by one point: if
the point `(x, y)` of the rectangle lies within `√radiusSq` of the origin and its projection on
the direction `γ` is at least `L`, the segment at distance `L` meets the rectangle in every
direction of `[0, γ]`. So one point gives a whole interval of forbidden directions, and two such supports give the ends of a forbidden interval. -/
lemma rectangle_segment_interval {A d x y γ : ℝ}
    (hA : L ≤ A) (hp : Rectangle A d (x,y))
    (hrad : x^2+y^2 ≤ radiusSq) (hγ : 0 ≤ γ ∧ γ ≤ 2)
    (hsupport : L ≤ x*Real.cos γ+y*Real.sin γ) :
    ∀ β, 0 ≤ β ∧ β ≤ γ →
      ∃ v, |v| ≤ c ∧ Rectangle A d (pointInDirection (0,0) (β : Direction) L v) := by
  let r := Real.sqrt (x^2+y^2)
  have hr₂ : r^2=x^2+y^2 := Real.sq_sqrt (by positivity)
  have hr₀ : 0 ≤ r := Real.sqrt_nonneg _
  have hunitγ := Real.sin_sq_add_cos_sq γ
  have hcauchy := cauchy_sq (x,y) (Real.cos γ,Real.sin γ)
  dsimp [dot,normSq] at hcauchy
  have hrL : L ≤ r := by
    dsimp [L] at *
    nlinarith only [hsupport, hr₂, hcauchy, hunitγ, hr₀]
  have hr : 0 < r := by dsimp [L] at hrL; linarith only [hrL]
  have hxr : -1 ≤ x/r ∧ x/r ≤ 1 := by
    constructor
    · apply (le_div_iff₀ hr).2
      linarith only [hp.1, hr]
    · apply (div_le_iff₀ hr).2
      nlinarith only [hp.1, sq_nonneg y, hr₂, hr]
  let θ := Real.arccos (x/r)
  have hθ₀ : 0 ≤ θ := Real.arccos_nonneg _
  have hθ₁ : θ ≤ Real.pi/2 := Real.arccos_le_pi_div_two.mpr (div_nonneg hp.1 hr.le)
  have hcosθ : r*Real.cos θ=x := by
    rw [Real.cos_arccos hxr.1 hxr.2]
    field_simp
  have hsinθ : r*Real.sin θ=y := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ (by linarith only [Real.pi_pos, hθ₀, hθ₁])
    have hunit := Real.sin_sq_add_cos_sq θ
    have hsq : (r*Real.sin θ)^2 = y^2 := by
      have h2 := congrArg (fun z : ℝ => z^2) hcosθ
      linear_combination r^2*hunit - h2 + hr₂
    exact (pow_left_inj₀ (mul_nonneg hr₀ hs) hp.2.2.1 two_ne_zero).mp hsq
  intro β hβ
  by_cases hβθ : β ≤ θ
  · refine ⟨0,by norm_num [c],?_⟩
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith only [hβ.1, Real.pi_pos, hθ₀, hθ₁]) hθ₁ hβθ
    have hc := cos_sin_nonneg (x := β) ⟨hβ.1,hβθ.trans hθ₁⟩
    have hsin' := mul_le_mul_of_nonneg_left hsin (show 0 ≤ L by norm_num [L])
    have hr' := mul_le_mul_of_nonneg_right hrL
      (Real.sin_nonneg_of_nonneg_of_le_pi hθ₀ (by linarith only [Real.pi_pos, hθ₀, hθ₁]))
    have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one β) (show 0 ≤ L by norm_num [L])
    simp only [Rectangle,pointInDirection,Real.Angle.cos_coe,Real.Angle.sin_coe,
      mul_zero,sub_zero,zero_add,add_zero]
    exact ⟨mul_nonneg hc.1 (by norm_num [L]),by linarith only [hA, hcos],
      mul_nonneg hc.2 (by norm_num [L]),by linarith only [hp.2.2.2, hsinθ, hsin', hr']⟩
  · have hproj : L ≤ x*Real.cos β+y*Real.sin β := by
      have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
        (show 0 ≤ β-θ by linarith only [hβθ])
        (show γ-θ ≤ Real.pi by linarith only [hγ.2, hθ₀, Real.pi_gt_three])
        (show β-θ ≤ γ-θ by linarith only [hβ.2])
      have hm := mul_le_mul_of_nonneg_left hmono hr.le
      have hid (t : ℝ) : r*Real.cos (t-θ)=x*Real.cos t+y*Real.sin t := by
        rw [Real.cos_sub]
        linear_combination Real.cos t*hcosθ+Real.sin t*hsinθ
      rw [hid γ,hid β] at hm
      exact hsupport.trans hm
    obtain ⟨D,hDdef⟩ : ∃ D, D = x*Real.cos β+y*Real.sin β := ⟨_,rfl⟩
    obtain ⟨t,htdef⟩ : ∃ t, t = L/D := ⟨_,rfl⟩
    obtain ⟨qx,hqx⟩ : ∃ qx, qx = t*x := ⟨_,rfl⟩
    obtain ⟨qy,hqy⟩ : ∃ qy, qy = t*y := ⟨_,rfl⟩
    obtain ⟨v,hvdef⟩ : ∃ v, v = -Real.sin β*qx+Real.cos β*qy := ⟨_,rfl⟩
    rw [← hDdef] at hproj
    have hD : 0 < D := by dsimp [L] at hproj; linarith only [hproj]
    have ht : 0 < t ∧ t ≤ 1 := by
      rw [htdef]
      exact ⟨div_pos (by norm_num [L]) hD,(div_le_one hD).2 hproj⟩
    have hdot : qx*Real.cos β+qy*Real.sin β=L := by
      have he : qx*Real.cos β+qy*Real.sin β = t*D := by rw [hqx,hqy,hDdef]; ring
      rw [he,htdef]
      exact div_mul_cancel₀ L (ne_of_gt hD)
    have hpoint : pointInDirection (0,0) (β : Direction) L v=(qx,qy) := by
      have hu := Real.sin_sq_add_cos_sq β
      apply Prod.ext <;>
        simp only [pointInDirection,Real.Angle.cos_coe,Real.Angle.sin_coe,zero_add,hvdef]
      · linear_combination qx*hu - Real.cos β*hdot
      · linear_combination qy*hu - Real.sin β*hdot
    have hnorm : qx^2+qy^2 ≤ radiusSq := by
      have htu : t^2 ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have hh := mul_le_mul_of_nonneg_right htu (show 0 ≤ x^2+y^2 by positivity)
      rw [hqx,hqy]
      linarith only [hrad, hh]
    have hv₂ : v^2 ≤ c^2 := by
      have hn := pointInDirection_norm (0,0) (β : Direction) L v
      rw [hpoint] at hn
      simp only [normSq,sub,sub_zero] at hn
      simp only [L,c,radiusSq] at hn hnorm ⊢
      linarith only [hnorm, hn]
    refine ⟨v,?_,?_⟩
    · exact abs_le_of_sq_le_sq hv₂ (by norm_num [c])
    · rw [hpoint]
      have hx := mul_le_mul_of_nonneg_right ht.2 hp.1
      have hy := mul_le_mul_of_nonneg_right ht.2 hp.2.2.1
      exact ⟨by rw [hqx]; exact mul_nonneg ht.1.le hp.1,by rw [hqx]; linarith only [hp.2.1, hx],
        by rw [hqy]; exact mul_nonneg ht.1.le hp.2.2.1,by rw [hqy]; linarith only [hp.2.2.2, hy]⟩


end SquaresInCircles.Eight.CentralForbidden
