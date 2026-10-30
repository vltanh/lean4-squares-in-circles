module

public import SquaresInCircles.Common.Trigonometry
public import SquaresInCircles.Common.Charts
public import Mathlib.Tactic

/-!
# Eight squares: the forbidden directions of the central square

When the origin lies within `1/12` of a side of the central square, the square contains a
rectangle that no transverse segment of an exterior square may meet. In the frame of the central
square, with `d` in `[0, 1/2]`, the rectangle is `[0, A] × [-d, 1 - d]` with `A = 11/12` or
`A = 19/20`, and the segments are those of length `7/10` at distance `11/12` from the origin,
perpendicular to their direction (`CentralCore.lean`). For every `d` the directions in which such
a segment meets the rectangle contain a closed interval about the axis, of length more than
`347/200` for `A = 11/12` (`bandA_forbidden`) and more than `899/500` for `A = 19/20`
(`bandB_forbidden`).

Radial projection turns one point of the rectangle into a whole interval of these directions
(`rectangle_segment_interval`): if the point lies within `√(1733/1800)` of the origin and its
projection on the direction `γ` is at least `11/12`, the segment meets the rectangle in every
direction between the axis and `γ`. A `Row` gives, for an interval of values of `d`, one such
rational point and angle on each side of the axis, with a squared radius bound and a Taylor lower
bound for the projection. The rows form a closed dyadic cover of `0 ≤ d ≤ 1/2` (`bandA_cover`,
`bandB_cover`), and each is checked by rational arithmetic.
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
def S11 (x : ℝ) := S9 x-x^11/39916800
def C12 (x : ℝ) := C10 x+x^12/479001600
def S13 (x : ℝ) := S11 x+x^13/6227020800
def C14 (x : ℝ) := C12 x-x^14/87178291200
def S15 (x : ℝ) := S13 x-x^15/1307674368000

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
lemma S11_le_sin {x : ℝ} (hx : 0 ≤ x) : S11 x ≤ Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-S11 t)
    (by unfold S11 S9; fun_prop) (by norm_num [S11,S9]) (fun t ht => by
      simp (disch := fun_prop) only [S11, S9, deriv_fun_sub, Real.deriv_sin, deriv_fun_add,
        deriv_id'', deriv_div_const, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one, mul_one,
        sub_nonneg, tsub_le_iff_right]
      have hh := C10_le_cos ht
      dsimp [C10,C8] at hh
      linarith only [hh]) hx
  linarith only [h]
lemma cos_le_C12 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ C12 x := by
  have h := nonneg_of_deriv_nonneg (fun t => C12 t-Real.cos t)
    (by unfold C12 C10 C8; fun_prop) (by norm_num [C12,C10,C8]) (fun t ht => by
      simp (disch := fun_prop) only [C12, C10, C8, deriv_fun_sub, deriv_fun_add, deriv_const',
        deriv_div_const, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'',
        mul_one, zero_sub, Real.deriv_cos', sub_neg_eq_add]
      have hh := S11_le_sin ht
      dsimp [S11,S9] at hh
      linarith only [hh]) hx
  linarith only [h]
lemma sin_le_S13 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ S13 x := by
  have h := nonneg_of_deriv_nonneg (fun t => S13 t-Real.sin t)
    (by unfold S13 S11 S9; fun_prop) (by norm_num [S13,S11,S9]) (fun t ht => by
      simp (disch := fun_prop) only [S13, S11, S9, deriv_fun_sub, deriv_fun_add, deriv_id'',
        deriv_div_const, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one, mul_one,
        Real.deriv_sin, sub_nonneg]
      have hh := cos_le_C12 ht
      dsimp [C12,C10,C8] at hh
      linarith only [hh]) hx
  linarith only [h]
lemma C14_le_cos {x : ℝ} (hx : 0 ≤ x) : C14 x ≤ Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-C14 t)
    (by unfold C14 C12 C10 C8; fun_prop) (by norm_num [C14,C12,C10,C8]) (fun t ht => by
      simp (disch := fun_prop) only [C14, C12, C10, C8, deriv_fun_sub, Real.deriv_cos',
        deriv_fun_add, deriv_const', deriv_div_const, deriv_fun_pow, Nat.cast_ofNat,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_sub, sub_nonneg, tsub_le_iff_right,
        le_neg_add_iff_add_le]
      have hh := sin_le_S13 ht
      dsimp [S13,S11,S9] at hh
      linarith only [hh]) hx
  linarith only [h]
lemma S15_le_sin {x : ℝ} (hx : 0 ≤ x) : S15 x ≤ Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-S15 t)
    (by unfold S15 S13 S11 S9; fun_prop) (by norm_num [S15,S13,S11,S9]) (fun t ht => by
      simp (disch := fun_prop) only [S15, S13, S11, S9, deriv_fun_sub, Real.deriv_sin,
        deriv_fun_add, deriv_id'', deriv_div_const, deriv_fun_pow, Nat.cast_ofNat,
        Nat.add_one_sub_one, mul_one, sub_nonneg, tsub_le_iff_right]
      have hh := C14_le_cos ht
      dsimp [C14,C12,C10,C8] at hh
      linarith only [hh]) hx
  linarith only [h]

def Rectangle (A d : ℝ) (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ A ∧ 0 ≤ p.2 ∧ p.2 ≤ d

/-- Radial projection joins the axial direction to the directions supported by one point: if
the point `(x, y)` of the rectangle lies within `√radiusSq` of the origin and its projection on
the direction `γ` is at least `L`, the segment at distance `L` meets the rectangle in every
direction of `[0, γ]`. So one point gives a whole interval of forbidden directions, and the rows
only supply its two ends. -/
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

structure Row where
  lower : ℝ
  upper : ℝ
  x₁ : ℝ
  y₁ : ℝ
  angle₁ : ℝ
  x₂ : ℝ
  y₂ : ℝ
  angle₂ : ℝ

def Row.Valid (A W : ℝ) (row : Row) : Prop :=
  0 ≤ row.lower ∧ row.lower ≤ row.upper ∧ row.upper ≤ 1/2 ∧
  Rectangle A row.lower (row.x₁,row.y₁) ∧
  Rectangle A (1-row.upper) (row.x₂,row.y₂) ∧
  row.x₁^2+row.y₁^2 ≤ radiusSq ∧ row.x₂^2+row.y₂^2 ≤ radiusSq ∧
  (0 ≤ row.angle₁ ∧ row.angle₁ ≤ 2) ∧ (0 ≤ row.angle₂ ∧ row.angle₂ ≤ 2) ∧
  L ≤ row.x₁*C14 row.angle₁+row.y₁*S15 row.angle₁ ∧
  L ≤ row.x₂*C14 row.angle₂+row.y₂*S15 row.angle₂ ∧ W < row.angle₁+row.angle₂

lemma Row.Valid.forbidden {A W d : ℝ} {row : Row} (h : row.Valid A W)
    (hA : L ≤ A) (hd : row.lower ≤ d ∧ d ≤ row.upper) :
    W < row.angle₁+row.angle₂ ∧
    ∀ β, -row.angle₁ ≤ β ∧ β ≤ row.angle₂ →
      ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ A ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  rcases h with ⟨hl,hu,hhalf,hp₁,hp₂,hn₁,hn₂,hθ₁,hθ₂,hs₁,hs₂,hwidth⟩
  have hsupp₁ : L ≤ row.x₁*Real.cos row.angle₁+row.y₁*Real.sin row.angle₁ := by
    have hc := mul_le_mul_of_nonneg_left (C14_le_cos hθ₁.1) hp₁.1
    have hs := mul_le_mul_of_nonneg_left (S15_le_sin hθ₁.1) hp₁.2.2.1
    linarith only [hs₁, hc, hs]
  have hsupp₂ : L ≤ row.x₂*Real.cos row.angle₂+row.y₂*Real.sin row.angle₂ := by
    have hc := mul_le_mul_of_nonneg_left (C14_le_cos hθ₂.1) hp₂.1
    have hs := mul_le_mul_of_nonneg_left (S15_le_sin hθ₂.1) hp₂.2.2.1
    linarith only [hs₂, hc, hs]
  refine ⟨hwidth,fun β hβ => ?_⟩
  by_cases hβ₀ : 0 ≤ β
  · obtain ⟨v,hv,hp⟩ := rectangle_segment_interval hA hp₂ hn₂ hθ₂ hsupp₂ β ⟨hβ₀,hβ.2⟩
    exact ⟨v,hv,hp.1,hp.2.1,by linarith only [hp.2.2.1, hd, hl],by linarith only [hp.2.2.2, hd]⟩
  · obtain ⟨v,hv,
    hp⟩ := rectangle_segment_interval hA hp₁ hn₁ hθ₁ hsupp₁ (-β) ⟨by linarith only [hβ₀],
    by linarith only [hβ.1]⟩
    refine ⟨-v,by simpa using hv,?_,?_,?_,?_⟩
    all_goals
      dsimp [Rectangle,pointInDirection] at hp ⊢
      simp only [Real.Angle.cos_neg,Real.Angle.sin_neg,Real.Angle.cos_coe,
        Real.Angle.sin_coe] at hp
      linarith only [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hd, hhalf]

/-! ### The rows of the two covers -/

set_option maxRecDepth 200000

/-- Checks a row by rational arithmetic: unfolds the row and the Taylor polynomials, evaluates
each condition and joins the results. -/
local macro "row_check " row:ident : tactic => `(tactic|
  (simp only [$row:ident,Row.Valid,Rectangle,L,radiusSq,C14,C12,C10,C8,S15,S13,S11,S9]
   norm_num1
   simp only [and_self]))

def bandA_000 : Row := ⟨0, (1/16), (11/12), 0, 0, 0, (15/16), (1781997/1000000)⟩
lemma bandA_000_valid : bandA_000.Valid (11/12) (347/200) := by
  row_check bandA_000
def bandA_001 : Row := ⟨(1/16), (5/64), (11/12), (1/16), (68071/500000), 0, (59/64), (335427/200000)⟩
lemma bandA_001_valid : bandA_001.Valid (11/12) (347/200) := by
  row_check bandA_001
def bandA_002 : Row := ⟨(5/64), (21/256), (11/12), (5/64), (170033/1000000), 0, (235/256), (812027/500000)⟩
lemma bandA_002_valid : bandA_002.Valid (11/12) (347/200) := by
  row_check bandA_002
def bandA_003 : Row := ⟨(21/256), (11/128), (11/12), (21/256), (178491/1000000), (356745741/1000000000), (117/128), (195427/125000)⟩
lemma bandA_003_valid : bandA_003.Valid (11/12) (347/200) := by
  row_check bandA_003
def bandA_004 : Row := ⟨(11/128), (23/256), (11/12), (11/128), (186943/1000000), (11456157/31250000), (233/256), (194077/125000)⟩
lemma bandA_004_valid : bandA_004.Valid (11/12) (347/200) := by
  row_check bandA_004
def bandA_005 : Row := ⟨(23/256), (3/32), (11/12), (23/256), (48847/250000), (376149857/1000000000), (29/32), (771049/500000)⟩
lemma bandA_005_valid : bandA_005.Valid (11/12) (347/200) := by
  row_check bandA_005
def bandA_006 : Row := ⟨(3/32), (25/256), (11/12), (3/32), (101913/500000), (752786/1953125), (231/256), (1531839/1000000)⟩
lemma bandA_006_valid : bandA_006.Valid (11/12) (347/200) := by
  row_check bandA_006
def bandA_007 : Row := ⟨(25/256), (51/512), (11/12), (25/256), (212257/1000000), (194983653/500000000), (461/512), (763401/500000)⟩
lemma bandA_007_valid : bandA_007.Valid (11/12) (347/200) := by
  row_check bandA_007
def bandA_008 : Row := ⟨(51/512), (13/128), (11/12), (51/512), (21647/100000), (2465289/6250000), (115/128), (760911/500000)⟩
lemma bandA_008_valid : bandA_008.Valid (11/12) (347/200) := by
  row_check bandA_008
def bandA_009 : Row := ⟨(13/128), (53/512), (11/12), (13/128), (5517/25000), (398865319/1000000000), (459/512), (758449/500000)⟩
lemma bandA_009_valid : bandA_009.Valid (11/12) (347/200) := by
  row_check bandA_009
def bandA_010 : Row := ⟨(53/512), (27/256), (11/12), (53/512), (224889/1000000), (25201657/62500000), (229/256), (378007/250000)⟩
lemma bandA_010_valid : bandA_010.Valid (11/12) (347/200) := by
  row_check bandA_010
def bandA_011 : Row := ⟨(27/256), (55/512), (11/12), (27/256), (28637/125000), (407531677/1000000000), (457/512), (150721/100000)⟩
lemma bandA_011_valid : bandA_011.Valid (11/12) (347/200) := by
  row_check bandA_011
def bandA_012 : Row := ⟨(55/512), (7/64), (11/12), (55/512), (2333/10000), (102945643/250000000), (57/64), (751221/500000)⟩
lemma bandA_012_valid : bandA_012.Valid (11/12) (347/200) := by
  row_check bandA_012
def bandA_013 : Row := ⟨(7/64), (57/512), (11/12), (7/64), (237503/1000000), (20799043/50000000), (455/512), (1497723/1000000)⟩
lemma bandA_013_valid : bandA_013.Valid (11/12) (347/200) := by
  row_check bandA_013
def bandA_014 : Row := ⟨(57/512), (115/1024), (11/12), (57/512), (241703/1000000), (418060773/1000000000), (909/1024), (1495381/1000000)⟩
lemma bandA_014_valid : bandA_014.Valid (11/12) (347/200) := by
  row_check bandA_014
def bandA_015 : Row := ⟨(115/1024), (29/256), (11/12), (115/1024), (243803/1000000), (210064059/500000000), (227/256), (1493051/1000000)⟩
lemma bandA_015_valid : bandA_015.Valid (11/12) (347/200) := by
  row_check bandA_015
def bandA_016 : Row := ⟨(29/256), (117/1024), (11/12), (29/256), (122951/500000), (211091541/500000000), (907/1024), (372683/250000)⟩
lemma bandA_016_valid : bandA_016.Valid (11/12) (347/200) := by
  row_check bandA_016
def bandA_017 : Row := ⟨(117/1024), (59/512), (11/12), (117/1024), (31/125), (424225843/1000000000), (453/512), (59537/40000)⟩
lemma bandA_017_valid : bandA_017.Valid (11/12) (347/200) := by
  row_check bandA_017
def bandA_018 : Row := ⟨(59/512), (119/1024), (11/12), (59/512), (125049/500000), (213128289/500000000), (905/1024), (92883/62500)⟩
lemma bandA_018_valid : bandA_018.Valid (11/12) (347/200) := by
  row_check bandA_018
def bandA_019 : Row := ⟨(119/1024), (15/128), (11/12), (119/1024), (50439/200000), (428275457/1000000000), (113/128), (1483843/1000000)⟩
lemma bandA_019_valid : bandA_019.Valid (11/12) (347/200) := by
  row_check bandA_019
def bandA_020 : Row := ⟨(15/128), (121/1024), (11/12), (15/128), (63573/250000), (430282647/1000000000), (903/1024), (46299/31250)⟩
lemma bandA_020_valid : bandA_020.Valid (11/12) (347/200) := by
  row_check bandA_020
def bandA_021 : Row := ⟨(121/1024), (61/512), (11/12), (121/1024), (64097/250000), (54034789/125000000), (451/512), (184913/125000)⟩
lemma bandA_021_valid : bandA_021.Valid (11/12) (347/200) := by
  row_check bandA_021
def bandA_022 : Row := ⟨(61/512), (123/1024), (11/12), (61/512), (64621/250000), (434262609/1000000000), (901/1024), (29541/20000)⟩
lemma bandA_022_valid : bandA_022.Valid (11/12) (347/200) := by
  row_check bandA_022
def bandA_023 : Row := ⟨(123/1024), (31/256), (11/12), (123/1024), (260579/1000000), (218117847/500000000), (225/256), (737403/500000)⟩
lemma bandA_023_valid : bandA_023.Valid (11/12) (347/200) := by
  row_check bandA_023
def bandA_024 : Row := ⟨(31/256), (125/1024), (11/12), (31/256), (262673/1000000), (438197719/1000000000), (899/1024), (368143/250000)⟩
lemma bandA_024_valid : bandA_024.Valid (11/12) (347/200) := by
  row_check bandA_024
def bandA_025 : Row := ⟨(125/1024), (63/512), (11/12), (125/1024), (264767/1000000), (13754651/31250000), (449/512), (1470349/1000000)⟩
lemma bandA_025_valid : bandA_025.Valid (11/12) (347/200) := by
  row_check bandA_025
def bandA_026 : Row := ⟨(63/512), (253/2048), (11/12), (63/512), (13343/50000), (441120341/1000000000), (1795/2048), (1469241/1000000)⟩
lemma bandA_026_valid : bandA_026.Valid (11/12) (347/200) := by
  row_check bandA_026
def bandA_027 : Row := ⟨(253/2048), (127/1024), (11/12), (253/2048), (267907/1000000), (55261147/125000000), (897/1024), (293627/200000)⟩
lemma bandA_027_valid : bandA_027.Valid (11/12) (347/200) := by
  row_check bandA_027
def bandA_028 : Row := ⟨(127/1024), (255/2048), (11/12), (127/1024), (268953/1000000), (221527677/500000000), (1793/2048), (183379/125000)⟩
lemma bandA_028_valid : bandA_028.Valid (11/12) (347/200) := by
  row_check bandA_028
def bandA_029 : Row := ⟨(255/2048), (1/8), (11/12), (255/2048), (269999/1000000), (444018893/1000000000), (7/8), (1465931/1000000)⟩
lemma bandA_029_valid : bandA_029.Valid (11/12) (347/200) := by
  row_check bandA_029
def bandA_030 : Row := ⟨(1/8), (257/2048), (11/12), (1/8), (54209/200000), (44497981/100000000), (1791/2048), (22888/15625)⟩
lemma bandA_030_valid : bandA_030.Valid (11/12) (347/200) := by
  row_check bandA_030
def bandA_031 : Row := ⟨(257/2048), (129/1024), (11/12), (257/2048), (272091/1000000), (445938121/1000000000), (895/1024), (182967/125000)⟩
lemma bandA_031_valid : bandA_031.Valid (11/12) (347/200) := by
  row_check bandA_031
def bandA_032 : Row := ⟨(129/1024), (259/2048), (11/12), (129/1024), (17071/62500), (111723461/250000000), (1789/2048), (731321/500000)⟩
lemma bandA_032_valid : bandA_032.Valid (11/12) (347/200) := by
  row_check bandA_032
def bandA_033 : Row := ⟨(259/2048), (65/512), (11/12), (259/2048), (137091/500000), (111961749/250000000), (447/512), (1461551/1000000)⟩
lemma bandA_033_valid : bandA_033.Valid (11/12) (347/200) := by
  row_check bandA_033
def bandA_034 : Row := ⟨(65/512), (261/2048), (11/12), (65/512), (275227/1000000), (448797591/1000000000), (1787/2048), (730231/500000)⟩
lemma bandA_034_valid : bandA_034.Valid (11/12) (347/200) := by
  row_check bandA_034
def bandA_035 : Row := ⟨(261/2048), (131/1024), (11/12), (261/2048), (276273/1000000), (449745647/1000000000), (893/1024), (467/320)⟩
lemma bandA_035_valid : bandA_035.Valid (11/12) (347/200) := by
  row_check bandA_035
def bandA_036 : Row := ⟨(131/1024), (263/2048), (11/12), (131/1024), (138659/500000), (22534559/50000000), (1785/2048), (145829/100000)⟩
lemma bandA_036_valid : bandA_036.Valid (11/12) (347/200) := by
  row_check bandA_036
def bandA_037 : Row := ⟨(263/2048), (33/256), (11/12), (263/2048), (139181/500000), (225817103/500000000), (223/256), (182151/125000)⟩
lemma bandA_037_valid : bandA_037.Valid (11/12) (347/200) := by
  row_check bandA_037
def bandA_038 : Row := ⟨(33/256), (265/2048), (11/12), (33/256), (279407/1000000), (22628737/50000000), (1783/2048), (22752/15625)⟩
lemma bandA_038_valid : bandA_038.Valid (11/12) (347/200) := by
  row_check bandA_038
def bandA_039 : Row := ⟨(265/2048), (133/1024), (11/12), (265/2048), (70113/250000), (453512797/1000000000), (891/1024), (29101/20000)⟩
lemma bandA_039_valid : bandA_039.Valid (11/12) (347/200) := by
  row_check bandA_039
def bandA_040 : Row := ⟨(133/1024), (267/2048), (11/12), (133/1024), (35187/125000), (227224197/500000000), (1781/2048), (58159/40000)⟩
lemma bandA_040_valid : bandA_040.Valid (11/12) (347/200) := by
  row_check bandA_040
def bandA_041 : Row := ⟨(267/2048), (67/512), (11/12), (267/2048), (282541/1000000), (91076309/200000000), (445/512), (1452901/1000000)⟩
lemma bandA_041_valid : bandA_041.Valid (11/12) (347/200) := by
  row_check bandA_041
def bandA_042 : Row := ⟨(67/512), (269/2048), (11/12), (67/512), (56717/200000), (91262453/200000000), (1779/2048), (145183/100000)⟩
lemma bandA_042_valid : bandA_042.Valid (11/12) (347/200) := by
  row_check bandA_042
def bandA_043 : Row := ⟨(269/2048), (135/1024), (11/12), (269/2048), (284629/1000000), (457240569/1000000000), (889/1024), (1450761/1000000)⟩
lemma bandA_043_valid : bandA_043.Valid (11/12) (347/200) := by
  row_check bandA_043
def bandA_044 : Row := ⟨(135/1024), (271/2048), (11/12), (135/1024), (285673/1000000), (57270809/125000000), (1777/2048), (724847/500000)⟩
lemma bandA_044_valid : bandA_044.Valid (11/12) (347/200) := by
  row_check bandA_044
def bandA_045 : Row := ⟨(271/2048), (17/128), (11/12), (271/2048), (71679/250000), (114772497/250000000), (111/128), (144863/100000)⟩
lemma bandA_045_valid : bandA_045.Valid (11/12) (347/200) := by
  row_check bandA_045
def bandA_046 : Row := ⟨(17/128), (273/2048), (11/12), (17/128), (3597/12500), (115002783/250000000), (1775/2048), (1447567/1000000)⟩
lemma bandA_046_valid : bandA_046.Valid (11/12) (347/200) := by
  row_check bandA_046
def bandA_047 : Row := ⟨(273/2048), (137/1024), (11/12), (273/2048), (288803/1000000), (230464959/500000000), (887/1024), (1446507/1000000)⟩
lemma bandA_047_valid : bandA_047.Valid (11/12) (347/200) := by
  row_check bandA_047
def bandA_048 : Row := ⟨(137/1024), (275/2048), (11/12), (137/1024), (144923/500000), (461846359/1000000000), (1773/2048), (1445449/1000000)⟩
lemma bandA_048_valid : bandA_048.Valid (11/12) (347/200) := by
  row_check bandA_048
def bandA_049 : Row := ⟨(275/2048), (69/512), (11/12), (275/2048), (290889/1000000), (462760471/1000000000), (443/512), (180549/125000)⟩
lemma bandA_049_valid : bandA_049.Valid (11/12) (347/200) := by
  row_check bandA_049
def bandA_050 : Row := ⟨(69/512), (277/2048), (11/12), (69/512), (72983/250000), (231836133/500000000), (1771/2048), (721669/500000)⟩
lemma bandA_050_valid : bandA_050.Valid (11/12) (347/200) := by
  row_check bandA_050
def bandA_051 : Row := ⟨(277/2048), (139/1024), (11/12), (277/2048), (11719/40000), (464581759/1000000000), (885/1024), (721143/500000)⟩
lemma bandA_051_valid : bandA_051.Valid (11/12) (347/200) := by
  row_check bandA_051
def bandA_052 : Row := ⟨(139/1024), (279/2048), (11/12), (139/1024), (147009/500000), (232744481/500000000), (1769/2048), (360309/250000)⟩
lemma bandA_052_valid : bandA_052.Valid (11/12) (347/200) := by
  row_check bandA_052
def bandA_053 : Row := ⟨(279/2048), (35/256), (11/12), (279/2048), (14753/50000), (46639389/100000000), (221/256), (360047/250000)⟩
lemma bandA_053_valid : bandA_053.Valid (11/12) (347/200) := by
  row_check bandA_053
def bandA_054 : Row := ⟨(35/256), (281/2048), (11/12), (35/256), (148051/500000), (93459311/200000000), (1767/2048), (719571/500000)⟩
lemma bandA_054_valid : bandA_054.Valid (11/12) (347/200) := by
  row_check bandA_054
def bandA_055 : Row := ⟨(281/2048), (141/1024), (11/12), (281/2048), (37143/125000), (468196971/1000000000), (883/1024), (719049/500000)⟩
lemma bandA_055_valid : bandA_055.Valid (11/12) (347/200) := by
  row_check bandA_055
def bandA_056 : Row := ⟨(141/1024), (283/2048), (11/12), (141/1024), (149093/500000), (469095149/1000000000), (1765/2048), (1437057/1000000)⟩
lemma bandA_056_valid : bandA_056.Valid (11/12) (347/200) := by
  row_check bandA_056
def bandA_057 : Row := ⟨(283/2048), (71/512), (11/12), (283/2048), (74807/250000), (93998221/200000000), (441/512), (1436017/1000000)⟩
lemma bandA_057_valid : bandA_057.Valid (11/12) (347/200) := by
  row_check bandA_057
def bandA_058 : Row := ⟨(71/512), (285/2048), (11/12), (71/512), (300269/1000000), (470884849/1000000000), (1763/2048), (1434979/1000000)⟩
lemma bandA_058_valid : bandA_058.Valid (11/12) (347/200) := by
  row_check bandA_058
def bandA_059 : Row := ⟨(285/2048), (143/1024), (11/12), (285/2048), (301311/1000000), (235888197/500000000), (881/1024), (1433943/1000000)⟩
lemma bandA_059_valid : bandA_059.Valid (11/12) (347/200) := by
  row_check bandA_059
def bandA_060 : Row := ⟨(143/1024), (287/2048), (11/12), (143/1024), (18897/62500), (236332877/500000000), (1761/2048), (1432909/1000000)⟩
lemma bandA_060_valid : bandA_060.Valid (11/12) (347/200) := by
  row_check bandA_060
def bandA_061 : Row := ⟨(287/2048), (9/64), (11/12), (287/2048), (303393/1000000), (23677647/50000000), (55/64), (1431877/1000000)⟩
lemma bandA_061_valid : bandA_061.Valid (11/12) (347/200) := by
  row_check bandA_061
def bandA_062 : Row := ⟨(9/64), (289/2048), (11/12), (9/64), (152217/500000), (118609491/250000000), (1759/2048), (1430847/1000000)⟩
lemma bandA_062_valid : bandA_062.Valid (11/12) (347/200) := by
  row_check bandA_062
def bandA_063 : Row := ⟨(289/2048), (145/1024), (11/12), (289/2048), (12219/40000), (475320839/1000000000), (879/1024), (714909/500000)⟩
lemma bandA_063_valid : bandA_063.Valid (11/12) (347/200) := by
  row_check bandA_063
def bandA_064 : Row := ⟨(145/1024), (291/2048), (11/12), (145/1024), (76629/250000), (59525197/125000000), (1757/2048), (178599/125000)⟩
lemma bandA_064_valid : bandA_064.Valid (11/12) (347/200) := by
  row_check bandA_064
def bandA_065 : Row := ⟨(291/2048), (73/512), (11/12), (291/2048), (76889/250000), (119270047/250000000), (439/512), (178471/125000)⟩
lemma bandA_065_valid : bandA_065.Valid (11/12) (347/200) := by
  row_check bandA_065
def bandA_066 : Row := ⟨(73/512), (293/2048), (11/12), (73/512), (77149/250000), (95591337/200000000), (1755/2048), (285349/200000)⟩
lemma bandA_066_valid : bandA_066.Valid (11/12) (347/200) := by
  row_check bandA_066
def bandA_067 : Row := ⟨(293/2048), (147/1024), (11/12), (293/2048), (77409/250000), (478831081/1000000000), (877/1024), (356431/250000)⟩
lemma bandA_067_valid : bandA_067.Valid (11/12) (347/200) := by
  row_check bandA_067
def bandA_068 : Row := ⟨(147/1024), (295/2048), (11/12), (147/1024), (77669/250000), (95940677/200000000), (1753/2048), (712353/500000)⟩
lemma bandA_068_valid : bandA_068.Valid (11/12) (347/200) := by
  row_check bandA_068
def bandA_069 : Row := ⟨(295/2048), (37/256), (11/12), (295/2048), (77929/250000), (48057361/100000000), (219/256), (1423689/1000000)⟩
lemma bandA_069_valid : bandA_069.Valid (11/12) (347/200) := by
  row_check bandA_069
def bandA_070 : Row := ⟨(37/256), (297/2048), (11/12), (37/256), (78189/250000), (481441767/1000000000), (1751/2048), (1422673/1000000)⟩
lemma bandA_070_valid : bandA_070.Valid (11/12) (347/200) := by
  row_check bandA_070
def bandA_071 : Row := ⟨(297/2048), (149/1024), (11/12), (297/2048), (62759/200000), (482307867/1000000000), (875/1024), (71083/50000)⟩
lemma bandA_071_valid : bandA_071.Valid (11/12) (347/200) := by
  row_check bandA_071
def bandA_072 : Row := ⟨(149/1024), (299/2048), (11/12), (149/1024), (157417/500000), (483171921/1000000000), (1749/2048), (1420649/1000000)⟩
lemma bandA_072_valid : bandA_072.Valid (11/12) (347/200) := by
  row_check bandA_072
def bandA_073 : Row := ⟨(299/2048), (75/512), (11/12), (299/2048), (315873/1000000), (24201697/50000000), (437/512), (1419639/1000000)⟩
lemma bandA_073_valid : bandA_073.Valid (11/12) (347/200) := by
  row_check bandA_073
def bandA_074 : Row := ⟨(75/512), (301/2048), (11/12), (75/512), (19807/62500), (96978787/200000000), (1747/2048), (1418631/1000000)⟩
lemma bandA_074_valid : bandA_074.Valid (11/12) (347/200) := by
  row_check bandA_074
def bandA_075 : Row := ⟨(301/2048), (151/1024), (11/12), (301/2048), (317951/1000000), (121437979/250000000), (873/1024), (11341/8000)⟩
lemma bandA_075_valid : bandA_075.Valid (11/12) (347/200) := by
  row_check bandA_075
def bandA_076 : Row := ⟨(151/1024), (303/2048), (11/12), (151/1024), (318989/1000000), (97321579/200000000), (1745/2048), (1416621/1000000)⟩
lemma bandA_076_valid : bandA_076.Valid (11/12) (347/200) := by
  row_check bandA_076
def bandA_077 : Row := ⟨(303/2048), (19/128), (11/12), (303/2048), (80007/250000), (487461881/1000000000), (109/128), (707809/500000)⟩
lemma bandA_077_valid : bandA_077.Valid (11/12) (347/200) := by
  row_check bandA_077
def bandA_078 : Row := ⟨(19/128), (305/2048), (11/12), (19/128), (160533/500000), (244156943/500000000), (1743/2048), (1414617/1000000)⟩
lemma bandA_078_valid : bandA_078.Valid (11/12) (347/200) := by
  row_check bandA_078
def bandA_079 : Row := ⟨(305/2048), (153/1024), (11/12), (305/2048), (40263/125000), (6114549/12500000), (871/1024), (706809/500000)⟩
lemma bandA_079_valid : bandA_079.Valid (11/12) (347/200) := by
  row_check bandA_079
def bandA_080 : Row := ⟨(153/1024), (307/2048), (11/12), (153/1024), (161571/500000), (61251499/125000000), (1741/2048), (1412621/1000000)⟩
lemma bandA_080_valid : bandA_080.Valid (11/12) (347/200) := by
  row_check bandA_080
def bandA_081 : Row := ⟨(307/2048), (77/512), (11/12), (307/2048), (16209/50000), (490858113/1000000000), (435/512), (11293/8000)⟩
lemma bandA_081_valid : bandA_081.Valid (11/12) (347/200) := by
  row_check bandA_081
def bandA_082 : Row := ⟨(77/512), (309/2048), (11/12), (77/512), (325217/1000000), (245851147/500000000), (1739/2048), (1410631/1000000)⟩
lemma bandA_082_valid : bandA_082.Valid (11/12) (347/200) := by
  row_check bandA_082
def bandA_083 : Row := ⟨(309/2048), (155/1024), (11/12), (309/2048), (163127/500000), (492544543/1000000000), (869/1024), (1409639/1000000)⟩
lemma bandA_083_valid : bandA_083.Valid (11/12) (347/200) := by
  row_check bandA_083
def bandA_084 : Row := ⟨(155/1024), (311/2048), (11/12), (155/1024), (81823/250000), (493384871/1000000000), (1737/2048), (1408649/1000000)⟩
lemma bandA_084_valid : bandA_084.Valid (11/12) (347/200) := by
  row_check bandA_084
def bandA_085 : Row := ⟨(311/2048), (39/256), (11/12), (311/2048), (328329/1000000), (494223289/1000000000), (217/256), (70383/50000)⟩
lemma bandA_085_valid : bandA_085.Valid (11/12) (347/200) := by
  row_check bandA_085
def bandA_086 : Row := ⟨(39/256), (157/1024), (11/12), (39/256), (65873/200000), (123973607/250000000), (867/1024), (1405687/1000000)⟩
lemma bandA_086_valid : bandA_086.Valid (11/12) (347/200) := by
  row_check bandA_086
def bandA_087 : Row := ⟨(157/1024), (79/512), (11/12), (157/1024), (165719/500000), (248779019/500000000), (433/512), (1403721/1000000)⟩
lemma bandA_087_valid : bandA_087.Valid (11/12) (347/200) := by
  row_check bandA_087
def bandA_088 : Row := ⟨(79/512), (159/1024), (11/12), (79/512), (333511/1000000), (249607097/500000000), (865/1024), (700881/500000)⟩
lemma bandA_088_valid : bandA_088.Valid (11/12) (347/200) := by
  row_check bandA_088
def bandA_089 : Row := ⟨(159/1024), (5/32), (11/12), (159/1024), (167791/500000), (50086297/100000000), (27/32), (1399809/1000000)⟩
lemma bandA_089_valid : bandA_089.Valid (11/12) (347/200) := by
  row_check bandA_089
def bandA_090 : Row := ⟨(5/32), (161/1024), (11/12), (5/32), (337653/1000000), (251252219/500000000), (863/1024), (698931/500000)⟩
lemma bandA_090_valid : bandA_090.Valid (11/12) (347/200) := by
  row_check bandA_090
def bandA_091 : Row := ⟨(161/1024), (81/512), (11/12), (161/1024), (339723/1000000), (50413867/100000000), (431/512), (697961/500000)⟩
lemma bandA_091_valid : bandA_091.Valid (11/12) (347/200) := by
  row_check bandA_091
def bandA_092 : Row := ⟨(81/512), (163/1024), (11/12), (81/512), (341793/1000000), (63220717/125000000), (861/1024), (348497/250000)⟩
lemma bandA_092_valid : bandA_092.Valid (11/12) (347/200) := by
  row_check bandA_092
def bandA_093 : Row := ⟨(163/1024), (41/256), (11/12), (163/1024), (171931/500000), (63423213/125000000), (215/256), (69603/50000)⟩
lemma bandA_093_valid : bandA_093.Valid (11/12) (347/200) := by
  row_check bandA_093
def bandA_094 : Row := ⟨(41/256), (165/1024), (11/12), (41/256), (34593/100000), (508998643/1000000000), (859/1024), (1390139/1000000)⟩
lemma bandA_094_valid : bandA_094.Valid (11/12) (347/200) := by
  row_check bandA_094
def bandA_095 : Row := ⟨(165/1024), (83/512), (11/12), (165/1024), (347997/1000000), (25530231/50000000), (429/512), (1388223/1000000)⟩
lemma bandA_095_valid : bandA_095.Valid (11/12) (347/200) := by
  row_check bandA_095
def bandA_096 : Row := ⟨(83/512), (167/1024), (11/12), (83/512), (350063/1000000), (512203699/1000000000), (857/1024), (693157/500000)⟩
lemma bandA_096_valid : bandA_096.Valid (11/12) (347/200) := by
  row_check bandA_096
def bandA_097 : Row := ⟨(167/1024), (21/128), (11/12), (167/1024), (352129/1000000), (102759189/200000000), (107/128), (138441/100000)⟩
lemma bandA_097_valid : bandA_097.Valid (11/12) (347/200) := by
  row_check bandA_097
def bandA_098 : Row := ⟨(21/128), (169/1024), (11/12), (21/128), (177097/500000), (257690711/500000000), (855/1024), (86407/62500)⟩
lemma bandA_098_valid : bandA_098.Valid (11/12) (347/200) := by
  row_check bandA_098
def bandA_099 : Row := ⟨(169/1024), (85/512), (11/12), (169/1024), (178129/500000), (516960191/1000000000), (427/512), (69031/50000)⟩
lemma bandA_099_valid : bandA_099.Valid (11/12) (347/200) := by
  row_check bandA_099
def bandA_100 : Row := ⟨(85/512), (43/256), (11/12), (85/512), (358321/1000000), (520097853/1000000000), (213/256), (688427/500000)⟩
lemma bandA_100_valid : bandA_100.Valid (11/12) (347/200) := by
  row_check bandA_100
def bandA_101 : Row := ⟨(43/256), (87/512), (11/12), (43/256), (181223/500000), (523209407/1000000000), (425/512), (137311/100000)⟩
lemma bandA_101_valid : bandA_101.Valid (11/12) (347/200) := by
  row_check bandA_101
def bandA_102 : Row := ⟨(87/512), (11/64), (11/12), (87/512), (366567/1000000), (263147659/500000000), (53/64), (342347/250000)⟩
lemma bandA_102_valid : bandA_102.Valid (11/12) (347/200) := by
  row_check bandA_102
def bandA_103 : Row := ⟨(11/64), (89/512), (11/12), (11/64), (74137/200000), (264678017/500000000), (423/512), (1365687/1000000)⟩
lemma bandA_103_valid : bandA_103.Valid (11/12) (347/200) := by
  row_check bandA_103
def bandA_104 : Row := ⟨(89/512), (45/256), (11/12), (89/512), (937/2500), (133097997/250000000), (211/256), (170251/125000)⟩
lemma bandA_104_valid : bandA_104.Valid (11/12) (347/200) := by
  row_check bandA_104
def bandA_105 : Row := ⟨(45/256), (91/512), (11/12), (45/256), (11841/31250), (133850901/250000000), (421/512), (27167/20000)⟩
lemma bandA_105_valid : bandA_105.Valid (11/12) (347/200) := by
  row_check bandA_105
def bandA_106 : Row := ⟨(91/512), (23/128), (11/12), (91/512), (383021/1000000), (538391289/1000000000), (105/128), (169339/125000)⟩
lemma bandA_106_valid : bandA_106.Valid (11/12) (347/200) := by
  row_check bandA_106
def bandA_107 : Row := ⟨(23/128), (93/512), (11/12), (23/128), (193563/500000), (270677719/500000000), (419/512), (675547/500000)⟩
lemma bandA_107_valid : bandA_107.Valid (11/12) (347/200) := by
  row_check bandA_107
def bandA_108 : Row := ⟨(93/512), (47/256), (11/12), (93/512), (97807/250000), (272148219/500000000), (209/256), (168437/125000)⟩
lemma bandA_108_valid : bandA_108.Valid (11/12) (347/200) := by
  row_check bandA_108
def bandA_109 : Row := ⟨(47/256), (3/16), (11/12), (47/256), (395327/1000000), (137527617/250000000), (13/16), (670179/500000)⟩
lemma bandA_109_valid : bandA_109.Valid (11/12) (347/200) := by
  row_check bandA_109
def bandA_110 : Row := ⟨(3/16), (49/256), (11/12), (3/16), (201757/500000), (555836239/1000000000), (207/256), (666647/500000)⟩
lemma bandA_110_valid : bandA_110.Valid (11/12) (347/200) := by
  row_check bandA_110
def bandA_111 : Row := ⟨(49/256), (25/128), (11/12), (49/256), (51461/125000), (561476451/1000000000), (103/128), (663151/500000)⟩
lemma bandA_111_valid : bandA_111.Valid (11/12) (347/200) := by
  row_check bandA_111
def bandA_112 : Row := ⟨(25/128), (51/256), (11/12), (25/128), (419847/1000000), (70879207/125000000), (205/256), (1319379/1000000)⟩
lemma bandA_112_valid : bandA_112.Valid (11/12) (347/200) := by
  row_check bandA_112
def bandA_113 : Row := ⟨(51/256), (13/64), (11/12), (51/256), (427993/1000000), (8945473/15625000), (51/64), (1312523/1000000)⟩
lemma bandA_113_valid : bandA_113.Valid (11/12) (347/200) := by
  row_check bandA_113
def bandA_114 : Row := ⟨(13/64), (27/128), (11/12), (13/64), (109031/250000), (116646157/200000000), (101/128), (324751/250000)⟩
lemma bandA_114_valid : bandA_114.Valid (11/12) (347/200) := by
  row_check bandA_114
def bandA_115 : Row := ⟨(27/128), (7/32), (11/12), (27/128), (226171/500000), (593654963/1000000000), (25/32), (1285727/1000000)⟩
lemma bandA_115_valid : bandA_115.Valid (11/12) (347/200) := by
  row_check bandA_115
def bandA_116 : Row := ⟨(7/32), (29/128), (11/12), (7/32), (937/2000), (301899077/500000000), (99/128), (1272679/1000000)⟩
lemma bandA_116_valid : bandA_116.Valid (11/12) (347/200) := by
  row_check bandA_116
def bandA_117 : Row := ⟨(29/128), (15/64), (11/12), (29/128), (121149/250000), (153418573/250000000), (49/64), (251969/200000)⟩
lemma bandA_117_valid : bandA_117.Valid (11/12) (347/200) := by
  row_check bandA_117
def bandA_118 : Row := ⟨(15/64), (1/4), (11/12), (15/64), (125157/250000), (79084387/125000000), (3/4), (1234773/1000000)⟩
lemma bandA_118_valid : bandA_118.Valid (11/12) (347/200) := by
  row_check bandA_118
def bandA_119 : Row := ⟨(1/4), (17/64), (11/12), (1/4), (266247/500000), (650746599/1000000000), (47/64), (48417/40000)⟩
lemma bandA_119_valid : bandA_119.Valid (11/12) (347/200) := by
  row_check bandA_119
def bandA_120 : Row := ⟨(17/64), (9/32), (11/12), (17/64), (112817/200000), (83495529/125000000), (23/32), (1186729/1000000)⟩
lemma bandA_120_valid : bandA_120.Valid (11/12) (347/200) := by
  row_check bandA_120
def bandA_121 : Row := ⟨(9/32), (5/16), (11/12), (9/32), (59539/100000), (1750217/2500000), (11/16), (285263/250000)⟩
lemma bandA_121_valid : bandA_121.Valid (11/12) (347/200) := by
  row_check bandA_121
def bandA_122 : Row := ⟨(5/16), (11/32), (11/12), (5/16), (82137/125000), (583569/800000), (21/32), (1097339/1000000)⟩
lemma bandA_122_valid : bandA_122.Valid (11/12) (347/200) := by
  row_check bandA_122
def bandA_123 : Row := ⟨(11/32), (3/8), (11/12), (11/32), (717531/1000000), (756407811/1000000000), (5/8), (527641/500000)⟩
lemma bandA_123_valid : bandA_123.Valid (11/12) (347/200) := by
  row_check bandA_123
def bandA_124 : Row := ⟨(3/8), (13/32), (906726407/1000000000), (3/8), (756879/1000000), (390588887/500000000), (19/32), (1014639/1000000)⟩
lemma bandA_124_valid : bandA_124.Valid (11/12) (347/200) := by
  row_check bandA_124
def bandA_125 : Row := ⟨(13/32), (7/16), (893162199/1000000000), (13/32), (1979/2500), (401986171/500000000), (9/16), (60951/62500)⟩
lemma bandA_125_valid : bandA_125.Valid (11/12) (347/200) := by
  row_check bandA_125
def bandA_126 : Row := ⟨(7/16), (15/32), (878277591/1000000000), (7/16), (413439/500000), (10311941/12500000), (17/32), (234213/250000)⟩
lemma bandA_126_valid : bandA_126.Valid (11/12) (347/200) := by
  row_check bandA_126
def bandA_127 : Row := ⟨(15/32), (1/2), (172400837/200000000), (15/32), (215697/250000), (211065419/250000000), (1/2), (449707/500000)⟩
lemma bandA_127_valid : bandA_127.Valid (11/12) (347/200) := by
  row_check bandA_127

/-- Closes `row.lower ≤ d` and `d ≤ row.upper` from the case hypotheses. -/
local macro "row_bound" : tactic =>
  `(tactic| first | assumption | exact le_of_lt (lt_of_not_ge ‹_›) | linarith)

theorem bandA_cover {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/2) :
    ∃ row : Row, row.Valid (11/12) (347/200) ∧ row.lower ≤ d ∧ d ≤ row.upper := by
  by_cases h2 : d ≤ (1/4)
  ·
    by_cases h4 : d ≤ (1/8)
    ·
      by_cases h6 : d ≤ (1/16)
      ·
        refine ⟨bandA_000,bandA_000_valid,?_,?_⟩
        all_goals dsimp only [bandA_000]; row_bound
      ·
        by_cases h8 : d ≤ (3/32)
        ·
          by_cases h10 : d ≤ (5/64)
          ·
            refine ⟨bandA_001,bandA_001_valid,?_,?_⟩
            all_goals dsimp only [bandA_001]; row_bound
          ·
            by_cases h12 : d ≤ (11/128)
            ·
              by_cases h14 : d ≤ (21/256)
              ·
                refine ⟨bandA_002,bandA_002_valid,?_,?_⟩
                all_goals dsimp only [bandA_002]; row_bound
              ·
                refine ⟨bandA_003,bandA_003_valid,?_,?_⟩
                all_goals dsimp only [bandA_003]; row_bound
            ·
              by_cases h14 : d ≤ (23/256)
              ·
                refine ⟨bandA_004,bandA_004_valid,?_,?_⟩
                all_goals dsimp only [bandA_004]; row_bound
              ·
                refine ⟨bandA_005,bandA_005_valid,?_,?_⟩
                all_goals dsimp only [bandA_005]; row_bound
        ·
          by_cases h10 : d ≤ (7/64)
          ·
            by_cases h12 : d ≤ (13/128)
            ·
              by_cases h14 : d ≤ (25/256)
              ·
                refine ⟨bandA_006,bandA_006_valid,?_,?_⟩
                all_goals dsimp only [bandA_006]; row_bound
              ·
                by_cases h16 : d ≤ (51/512)
                ·
                  refine ⟨bandA_007,bandA_007_valid,?_,?_⟩
                  all_goals dsimp only [bandA_007]; row_bound
                ·
                  refine ⟨bandA_008,bandA_008_valid,?_,?_⟩
                  all_goals dsimp only [bandA_008]; row_bound
            ·
              by_cases h14 : d ≤ (27/256)
              ·
                by_cases h16 : d ≤ (53/512)
                ·
                  refine ⟨bandA_009,bandA_009_valid,?_,?_⟩
                  all_goals dsimp only [bandA_009]; row_bound
                ·
                  refine ⟨bandA_010,bandA_010_valid,?_,?_⟩
                  all_goals dsimp only [bandA_010]; row_bound
              ·
                by_cases h16 : d ≤ (55/512)
                ·
                  refine ⟨bandA_011,bandA_011_valid,?_,?_⟩
                  all_goals dsimp only [bandA_011]; row_bound
                ·
                  refine ⟨bandA_012,bandA_012_valid,?_,?_⟩
                  all_goals dsimp only [bandA_012]; row_bound
          ·
            by_cases h12 : d ≤ (15/128)
            ·
              by_cases h14 : d ≤ (29/256)
              ·
                by_cases h16 : d ≤ (57/512)
                ·
                  refine ⟨bandA_013,bandA_013_valid,?_,?_⟩
                  all_goals dsimp only [bandA_013]; row_bound
                ·
                  by_cases h18 : d ≤ (115/1024)
                  ·
                    refine ⟨bandA_014,bandA_014_valid,?_,?_⟩
                    all_goals dsimp only [bandA_014]; row_bound
                  ·
                    refine ⟨bandA_015,bandA_015_valid,?_,?_⟩
                    all_goals dsimp only [bandA_015]; row_bound
              ·
                by_cases h16 : d ≤ (59/512)
                ·
                  by_cases h18 : d ≤ (117/1024)
                  ·
                    refine ⟨bandA_016,bandA_016_valid,?_,?_⟩
                    all_goals dsimp only [bandA_016]; row_bound
                  ·
                    refine ⟨bandA_017,bandA_017_valid,?_,?_⟩
                    all_goals dsimp only [bandA_017]; row_bound
                ·
                  by_cases h18 : d ≤ (119/1024)
                  ·
                    refine ⟨bandA_018,bandA_018_valid,?_,?_⟩
                    all_goals dsimp only [bandA_018]; row_bound
                  ·
                    refine ⟨bandA_019,bandA_019_valid,?_,?_⟩
                    all_goals dsimp only [bandA_019]; row_bound
            ·
              by_cases h14 : d ≤ (31/256)
              ·
                by_cases h16 : d ≤ (61/512)
                ·
                  by_cases h18 : d ≤ (121/1024)
                  ·
                    refine ⟨bandA_020,bandA_020_valid,?_,?_⟩
                    all_goals dsimp only [bandA_020]; row_bound
                  ·
                    refine ⟨bandA_021,bandA_021_valid,?_,?_⟩
                    all_goals dsimp only [bandA_021]; row_bound
                ·
                  by_cases h18 : d ≤ (123/1024)
                  ·
                    refine ⟨bandA_022,bandA_022_valid,?_,?_⟩
                    all_goals dsimp only [bandA_022]; row_bound
                  ·
                    refine ⟨bandA_023,bandA_023_valid,?_,?_⟩
                    all_goals dsimp only [bandA_023]; row_bound
              ·
                by_cases h16 : d ≤ (63/512)
                ·
                  by_cases h18 : d ≤ (125/1024)
                  ·
                    refine ⟨bandA_024,bandA_024_valid,?_,?_⟩
                    all_goals dsimp only [bandA_024]; row_bound
                  ·
                    refine ⟨bandA_025,bandA_025_valid,?_,?_⟩
                    all_goals dsimp only [bandA_025]; row_bound
                ·
                  by_cases h18 : d ≤ (127/1024)
                  ·
                    by_cases h20 : d ≤ (253/2048)
                    ·
                      refine ⟨bandA_026,bandA_026_valid,?_,?_⟩
                      all_goals dsimp only [bandA_026]; row_bound
                    ·
                      refine ⟨bandA_027,bandA_027_valid,?_,?_⟩
                      all_goals dsimp only [bandA_027]; row_bound
                  ·
                    by_cases h20 : d ≤ (255/2048)
                    ·
                      refine ⟨bandA_028,bandA_028_valid,?_,?_⟩
                      all_goals dsimp only [bandA_028]; row_bound
                    ·
                      refine ⟨bandA_029,bandA_029_valid,?_,?_⟩
                      all_goals dsimp only [bandA_029]; row_bound
    ·
      by_cases h6 : d ≤ (3/16)
      ·
        by_cases h8 : d ≤ (5/32)
        ·
          by_cases h10 : d ≤ (9/64)
          ·
            by_cases h12 : d ≤ (17/128)
            ·
              by_cases h14 : d ≤ (33/256)
              ·
                by_cases h16 : d ≤ (65/512)
                ·
                  by_cases h18 : d ≤ (129/1024)
                  ·
                    by_cases h20 : d ≤ (257/2048)
                    ·
                      refine ⟨bandA_030,bandA_030_valid,?_,?_⟩
                      all_goals dsimp only [bandA_030]; row_bound
                    ·
                      refine ⟨bandA_031,bandA_031_valid,?_,?_⟩
                      all_goals dsimp only [bandA_031]; row_bound
                  ·
                    by_cases h20 : d ≤ (259/2048)
                    ·
                      refine ⟨bandA_032,bandA_032_valid,?_,?_⟩
                      all_goals dsimp only [bandA_032]; row_bound
                    ·
                      refine ⟨bandA_033,bandA_033_valid,?_,?_⟩
                      all_goals dsimp only [bandA_033]; row_bound
                ·
                  by_cases h18 : d ≤ (131/1024)
                  ·
                    by_cases h20 : d ≤ (261/2048)
                    ·
                      refine ⟨bandA_034,bandA_034_valid,?_,?_⟩
                      all_goals dsimp only [bandA_034]; row_bound
                    ·
                      refine ⟨bandA_035,bandA_035_valid,?_,?_⟩
                      all_goals dsimp only [bandA_035]; row_bound
                  ·
                    by_cases h20 : d ≤ (263/2048)
                    ·
                      refine ⟨bandA_036,bandA_036_valid,?_,?_⟩
                      all_goals dsimp only [bandA_036]; row_bound
                    ·
                      refine ⟨bandA_037,bandA_037_valid,?_,?_⟩
                      all_goals dsimp only [bandA_037]; row_bound
              ·
                by_cases h16 : d ≤ (67/512)
                ·
                  by_cases h18 : d ≤ (133/1024)
                  ·
                    by_cases h20 : d ≤ (265/2048)
                    ·
                      refine ⟨bandA_038,bandA_038_valid,?_,?_⟩
                      all_goals dsimp only [bandA_038]; row_bound
                    ·
                      refine ⟨bandA_039,bandA_039_valid,?_,?_⟩
                      all_goals dsimp only [bandA_039]; row_bound
                  ·
                    by_cases h20 : d ≤ (267/2048)
                    ·
                      refine ⟨bandA_040,bandA_040_valid,?_,?_⟩
                      all_goals dsimp only [bandA_040]; row_bound
                    ·
                      refine ⟨bandA_041,bandA_041_valid,?_,?_⟩
                      all_goals dsimp only [bandA_041]; row_bound
                ·
                  by_cases h18 : d ≤ (135/1024)
                  ·
                    by_cases h20 : d ≤ (269/2048)
                    ·
                      refine ⟨bandA_042,bandA_042_valid,?_,?_⟩
                      all_goals dsimp only [bandA_042]; row_bound
                    ·
                      refine ⟨bandA_043,bandA_043_valid,?_,?_⟩
                      all_goals dsimp only [bandA_043]; row_bound
                  ·
                    by_cases h20 : d ≤ (271/2048)
                    ·
                      refine ⟨bandA_044,bandA_044_valid,?_,?_⟩
                      all_goals dsimp only [bandA_044]; row_bound
                    ·
                      refine ⟨bandA_045,bandA_045_valid,?_,?_⟩
                      all_goals dsimp only [bandA_045]; row_bound
            ·
              by_cases h14 : d ≤ (35/256)
              ·
                by_cases h16 : d ≤ (69/512)
                ·
                  by_cases h18 : d ≤ (137/1024)
                  ·
                    by_cases h20 : d ≤ (273/2048)
                    ·
                      refine ⟨bandA_046,bandA_046_valid,?_,?_⟩
                      all_goals dsimp only [bandA_046]; row_bound
                    ·
                      refine ⟨bandA_047,bandA_047_valid,?_,?_⟩
                      all_goals dsimp only [bandA_047]; row_bound
                  ·
                    by_cases h20 : d ≤ (275/2048)
                    ·
                      refine ⟨bandA_048,bandA_048_valid,?_,?_⟩
                      all_goals dsimp only [bandA_048]; row_bound
                    ·
                      refine ⟨bandA_049,bandA_049_valid,?_,?_⟩
                      all_goals dsimp only [bandA_049]; row_bound
                ·
                  by_cases h18 : d ≤ (139/1024)
                  ·
                    by_cases h20 : d ≤ (277/2048)
                    ·
                      refine ⟨bandA_050,bandA_050_valid,?_,?_⟩
                      all_goals dsimp only [bandA_050]; row_bound
                    ·
                      refine ⟨bandA_051,bandA_051_valid,?_,?_⟩
                      all_goals dsimp only [bandA_051]; row_bound
                  ·
                    by_cases h20 : d ≤ (279/2048)
                    ·
                      refine ⟨bandA_052,bandA_052_valid,?_,?_⟩
                      all_goals dsimp only [bandA_052]; row_bound
                    ·
                      refine ⟨bandA_053,bandA_053_valid,?_,?_⟩
                      all_goals dsimp only [bandA_053]; row_bound
              ·
                by_cases h16 : d ≤ (71/512)
                ·
                  by_cases h18 : d ≤ (141/1024)
                  ·
                    by_cases h20 : d ≤ (281/2048)
                    ·
                      refine ⟨bandA_054,bandA_054_valid,?_,?_⟩
                      all_goals dsimp only [bandA_054]; row_bound
                    ·
                      refine ⟨bandA_055,bandA_055_valid,?_,?_⟩
                      all_goals dsimp only [bandA_055]; row_bound
                  ·
                    by_cases h20 : d ≤ (283/2048)
                    ·
                      refine ⟨bandA_056,bandA_056_valid,?_,?_⟩
                      all_goals dsimp only [bandA_056]; row_bound
                    ·
                      refine ⟨bandA_057,bandA_057_valid,?_,?_⟩
                      all_goals dsimp only [bandA_057]; row_bound
                ·
                  by_cases h18 : d ≤ (143/1024)
                  ·
                    by_cases h20 : d ≤ (285/2048)
                    ·
                      refine ⟨bandA_058,bandA_058_valid,?_,?_⟩
                      all_goals dsimp only [bandA_058]; row_bound
                    ·
                      refine ⟨bandA_059,bandA_059_valid,?_,?_⟩
                      all_goals dsimp only [bandA_059]; row_bound
                  ·
                    by_cases h20 : d ≤ (287/2048)
                    ·
                      refine ⟨bandA_060,bandA_060_valid,?_,?_⟩
                      all_goals dsimp only [bandA_060]; row_bound
                    ·
                      refine ⟨bandA_061,bandA_061_valid,?_,?_⟩
                      all_goals dsimp only [bandA_061]; row_bound
          ·
            by_cases h12 : d ≤ (19/128)
            ·
              by_cases h14 : d ≤ (37/256)
              ·
                by_cases h16 : d ≤ (73/512)
                ·
                  by_cases h18 : d ≤ (145/1024)
                  ·
                    by_cases h20 : d ≤ (289/2048)
                    ·
                      refine ⟨bandA_062,bandA_062_valid,?_,?_⟩
                      all_goals dsimp only [bandA_062]; row_bound
                    ·
                      refine ⟨bandA_063,bandA_063_valid,?_,?_⟩
                      all_goals dsimp only [bandA_063]; row_bound
                  ·
                    by_cases h20 : d ≤ (291/2048)
                    ·
                      refine ⟨bandA_064,bandA_064_valid,?_,?_⟩
                      all_goals dsimp only [bandA_064]; row_bound
                    ·
                      refine ⟨bandA_065,bandA_065_valid,?_,?_⟩
                      all_goals dsimp only [bandA_065]; row_bound
                ·
                  by_cases h18 : d ≤ (147/1024)
                  ·
                    by_cases h20 : d ≤ (293/2048)
                    ·
                      refine ⟨bandA_066,bandA_066_valid,?_,?_⟩
                      all_goals dsimp only [bandA_066]; row_bound
                    ·
                      refine ⟨bandA_067,bandA_067_valid,?_,?_⟩
                      all_goals dsimp only [bandA_067]; row_bound
                  ·
                    by_cases h20 : d ≤ (295/2048)
                    ·
                      refine ⟨bandA_068,bandA_068_valid,?_,?_⟩
                      all_goals dsimp only [bandA_068]; row_bound
                    ·
                      refine ⟨bandA_069,bandA_069_valid,?_,?_⟩
                      all_goals dsimp only [bandA_069]; row_bound
              ·
                by_cases h16 : d ≤ (75/512)
                ·
                  by_cases h18 : d ≤ (149/1024)
                  ·
                    by_cases h20 : d ≤ (297/2048)
                    ·
                      refine ⟨bandA_070,bandA_070_valid,?_,?_⟩
                      all_goals dsimp only [bandA_070]; row_bound
                    ·
                      refine ⟨bandA_071,bandA_071_valid,?_,?_⟩
                      all_goals dsimp only [bandA_071]; row_bound
                  ·
                    by_cases h20 : d ≤ (299/2048)
                    ·
                      refine ⟨bandA_072,bandA_072_valid,?_,?_⟩
                      all_goals dsimp only [bandA_072]; row_bound
                    ·
                      refine ⟨bandA_073,bandA_073_valid,?_,?_⟩
                      all_goals dsimp only [bandA_073]; row_bound
                ·
                  by_cases h18 : d ≤ (151/1024)
                  ·
                    by_cases h20 : d ≤ (301/2048)
                    ·
                      refine ⟨bandA_074,bandA_074_valid,?_,?_⟩
                      all_goals dsimp only [bandA_074]; row_bound
                    ·
                      refine ⟨bandA_075,bandA_075_valid,?_,?_⟩
                      all_goals dsimp only [bandA_075]; row_bound
                  ·
                    by_cases h20 : d ≤ (303/2048)
                    ·
                      refine ⟨bandA_076,bandA_076_valid,?_,?_⟩
                      all_goals dsimp only [bandA_076]; row_bound
                    ·
                      refine ⟨bandA_077,bandA_077_valid,?_,?_⟩
                      all_goals dsimp only [bandA_077]; row_bound
            ·
              by_cases h14 : d ≤ (39/256)
              ·
                by_cases h16 : d ≤ (77/512)
                ·
                  by_cases h18 : d ≤ (153/1024)
                  ·
                    by_cases h20 : d ≤ (305/2048)
                    ·
                      refine ⟨bandA_078,bandA_078_valid,?_,?_⟩
                      all_goals dsimp only [bandA_078]; row_bound
                    ·
                      refine ⟨bandA_079,bandA_079_valid,?_,?_⟩
                      all_goals dsimp only [bandA_079]; row_bound
                  ·
                    by_cases h20 : d ≤ (307/2048)
                    ·
                      refine ⟨bandA_080,bandA_080_valid,?_,?_⟩
                      all_goals dsimp only [bandA_080]; row_bound
                    ·
                      refine ⟨bandA_081,bandA_081_valid,?_,?_⟩
                      all_goals dsimp only [bandA_081]; row_bound
                ·
                  by_cases h18 : d ≤ (155/1024)
                  ·
                    by_cases h20 : d ≤ (309/2048)
                    ·
                      refine ⟨bandA_082,bandA_082_valid,?_,?_⟩
                      all_goals dsimp only [bandA_082]; row_bound
                    ·
                      refine ⟨bandA_083,bandA_083_valid,?_,?_⟩
                      all_goals dsimp only [bandA_083]; row_bound
                  ·
                    by_cases h20 : d ≤ (311/2048)
                    ·
                      refine ⟨bandA_084,bandA_084_valid,?_,?_⟩
                      all_goals dsimp only [bandA_084]; row_bound
                    ·
                      refine ⟨bandA_085,bandA_085_valid,?_,?_⟩
                      all_goals dsimp only [bandA_085]; row_bound
              ·
                by_cases h16 : d ≤ (79/512)
                ·
                  by_cases h18 : d ≤ (157/1024)
                  ·
                    refine ⟨bandA_086,bandA_086_valid,?_,?_⟩
                    all_goals dsimp only [bandA_086]; row_bound
                  ·
                    refine ⟨bandA_087,bandA_087_valid,?_,?_⟩
                    all_goals dsimp only [bandA_087]; row_bound
                ·
                  by_cases h18 : d ≤ (159/1024)
                  ·
                    refine ⟨bandA_088,bandA_088_valid,?_,?_⟩
                    all_goals dsimp only [bandA_088]; row_bound
                  ·
                    refine ⟨bandA_089,bandA_089_valid,?_,?_⟩
                    all_goals dsimp only [bandA_089]; row_bound
        ·
          by_cases h10 : d ≤ (11/64)
          ·
            by_cases h12 : d ≤ (21/128)
            ·
              by_cases h14 : d ≤ (41/256)
              ·
                by_cases h16 : d ≤ (81/512)
                ·
                  by_cases h18 : d ≤ (161/1024)
                  ·
                    refine ⟨bandA_090,bandA_090_valid,?_,?_⟩
                    all_goals dsimp only [bandA_090]; row_bound
                  ·
                    refine ⟨bandA_091,bandA_091_valid,?_,?_⟩
                    all_goals dsimp only [bandA_091]; row_bound
                ·
                  by_cases h18 : d ≤ (163/1024)
                  ·
                    refine ⟨bandA_092,bandA_092_valid,?_,?_⟩
                    all_goals dsimp only [bandA_092]; row_bound
                  ·
                    refine ⟨bandA_093,bandA_093_valid,?_,?_⟩
                    all_goals dsimp only [bandA_093]; row_bound
              ·
                by_cases h16 : d ≤ (83/512)
                ·
                  by_cases h18 : d ≤ (165/1024)
                  ·
                    refine ⟨bandA_094,bandA_094_valid,?_,?_⟩
                    all_goals dsimp only [bandA_094]; row_bound
                  ·
                    refine ⟨bandA_095,bandA_095_valid,?_,?_⟩
                    all_goals dsimp only [bandA_095]; row_bound
                ·
                  by_cases h18 : d ≤ (167/1024)
                  ·
                    refine ⟨bandA_096,bandA_096_valid,?_,?_⟩
                    all_goals dsimp only [bandA_096]; row_bound
                  ·
                    refine ⟨bandA_097,bandA_097_valid,?_,?_⟩
                    all_goals dsimp only [bandA_097]; row_bound
            ·
              by_cases h14 : d ≤ (43/256)
              ·
                by_cases h16 : d ≤ (85/512)
                ·
                  by_cases h18 : d ≤ (169/1024)
                  ·
                    refine ⟨bandA_098,bandA_098_valid,?_,?_⟩
                    all_goals dsimp only [bandA_098]; row_bound
                  ·
                    refine ⟨bandA_099,bandA_099_valid,?_,?_⟩
                    all_goals dsimp only [bandA_099]; row_bound
                ·
                  refine ⟨bandA_100,bandA_100_valid,?_,?_⟩
                  all_goals dsimp only [bandA_100]; row_bound
              ·
                by_cases h16 : d ≤ (87/512)
                ·
                  refine ⟨bandA_101,bandA_101_valid,?_,?_⟩
                  all_goals dsimp only [bandA_101]; row_bound
                ·
                  refine ⟨bandA_102,bandA_102_valid,?_,?_⟩
                  all_goals dsimp only [bandA_102]; row_bound
          ·
            by_cases h12 : d ≤ (23/128)
            ·
              by_cases h14 : d ≤ (45/256)
              ·
                by_cases h16 : d ≤ (89/512)
                ·
                  refine ⟨bandA_103,bandA_103_valid,?_,?_⟩
                  all_goals dsimp only [bandA_103]; row_bound
                ·
                  refine ⟨bandA_104,bandA_104_valid,?_,?_⟩
                  all_goals dsimp only [bandA_104]; row_bound
              ·
                by_cases h16 : d ≤ (91/512)
                ·
                  refine ⟨bandA_105,bandA_105_valid,?_,?_⟩
                  all_goals dsimp only [bandA_105]; row_bound
                ·
                  refine ⟨bandA_106,bandA_106_valid,?_,?_⟩
                  all_goals dsimp only [bandA_106]; row_bound
            ·
              by_cases h14 : d ≤ (47/256)
              ·
                by_cases h16 : d ≤ (93/512)
                ·
                  refine ⟨bandA_107,bandA_107_valid,?_,?_⟩
                  all_goals dsimp only [bandA_107]; row_bound
                ·
                  refine ⟨bandA_108,bandA_108_valid,?_,?_⟩
                  all_goals dsimp only [bandA_108]; row_bound
              ·
                refine ⟨bandA_109,bandA_109_valid,?_,?_⟩
                all_goals dsimp only [bandA_109]; row_bound
      ·
        by_cases h8 : d ≤ (7/32)
        ·
          by_cases h10 : d ≤ (13/64)
          ·
            by_cases h12 : d ≤ (25/128)
            ·
              by_cases h14 : d ≤ (49/256)
              ·
                refine ⟨bandA_110,bandA_110_valid,?_,?_⟩
                all_goals dsimp only [bandA_110]; row_bound
              ·
                refine ⟨bandA_111,bandA_111_valid,?_,?_⟩
                all_goals dsimp only [bandA_111]; row_bound
            ·
              by_cases h14 : d ≤ (51/256)
              ·
                refine ⟨bandA_112,bandA_112_valid,?_,?_⟩
                all_goals dsimp only [bandA_112]; row_bound
              ·
                refine ⟨bandA_113,bandA_113_valid,?_,?_⟩
                all_goals dsimp only [bandA_113]; row_bound
          ·
            by_cases h12 : d ≤ (27/128)
            ·
              refine ⟨bandA_114,bandA_114_valid,?_,?_⟩
              all_goals dsimp only [bandA_114]; row_bound
            ·
              refine ⟨bandA_115,bandA_115_valid,?_,?_⟩
              all_goals dsimp only [bandA_115]; row_bound
        ·
          by_cases h10 : d ≤ (15/64)
          ·
            by_cases h12 : d ≤ (29/128)
            ·
              refine ⟨bandA_116,bandA_116_valid,?_,?_⟩
              all_goals dsimp only [bandA_116]; row_bound
            ·
              refine ⟨bandA_117,bandA_117_valid,?_,?_⟩
              all_goals dsimp only [bandA_117]; row_bound
          ·
            refine ⟨bandA_118,bandA_118_valid,?_,?_⟩
            all_goals dsimp only [bandA_118]; row_bound
  ·
    by_cases h4 : d ≤ (3/8)
    ·
      by_cases h6 : d ≤ (5/16)
      ·
        by_cases h8 : d ≤ (9/32)
        ·
          by_cases h10 : d ≤ (17/64)
          ·
            refine ⟨bandA_119,bandA_119_valid,?_,?_⟩
            all_goals dsimp only [bandA_119]; row_bound
          ·
            refine ⟨bandA_120,bandA_120_valid,?_,?_⟩
            all_goals dsimp only [bandA_120]; row_bound
        ·
          refine ⟨bandA_121,bandA_121_valid,?_,?_⟩
          all_goals dsimp only [bandA_121]; row_bound
      ·
        by_cases h8 : d ≤ (11/32)
        ·
          refine ⟨bandA_122,bandA_122_valid,?_,?_⟩
          all_goals dsimp only [bandA_122]; row_bound
        ·
          refine ⟨bandA_123,bandA_123_valid,?_,?_⟩
          all_goals dsimp only [bandA_123]; row_bound
    ·
      by_cases h6 : d ≤ (7/16)
      ·
        by_cases h8 : d ≤ (13/32)
        ·
          refine ⟨bandA_124,bandA_124_valid,?_,?_⟩
          all_goals dsimp only [bandA_124]; row_bound
        ·
          refine ⟨bandA_125,bandA_125_valid,?_,?_⟩
          all_goals dsimp only [bandA_125]; row_bound
      ·
        by_cases h8 : d ≤ (15/32)
        ·
          refine ⟨bandA_126,bandA_126_valid,?_,?_⟩
          all_goals dsimp only [bandA_126]; row_bound
        ·
          refine ⟨bandA_127,bandA_127_valid,?_,?_⟩
          all_goals dsimp only [bandA_127]; row_bound

theorem bandA_forbidden {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/2) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (347/200) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ (11/12) ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  obtain ⟨row,hrow,hlo,hhi⟩ := bandA_cover hd
  have hh := hrow.forbidden (by norm_num [L]) ⟨hlo,hhi⟩
  rcases hrow with ⟨_,_,_,_,_,_,_,h₁,h₂,_,_,_⟩
  exact ⟨-row.angle₁,row.angle₂,by linarith only [h₁.1],h₂.1,
    by linarith only [hh.1],by linarith only [h₁.2, h₂.2],hh.2⟩

def bandB_000 : Row := ⟨0, (1/16), (19/20), 0, (265677/1000000), 0, (15/16), (1781997/1000000)⟩
lemma bandB_000_valid : bandB_000.Valid (19/20) (899/500) := by
  row_check bandB_000
def bandB_001 : Row := ⟨(1/16), (1/8), (19/20), (1/16), (169593/500000), (444018893/1000000000), (7/8), (1465931/1000000)⟩
lemma bandB_001_valid : bandB_001.Valid (19/20) (899/500) := by
  row_check bandB_001
def bandB_002 : Row := ⟨(1/8), (5/32), (19/20), (1/8), (426283/1000000), (50086297/100000000), (27/32), (1399809/1000000)⟩
lemma bandB_002_valid : bandB_002.Valid (19/20) (899/500) := by
  row_check bandB_002
def bandB_003 : Row := ⟨(5/32), (3/16), (19/20), (5/32), (473703/1000000), (137527617/250000000), (13/16), (670179/500000)⟩
lemma bandB_003_valid : bandB_003.Valid (19/20) (899/500) := by
  row_check bandB_003
def bandB_004 : Row := ⟨(3/16), (7/32), (19/20), (3/16), (130743/250000), (593654963/1000000000), (25/32), (1285727/1000000)⟩
lemma bandB_004_valid : bandB_004.Valid (19/20) (899/500) := by
  row_check bandB_004
def bandB_005 : Row := ⟨(7/32), (1/4), (19/20), (7/32), (22943/40000), (79084387/125000000), (3/4), (1234773/1000000)⟩
lemma bandB_005_valid : bandB_005.Valid (19/20) (899/500) := by
  row_check bandB_005
def bandB_006 : Row := ⟨(1/4), (9/32), (118603711/125000000), (1/4), (38897/62500), (83495529/125000000), (23/32), (1186729/1000000)⟩
lemma bandB_006_valid : bandB_006.Valid (19/20) (899/500) := by
  row_check bandB_006
def bandB_007 : Row := ⟨(9/32), (19/64), (940040539/1000000000), (9/32), (655437/1000000), (17109811/25000000), (45/64), (581811/500000)⟩
lemma bandB_007_valid : bandB_007.Valid (19/20) (899/500) := by
  row_check bandB_007
def bandB_008 : Row := ⟨(19/64), (5/16), (935223509/1000000000), (19/64), (672101/1000000), (1750217/2500000), (11/16), (285263/250000)⟩
lemma bandB_008_valid : bandB_008.Valid (19/20) (899/500) := by
  row_check bandB_008
def bandB_009 : Row := ⟨(5/16), (21/64), (930119093/1000000000), (5/16), (344427/500000), (715095631/1000000000), (43/64), (1118971/1000000)⟩
lemma bandB_009_valid : bandB_009.Valid (19/20) (899/500) := by
  row_check bandB_009
def bandB_010 : Row := ⟨(21/64), (11/32), (231180633/250000000), (21/64), (705701/1000000), (583569/800000), (21/32), (1097339/1000000)⟩
lemma bandB_010_valid : bandB_010.Valid (19/20) (899/500) := by
  row_check bandB_010
def bandB_011 : Row := ⟨(11/32), (23/64), (22975717/25000000), (11/32), (14453/20000), (371610477/500000000), (41/64), (26903/25000)⟩
lemma bandB_011_valid : bandB_011.Valid (19/20) (899/500) := by
  row_check bandB_011
def bandB_012 : Row := ⟨(23/64), (47/128), (456515987/500000000), (23/64), (739707/1000000), (749884069/1000000000), (81/128), (213131/200000)⟩
lemma bandB_012_valid : bandB_012.Valid (19/20) (899/500) := by
  row_check bandB_012
def bandB_013 : Row := ⟨(47/128), (3/8), (56869887/62500000), (47/128), (374139/500000), (756407811/1000000000), (5/8), (527641/500000)⟩
lemma bandB_013_valid : bandB_013.Valid (19/20) (899/500) := by
  row_check bandB_013
def bandB_014 : Row := ⟨(3/8), (49/128), (906726407/1000000000), (3/8), (756879/1000000), (762795757/1000000000), (79/128), (1044997/1000000)⟩
lemma bandB_014_valid : bandB_014.Valid (19/20) (899/500) := by
  row_check bandB_014
def bandB_015 : Row := ⟨(49/128), (25/64), (903455791/1000000000), (49/128), (76551/100000), (76905129/100000000), (39/64), (1034797/1000000)⟩
lemma bandB_015_valid : bandB_015.Valid (19/20) (899/500) := by
  row_check bandB_015
def bandB_016 : Row := ⟨(25/64), (51/128), (450052743/500000000), (25/64), (387087/500000), (48448601/62500000), (77/128), (1024679/1000000)⟩
lemma bandB_016_valid : bandB_016.Valid (19/20) (899/500) := by
  row_check bandB_016
def bandB_017 : Row := ⟨(51/128), (103/256), (448337299/500000000), (51/128), (78287/100000), (389096641/500000000), (153/256), (1019649/1000000)⟩
lemma bandB_017_valid : bandB_017.Valid (19/20) (899/500) := by
  row_check bandB_017
def bandB_018 : Row := ⟨(103/256), (13/32), (894928647/1000000000), (103/256), (787231/1000000), (390588887/500000000), (19/32), (1014639/1000000)⟩
lemma bandB_018_valid : bandB_018.Valid (19/20) (899/500) := by
  row_check bandB_018
def bandB_019 : Row := ⟨(13/32), (105/256), (893162199/1000000000), (13/32), (1979/2500), (98016431/125000000), (151/256), (63103/62500)⟩
lemma bandB_019_valid : bandB_019.Valid (19/20) (899/500) := by
  row_check bandB_019
def bandB_020 : Row := ⟨(105/256), (53/128), (891375133/1000000000), (105/256), (397989/500000), (787054651/1000000000), (75/128), (251169/250000)⟩
lemma bandB_020_valid : bandB_020.Valid (19/20) (899/500) := by
  row_check bandB_020
def bandB_021 : Row := ⟨(53/128), (107/256), (889567323/1000000000), (53/128), (200091/250000), (19748693/25000000), (149/256), (499861/500000)⟩
lemma bandB_021_valid : bandB_021.Valid (19/20) (899/500) := by
  row_check bandB_021
def bandB_022 : Row := ⟨(107/256), (27/64), (221934661/250000000), (107/256), (20119/25000), (792810987/1000000000), (37/64), (497393/500000)⟩
lemma bandB_022_valid : bandB_022.Valid (19/20) (899/500) := by
  row_check bandB_022
def bandB_023 : Row := ⟨(27/64), (109/256), (885888967/1000000000), (27/64), (161833/200000), (795644773/1000000000), (147/256), (247467/250000)⟩
lemma bandB_023_valid : bandB_023.Valid (19/20) (899/500) := by
  row_check bandB_023
def bandB_024 : Row := ⟨(109/256), (55/128), (442009079/500000000), (109/256), (813579/1000000), (798449391/1000000000), (73/128), (984967/1000000)⟩
lemma bandB_024_valid : bandB_024.Valid (19/20) (899/500) := by
  row_check bandB_024
def bandB_025 : Row := ⟨(55/128), (111/256), (176425217/200000000), (55/128), (409001/500000), (801225147/1000000000), (145/256), (980083/1000000)⟩
lemma bandB_025_valid : bandB_025.Valid (19/20) (899/500) := by
  row_check bandB_025
def bandB_026 : Row := ⟨(111/256), (223/512), (880212609/1000000000), (111/256), (164487/200000), (802602297/1000000000), (289/512), (977647/1000000)⟩
lemma bandB_026_valid : bandB_026.Valid (19/20) (899/500) := by
  row_check bandB_026
def bandB_027 : Row := ⟨(223/512), (7/16), (439623901/500000000), (223/512), (164931/200000), (401986171/500000000), (9/16), (60951/62500)⟩
lemma bandB_027_valid : bandB_027.Valid (19/20) (899/500) := by
  row_check bandB_027
def bandB_028 : Row := ⟨(7/16), (225/512), (878277591/1000000000), (7/16), (413439/500000), (20133383/25000000), (287/512), (972789/1000000)⟩
lemma bandB_028_valid : bandB_028.Valid (19/20) (899/500) := by
  row_check bandB_028
def bandB_029 : Row := ⟨(225/512), (113/256), (877301959/1000000000), (225/512), (829103/1000000), (403345633/500000000), (143/256), (194073/200000)⟩
lemma bandB_029_valid : bandB_029.Valid (19/20) (899/500) := by
  row_check bandB_029
def bandB_030 : Row := ⟨(113/256), (227/512), (109540111/125000000), (113/256), (831331/1000000), (808040217/1000000000), (285/512), (483973/500000)⟩
lemma bandB_030_valid : bandB_030.Valid (19/20) (899/500) := by
  row_check bandB_030
def bandB_031 : Row := ⟨(227/512), (57/128), (21883359/25000000), (227/512), (833561/1000000), (161876441/200000000), (71/128), (965531/1000000)⟩
lemma bandB_031_valid : bandB_031.Valid (19/20) (899/500) := by
  row_check bandB_031
def bandB_032 : Row := ⟨(57/128), (229/512), (174868471/200000000), (57/128), (835793/1000000), (810717267/1000000000), (283/512), (12039/12500)⟩
lemma bandB_032_valid : bandB_032.Valid (19/20) (899/500) := by
  row_check bandB_032
def bandB_033 : Row := ⟨(229/512), (115/256), (109168107/125000000), (229/512), (209507/250000), (812045437/1000000000), (141/256), (960713/1000000)⟩
lemma bandB_033_valid : bandB_033.Valid (19/20) (899/500) := by
  row_check bandB_033
def bandB_034 : Row := ⟨(115/256), (231/512), (872341843/1000000000), (115/256), (420133/500000), (203341687/250000000), (281/512), (95831/100000)⟩
lemma bandB_034_valid : bandB_034.Valid (19/20) (899/500) := by
  row_check bandB_034
def bandB_035 : Row := ⟨(231/512), (29/64), (435666649/500000000), (231/512), (421253/500000), (814681233/1000000000), (35/64), (95591/100000)⟩
lemma bandB_035_valid : bandB_035.Valid (19/20) (899/500) := by
  row_check bandB_035
def bandB_036 : Row := ⟨(29/64), (233/512), (870319201/1000000000), (29/64), (844749/1000000), (407994463/500000000), (279/512), (190703/200000)⟩
lemma bandB_036_valid : bandB_036.Valid (19/20) (899/500) := by
  row_check bandB_036
def bandB_037 : Row := ⟨(233/512), (117/256), (217324883/250000000), (233/512), (169399/200000), (817289859/1000000000), (139/256), (951123/1000000)⟩
lemma bandB_037_valid : bandB_037.Valid (19/20) (899/500) := by
  row_check bandB_037
def bandB_038 : Row := ⟨(117/256), (469/1024), (868274273/1000000000), (117/256), (849243/1000000), (817937801/1000000000), (555/1024), (949929/1000000)⟩
lemma bandB_038_valid : bandB_038.Valid (19/20) (899/500) := by
  row_check bandB_038
def bandB_039 : Row := ⟨(469/1024), (235/512), (867759541/1000000000), (469/1024), (13287/15625), (1598797/1953125), (277/512), (189747/200000)⟩
lemma bandB_039_valid : bandB_039.Valid (19/20) (899/500) := by
  row_check bandB_039
def bandB_040 : Row := ⟨(235/512), (471/1024), (867243403/1000000000), (235/512), (851493/1000000), (409614327/500000000), (553/1024), (947543/1000000)⟩
lemma bandB_040_valid : bandB_040.Valid (19/20) (899/500) := by
  row_check bandB_040
def bandB_041 : Row := ⟨(471/1024), (59/128), (433362929/500000000), (471/1024), (42631/50000), (409935787/500000000), (69/128), (946351/1000000)⟩
lemma bandB_041_valid : bandB_041.Valid (19/20) (899/500) := by
  row_check bandB_041
def bandB_042 : Row := ⟨(59/128), (473/1024), (866206903/1000000000), (59/128), (853747/1000000), (205128207/250000000), (551/1024), (945161/1000000)⟩
lemma bandB_042_valid : bandB_042.Valid (19/20) (899/500) := by
  row_check bandB_042
def bandB_043 : Row := ⟨(473/1024), (237/512), (432843267/500000000), (473/1024), (6839/8000), (41057621/50000000), (275/512), (943971/1000000)⟩
lemma bandB_043_valid : bandB_043.Valid (19/20) (899/500) := by
  row_check bandB_043
def bandB_044 : Row := ⟨(237/512), (475/1024), (865164751/1000000000), (237/512), (856003/1000000), (821790353/1000000000), (549/1024), (471391/500000)⟩
lemma bandB_044_valid : bandB_044.Valid (19/20) (899/500) := by
  row_check bandB_044
def bandB_045 : Row := ⟨(475/1024), (119/256), (17292831/20000000), (475/1024), (214283/250000), (102803329/125000000), (137/256), (470797/500000)⟩
lemma bandB_045_valid : bandB_045.Valid (19/20) (899/500) := by
  row_check bandB_045
def bandB_046 : Row := ⟨(119/256), (477/1024), (13501827/15625000), (119/256), (429131/500000), (41153063/50000000), (547/1024), (940407/1000000)⟩
lemma bandB_046_valid : bandB_046.Valid (19/20) (899/500) := by
  row_check bandB_046
def bandB_047 : Row := ⟨(477/1024), (239/512), (863590883/1000000000), (477/1024), (13428/15625), (411847121/500000000), (273/512), (939221/1000000)⟩
lemma bandB_047_valid : bandB_047.Valid (19/20) (899/500) := by
  row_check bandB_047
def bandB_048 : Row := ⟨(239/512), (479/1024), (863063413/1000000000), (239/512), (215131/250000), (824325581/1000000000), (545/1024), (234509/250000)⟩
lemma bandB_048_valid : bandB_048.Valid (19/20) (899/500) := by
  row_check bandB_048
def bandB_049 : Row := ⟨(479/1024), (15/32), (431267257/500000000), (479/1024), (172331/200000), (10311941/12500000), (17/32), (234213/250000)⟩
lemma bandB_049_valid : bandB_049.Valid (19/20) (899/500) := by
  row_check bandB_049
def bandB_050 : Row := ⟨(15/32), (481/1024), (172400837/200000000), (15/32), (215697/250000), (51598959/62500000), (543/1024), (935669/1000000)⟩
lemma bandB_050_valid : bandB_050.Valid (19/20) (899/500) := by
  row_check bandB_050
def bandB_051 : Row := ⟨(481/1024), (241/512), (430736211/500000000), (481/1024), (863921/1000000), (826209777/1000000000), (271/512), (467243/500000)⟩
lemma bandB_051_valid : bandB_051.Valid (19/20) (899/500) := by
  row_check bandB_051
def bandB_052 : Row := ⟨(241/512), (483/1024), (860939223/1000000000), (241/512), (173011/200000), (826834581/1000000000), (541/1024), (186661/200000)⟩
lemma bandB_052_valid : bandB_052.Valid (19/20) (899/500) := by
  row_check bandB_052
def bandB_053 : Row := ⟨(483/1024), (121/256), (172080917/200000000), (483/1024), (86619/100000), (827457761/1000000000), (135/256), (233031/250000)⟩
lemma bandB_053_valid : bandB_053.Valid (19/20) (899/500) := by
  row_check bandB_053
def bandB_054 : Row := ⟨(121/256), (485/1024), (171973701/200000000), (121/256), (34693/40000), (20701983/25000000), (539/1024), (14546/15625)⟩
lemma bandB_054_valid : bandB_054.Valid (19/20) (899/500) := by
  row_check bandB_054
def bandB_055 : Row := ⟨(485/1024), (243/512), (429665491/500000000), (485/1024), (868461/1000000), (828699263/1000000000), (269/512), (185953/200000)⟩
lemma bandB_055_valid : bandB_055.Valid (19/20) (899/500) := by
  row_check bandB_055
def bandB_056 : Row := ⟨(243/512), (487/1024), (858792011/1000000000), (243/512), (434799/500000), (103664699/125000000), (537/1024), (928587/1000000)⟩
lemma bandB_056_valid : bandB_056.Valid (19/20) (899/500) := by
  row_check bandB_056
def bandB_057 : Row := ⟨(487/1024), (61/128), (858251591/1000000000), (487/1024), (174147/200000), (829934311/1000000000), (67/128), (92741/100000)⟩
lemma bandB_057_valid : bandB_057.Valid (19/20) (899/500) := by
  row_check bandB_057
def bandB_058 : Row := ⟨(61/128), (489/1024), (428854859/500000000), (61/128), (435937/500000), (51909339/62500000), (535/1024), (463117/500000)⟩
lemma bandB_058_valid : bandB_058.Valid (19/20) (899/500) := by
  row_check bandB_058
def bandB_059 : Row := ⟨(489/1024), (245/512), (85716639/100000000), (489/1024), (873013/1000000), (415581467/500000000), (267/512), (925059/1000000)⟩
lemma bandB_059_valid : bandB_059.Valid (19/20) (899/500) := by
  row_check bandB_059
def bandB_060 : Row := ⟨(245/512), (491/1024), (171324321/200000000), (245/512), (109269/125000), (415887423/500000000), (533/1024), (230971/250000)⟩
lemma bandB_060_valid : bandB_060.Valid (19/20) (899/500) := by
  row_check bandB_060
def bandB_061 : Row := ⟨(491/1024), (123/256), (428037679/500000000), (491/1024), (875293/1000000), (416192581/500000000), (133/256), (92271/100000)⟩
lemma bandB_061_valid : bandB_061.Valid (19/20) (899/500) := by
  row_check bandB_061
def bandB_062 : Row := ⟨(123/256), (985/2048), (26735239/31250000), (123/256), (438217/500000), (416344861/500000000), (1063/2048), (230531/250000)⟩
lemma bandB_062_valid : bandB_062.Valid (19/20) (899/500) := by
  row_check bandB_062
def bandB_063 : Row := ⟨(985/2048), (493/1024), (213813311/250000000), (985/2048), (175401/200000), (166598777/200000000), (531/1024), (460769/500000)⟩
lemma bandB_063_valid : bandB_063.Valid (19/20) (899/500) := by
  row_check bandB_063
def bandB_064 : Row := ⟨(493/1024), (987/2048), (106872309/125000000), (493/1024), (109697/125000), (833297651/1000000000), (1061/2048), (115119/125000)⟩
lemma bandB_064_valid : bandB_064.Valid (19/20) (899/500) := by
  row_check bandB_064
def bandB_065 : Row := ⟨(987/2048), (247/512), (854703333/1000000000), (987/2048), (878147/1000000), (833601021/1000000000), (265/512), (460183/500000)⟩
lemma bandB_065_valid : bandB_065.Valid (19/20) (899/500) := by
  row_check bandB_065
def bandB_066 : Row := ⟨(247/512), (989/2048), (854427827/1000000000), (247/512), (439359/500000), (416951997/500000000), (1059/2048), (45989/50000)⟩
lemma bandB_066_valid : bandB_066.Valid (19/20) (899/500) := by
  row_check bandB_066
def bandB_067 : Row := ⟨(989/2048), (495/1024), (53384497/62500000), (989/2048), (87929/100000), (834206571/1000000000), (529/1024), (183839/200000)⟩
lemma bandB_067_valid : bandB_067.Valid (19/20) (899/500) := by
  row_check bandB_067
def bandB_068 : Row := ⟨(495/1024), (991/2048), (85387571/100000000), (495/1024), (879861/1000000), (52156797/62500000), (1057/2048), (918609/1000000)⟩
lemma bandB_068_valid : bandB_068.Valid (19/20) (899/500) := by
  row_check bandB_068
def bandB_069 : Row := ⟨(991/2048), (31/64), (426799549/500000000), (991/2048), (880433/1000000), (834810539/1000000000), (33/64), (114753/125000)⟩
lemma bandB_069_valid : bandB_069.Valid (19/20) (899/500) := by
  row_check bandB_069
def bandB_070 : Row := ⟨(31/64), (993/2048), (426661059/500000000), (31/64), (440503/500000), (835111931/1000000000), (1055/2048), (2867/3125)⟩
lemma bandB_070_valid : bandB_070.Valid (19/20) (899/500) := by
  row_check bandB_070
def bandB_071 : Row := ⟨(993/2048), (497/1024), (26657649/31250000), (993/2048), (440789/500000), (835412929/1000000000), (527/1024), (183371/200000)⟩
lemma bandB_071_valid : bandB_071.Valid (19/20) (899/500) := by
  row_check bandB_071
def bandB_072 : Row := ⟨(497/1024), (995/2048), (106595881/125000000), (497/1024), (17643/20000), (417856767/500000000), (1053/2048), (916271/1000000)⟩
lemma bandB_072_valid : bandB_072.Valid (19/20) (899/500) := by
  row_check bandB_072
def bandB_073 : Row := ⟨(995/2048), (249/512), (426244479/500000000), (995/2048), (882723/1000000), (167202749/200000000), (263/512), (915687/1000000)⟩
lemma bandB_073_valid : bandB_073.Valid (19/20) (899/500) := by
  row_check bandB_073
def bandB_074 : Row := ⟨(249/512), (997/2048), (852210497/1000000000), (249/512), (27603/31250), (836313563/1000000000), (1051/2048), (915103/1000000)⟩
lemma bandB_074_valid : bandB_074.Valid (19/20) (899/500) := by
  row_check bandB_074
def bandB_075 : Row := ⟨(997/2048), (499/1024), (425965833/500000000), (997/2048), (883869/1000000), (836612989/1000000000), (525/1024), (914519/1000000)⟩
lemma bandB_075_valid : bandB_075.Valid (19/20) (899/500) := by
  row_check bandB_075
def bandB_076 : Row := ⟨(499/1024), (999/2048), (851652463/1000000000), (499/1024), (442221/500000), (836912023/1000000000), (1049/2048), (182787/200000)⟩
lemma bandB_076_valid : bandB_076.Valid (19/20) (899/500) := by
  row_check bandB_076
def bandB_077 : Row := ⟨(999/2048), (125/256), (851372889/1000000000), (999/2048), (110627/125000), (167442133/200000000), (131/256), (114169/125000)⟩
lemma bandB_077_valid : bandB_077.Valid (19/20) (899/500) := by
  row_check bandB_077
def bandB_078 : Row := ⟨(125/256), (1001/2048), (851092943/1000000000), (125/256), (885589/1000000), (209377229/250000000), (1047/2048), (912769/1000000)⟩
lemma bandB_078_valid : bandB_078.Valid (19/20) (899/500) := by
  row_check bandB_078
def bandB_079 : Row := ⟨(1001/2048), (501/1024), (6806501/8000000), (1001/2048), (886163/1000000), (837806777/1000000000), (523/1024), (456093/500000)⟩
lemma bandB_079_valid : bandB_079.Valid (19/20) (899/500) := by
  row_check bandB_079
def bandB_080 : Row := ⟨(501/1024), (1003/2048), (850531933/1000000000), (501/1024), (886737/1000000), (838104247/1000000000), (1045/2048), (911603/1000000)⟩
lemma bandB_080_valid : bandB_080.Valid (19/20) (899/500) := by
  row_check bandB_080
def bandB_081 : Row := ⟨(1003/2048), (251/512), (850250869/1000000000), (1003/2048), (887311/1000000), (838401327/1000000000), (261/512), (911021/1000000)⟩
lemma bandB_081_valid : bandB_081.Valid (19/20) (899/500) := by
  row_check bandB_081
def bandB_082 : Row := ⟨(251/512), (1005/2048), (106246179/125000000), (251/512), (443943/500000), (838698017/1000000000), (1043/2048), (455219/500000)⟩
lemma bandB_082_valid : bandB_082.Valid (19/20) (899/500) := by
  row_check bandB_082
def bandB_083 : Row := ⟨(1005/2048), (503/1024), (42484381/50000000), (1005/2048), (44423/50000), (838994319/1000000000), (521/1024), (28433/31250)⟩
lemma bandB_083_valid : bandB_083.Valid (19/20) (899/500) := by
  row_check bandB_083
def bandB_084 : Row := ⟨(503/1024), (1007/2048), (424702717/500000000), (503/1024), (177807/200000), (104911279/125000000), (1041/2048), (454637/500000)⟩
lemma bandB_084_valid : bandB_084.Valid (19/20) (899/500) := by
  row_check bandB_084
def bandB_085 : Row := ⟨(1007/2048), (63/128), (424561437/500000000), (1007/2048), (88961/100000), (209896439/250000000), (65/128), (908693/1000000)⟩
lemma bandB_085_valid : bandB_085.Valid (19/20) (899/500) := by
  row_check bandB_085
def bandB_086 : Row := ⟨(63/128), (1009/2048), (848839939/1000000000), (63/128), (178037/200000), (839880893/1000000000), (1039/2048), (908111/1000000)⟩
lemma bandB_086_valid : bandB_086.Valid (19/20) (899/500) := by
  row_check bandB_086
def bandB_087 : Row := ⟨(1009/2048), (505/1024), (212139157/250000000), (1009/2048), (22269/25000), (420087821/500000000), (519/1024), (90753/100000)⟩
lemma bandB_087_valid : bandB_087.Valid (19/20) (899/500) := by
  row_check bandB_087
def bandB_088 : Row := ⟨(505/1024), (1011/2048), (424136471/500000000), (505/1024), (111417/125000), (210117501/250000000), (1037/2048), (906949/1000000)⟩
lemma bandB_088_valid : bandB_088.Valid (19/20) (899/500) := by
  row_check bandB_088
def bandB_089 : Row := ⟨(1011/2048), (253/512), (10599861/12500000), (1011/2048), (111489/125000), (42038199/50000000), (259/512), (14162/15625)⟩
lemma bandB_089_valid : bandB_089.Valid (19/20) (899/500) := by
  row_check bandB_089
def bandB_090 : Row := ⟨(253/512), (1013/2048), (847704441/1000000000), (253/512), (892487/1000000), (841057569/1000000000), (1035/2048), (905787/1000000)⟩
lemma bandB_090_valid : bandB_090.Valid (19/20) (899/500) := by
  row_check bandB_090
def bandB_091 : Row := ⟨(1013/2048), (507/1024), (423709813/500000000), (1013/2048), (111633/125000), (841350773/1000000000), (517/1024), (905207/1000000)⟩
lemma bandB_091_valid : bandB_091.Valid (19/20) (899/500) := by
  row_check bandB_091
def bandB_092 : Row := ⟨(507/1024), (1015/2048), (847134433/1000000000), (507/1024), (22341/25000), (841643591/1000000000), (1033/2048), (904627/1000000)⟩
lemma bandB_092_valid : bandB_092.Valid (19/20) (899/500) := by
  row_check bandB_092
def bandB_093 : Row := ⟨(1015/2048), (127/256), (846848863/1000000000), (1015/2048), (111777/125000), (105242003/125000000), (129/256), (904047/1000000)⟩
lemma bandB_093_valid : bandB_093.Valid (19/20) (899/500) := by
  row_check bandB_093
def bandB_094 : Row := ⟨(127/256), (1017/2048), (423281457/500000000), (127/256), (894793/1000000), (105278509/125000000), (1031/2048), (903467/1000000)⟩
lemma bandB_094_valid : bandB_094.Valid (19/20) (899/500) := by
  row_check bandB_094
def bandB_095 : Row := ⟨(1017/2048), (509/1024), (211569147/250000000), (1017/2048), (89537/100000), (105314967/125000000), (515/1024), (902887/1000000)⟩
lemma bandB_095_valid : bandB_095.Valid (19/20) (899/500) := by
  row_check bandB_095
def bandB_096 : Row := ⟨(509/1024), (1019/2048), (845989883/1000000000), (509/1024), (895947/1000000), (842811017/1000000000), (1029/2048), (225577/250000)⟩
lemma bandB_096_valid : bandB_096.Valid (19/20) (899/500) := by
  row_check bandB_096
def bandB_097 : Row := ⟨(1019/2048), (255/512), (422851399/500000000), (1019/2048), (224131/250000), (421550957/500000000), (257/512), (901729/1000000)⟩
lemma bandB_097_valid : bandB_097.Valid (19/20) (899/500) := by
  row_check bandB_097
def bandB_098 : Row := ⟨(255/512), (1021/2048), (422707667/500000000), (255/512), (448551/500000), (210848107/250000000), (1027/2048), (901149/1000000)⟩
lemma bandB_098_valid : bandB_098.Valid (19/20) (899/500) := by
  row_check bandB_098
def bandB_099 : Row := ⟨(1021/2048), (511/1024), (84512749/100000000), (1021/2048), (897679/1000000), (843682559/1000000000), (513/1024), (900571/1000000)⟩
lemma bandB_099_valid : bandB_099.Valid (19/20) (899/500) := by
  row_check bandB_099
def bandB_100 : Row := ⟨(511/1024), (1023/2048), (422419633/500000000), (511/1024), (898257/1000000), (210993077/250000000), (1025/2048), (112499/125000)⟩
lemma bandB_100_valid : bandB_100.Valid (19/20) (899/500) := by
  row_check bandB_100
def bandB_101 : Row := ⟨(1023/2048), (1/2), (844550661/1000000000), (1023/2048), (179767/200000), (211065419/250000000), (1/2), (449707/500000)⟩
lemma bandB_101_valid : bandB_101.Valid (19/20) (899/500) := by
  row_check bandB_101

theorem bandB_cover {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/2) :
    ∃ row : Row, row.Valid (19/20) (899/500) ∧ row.lower ≤ d ∧ d ≤ row.upper := by
  by_cases h2 : d ≤ (1/4)
  ·
    by_cases h4 : d ≤ (1/8)
    ·
      by_cases h6 : d ≤ (1/16)
      ·
        refine ⟨bandB_000,bandB_000_valid,?_,?_⟩
        all_goals dsimp only [bandB_000]; row_bound
      ·
        refine ⟨bandB_001,bandB_001_valid,?_,?_⟩
        all_goals dsimp only [bandB_001]; row_bound
    ·
      by_cases h6 : d ≤ (3/16)
      ·
        by_cases h8 : d ≤ (5/32)
        ·
          refine ⟨bandB_002,bandB_002_valid,?_,?_⟩
          all_goals dsimp only [bandB_002]; row_bound
        ·
          refine ⟨bandB_003,bandB_003_valid,?_,?_⟩
          all_goals dsimp only [bandB_003]; row_bound
      ·
        by_cases h8 : d ≤ (7/32)
        ·
          refine ⟨bandB_004,bandB_004_valid,?_,?_⟩
          all_goals dsimp only [bandB_004]; row_bound
        ·
          refine ⟨bandB_005,bandB_005_valid,?_,?_⟩
          all_goals dsimp only [bandB_005]; row_bound
  ·
    by_cases h4 : d ≤ (3/8)
    ·
      by_cases h6 : d ≤ (5/16)
      ·
        by_cases h8 : d ≤ (9/32)
        ·
          refine ⟨bandB_006,bandB_006_valid,?_,?_⟩
          all_goals dsimp only [bandB_006]; row_bound
        ·
          by_cases h10 : d ≤ (19/64)
          ·
            refine ⟨bandB_007,bandB_007_valid,?_,?_⟩
            all_goals dsimp only [bandB_007]; row_bound
          ·
            refine ⟨bandB_008,bandB_008_valid,?_,?_⟩
            all_goals dsimp only [bandB_008]; row_bound
      ·
        by_cases h8 : d ≤ (11/32)
        ·
          by_cases h10 : d ≤ (21/64)
          ·
            refine ⟨bandB_009,bandB_009_valid,?_,?_⟩
            all_goals dsimp only [bandB_009]; row_bound
          ·
            refine ⟨bandB_010,bandB_010_valid,?_,?_⟩
            all_goals dsimp only [bandB_010]; row_bound
        ·
          by_cases h10 : d ≤ (23/64)
          ·
            refine ⟨bandB_011,bandB_011_valid,?_,?_⟩
            all_goals dsimp only [bandB_011]; row_bound
          ·
            by_cases h12 : d ≤ (47/128)
            ·
              refine ⟨bandB_012,bandB_012_valid,?_,?_⟩
              all_goals dsimp only [bandB_012]; row_bound
            ·
              refine ⟨bandB_013,bandB_013_valid,?_,?_⟩
              all_goals dsimp only [bandB_013]; row_bound
    ·
      by_cases h6 : d ≤ (7/16)
      ·
        by_cases h8 : d ≤ (13/32)
        ·
          by_cases h10 : d ≤ (25/64)
          ·
            by_cases h12 : d ≤ (49/128)
            ·
              refine ⟨bandB_014,bandB_014_valid,?_,?_⟩
              all_goals dsimp only [bandB_014]; row_bound
            ·
              refine ⟨bandB_015,bandB_015_valid,?_,?_⟩
              all_goals dsimp only [bandB_015]; row_bound
          ·
            by_cases h12 : d ≤ (51/128)
            ·
              refine ⟨bandB_016,bandB_016_valid,?_,?_⟩
              all_goals dsimp only [bandB_016]; row_bound
            ·
              by_cases h14 : d ≤ (103/256)
              ·
                refine ⟨bandB_017,bandB_017_valid,?_,?_⟩
                all_goals dsimp only [bandB_017]; row_bound
              ·
                refine ⟨bandB_018,bandB_018_valid,?_,?_⟩
                all_goals dsimp only [bandB_018]; row_bound
        ·
          by_cases h10 : d ≤ (27/64)
          ·
            by_cases h12 : d ≤ (53/128)
            ·
              by_cases h14 : d ≤ (105/256)
              ·
                refine ⟨bandB_019,bandB_019_valid,?_,?_⟩
                all_goals dsimp only [bandB_019]; row_bound
              ·
                refine ⟨bandB_020,bandB_020_valid,?_,?_⟩
                all_goals dsimp only [bandB_020]; row_bound
            ·
              by_cases h14 : d ≤ (107/256)
              ·
                refine ⟨bandB_021,bandB_021_valid,?_,?_⟩
                all_goals dsimp only [bandB_021]; row_bound
              ·
                refine ⟨bandB_022,bandB_022_valid,?_,?_⟩
                all_goals dsimp only [bandB_022]; row_bound
          ·
            by_cases h12 : d ≤ (55/128)
            ·
              by_cases h14 : d ≤ (109/256)
              ·
                refine ⟨bandB_023,bandB_023_valid,?_,?_⟩
                all_goals dsimp only [bandB_023]; row_bound
              ·
                refine ⟨bandB_024,bandB_024_valid,?_,?_⟩
                all_goals dsimp only [bandB_024]; row_bound
            ·
              by_cases h14 : d ≤ (111/256)
              ·
                refine ⟨bandB_025,bandB_025_valid,?_,?_⟩
                all_goals dsimp only [bandB_025]; row_bound
              ·
                by_cases h16 : d ≤ (223/512)
                ·
                  refine ⟨bandB_026,bandB_026_valid,?_,?_⟩
                  all_goals dsimp only [bandB_026]; row_bound
                ·
                  refine ⟨bandB_027,bandB_027_valid,?_,?_⟩
                  all_goals dsimp only [bandB_027]; row_bound
      ·
        by_cases h8 : d ≤ (15/32)
        ·
          by_cases h10 : d ≤ (29/64)
          ·
            by_cases h12 : d ≤ (57/128)
            ·
              by_cases h14 : d ≤ (113/256)
              ·
                by_cases h16 : d ≤ (225/512)
                ·
                  refine ⟨bandB_028,bandB_028_valid,?_,?_⟩
                  all_goals dsimp only [bandB_028]; row_bound
                ·
                  refine ⟨bandB_029,bandB_029_valid,?_,?_⟩
                  all_goals dsimp only [bandB_029]; row_bound
              ·
                by_cases h16 : d ≤ (227/512)
                ·
                  refine ⟨bandB_030,bandB_030_valid,?_,?_⟩
                  all_goals dsimp only [bandB_030]; row_bound
                ·
                  refine ⟨bandB_031,bandB_031_valid,?_,?_⟩
                  all_goals dsimp only [bandB_031]; row_bound
            ·
              by_cases h14 : d ≤ (115/256)
              ·
                by_cases h16 : d ≤ (229/512)
                ·
                  refine ⟨bandB_032,bandB_032_valid,?_,?_⟩
                  all_goals dsimp only [bandB_032]; row_bound
                ·
                  refine ⟨bandB_033,bandB_033_valid,?_,?_⟩
                  all_goals dsimp only [bandB_033]; row_bound
              ·
                by_cases h16 : d ≤ (231/512)
                ·
                  refine ⟨bandB_034,bandB_034_valid,?_,?_⟩
                  all_goals dsimp only [bandB_034]; row_bound
                ·
                  refine ⟨bandB_035,bandB_035_valid,?_,?_⟩
                  all_goals dsimp only [bandB_035]; row_bound
          ·
            by_cases h12 : d ≤ (59/128)
            ·
              by_cases h14 : d ≤ (117/256)
              ·
                by_cases h16 : d ≤ (233/512)
                ·
                  refine ⟨bandB_036,bandB_036_valid,?_,?_⟩
                  all_goals dsimp only [bandB_036]; row_bound
                ·
                  refine ⟨bandB_037,bandB_037_valid,?_,?_⟩
                  all_goals dsimp only [bandB_037]; row_bound
              ·
                by_cases h16 : d ≤ (235/512)
                ·
                  by_cases h18 : d ≤ (469/1024)
                  ·
                    refine ⟨bandB_038,bandB_038_valid,?_,?_⟩
                    all_goals dsimp only [bandB_038]; row_bound
                  ·
                    refine ⟨bandB_039,bandB_039_valid,?_,?_⟩
                    all_goals dsimp only [bandB_039]; row_bound
                ·
                  by_cases h18 : d ≤ (471/1024)
                  ·
                    refine ⟨bandB_040,bandB_040_valid,?_,?_⟩
                    all_goals dsimp only [bandB_040]; row_bound
                  ·
                    refine ⟨bandB_041,bandB_041_valid,?_,?_⟩
                    all_goals dsimp only [bandB_041]; row_bound
            ·
              by_cases h14 : d ≤ (119/256)
              ·
                by_cases h16 : d ≤ (237/512)
                ·
                  by_cases h18 : d ≤ (473/1024)
                  ·
                    refine ⟨bandB_042,bandB_042_valid,?_,?_⟩
                    all_goals dsimp only [bandB_042]; row_bound
                  ·
                    refine ⟨bandB_043,bandB_043_valid,?_,?_⟩
                    all_goals dsimp only [bandB_043]; row_bound
                ·
                  by_cases h18 : d ≤ (475/1024)
                  ·
                    refine ⟨bandB_044,bandB_044_valid,?_,?_⟩
                    all_goals dsimp only [bandB_044]; row_bound
                  ·
                    refine ⟨bandB_045,bandB_045_valid,?_,?_⟩
                    all_goals dsimp only [bandB_045]; row_bound
              ·
                by_cases h16 : d ≤ (239/512)
                ·
                  by_cases h18 : d ≤ (477/1024)
                  ·
                    refine ⟨bandB_046,bandB_046_valid,?_,?_⟩
                    all_goals dsimp only [bandB_046]; row_bound
                  ·
                    refine ⟨bandB_047,bandB_047_valid,?_,?_⟩
                    all_goals dsimp only [bandB_047]; row_bound
                ·
                  by_cases h18 : d ≤ (479/1024)
                  ·
                    refine ⟨bandB_048,bandB_048_valid,?_,?_⟩
                    all_goals dsimp only [bandB_048]; row_bound
                  ·
                    refine ⟨bandB_049,bandB_049_valid,?_,?_⟩
                    all_goals dsimp only [bandB_049]; row_bound
        ·
          by_cases h10 : d ≤ (31/64)
          ·
            by_cases h12 : d ≤ (61/128)
            ·
              by_cases h14 : d ≤ (121/256)
              ·
                by_cases h16 : d ≤ (241/512)
                ·
                  by_cases h18 : d ≤ (481/1024)
                  ·
                    refine ⟨bandB_050,bandB_050_valid,?_,?_⟩
                    all_goals dsimp only [bandB_050]; row_bound
                  ·
                    refine ⟨bandB_051,bandB_051_valid,?_,?_⟩
                    all_goals dsimp only [bandB_051]; row_bound
                ·
                  by_cases h18 : d ≤ (483/1024)
                  ·
                    refine ⟨bandB_052,bandB_052_valid,?_,?_⟩
                    all_goals dsimp only [bandB_052]; row_bound
                  ·
                    refine ⟨bandB_053,bandB_053_valid,?_,?_⟩
                    all_goals dsimp only [bandB_053]; row_bound
              ·
                by_cases h16 : d ≤ (243/512)
                ·
                  by_cases h18 : d ≤ (485/1024)
                  ·
                    refine ⟨bandB_054,bandB_054_valid,?_,?_⟩
                    all_goals dsimp only [bandB_054]; row_bound
                  ·
                    refine ⟨bandB_055,bandB_055_valid,?_,?_⟩
                    all_goals dsimp only [bandB_055]; row_bound
                ·
                  by_cases h18 : d ≤ (487/1024)
                  ·
                    refine ⟨bandB_056,bandB_056_valid,?_,?_⟩
                    all_goals dsimp only [bandB_056]; row_bound
                  ·
                    refine ⟨bandB_057,bandB_057_valid,?_,?_⟩
                    all_goals dsimp only [bandB_057]; row_bound
            ·
              by_cases h14 : d ≤ (123/256)
              ·
                by_cases h16 : d ≤ (245/512)
                ·
                  by_cases h18 : d ≤ (489/1024)
                  ·
                    refine ⟨bandB_058,bandB_058_valid,?_,?_⟩
                    all_goals dsimp only [bandB_058]; row_bound
                  ·
                    refine ⟨bandB_059,bandB_059_valid,?_,?_⟩
                    all_goals dsimp only [bandB_059]; row_bound
                ·
                  by_cases h18 : d ≤ (491/1024)
                  ·
                    refine ⟨bandB_060,bandB_060_valid,?_,?_⟩
                    all_goals dsimp only [bandB_060]; row_bound
                  ·
                    refine ⟨bandB_061,bandB_061_valid,?_,?_⟩
                    all_goals dsimp only [bandB_061]; row_bound
              ·
                by_cases h16 : d ≤ (247/512)
                ·
                  by_cases h18 : d ≤ (493/1024)
                  ·
                    by_cases h20 : d ≤ (985/2048)
                    ·
                      refine ⟨bandB_062,bandB_062_valid,?_,?_⟩
                      all_goals dsimp only [bandB_062]; row_bound
                    ·
                      refine ⟨bandB_063,bandB_063_valid,?_,?_⟩
                      all_goals dsimp only [bandB_063]; row_bound
                  ·
                    by_cases h20 : d ≤ (987/2048)
                    ·
                      refine ⟨bandB_064,bandB_064_valid,?_,?_⟩
                      all_goals dsimp only [bandB_064]; row_bound
                    ·
                      refine ⟨bandB_065,bandB_065_valid,?_,?_⟩
                      all_goals dsimp only [bandB_065]; row_bound
                ·
                  by_cases h18 : d ≤ (495/1024)
                  ·
                    by_cases h20 : d ≤ (989/2048)
                    ·
                      refine ⟨bandB_066,bandB_066_valid,?_,?_⟩
                      all_goals dsimp only [bandB_066]; row_bound
                    ·
                      refine ⟨bandB_067,bandB_067_valid,?_,?_⟩
                      all_goals dsimp only [bandB_067]; row_bound
                  ·
                    by_cases h20 : d ≤ (991/2048)
                    ·
                      refine ⟨bandB_068,bandB_068_valid,?_,?_⟩
                      all_goals dsimp only [bandB_068]; row_bound
                    ·
                      refine ⟨bandB_069,bandB_069_valid,?_,?_⟩
                      all_goals dsimp only [bandB_069]; row_bound
          ·
            by_cases h12 : d ≤ (63/128)
            ·
              by_cases h14 : d ≤ (125/256)
              ·
                by_cases h16 : d ≤ (249/512)
                ·
                  by_cases h18 : d ≤ (497/1024)
                  ·
                    by_cases h20 : d ≤ (993/2048)
                    ·
                      refine ⟨bandB_070,bandB_070_valid,?_,?_⟩
                      all_goals dsimp only [bandB_070]; row_bound
                    ·
                      refine ⟨bandB_071,bandB_071_valid,?_,?_⟩
                      all_goals dsimp only [bandB_071]; row_bound
                  ·
                    by_cases h20 : d ≤ (995/2048)
                    ·
                      refine ⟨bandB_072,bandB_072_valid,?_,?_⟩
                      all_goals dsimp only [bandB_072]; row_bound
                    ·
                      refine ⟨bandB_073,bandB_073_valid,?_,?_⟩
                      all_goals dsimp only [bandB_073]; row_bound
                ·
                  by_cases h18 : d ≤ (499/1024)
                  ·
                    by_cases h20 : d ≤ (997/2048)
                    ·
                      refine ⟨bandB_074,bandB_074_valid,?_,?_⟩
                      all_goals dsimp only [bandB_074]; row_bound
                    ·
                      refine ⟨bandB_075,bandB_075_valid,?_,?_⟩
                      all_goals dsimp only [bandB_075]; row_bound
                  ·
                    by_cases h20 : d ≤ (999/2048)
                    ·
                      refine ⟨bandB_076,bandB_076_valid,?_,?_⟩
                      all_goals dsimp only [bandB_076]; row_bound
                    ·
                      refine ⟨bandB_077,bandB_077_valid,?_,?_⟩
                      all_goals dsimp only [bandB_077]; row_bound
              ·
                by_cases h16 : d ≤ (251/512)
                ·
                  by_cases h18 : d ≤ (501/1024)
                  ·
                    by_cases h20 : d ≤ (1001/2048)
                    ·
                      refine ⟨bandB_078,bandB_078_valid,?_,?_⟩
                      all_goals dsimp only [bandB_078]; row_bound
                    ·
                      refine ⟨bandB_079,bandB_079_valid,?_,?_⟩
                      all_goals dsimp only [bandB_079]; row_bound
                  ·
                    by_cases h20 : d ≤ (1003/2048)
                    ·
                      refine ⟨bandB_080,bandB_080_valid,?_,?_⟩
                      all_goals dsimp only [bandB_080]; row_bound
                    ·
                      refine ⟨bandB_081,bandB_081_valid,?_,?_⟩
                      all_goals dsimp only [bandB_081]; row_bound
                ·
                  by_cases h18 : d ≤ (503/1024)
                  ·
                    by_cases h20 : d ≤ (1005/2048)
                    ·
                      refine ⟨bandB_082,bandB_082_valid,?_,?_⟩
                      all_goals dsimp only [bandB_082]; row_bound
                    ·
                      refine ⟨bandB_083,bandB_083_valid,?_,?_⟩
                      all_goals dsimp only [bandB_083]; row_bound
                  ·
                    by_cases h20 : d ≤ (1007/2048)
                    ·
                      refine ⟨bandB_084,bandB_084_valid,?_,?_⟩
                      all_goals dsimp only [bandB_084]; row_bound
                    ·
                      refine ⟨bandB_085,bandB_085_valid,?_,?_⟩
                      all_goals dsimp only [bandB_085]; row_bound
            ·
              by_cases h14 : d ≤ (127/256)
              ·
                by_cases h16 : d ≤ (253/512)
                ·
                  by_cases h18 : d ≤ (505/1024)
                  ·
                    by_cases h20 : d ≤ (1009/2048)
                    ·
                      refine ⟨bandB_086,bandB_086_valid,?_,?_⟩
                      all_goals dsimp only [bandB_086]; row_bound
                    ·
                      refine ⟨bandB_087,bandB_087_valid,?_,?_⟩
                      all_goals dsimp only [bandB_087]; row_bound
                  ·
                    by_cases h20 : d ≤ (1011/2048)
                    ·
                      refine ⟨bandB_088,bandB_088_valid,?_,?_⟩
                      all_goals dsimp only [bandB_088]; row_bound
                    ·
                      refine ⟨bandB_089,bandB_089_valid,?_,?_⟩
                      all_goals dsimp only [bandB_089]; row_bound
                ·
                  by_cases h18 : d ≤ (507/1024)
                  ·
                    by_cases h20 : d ≤ (1013/2048)
                    ·
                      refine ⟨bandB_090,bandB_090_valid,?_,?_⟩
                      all_goals dsimp only [bandB_090]; row_bound
                    ·
                      refine ⟨bandB_091,bandB_091_valid,?_,?_⟩
                      all_goals dsimp only [bandB_091]; row_bound
                  ·
                    by_cases h20 : d ≤ (1015/2048)
                    ·
                      refine ⟨bandB_092,bandB_092_valid,?_,?_⟩
                      all_goals dsimp only [bandB_092]; row_bound
                    ·
                      refine ⟨bandB_093,bandB_093_valid,?_,?_⟩
                      all_goals dsimp only [bandB_093]; row_bound
              ·
                by_cases h16 : d ≤ (255/512)
                ·
                  by_cases h18 : d ≤ (509/1024)
                  ·
                    by_cases h20 : d ≤ (1017/2048)
                    ·
                      refine ⟨bandB_094,bandB_094_valid,?_,?_⟩
                      all_goals dsimp only [bandB_094]; row_bound
                    ·
                      refine ⟨bandB_095,bandB_095_valid,?_,?_⟩
                      all_goals dsimp only [bandB_095]; row_bound
                  ·
                    by_cases h20 : d ≤ (1019/2048)
                    ·
                      refine ⟨bandB_096,bandB_096_valid,?_,?_⟩
                      all_goals dsimp only [bandB_096]; row_bound
                    ·
                      refine ⟨bandB_097,bandB_097_valid,?_,?_⟩
                      all_goals dsimp only [bandB_097]; row_bound
                ·
                  by_cases h18 : d ≤ (511/1024)
                  ·
                    by_cases h20 : d ≤ (1021/2048)
                    ·
                      refine ⟨bandB_098,bandB_098_valid,?_,?_⟩
                      all_goals dsimp only [bandB_098]; row_bound
                    ·
                      refine ⟨bandB_099,bandB_099_valid,?_,?_⟩
                      all_goals dsimp only [bandB_099]; row_bound
                  ·
                    by_cases h20 : d ≤ (1023/2048)
                    ·
                      refine ⟨bandB_100,bandB_100_valid,?_,?_⟩
                      all_goals dsimp only [bandB_100]; row_bound
                    ·
                      refine ⟨bandB_101,bandB_101_valid,?_,?_⟩
                      all_goals dsimp only [bandB_101]; row_bound

theorem bandB_forbidden {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1/2) :
    ∃ l u : ℝ, l ≤ 0 ∧ 0 ≤ u ∧ (899/500) < u-l ∧ u-l ≤ 4 ∧
      ∀ β, l ≤ β ∧ β ≤ u → ∃ v, |v| ≤ c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0 ≤ p.1 ∧ p.1 ≤ (19/20) ∧ -d ≤ p.2 ∧ p.2 ≤ 1-d := by
  obtain ⟨row,hrow,hlo,hhi⟩ := bandB_cover hd
  have hh := hrow.forbidden (by norm_num [L]) ⟨hlo,hhi⟩
  rcases hrow with ⟨_,_,_,_,_,_,_,h₁,h₂,_,_,_⟩
  exact ⟨-row.angle₁,row.angle₂,by linarith only [h₁.1],h₂.1,
    by linarith only [hh.1],by linarith only [h₁.2, h₂.2],hh.2⟩


end SquaresInCircles.Eight.CentralForbidden
