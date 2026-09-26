import SquaresInCircles.Common.RectangleArcs
import SquaresInCircles.Common.ElementaryTrig

/-!
# Five squares: the 12-gon and the exterior arcs

The tangents to `phi = 5/2` at `(1, 0)`, `(0, 1)` and `(g, g)`, with
`g = (√5-1)/2`, cut out the 12-gon `P5`. On the circle of radius `5/6`, every
exterior square with its centre in `P5` holds an arc longer than 72 degrees.
The radius is rational, and a cubic arcsine bound suffices.
-/
noncomputable section
open Set
namespace SquaresInCircles.Five

/-- The 12-gon: the octagon `P8` and the tangent at `(g, g)`. -/
def P5 (a b : ℝ) : Prop := P8 a b ∧ a+b ≤ Real.sqrt 5-1

/-- A square in the closed disk of radius `sqrt (5/2)` has its centre in `P5`. -/
lemma p5_of_phi {a b : ℝ} (h : phi a b ≤ 5/2) : P5 a b := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have h₀ := tangent_le (u := 1) (v := 0) h (by norm_num [phi])
  have h₁ := tangent_le (u := 0) (v := 1) h (by norm_num [phi])
  have h₂ := tangent_le (u := (Real.sqrt 5-1)/2) (v := (Real.sqrt 5-1)/2) h
    (by unfold phi; linarith)
  refine ⟨⟨by linarith,by linarith⟩,le_of_not_gt fun hn => ?_⟩
  nlinarith [mul_pos (Real.sqrt_pos.2 (show (0:ℝ) < 5 by norm_num)) (sub_pos.2 hn)]

lemma p5_swap {a b : ℝ} (h : P5 a b) : P5 b a :=
  ⟨⟨by linarith [h.1.2],by linarith [h.1.1]⟩,by linarith [h.2]⟩

def aux : ℝ := 5/6

/-- An arcsine sum, from the cubic bound on `arcsin`. -/
lemma arcsin_sum {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (hy0 : -1/2 ≤ y) (hy1 : y ≤ 1/2)
    (hsum : x+y ≤ 237/1000) (hside : 3*x+y ≤ 1) :
    Real.arcsin (x/aux)+Real.arcsin (y/aux) < Real.pi/10 := by
  rw [show x/aux=6/5*x by rw [aux]; ring,show y/aux=6/5*y by rw [aux]; ring]
  have hFx := arcsin_le_cubic (x := 6/5*x) (by positivity) (by linarith)
  have hrat : Real.arcsin (6/5*x)+Real.arcsin (6/5*y) < 313/1000 := by
    by_cases hy : 0 ≤ y
    · have hFy := arcsin_le_cubic (x := 6/5*y) (by positivity) (by linarith)
      have hcross := mul_nonneg (mul_nonneg hx0 hy) (add_nonneg hx0 hy)
      have hsumcube : (x+y)^3 ≤ (237/1000:ℝ)^3 := by gcongr
      linarith
    · have hFy := arcsin_le_self_of_nonpos (x := 6/5*y) (by linarith) (by linarith)
      by_cases hxq : x ≤ 23/60
      · have hc : x^3 ≤ (23/60:ℝ)^3 := by gcongr
        linarith
      · have hq : 23/60 ≤ x := (lt_of_not_ge hxq).le
        have hxsq : x^2+x*(23/60)+(23/60:ℝ)^2 ≤ 3/4 := by nlinarith
        have hprod := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hxsq)
        linarith
  linarith [Real.pi_gt_d2]

/-- On the circle of radius `5/6` the crossings of an exterior square with
centre in `P5` are more than `2π/5` apart: each of `2A`, `A+V`, `A+U` and `U+V`
exceeds it. -/
lemma arc_length {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b) (hsort : b ≤ a) (h : P5 a b) :
    2*Real.pi/5 < min (capA aux a) (capU aux b)+min (capA aux a) (capV aux b) := by
  have ha1 : a ≤ 1 := by linarith [h.1.1]
  have hA : capA aux a=Real.pi/2-Real.arcsin ((a-1/2)/aux) :=
    Real.arccos_eq_pi_div_two_sub_arcsin _
  have hV : capV aux b=-Real.arcsin ((b-1/2)/aux) := by
    rw [capV,← Real.arcsin_neg]; congr 1; ring
  have h₁ : Real.pi/5 < capA aux a := by
    have hc := cos_gt_401_500 (t := Real.pi/5) (by rw [abs_of_pos (by positivity)])
    calc Real.pi/5=Real.arccos (Real.cos (Real.pi/5)) :=
          (Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])).symm
      _ < capA aux a := Real.arccos_lt_arccos (by rw [aux]; linarith) (by rw [aux]; linarith)
          (Real.cos_le_one _)
  have h₂ : 2*Real.pi/5 < capA aux a+capV aux b := by
    have hf := arcsin_sum (x := a-1/2) (y := b-1/2) (by linarith) (by linarith) (by linarith)
      (by linarith) (by nlinarith [h.2,Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)])
      (by linarith [h.1.1])
    rw [hA,hV]
    linarith
  have h₃ : 2*Real.pi/5 < capA aux a+capU aux b := by
    have hh := Real.arcsin_le_arcsin (show (a-1/2)/aux ≤ (b+1/2)/aux by rw [aux]; linarith)
    rw [hA,capU]
    linarith [Real.pi_pos]
  have h₄ : 2*Real.pi/5 < capU aux b+capV aux b := by
    by_cases htop : aux ≤ b+1/2
    · have hU : capU aux b=Real.pi/2 :=
        Real.arcsin_of_one_le ((le_div_iff₀ (by norm_num [aux])).mpr (by linarith))
      linarith [Real.arccos_le_pi_div_two.mpr (show 0 ≤ (a-1/2)/aux by rw [aux]; linarith),
        show capA aux a ≤ Real.pi/2 from Real.arccos_le_pi_div_two.mpr
          (show 0 ≤ (a-1/2)/aux by rw [aux]; linarith)]
    · rw [aux] at htop
      have hh := arcsin_sum_gt_of_sin_lt (u := (b+1/2)/aux) (v := (1/2-b)/aux)
        (by rw [aux]; constructor <;> linarith) (by rw [aux]; constructor <;> linarith)
        (show Real.pi/5 ∈ Icc (0:ℝ) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
        (by rw [aux]; linarith [sin_pi_fifth_lt_three_fifths])
      unfold capU capV
      linarith
  rcases min_cases (capA aux a) (capU aux b) with ⟨hu,-⟩ | ⟨hu,-⟩ <;>
    rcases min_cases (capA aux a) (capV aux b) with ⟨hv,-⟩ | ⟨hv,-⟩ <;> rw [hu,hv] <;> linarith

/-- An exterior square with its centre in `P5` holds an arc of the circle of
radius `5/6` longer than 72 degrees. -/
theorem exterior_arc (S : UnitSquare) (o : Point)
    (h : P5 (alpha S o) (beta S o)) (hout : ¬ openSquare S o) :
    ∃ A : OpenArc o aux {p | openSquare S p}, Real.pi/5 < A.halfWidth := by
  obtain ⟨C,hsort⟩ := sorted_square_chart S o
  have hC := C.transfer P5 p5_swap h
  have ha := C.exterior hsort hout
  have hlen := arc_length ha C.nonneg.2 hsort hC
  obtain ⟨A,hA,-⟩ := C.edge_arc (r := aux) (by norm_num [aux]) ha
    (by rw [aux]; linarith [hC.1.1,C.nonneg.2]) (by rw [aux]; linarith)
    (by linarith [Real.pi_pos])
  exact ⟨A,by rw [hA]; linarith⟩

end SquaresInCircles.Five
