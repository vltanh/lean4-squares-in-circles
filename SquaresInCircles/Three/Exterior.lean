import SquaresInCircles.Common.RectangleArcs

/-!
# Three squares: the contact tangents and the exterior caps

In a sorted chart, `b ≤ a`, the tangents to `phi = 425/256` at `(1/2, 5/16)`
and `(11/16, 0)`, the positions of the squares of the T, bound the centre of
every square. On the circle of radius `3/8` a square that does not contain the
disk centre then holds a cap of at least 120 degrees, with equality only at
those two positions: type A, `(11/16, 0)`, and type B, `(1/2, 5/16)`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Three

/-- The two sides of the contact 16-gon that bound sorted coordinates `b ≤ a`:
the tangents to `phi = 425/256` at `(1/2, 5/16)` and at `(11/16, 0)`. -/
def P3 (a b : ℝ) : Prop := 16*a+13*b ≤ 193/16 ∧ 19*a+8*b ≤ 209/16

/-- A square in the closed disk of radius `5√17/16` has its centre in `P3`. -/
lemma p3_of_phi {a b : ℝ} (h : phi a b ≤ 425/256) : P3 a b :=
  ⟨by linarith [tangent_le (u := 1/2) (v := 5/16) h (by norm_num [phi])],
    by linarith [tangent_le (u := 11/16) (v := 0) h (by norm_num [phi])]⟩

def aux : ℝ := 3/8

/-- The clipped cap is at least 120 degrees, with equality only at `u = 0`,
`v = 1/2`. -/
lemma truncated_gap {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hv : 1/2+(16/13)*u ≤ v) :
    2*Real.pi/3 ≤ Real.arccos u+Real.arcsin v ∧
      (Real.arccos u+Real.arcsin v ≤ 2*Real.pi/3 → u=0 ∧ v=1/2) := by
  have hA : Real.arcsin u ≤ Real.pi/6 :=
    (Real.arcsin_le_arcsin hu1).trans_eq (Real.arcsin_eq_of_sin_eq Real.sin_pi_div_six
      ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩)
  have hA0 := Real.arcsin_nonneg.mpr hu0
  have hsin : Real.sin (Real.arcsin u+Real.pi/6) ≤ 1/2+u := by
    rw [Real.sin_add,Real.sin_arcsin (by linarith) (by linarith),Real.sin_pi_div_six]
    have hp := mul_nonneg hu0 (sub_nonneg.mpr (Real.cos_le_one (Real.pi/6)))
    linarith [Real.cos_le_one (Real.arcsin u)]
  have hdom : Real.arcsin u+Real.pi/6 ∈ Ioc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  have hle := (Real.le_arcsin_iff_sin_le' (y := v) hdom).mpr (hsin.trans (by linarith))
  refine ⟨by rw [Real.arccos_eq_pi_div_two_sub_arcsin]; linarith,fun hbudget => ?_⟩
  rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hbudget
  have hu : u=0 := by
    refine le_antisymm (not_lt.mp fun hu' => ?_) hu0
    have hh := (Real.lt_arcsin_iff_sin_lt' ⟨hdom.1.le,by linarith [Real.pi_pos]⟩).mpr
      (hsin.trans_lt (show 1/2+u < v by linarith))
    linarith
  subst u
  have he : Real.arcsin v=Real.pi/6 := by
    simp only [Real.arcsin_zero] at hbudget hle
    linarith
  have hv1 := Real.sin_arcsin (x := v) (by linarith)
    (Real.arcsin_lt_pi_div_two.mp (by linarith [Real.pi_pos])).le
  rw [he,Real.sin_pi_div_six] at hv1
  exact ⟨rfl,hv1.symm⟩

/-- The cap angles on the circle of radius `3/8` of an exterior square with
centre in `P3`: `π/3 ≤ A ≤ π/2` and `2π/3 ≤ A + V`, where `A = π/3` only at type
A and `A + V = 2π/3` only at type B. -/
lemma cap_bounds {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b) (hp : P3 a b) :
    Real.pi/3 ≤ capA aux a ∧ capA aux a ≤ Real.pi/2 ∧ 2*Real.pi/3 ≤ capA aux a+capV aux b ∧
      (capA aux a ≤ Real.pi/3 → a=11/16 ∧ b=0) ∧
      (capA aux a+capV aux b ≤ 2*Real.pi/3 → a=1/2 ∧ b=5/16) := by
  have hu0 : 0 ≤ (a-1/2)/aux := by rw [aux]; linarith
  have hu1 : (a-1/2)/aux ≤ 1/2 := by rw [aux]; linarith [hp.2]
  have hv : 1/2+16/13*((a-1/2)/aux) ≤ (1/2-b)/aux := by rw [aux]; linarith [hp.1]
  have hthird : Real.arccos (1/2)=Real.pi/3 :=
    Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_three.symm
  have hA : Real.pi/3 ≤ capA aux a := hthird ▸ Real.arccos_le_arccos hu1
  obtain ⟨hgap,heq⟩ := truncated_gap hu0 hu1 hv
  refine ⟨hA,Real.arccos_le_pi_div_two.mpr hu0,hgap,fun h => ?_,fun h => ?_⟩
  · have hu := Real.cos_arccos (x := (a-1/2)/aux) (by linarith) (by linarith)
    rw [show Real.arccos ((a-1/2)/aux)=Real.pi/3 from le_antisymm h hA,Real.cos_pi_div_three,
      aux] at hu
    constructor <;> linarith [hp.2]
  · obtain ⟨hu,hv'⟩ := heq h
    rw [aux] at hu hv'
    constructor <;> linarith

/-- On the circle of radius `3/8` an exterior square with centre in `P3` holds
its cap, the chart angles from `-min A V` to `A`, of half-width at least `π/3`. -/
lemma exterior_cap {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3 C.a C.b) :
    ∃ W : OpenArc o aux {p | openSquare S p},
      W.halfWidth=(capA aux C.a+min (capA aux C.a) (capV aux C.b))/2 ∧
      W.center=chartAngle C.phase C.reversed ((capA aux C.a-min (capA aux C.a) (capV aux C.b))/2) ∧
      Real.pi/3 ≤ W.halfWidth := by
  obtain ⟨W,hw,hc⟩ := C.cap_arc (r := aux) (by norm_num [aux]) (by norm_num [aux]) ha
    (by rw [aux]; linarith [hp.2,C.nonneg.2]) (by linarith [hp.1,C.nonneg.2])
  obtain ⟨h₁,-,h₂,-⟩ := cap_bounds ha C.nonneg.2 hp
  refine ⟨W,hw,hc,?_⟩
  rw [hw]
  rcases min_cases (capA aux C.a) (capV aux C.b) with ⟨h,-⟩ | ⟨h,-⟩ <;> rw [h] <;> linarith

end SquaresInCircles.Three
