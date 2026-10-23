module

public import SquaresInCircles.Eight.Arithmetic.Arctangent
public import SquaresInCircles.Eight.BoundaryGeometry
public import SquaresInCircles.Eight.Frames

/-!
# The whole core/core pair inequality from center separation

Every core-boundary center has radius less than `4/5`. Disjoint unit
squares have center distance at least one, so their positive angular gap
exceeds `4/3`. A uniform bound on the same core marker used in the four-type
proof then gives the desired pair cost, for all signs and all separating
axes at once. There is no angular subdivision or real-box decision here.

The corner-marker estimate uses a tangent to arctangent and the core
circle equation; no derivative of a radical at a chart endpoint is needed.
Only two fixed arctangent endpoint enclosures are evaluated symbolically.
This Lean source remains uncompiled.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.CorePairGeometry

def K : ℝ := 7506931/1000000
def g : ℝ := 269343/250000
def label (a b : ℝ) : ℝ := K*(7/12-a)+g*b
def marker (a b : ℝ) : ℝ := Real.arctan (b/a)-label a b

/-- Both closed core charts, with the canonical order retained. -/
def CoreState (a b : ℝ) : Prop :=
  (a=7/12 ∧ 0 ≤ b ∧ b ≤ 1/2) ∨
  (1/2 ≤ b ∧ b ≤ a ∧ (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2)

/-- Concavity of arctangent expressed as its tangent-line majorant.
The proof uses monotonicity of its derivative on the nonnegative axis. -/
theorem arctan_tangent {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    Real.arctan x ≤ Real.arctan t+(x-t)/(1+t^2) := by
  let f : ℝ → ℝ := fun y => Real.arctan y-(1/(1+t^2))*y
  let d : ℝ → ℝ := fun y => 1/(1+y^2)-1/(1+t^2)
  have hd (y : ℝ) : HasDerivAt f (d y) y := by
    convert (Real.hasDerivAt_arctan y).sub
      ((hasDerivAt_id y).const_mul (1/(1+t^2))) using 1 <;>
      dsimp [f,d] <;> ring
  have hleft (y : ℝ) (hy : y ∈ Icc 0 t) : 0 ≤ d y := by
    dsimp [d]
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by positivity : 0<1+t^2)
      (by positivity : 0<1+y^2)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hy.2) (by linarith : 0 ≤ t+y)]
  have hright (y : ℝ) (hy : y ∈ Icc t (max x t)) : d y ≤ 0 := by
    dsimp [d]
    apply sub_nonpos.mpr
    apply (div_le_div_iff₀ (by positivity : 0<1+y^2)
      (by positivity : 0<1+t^2)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hy.1) (by linarith : 0 ≤ y+t)]
  have hh := le_at_peak (l := 0) (c := t) (u := max x t) (x := x)
    ⟨ht,le_max_right x t⟩ ⟨hx,le_max_left x t⟩
    (show Continuous f by dsimp [f]; fun_prop) hd hleft hright
  dsimp [f] at hh
  have he : (x-t)/(1+t^2)=(1/(1+t^2))*x-(1/(1+t^2))*t := by ring
  rw [he]
  linarith

theorem arctan_lower_three {x : ℝ} (hx : 0 ≤ x) :
    x-x^3/3 ≤ Real.arctan x := by
  have hd (y : ℝ) :
      HasDerivAt (fun z : ℝ => Real.arctan z-(z-z^3/3))
        (y^4/(1+y^2)) y := by
    convert (Real.hasDerivAt_arctan y).sub
      ((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 3).div_const 3)) using 1
    field_simp [ne_of_gt (show (0:ℝ)<1+y^2 by positivity)]
    ring
  have hh := nonneg_of_deriv_nonneg
    (fun z : ℝ => Real.arctan z-(z-z^3/3)) (by fun_prop) (by norm_num)
    (fun y _ => by rw [(hd y).deriv]; positivity) hx
  linarith

theorem arctan_three_quarters : Real.arctan (3/4:ℝ)<161/250 := by
  have h := Arithmetic.arctan_le_atanUpper (x := (3/4:ℝ)) (by norm_num)
  norm_num [Arithmetic.atanUpper] at h
  linarith

theorem arctan_six_sevenths : (2/3:ℝ)<Real.arctan (6/7:ℝ) := by
  have h := Arithmetic.atanLower_le (x := (6/7:ℝ)) (by norm_num)
  norm_num [Arithmetic.atanLower] at h
  linarith

/-- One tangent at `3/4` bounds the full core side, including its endpoints. -/
theorem side_marker {b : ℝ} (hb : 0 ≤ b ∧ b ≤ 1/2) :
    0 ≤ Real.arctan (b/(7/12:ℝ))-g*b ∧
      Real.arctan (b/(7/12:ℝ))-g*b<7/40 := by
  let x : ℝ := 12*b/7
  have hx : 0 ≤ x ∧ x ≤ 6/7 := by dsimp [x]; constructor <;> linarith [hb.1,hb.2]
  have he : b/(7/12:ℝ)=x := by dsimp [x]; ring
  have hb' : b=(7/12)*x := by dsimp [x]; ring
  have hl := arctan_lower_three hx.1
  have hu := arctan_tangent hx.1 (show (0:ℝ) ≤ 3/4 by norm_num)
  have hp := arctan_three_quarters
  norm_num at hu
  have hsq : x^2 ≤ (6/7:ℝ)^2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hcube := mul_le_mul_of_nonneg_right hsq hx.1
  rw [he,hb']
  dsimp [g]
  constructor <;> nlinarith [hx.1,hx.2]

/-- The circle equation supplies both the radial loss and a linear chord
bound, uniformly on the closed corner arc. -/
theorem corner_geometry {a b : ℝ}
    (hb : 1/2 ≤ b) (hab : b ≤ a)
    (hc : (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2) :
    67/120<a ∧ a ≤ 7/12 ∧
      7/12-a ≤ (b-1/2)/2 ∧ 6*(b-1/2)^2 ≤ 7/12-a := by
  have hd : 0 ≤ b-1/2 := by linarith
  have he : 0 ≤ a-1/2 := by linarith
  have hde : b-1/2 ≤ a-1/2 := by linarith
  have hsq := pow_le_pow_left₀ hd hde 2
  have hal : 67/120<a := by
    by_contra! hbad
    have heU : a-1/2 ≤ 7/120 := by linarith
    have heSq := pow_le_pow_left₀ he heU 2
    nlinarith
  have hau : a ≤ 7/12 := by
    by_contra! hbad
    have hp := mul_pos (by linarith : 0<a-7/12)
      (by linarith : 0<(a-1/2)+1/12)
    nlinarith [sq_nonneg (b-1/2)]
  refine ⟨hal,hau,?_,?_⟩
  · have hp := mul_nonneg (sub_nonneg.mpr hab) hd
    by_contra! hbad
    have hprod := mul_pos
      (by linarith : 0<1/12-((a-1/2)+(b-1/2)/2))
      (by linarith : 0<1/12+((a-1/2)+(b-1/2)/2))
    nlinarith [sq_nonneg (b-1/2)]
  · nlinarith [sq_nonneg (a-7/12)]

theorem corner_marker {a b : ℝ}
    (hb : 1/2 ≤ b) (hab : b ≤ a)
    (hc : (a-1/2)^2+(b-1/2)^2=(1/12:ℝ)^2) :
    -(9/50:ℝ)<marker a b ∧ marker a b<9/50 := by
  obtain ⟨hal,hau,hlossU,hlossL⟩ := corner_geometry hb hab hc
  have ha : 0<a := by linarith
  have hd : 0 ≤ b-1/2 := by linarith
  have hx : 0 ≤ b/a := div_nonneg (by linarith) ha.le
  have hxL : (6/7:ℝ) ≤ b/a := (le_div_iff₀ ha).mpr (by linarith)
  have ht := arctan_tangent hx (show (0:ℝ) ≤ 6/7 by norm_num)
  norm_num at ht
  have hratio : (49/85:ℝ)*(b/a-6/7) ≤ (9/5)*(b-1/2) := by
    have hmul := mul_nonneg (by linarith : 0 ≤ a-5/9) hd
    have hdiv : (b/a)*a=b := div_mul_cancel₀ b (ne_of_gt ha)
    apply (mul_le_mul_iff_of_pos_right ha).mp
    nlinarith
  have hside := (side_marker (b := (1/2:ℝ)) (by norm_num)).2
  norm_num at hside
  have hquad : (9/5-g)*(b-1/2)-6*K*(b-1/2)^2<1/300 := by
    have hs := sq_nonneg (84*(b-1/2)-(9/5-g))
    dsimp [K,g] at hs ⊢
    nlinarith [sq_nonneg (b-1/2)]
  have hlabelL := mul_le_mul_of_nonneg_left hlossL (show 0 ≤ K by norm_num [K])
  have hlabelU : label a b<977/1200 := by
    have hgd := mul_nonneg (show 0 ≤ g by norm_num [g]) (sub_nonneg.mpr hab)
    have hke := mul_pos (show 0<K-g by norm_num [K,g])
      (show 0<a-67/120 by linarith)
    dsimp [label,K,g] at hgd hke ⊢
    linarith
  have hangleL := lt_of_lt_of_le arctan_six_sevenths (Real.arctan_le_arctan hxL)
  constructor
  · dsimp [marker]
    linarith
  · dsimp [marker,label,K,g] at ⊢
    dsimp [K,g] at hlabelL hquad hside
    nlinarith

theorem marker_mem {a b : ℝ} (h : CoreState a b) :
    -(9/50:ℝ)<marker a b ∧ marker a b<9/50 := by
  rcases h with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
  · have hh := side_marker ⟨hb,hbu⟩
    dsimp [marker,label]
    constructor <;> linarith [hh.1,hh.2]
  · exact corner_marker hb hab hcircle

/-- The coarse radius bound uses only the core circle and canonical order. -/
theorem core_radius_sq {a b : ℝ} (h : CoreState a b) : a^2+b^2<16/25 := by
  rcases h with ⟨rfl,hb,hbu⟩ | ⟨hb,hab,hcircle⟩
  · have hs := pow_le_pow_left₀ hb hbu 2
    nlinarith
  · have he : 0 ≤ a-1/2 := by linarith
    have hd : 0 ≤ b-1/2 := by linarith
    have hsum : a+b-1<3/25 := by
      by_contra! hbad
      have hp := mul_nonneg (by linarith : 0≤a+b-1-3/25)
        (by linarith : 0≤a+b-1+3/25)
      nlinarith [sq_nonneg (a-b)]
    nlinarith

theorem boundary_core_state {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hk : C.kind i ≠ .outer) : CoreState (C.a i) (C.b i) := by
  have hb := C.boundary i
  cases he : C.kind i with
  | outer => exact False.elim (hk he)
  | coreSide =>
      have hh : C.a i=7/12 ∧ C.b i ≤ 1/2 := by simpa [BoundaryState,he] using hb
      exact Or.inl ⟨hh.1,C.b_nonneg i,hh.2⟩
  | coreCorner =>
      have hh : 1/2 ≤ C.b i ∧
          (C.a i-1/2)^2+(C.b i-1/2)^2=(1/12:ℝ)^2 := by
        simpa [BoundaryState,he] using hb
      exact Or.inr ⟨hh.1,C.b_le_a i,hh.2⟩

theorem boundary_core_radius {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hk : C.kind i ≠ .outer) : C.radius i<4/5 := by
  have h := core_radius_sq (boundary_core_state C i hk)
  by_contra! hbad
  have hsq := pow_le_pow_left₀ (show (0:ℝ) ≤ 4/5 by norm_num) hbad 2
  nlinarith [C.radius_sq i]

/-- An elementary two-variable bound on the square of the chord. -/
theorem chord_upper {r s : ℝ} (hr : 0 ≤ r ∧ r ≤ 4/5)
    (hs : 0 ≤ s ∧ s ≤ 4/5) : r^2+s^2-(7/16)*r*s ≤ 1 := by
  have hr₂ := mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  have hs₂ := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  have hrs := mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hs.2)
  nlinarith [hr.2,hs.2]

/-- A positive core/core gap exceeds `4/3`, regardless of the separating axis. -/
theorem core_gap {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hi : C.kind i ≠ .outer) (hj : C.kind (next i) ≠ .outer) :
    (4/3:ℝ)<angleGap C.beta i := by
  have hr := boundary_core_radius C i hi
  have hs := boundary_core_radius C (next i) hj
  have hr0 := C.radius_pos i
  have hs0 := C.radius_pos (next i)
  have hd := centers_distance_sq_ge_one (C.square i) (C.square (next i))
    (C.feasible i).disjoint
  rw [polar_pair_distance (C.center_cos i) (C.center_sin i)
    (C.center_cos (next i)) (C.center_sin (next i))] at hd
  have hcos : Real.cos (angleGap C.beta i)=Real.cos (C.beta (next i)-C.beta i) := by
    by_cases hlast : i=6 <;> simp [angleGap,hlast,Real.cos_add_two_pi]
  rw [← hcos] at hd
  change 1 ≤ C.radius i^2+C.radius (next i)^2-
    2*C.radius i*C.radius (next i)*Real.cos (angleGap C.beta i) at hd
  have hmax := chord_upper ⟨hr0.le,hr.le⟩ ⟨hs0.le,hs.le⟩
  have hfour : (7/32:ℝ)<Real.cos (4/3:ℝ) := by
    have hh := cos_lower_six (x := (4/3:ℝ)) (by norm_num)
    norm_num at hh
    linarith
  by_contra! hbad
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi (C.gap_pos i).le
    (by linarith [Real.pi_gt_three] : (4/3:ℝ) ≤ Real.pi) hbad
  have hp := mul_pos (mul_pos hr0 hs0)
    (sub_pos.mpr (lt_of_lt_of_le hfour hm))
  nlinarith

/-- Cauchy on the sine and cosine gives a uniform width charge. -/
theorem charge_upper (φ : ℝ) : periodicFrameCost φ<21/100 := by
  have hu := Real.sin_sq_add_cos_sq φ
  have hc := abs_nonneg (Real.cos φ)
  have hs := abs_nonneg (Real.sin φ)
  have hd := sq_nonneg (|Real.cos φ|-|Real.sin φ|)
  dsimp [periodicFrameCost]
  nlinarith [sq_abs (Real.cos φ),sq_abs (Real.sin φ)]

theorem boundary_marker_mem {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hk : C.kind i ≠ .outer) :
    -(9/50:ℝ)<C.alpha i-C.sigma i*label (C.a i) (C.b i) ∧
      C.alpha i-C.sigma i*label (C.a i) (C.b i)<9/50 := by
  have h := marker_mem (boundary_core_state C i hk)
  dsimp [marker] at h
  rcases C.sigma_sign i with hσ | hσ <;>
    simp only [BoundaryCycle.alpha,BoundaryCycle.tangent,hσ,
      neg_one_mul,one_mul,neg_div,Real.arctan_neg] <;>
    constructor <;> linarith [h.1,h.2]

/-- The full continuous core/core pair theorem with its strict reserve.
The marker at a vertex is fixed independently of either incident edge. -/
theorem core_pair_cost {q : ℝ} (C : BoundaryCycle q) (i : Vertex)
    (hi : C.kind i ≠ .outer) (hj : C.kind (next i) ≠ .outer) (φ : ℝ) :
    (14033/15000:ℝ)<angleGap C.beta i-(9/50)*periodicFrameCost φ+
      (C.alpha (next i)-C.sigma (next i)*label (C.a (next i)) (C.b (next i)))-
      (C.alpha i-C.sigma i*label (C.a i) (C.b i)) := by
  have hg := core_gap C i hi hj
  have hcharge := charge_upper φ
  have hmi := boundary_marker_mem C i hi
  have hmj := boundary_marker_mem C (next i) hj
  linarith [hmi.2,hmj.1]

end SquaresInCircles.Eight.CorePairGeometry
