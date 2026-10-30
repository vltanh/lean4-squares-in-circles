module

public import SquaresInCircles.Eight.Candidate.Dual
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Eight squares: projection estimates for the owner and tilt tables

As a function of the relative angle `x`, the projection of the difference of two centres on a
forward axis is a sinusoid `c + u sin x + v cos x` (`projection`). These estimates concern the
centres of the cycle themselves, on either radial curve: containment bounds the amplitude of the
sinusoid by `3/2` (`projection_amplitude`), which gives a Lipschitz bound and second-order Taylor
bounds (`sinusoid_lipschitz`, `sinusoid_taylor`). The threshold `pairWidth` has a cusp at `0`,
which the linear and quadratic error estimates keep (`width_cusp_lower`, `width_semiconvex`). The
file ends with the half-angle chart `t = 2 arctan z` of the tilt (`half_angle_chart`,
`half_angle_terminal_window`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate

def sinusoid (c u v x : ℝ) : ℝ := c + u * Real.sin x + v * Real.cos x
def sinusoidDeriv (u v x : ℝ) : ℝ := u * Real.cos x - v * Real.sin x

theorem sinusoid_hasDeriv (c u v x : ℝ) :
    HasDerivAt (sinusoid c u v) (sinusoidDeriv u v x) x := by
  have hfun : sinusoid c u v = fun y => c + u * Real.sin y + v * Real.cos y := rfl
  rw [hfun]
  convert (((Real.hasDerivAt_sin x).const_mul u).const_add c).add
    ((Real.hasDerivAt_cos x).const_mul v) using 1
  simp only [sinusoidDeriv]
  ring

theorem sinusoidDeriv_hasDeriv (u v x : ℝ) :
    HasDerivAt (sinusoidDeriv u v) (-u * Real.sin x - v * Real.cos x) x := by
  have hfun : sinusoidDeriv u v = fun y => u * Real.cos y - v * Real.sin y := rfl
  rw [hfun]
  convert ((Real.hasDerivAt_cos x).const_mul u).sub
    ((Real.hasDerivAt_sin x).const_mul v) using 1
  ring

theorem harmonic_abs_le {u v M : ℝ} (hM : 0 ≤ M)
    (huv : u ^ 2 + v ^ 2 ≤ M ^ 2) (x : ℝ) :
    |u * Real.sin x + v * Real.cos x| ≤ M := by
  have hid : (u * Real.sin x + v * Real.cos x) ^ 2 +
      (u * Real.cos x - v * Real.sin x) ^ 2 = u ^ 2 + v ^ 2 := by
    linear_combination (u^2+v^2) * Real.sin_sq_add_cos_sq x
  have hsq := sq_nonneg (u * Real.cos x - v * Real.sin x)
  have habs := abs_nonneg (u * Real.sin x + v * Real.cos x)
  rw [← sq_abs (u * Real.sin x + v * Real.cos x)] at hid
  nlinarith only [huv, hid, hM]

theorem sinusoid_lipschitz {u v M : ℝ} (hM : 0 ≤ M)
    (huv : u ^ 2 + v ^ 2 ≤ M ^ 2) (c x y : ℝ) :
    |sinusoid c u v x - sinusoid c u v y| ≤ M * |x - y| := by
  have hchord : (Real.sin x - Real.sin y) ^ 2 +
      (Real.cos x - Real.cos y) ^ 2 ≤ (x - y) ^ 2 := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := x - y)
    rw [Real.cos_sub] at hc
    linarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y]
  have hcauchy :
      (u * (Real.sin x - Real.sin y) + v * (Real.cos x - Real.cos y)) ^ 2 ≤
      (u ^ 2 + v ^ 2) * ((Real.sin x - Real.sin y) ^ 2 + (Real.cos x - Real.cos y) ^ 2) := by
    linarith [sq_nonneg (u * (Real.cos x - Real.cos y) - v * (Real.sin x - Real.sin y))]
  have hprod := mul_le_mul huv hchord (by positivity :
      0 ≤ (Real.sin x - Real.sin y) ^ 2 + (Real.cos x - Real.cos y) ^ 2) (sq_nonneg M)
  have he : sinusoid c u v x - sinusoid c u v y =
      u * (Real.sin x - Real.sin y) + v * (Real.cos x - Real.cos y) := by
    unfold sinusoid; ring
  rw [← he, ← sq_abs] at hcauchy
  have ha := abs_nonneg (sinusoid c u v x - sinusoid c u v y)
  have hb := mul_nonneg hM (abs_nonneg (x-y))
  nlinarith only [sq_abs (x-y), hcauchy, hprod, hb]

theorem sinusoid_taylor {u v M : ℝ} (hM : 0 ≤ M)
    (huv : u ^ 2 + v ^ 2 ≤ M ^ 2) (c x d : ℝ) :
    sinusoid c u v x + sinusoidDeriv u v x * d - M / 2 * d ^ 2 ≤ sinusoid c u v (x+d) ∧
    sinusoid c u v (x+d) ≤ sinusoid c u v x + sinusoidDeriv u v x * d + M / 2 * d ^ 2 := by
  have hx : x ∈ Icc (min x (x+d)) (max x (x+d)) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hy : x+d ∈ Icc (min x (x+d)) (max x (x+d)) := ⟨min_le_right _ _, le_max_right _ _⟩
  have hl := curvature_tangent (f := sinusoid c u v) (d := sinusoidDeriv u v)
    (dd := fun y => -u * Real.sin y - v * Real.cos y) (κ := -M) hy hx
    (fun y _ => sinusoid_hasDeriv c u v y) (fun y _ => sinusoidDeriv_hasDeriv u v y)
    (fun y _ => by have hh := (abs_le.mp (harmonic_abs_le hM huv y)).2; linarith)
  have hu := curvature_tangent (f := sinusoid (-c) (-u) (-v))
    (d := sinusoidDeriv (-u) (-v))
    (dd := fun y => u * Real.sin y + v * Real.cos y) (κ := -M) hy hx
    (fun y _ => sinusoid_hasDeriv _ _ _ y)
    (fun y _ => by simpa using sinusoidDeriv_hasDeriv (-u) (-v) y)
    (fun y _ => (abs_le.mp (harmonic_abs_le hM huv y)).1)
  constructor <;> dsimp [sinusoid, sinusoidDeriv] at * <;> linarith

theorem center_amplitude {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0) (i : Vertex) :
    (C.a i) ^ 2 + (C.b i) ^ 2 < (3 / 2 : ℝ) ^ 2 := by
  have hc := (canonical_containment C i).trans hq
  have ha := (C.a_pos i).le
  have hb := C.b_nonneg i
  dsimp [SquaresInCircles.phi, Q0] at hc
  by_contra! hn
  have hs : (3 / 2 : ℝ) ≤ C.a i + C.b i := by
    by_contra! hs
    have hh : (C.a i + C.b i) ^ 2 < (3 / 2 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (by positivity) (by norm_num)).2 hs
    linarith [mul_nonneg ha hb]
  linarith

def projectionCoefficients (a b A B σ τ : ℝ) (j : Fin 4) : Fin 3 → ℝ :=
  ![![σ*b, A, -τ*B], ![A, σ*b, -a], ![-τ*B, a, σ*b], ![a, -τ*B, -A]] j

def projection (a b A B σ τ : ℝ) (j : Fin 4) (x : ℝ) : ℝ :=
  sinusoid (projectionCoefficients a b A B σ τ j 0)
    (projectionCoefficients a b A B σ τ j 1) (projectionCoefficients a b A B σ τ j 2) x

def projectionDeriv (a b A B σ τ : ℝ) (j : Fin 4) (x : ℝ) : ℝ :=
  sinusoidDeriv (projectionCoefficients a b A B σ τ j 1)
    (projectionCoefficients a b A B σ τ j 2) x

theorem projection_margin (a b A B σ τ x : ℝ) (j : Fin 4) :
    projection a b A B σ τ j x = forwardMargin j a b A B σ τ x + pairWidth x := by
  fin_cases j <;> simp [projection, projectionCoefficients, sinusoid, forwardMargin] <;> ring

theorem projection_amplitude {q : ℝ} (C : BoundaryCycle q) (hq : q ≤ Q0)
    (i : Vertex) (j : Fin 4) :
    (projectionCoefficients (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (C.sigma i) (C.sigma (next i)) j 1) ^ 2 +
    (projectionCoefficients (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (C.sigma i) (C.sigma (next i)) j 2) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
  have hs := center_amplitude C hq i
  have ht := center_amplitude C hq (next i)
  rcases C.sigma_sign i with hi | hi <;>
    rcases C.sigma_sign (next i) with hj | hj <;>
    fin_cases j <;> simp [projectionCoefficients, hi, hj] <;> linarith

theorem width_one_le (x : ℝ) : 1 ≤ pairWidth x := by
  have hh := h_nonneg x
  dsimp [h, pairWidth] at *
  linarith

theorem width_abs_small {x : ℝ} (hx : |x| ≤ 3 / 4) :
    pairWidth x = 1 + hSmooth |x| := by
  have hcx : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc
    ⟨by have hh := (abs_le.mp hx).1; linarith [Real.pi_gt_three],
     by have hh := (abs_le.mp hx).2; linarith [Real.pi_gt_three]⟩
  have hsin : |Real.sin x| = Real.sin |x| := by
    rcases le_total 0 x with h | h
    · have hs := Real.sin_nonneg_of_nonneg_of_le_pi h
        (by have hh := (abs_le.mp hx).2; linarith [Real.pi_gt_three])
      simp [abs_of_nonneg h, abs_of_nonneg hs]
    · have hs := Real.sin_nonpos_of_nonpos_of_neg_pi_le h
        (by have hh := (abs_le.mp hx).1; linarith [Real.pi_gt_three])
      simp [abs_of_nonpos h, abs_of_nonpos hs]
  rw [pairWidth, hsin, abs_of_nonneg hcx]
  simp [hSmooth, Real.cos_abs]
  ring

theorem width_cusp_lower {d : ℝ} (hd : |d| ≤ 1 / 500) :
    1 + |d| / 2 - d ^ 2 / 4 - |d| ^ 3 / 12 ≤ pairWidth d := by
  have hs := Real.sin_ge_sub_cube (abs_nonneg d)
  have hc := Real.one_sub_sq_div_two_le_cos (x := |d|)
  rw [width_abs_small (by linarith)]
  dsimp [hSmooth]
  linarith [sq_abs d]

theorem hSmooth_lipschitz {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (3/4)) (hy : y ∈ Icc (0 : ℝ) (3/4)) :
    |hSmooth x - hSmooth y| ≤ (1/2 : ℝ) * |x-y| := by
  have hd (t : ℝ) : HasDerivAt hSmooth ((Real.cos t - Real.sin t)/2) t := by
    have hfun : hSmooth = fun y => (Real.sin y + Real.cos y - 1) / 2 := rfl
    rw [hfun]
    convert (((Real.hasDerivAt_sin t).add (Real.hasDerivAt_cos t)).sub_const 1).div_const 2
      using 1
  have hder (t : ℝ) (ht : t ∈ Ioo (0:ℝ) (3/4)) :
      0 ≤ (Real.cos t - Real.sin t)/2 ∧ (Real.cos t - Real.sin t)/2 ≤ 1/2 := by
    have hsc := sin_le_cos_of_small ⟨ht.1.le, by linarith [ht.2, Real.pi_gt_three]⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2, Real.pi_gt_three])
    have hc := Real.cos_le_one t
    constructor <;> linarith
  have hm := monoOn_of_hasDeriv_nonneg
    (show ContinuousOn hSmooth (Icc (0:ℝ) (3/4)) by unfold hSmooth; fun_prop)
    (fun t _ => hd t) (fun t ht => (hder t ht).1)
  have hM := monoOn_of_hasDeriv_nonneg
    (f := fun t => t/2-hSmooth t)
    (show ContinuousOn (fun t => t/2-hSmooth t) (Icc (0:ℝ) (3/4)) by unfold hSmooth; fun_prop)
    (fun t _ => ((hasDerivAt_id t).div_const 2).sub (hd t))
    (fun t ht => by have hh := (hder t ht).2; linarith)
  rcases le_total x y with hxy | hyx
  · have h₁ := hm hx hy hxy
    have h₂ := hM hx hy hxy
    rw [abs_of_nonpos (sub_nonpos.mpr h₁), abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  · have h₁ := hm hy hx hyx
    have h₂ := hM hy hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr h₁), abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith

theorem width_lipschitz_small {x y : ℝ} (hx : |x| ≤ 3/4) (hy : |y| ≤ 3/4) :
    |pairWidth x - pairWidth y| ≤ (1/2 : ℝ) * |x-y| := by
  rw [width_abs_small hx, width_abs_small hy]
  have hh := hSmooth_lipschitz ⟨abs_nonneg x,hx⟩ ⟨abs_nonneg y,hy⟩
  have hdist : |(|x|-|y|)| ≤ |x-y| := abs_abs_sub_abs_le_abs_sub x y
  simpa only [add_sub_add_left_eq_sub] using hh.trans
    (mul_le_mul_of_nonneg_left hdist (by norm_num))

def widthSlope (positive : Bool) (t : ℝ) : ℝ :=
  if positive then (Real.cos t - Real.sin t)/2 else -(Real.cos t + Real.sin t)/2

theorem width_semiconvex {t v : ℝ} {positive : Bool}
    (ht : |t| ≤ 7/10) (hv : |v| ≤ 1/500)
    (hsgn : if positive then 0 ≤ t else t ≤ 0) :
    pairWidth t + widthSlope positive t * v - (3/8 : ℝ)*v^2 ≤ pairWidth (t+v) := by
  let σ : ℝ := if positive then 1 else -1
  have hσ : σ=1 ∨ σ= -1 := by cases positive <;> simp [σ]
  have ht' : |t+v| ≤ 3/4 := (abs_add_le t v).trans (by linarith)
  have h₀ : pairWidth t = sinusoid (1/2) (σ/2) (1/2) t := by
    rw [width_abs_small (by linarith)]
    cases positive
    · have hneg : t ≤ 0 := by simpa using hsgn
      simp [σ, hSmooth, sinusoid, abs_of_nonpos hneg, Real.sin_neg]
      ring
    · have hpos : 0 ≤ t := by simpa using hsgn
      simp [σ, hSmooth, sinusoid, abs_of_nonneg hpos]
      ring
  have h₁ : sinusoid (1/2) (σ/2) (1/2) (t+v) ≤ pairWidth (t+v) := by
    have hc := Real.cos_nonneg_of_mem_Icc
      (show t+v ∈ Icc (-(Real.pi/2)) (Real.pi/2) by
        have hh := abs_le.mp ht'; constructor <;> linarith [Real.pi_gt_three])
    rw [pairWidth, abs_of_nonneg hc]
    rcases hσ with h | h <;> rw [h] <;> unfold sinusoid <;>
      linarith [le_abs_self (Real.sin (t+v)), neg_le_abs (Real.sin (t+v))]
  have hT := (sinusoid_taylor (M := 3/4) (by norm_num)
    (u := σ/2) (v := 1/2) (by rcases hσ with h | h <;> norm_num [h]) (1/2) t v).1
  have hd : sinusoidDeriv (σ/2) (1/2) t = widthSlope positive t := by
    cases positive <;> simp [σ, sinusoidDeriv, widthSlope] <;> ring
  rw [← h₀, hd] at hT
  linarith

theorem arctan_cubic_lower {x : ℝ} (hx : 0 ≤ x) : x - x^3/3 ≤ Real.arctan x := by
  have hm := nonneg_of_deriv_nonneg (fun t : ℝ => Real.arctan t-t+t^3/3)
    ((Real.differentiable_arctan.sub differentiable_id).add
      ((differentiable_id.pow 3).div_const 3)) (by norm_num)
    (fun t ht => by
      have hd : HasDerivAt (fun t : ℝ => Real.arctan t-t+t^3/3)
          (1/(1+t^2)-1+t^2) t := by
        convert ((Real.hasDerivAt_arctan t).sub (hasDerivAt_id' t)).add
          (((hasDerivAt_id' t).pow 3).div_const 3) using 1
        norm_num
      rw [hd.deriv]
      have hp : 0 < 1+t^2 := by positivity
      have hid : 1/(1+t^2)-1+t^2 = t^4/(1+t^2) := by
        field_simp [ne_of_gt hp]
        ring
      rw [hid]
      positivity) hx
  linarith

theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hm := nonneg_of_deriv_nonneg (fun t : ℝ => t-Real.arctan t)
    (differentiable_id.sub Real.differentiable_arctan) (by norm_num)
    (fun t ht => by
      have hd : HasDerivAt (fun t : ℝ => t - Real.arctan t) (1 - 1 / (1 + t ^ 2)) t :=
        (hasDerivAt_id' t).sub (Real.hasDerivAt_arctan t)
      rw [hd.deriv]
      have hp : 0 < 1+t^2 := by positivity
      have hh : 1/(1+t^2) ≤ (1:ℝ) := (div_le_one hp).2 (by nlinarith only [])
      linarith) hx
  linarith

theorem half_angle_chart {t : ℝ} (ht : |t| < 7/10) :
    ∃ z : ℝ, -(3/8 : ℝ) < z ∧ z < 3/8 ∧ t = 2*Real.arctan z := by
  have hl := arctan_cubic_lower (x := 3/8) (by norm_num)
  have hends : 2*Real.arctan (-(3/8 : ℝ)) < t ∧ t < 2*Real.arctan (3/8 : ℝ) := by
    rw [Real.arctan_neg]
    have h := abs_lt.mp ht
    constructor <;> norm_num at * <;> linarith
  have hc : ContinuousOn (fun z : ℝ => 2*Real.arctan z) (Icc (-(3/8:ℝ)) (3/8)) := by fun_prop
  obtain ⟨z,hz,he⟩ := intermediate_value_Icc (by norm_num : -(3/8:ℝ) ≤ 3/8) hc
    ⟨hends.1.le,hends.2.le⟩
  refine ⟨z, ?_, ?_, he.symm⟩
  · by_contra! h; have hz' : z = -(3/8 : ℝ) := le_antisymm h hz.1
    subst z; linarith
  · by_contra! h; have hz' : z = (3/8 : ℝ) := le_antisymm hz.2 h
    subst z; linarith

theorem half_angle_identities (z : ℝ) :
    Real.sin (2*Real.arctan z) = 2*z/(1+z^2) ∧
    Real.cos (2*Real.arctan z) = (1-z^2)/(1+z^2) := by
  have hp : 0 < 1+z^2 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hsn := ne_of_gt (Real.sqrt_pos.2 hp)
  constructor
  · rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    field_simp
    rw [hs]
  · rw [Real.cos_two_mul, Real.cos_arctan]
    field_simp
    rw [hs]
    ring

theorem half_angle_terminal_window {z t : ℝ} (hlo : 1001/20000 < z)
    (hhi : z < 2/25) (ht : t=2*Real.arctan z) : 1/10 < t ∧ t < 4/25 := by
  have hz : 0 ≤ z := by linarith
  have hatan := Real.arctan_strictMono hlo
  have hlow := arctan_cubic_lower (x := 1001/20000) (by norm_num)
  have hu := arctan_le_self hz
  norm_num at hlow
  rw [ht]
  constructor <;> linarith

end SquaresInCircles.Eight.Candidate
