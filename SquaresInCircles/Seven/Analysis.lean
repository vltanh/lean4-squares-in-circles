import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# One-variable estimates

The analytic tools of the sector analysis: monotonicity and concavity from
derivatives, positivity from a curvature bound and one value, Taylor bounds of
`sin` and `cos` on `[0, ∞)`, and positivity of a polynomial from its
coefficients in a Bernstein basis.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma monoOn_of_hasDeriv_nonneg {l u : ℝ} {f d : ℝ → ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ x ∈ Ioo l u, HasDerivAt f (d x) x)
    (hs : ∀ x ∈ Ioo l u, 0 ≤ d x) : MonotoneOn f (Icc l u) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l u) hc
    (by simpa only [interior_Icc] using fun x hx => (hd x hx).hasDerivWithinAt)
    (by simpa only [interior_Icc] using hs)

lemma antiOn_of_hasDeriv_nonpos {l u : ℝ} {f d : ℝ → ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ x ∈ Ioo l u, HasDerivAt f (d x) x)
    (hs : ∀ x ∈ Ioo l u, d x ≤ 0) : AntitoneOn f (Icc l u) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l u) hc
    (by simpa only [interior_Icc] using fun x hx => (hd x hx).hasDerivWithinAt)
    (by simpa only [interior_Icc] using hs)

/-- A function on `[l, u]` with second derivative at least `κ` lies above its
tangent parabola of curvature `κ` at any point. -/
lemma curvature_tangent {l u x t κ : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (ht : t ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, κ ≤ dd y) : f t+d t*(x-t)+κ/2*(x-t)^2 ≤ f x := by
  let g : ℝ → ℝ := fun y => f y-κ/2*y^2
  have hg (y : ℝ) (hy : y ∈ Icc l u) : HasDerivAt g (d y-κ*y) y := by
    convert (hd y hy).sub (((hasDerivAt_id y).pow 2).const_mul (κ/2)) using 1
    · rfl
    · dsimp; ring
  have hc : ConvexOn ℝ (Icc l u) g := convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc l u)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hg y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => ((hdd y (interior_subset hy)).sub
      ((hasDerivAt_id y).const_mul κ)).hasDerivWithinAt)
    (fun y hy => by linarith [hm y (interior_subset hy)])
  have htan : g t+(d t-κ*t)*(x-t) ≤ g x := by
    rcases lt_trichotomy t x with h | rfl | h
    · have hs := hc.le_slope_of_hasDerivAt ht hx h (hg t ht)
      rw [slope_def_field,le_div_iff₀ (sub_pos.2 h)] at hs
      linarith
    · simp
    · have hs := hc.slope_le_of_hasDerivAt hx ht h (hg t ht)
      rw [slope_def_field,div_le_iff₀ (sub_pos.2 h)] at hs
      linarith
  dsimp [g] at htan
  linarith

/-- A function on `[l, u]` with second derivative at least `κ > 0` is positive
if at one point its slope `d` and value `f` satisfy `d² < 2κf`. -/
lemma positive_of_curvature {l u x t κ : ℝ} {f d dd : ℝ → ℝ} (hκ : 0 < κ)
    (hx : x ∈ Icc l u) (ht : t ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, κ ≤ dd y) (hval : d t^2 < 2*κ*f t) : 0 < f x := by
  nlinarith [curvature_tangent hx ht hd hdd hm,sq_nonneg (κ*(x-t)+d t)]

/-- A function on `[l, u]` with nonpositive second derivative is positive if it
is positive at both ends. -/
lemma positive_of_second_nonpos {l u x : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (hf : ContinuousOn f (Icc l u))
    (hdf : ContinuousOn d (Icc l u))
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, dd y ≤ 0)
    (hl : 0 < f l) (hu : 0 < f u) : 0 < f x := by
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l u) hdf
    (fun y hy => (hdd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => hm y (interior_subset hy))
  have hconc : ConcaveOn ℝ (Icc l u) f := AntitoneOn.concaveOn_of_deriv (convex_Icc l u) hf
    (fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    (fun a ha b hb hab => by
      rw [(hd a (interior_subset ha)).deriv,(hd b (interior_subset hb)).deriv]
      exact hanti (interior_subset ha) (interior_subset hb) hab)
  exact (lt_min hl hu).trans_le (hconc.min_le_of_mem_Icc
    (left_mem_Icc.mpr (hx.1.trans hx.2)) (right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

/-- `αx + A sin x + B cos x` with `A, B ≥ 0` is concave on `[0, π/2]`, so on an
interval there it exceeds any bound that it exceeds at both ends. -/
lemma trig_concave_gt {α A B m l u x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hl : 0 ≤ l) (hu : u ≤ Real.pi/2) (hx : l ≤ x ∧ x ≤ u)
    (hml : m < α*l+A*Real.sin l+B*Real.cos l) (hmu : m < α*u+A*Real.sin u+B*Real.cos u) :
    m < α*x+A*Real.sin x+B*Real.cos x := by
  have hs : Icc l u ⊆ Icc 0 Real.pi := Icc_subset_Icc hl (by linarith [Real.pi_pos])
  have hc : Icc l u ⊆ Icc (-(Real.pi/2)) (Real.pi/2) :=
    Icc_subset_Icc (by linarith [Real.pi_pos]) hu
  have hlin : ConcaveOn ℝ (Icc l u) fun x => α*x :=
    ⟨convex_Icc l u,fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; ring_nf; rfl⟩
  have hf : ConcaveOn ℝ (Icc l u) fun x => α*x+A*Real.sin x+B*Real.cos x :=
    (hlin.add ((strictConcaveOn_sin_Icc.concaveOn.subset hs (convex_Icc l u)).smul hA)).add
      ((strictConcaveOn_cos_Icc.concaveOn.subset hc (convex_Icc l u)).smul hB)
  exact (lt_min hml hmu).trans_le (hf.min_le_of_mem_Icc
    (left_mem_Icc.mpr (hx.1.trans hx.2)) (right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

lemma sin_le_cos_of_small {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/4) : Real.sin x ≤ Real.cos x := by
  rw [← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos]) (by linarith)

lemma cos_le_sin_of_quarter {x : ℝ} (hx : Real.pi/4 ≤ x ∧ x ≤ Real.pi/2) :
    Real.cos x ≤ Real.sin x := by
  rw [← Real.cos_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) (by linarith)

lemma cos_ge_half {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) : (1/2 : ℝ) ≤ Real.cos z := by
  simpa only [Real.cos_pi_div_three] using
    Real.cos_le_cos_of_nonneg_of_le_pi hz.1 (by linarith [Real.pi_pos]) hz.2

/-- A function that vanishes at `0` and has a nonnegative derivative on `[0, ∞)`
is nonnegative there. -/
lemma nonneg_of_deriv_nonneg (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hzero : f 0 = 0) (hder : ∀ x, 0 ≤ x → 0 ≤ deriv f x)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x :=
  hzero ▸ monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuous.continuousOn
    hf.differentiableOn (fun t ht => hder t (interior_subset ht)) self_mem_Ici hx hx

/-! Taylor polynomials of `sin` and `cos` of degrees 4 to 7 bound them on
`[0, ∞)`: each remainder has the derivative of the previous one. -/

lemma cos_upper_four {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1-x^2/2+x^4/24 := by
  have h := nonneg_of_deriv_nonneg (fun t => 1-t^2/2+t^4/24-Real.cos t) (by fun_prop)
    (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [Real.sin_ge_sub_cube ht]) hx
  linarith

lemma sin_upper_five {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x-x^3/6+x^5/120 := by
  have h := nonneg_of_deriv_nonneg (fun t => t-t^3/6+t^5/120-Real.sin t) (by fun_prop)
    (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [cos_upper_four ht]) hx
  linarith

lemma cos_lower_six {x : ℝ} (hx : 0 ≤ x) : 1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.cos t-(1-t^2/2+t^4/24-t^6/720))
    (by fun_prop) (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [sin_upper_five ht]) hx
  linarith

lemma sin_lower_seven {x : ℝ} (hx : 0 ≤ x) : x-x^3/6+x^5/120-x^7/5040 ≤ Real.sin x := by
  have h := nonneg_of_deriv_nonneg (fun t => Real.sin t-(t-t^3/6+t^5/120-t^7/5040))
    (by fun_prop) (by norm_num) (fun t ht => by
      simp (disch := fun_prop)
      linarith [cos_lower_six ht]) hx
  linarith

lemma cos_sq_lower_six {x : ℝ} (hx : 0 ≤ x) :
    1-x^2+x^4/3-2*x^6/45 ≤ Real.cos x^2 := by
  have h := cos_lower_six (show 0 ≤ 2*x by linarith)
  rw [Real.cos_two_mul] at h
  linarith

/-- Polynomial brackets of `sin` and `cos` on an interval `[l, u] ⊆ [0, π/2]`. -/
lemma trig_bracket {l u x : ℝ} (hl : 0 ≤ l) (hu : u ≤ Real.pi/2) (hx : l ≤ x ∧ x ≤ u) :
    l-l^3/6+l^5/120-l^7/5040 ≤ Real.sin x ∧ Real.sin x ≤ u-u^3/6+u^5/120 ∧
    1-u^2/2+u^4/24-u^6/720 ≤ Real.cos x ∧ Real.cos x ≤ 1-l^2/2+l^4/24 := by
  have hx0 : 0 ≤ x := hl.trans hx.1
  have hu0 : 0 ≤ u := hx0.trans hx.2
  have hpi := Real.pi_pos
  exact ⟨(sin_lower_seven hl).trans (Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith) (hx.2.trans hu) hx.1),
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hu hx.2).trans (sin_upper_five hu0),
    (cos_lower_six hu0).trans (Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith) hx.2),
    (Real.cos_le_cos_of_nonneg_of_le_pi hl (by linarith) hx.1).trans (cos_upper_four hl)⟩

/-- The Bernstein basis polynomials of degree `n` on `[l, u]`, scaled by `(u - l)ⁿ`. -/
def bernstein (n : ℕ) (i : Fin (n+1)) (l u x : ℝ) : ℝ :=
  (n.choose i : ℝ)*(x-l)^(i : ℕ)*(u-x)^(n-i)

/-- A polynomial with positive coefficients in the Bernstein basis of `[l, u]` is
positive on `[l, u]`. -/
lemma bernstein_pos {n : ℕ} (c : Fin (n+1) → ℝ) (hc : ∀ i, 0 < c i) {p : ℝ → ℝ}
    {l u : ℝ} (hlu : l < u) (hp : ∀ x, p x*(u-l)^n = ∑ i, c i*bernstein n i l u x)
    {x : ℝ} (hx : l ≤ x ∧ x ≤ u) : 0 < p x := by
  have hnon (i : Fin (n+1)) : 0 ≤ c i*bernstein n i l u x := by
    have := sub_nonneg.mpr hx.1
    have := sub_nonneg.mpr hx.2
    have := (hc i).le
    unfold bernstein
    positivity
  have hsum : 0 < ∑ i, c i*bernstein n i l u x := by
    rcases eq_or_lt_of_le hx.2 with rfl | hxu
    · refine (mul_pos (hc (Fin.last n)) ?_).trans_le
        (Finset.single_le_sum (fun i _ => hnon i) (Finset.mem_univ _))
      simp only [bernstein,Fin.val_last,Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,
        pow_zero,mul_one]
      exact pow_pos (sub_pos.mpr hlu) n
    · refine (mul_pos (hc 0) ?_).trans_le
        (Finset.single_le_sum (fun i _ => hnon i) (Finset.mem_univ _))
      simp only [bernstein,Fin.val_zero,Nat.choose_zero_right,Nat.cast_one,one_mul,pow_zero,
        Nat.sub_zero]
      exact pow_pos (sub_pos.mpr hxu) n
  rw [← hp] at hsum
  exact pos_of_mul_pos_left hsum (pow_nonneg (sub_nonneg.mpr hlu.le) n)

end SquaresInCircles.Seven
