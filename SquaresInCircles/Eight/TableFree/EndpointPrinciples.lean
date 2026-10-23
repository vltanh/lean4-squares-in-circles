module

public import SquaresInCircles.Eight.TableFree.CircleGeometry

/-!
# Endpoint principles for continuous geometric transports

Uncompiled draft. The statements quantify whole intervals. Their endpoints
are intrinsic contacts, alignments or circle/core junctions, never a mesh.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree

/-- Derivative lower bounds retain an explicit displacement reserve. -/
theorem derivative_reserve {f df : ℝ → ℝ} {l u x y k : ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ z ∈ Ioo l u, HasDerivAt f (df z) z)
    (hk : ∀ z ∈ Ioo l u, k ≤ df z)
    (hx : x ∈ Icc l u) (hy : y ∈ Icc l u) (hxy : x ≤ y) :
    k*(y-x) ≤ f y-f x := by
  have hm : MonotoneOn (fun z => f z-k*z) (Icc l u) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact hc.sub (continuous_const.mul continuous_id).continuousOn
    · intro z hz
      exact (hd z hz).sub ((hasDerivAt_id z).const_mul k)
    · intro z hz
      exact sub_nonneg.mpr (hk z hz)
  have h := hm hx hy hxy
  linarith

theorem strict_increase_of_reserve {f df : ℝ → ℝ} {l u k : ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ z ∈ Ioo l u, HasDerivAt f (df z) z)
    (hk0 : 0 < k) (hk : ∀ z ∈ Ioo l u, k ≤ df z) :
    StrictMonoOn f (Icc l u) := by
  intro x hx y hy hxy
  have h := derivative_reserve hc hd hk hx hy hxy.le
  have hp := mul_pos hk0 (sub_pos.mpr hxy)
  linarith

/-- Strong concavity gives a positive reserve over the smaller endpoint. -/
theorem concave_endpoint_reserve {f : ℝ → ℝ} {l u x k : ℝ}
    (hk : 0 ≤ k) (hx : x ∈ Icc l u)
    (hg : ConcaveOn ℝ (Icc l u) (fun z => f z+k/2*z^2)) :
    min (f l) (f u)+k/2*(x-l)*(u-x) ≤ f x := by
  by_cases hlu : l=u
  · have hxl : x=l := by linarith [hx.1,hx.2]
    simp [hlu,hxl]
  have hgap : 0 < u-l := by linarith [hx.1,hx.2]
  let t : ℝ := (x-l)/(u-l)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) hgap.le
  have ht1 : t ≤ 1 := (div_le_one hgap).mpr (by linarith [hx.2])
  have hid : (1-t)*l+t*u=x := by dsimp [t]; field_simp; ring
  have hh := hg.2 (left_mem_Icc.mpr (by linarith))
    (right_mem_Icc.mpr (by linarith)) (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul,hid] at hh
  have hminL := mul_le_mul_of_nonneg_left (min_le_left (f l) (f u))
    (sub_nonneg.mpr ht1)
  have hminU := mul_le_mul_of_nonneg_left (min_le_right (f l) (f u)) ht0
  have hvar : (1-t)*l^2+t*u^2-x^2=(x-l)*(u-x) := by
    dsimp [t]
    field_simp
    ring
  have hmul := congrArg (fun r : ℝ => k/2*r) hvar
  nlinarith

/-- Curvature on the entire interval, rather than endpoint sampling. -/
theorem strict_endpoint_of_second_derivative {f df ddf : ℝ → ℝ}
    {l u x k : ℝ} (hk : 0 < k) (hx : x ∈ Ioo l u)
    (hd : ∀ z ∈ Icc l u, HasDerivAt f (df z) z)
    (hdd : ∀ z ∈ Icc l u, HasDerivAt df (ddf z) z)
    (hcurv : ∀ z ∈ Icc l u, ddf z ≤ -k) :
    f l < f x ∨ f u < f x := by
  have hg : ConcaveOn ℝ (Icc l u) (fun z => f z+k/2*z^2) := by
    apply concave_of_deriv2
      (f' := fun z => df z+k*z) (f'' := fun z => ddf z+k)
    · intro z hz
      convert (hd z hz).add (((hasDerivAt_id z).pow 2).const_mul (k/2)) using 1 <;> ring
    · intro z hz
      convert (hdd z hz).add ((hasDerivAt_id z).const_mul k) using 1 <;> ring
    · intro z hz
      linarith [hcurv z hz]
  have h := concave_endpoint_reserve hk.le (Ioo_subset_Icc_self hx) hg
  have hpos : 0 < k/2*(x-l)*(u-x) := by
    exact mul_pos (mul_pos (div_pos hk (by norm_num)) (sub_pos.mpr hx.1))
      (sub_pos.mpr hx.2)
  have hm : min (f l) (f u)<f x := by linarith
  exact (min_lt_iff).mp hm

/-- An infeasible endpoint is discarded only after the complete endpoint
alternative has been proved. This includes equality at an intrinsic junction. -/
theorem choose_feasible_endpoint {f : ℝ → ℝ} {l u x bound : ℝ}
    (h : f l < f x ∨ f u < f x) (hx : f x ≤ bound)
    (hu : bound < f u) : f l < bound := by
  rcases h with h | h
  · exact h.trans_le hx
  · exact False.elim (not_lt_of_ge hx (hu.trans h))

/-- Width preserving affine motion: one contact stays exact and the opposite
projection improves at the rate displayed in the paired-primary proof. -/
theorem primary_affine_projection_identities (a y A B u v λ : ℝ)
    (hu : Real.cos u ≠ 0) :
    A+(a+λ)*Real.sin u-(y+λ*Real.tan u)*Real.cos u=
        A+a*Real.sin u-y*Real.cos u ∧
      (a+λ)*Real.sin v+(y+λ*Real.tan u)*Real.cos v+B=
        a*Real.sin v+y*Real.cos v+B+λ*Real.sin (u+v)/Real.cos u := by
  rw [Real.tan_eq_sin_div_cos]
  constructor <;> field_simp [hu] <;>
    simp only [Real.sin_add] <;> ring

/-- Two corner coordinates rotated on their own actual q-circle. -/
theorem contact_rotation_norm {q X Z u : ℝ} (h : X^2+Z^2=q) :
    (X*Real.cos u+Z*Real.sin u)^2+
      (-X*Real.sin u+Z*Real.cos u)^2=q := by
  have hid := circle_rotation_identity X (-Z) u
  nlinarith [Real.sin_sq_add_cos_sq u]

end SquaresInCircles.Eight.TableFree