module

public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import SquaresInCircles.Common.Analysis

/-!
# Eight squares: endpoint principles for continuous geometric transports

The statements quantify whole intervals. Their endpoints
are intrinsic contacts, alignments or circle/core junctions, never a mesh.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight

/-- Derivative lower bounds retain an explicit displacement reserve. -/
theorem derivative_reserve {f df : ℝ → ℝ} {l u x y k : ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ z ∈ Ioo l u, HasDerivAt f (df z) z)
    (hk : ∀ z ∈ Ioo l u, k ≤ df z)
    (hx : x ∈ Icc l u) (hy : y ∈ Icc l u) (hxy : x ≤ y) :
    k*(y-x) ≤ f y-f x := by
  have hm : MonotoneOn (fun z => f z-k*z) (Icc l u) := by
    apply monoOn_of_hasDeriv_nonneg (d := fun z => df z-k*1)
    · exact hc.sub (continuous_const.mul continuous_id).continuousOn
    · intro z hz
      exact (hd z hz).fun_sub ((hasDerivAt_id' z).const_mul k)
    · intro z hz
      linarith [hk z hz]
  have h := hm hx hy hxy
  simp only at h
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
    (_hk : 0 ≤ k) (hx : x ∈ Icc l u)
    (hg : ConcaveOn ℝ (Icc l u) (fun z => f z+k/2*z^2)) :
    min (f l) (f u)+k/2*(x-l)*(u-x) ≤ f x := by
  by_cases hlu : l=u
  · have hxl : x=l := by linarith [hx.1,hx.2]
    simp [hlu,hxl]
  have hgap : 0 < u-l := sub_pos.mpr (lt_of_le_of_ne (hx.1.trans hx.2) hlu)
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
      convert (hd z hz).fun_add ((hasDerivAt_pow 2 z).const_mul (k/2)) using 1
      ring
    · intro z hz
      convert (hdd z hz).fun_add ((hasDerivAt_id' z).const_mul k) using 1
      ring
    · intro z hz
      linarith [hcurv z hz]
  have h := concave_endpoint_reserve hk.le (Ioo_subset_Icc_self hx) hg
  have hpos : 0 < k/2*(x-l)*(u-x) := by
    exact mul_pos (mul_pos (div_pos hk (by norm_num)) (sub_pos.mpr hx.1))
      (sub_pos.mpr hx.2)
  have hm : min (f l) (f u)<f x := by linarith
  exact (min_lt_iff).mp hm

/-- Width preserving affine motion: one contact stays exact and the opposite
projection improves at the rate displayed in the paired-primary proof. -/
theorem primary_affine_projection_identities (a y A B u v lam : ℝ)
    (hu : Real.cos u ≠ 0) :
    A+(a+lam)*Real.sin u-(y+lam*Real.tan u)*Real.cos u=
        A+a*Real.sin u-y*Real.cos u ∧
      (a+lam)*Real.sin v+(y+lam*Real.tan u)*Real.cos v+B=
        a*Real.sin v+y*Real.cos v+B+lam*Real.sin (u+v)/Real.cos u := by
  rw [Real.tan_eq_sin_div_cos,Real.sin_add]
  constructor
  · field_simp
    ring
  · field_simp
    ring

end SquaresInCircles.Eight