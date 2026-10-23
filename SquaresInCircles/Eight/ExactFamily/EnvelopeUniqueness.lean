module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.Order.Compact

/-!
# The global critical-point uniqueness step for a scalar envelope

Two strict local minima of a continuous function force an interior local
maximum between them. Consequently, if every critical point in an interval
is a strict local minimum, there is at most one critical point there.
This argument includes critical points at positive defect.

This is a general analytic lemma, not an assertion that the five-corner
envelope satisfies its hypotheses. The actual envelope regularity and
Hessian estimates must be supplied at the application site. The Lean
source remains uncompiled.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ExactFamily.EnvelopeGeometry

open Set
open Filter
open scoped Topology

/-- A strict minimum on an explicit open neighborhood. -/
def StrictMinimum (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε>0, ∀ y∈Ioo (x-ε) (x+ε), y≠x → f x<f y

/-- The strict second-derivative test, in the neighborhood form needed
by the intervening-maximum argument. The derivative sign follows from
its positive derivative at the critical point; the mean value theorem
then gives strict inequalities on both sides. -/
theorem strictMinimum_of_positive_second_derivative {f : ℝ → ℝ} {a b x d : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b)) (hx : x∈Ioo a b)
    (hzero : deriv f x=0) (hsecond : HasDerivAt (deriv f) d x) (hdpos : 0<d) :
    StrictMinimum f x := by
  have hsign : ∀ᶠ y in 𝓝 x, SignType.sign (deriv f y)=SignType.sign (y-x) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos (by rw [hsecond.deriv]; exact hdpos) hzero
  obtain ⟨ε,hε,hnear⟩ := Metric.eventually_nhds_iff.mp hsign
  let δ : ℝ := min ε (min (x-a) (b-x))
  have hδ : 0<δ := lt_min_iff.mpr ⟨hε,lt_min_iff.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
  have hδε : δ≤ε := min_le_left _ _
  have hδa : δ≤x-a := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ≤b-x := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,?_⟩
  intro y hy hyx
  have hya : a<y := by linarith [hy.1]
  have hyb : y<b := by linarith [hy.2]
  have hsign' (z : ℝ) (hz : z∈Ioo (x-δ) (x+δ)) :
      SignType.sign (deriv f z)=SignType.sign (z-x) := by
    apply hnear
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith [hz.1,hz.2]
  rcases lt_or_gt_of_ne hyx with hyx | hxy
  · have hsub : Icc y x ⊆ Icc a b := by
      intro z hz
      exact ⟨hya.le.trans hz.1,hz.2.trans hx.2.le⟩
    have hsub' : Ioo y x ⊆ Ioo a b := by
      intro z hz
      exact ⟨hya.trans hz.1,hz.2.trans hx.2⟩
    obtain ⟨z,hz,he⟩ := exists_deriv_eq_slope f hyx (hc.mono hsub) (hd.mono hsub')
    have hsg := hsign' z ⟨by linarith [hy.1,hz.1],by linarith [hz.2]⟩
    have hdz : deriv f z<0 := by
      rw [SignType.sign_neg (sub_neg.mpr hz.2)] at hsg
      exact SignType.sign_eq_neg_one_iff.mp hsg
    rw [he] at hdz
    have hnum : f x-f y<0 := by
      simpa using (div_lt_iff₀ (sub_pos.mpr hyx)).mp hdz
    linarith
  · have hsub : Icc x y ⊆ Icc a b := by
      intro z hz
      exact ⟨hx.1.le.trans hz.1,hz.2.trans hyb.le⟩
    have hsub' : Ioo x y ⊆ Ioo a b := by
      intro z hz
      exact ⟨hx.1.trans hz.1,hz.2.trans hyb⟩
    obtain ⟨z,hz,he⟩ := exists_deriv_eq_slope f hxy (hc.mono hsub) (hd.mono hsub')
    have hsg := hsign' z ⟨by linarith [hz.1],by linarith [hy.2,hz.2]⟩
    have hdz : 0<deriv f z := by
      rw [SignType.sign_pos (sub_pos.mpr hz.1)] at hsg
      exact SignType.sign_eq_one_iff.mp hsg
    rw [he] at hdz
    have hnum : 0<f y-f x := by
      simpa using (lt_div_iff₀ (sub_pos.mpr hxy)).mp hdz
    linarith

theorem StrictMinimum.right_witness {f : ℝ → ℝ} {x y : ℝ}
    (h : StrictMinimum f x) (hxy : x<y) :
    ∃ z∈Ioo x y, f x<f z := by
  obtain ⟨ε,hε,hf⟩ := h
  have hbound : x<min y (x+ε) := lt_min_iff.mpr ⟨hxy,by linarith⟩
  obtain ⟨z,hxz,hzu⟩ := exists_between hbound
  have hzy : z<y := lt_of_lt_of_le hzu (min_le_left _ _)
  have hze : z<x+ε := lt_of_lt_of_le hzu (min_le_right _ _)
  exact ⟨z,⟨hxz,hzy⟩,hf z ⟨by linarith,hze⟩ (ne_of_gt hxz)⟩

theorem StrictMinimum.left_witness {f : ℝ → ℝ} {x y : ℝ}
    (h : StrictMinimum f x) (hyx : y<x) :
    ∃ z∈Ioo y x, f x<f z := by
  obtain ⟨ε,hε,hf⟩ := h
  have hbound : max y (x-ε)<x := max_lt_iff.mpr ⟨hyx,by linarith⟩
  obtain ⟨z,hlz,hzx⟩ := exists_between hbound
  have hyz : y<z := lt_of_le_of_lt (le_max_left _ _) hlz
  have hez : x-ε<z := lt_of_le_of_lt (le_max_right _ _) hlz
  exact ⟨z,⟨hyz,hzx⟩,hf z ⟨hez,by linarith⟩ (ne_of_lt hzx)⟩

theorem point_above_endpoints_forces_interior_maximum {f : ℝ → ℝ} {x y u : ℝ}
    (hxy : x<y) (hc : ContinuousOn f (Icc x y)) (hu : u∈Icc x y)
    (hux : f x<f u) (huy : f y<f u) :
    ∃ z∈Ioo x y, IsMaxOn f (Icc x y) z ∧ IsLocalMax f z := by
  obtain ⟨z,hz,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc x y).Nonempty from ⟨x,le_rfl,hxy.le⟩) hc
  have hzx : z≠x := by
    intro he
    have hh := hmax hu
    rw [he] at hh
    exact (not_lt_of_ge hh) hux
  have hzy : z≠y := by
    intro he
    have hh := hmax hu
    rw [he] at hh
    exact (not_lt_of_ge hh) huy
  have hxz : x<z := lt_of_le_of_ne hz.1 hzx.symm
  have hzy' : z<y := lt_of_le_of_ne hz.2 hzy
  exact ⟨z,⟨hxz,hzy'⟩,hmax,hmax.isLocalMax (Icc_mem_nhds hxz hzy')⟩

/-- The intervening maximum lies strictly between the two strict minima.
Only continuity on the closed interval is needed for this step. -/
theorem strict_minima_force_interior_maximum {f : ℝ → ℝ} {x y : ℝ}
    (hxy : x<y) (hc : ContinuousOn f (Icc x y))
    (hx : StrictMinimum f x) (hy : StrictMinimum f y) :
    ∃ z∈Ioo x y, IsMaxOn f (Icc x y) z ∧ IsLocalMax f z := by
  obtain ⟨u,hu,hfu⟩ := hx.right_witness hxy
  obtain ⟨v,hv,hfv⟩ := hy.left_witness hxy
  obtain ⟨z,hz,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc x y).Nonempty from ⟨x,le_rfl,hxy.le⟩) hc
  have hzx : z≠x := by
    intro he
    have hh := hmax (show u∈Icc x y from ⟨hu.1.le,hu.2.le⟩)
    rw [he] at hh
    exact (not_lt_of_ge hh) hfu
  have hzy : z≠y := by
    intro he
    have hh := hmax (show v∈Icc x y from ⟨hv.1.le,hv.2.le⟩)
    rw [he] at hh
    exact (not_lt_of_ge hh) hfv
  have hxz : x<z := lt_of_le_of_ne hz.1 hzx.symm
  have hzy' : z<y := lt_of_le_of_ne hz.2 hzy
  exact ⟨z,⟨hxz,hzy'⟩,hmax,hmax.isLocalMax (Icc_mem_nhds hxz hzy')⟩

/-- Every critical point must be a strict minimum on the entire interval,
not merely on one sublevel component. This rules out an intervening
maximum and gives global uniqueness of critical points. -/
theorem critical_unique_of_strict_minimum {f : ℝ → ℝ} {a b x y : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hmin : ∀ z∈Ioo a b, deriv f z=0 → StrictMinimum f z)
    (hx : x∈Ioo a b) (hy : y∈Ioo a b)
    (hxd : deriv f x=0) (hyd : deriv f y=0) : x=y := by
  have himpossible (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b)
      (hud : deriv f u=0) (hvd : deriv f v=0) (huv : u<v) : False := by
    have hsub : Icc u v ⊆ Icc a b := by
      intro z hz
      exact ⟨hu.1.le.trans hz.1,hz.2.trans hv.2.le⟩
    obtain ⟨z,hz,hmax,hloc⟩ := strict_minima_force_interior_maximum huv
      (hc.mono hsub) (hmin u hu hud) (hmin v hv hvd)
    have hzab : z∈Ioo a b := ⟨hu.1.trans hz.1,hz.2.trans hv.2⟩
    have hzmin := hmin z hzab hloc.deriv_eq_zero
    obtain ⟨w,hw,hfw⟩ := hzmin.right_witness hz.2
    have hwuv : w∈Icc u v := ⟨(hz.1.trans hw.1).le,hw.2.le⟩
    exact (not_lt_of_ge (hmax hwuv)) hfw
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact False.elim (himpossible x y hx hy hxd hyd hxy)
  · exact hxy
  · exact False.elim (himpossible y x hy hx hyd hxd hyx)

/-- An application form using actual first derivatives. Differentiability
is stated pointwise on the open interval, matching an envelope theorem. -/
theorem critical_unique_of_hasDerivAt {f : ℝ → ℝ} {a b x y : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ z∈Ioo a b, DifferentiableAt ℝ f z)
    (hmin : ∀ z∈Ioo a b, HasDerivAt f 0 z → StrictMinimum f z)
    (hx : x∈Ioo a b) (hy : y∈Ioo a b)
    (hxd : HasDerivAt f 0 x) (hyd : HasDerivAt f 0 y) : x=y := by
  apply critical_unique_of_strict_minimum hc ?_ hx hy hxd.deriv hyd.deriv
  intro z hz hzero
  apply hmin z hz
  simpa only [hzero] using (hd z hz).hasDerivAt

/-- The same maximum argument proves more than uniqueness: every
interior critical point is the strict global minimum, including comparison
with the two endpoints. No derivative sign at those endpoints is needed. -/
theorem critical_is_strict_global_minimum {f : ℝ → ℝ} {a b x : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hmin : ∀ z∈Ioo a b, deriv f z=0 → StrictMinimum f z)
    (hx : x∈Ioo a b) (hxd : deriv f x=0) :
    ∀ y∈Icc a b, y≠x → f x<f y := by
  intro y hy hyx
  by_contra! hle
  rcases lt_or_gt_of_ne hyx with hyx | hxy
  · obtain ⟨u,hu,hfu⟩ := (hmin x hx hxd).left_witness hyx
    have hsub : Icc y x ⊆ Icc a b := by
      intro z hz
      exact ⟨hy.1.trans hz.1,hz.2.trans hx.2.le⟩
    obtain ⟨z,hz,hmax,hloc⟩ := point_above_endpoints_forces_interior_maximum
      hyx (hc.mono hsub) ⟨hu.1.le,hu.2.le⟩ (hle.trans_lt hfu) hfu
    have hzab : z∈Ioo a b := ⟨hy.1.trans_lt hz.1,hz.2.trans hx.2⟩
    obtain ⟨w,hw,hfw⟩ := (hmin z hzab hloc.deriv_eq_zero).right_witness hz.2
    have hwsub : w∈Icc y x := ⟨(hz.1.trans hw.1).le,hw.2.le⟩
    exact (not_lt_of_ge (hmax hwsub)) hfw
  · obtain ⟨u,hu,hfu⟩ := (hmin x hx hxd).right_witness hxy
    have hsub : Icc x y ⊆ Icc a b := by
      intro z hz
      exact ⟨hx.1.le.trans hz.1,hz.2.trans hy.2⟩
    obtain ⟨z,hz,hmax,hloc⟩ := point_above_endpoints_forces_interior_maximum
      hxy (hc.mono hsub) ⟨hu.1.le,hu.2.le⟩ hfu (hle.trans_lt hfu)
    have hzab : z∈Ioo a b := ⟨hx.1.trans hz.1,hz.2.trans_le hy.2⟩
    obtain ⟨w,hw,hfw⟩ := (hmin z hzab hloc.deriv_eq_zero).right_witness hz.2
    have hwsub : w∈Icc x y := ⟨(hz.1.trans hw.1).le,hw.2.le⟩
    exact (not_lt_of_ge (hmax hwsub)) hfw

theorem critical_is_global_minimum {f : ℝ → ℝ} {a b x : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hmin : ∀ z∈Ioo a b, deriv f z=0 → StrictMinimum f z)
    (hx : x∈Ioo a b) (hxd : deriv f x=0) :
    ∀ y∈Icc a b, f x≤f y := by
  intro y hy
  by_cases he : y=x
  · simpa [he]
  · exact (critical_is_strict_global_minimum hc hmin hx hxd y hy he).le

end SquaresInCircles.Eight.ExactFamily.EnvelopeGeometry
