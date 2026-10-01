import SquaresInCircles.Six.Analytic.EndpointReduction
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A curvature identity for the radical terms in Appendix A

For r(x)=sqrt(p+q sin x), direct differentiation gives
r''(x)=-r(x)/4+(p^2-q^2)/(4 r(x)^3).
Consequently A cos x+B sin x-R r(x) is concave whenever p^2>=q^2,
R>=0 and R r(x)<=4(A cos x+B sin x). The identity and the sufficient
inequality are proved on the whole interval; no derivative boxes are checked.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

def radicalTrig (A B p q R x:ℝ) : ℝ :=
  A*Real.cos x+B*Real.sin x-R*Real.sqrt (p+q*Real.sin x)

lemma radical_second_identity {p q s c r:ℝ} (hr:r≠0)
    (hsq:r^2=p+q*s) (hu:c^2+s^2=1) :
    -q*s/(2*r)-q^2*c^2/(4*r^3) = -r/4+(p^2-q^2)/(4*r^3) := by
  calc
    _ = (-2*q*s*r^2-q^2*c^2)/(4*r^3) := by field_simp [hr]; ring
    _ = (-r^4+p^2-q^2)/(4*r^3) := by
      congr 1
      linear_combination (r^2+p-q*s)*hsq - q^2*hu
    _ = _ := by field_simp [hr]; ring

lemma radical_first_derivative {p q x:ℝ} (hx:0<p+q*Real.sin x) :
    HasDerivAt (fun y=>Real.sqrt (p+q*Real.sin y))
      (q*Real.cos x/(2*Real.sqrt (p+q*Real.sin x))) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul q).const_add p).sqrt (ne_of_gt hx)
  simpa only [mul_comm] using h

lemma radical_second_derivative {p q x:ℝ} (hx:0<p+q*Real.sin x) :
    HasDerivAt (fun y=>q*Real.cos y/(2*Real.sqrt (p+q*Real.sin y)))
      (-Real.sqrt (p+q*Real.sin x)/4+
        (p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3)) x := by
  let r := Real.sqrt (p+q*Real.sin x)
  have hr : 0<r := Real.sqrt_pos.mpr hx
  have hroot := radical_first_derivative hx
  have hd := ((Real.hasDerivAt_cos x).const_mul q).div (hroot.const_mul 2)
    (mul_ne_zero (by norm_num) (ne_of_gt hr))
  have hformula : HasDerivAt (fun y=>q*Real.cos y/(2*Real.sqrt (p+q*Real.sin y)))
      (-q*Real.sin x/(2*r)-q^2*(Real.cos x)^2/(4*r^3)) x := by
    convert hd using 1
    field_simp [ne_of_gt hr]
    ring
  have hsq : r^2=p+q*Real.sin x := Real.sq_sqrt hx.le
  rw [radical_second_identity (ne_of_gt hr) hsq
    (by nlinarith [Real.sin_sq_add_cos_sq x])] at hformula
  exact hformula

/-- Concavity follows from an explicit algebraic upper bound on curvature. -/
theorem radicalTrig_concave {A B p q R l u:ℝ}
    (hR:0≤R) (hpq:q^2≤p^2)
    (hroot:∀x∈Set.Icc l u,0<p+q*Real.sin x)
    (hbound:∀x∈Set.Icc l u,
      R*Real.sqrt (p+q*Real.sin x)≤4*(A*Real.cos x+B*Real.sin x)) :
    ConcaveOn ℝ (Set.Icc l u) (radicalTrig A B p q R) := by
  let d : ℝ→ℝ := fun x=>-A*Real.sin x+B*Real.cos x-
    R*(q*Real.cos x/(2*Real.sqrt (p+q*Real.sin x)))
  let dd : ℝ→ℝ := fun x=>-A*Real.cos x-B*Real.sin x-
    R*(-Real.sqrt (p+q*Real.sin x)/4+(p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3))
  have hd (x:ℝ) (hx:x∈Set.Icc l u) : HasDerivAt (radicalTrig A B p q R) (d x) x := by
    convert (((Real.hasDerivAt_cos x).const_mul A).add
      ((Real.hasDerivAt_sin x).const_mul B)).sub
      ((radical_first_derivative (hroot x hx)).const_mul R) using 1
    · funext y
      simp only [radicalTrig,Pi.add_apply,Pi.sub_apply]
    · simp only [d]
      ring
  have hdd (x:ℝ) (hx:x∈Set.Icc l u) : HasDerivAt d (dd x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (-A)).add
      ((Real.hasDerivAt_cos x).const_mul B)).sub
      ((radical_second_derivative (hroot x hx)).const_mul R) using 1
    simp only [dd]
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (f':=d) (f'':=dd) (by unfold radicalTrig; fun_prop)
  · intro x hx
    exact (hd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact (hdd x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hmem : x∈Set.Icc l u := interior_subset hx
    have hr : 0<Real.sqrt (p+q*Real.sin x) := Real.sqrt_pos.mpr (hroot x hmem)
    have hquot : 0≤R*((p^2-q^2)/(4*(Real.sqrt (p+q*Real.sin x))^3)) :=
      mul_nonneg hR (div_nonneg (sub_nonneg.mpr hpq) (by positivity))
    have hb := hbound x hmem
    dsimp [dd]
    nlinarith

/-- Affine changes of argument preserve concavity when their image remains
inside the proved domain. In particular this handles x -> u-x. -/
lemma concave_affine_argument {f:ℝ→ℝ} {L U l u a b:ℝ}
    (hf:ConcaveOn ℝ (Set.Icc L U) f)
    (hmap:∀x∈Set.Icc l u,a*x+b∈Set.Icc L U) :
    ConcaveOn ℝ (Set.Icc l u) (fun x=>f (a*x+b)) := by
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy r s hr hs hrs
  have h := hf.2 (hmap x hx) (hmap y hy) hr hs hrs
  have hid : a*(r*x+s*y)+b=r*(a*x+b)+s*(a*y+b) := by
    linear_combination -b*hrs
  simpa only [smul_eq_mul,hid] using h

lemma concave_constant (C l u:ℝ) : ConcaveOn ℝ (Set.Icc l u) (fun _=>C) := by
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy r s hr hs hrs
  simp only [smul_eq_mul]
  rw [← add_mul,hrs,one_mul]

lemma positive_on_concave_interval {f:ℝ→ℝ} {l u x:ℝ}
    (hf:ConcaveOn ℝ (Set.Icc l u) f) (hx:l≤x ∧ x≤u)
    (hl:0<f l) (hu:0<f u) : 0<f x := by
  exact (lt_min hl hu).trans_le
    (hf.min_le_of_mem_Icc ⟨le_rfl,hx.1.trans hx.2⟩ ⟨hx.1.trans hx.2,le_rfl⟩ hx)

end SquaresInCircles.Six.Analytic
