import SquaresInCircles.Six.Analytic.RadicalTrigConcavity

/-!
# Curvature of a general first-harmonic square root

For z(x)=sqrt(p+q sin x+r cos x), the exact identity is
z''=-z/4+(p^2-q^2-r^2)/(4 z^3). This extends the one-sine lemma without
choosing a phase or losing its sine/cosine signs. Applications prove positivity
of the radicand and the displayed curvature reserve on their whole interval.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

def harmonicRoot (p q r x : ℝ) : ℝ := Real.sqrt (p+q*Real.sin x+r*Real.cos x)

def harmonicRootFirst (p q r x : ℝ) : ℝ :=
  (q*Real.cos x-r*Real.sin x)/(2*harmonicRoot p q r x)

lemma harmonic_root_second_identity {p q r s c z : ℝ} (hz : z≠0)
    (hsq : z^2=p+q*s+r*c) (hu : c^2+s^2=1) :
    -(q*s+r*c)/(2*z)-(q*c-r*s)^2/(4*z^3) =
      -z/4+(p^2-q^2-r^2)/(4*z^3) := by
  calc
    _ = (-2*(q*s+r*c)*z^2-(q*c-r*s)^2)/(4*z^3) := by
      field_simp [hz]
      ring
    _ = (-z^4+p^2-q^2-r^2)/(4*z^3) := by
      congr 1
      linear_combination (z^2+p-q*s-r*c)*hsq-(q^2+r^2)*hu
    _ = _ := by field_simp [hz]; ring

lemma harmonic_root_hasDeriv {p q r x : ℝ}
    (hx : 0 < p+q*Real.sin x+r*Real.cos x) :
    HasDerivAt (harmonicRoot p q r) (harmonicRootFirst p q r x) x := by
  have h := ((((Real.hasDerivAt_sin x).const_mul q).const_add p).add
    ((Real.hasDerivAt_cos x).const_mul r)).sqrt (ne_of_gt hx)
  convert h using 1 <;> dsimp [harmonicRoot,harmonicRootFirst] <;> ring

lemma harmonic_root_first_hasDeriv {p q r x : ℝ}
    (hx : 0 < p+q*Real.sin x+r*Real.cos x) :
    HasDerivAt (harmonicRootFirst p q r)
      (-harmonicRoot p q r x/4+
        (p^2-q^2-r^2)/(4*(harmonicRoot p q r x)^3)) x := by
  let z := harmonicRoot p q r x
  have hz : 0 < z := Real.sqrt_pos.mpr hx
  have hf := harmonic_root_hasDeriv hx
  have hn := ((Real.hasDerivAt_cos x).const_mul q).sub
    ((Real.hasDerivAt_sin x).const_mul r)
  have hd := hn.div (hf.const_mul 2) (mul_ne_zero (by norm_num) (ne_of_gt hz))
  have hformula : HasDerivAt (harmonicRootFirst p q r)
      (-(q*Real.sin x+r*Real.cos x)/(2*z)-
        (q*Real.cos x-r*Real.sin x)^2/(4*z^3)) x := by
    convert hd using 1
    · rfl
    · dsimp [harmonicRootFirst]
      field_simp [ne_of_gt hz]
      ring
  have hsq : z^2=p+q*Real.sin x+r*Real.cos x := Real.sq_sqrt hx.le
  rw [harmonic_root_second_identity (ne_of_gt hz) hsq
    (by nlinarith [Real.sin_sq_add_cos_sq x])] at hformula
  exact hformula

/-- A whole-interval algebraic reserve proves the required second-derivative sign. -/
theorem harmonic_root_trig_concave {A B p q r R l u : ℝ}
    (hR : 0 ≤ R) (hp : q^2+r^2 ≤ p^2)
    (hroot : ∀ x∈Set.Icc l u,0 < p+q*Real.sin x+r*Real.cos x)
    (hreserve : ∀ x∈Set.Icc l u,
      R*harmonicRoot p q r x ≤ 4*(A*Real.cos x+B*Real.sin x)) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun x => A*Real.cos x+B*Real.sin x-R*harmonicRoot p q r x) := by
  let f : ℝ → ℝ := fun x => A*Real.cos x+B*Real.sin x-R*harmonicRoot p q r x
  let f' : ℝ → ℝ := fun x => -A*Real.sin x+B*Real.cos x-R*harmonicRootFirst p q r x
  let f'' : ℝ → ℝ := fun x => -A*Real.cos x-B*Real.sin x-
    R*(-harmonicRoot p q r x/4+(p^2-q^2-r^2)/(4*(harmonicRoot p q r x)^3))
  have hf (x : ℝ) (hx : x∈Set.Icc l u) : HasDerivAt f (f' x) x := by
    convert (((Real.hasDerivAt_cos x).const_mul A).add
      ((Real.hasDerivAt_sin x).const_mul B)).sub
      ((harmonic_root_hasDeriv (hroot x hx)).const_mul R) using 1 <;>
      dsimp [f,f'] <;> ring
  have hff (x : ℝ) (hx : x∈Set.Icc l u) : HasDerivAt f' (f'' x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (-A)).add
      ((Real.hasDerivAt_cos x).const_mul B)).sub
      ((harmonic_root_first_hasDeriv (hroot x hx)).const_mul R) using 1 <;>
      dsimp [f',f''] <;> ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (f' := f') (f'' := f'') (by dsimp [f,harmonicRoot]; fun_prop)
  · intro x hx
    exact (hf x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact (hff x (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have hmem : x∈Set.Icc l u := interior_subset hx
    have hz : 0 < harmonicRoot p q r x := Real.sqrt_pos.mpr (hroot x hmem)
    have hnonneg : 0 ≤ R*((p^2-q^2-r^2)/(4*(harmonicRoot p q r x)^3)) :=
      mul_nonneg hR (div_nonneg (by linarith [hp]) (by positivity))
    have hb := hreserve x hmem
    dsimp [f'']
    nlinarith only [hnonneg,hb]

end SquaresInCircles.Six.Analytic
