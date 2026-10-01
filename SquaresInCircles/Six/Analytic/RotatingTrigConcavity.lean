import SquaresInCircles.Six.Analytic.RotatingLength
import SquaresInCircles.Six.Analytic.CompensatedTrigConcavity

/-!
# A trigonometric sum minus one rotating-vector length

The sharp harmonic-mean curvature bound is compensated by the actual
trigonometric terms. The hypotheses are whole-interval analytic inequalities,
not sampled derivatives. The unequal fixed lengths guarantee a nonzero
resultant everywhere, so no hidden root singularity is crossed.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

def sineRoot (R p q x : ℝ) : ℝ := -R*Real.sqrt (p^2+q^2+2*p*q*Real.sin x)

lemma sineRoot_eq_harmonic (R p q x : ℝ) :
    sineRoot R p q x=harmonicRoot R (p^2+q^2) 0 (2*p*q) x := by
  simp only [sineRoot,harmonicRoot,harmonicArg,zero_mul,add_zero]

lemma sineRoot_arg_positive {p q x : ℝ} (hp : 0≤p) (hq : 0≤q) (hne : p≠q) :
    0<harmonicArg (p^2+q^2) 0 (2*p*q) x :=
  harmonic_arg_positive hp hq hne rfl (by ring)

/-- Concavity of the whole expression, even if the root term itself is convex. -/
theorem rotating_trig_concave {C A B G H c R p q L l u : ℝ}
    (hR : 0≤R) (hp : 0≤p) (hq : 0≤q) (hpq : 0<p+q) (hne : p≠q)
    (hL : R*p*q/(p+q)≤L)
    (htrig : ∀ x∈Set.Icc l u,
      L≤A*Real.cos x+B*Real.sin x+G*Real.cos (x+c)+H*Real.sin (x+c)) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun x => C+A*Real.cos x+B*Real.sin x+G*Real.cos (x+c)+H*Real.sin (x+c)+sineRoot R p q x) := by
  let f : ℝ→ℝ := fun x => C+A*Real.cos x+B*Real.sin x+
    G*Real.cos (x+c)+H*Real.sin (x+c)+sineRoot R p q x
  let f' : ℝ→ℝ := fun x => -A*Real.sin x+B*Real.cos x-
    G*Real.sin (x+c)+H*Real.cos (x+c)+harmonicRootD R (p^2+q^2) 0 (2*p*q) x
  let f'' : ℝ→ℝ := fun x => -A*Real.cos x-B*Real.sin x-
    G*Real.cos (x+c)-H*Real.sin (x+c)+harmonicCurvature R (p^2+q^2) 0 (2*p*q) x
  have harg (x : ℝ) : 0<harmonicArg (p^2+q^2) 0 (2*p*q) x :=
    sineRoot_arg_positive hp hq hne
  have hd (x : ℝ) : HasDerivAt f (f' x) x := by
    have hb := ((((Real.hasDerivAt_cos x).const_mul A).const_add C).add
      ((Real.hasDerivAt_sin x).const_mul B)).add
      ((((Real.hasDerivAt_cos (x+c)).comp x ((hasDerivAt_id x).add_const c)).const_mul G).add
        (((Real.hasDerivAt_sin (x+c)).comp x ((hasDerivAt_id x).add_const c)).const_mul H))
    have hr := harmonicRoot_deriv (R := R) (harg x)
    convert hb.add hr using 1
    · funext y
      dsimp [f]
      rw [sineRoot_eq_harmonic]
      ring
    · dsimp [f']
      ring
  have hdd (x : ℝ) : HasDerivAt f' (f'' x) x := by
    have hb := (((Real.hasDerivAt_sin x).const_mul (-A)).add
      ((Real.hasDerivAt_cos x).const_mul B)).add
      ((((Real.hasDerivAt_sin (x+c)).comp x ((hasDerivAt_id x).add_const c)).const_mul (-G)).add
        (((Real.hasDerivAt_cos (x+c)).comp x ((hasDerivAt_id x).add_const c)).const_mul H))
    have hr := harmonicRoot_second (R := R) (harg x)
    convert hb.add hr using 1
    · funext y
      dsimp [f']
      ring
    · dsimp [f'']
      ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc l u)
    (f' := f') (f'' := f'') (by dsimp [f,sineRoot]; fun_prop)
  · intro x _; exact (hd x).hasDerivWithinAt
  · intro x _; exact (hdd x).hasDerivWithinAt
  · intro x hx
    have ht := htrig x (interior_subset hx)
    have hr := (harmonicCurvature_le_harmonic_mean hR hp hq hpq rfl (by ring) (harg x)).trans hL
    dsimp [f'']
    linarith

/-- A root upper bound proved by squaring yields a lower bound on its negative. -/
lemma sineRoot_lower_of_squared {R p q x L : ℝ}
    (hR : 0≤R) (hL : 0≤L) (hp : 0≤p) (hq : 0≤q) (hne : p≠q)
    (hsq : p^2+q^2+2*p*q*Real.sin x≤L^2) : -R*L≤ sineRoot R p q x := by
  have harg : 0≤p^2+q^2+2*p*q*Real.sin x := by
    have hh := sineRoot_arg_positive (x := x) hp hq hne
    simpa [harmonicArg] using hh.le
  have hroot := Real.sq_sqrt harg
  have hn := Real.sqrt_nonneg (p^2+q^2+2*p*q*Real.sin x)
  have hle : Real.sqrt (p^2+q^2+2*p*q*Real.sin x)≤L := by nlinarith
  dsimp [sineRoot]
  exact mul_le_mul_of_nonpos_left hle (by linarith)

end SquaresInCircles.Six.Analytic
