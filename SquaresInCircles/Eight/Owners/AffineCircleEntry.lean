module

public import Mathlib.Topology.Order.IntermediateValue
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: reaching the circle with one primary projection fixed

The ray `ray p τ lam` moves a signed point `p` along the direction `(1, τ)`. For `τ = tan u` the
first primary projection `A + a sin u - y cos u` is constant along it, and the second,
`a sin v + y cos v + B`, increases when `u + v > 0`. Neither the distance `coreDistance` to the
core nor the squared radius `circle` decreases along the ray (`core_nondec`, `circle_nondec`); the
core inequality is proved algebraically, also where the ray crosses the tangent axis or the side
of the core. The intermediate value theorem gives the point where the ray meets the circle
(`exists_outer`), so a sorted contained point off the core with both primary projections moves to
the circle with both projections (`primary_outer_entry`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AffineCircleEntry

/-- The point `p` moved by `lam` along the direction `(1, τ)`. -/
def ray (p : SignedPoint) (τ lam : ℝ) : SignedPoint := ⟨p.a+lam,p.y+lam*τ⟩

@[simp] theorem ray_zero (p : SignedPoint) (τ : ℝ) : ray p τ 0=p := by
  cases p
  simp [ray]

/-- A ray of slope at most one does not leave the sorted cone. -/
theorem ray_sorted {p : SignedPoint} {τ lam : ℝ}
    (hp : p.Sorted) (hτ : |τ|≤1) (hlam : 0≤lam) : (ray p τ lam).Sorted := by
  have hab := abs_add_le p.y (lam*τ)
  rw [abs_mul,abs_of_nonneg hlam] at hab
  have hm := mul_le_mul_of_nonneg_left hτ hlam
  exact ⟨by dsimp [ray]; linarith [hp.1],by dsimp [ray]; linarith [hp.2]⟩

/-- Along a ray of slope at most one, the positive excess `max (|y| - 1/2) 0` of the transverse
coordinate drops by at most `lam`. -/
theorem excess_loss_bound (y τ lam : ℝ) (hlam : 0≤lam) (hτ : |τ|≤1) :
    max (|y|-1/2) 0 - max (|y+lam*τ|-1/2) 0 ≤ lam := by
  have hab := abs_sub_abs_le_abs_sub y (y+lam*τ)
  have he : y-(y+lam*τ)= -(lam*τ) := by ring
  rw [he,abs_neg,abs_mul,abs_of_nonneg hlam] at hab
  have hm := mul_le_mul_of_nonneg_left hτ hlam
  by_cases hy : |y|≤1/2
  · rw [max_eq_right (by linarith : |y|-1/2≤0)]
    linarith [le_max_right (|y+lam*τ|-1/2) 0]
  · rw [max_eq_left (by linarith : 0≤|y|-1/2)]
    have hmax := le_max_left (|y+lam*τ|-1/2) 0
    linarith

/-- `A² + b² ≤ (A + lam)² + b'²` when `0 ≤ b ≤ A`, `0 ≤ b'` and `b - b' ≤ lam`: the comparison
behind both `core_nondec` and `circle_nondec`, where the transverse magnitude may decrease and
pass through zero. -/
theorem cone_square_mono {A b b' lam : ℝ}
    (hA : 0≤A) (hb : 0≤b) (hba : b≤A) (hb' : 0≤b')
    (hlam : 0≤lam) (hloss : b-b'≤lam) :
    A^2+b^2≤(A+lam)^2+b'^2 := by
  by_cases hbb : b≤b'
  · have hsq := pow_le_pow_left₀ hb hbb 2
    nlinarith
  · have hdiff : 0≤b-b' := by linarith
    have h₁ := mul_le_mul_of_nonneg_right hloss (show 0≤b+b' by linarith)
    have h₂ := mul_le_mul_of_nonneg_left
      (show b+b'≤2*A by linarith) hlam
    nlinarith [sq_nonneg lam]

theorem core_nondec {p : SignedPoint} {τ lam : ℝ}
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hτ : |τ|≤1) (hlam : 0≤lam) :
    p.coreDistance≤(ray p τ lam).coreDistance := by
  have ha := SignedPoint.primary_gt_half hp hcore
  have hsmall : max (|p.y|-1/2) 0≤p.a-1/2 :=
    max_le (by linarith [hp.2]) (by linarith)
  have hsq := cone_square_mono (by linarith : 0≤p.a-1/2)
    (le_max_right (|p.y|-1/2) 0) hsmall
    (le_max_right (|p.y+lam*τ|-1/2) 0) hlam
    (excess_loss_bound p.y τ lam hlam hτ)
  have e0 : p.coreDistance=(p.a-1/2)^2+(max (|p.y|-1/2) 0)^2 := by
    simp only [SignedPoint.coreDistance]
    rw [max_eq_left (by linarith : 0≤p.a-1/2)]
  have e1 : (ray p τ lam).coreDistance=
      (p.a-1/2+lam)^2+(max (|p.y+lam*τ|-1/2) 0)^2 := by
    simp only [SignedPoint.coreDistance,ray]
    rw [max_eq_left (by linarith : 0≤p.a+lam-1/2)]
    ring
  rw [e0,e1]
  exact hsq

theorem circle_nondec {p : SignedPoint} {τ lam : ℝ}
    (hp : p.Sorted) (hτ : |τ|≤1) (hlam : 0≤lam) :
    p.circle≤(ray p τ lam).circle := by
  have hab := abs_sub_abs_le_abs_sub p.y (p.y+lam*τ)
  have he : p.y-(p.y+lam*τ)= -(lam*τ) := by ring
  rw [he,abs_neg,abs_mul,abs_of_nonneg hlam] at hab
  have hm := mul_le_mul_of_nonneg_left hτ hlam
  have hsq := cone_square_mono (by linarith [hp.1] : 0≤p.a+1/2)
    (by positivity : 0≤|p.y|+1/2)
    (by linarith [hp.2] : |p.y|+1/2≤p.a+1/2)
    (by positivity : 0≤|p.y+lam*τ|+1/2) hlam (by linarith)
  have e1 : (ray p τ lam).circle=(p.a+1/2+lam)^2+(|p.y+lam*τ|+1/2)^2 := by
    simp only [SignedPoint.circle,ray]
    ring
  rw [e1]
  exact hsq

/-- A sorted point in the circle of squared radius `q`, off the core, reaches the circle along the
ray of slope `τ`, `|τ| ≤ 1`, and stays contained, sorted and off the core on the way. -/
theorem exists_outer {q : ℝ} {p : SignedPoint} {τ : ℝ}
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (hτ : |τ|≤1) :
    ∃ lam : ℝ, 0≤lam ∧ (ray p τ lam).Sorted ∧ (ray p τ lam).Outer q ∧
      (ray p τ lam).AvoidsCore ∧
      ∀ μ∈Icc 0 lam, (ray p τ μ).Contained q ∧ (ray p τ μ).AvoidsCore := by
  have hq : 0≤q := p.circle_nonneg.trans hc
  let L : ℝ := Real.sqrt q+1
  have hL : 0<L := by dsimp [L]; positivity
  have hs := Real.sq_sqrt hq
  have hn := Real.sqrt_nonneg q
  have hbig : q≤(ray p τ L).circle := by
    dsimp [ray,SignedPoint.circle,L]
    nlinarith [hp.1,sq_nonneg (|p.y+(Real.sqrt q+1)*τ|+1/2)]
  have hcont : ContinuousOn (fun lam => (ray p τ lam).circle) (Icc 0 L) := by
    dsimp [ray,SignedPoint.circle]
    fun_prop
  obtain ⟨lam,hlam,heq⟩ := intermediate_value_Icc hL.le hcont
    (show q∈Icc ((ray p τ 0).circle) ((ray p τ L).circle) from
      ⟨by rw [ray_zero]; exact hc,hbig⟩)
  have heq' : (ray p τ lam).circle=q := heq
  refine ⟨lam,hlam.1,ray_sorted hp hτ hlam.1,heq,?_,?_⟩
  · exact hcore.trans (core_nondec hp hcore hτ hlam.1)
  · intro μ hμ
    have hμs := ray_sorted hp hτ hμ.1
    have hμcore : (ray p τ μ).AvoidsCore :=
      hcore.trans (core_nondec hp hcore hτ hμ.1)
    have hid : ray (ray p τ μ) τ (lam-μ)=ray p τ lam := by
      simp only [ray,SignedPoint.mk.injEq]
      constructor <;> ring
    have hmono := circle_nondec hμs hτ (sub_nonneg.mpr hμ.2)
    rw [hid,heq'] at hmono
    exact ⟨hmono,hμcore⟩

/-- For `|u| ≤ frameCap`, `|sin u| < cos u`: the slope `tan u` lies strictly inside the sorted
cone. -/
theorem signed_trig {u : ℝ} (hu : |u|≤frameCap) :
    0<Real.cos u ∧ |Real.sin u|<Real.cos u ∧ |Real.tan u|<1 := by
  have hu' : |u|∈Icc 0 (7/10 : ℝ) := ⟨abs_nonneg _,hu⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hu'
  have hec : Real.cos |u|=Real.cos u := by
    rcases le_total 0 u with h | h
    · simp [abs_of_nonneg h]
    · simp [abs_of_nonpos h]
  have hes : Real.sin |u|=|Real.sin u| := by
    rcases le_total 0 u with h | h
    · have hh := (transport_trig ⟨h,by simpa [abs_of_nonneg h] using hu⟩).2.2.1
      simp [abs_of_nonneg h,abs_of_nonneg hh]
    · have hh := (transport_trig (x := -u)
        ⟨by linarith,by rw [abs_of_nonpos h] at hu; exact hu⟩).2.2.1
      rw [Real.sin_neg] at hh
      rw [abs_of_nonpos h,Real.sin_neg,abs_of_nonpos (by linarith : Real.sin u≤0)]
  rw [hec] at hc
  rw [hec,hes] at hsc
  refine ⟨by linarith,hsc,?_⟩
  rw [Real.tan_eq_sin_div_cos,abs_div,abs_of_pos (by linarith : 0<Real.cos u)]
  exact (div_lt_one (by linarith)).mpr hsc

/-- A sorted point in the circle, off the core, with the primary projections at the angles `u` and
`v`, `0 < u + v ≤ 7/10`, moves to a point on the circle, sorted and off the core, with the same
two projections. -/
theorem primary_outer_entry {q A B u v : ℝ} {p : SignedPoint}
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (hu : |u|≤frameCap) (ht : u+v∈Ioc 0 (7/10 : ℝ))
    (hfirst : edgeWidth u≤A+p.a*Real.sin u-p.y*Real.cos u)
    (hsecond : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+B) :
    ∃ p' : SignedPoint, p'.Sorted ∧ p'.Outer q ∧ p'.AvoidsCore ∧
      edgeWidth u≤A+p'.a*Real.sin u-p'.y*Real.cos u ∧
      edgeWidth v≤p'.a*Real.sin v+p'.y*Real.cos v+B := by
  obtain ⟨hcos,hs,hτ⟩ := signed_trig hu
  obtain ⟨lam,hlam,hps,hpo,hpc,hpath⟩ := exists_outer hp hcore hc hτ.le
  have hid := primary_affine_projection_identities p.a p.y A B u v lam (ne_of_gt hcos)
  have htotal : 0<Real.sin (u+v) := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [Real.pi_gt_three,ht.2])
  have hgain : 0≤lam*Real.sin (u+v)/Real.cos u :=
    div_nonneg (mul_nonneg hlam htotal.le) hcos.le
  refine ⟨ray p (Real.tan u) lam,hps,hpo,hpc,?_,?_⟩
  · dsimp [ray]
    rwa [hid.1]
  · dsimp [ray]
    rw [hid.2]
    linarith

end AffineCircleEntry
end SquaresInCircles.Eight