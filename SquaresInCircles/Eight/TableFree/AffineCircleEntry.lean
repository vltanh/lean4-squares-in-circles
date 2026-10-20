module

public import SquaresInCircles.Eight.TableFree.EndpointPrinciples
public import SquaresInCircles.Eight.TableFree.TrigonometricReserves
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Entry to the actual circle while an original primary stays fixed

Uncompiled source draft. The affine ray has slope `tan u` in the signed
coordinates. Its first physical projection is unchanged; the other increases
when the paired total is positive. The exact core-distance inequality is
proved algebraically, including crossings of the tangent axis and core side.
The circle endpoint is obtained by the intermediate value theorem, not by
substituting an auxiliary ceiling.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace AffineCircleEntry

/-- A direction of slope at most one cannot leave the sorted cone. -/
def ray (p : SignedPoint) (τ λ : ℝ) : SignedPoint := ⟨p.a+λ,p.y+λ*τ⟩

@[simp] theorem ray_zero (p : SignedPoint) (τ : ℝ) : ray p τ 0=p := by
  cases p
  simp [ray]

theorem ray_sorted {p : SignedPoint} {τ λ : ℝ}
    (hp : p.Sorted) (hτ : |τ|≤1) (hλ : 0≤λ) : (ray p τ λ).Sorted := by
  have hab := abs_add p.y (λ*τ)
  rw [abs_mul,abs_of_nonneg hλ] at hab
  have hm := mul_le_mul_of_nonneg_left hτ hλ
  exact ⟨by dsimp [ray]; linarith [hp.1],by dsimp [ray]; linarith [hp.2]⟩

/-- Quantitative Lipschitz loss of the positive transverse excess. -/
theorem excess_loss_bound (y τ λ : ℝ) (hλ : 0≤λ) (hτ : |τ|≤1) :
    max (|y|-1/2) 0 - max (|y+λ*τ|-1/2) 0 ≤ λ := by
  have hab := abs_sub_abs_le_abs_sub y (y+λ*τ)
  have he : y-(y+λ*τ)= -(λ*τ) := by ring
  rw [he,abs_neg,abs_mul,abs_of_nonneg hλ] at hab
  have hm := mul_le_mul_of_nonneg_left hτ hλ
  by_cases hy : |y|≤1/2
  · rw [max_eq_right (by linarith : |y|-1/2≤0)]
    linarith [le_max_right (|y+λ*τ|-1/2) 0]
  · rw [max_eq_left (by linarith : 0≤|y|-1/2)]
    have hmax := le_max_left (|y+λ*τ|-1/2) 0
    linarith

/-- The same squared-distance comparison proves core and circle monotonicity.
It allows the transverse magnitude to decrease and pass through zero. -/
theorem cone_square_mono {A b b' λ : ℝ}
    (hA : 0≤A) (hb : 0≤b) (hba : b≤A) (hb' : 0≤b')
    (hλ : 0≤λ) (hloss : b-b'≤λ) :
    A^2+b^2≤(A+λ)^2+b'^2 := by
  by_cases hbb : b≤b'
  · have hsq := pow_le_pow_left₀ hb hbb 2
    nlinarith
  · have hdiff : 0≤b-b' := by linarith
    have h₁ := mul_le_mul_of_nonneg_right hloss (show 0≤b+b' by linarith)
    have h₂ := mul_le_mul_of_nonneg_left
      (show b+b'≤2*A by linarith) hλ
    nlinarith [sq_nonneg λ]

theorem core_nondec {p : SignedPoint} {τ λ : ℝ}
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hτ : |τ|≤1) (hλ : 0≤λ) :
    p.coreDistance≤(ray p τ λ).coreDistance := by
  have ha := SignedPoint.primary_gt_half hp hcore
  have hsmall : max (|p.y|-1/2) 0≤p.a-1/2 :=
    max_le (by linarith [hp.2]) (by linarith)
  have hsq := cone_square_mono (by linarith : 0≤p.a-1/2)
    (le_max_right (|p.y|-1/2) 0) hsmall
    (le_max_right (|p.y+λ*τ|-1/2) 0) hλ
    (excess_loss_bound p.y τ λ hλ hτ)
  simpa [SignedPoint.coreDistance,ray,
    max_eq_left (by linarith : 0≤p.a-1/2),
    max_eq_left (by linarith : 0≤p.a+λ-1/2)] using hsq

theorem circle_nondec {p : SignedPoint} {τ λ : ℝ}
    (hp : p.Sorted) (hτ : |τ|≤1) (hλ : 0≤λ) :
    p.circle≤(ray p τ λ).circle := by
  have hab := abs_sub_abs_le_abs_sub p.y (p.y+λ*τ)
  have he : p.y-(p.y+λ*τ)= -(λ*τ) := by ring
  rw [he,abs_neg,abs_mul,abs_of_nonneg hλ] at hab
  have hm := mul_le_mul_of_nonneg_left hτ hλ
  have hsq := cone_square_mono (by linarith [hp.1] : 0≤p.a+1/2)
    (by positivity : 0≤|p.y|+1/2)
    (by linarith [hp.2] : |p.y|+1/2≤p.a+1/2)
    (by positivity : 0≤|p.y+λ*τ|+1/2) hλ (by linarith)
  simpa [SignedPoint.circle,ray] using hsq

/-- A bounded circle has an actual intersection with every such outward ray. -/
theorem exists_outer {q : ℝ} {p : SignedPoint} {τ : ℝ}
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (hτ : |τ|≤1) :
    ∃ λ : ℝ, 0≤λ ∧ (ray p τ λ).Sorted ∧ (ray p τ λ).Outer q ∧
      (ray p τ λ).AvoidsCore ∧
      ∀ μ∈Icc 0 λ, (ray p τ μ).Contained q ∧ (ray p τ μ).AvoidsCore := by
  have hq : 0≤q := p.circle_nonneg.trans hc
  let L : ℝ := Real.sqrt q+1
  have hL : 0<L := by dsimp [L]; positivity
  have hs := Real.sq_sqrt hq
  have hn := Real.sqrt_nonneg q
  have hbig : q≤(ray p τ L).circle := by
    dsimp [ray,SignedPoint.circle,L]
    nlinarith [hp.1,sq_nonneg (|p.y+(Real.sqrt q+1)*τ|+1/2)]
  have hcont : ContinuousOn (fun λ => (ray p τ λ).circle) (Icc 0 L) := by
    dsimp [ray,SignedPoint.circle]
    fun_prop
  obtain ⟨λ,hλ,heq⟩ := intermediate_value_Icc hL.le hcont
    (show q∈Icc ((ray p τ 0).circle) ((ray p τ L).circle) from
      ⟨by simpa using hc,hbig⟩)
  refine ⟨λ,hλ.1,ray_sorted hp hτ hλ.1,heq,?_,?_⟩
  · exact hcore.trans (core_nondec hp hcore hτ hλ.1)
  · intro μ hμ
    have hμs := ray_sorted hp hτ hμ.1
    have hμcore : (ray p τ μ).AvoidsCore :=
      hcore.trans (core_nondec hp hcore hτ hμ.1)
    have hid : ray (ray p τ μ) τ (λ-μ)=ray p τ λ := by
      ext <;> dsimp [ray] <;> ring
    have hmono := circle_nondec hμs hτ (sub_nonneg.mpr hμ.2)
    rw [hid,heq] at hmono
    exact ⟨hmono,hμcore⟩

/-- All signed small angles have a slope strictly inside the sorted cone. -/
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
    · have hh := (transport_trig ⟨by linarith,by simpa [abs_of_nonpos h] using hu⟩).2.2.1
      rw [abs_of_nonpos h,Real.sin_neg]
      simpa only [Real.sin_neg] using (abs_of_nonpos (by linarith : Real.sin u≤0)).symm
  rw [hec,hes] at hc hsc
  refine ⟨by linarith,hsc,?_⟩
  rw [Real.tan_eq_sin_div_cos,abs_div,abs_of_pos (by linarith : 0<Real.cos u)]
  exact (div_lt_one (by linarith)).mpr hsc

/-- Both originally selected projections are retained on the entire entry ray. -/
theorem primary_outer_entry {q A B u v : ℝ} {p : SignedPoint}
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (hu : |u|≤frameCap) (ht : u+v∈Ioc 0 (7/10 : ℝ))
    (hfirst : edgeWidth u≤A+p.a*Real.sin u-p.y*Real.cos u)
    (hsecond : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+B) :
    ∃ p' : SignedPoint, p'.Sorted ∧ p'.Outer q ∧ p'.AvoidsCore ∧
      edgeWidth u≤A+p'.a*Real.sin u-p'.y*Real.cos u ∧
      edgeWidth v≤p'.a*Real.sin v+p'.y*Real.cos v+B := by
  obtain ⟨hcos,hs,hτ⟩ := signed_trig hu
  obtain ⟨λ,hλ,hps,hpo,hpc,hpath⟩ := exists_outer hp hcore hc hτ.le
  have hid := primary_affine_projection_identities p.a p.y A B u v λ (ne_of_gt hcos)
  have htotal : 0<Real.sin (u+v) := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [Real.pi_gt_three,ht.2])
  have hgain : 0≤λ*Real.sin (u+v)/Real.cos u :=
    div_nonneg (mul_nonneg hλ htotal.le) hcos.le
  refine ⟨ray p (Real.tan u) λ,hps,hpo,hpc,?_,?_⟩
  · dsimp [ray]
    rwa [hid.1]
  · dsimp [ray]
    rw [hid.2]
    linarith

end AffineCircleEntry
end SquaresInCircles.Eight.TableFree