module

public import Mathlib.Topology.Order.IntermediateValue
public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcentration
public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: signed concentration after both primary signs are removed

The scalar block functions of `Data` may include a clipped support minorant or a minimum of two
negative charges. Both sign totals are concentrated at indices that were occupied
(`concentrated_sum`, `occupied_both_signs`). The remaining one-dimensional interval has the caps
`h - t` and `h - s`, and includes the junction `t = s` without a strict sign hypothesis
(`line_domain`, `lower_from_endpoints`).
-/

section
/-!
## Reaching the circle with one primary projection fixed

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
end
end
end

section
/-!
## The coefficient of a single negative ordinary angle

An anchor with one ordinary angle has its own negative coefficient `nu`, which can be strictly
smaller than the larger force coefficient (`Vnu`). Its negative curvature is controlled on the
whole interval by the curvature at zero (`Vnu_second_lt`, `Vnu_concave`). The anchors with two
angles keep the mixed block (`pure`, `F`), and a single angle has the minorant `single_minorant`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SingleAngleConcavity
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryAngleConcentration ActualOrdinaryBlocks

def Vnu (R p q nu s : ℝ) : ℝ :=
  nu*(Real.cos s-1)-R*(pairNorm p q (-s)-pairNorm p q 0)

def VnuDeriv (R p q nu s : ℝ) : ℝ :=
  -nu*Real.sin s+R*normD1 p q (-s)

@[simp] theorem Vnu_zero (R p q nu : ℝ) : Vnu R p q nu 0=0 := by simp [Vnu]
@[simp] theorem Vnu_larger (R p q s : ℝ) : Vnu R p q q s=V R p q s := rfl

theorem Vnu_ge_V {R p q nu s : ℝ} (hnu : nu≤q) :
    V R p q s≤Vnu R p q nu s := by
  have hh := mul_le_mul_of_nonpos_right hnu
    (show Real.cos s-1≤0 by linarith [Real.cos_le_one s])
  dsimp [V,Vnu]
  linarith

theorem Vnu_hasDerivAt {R p q nu s : ℝ} (hp : 0<p) (hq : 0<q)
    (hs : s∈Icc 0 frameCap) : HasDerivAt (Vnu R p q nu) (VnuDeriv R p q nu s) s := by
  have hn : HasDerivAt (fun x => pairNorm p q (-x)) (normD1 p q (-s)*(-1)) s :=
    (pairNorm_hasDerivAt (t := -s) hp hq
      (by rw [abs_neg,abs_of_nonneg hs.1]; exact hs.2)).comp s (hasDerivAt_neg s)
  have hh := (((Real.hasDerivAt_cos s).sub_const 1).const_mul nu).sub
    ((hn.sub_const (pairNorm p q 0)).const_mul R)
  convert hh using 1
  · rfl
  · unfold VnuDeriv
    ring

theorem VnuDeriv_hasDerivAt {R p q nu s : ℝ} (hp : 0<p) (hq : 0<q)
    (hs : s∈Icc 0 frameCap) :
    HasDerivAt (VnuDeriv R p q nu) (curvature R p q (-s)-nu*Real.cos s) s := by
  have hn : HasDerivAt (fun x => normD1 p q (-x)) (normD2 p q (-s)*(-1)) s :=
    (normD1_hasDerivAt (t := -s) hp hq
      (by rw [abs_neg,abs_of_nonneg hs.1]; exact hs.2)).comp s (hasDerivAt_neg s)
  convert ((Real.hasDerivAt_sin s).const_mul (-nu)).add (hn.const_mul R) using 1
  · rfl
  · unfold curvature
    ring

/-- The curvature bound `curvature R p q (-s) - nu cos s < -(7/2500) p`, which needs `nu` to
dominate only the smaller force coefficient `p`; no second ordinary angle enters. -/
theorem Vnu_second_lt {R p q nu s : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu)
    (hs : s∈Icc 0 frameCap) :
    curvature R p q (-s)-nu*Real.cos s< -(7/2500)*p := by
  have hc := (curvature_constant_bounds hR hQ hp hpq hqp).1
  have hm := curvature_negative_upper hR hp (hp.trans_le hpq)
    (show -s∈Icc (-frameCap) 0 by constructor <;> linarith [hs.1,hs.2])
  have hcos := (transport_trig hs).1
  have hnucos := mul_le_mul_of_nonneg_right hnu (show 0≤Real.cos s by linarith)
  have hpcos := mul_lt_mul_of_pos_left hcos hp
  linarith

theorem Vnu_concave {R p q nu : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu) :
    ConcaveOn ℝ (Icc 0 frameCap) (Vnu R p q nu) := by
  apply concave_of_deriv2
    (fun s hs => Vnu_hasDerivAt hp (hp.trans_le hpq) hs)
    (fun s hs => VnuDeriv_hasDerivAt hp (hp.trans_le hpq) hs)
  intro s hs
  linarith [Vnu_second_lt hR hQ hp hpq hqp hnu hs]

def pure (single : Bool) (R p q nu N : ℝ) : ℝ :=
  if single then Vnu R p q nu N else V R p q N

def F (single : Bool) (R p q nu P N : ℝ) : ℝ :=
  if single then U R p q P+Vnu R p q nu N else mixedBlock R p q P N

@[simp] theorem pure_zero (single : Bool) (R p q nu : ℝ) : pure single R p q nu 0=0 := by
  cases single <;> simp [pure]
@[simp] theorem F_zero_left (single : Bool) (R p q nu N : ℝ) :
    F single R p q nu 0 N=pure single R p q nu N := by cases single <;> simp [F,pure]
@[simp] theorem F_zero_right (single : Bool) (R p q nu P : ℝ) :
    F single R p q nu P 0=U R p q P := by cases single <;> simp [F]
@[simp] theorem F_zero (single : Bool) (R p q nu : ℝ) : F single R p q nu 0 0=0 := by simp

theorem pure_concave {single : Bool} {R p q nu : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hnu : p≤nu) : ConcaveOn ℝ (Icc 0 frameCap) (pure single R p q nu) := by
  cases single
  · exact V_concave hR hQ hp hpq hqp
  · exact Vnu_concave hR hQ hp hpq hqp hnu

theorem F_concave_P {single : Bool} {R p q nu N : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => F single R p q nu P N) := by
  cases single
  · exact mixedBlock_concave_positive hR hQ hp hpq hqp hN
  · exact (U_concave hR hQ hp hpq hqp).add_const (Vnu R p q nu N)

theorem F_concave_N {single : Bool} {R p q nu P : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap) (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hnu : p≤nu) (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (F single R p q nu P) := by
  cases single
  · exact mixedBlock_concave_negative hR hQ hp hpq hqp hP
  · have hF : F true R p q nu P=fun N => U R p q P+Vnu R p q nu N := by
      funext N; simp [F]
    rw [hF]
    exact (concaveOn_const (U R p q P) (convex_Icc _ _)).add (Vnu_concave hR hQ hp hpq hqp hnu)

/-- For a single angle its positive and negative parts are not both nonzero; the negative
coefficient `nu` stays exact, and only the positive coefficient is bounded below by the smaller
pair coefficient. -/
theorem single_minorant {R p q nu d : ℝ} (hpnu : p≤nu)
    (hd : |d|≤frameCap) :
    F true R p q nu (positivePart d) (negativePart d)≤
      nu*psi d-R*(pairNorm p q d-pairNorm p q 0) := by
  by_cases hd0 : 0≤d
  · have hP : positivePart d=d := max_eq_left hd0
    have hN : negativePart d=0 := max_eq_right (by linarith)
    have hphi := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi ⟨hd0,(le_abs_self d).trans hd⟩)
    have hm := mul_le_mul_of_nonneg_right hpnu hphi
    rw [hP,hN,F_zero_right,psi_positive ⟨hd0,(le_abs_self d).trans hd⟩]
    dsimp [U]
    linarith
  · have hn : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hP : positivePart d=0 := max_eq_right (le_of_lt (lt_of_not_ge hd0))
    have hN : negativePart d= -d := max_eq_left hn.1
    rw [hP,hN,F_zero_left]
    have hpsi := psi_negative hn
    simp only [neg_neg] at hpsi
    simp [pure,Vnu,hpsi]

end SquaresInCircles.Eight.SingleAngleConcavity
end
end
end

section
/-!
## Concentration that respects the anchors with one ordinary angle

A positive total can be concentrated at an index where the mass was positive
(`support_concentrates`). Applied to each sign, this keeps an anchor with one angle from receiving
both signs (`both_signs`), so only the anchors with two angles need the comparison of endpoints in
the same block (`lower_from_endpoints`). Zero total is included.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.SingleAngleConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity

/-- A positive simplex total concentrates at a member of its support without increasing the
concave sum; the proof is the finite chord inequality on that support. -/
theorem support_concentrates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (x : ι → ℝ) {h : ℝ}
    (hx : ∀ i,0≤x i) (hpos : 0<∑ i,x i) (hbound : (∑ i,x i)≤h)
    (hf : ∀ i,ConcaveOn ℝ (Icc 0 h) (f i)) :
    ∃ j,0<x j ∧ (∑ i,f i (massAt j (∑ a,x a) i))≤∑ i,f i (x i) := by
  classical
  let T := ∑ i,x i
  let S : Finset ι := Finset.univ.filter (fun i => 0<x i)
  let a (i : ι) := f i T-f i 0
  have hT : 0<T := hpos
  have hxT (i : ι) : x i≤T := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  have hex : ∃ i,0<x i := by
    by_contra hn
    push Not at hn
    have hs : (∑ i,x i)≤0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,by simp [S,hi]⟩
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S a hS
  have hjpos : 0<x j := (Finset.mem_filter.mp hj).2
  have hc (i : ι) : 0≤x i/T ∧ x i/T≤1 :=
    ⟨div_nonneg (hx i) hT.le,(div_le_one hT).2 (hxT i)⟩
  have hchord (i : ι) : f i 0+(x i/T)*a i≤f i (x i) := by
    have hh := (hf i).2
      (show (0:ℝ)∈Icc 0 h from ⟨le_rfl,hT.le.trans hbound⟩)
      (show T∈Icc 0 h from ⟨hT.le,hbound⟩)
      (sub_nonneg.mpr (hc i).2) (hc i).1 (by ring)
    have he : (1-x i/T)*0+(x i/T)*T=x i := by field_simp [hT.ne']; ring
    simp only [smul_eq_mul,he] at hh
    dsimp [a]
    nlinarith only [hh]
  have hterm (i : ι) : f i 0+(x i/T)*a j≤f i (x i) := by
    by_cases hi : 0<x i
    · have hm := mul_le_mul_of_nonneg_left (hmin i (by simp [S,hi])) (hc i).1
      linarith [hchord i]
    · have hz : x i=0 := by linarith [hx i]
      simp [hz]
  have hsumcoeff : (∑ i,x i/T)=1 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change T*T⁻¹=1
    exact mul_inv_cancel₀ hT.ne'
  have hsumleft : (∑ i,(f i 0+(x i/T)*a j))=(∑ i,f i 0)+a j := by
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hsumcoeff,one_mul]
  have hsumright : (∑ i,f i (massAt j T i))=(∑ i,f i 0)+a j := by
    have he (i : ι) : f i (massAt j T i)=f i 0+if i=j then a j else 0 := by
      by_cases hi : i=j
      · subst i; simp [massAt,a]
      · simp [massAt,hi]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp
  refine ⟨j,hjpos,?_⟩
  rw [hsumright,← hsumleft]
  exact Finset.sum_le_sum (fun i _ => hterm i)

theorem concentrated_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → Bool) (R : ℝ) (p q nu : ι → ℝ) (i j : ι) (P N : ℝ) :
    (∑ a,F (m a) R (p a) (q a) (nu a) (massAt i P a) (massAt j N a))=
      if i=j then F (m i) R (p i) (q i) (nu i) P N
      else U R (p i) (q i) P+pure (m j) R (p j) (q j) (nu j) N := by
  by_cases hij : i=j
  · subst j
    have he (a : ι) : F (m a) R (p a) (q a) (nu a) (massAt i P a) (massAt i N a)=
        if a=i then F (m i) R (p i) (q i) (nu i) P N else 0 := by
      by_cases hai : a=i
      · subst a; simp [massAt]
      · simp [massAt,hai]
    simp_rw [he]
    simp
  · have he (a : ι) : F (m a) R (p a) (q a) (nu a) (massAt i P a) (massAt j N a)=
        (if a=i then U R (p i) (q i) P else 0)+
        (if a=j then pure (m j) R (p j) (q j) (nu j) N else 0) := by
      by_cases hai : a=i
      · subst a; simp [massAt,hij]
      · by_cases haj : a=j
        · subst a; simp [massAt,hai]
        · simp [massAt,hai,haj]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hij]

/-- If both totals are positive, concentration does not put them together at an anchor with a
single angle: each total lands in its own support. -/
theorem both_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → Bool) (R : ℝ) (p q nu P N : ι → ℝ)
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hnu : ∀ i,p i≤nu i) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hPpos : 0<∑ i,P i) (hNpos : 0<∑ i,N i)
    (hPt : (∑ i,P i)≤frameCap) (hNt : (∑ i,N i)≤frameCap)
    (hsingle : ∀ i,m i=true → P i=0 ∨ N i=0) :
    ∃ i j,(i=j → m i=false) ∧
      (if i=j then F (m i) R (p i) (q i) (nu i) (∑ a,P a) (∑ a,N a)
       else U R (p i) (q i) (∑ a,P a)+pure (m j) R (p j) (q j) (nu j) (∑ a,N a))≤
        ∑ a,F (m a) R (p a) (q a) (nu a) (P a) (N a) := by
  have hPi (i : ι) : P i∈Icc 0 frameCap :=
    ⟨hP i,(Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)).trans hPt⟩
  obtain ⟨j,hjpos,hj⟩ := support_concentrates
    (fun a n => F (m a) R (p a) (q a) (nu a) (P a) n) N hN hNpos hNt
    (fun a => F_concave_N hR hQ (hp a) (hpq a) (hqp a) (hnu a) (hPi a))
  have hNm (a : ι) : massAt j (∑ b,N b) a∈Icc 0 frameCap := massAt_mem ⟨hNpos.le,hNt⟩
  obtain ⟨i,hipos,hi⟩ := support_concentrates
    (fun a p' => F (m a) R (p a) (q a) (nu a) p' (massAt j (∑ b,N b) a))
    P hP hPpos hPt (fun a => F_concave_P hR hQ (hp a) (hpq a) (hqp a) (hNm a))
  refine ⟨i,j,?_,?_⟩
  · intro hij
    subst j
    cases hm : m i
    · rfl
    · rcases hsingle i hm with hz | hz
      · linarith
      · linarith
  · rw [concentrated_sum] at hi
    exact hi.trans hj

theorem separated_concave {single : Bool} {R p q p' q' nu t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p') (hnu : p'≤nu)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun P => U R p q P+pure single R p' q' nu (t+P)) := by
  have hU := (U_concave hR hQ hp hpq hqp).subset
    (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
  have hV := concave_affine_argument (pure_concave (single := single) hR hQ hp' hpq' hqp' hnu)
    (a := 1) (b := t) (l := 0) (u := frameCap-t)
    (fun x hx => ⟨by linarith [ht.1,hx.1],by linarith [hx.2]⟩)
  convert hU.add hV using 1
  funext P
  simp only [Pi.add_apply,one_mul,add_comm t]

/-- The endpoint comparisons give a lower bound for every allocation; the same-block premise is
needed only at the anchors with two ordinary angles. -/
theorem lower_from_endpoints {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (m : ι → Bool) (R : ℝ) (p q nu P N : ι → ℝ) {t L : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hnu : ∀ i,p i≤nu i) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (ht : t∈Icc 0 frameCap) (hbudget : (∑ i,P i)≤frameCap-t)
    (hbalance : (∑ i,N i)=t+∑ i,P i)
    (hsingle : ∀ i,m i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,L≤pure (m i) R (p i) (q i) (nu i) t)
    (hmixed : ∀ i,m i=false → L≤M R (p i) (q i) t)
    (hseparated : ∀ i j,i≠j → L≤U R (p i) (q i) (frameCap-t)+
      pure (m j) R (p j) (q j) (nu j) frameCap) :
    L≤∑ i,F (m i) R (p i) (q i) (nu i) (P i) (N i) := by
  have hP0 : 0≤∑ i,P i := Finset.sum_nonneg (fun i _ => hP i)
  have hPt : (∑ i,P i)≤frameCap := by linarith [ht.1]
  have hNt : (∑ i,N i)≤frameCap := by linarith
  by_cases hz : (∑ i,P i)=0
  · have hPi (i : ι) : P i=0 := by
      have hh := Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)
      linarith [hP i]
    have hNeq : (∑ i,N i)=t := by linarith
    obtain ⟨j,hj⟩ := concave_sum_concentrates
      (fun i n => pure (m i) R (p i) (q i) (nu i) n) N hN hNeq ht.2
      (fun i => pure_concave hR hQ (hp i) (hpq i) (hqp i) (hnu i))
    have hsum : (∑ i,pure (m i) R (p i) (q i) (nu i) (massAt j t i))=
        pure (m j) R (p j) (q j) (nu j) t := by
      simp only [massAt,apply_ite,pure_zero]
      simp
    rw [hsum] at hj
    have heq : (∑ i,F (m i) R (p i) (q i) (nu i) (P i) (N i))=
        ∑ i,pure (m i) R (p i) (q i) (nu i) (N i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hPi i,F_zero_left]
    rw [heq]
    exact (hpure j).trans hj
  · have hPpos : 0<∑ i,P i := lt_of_le_of_ne hP0 (Ne.symm hz)
    have hNpos : 0<∑ i,N i := by linarith [ht.1]
    obtain ⟨i,j,htwo,hij⟩ := both_signs m R p q nu P N hR hQ hp hpq hqp hnu
      hP hN hPpos hNpos hPt hNt hsingle
    have htotal : (∑ i,P i)∈Icc 0 (frameCap-t) := ⟨hP0,hbudget⟩
    have hspan : 0≤frameCap-t := by linarith [ht.2]
    by_cases he : i=j
    · subst j
      have hm : m i=false := htwo rfl
      simp only [↓reduceIte] at hij
      rw [show F (m i) R (p i) (q i) (nu i) (∑ a,P a) (∑ a,N a)=
        mixedBlock R (p i) (q i) (∑ a,P a) (∑ a,N a) by simp [F,hm],hbalance] at hij
      have hc := sameBlockLine_concave (R := R) (hp i).le ((hp i).trans_le (hpq i)).le ht
      have hmin := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,mixedBlock_zero_left,mixedBlock_saturated] at hmin
      have hpure' : L≤V R (p i) (q i) t := by simpa [SingleAngleConcavity.pure,hm] using hpure i
      exact (le_min hpure' (hmixed i hm)).trans (hmin.trans hij)
    · simp only [he,↓reduceIte] at hij
      rw [hbalance] at hij
      have hc := separated_concave (single := m j) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) (hnu j) ht
      have hmin := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [U_zero,zero_add,add_zero,show t+(frameCap-t)=frameCap by ring] at hmin
      exact (le_min (hpure j) (hseparated i j he)).trans (hmin.trans hij)

end SquaresInCircles.Eight.SingleAngleConcentration
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.OccupiedSignedConcentration
open OrdinaryAngleConcavity OrdinaryAngleConcentration

structure Data (ι : Type*) where
  U : ι → ℝ → ℝ
  V : ι → ℝ → ℝ
  F : ι → ℝ → ℝ → ℝ
  single : ι → Bool
  U_zero : ∀ i,U i 0=0
  V_zero : ∀ i,V i 0=0
  F_left : ∀ i N,F i 0 N=V i N
  F_right : ∀ i P,F i P 0=U i P
  U_concave : ∀ i,ConcaveOn ℝ (Icc 0 frameCap) (U i)
  V_concave : ∀ i,ConcaveOn ℝ (Icc 0 frameCap) (V i)
  F_concave_P : ∀ i N,N∈Icc 0 frameCap →
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => F i P N)
  F_concave_N : ∀ i P,P∈Icc 0 frameCap →
    ConcaveOn ℝ (Icc 0 frameCap) (F i P)

namespace Data

@[simp] theorem F_zero {ι : Type*} (D : Data ι) (i : ι) : D.F i 0 0=0 := by
  rw [D.F_left,D.V_zero]

theorem concentrated_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (i j : ι) (P N : ℝ) :
    (∑ a,D.F a (massAt i P a) (massAt j N a))=
      if i=j then D.F i P N else D.U i P+D.V j N := by
  by_cases hij : i=j
  · subst j
    have he (a : ι) : D.F a (massAt i P a) (massAt i N a)=
        if a=i then D.F i P N else 0 := by
      by_cases hai : a=i
      · subst a; simp [massAt]
      · simp [massAt,hai]
    simp_rw [he]
    simp
  · have he (a : ι) : D.F a (massAt i P a) (massAt j N a)=
        (if a=i then D.U i P else 0)+(if a=j then D.V j N else 0) := by
      by_cases hai : a=i
      · subst a; simp [massAt,hij,D.F_right]
      · by_cases haj : a=j
        · subst a; simp [massAt,hai,D.F_left]
        · simp [massAt,hai,haj]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hij]

theorem occupied_both_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (P N : ι → ℝ)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hPpos : 0<∑ i,P i) (hNpos : 0<∑ i,N i)
    (hPt : (∑ i,P i)≤frameCap) (hNt : (∑ i,N i)≤frameCap)
    (hsingle : ∀ i,D.single i=true → P i=0 ∨ N i=0) :
    ∃ i j,(i=j → D.single i=false) ∧
      (if i=j then D.F i (∑ a,P a) (∑ a,N a)
       else D.U i (∑ a,P a)+D.V j (∑ a,N a))≤∑ a,D.F a (P a) (N a) := by
  have hPi (i : ι) : P i∈Icc 0 frameCap :=
    ⟨hP i,(Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)).trans hPt⟩
  obtain ⟨j,hjpos,hj⟩ := SingleAngleConcentration.support_concentrates
    (fun a n => D.F a (P a) n) N hN hNpos hNt
    (fun a => D.F_concave_N a (P a) (hPi a))
  have hNm (a : ι) : massAt j (∑ b,N b) a∈Icc 0 frameCap :=
    massAt_mem ⟨hNpos.le,hNt⟩
  obtain ⟨i,hipos,hi⟩ := SingleAngleConcentration.support_concentrates
    (fun a p => D.F a p (massAt j (∑ b,N b) a)) P hP hPpos hPt
    (fun a => D.F_concave_P a _ (hNm a))
  refine ⟨i,j,?_,?_⟩
  · intro hij
    subst j
    cases hm : D.single i
    · rfl
    · rcases hsingle i hm with hz | hz <;> linarith
  · rw [D.concentrated_sum] at hi
    exact hi.trans hj

theorem line_domain {t s : ℝ} (ht : t∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) :
    max 0 (s-t)≤frameCap-t ∧
      ∀ P∈Icc (max 0 (s-t)) (frameCap-t),
        P∈Icc 0 frameCap ∧ t-s+P∈Icc 0 frameCap := by
  refine ⟨max_le (by linarith [ht.2]) (by linarith [hs.2]),?_⟩
  intro P hP
  have hP0 := (le_max_left (0:ℝ) (s-t)).trans hP.1
  have hdiff := (le_max_right (0:ℝ) (s-t)).trans hP.1
  exact ⟨⟨hP0,by linarith [hP.2,ht.1]⟩,
    ⟨by linarith,by linarith [hP.2,hs.1]⟩⟩

theorem separated_line {ι : Type*} (D : Data ι) (i j : ι) {t s : ℝ}
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t))
      (fun P => D.U i P+D.V j (t-s+P)) := by
  have hdom := line_domain ht hs
  have hU := (D.U_concave i).subset
    (fun P hP => (hdom.2 P hP).1) (convex_Icc _ _)
  have hV := concave_affine_argument (D.V_concave j)
    (a:=1) (b:=t-s) (l:=max 0 (s-t)) (u:=frameCap-t)
    (fun P hP => by simpa only [one_mul,add_comm P] using (hdom.2 P hP).2)
  have hfun : (fun P => D.U i P+D.V j (t-s+P))=
      D.U i+(fun x => D.V j (1*x+(t-s))) := by
    funext P
    simp only [Pi.add_apply,one_mul,add_comm P]
  rw [hfun]
  exact hU.add hV

/-- Every allocation is bounded below through the pure-sign junction or one of the two saturated
alternatives; the concavity along the mixed line is used only at an index that carried both
signs. -/
theorem lower_from_endpoints {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (D : Data ι) (P N : ι → ℝ) {t s L : ℝ}
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hbudget : (∑ i,P i)≤frameCap-t) (hbalance : (∑ i,N i)=t-s+∑ i,P i)
    (hsingle : ∀ i,D.single i=true → P i=0 ∨ N i=0)
    (hline : ∀ i,D.single i=false →
      ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t))
        (fun P => D.F i P (t-s+P)))
    (hnegative : s≤t → ∀ i,L≤D.V i (t-s))
    (hpositive : t≤ s → ∀ i,L≤D.U i (s-t))
    (hmixed : ∀ i,D.single i=false → L≤D.F i (frameCap-t) (frameCap-s))
    (hseparated : ∀ i j,i≠j → L≤D.U i (frameCap-t)+D.V j (frameCap-s)) :
    L≤∑ i,D.F i (P i) (N i) := by
  have hP0 : 0≤∑ i,P i := Finset.sum_nonneg (fun i _ => hP i)
  have hN0 : 0≤∑ i,N i := Finset.sum_nonneg (fun i _ => hN i)
  have hPt : (∑ i,P i)≤frameCap := by linarith [ht.1]
  have hNt : (∑ i,N i)≤frameCap := by linarith [hs.1]
  by_cases hzP : (∑ i,P i)=0
  · have hPi (i : ι) : P i=0 := by
      have hh := Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)
      linarith [hP i]
    have hNeq : (∑ i,N i)=t-s := by linarith
    have hst : s≤t := by linarith
    obtain ⟨j,hj⟩ := concave_sum_concentrates D.V N hN hNeq
      (by linarith [ht.2,hs.1] : t-s≤frameCap) D.V_concave
    have hsum : (∑ i,D.V i (massAt j (t-s) i))=D.V j (t-s) := by
      simp only [massAt,apply_ite,D.V_zero]
      simp
    rw [hsum] at hj
    calc
      L≤D.V j (t-s) := hnegative hst j
      _≤∑ i,D.V i (N i) := hj
      _=∑ i,D.F i (P i) (N i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hPi i,D.F_left]
  by_cases hzN : (∑ i,N i)=0
  · have hNi (i : ι) : N i=0 := by
      have hh := Finset.single_le_sum (fun a _ => hN a) (Finset.mem_univ i)
      linarith [hN i]
    have hPeq : (∑ i,P i)=s-t := by linarith
    have hts : t≤ s := by linarith
    obtain ⟨i,hi⟩ := concave_sum_concentrates D.U P hP hPeq
      (by linarith [hs.2,ht.1] : s-t≤frameCap) D.U_concave
    have hsum : (∑ j,D.U j (massAt i (s-t) j))=D.U i (s-t) := by
      simp only [massAt,apply_ite,D.U_zero]
      simp
    rw [hsum] at hi
    calc
      L≤D.U i (s-t) := hpositive hts i
      _≤∑ j,D.U j (P j) := hi
      _=∑ j,D.F j (P j) (N j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hNi j,D.F_right]
  have hPpos : 0<∑ i,P i := lt_of_le_of_ne hP0 (Ne.symm hzP)
  have hNpos : 0<∑ i,N i := lt_of_le_of_ne hN0 (Ne.symm hzN)
  obtain ⟨i,j,htwo,hij⟩ := D.occupied_both_signs P N hP hN
    hPpos hNpos hPt hNt hsingle
  have hspan := (line_domain ht hs).1
  have htotal : (∑ i,P i)∈Icc (max 0 (s-t)) (frameCap-t) :=
    ⟨max_le hP0 (by linarith),hbudget⟩
  have hleft : max 0 (s-t)∈Icc (max 0 (s-t)) (frameCap-t) := ⟨le_rfl,hspan⟩
  have hright : frameCap-t∈Icc (max 0 (s-t)) (frameCap-t) := ⟨hspan,le_rfl⟩
  by_cases he : i=j
  · subst j
    have hm : D.single i=false := htwo rfl
    simp only at hij
    rw [hbalance] at hij
    have hpure : L≤D.F i (max 0 (s-t)) (t-s+max 0 (s-t)) := by
      by_cases hst : s≤t
      · rw [max_eq_left (by linarith : s-t≤0),add_zero,D.F_left]
        exact hnegative hst i
      · have hts : t≤ s := (lt_of_not_ge hst).le
        rw [max_eq_right (by linarith : 0≤ s-t),
          show t-s+(s-t)=0 by ring,D.F_right]
        exact hpositive hts i
    have hfar := hmixed i hm
    have hmin := (hline i hm).min_le_of_mem_Icc hleft hright htotal
    rw [show t-s+(frameCap-t)=frameCap-s by ring] at hmin
    exact (le_min hpure hfar).trans (hmin.trans hij)
  · simp only [he,↓reduceIte] at hij
    rw [hbalance] at hij
    have hpure : L≤D.U i (max 0 (s-t))+D.V j (t-s+max 0 (s-t)) := by
      by_cases hst : s≤t
      · rw [max_eq_left (by linarith : s-t≤0),add_zero,D.U_zero,zero_add]
        exact hnegative hst j
      · have hts : t≤ s := (lt_of_not_ge hst).le
        rw [max_eq_right (by linarith : 0≤ s-t),
          show t-s+(s-t)=0 by ring,D.V_zero,add_zero]
        exact hpositive hts i
    have hmin := (D.separated_line i j ht hs).min_le_of_mem_Icc hleft hright htotal
    rw [show t-s+(frameCap-t)=frameCap-s by ring] at hmin
    exact (le_min hpure (hseparated i j he)).trans (hmin.trans hij)

end Data

end SquaresInCircles.Eight.OccupiedSignedConcentration
end
end
end
