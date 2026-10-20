module

public import SquaresInCircles.Eight.TableFree.PairedPrimaryScalars

/-!
# Positive paired-primary endpoints on the original circle

Uncompiled draft. A continuous cost is minimized over the single compact
contact rectangle. Its minimum is either an actual alignment, an actual
zero tangent, or an actual positive diagonal. An interior point of either
signed contact arc is excluded by the preceding whole-interval curvature
bounds. This avoids imposing concavity across the sign junction.

The diagonal remains an explicit alternative until the global nearest-axis
theorem is applied. The zero-tangent alternative is treated in the companion
module. No global exclusion is smuggled into this local theorem.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace PairedPrimary

abbrev arc (q y : ℝ) : SignedPoint := SignedPoint.outerAt q y

def contact (q B u y : ℝ) : ℝ :=
  B+(arc q y).a*Real.sin u-y*Real.cos u-edgeWidth u

def required (q t u y : ℝ) : ℝ :=
  edgeWidth (t-u)-(arc q y).a*Real.sin (t-u)-y*Real.cos (t-u)

theorem eq_outerAt_of_outer {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (ho : p.Outer q) : p=arc q p.y := by
  have hp : 0≤p.a+1/2 := by linarith [hs.1]
  have hr : q-(|p.y|+1/2)^2=(p.a+1/2)^2 := by
    dsimp [SignedPoint.Outer,SignedPoint.circle] at ho
    linarith
  cases p
  simp [arc,SignedPoint.outerAt,hr,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]

theorem outer_primary_ge {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hc : p.Contained q) : p.a≤(arc q p.y).a := by
  have hbound : (p.a+1/2)^2≤q-(|p.y|+1/2)^2 := by
    dsimp [SignedPoint.Contained,SignedPoint.circle] at hc
    linarith
  have hrad : 0≤q-(|p.y|+1/2)^2 := (sq_nonneg _).trans hbound
  have hroot := Real.sq_sqrt hrad
  have hnon := Real.sqrt_nonneg (q-(|p.y|+1/2)^2)
  dsimp [arc,SignedPoint.outerAt]
  nlinarith [hs.1]

theorem arc_diagonal {q : ℝ} (hq : qLow≤q) :
    (arc q (diagonalCoordinate q)).a=diagonalCoordinate q ∧
      (arc q (-diagonalCoordinate q)).a=diagonalCoordinate q := by
  have hq0 : 0≤q := by dsimp [qLow] at hq; linarith
  have hroot := Real.sq_sqrt (show 0≤q/2 by positivity)
  have hnon := Real.sqrt_nonneg (q/2)
  have hc : 0≤diagonalCoordinate q := by
    dsimp [diagonalCoordinate,qLow] at *
    nlinarith
  have hrad : q-(diagonalCoordinate q+1/2)^2=q/2 := by
    dsimp [diagonalCoordinate]
    nlinarith
  constructor <;>
    simp [arc,SignedPoint.outerAt,abs_of_nonneg hc,hrad,diagonalCoordinate]

/-- The slope bound on the two circular half-arcs also holds across y=0. -/
theorem arc_lipschitz {q y z : ℝ} (hq : qLow≤q)
    (hy : |y|≤diagonalCoordinate q) (hz : |z|≤diagonalCoordinate q) :
    |(arc q y).a-(arc q z).a|≤|y-z| := by
  obtain ⟨hys,hyo,hycore⟩ := SignedPoint.outerAt_spec hq hy
  obtain ⟨hzs,hzo,hzcore⟩ := SignedPoint.outerAt_spec hq hz
  have hyb : |y|≤(arc q y).a := hys.2
  have hzb : |z|≤(arc q z).a := hzs.2
  have hsum : 0<(arc q y).a+(arc q z).a+1 := by linarith [hys.1,hzs.1]
  have hid : ((arc q y).a-(arc q z).a)*((arc q y).a+(arc q z).a+1)=
      -(|y|-|z|)*(|y|+|z|+1) := by
    dsimp [SignedPoint.Outer,SignedPoint.circle] at hyo hzo
    nlinarith
  have ha := congrArg abs hid
  rw [abs_mul,abs_mul,abs_neg,
    abs_of_pos hsum,abs_of_nonneg (by positivity : 0≤|y|+|z|+1)] at ha
  have hab : ||y|-|z||≤|y-z| := by
    apply abs_le.mpr
    constructor
    · have h := abs_sub_abs_le_abs_sub z y
      rw [abs_sub_comm z y] at h
      linarith
    · exact abs_sub_abs_le_abs_sub y z
  have hmul₁ := mul_le_mul_of_nonneg_right hab (by positivity : 0≤|y|+|z|+1)
  have hmul₂ := mul_le_mul_of_nonneg_left
    (show |y|+|z|+1≤(arc q y).a+(arc q z).a+1 by linarith)
    (abs_nonneg (y-z))
  have hprod : |(arc q y).a-(arc q z).a|*
      ((arc q y).a+(arc q z).a+1)≤
      |y-z|*((arc q y).a+(arc q z).a+1) := by linarith
  exact (mul_le_mul_right hsum).mp hprod

theorem contact_strictAnti {q B u : ℝ} (hq : qLow≤q)
    (hu : u∈Icc 0 (7/10 : ℝ)) :
    StrictAntiOn (contact q B u) (Icc (-diagonalCoordinate q) (diagonalCoordinate q)) := by
  intro y hy z hz hyz
  have hab := arc_lipschitz hq (abs_le.mpr hy) (abs_le.mpr hz)
  have hdiff : (arc q z).a-(arc q y).a≤z-y := by
    rw [abs_sub_comm,abs_of_nonpos hyz.le] at hab
    exact (le_abs_self _).trans hab
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hu
  have hmul := mul_le_mul_of_nonneg_right hdiff hs0
  have hstrict := mul_pos (sub_pos.mpr hyz) (sub_pos.mpr hsc)
  dsimp [contact]
  nlinarith

theorem required_strictAnti {q t u : ℝ} (hq : qLow≤q)
    (hv : t-u∈Icc 0 (7/10 : ℝ)) :
    StrictAntiOn (required q t u) (Icc (-diagonalCoordinate q) (diagonalCoordinate q)) := by
  intro y hy z hz hyz
  have hab := arc_lipschitz hq (abs_le.mpr hy) (abs_le.mpr hz)
  have hdiff : -(z-y)≤(arc q z).a-(arc q y).a := by
    rw [abs_sub_comm,abs_of_nonpos hyz.le] at hab
    exact (abs_le.mp hab).1
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hv
  have hmul := mul_le_mul_of_nonneg_right hdiff hs0
  have hstrict := mul_pos (sub_pos.mpr hyz) (sub_pos.mpr hsc)
  dsimp [required]
  nlinarith

theorem lower_diagonal_strict {q B u : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B) (hu : u∈Icc 0 (7/10 : ℝ)) :
    0<contact q B u (-diagonalCoordinate q) := by
  obtain ⟨hc0,hc1,hA0,hA1⟩ := uniform_circle_reserves hqL hqU
  obtain ⟨hcos,hs0,hs⟩ := transport_trig_coarse hu
  have hsum : 1≤Real.sin u+Real.cos u := by
    have h := one_le_abs_cos_add_abs_sin u
    simpa [abs_of_nonneg hs0,abs_of_pos hcos,add_comm] using h
  have hmul := mul_nonneg
    (show 0≤diagonalCoordinate q-1/2 by linarith) (sub_nonneg.mpr hsum)
  rw [contact,(arc_diagonal hqL).2,edgeWidth_positive_formula hu]
  nlinarith

theorem strict_sorting_of_inner_tangent {q y : ℝ} (hq : qLow≤q)
    (hy : |y|<diagonalCoordinate q) : |y|<(arc q y).a := by
  obtain ⟨hs,ho,hcore⟩ := SignedPoint.outerAt_spec hq hy.le
  have ha := (SignedPoint.outer_bounds hs ho).1
  exact hy.trans_le ha

theorem outerization_preserves_pair {q B D u v : ℝ} {p : SignedPoint}
    (hq : qLow≤q) (hs : p.Sorted) (hc : p.Contained q)
    (hu : u∈Icc 0 (7/10 : ℝ)) (hv : v∈Icc 0 (7/10 : ℝ))
    (h₁ : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (h₂ : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    |p.y|≤diagonalCoordinate q ∧
      0≤contact q B u p.y ∧ required q (u+v) u p.y≤D := by
  have hy := SignedPoint.contained_minor_le_diagonal hs hc
  have ha := outer_primary_ge hs hc
  have hsinu := (transport_trig_coarse hu).2.1
  have hsinv := (transport_trig_coarse hv).2.1
  have hmu := mul_le_mul_of_nonneg_right ha hsinu
  have hmv := mul_le_mul_of_nonneg_right ha hsinv
  refine ⟨hy,?_,?_⟩
  · dsimp [contact]
    linarith
  · simp only [required,add_sub_cancel_left]
    linarith

/-- A positive signed contact in the interior of the rectangle cannot be a
minimum of the required opposite coordinate. The feasible curve is explicit. -/
theorem positive_contact_not_minimum {q B t u y : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (ht : 0<t ∧ t≤7/10) (hu : 0<u ∧ u<t)
    (hy : 0<y ∧ y<diagonalCoordinate q)
    (hc : contact q B u y=0)
    (hmin : ∀ z : ℝ × ℝ, z.1∈Icc 0 t →
      z.2∈Icc (-diagonalCoordinate q) (diagonalCoordinate q) →
      0≤contact q B z.1 z.2 → required q t u y≤required q t z.1 z.2) : False := by
  let P := B-1/2
  have hP : 3/8≤P ∧ P≤183/200 := by
    obtain ⟨hcl,hcu,hal,hau⟩ := uniform_circle_reserves hqL hqU
    dsimp [P,axisCoordinate] at *
    constructor <;> linarith [hB.1,hB.2]
  have hu' : u∈Icc 0 (7/10 : ℝ) := ⟨hu.1.le,by linarith⟩
  have hyabs : |y|<diagonalCoordinate q := by rwa [abs_of_pos hy.1]
  obtain ⟨has,hao,hac⟩ := SignedPoint.outerAt_spec hqL hyabs.le
  have hrecovery : plusCurve q P u=arc q y := by
    apply plusCurve_recovery has hao hy.1.le hu'
    have h := hc
    rw [contact,edgeWidth_positive_formula hu'] at h
    dsimp [P]
    linarith
  let O : Set ℝ := Ioo 0 t ∩ {x | 0<(plusCurve q P x).y} ∩
    {x | |(plusCurve q P x).y|<(plusCurve q P x).a} ∩
    {x | (plusCurve q P x).y∈Ioo (-diagonalCoordinate q) (diagonalCoordinate q)}
  have hcy : Continuous (fun x => (plusCurve q P x).y) := by
    dsimp [plusCurve,rootPlus,zPlus]
    fun_prop
  have hca : Continuous (fun x => (plusCurve q P x).a) := by
    dsimp [plusCurve,rootPlus,zPlus]
    fun_prop
  have hO : IsOpen O := by
    exact ((isOpen_Ioo.inter (isOpen_lt continuous_const hcy)).inter
      (isOpen_lt hcy.abs hca)).inter (isOpen_Ioo.preimage hcy)
  have huO : u∈O := by
    dsimp [O]
    rw [hrecovery]
    exact ⟨⟨⟨hu,hy.1⟩,strict_sorting_of_inner_tangent hqL hyabs⟩,
      ⟨by linarith [(abs_nonneg y)],hy.2⟩⟩
  let region : Set (ℝ × ℝ) := {z | z.1∈Icc 0 t ∧
    z.2∈Icc (-diagonalCoordinate q) (diagonalCoordinate q) ∧ 0≤contact q B z.1 z.2}
  let curve : ℝ → ℝ × ℝ := fun x => (x,(plusCurve q P x).y)
  have hcurve (x : ℝ) (hx : x∈O) :
      plusCurve q P x=arc q (plusCurve q P x).y := by
    obtain ⟨⟨⟨hxt,hxy⟩,hxa⟩,hxb⟩ := hx
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.1
    have hrad : 0≤q-(zPlus P x)^2 := by
      have hroot : 0<rootPlus q P x := by linarith
      exact (Real.sqrt_pos.mp hroot).le
    exact eq_outerAt_of_outer ⟨by linarith [abs_nonneg (plusCurve q P x).y],hxa.le⟩
      (plusCurve_circle hrad hxy.le)
  have hfeasible (x : ℝ) (hx : x∈O) : curve x∈region := by
    obtain ⟨⟨⟨hxt,hxy⟩,hxa⟩,hxb⟩ := hx
    refine ⟨⟨hxt.1.le,hxt.2.le⟩,⟨hxb.1.le,hxb.2.le⟩,?_⟩
    have hc' := plusCurve_contact q P x
    rw [hcurve x hx] at hc'
    rw [contact,edgeWidth_positive_formula ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩]
    dsimp [P] at hc'
    linarith
  apply not_minimum_on_strictly_concave_curve
    (s := region) (cost := fun z => required q t z.1 z.2) (p := (u,y))
    (curve := curve) (value := plusDemand q P t)
    (dvalue := plusDerivative q P t) (ddvalue := plusSecond q P t)
    (x := u) (k := 1/25)
    (fun z hz => hmin z hz.1 hz.2.1 hz.2.2) hO huO (by norm_num)
  · simp [curve,hrecovery,arc,SignedPoint.outerAt]
  · exact hfeasible
  · intro x hx
    obtain ⟨⟨⟨hxt,hxy⟩,hxa⟩,hxb⟩ := hx
    rw [show required q t (curve x).1 (curve x).2=
        edgeWidth (t-x)-(arc q (plusCurve q P x).y).a*Real.sin (t-x)-
          (plusCurve q P x).y*Real.cos (t-x) by rfl]
    rw [← hcurve x hx,edgeWidth_positive_formula ⟨by linarith [hxt.2],by linarith [hxt.1,ht.2]⟩]
    exact plusCurve_demand q P t x
  · intro x hx
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hx.1.1.1.1.le,by linarith [hx.1.1.1.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.1
    exact (plus_derivatives (Real.sqrt_pos.mp (show 0<rootPlus q P x by linarith))).1
  · intro x hx
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hx.1.1.1.1.le,by linarith [hx.1.1.1.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.1
    exact (plus_derivatives (Real.sqrt_pos.mp (show 0<rootPlus q P x by linarith))).2
  · intro x hx
    exact plus_second_negative hqL hqU hP ⟨ht.1.le,ht.2⟩
      ⟨hx.1.1.1.1.le,by linarith [hx.1.1.1.2,ht.2]⟩

/-- The negative half uses its own actual contact curve, not an extension of
positive-branch concavity across y=0. -/
theorem negative_contact_not_minimum {q B t u y : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (ht : 0<t ∧ t≤7/10) (hu : 0<u ∧ u<t)
    (hy : -diagonalCoordinate q<y ∧ y<0)
    (hc : contact q B u y=0)
    (hmin : ∀ z : ℝ × ℝ, z.1∈Icc 0 t →
      z.2∈Icc (-diagonalCoordinate q) (diagonalCoordinate q) →
      0≤contact q B z.1 z.2 → required q t u y≤required q t z.1 z.2) : False := by
  let P := B-1/2
  have hP : 3/8≤P ∧ P≤183/200 := by
    obtain ⟨hcl,hcu,hal,hau⟩ := uniform_circle_reserves hqL hqU
    dsimp [P,axisCoordinate] at *
    constructor <;> linarith [hB.1,hB.2]
  have hu' : u∈Icc 0 (7/10 : ℝ) := ⟨hu.1.le,by linarith⟩
  have hyabs : |y|<diagonalCoordinate q := by rw [abs_of_neg hy.2]; linarith
  obtain ⟨has,hao,hac⟩ := SignedPoint.outerAt_spec hqL hyabs.le
  have hrecovery : minusCurve q P u=arc q y := by
    apply minusCurve_recovery has hao hy.2.le hu'
    have h := hc
    rw [contact,edgeWidth_positive_formula hu'] at h
    dsimp [P]
    linarith
  let O : Set ℝ := Ioo 0 t ∩ {x | (minusCurve q P x).y<0} ∩
    {x | |(minusCurve q P x).y|<(minusCurve q P x).a} ∩
    {x | (minusCurve q P x).y∈Ioo (-diagonalCoordinate q) (diagonalCoordinate q)}
  have hcy : Continuous (fun x => (minusCurve q P x).y) := by
    dsimp [minusCurve,rootMinus,zMinus]
    fun_prop
  have hca : Continuous (fun x => (minusCurve q P x).a) := by
    dsimp [minusCurve,rootMinus,zMinus]
    fun_prop
  have hO : IsOpen O := by
    exact ((isOpen_Ioo.inter (isOpen_lt hcy continuous_const)).inter
      (isOpen_lt hcy.abs hca)).inter (isOpen_Ioo.preimage hcy)
  have huO : u∈O := by
    dsimp [O]
    rw [hrecovery]
    exact ⟨⟨⟨hu,hy.2⟩,strict_sorting_of_inner_tangent hqL hyabs⟩,
      ⟨hy.1,by linarith [(abs_nonneg y)]⟩⟩
  let region : Set (ℝ × ℝ) := {z | z.1∈Icc 0 t ∧
    z.2∈Icc (-diagonalCoordinate q) (diagonalCoordinate q) ∧ 0≤contact q B z.1 z.2}
  let curve : ℝ → ℝ × ℝ := fun x => (x,(minusCurve q P x).y)
  have hcurve (x : ℝ) (hx : x∈O) :
      minusCurve q P x=arc q (minusCurve q P x).y := by
    obtain ⟨⟨⟨hxt,hxy⟩,hxa⟩,hxb⟩ := hx
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.2
    have hrad : 0≤q-(zMinus P x)^2 := by
      have hroot : 0<rootMinus q P x := by linarith
      exact (Real.sqrt_pos.mp hroot).le
    exact eq_outerAt_of_outer ⟨by linarith [abs_nonneg (minusCurve q P x).y],hxa.le⟩
      (minusCurve_circle hrad hxy.le)
  have hfeasible (x : ℝ) (hx : x∈O) : curve x∈region := by
    obtain ⟨⟨⟨hxt,hxy⟩,hxa⟩,hxb⟩ := hx
    refine ⟨⟨hxt.1.le,hxt.2.le⟩,⟨hxb.1.le,hxb.2.le⟩,?_⟩
    have hc' := minusCurve_contact q P x
    rw [hcurve x hx] at hc'
    rw [contact,edgeWidth_positive_formula ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩]
    dsimp [P] at hc'
    linarith
  apply not_minimum_on_strictly_concave_curve
    (s := region) (cost := fun z => required q t z.1 z.2) (p := (u,y))
    (curve := curve) (value := minusDemand q P t)
    (dvalue := minusDerivative q P t) (ddvalue := minusSecond q P t)
    (x := u) (k := 1/10)
    (fun z hz => hmin z hz.1 hz.2.1 hz.2.2) hO huO (by norm_num)
  · simp [curve,hrecovery,arc,SignedPoint.outerAt]
  · exact hfeasible
  · intro x hx
    obtain ⟨⟨⟨hxt,hxy⟩,hxa⟩,hxb⟩ := hx
    rw [show required q t (curve x).1 (curve x).2=
        edgeWidth (t-x)-(arc q (minusCurve q P x).y).a*Real.sin (t-x)-
          (minusCurve q P x).y*Real.cos (t-x) by rfl]
    rw [← hcurve x hx,edgeWidth_positive_formula ⟨by linarith [hxt.2],by linarith [hxt.1,ht.2]⟩]
    exact minusCurve_demand q P t x
  · intro x hx
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hx.1.1.1.1.le,by linarith [hx.1.1.1.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.2
    exact (minus_derivatives (Real.sqrt_pos.mp (show 0<rootMinus q P x by linarith))).1
  · intro x hx
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hx.1.1.1.1.le,by linarith [hx.1.1.1.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.2
    exact (minus_derivatives (Real.sqrt_pos.mp (show 0<rootMinus q P x by linarith))).2
  · intro x hx
    exact minus_second_negative hqL hqU hP ⟨ht.1.le,ht.2⟩
      ⟨hx.1.1.1.1.le,by linarith [hx.1.1.1.2,ht.2]⟩

/-- Complete compact contact reduction at the actual q. The four alternatives
are alignments, the unique possible sign join, and a positive diagonal.
Every alternative returned satisfies both actual pair inequalities. -/
theorem intrinsic_endpoint {q B D t u₀ y₀ : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (ht : 0<t ∧ t≤7/10) (hu₀ : u₀∈Icc 0 t)
    (hy₀ : |y₀|≤diagonalCoordinate q)
    (hc₀ : 0≤contact q B u₀ y₀) (hd₀ : required q t u₀ y₀≤D) :
    ∃ u y : ℝ, u∈Icc 0 t ∧ |y|≤diagonalCoordinate q ∧
      0≤contact q B u y ∧ required q t u y≤D ∧
      (u=0 ∨ u=t ∨ y=0 ∨ y=diagonalCoordinate q) ∧
      (y=diagonalCoordinate q ∨ contact q B u y=0) := by
  have hc : Continuous (fun p : ℝ × ℝ => contact q B p.1 p.2) := by
    dsimp [contact,arc,SignedPoint.outerAt,edgeWidth,pairWidth]
    fun_prop
  have hf : Continuous (fun p : ℝ × ℝ => required q t p.1 p.2) := by
    dsimp [required,arc,SignedPoint.outerAt,edgeWidth,pairWidth]
    fun_prop
  obtain ⟨p,hp,hp₀,hmin⟩ := contact_region_minimum hc hf
    (p₀ := (u₀,y₀)) ⟨hu₀,abs_le.mp hy₀,hc₀⟩
  obtain ⟨u,y⟩ := p
  have huc : u∈Icc 0 (7/10 : ℝ) := ⟨hp.1.1,hp.1.2.trans ht.2⟩
  have hvc : t-u∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hp.1.2],by linarith [hp.1.1,ht.2]⟩
  have hcontact := upper_or_contact_at_minimum hp hmin
    (by dsimp [contact,arc,SignedPoint.outerAt]; fun_prop)
    (required_strictAnti hqL hvc)
  refine ⟨u,y,hp.1,abs_le.mpr hp.2.1,hp.2.2,hp₀.trans hd₀,?_,hcontact⟩
  by_cases hu0 : u=0
  · exact Or.inl hu0
  by_cases hut : u=t
  · exact Or.inr (Or.inl hut)
  by_cases hy0 : y=0
  · exact Or.inr (Or.inr (Or.inl hy0))
  rcases hcontact with hyc | hce
  · exact Or.inr (Or.inr (Or.inr hyc))
  have hui : 0<u ∧ u<t := ⟨lt_of_le_of_ne hp.1.1 (Ne.symm hu0),
    lt_of_le_of_ne hp.1.2 hut⟩
  by_cases hyceq : y=diagonalCoordinate q
  · exact Or.inr (Or.inr (Or.inr hyceq))
  have hyc : y<diagonalCoordinate q := lt_of_le_of_ne hp.2.1.2 hyceq
  by_cases hyl : y= -diagonalCoordinate q
  · have hstrict := lower_diagonal_strict hqL hqU hB.1 huc
    rw [hyl] at hce
    linarith
  have hylo : -diagonalCoordinate q<y := lt_of_le_of_ne hp.2.1.1 (Ne.symm hyl)
  rcases lt_or_gt_of_ne hy0 with hyneg | hypos
  · exact False.elim (negative_contact_not_minimum hqL hqU hB ht hui ⟨hylo,hyneg⟩ hce hmin)
  · exact False.elim (positive_contact_not_minimum hqL hqU hB ht hui ⟨hypos,hyc⟩ hce hmin)

end PairedPrimary
end SquaresInCircles.Eight.TableFree