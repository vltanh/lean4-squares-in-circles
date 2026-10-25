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
  rcases p with ⟨a,y⟩
  simp only [arc,SignedPoint.outerAt,SignedPoint.mk.injEq,and_true] at hr hp ⊢
  rw [hr,Real.sqrt_sq hp]
  ring

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
  have hq0 : 0≤q := by norm_num [qLow] at hq; linarith
  have hroot := Real.sq_sqrt (show 0≤q/2 by positivity)
  have hnon := Real.sqrt_nonneg (q/2)
  have hc : 0≤diagonalCoordinate q := by
    unfold diagonalCoordinate
    norm_num [qLow] at hq
    nlinarith
  have hrad : q-(diagonalCoordinate q+1/2)^2=q/2 := by
    unfold diagonalCoordinate
    rw [sub_add_cancel,hroot]
    ring
  have hval : Real.sqrt (q-(diagonalCoordinate q+1/2)^2)-1/2=diagonalCoordinate q := by
    rw [hrad]
    rfl
  constructor
  · show Real.sqrt (q-(|diagonalCoordinate q|+1/2)^2)-1/2=diagonalCoordinate q
    rw [abs_of_nonneg hc]
    exact hval
  · show Real.sqrt (q-(|-diagonalCoordinate q|+1/2)^2)-1/2=diagonalCoordinate q
    rw [abs_neg,abs_of_nonneg hc]
    exact hval

/-- The slope bound on the two circular half-arcs also holds across y=0. -/
theorem arc_lipschitz {q y z : ℝ} (hq : qLow≤q)
    (hy : |y|≤diagonalCoordinate q) (hz : |z|≤diagonalCoordinate q) :
    |(arc q y).a-(arc q z).a|≤|y-z| := by
  obtain ⟨hys,hyo,hycore⟩ := SignedPoint.outerAt_spec hq hy
  obtain ⟨hzs,hzo,hzcore⟩ := SignedPoint.outerAt_spec hq hz
  have hyb : |y|≤(arc q y).a := hys.2
  have hzb : |z|≤(arc q z).a := hzs.2
  have hyo' : ((arc q y).a+1/2)^2+(|y|+1/2)^2=q := hyo
  have hzo' : ((arc q z).a+1/2)^2+(|z|+1/2)^2=q := hzo
  have hsum : 0<(arc q y).a+(arc q z).a+1 := by
    linarith [abs_nonneg y,abs_nonneg z]
  have hid : ((arc q y).a-(arc q z).a)*((arc q y).a+(arc q z).a+1)=
      -(|y|-|z|)*(|y|+|z|+1) := by
    linear_combination hyo'-hzo'
  have ha := congrArg abs hid
  rw [abs_mul,abs_mul,abs_neg,
    abs_of_pos hsum,abs_of_nonneg (by positivity : 0≤|y|+|z|+1)] at ha
  have hab : |(|y|-|z|)|≤|y-z| := abs_abs_sub_abs_le_abs_sub y z
  have hmul₁ := mul_le_mul_of_nonneg_right hab (by positivity : 0≤|y|+|z|+1)
  have hmul₂ := mul_le_mul_of_nonneg_left
    (show |y|+|z|+1≤(arc q y).a+(arc q z).a+1 by linarith)
    (abs_nonneg (y-z))
  have hprod : |(arc q y).a-(arc q z).a| *
      ((arc q y).a+(arc q z).a+1)≤
      |y-z| * ((arc q y).a+(arc q z).a+1) := by linarith
  exact le_of_mul_le_mul_right hprod hsum

theorem contact_strictAnti {q B u : ℝ} (hq : qLow≤q)
    (hu : u∈Icc 0 (7/10 : ℝ)) :
    StrictAntiOn (contact q B u) (Icc (-diagonalCoordinate q) (diagonalCoordinate q)) := by
  intro y hy z hz hyz
  have hab := arc_lipschitz hq (abs_le.mpr hy) (abs_le.mpr hz)
  have hdiff : (arc q z).a-(arc q y).a≤z-y := by
    have h1 := neg_abs_le ((arc q y).a-(arc q z).a)
    have h2 : |y-z|=z-y := by
      rw [abs_sub_comm]
      exact abs_of_pos (sub_pos.mpr hyz)
    linarith
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hu
  have hmul := mul_le_mul_of_nonneg_right hdiff hs0
  have hstrict := mul_pos (sub_pos.mpr hyz) (sub_pos.mpr hsc)
  simp only [contact]
  nlinarith

theorem required_strictAnti {q t u : ℝ} (hq : qLow≤q)
    (hv : t-u∈Icc 0 (7/10 : ℝ)) :
    StrictAntiOn (required q t u) (Icc (-diagonalCoordinate q) (diagonalCoordinate q)) := by
  intro y hy z hz hyz
  have hab := arc_lipschitz hq (abs_le.mpr hy) (abs_le.mpr hz)
  have hdiff : -(z-y)≤(arc q z).a-(arc q y).a := by
    have h1 := le_abs_self ((arc q y).a-(arc q z).a)
    have h2 : |y-z|=z-y := by
      rw [abs_sub_comm]
      exact abs_of_pos (sub_pos.mpr hyz)
    linarith
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hv
  have hmul := mul_le_mul_of_nonneg_right hdiff hs0
  have hstrict := mul_pos (sub_pos.mpr hyz) (sub_pos.mpr hsc)
  simp only [required]
  nlinarith

theorem lower_diagonal_strict {q B u : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B) (hu : u∈Icc 0 (7/10 : ℝ)) :
    0<contact q B u (-diagonalCoordinate q) := by
  obtain ⟨hc0,hc1,hA0,hA1⟩ := uniform_circle_reserves hqL hqU
  obtain ⟨hcos,hs0,hs⟩ := transport_trig_coarse hu
  have hsum : 1≤Real.sin u+Real.cos u := by
    have h := one_le_abs_cos_add_abs_sin u
    rw [abs_of_nonneg hs0,abs_of_pos (by linarith : (0:ℝ)<Real.cos u)] at h
    linarith
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
  set P := B-1/2 with hPdef
  have hP : 3/8≤P ∧ P≤183/200 := by
    obtain ⟨hcl,hcu,hal,hau⟩ := uniform_circle_reserves hqL hqU
    have hB2 := hB.2
    unfold axisCoordinate at hB2
    constructor <;> linarith [hB.1]
  have hu' : u∈Icc 0 (7/10 : ℝ) := ⟨hu.1.le,by linarith⟩
  have hyabs : |y|<diagonalCoordinate q := by
    rw [abs_of_pos hy.1]
    exact hy.2
  obtain ⟨has,hao,hac⟩ := SignedPoint.outerAt_spec hqL hyabs.le
  have hrecovery : plusCurve q P u=arc q y := by
    apply plusCurve_recovery has hao hy.1.le hu'
    have h := hc
    rw [contact,edgeWidth_positive_formula hu'] at h
    show P+1/2+(arc q y).a*Real.sin u-y*Real.cos u=(1+Real.cos u+Real.sin u)/2
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
  have hpy : (plusCurve q P u).y=y := by rw [hrecovery]; rfl
  have hpa : (plusCurve q P u).a=(arc q y).a := by rw [hrecovery]
  have huO : u∈O := by
    refine ⟨⟨⟨hu,?_⟩,?_⟩,?_⟩
    · show 0<(plusCurve q P u).y
      rw [hpy]
      exact hy.1
    · show |(plusCurve q P u).y|<(plusCurve q P u).a
      rw [hpy,hpa]
      exact strict_sorting_of_inner_tangent hqL hyabs
    · show (plusCurve q P u).y∈Ioo (-diagonalCoordinate q) (diagonalCoordinate q)
      rw [hpy]
      exact ⟨by linarith [abs_nonneg y],hy.2⟩
  let region : Set (ℝ × ℝ) := {z | z.1∈Icc 0 t ∧
    z.2∈Icc (-diagonalCoordinate q) (diagonalCoordinate q) ∧ 0≤contact q B z.1 z.2}
  let curve : ℝ → ℝ × ℝ := fun x => (x,(plusCurve q P x).y)
  have hcurve (x : ℝ) (hx : x∈O) :
      plusCurve q P x=arc q (plusCurve q P x).y := by
    have hxt : x∈Ioo 0 t := hx.1.1.1
    have hxy : 0<(plusCurve q P x).y := hx.1.1.2
    have hxa : |(plusCurve q P x).y|<(plusCurve q P x).a := hx.1.2
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.1
    have hrad : 0≤q-(zPlus P x)^2 := by
      have hroot : 0<rootPlus q P x := by linarith
      exact (Real.sqrt_pos.mp hroot).le
    exact eq_outerAt_of_outer ⟨by linarith [abs_nonneg (plusCurve q P x).y],hxa.le⟩
      (plusCurve_circle hrad hxy.le)
  have harc (x : ℝ) (hx : x∈O) :
      (arc q (plusCurve q P x).y).a=(plusCurve q P x).a :=
    (congrArg SignedPoint.a (hcurve x hx)).symm
  have hfeasible (x : ℝ) (hx : x∈O) : curve x∈region := by
    have hxt : x∈Ioo 0 t := hx.1.1.1
    have hxb : (plusCurve q P x).y∈Ioo (-diagonalCoordinate q) (diagonalCoordinate q) := hx.2
    refine ⟨⟨hxt.1.le,hxt.2.le⟩,⟨hxb.1.le,hxb.2.le⟩,?_⟩
    have hc' := plusCurve_contact q P x
    show 0≤contact q B x (plusCurve q P x).y
    rw [contact,edgeWidth_positive_formula ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩,harc x hx]
    linarith
  apply not_minimum_on_strictly_concave_curve
    (s := region) (cost := fun z => required q t z.1 z.2) (p := (u,y))
    (curve := curve) (value := plusDemand q P t)
    (dvalue := plusDerivative q P t) (ddvalue := plusSecond q P t)
    (x := u) (k := 1/25)
    (fun z hz => hmin z hz.1 hz.2.1 hz.2.2) hO huO (by norm_num)
  · show (u,(plusCurve q P u).y)=(u,y)
    rw [hpy]
  · exact hfeasible
  · intro x hx
    have hxt : x∈Ioo 0 t := hx.1.1.1
    show required q t x (plusCurve q P x).y=plusDemand q P t x
    rw [required,edgeWidth_positive_formula ⟨by linarith [hxt.2],by linarith [hxt.1,ht.2]⟩,
      harc x hx]
    exact plusCurve_demand q P t x
  · intro x hx
    have hxt : x∈Ioo 0 t := hx.1.1.1
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.1
    exact (plus_derivatives (Real.sqrt_pos.mp (show 0<rootPlus q P x by linarith))).1
  · intro x hx
    have hxt : x∈Ioo 0 t := hx.1.1.1
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.1
    exact (plus_derivatives (Real.sqrt_pos.mp (show 0<rootPlus q P x by linarith))).2
  · intro x hx
    have hxt : x∈Ioo 0 t := hx.1.1.1
    exact plus_second_negative hqL hqU hP ⟨ht.1.le,ht.2⟩
      ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩

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
  set P := B-1/2 with hPdef
  have hP : 3/8≤P ∧ P≤183/200 := by
    obtain ⟨hcl,hcu,hal,hau⟩ := uniform_circle_reserves hqL hqU
    have hB2 := hB.2
    unfold axisCoordinate at hB2
    constructor <;> linarith [hB.1]
  have hu' : u∈Icc 0 (7/10 : ℝ) := ⟨hu.1.le,by linarith⟩
  have hyabs : |y|<diagonalCoordinate q := by
    rw [abs_of_neg hy.2]
    linarith
  obtain ⟨has,hao,hac⟩ := SignedPoint.outerAt_spec hqL hyabs.le
  have hrecovery : minusCurve q P u=arc q y := by
    apply minusCurve_recovery has hao hy.2.le hu'
    have h := hc
    rw [contact,edgeWidth_positive_formula hu'] at h
    show P+1/2+(arc q y).a*Real.sin u-y*Real.cos u=(1+Real.cos u+Real.sin u)/2
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
  have hpy : (minusCurve q P u).y=y := by rw [hrecovery]; rfl
  have hpa : (minusCurve q P u).a=(arc q y).a := by rw [hrecovery]
  have huO : u∈O := by
    refine ⟨⟨⟨hu,?_⟩,?_⟩,?_⟩
    · show (minusCurve q P u).y<0
      rw [hpy]
      exact hy.2
    · show |(minusCurve q P u).y|<(minusCurve q P u).a
      rw [hpy,hpa]
      exact strict_sorting_of_inner_tangent hqL hyabs
    · show (minusCurve q P u).y∈Ioo (-diagonalCoordinate q) (diagonalCoordinate q)
      rw [hpy]
      exact ⟨hy.1,by linarith [abs_nonneg y]⟩
  let region : Set (ℝ × ℝ) := {z | z.1∈Icc 0 t ∧
    z.2∈Icc (-diagonalCoordinate q) (diagonalCoordinate q) ∧ 0≤contact q B z.1 z.2}
  let curve : ℝ → ℝ × ℝ := fun x => (x,(minusCurve q P x).y)
  have hcurve (x : ℝ) (hx : x∈O) :
      minusCurve q P x=arc q (minusCurve q P x).y := by
    have hxt : x∈Ioo 0 t := hx.1.1.1
    have hxy : (minusCurve q P x).y<0 := hx.1.1.2
    have hxa : |(minusCurve q P x).y|<(minusCurve q P x).a := hx.1.2
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.2
    have hrad : 0≤q-(zMinus P x)^2 := by
      have hroot : 0<rootMinus q P x := by linarith
      exact (Real.sqrt_pos.mp hroot).le
    exact eq_outerAt_of_outer ⟨by linarith [abs_nonneg (minusCurve q P x).y],hxa.le⟩
      (minusCurve_circle hrad hxy.le)
  have harc (x : ℝ) (hx : x∈O) :
      (arc q (minusCurve q P x).y).a=(minusCurve q P x).a :=
    (congrArg SignedPoint.a (hcurve x hx)).symm
  have hfeasible (x : ℝ) (hx : x∈O) : curve x∈region := by
    have hxt : x∈Ioo 0 t := hx.1.1.1
    have hxb : (minusCurve q P x).y∈Ioo (-diagonalCoordinate q) (diagonalCoordinate q) := hx.2
    refine ⟨⟨hxt.1.le,hxt.2.le⟩,⟨hxb.1.le,hxb.2.le⟩,?_⟩
    have hc' := minusCurve_contact q P x
    show 0≤contact q B x (minusCurve q P x).y
    rw [contact,edgeWidth_positive_formula ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩,harc x hx]
    linarith
  apply not_minimum_on_strictly_concave_curve
    (s := region) (cost := fun z => required q t z.1 z.2) (p := (u,y))
    (curve := curve) (value := minusDemand q P t)
    (dvalue := minusDerivative q P t) (ddvalue := minusSecond q P t)
    (x := u) (k := 1/10)
    (fun z hz => hmin z hz.1 hz.2.1 hz.2.2) hO huO (by norm_num)
  · show (u,(minusCurve q P u).y)=(u,y)
    rw [hpy]
  · exact hfeasible
  · intro x hx
    have hxt : x∈Ioo 0 t := hx.1.1.1
    show required q t x (minusCurve q P x).y=minusDemand q P t x
    rw [required,edgeWidth_positive_formula ⟨by linarith [hxt.2],by linarith [hxt.1,ht.2]⟩,
      harc x hx]
    exact minusCurve_demand q P t x
  · intro x hx
    have hxt : x∈Ioo 0 t := hx.1.1.1
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.2
    exact (minus_derivatives (Real.sqrt_pos.mp (show 0<rootMinus q P x by linarith))).1
  · intro x hx
    have hxt : x∈Ioo 0 t := hx.1.1.1
    have hxw : x∈Icc 0 (7/10 : ℝ) := ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩
    have hr := (branch_bounds hqL hqU hP hxw).2.2.2.2
    exact (minus_derivatives (Real.sqrt_pos.mp (show 0<rootMinus q P x by linarith))).2
  · intro x hx
    have hxt : x∈Ioo 0 t := hx.1.1.1
    exact minus_second_negative hqL hqU hP ⟨ht.1.le,ht.2⟩
      ⟨hxt.1.le,by linarith [hxt.2,ht.2]⟩

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
  have hpu : u∈Icc 0 t := hp.1
  have hpy : y∈Icc (-diagonalCoordinate q) (diagonalCoordinate q) := hp.2.1
  have hpc : 0≤contact q B u y := hp.2.2
  have hmin' : ∀ z : ℝ × ℝ, z.1∈Icc 0 t →
      z.2∈Icc (-diagonalCoordinate q) (diagonalCoordinate q) →
      0≤contact q B z.1 z.2 → required q t u y≤required q t z.1 z.2 := hmin
  have huc : u∈Icc 0 (7/10 : ℝ) := ⟨hpu.1,hpu.2.trans ht.2⟩
  have hvc : t-u∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hpu.2],by linarith [hpu.1,ht.2]⟩
  have hcontact' := upper_or_contact_at_minimum
    (contact := fun p : ℝ × ℝ => contact q B p.1 p.2)
    (cost := fun p : ℝ × ℝ => required q t p.1 p.2) (x := u) (y := y)
    hp hmin (hc.comp (Continuous.prodMk_right u)) (required_strictAnti hqL hvc)
  have hcontact : y=diagonalCoordinate q ∨ contact q B u y=0 := hcontact'
  refine ⟨u,y,hpu,abs_le.mpr hpy,hpc,hp₀.trans hd₀,?_,hcontact⟩
  by_cases hu0 : u=0
  · exact Or.inl hu0
  by_cases hut : u=t
  · exact Or.inr (Or.inl hut)
  by_cases hy0 : y=0
  · exact Or.inr (Or.inr (Or.inl hy0))
  rcases hcontact with hyc | hce
  · exact Or.inr (Or.inr (Or.inr hyc))
  have hui : 0<u ∧ u<t := ⟨lt_of_le_of_ne hpu.1 (Ne.symm hu0),
    lt_of_le_of_ne hpu.2 hut⟩
  by_cases hyceq : y=diagonalCoordinate q
  · exact Or.inr (Or.inr (Or.inr hyceq))
  have hyc : y<diagonalCoordinate q := lt_of_le_of_ne hpy.2 hyceq
  by_cases hyl : y= -diagonalCoordinate q
  · have hstrict := lower_diagonal_strict hqL hqU hB.1 huc
    rw [hyl] at hce
    linarith
  have hylo : -diagonalCoordinate q<y := lt_of_le_of_ne hpy.1 (Ne.symm hyl)
  rcases lt_or_gt_of_ne hy0 with hyneg | hypos
  · exact False.elim (negative_contact_not_minimum hqL hqU hB ht hui ⟨hylo,hyneg⟩ hce hmin')
  · exact False.elim (positive_contact_not_minimum hqL hqU hB ht hui ⟨hypos,hyc⟩ hce hmin')

end PairedPrimary
end SquaresInCircles.Eight.TableFree