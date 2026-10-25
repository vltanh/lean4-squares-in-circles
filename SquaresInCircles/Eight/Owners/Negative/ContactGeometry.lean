module

public import SquaresInCircles.Eight.Owners.Negative.ContactScalars
public import SquaresInCircles.Eight.Owners.PairedPrimaryGeometry

/-!
# Eight squares: the endpoint on the circle for a primary pair of opposite signs

The opposite demand is minimized on one compact contact strip. At every minimum with negative
first error, a contact curve to the right strictly decreases the demand (`right_improvement`),
also at the lower diagonal and at the join at zero tangent. So the minimum is at the first
alignment, and the pair moves to a point on the circle of the same `q` with `B - y = 1`
(`first_negative_alignment`). Local reflection gives the second alignment
(`second_negative_alignment`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace NegativeContact
open PairedPrimary

private theorem signedPoint_eq {p r : SignedPoint} (ha : p.a=r.a) (hy : p.y=r.y) : p=r := by
  cases p
  cases r
  simp only [SignedPoint.mk.injEq]
  exact ⟨ha,hy⟩

theorem upper_diagonal_impossible {q B x : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap) (hB : B≤axisCoordinate q)
    (hx : x∈Icc (-7/10 : ℝ) 0) : contact q B x (diagonalCoordinate q)<0 := by
  obtain ⟨hc0,hc1,hA0,hA1⟩ := uniform_circle_reserves hqL hqU
  have htrig := transport_trig
    (show -x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith [hx.1,hx.2])
  have hsum := one_le_abs_cos_add_abs_sin (-x)
  rw [abs_of_pos (by linarith [htrig.1] : 0<Real.cos (-x)),
    abs_of_nonneg htrig.2.2.1,Real.cos_neg,Real.sin_neg] at hsum
  have hm := mul_le_mul_of_nonneg_left hsum (by linarith : 0≤diagonalCoordinate q)
  rw [contact,(arc_diagonal hqL).1]
  have hw := edgeWidth_ge_one x
  dsimp [axisCoordinate] at hB
  nlinarith

theorem recover_minus {q B x : ℝ} {p : SignedPoint}
    (hp : p.Sorted) (ho : p.Outer q) (hy : p.y≤0)
    (hx : x∈Ico (-7/10 : ℝ) 0)
    (hcontact : B+p.a*Real.sin x-p.y*Real.cos x=edgeWidth x) :
    minusPoint q (B-1/2) x=p := by
  obtain ⟨hc,hsc,htan⟩ := AffineCircleEntry.signed_trig
    (show |x|≤frameCap by rw [abs_of_neg hx.2]; show -x≤7/10; linarith only [hx.1])
  have hsneg : Real.sin x<0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith only [hx.2])
      (by linarith only [hx.1,Real.pi_gt_three])
    simpa only [Real.sin_neg,neg_pos] using h
  let X := p.a+1/2
  let Z := 1/2-p.y
  have hX : 0<X := by dsimp [X]; linarith only [hp.1]
  have hZ : 0<Z := by dsimp [Z]; linarith only [hy]
  have hcircle : X^2+Z^2=q := by
    simpa [X,Z,SignedPoint.Outer,SignedPoint.circle,abs_of_nonpos hy,sub_eq_add_neg,
      add_comm] using ho
  have hw : edgeWidth x=(1+Real.cos x-Real.sin x)/2 := by
    have h := edgeWidth_positive_formula
      (show -x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [hx.1,hx.2])
    simpa only [edgeWidth_neg,Real.cos_neg,Real.sin_neg,← sub_eq_add_neg] using h
  have hfirst : X*Real.sin x+Z*Real.cos x=S (B-1/2) x := by
    dsimp [X,Z,S]
    rw [hw] at hcontact
    linarith only [hcontact]
  have hrot : 0<X*Real.cos x-Z*Real.sin x := by
    linarith only [mul_pos hX hc,mul_neg_of_pos_of_neg hZ hsneg]
  have hrot2 : (X*Real.cos x-Z*Real.sin x)^2=q-S (B-1/2) x^2 := by
    have hid := circle_rotation_identity X Z x
    rw [hfirst,hcircle] at hid
    linarith only [hid]
  have hU : U q (B-1/2) x=X*Real.cos x-Z*Real.sin x := by
    rw [U,← hrot2,Real.sqrt_sq_eq_abs,abs_of_pos hrot]
  apply signedPoint_eq
  · dsimp [minusPoint,Xminus]
    rw [hU,← hfirst]
    have hid : (X*Real.cos x-Z*Real.sin x)*Real.cos x+
        (X*Real.sin x+Z*Real.cos x)*Real.sin x=X := by
      linear_combination X*Real.sin_sq_add_cos_sq x
    rw [hid]
    dsimp [X]
    ring
  · dsimp [minusPoint,Zminus]
    rw [hU,← hfirst]
    have hid : -(X*Real.cos x-Z*Real.sin x)*Real.sin x+
        (X*Real.sin x+Z*Real.cos x)*Real.cos x=Z := by
      linear_combination Z*Real.sin_sq_add_cos_sq x
    rw [hid]
    dsimp [Z]
    ring

theorem recover_plus {q B x : ℝ} {p : SignedPoint}
    (hp : p.Sorted) (ho : p.Outer q) (hy : 0≤p.y)
    (hx : x∈Ico (-7/10 : ℝ) 0)
    (hcontact : B+p.a*Real.sin x-p.y*Real.cos x=edgeWidth x) :
    plusPoint q (B-1/2) x=p := by
  obtain ⟨hc,hsc,htan⟩ := AffineCircleEntry.signed_trig
    (show |x|≤frameCap by rw [abs_of_neg hx.2]; show -x≤7/10; linarith only [hx.1])
  have hsneg : Real.sin x<0 := by
    have h := Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith only [hx.2])
      (by linarith only [hx.1,Real.pi_gt_three])
    simpa only [Real.sin_neg,neg_pos] using h
  let X := p.a+1/2
  let Z := p.y+1/2
  have hX : 0<X := by dsimp [X]; linarith only [hp.1]
  have hZ : 0<Z := by dsimp [Z]; linarith only [hy]
  have hZX : Z≤X := by dsimp [Z,X]; simpa [abs_of_nonneg hy] using hp.2
  have hcircle : X^2+Z^2=q := by
    simpa [X,Z,SignedPoint.Outer,SignedPoint.circle,abs_of_nonneg hy] using ho
  have hw : edgeWidth x=(1+Real.cos x-Real.sin x)/2 := by
    have h := edgeWidth_positive_formula
      (show -x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [hx.1,hx.2])
    simpa only [edgeWidth_neg,Real.cos_neg,Real.sin_neg,← sub_eq_add_neg] using h
  have hfirst : Z*Real.cos x-X*Real.sin x=B-1/2 := by
    dsimp [X,Z]
    rw [hw] at hcontact
    linarith only [hcontact]
  have hrot : 0<X*Real.cos x+Z*Real.sin x := by
    rw [abs_of_neg hsneg] at hsc
    have hmul := mul_le_mul_of_nonpos_right hZX hsneg.le
    have hpos := mul_pos hX (by linarith only [hsc] : 0<Real.cos x+Real.sin x)
    linarith only [hmul,hpos]
  have hrot2 : (X*Real.cos x+Z*Real.sin x)^2=q-(B-1/2)^2 := by
    have hid := circle_rotation_identity X (-Z) x
    have hf : X*Real.sin x-Z*Real.cos x= -(B-1/2) := by linarith only [hfirst]
    linear_combination hid+hcircle-(X*Real.sin x-Z*Real.cos x-(B-1/2))*hf
  have hV : V q (B-1/2)=X*Real.cos x+Z*Real.sin x := by
    rw [V,← hrot2,Real.sqrt_sq_eq_abs,abs_of_pos hrot]
  apply signedPoint_eq
  · dsimp [plusPoint,Xplus]
    rw [hV,← hfirst]
    have hid : (X*Real.cos x+Z*Real.sin x)*Real.cos x-
        (Z*Real.cos x-X*Real.sin x)*Real.sin x=X := by
      linear_combination X*Real.sin_sq_add_cos_sq x
    rw [hid]
    dsimp [X]
    ring
  · dsimp [plusPoint,Zplus]
    rw [hV,← hfirst]
    have hid : (X*Real.cos x+Z*Real.sin x)*Real.sin x+
        (Z*Real.cos x-X*Real.sin x)*Real.cos x=Z := by
      linear_combination Z*Real.sin_sq_add_cos_sq x
    rw [hid]
    dsimp [Z]
    ring

theorem minus_point_circle {q P x : ℝ} (hrad : 0≤q-S P x^2)
    (hZ : 1/2≤Zminus q P x) : (minusPoint q P x).Outer q := by
  have hr := Real.sq_sqrt hrad
  have hid := circle_rotation_identity (U q P x) (-S P x) x
  dsimp [SignedPoint.Outer,SignedPoint.circle,minusPoint]
  rw [abs_of_nonpos (by linarith : 1/2-Zminus q P x≤0)]
  dsimp [Xminus,Zminus,U] at hid ⊢
  nlinarith

theorem plus_point_circle {q P x : ℝ} (hrad : 0≤q-P^2)
    (hZ : 1/2≤Zplus q P x) : (plusPoint q P x).Outer q := by
  have hr := Real.sq_sqrt hrad
  have hid := circle_rotation_identity (V q P) P x
  dsimp [SignedPoint.Outer,SignedPoint.circle,plusPoint]
  rw [abs_of_nonneg (by linarith : 0≤Zplus q P x-1/2)]
  dsimp [Xplus,Zplus,V] at hid ⊢
  nlinarith

/-- A local contact curve to the right is feasible and strictly decreases the demand. At the
active lower diagonal the derivative of `X - Z` is positive; at zero tangent the positive branch
has a positive height derivative. -/
theorem right_improvement {q B t x y : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : 0≤B ∧ B≤axisCoordinate q)
    (hx : x∈Ico (-7/10 : ℝ) 0) (ht : t∈Ioc 0 (7/10 : ℝ))
    (hv : t-x≤7/10) (hy : |y|≤diagonalCoordinate q)
    (hcontact : contact q B x y=0) :
    ∃ z y' : ℝ, x<z ∧ z<0 ∧ |y'|≤diagonalCoordinate q ∧
      contact q B z y'=0 ∧ required q t z y'<required q t x y := by
  let P := B-1/2
  let p := arc q y
  obtain ⟨hp,ho,hcore⟩ := SignedPoint.outerAt_spec hqL hy
  have hP : P∈Icc (-1/2 : ℝ) (183/200) := by
    obtain ⟨hc0,hc1,hA0,hA1⟩ := uniform_circle_reserves hqL hqU
    have hB2 : B≤Real.sqrt (q-1/4)-1/2 := hB.2
    constructor <;> dsimp only [P] <;> linarith only [hB.1,hB2,hA1]
  have hroots := scalar_bounds hqL hqU hP ⟨hx.1,hx.2.le⟩
  have hbase : B+p.a*Real.sin x-p.y*Real.cos x=edgeWidth x := by
    have h : B+(arc q y).a*Real.sin x-y*Real.cos x-edgeWidth x=0 := hcontact
    show B+(arc q y).a*Real.sin x-y*Real.cos x=edgeWidth x
    linarith only [h]
  have hupper : y<diagonalCoordinate q := by
    have hle := (abs_le.mp hy).2
    apply lt_of_le_of_ne hle
    intro heq
    rw [heq] at hcontact
    linarith only [hcontact,upper_diagonal_impossible hqL hqU hB.2 ⟨hx.1,hx.2.le⟩]
  have hyarc : p.y=y := rfl
  have hxevent : ∀ᶠ z in 𝓝[>] x, z∈Ico (-7/10 : ℝ) 0 ∧
      t-z∈Icc 0 (7/10 : ℝ) := by
    have hzneg : ∀ᶠ z in 𝓝[>] x, z<0 :=
      (eventually_lt_nhds hx.2).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hzneg] with z hxz hz
    have hxz' : x<z := hxz
    refine ⟨⟨hx.1.trans hxz.le,hz⟩,⟨?_,?_⟩⟩ <;> linarith only [ht.1,hz,hxz',hv]
  by_cases hyneg : y<0
  · have hrec : minusPoint q P x=p := recover_minus hp ho
      (by simpa [hyarc] using hyneg.le) hx hbase
    have hX : 1/2<Xminus q P x := by
      have h := congrArg SignedPoint.a hrec
      dsimp [minusPoint] at h
      linarith only [h,hp.1]
    have hZ : 1/2<Zminus q P x := by
      have h := congrArg SignedPoint.y hrec
      dsimp [minusPoint] at h
      rw [hyarc] at h
      linarith only [h,hyneg]
    have hsort : Zminus q P x≤Xminus q P x := by
      have hs : |p.y|≤p.a := hp.2
      rw [← hrec] at hs
      dsimp [minusPoint] at hs
      rw [abs_of_neg (by linarith only [hZ] : 1/2-Zminus q P x<0)] at hs
      linarith only [hs]
    obtain ⟨hdX,hdZ⟩ := minus_coordinate_derivatives hroots.2.2.2.1
    have hfactor : 0<1+Real.sin x/U q P x := by
      have hU : 0<U q P x := by linarith only [hroots.2.2.1]
      have hs := Real.neg_one_le_sin x
      have hlt : -1<Real.sin x/U q P x := by
        rw [lt_div_iff₀ hU]
        linarith only [hroots.2.2.1,hs]
      linarith only [hlt]
    have hdsort : HasDerivAt (fun z => Xminus q P z-Zminus q P z)
        ((Xminus q P x+Zminus q P x)*(1+Real.sin x/U q P x)) x := by
      convert hdX.sub hdZ using 1
      ring
    have hsortevent := eventually_right_positive hdsort (sub_nonneg.mpr hsort)
      (mul_pos (by linarith only [hX,hZ]) hfactor)
    have hZevent : ∀ᶠ z in 𝓝[>] x, 1/2<Zminus q P z :=
      (hdZ.continuousAt.eventually (lt_mem_nhds hZ)).filter_mono nhdsWithin_le_nhds
    have hdemand := (demand_derivatives (t := t) hroots.2.2.2.1).1
    have hnegative := minus_demand_negative hx ht hv
      (by linarith only [hroots.2.2.1]) (by linarith only [hX]) hZ.le hsort
    have hcostevent := eventually_right_lt hdemand (hnegative.trans (by norm_num))
    obtain ⟨z,hxz,hxzdom,hzcost,hzsort,hzZ⟩ :=
      (eventually_mem_nhdsWithin.and (hxevent.and (hcostevent.and (hsortevent.and hZevent)))).exists
    let p' := minusPoint q P z
    have hzroots := scalar_bounds hqL hqU hP ⟨hxzdom.1.1,hxzdom.1.2.le⟩
    have hps : p'.Sorted := by
      dsimp [p',minusPoint,SignedPoint.Sorted]
      rw [abs_of_neg (by linarith only [hzZ] : 1/2-Zminus q P z<0)]
      constructor <;> linarith only [hzsort,hzZ]
    have hpo : p'.Outer q := minus_point_circle hzroots.2.2.2.1.le hzZ.le
    have hpa : p'=arc q p'.y := eq_outerAt_of_outer hps hpo
    have hproj := minus_contact_and_demand (q := q) (P := P) ⟨hxzdom.1.1,hxzdom.1.2.le⟩ hxzdom.2
    have hproj0 := minus_contact_and_demand (q := q) (P := P) ⟨hx.1,hx.2.le⟩
      (show t-x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [ht.1,hx.2,hv])
    refine ⟨z,p'.y,hxz,hxzdom.1.2,(SignedPoint.outer_bounds hps hpo).2.1,?_,?_⟩
    · dsimp [contact]
      rw [← hpa]
      dsimp [p',P] at hproj
      linarith only [hproj.1]
    · dsimp [required]
      rw [← hpa]
      have ha : (minusPoint q P x).a=(arc q y).a := congrArg SignedPoint.a hrec
      have hy' : (minusPoint q P x).y=y := congrArg SignedPoint.y hrec
      have h0 := hproj0.2
      rw [ha,hy'] at h0
      have h1 : edgeWidth (t-z)-p'.a*Real.sin (t-z)-p'.y*Real.cos (t-z)=minusDemand q P t z :=
        hproj.2
      linarith only [h0,h1,hzcost]
  · have hypos : 0≤y := le_of_not_gt hyneg
    have hrec : plusPoint q P x=p := recover_plus hp ho
      (by simpa [hyarc] using hypos) hx hbase
    have hX : 1/2<Xplus q P x := by
      have h := congrArg SignedPoint.a hrec
      dsimp [plusPoint] at h
      linarith only [h,hp.1]
    have hZ : 1/2≤Zplus q P x := by
      have h := congrArg SignedPoint.y hrec
      dsimp [plusPoint] at h
      rw [hyarc] at h
      linarith only [h,hypos]
    have hsort : Zplus q P x<Xplus q P x := by
      have hs : |p.y|<p.a := strict_sorting_of_inner_tangent hqL
        (show |y|<diagonalCoordinate q by simpa [abs_of_nonneg hypos] using hupper)
      rw [← hrec] at hs
      dsimp [plusPoint] at hs
      rw [abs_of_nonneg (by linarith only [hZ] : 0≤Zplus q P x-1/2)] at hs
      linarith only [hs]
    obtain ⟨hdX,hdZ⟩ := plus_coordinate_derivatives q P x
    have hZevent := eventually_right_positive (hdZ.sub_const (1/2))
      (sub_nonneg.mpr hZ) (by linarith only [hX] : 0<Xplus q P x)
    have hsortevent : ∀ᶠ z in 𝓝[>] x, Zplus q P z<Xplus q P z := by
      have h : ∀ᶠ z in 𝓝[>] x, 0<(Xplus q P-Zplus q P) z :=
        ((hdX.sub hdZ).continuousAt.eventually
          (lt_mem_nhds (sub_pos.mpr hsort))).filter_mono nhdsWithin_le_nhds
      filter_upwards [h] with z hz
      have hz' : 0<Xplus q P z-Zplus q P z := hz
      linarith only [hz']
    have hdemand := (demand_derivatives (t := t) hroots.2.2.2.1).2
    have hnegative := plus_demand_negative
      (show t-x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [ht.1,hx.2,hv])
    have hcostevent := eventually_right_lt hdemand (hnegative.trans (by norm_num))
    obtain ⟨z,hxz,hxzdom,hzcost,hzsort,hzZ⟩ :=
      (eventually_mem_nhdsWithin.and (hxevent.and (hcostevent.and (hsortevent.and hZevent)))).exists
    let p' := plusPoint q P z
    have hps : p'.Sorted := by
      dsimp [p',plusPoint,SignedPoint.Sorted]
      rw [abs_of_pos hzZ]
      constructor <;> linarith only [hzsort,hzZ]
    have hpo : p'.Outer q := plus_point_circle hroots.2.2.2.2.le (by linarith only [hzZ])
    have hpa : p'=arc q p'.y := eq_outerAt_of_outer hps hpo
    have hproj := plus_contact_and_demand (q := q) (P := P) ⟨hxzdom.1.1,hxzdom.1.2.le⟩ hxzdom.2
    have hproj0 := plus_contact_and_demand (q := q) (P := P) ⟨hx.1,hx.2.le⟩
      (show t-x∈Icc 0 (7/10 : ℝ) by constructor <;> linarith only [ht.1,hx.2,hv])
    refine ⟨z,p'.y,hxz,hxzdom.1.2,(SignedPoint.outer_bounds hps hpo).2.1,?_,?_⟩
    · dsimp [contact]
      rw [← hpa]
      dsimp [p',P] at hproj
      linarith only [hproj.1]
    · dsimp [required]
      rw [← hpa]
      have ha : (plusPoint q P x).a=(arc q y).a := congrArg SignedPoint.a hrec
      have hy' : (plusPoint q P x).y=y := congrArg SignedPoint.y hrec
      have h0 := hproj0.2
      rw [ha,hy'] at h0
      have h1 : edgeWidth (t-z)-p'.a*Real.sin (t-z)-p'.y*Real.cos (t-z)=plusDemand q P t z :=
        hproj.2
      linarith only [h0,h1,hzcost]

/-- A primary pair of opposite signs has an aligned endpoint on the circle of the same `q`. -/
theorem first_negative_alignment {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : 0≤B ∧ B≤axisCoordinate q)
    (hu : u∈Ico (-7/10 : ℝ) 0) (hv : v∈Ioc 0 (7/10 : ℝ))
    (ht : 0<u+v)
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (hfirst : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (hsecond : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    ∃ p' : SignedPoint, p'.Sorted ∧ p'.Outer q ∧ p'.AvoidsCore ∧
      B-p'.y=1 ∧ edgeWidth (u+v)≤p'.a*Real.sin (u+v)+p'.y*Real.cos (u+v)+D := by
  let t := u+v
  have htmem : t∈Ioc 0 (7/10 : ℝ) := ⟨ht,by dsimp [t]; linarith [hu.2,hv.2]⟩
  obtain ⟨p₀,hp₀,ho₀,hcore₀,hfirst₀,hsecond₀⟩ :=
    AffineCircleEntry.primary_outer_entry hp hcore hc
      (show |u|≤frameCap by rw [abs_of_neg hu.2]; show -u≤7/10; linarith [hu.1])
      htmem hfirst hsecond
  have harc₀ := eq_outerAt_of_outer hp₀ ho₀
  have hy₀ := (SignedPoint.outer_bounds hp₀ ho₀).2.1
  have hcontact₀ : 0≤contact q B u p₀.y := by
    rw [harc₀] at hfirst₀
    exact sub_nonneg.mpr hfirst₀
  have hcost₀ : required q t u p₀.y≤D := by
    dsimp [required,t]
    rw [show u+v-u=v by ring,← harc₀]
    linarith
  obtain ⟨m,hm,hcost,hmin⟩ := contact_region_minimum
    (l := u) (u := 0) (a := -diagonalCoordinate q) (b := diagonalCoordinate q)
    (contact := fun z : ℝ×ℝ => contact q B z.1 z.2)
    (cost := fun z : ℝ×ℝ => required q t z.1 z.2)
    (by dsimp [contact,arc,SignedPoint.outerAt,edgeWidth,pairWidth]; fun_prop)
    (by dsimp [required,arc,SignedPoint.outerAt,edgeWidth,pairWidth]; fun_prop)
    (p₀ := (u,p₀.y)) ⟨⟨le_rfl,hu.2.le⟩,abs_le.mp hy₀,hcontact₀⟩
  have hmv : t-m.1∈Icc 0 (7/10 : ℝ) := by
    constructor <;> dsimp [t] <;> linarith [hm.1.1,hm.1.2,hv.2,ht]
  have hmx : m.1∈Icc (-7/10 : ℝ) 0 := ⟨hu.1.trans hm.1.1,hm.1.2⟩
  have hact := upper_or_contact_at_minimum (x := m.1) (y := m.2)
    (contact := fun z : ℝ×ℝ => contact q B z.1 z.2)
    (cost := fun z : ℝ×ℝ => required q t z.1 z.2) hm hmin
    (by dsimp [contact,arc,SignedPoint.outerAt,edgeWidth,pairWidth]; fun_prop)
    (required_strictAnti hqL hmv)
  have hzero : contact q B m.1 m.2=0 := by
    rcases hact with hdiag | hzero
    · rw [hdiag] at hm
      exact False.elim (not_lt_of_ge hm.2.2
        (upper_diagonal_impossible hqL hqU hB.2 hmx))
    · exact hzero
  have hxzero : m.1=0 := by
    by_contra hn
    have hxneg : m.1<0 := lt_of_le_of_ne hm.1.2 hn
    obtain ⟨x,y,hxm,hx0,hy,hcontact,hbetter⟩ := right_improvement hqL hqU hB
      ⟨hmx.1,hxneg⟩ htmem hmv.2 (abs_le.mpr hm.2.1) hzero
    have hxmin : x∈Icc u 0 := ⟨hm.1.1.trans hxm.le,hx0.le⟩
    have hbad := hmin (x,y) hxmin (abs_le.mp hy) hcontact.ge
    exact not_lt_of_ge hbad hbetter
  let p' := arc q m.2
  obtain ⟨hps,hpo,hpc⟩ := SignedPoint.outerAt_spec hqL (abs_le.mpr hm.2.1)
  refine ⟨p',hps,hpo,hpc,?_,?_⟩
  · rw [hxzero] at hzero
    have h : B+(arc q m.2).a*Real.sin 0-m.2*Real.cos 0-edgeWidth 0=0 := hzero
    simp only [Real.sin_zero,Real.cos_zero,edgeWidth_zero] at h
    show B-m.2=1
    linarith
  · have hb := hcost.trans hcost₀
    rw [hxzero] at hb
    have hb' : edgeWidth (u+v-0)-(arc q m.2).a*Real.sin (u+v-0)-
        m.2*Real.cos (u+v-0)≤D := hb
    simp only [sub_zero] at hb'
    show edgeWidth (u+v)≤(arc q m.2).a*Real.sin (u+v)+m.2*Real.cos (u+v)+D
    linarith

/-- The mirror statement, by local reflection, which exchanges the primary inequalities and
negates only the signed tangent of the point; E and the other states are untouched. -/
theorem second_negative_alignment {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hD : 0≤D ∧ D≤axisCoordinate q)
    (hu : u∈Ioc 0 (7/10 : ℝ)) (hv : v∈Ico (-7/10 : ℝ) 0)
    (ht : 0<u+v)
    (hp : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (hfirst : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (hsecond : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    ∃ p' : SignedPoint, p'.Sorted ∧ p'.Outer q ∧ p'.AvoidsCore ∧
      p'.y+D=1 ∧ edgeWidth (u+v)≤B+p'.a*Real.sin (u+v)-p'.y*Real.cos (u+v) := by
  obtain ⟨p',hps,hpo,hpc,hfirst',hsecond'⟩ := first_negative_alignment (D := B) hqL hqU hD
    hv hu (by linarith)
    ((SignedPoint.reflect_sorted p).mpr hp)
    ((SignedPoint.reflect_avoidsCore p).mpr hcore)
    ((SignedPoint.reflect_contained p q).mpr hc)
    (by dsimp [SignedPoint.reflect]; linarith [hsecond])
    (by dsimp [SignedPoint.reflect]; linarith [hfirst])
  refine ⟨p'.reflect,(SignedPoint.reflect_sorted p').mpr hps,
    (SignedPoint.reflect_outer p' q).mpr hpo,(SignedPoint.reflect_avoidsCore p').mpr hpc,?_,?_⟩
  · dsimp [SignedPoint.reflect]
    linarith
  · rw [add_comm v u] at hsecond'
    dsimp [SignedPoint.reflect]
    linarith

end NegativeContact
end SquaresInCircles.Eight