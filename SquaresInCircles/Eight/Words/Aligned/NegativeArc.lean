module

public import SquaresInCircles.Eight.Words.Aligned.NegativeContact

/-!
# Eight squares: the H/G circle-contact arc and its retained EH0 derivative

At every angle `x` of the frame interval, `movingAnchor` places H on its own circle and `point`
places G on the flat core (`Source.path_geometry`). The EH0 margin `lowMixedSlack` is the
physical projection (`lowMixedSlack_actual`). Its derivative is below `-3/50` wherever the
negative primary is not converted, that is, where GA0 fails
(`Source.lowMixedDerivative_negative`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

def movingAnchor (qH P x : ℝ) : SignedPoint := anchorAt qH (value P x)

def primaryGain (qH P x : ℝ) : ℝ :=
  (2-value P x)*tangentRate (value P x) x/Real.sqrt (qH-(2-value P x)^2)

def lowMixedSlack (qH P e : ℝ) (E : SignedPoint) (x : ℝ) : ℝ :=
  E.y+(movingAnchor qH P x).a*Real.cos (e+x)+
    (movingAnchor qH P x).y*Real.sin (e+x)-
      (1+Real.cos (e+x)+Real.sin (e+x))/2

def lowMixedDerivative (qH P e x : ℝ) : ℝ :=
  ((movingAnchor qH P x).y-1/2)*Real.cos (e+x)-
    primaryGain qH P x*Real.cos (e+x)+
    (tangentRate (value P x) x-(movingAnchor qH P x).a+1/2)*Real.sin (e+x)

theorem Source.path_cap {q t x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Icc 0 t) :
    3/5<value (A.a-1/2) x ∧ value (A.a-1/2) x<183/200 ∧
      3/2-value (A.a-1/2) x≤H.y := by
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hxwide : x∈Icc 0 (7/10 : ℝ) := ⟨hx.1,hx.2.trans I.tilt_cap⟩
  have hanti := value_strictAnti ⟨by linarith,hPup.le⟩
  have hdown := hanti.antitoneOn hxwide ⟨I.tilt_pos.le,I.tilt_cap⟩ hx.2
  have hup := value_le_position ⟨by linarith,hPup.le⟩ hxwide
  have hglow := (I.cuts hq).2.1
  have hHG : 1≤H.y-G.y := by simpa [zeroFeasible,zeroProjection] using I.HG
  constructor
  · linarith
  constructor <;> linarith

theorem Source.path_geometry {q t x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Icc 0 t) :
    (movingAnchor H.circle (A.a-1/2) x).Sorted ∧
      (movingAnchor H.circle (A.a-1/2) x).circle=H.circle ∧
      H.a≤(movingAnchor H.circle (A.a-1/2) x).a ∧
      (movingAnchor H.circle (A.a-1/2) x).y≤H.y ∧
      (movingAnchor H.circle (A.a-1/2) x).AvoidsCore ∧
      0<(movingAnchor H.circle (A.a-1/2) x).y ∧
      0<H.circle-(2-value (A.a-1/2) x)^2 := by
  have hD := I.path_cap hq hx
  exact anchorAt_geometry I.H_sorted (I.cuts hq).2.2.2.1 ⟨hD.1,hD.2.1⟩ hD.2.2

theorem Source.path_tangent_strict {q t x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Ico 0 t) :
    (movingAnchor H.circle (A.a-1/2) x).y<H.y := by
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hm := value_strictAnti ⟨by linarith,hPup.le⟩
    (show x∈Icc 0 (7/10 : ℝ) from ⟨hx.1,hx.2.le.trans I.tilt_cap⟩)
    ⟨I.tilt_pos.le,I.tilt_cap⟩ hx.2
  have hHG : 1≤H.y-G.y := by simpa [zeroFeasible,zeroProjection] using I.HG
  dsimp [movingAnchor,anchorAt]
  linarith

/-- Every point of the arc where GA0 fails is again a `Source`, so the intrinsic cuts and the
circle-rate theorem apply there. -/
theorem Source.atAngle {q t x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (A.a-1/2) x) A (-x) 0) :
    Source q x (movingAnchor H.circle (A.a-1/2) x) (point (A.a-1/2) x) A := by
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hD := I.path_cap hq ⟨hx.1.le,hx.2⟩
  obtain ⟨hHs,hHcircle,hHprimary,hHtangent,hHcore,hHy,hHrad⟩ :=
    I.path_geometry hq ⟨hx.1.le,hx.2⟩
  obtain ⟨hGs,hGcore,hGavoid,hGinside⟩ := point_geometric
    ⟨hPlo,hPup⟩ ⟨hx.1.le,hx.2.trans I.tilt_cap⟩ (by linarith [hD.1])
    (I.cuts hq).2.2.2.2.2.2.2
  exact {
    H_sorted := hHs
    G_sorted := hGs
    A_sorted := I.A_sorted
    H_contained := hHcircle.le.trans I.H_contained
    G_contained := hGinside.le
    A_contained := I.A_contained
    H_core := hHcore
    G_core := hGavoid
    A_core := I.A_core
    H_nonneg := hHy.le
    G_nonpos := by dsimp [point]; linarith [hD.1]
    A_nonneg := I.A_nonneg
    tilt_pos := hx.1
    tilt_cap := hx.2.trans I.tilt_cap
    HG := by simp only [zeroFeasible,zeroProjection,movingAnchor,anchorAt,point,edgeWidth_zero,Real.sin_zero,Real.cos_zero,Matrix.cons_val_zero]; linarith
    GA := (actual_primary_contact (by ring) ⟨hx.1.le,hx.2.trans I.tilt_cap⟩).ge
    no_hard := hnot }

theorem movingAnchor_derivatives {qH P x : ℝ}
    (hc : Real.cos x≠0) (hrad : 0<qH-(2-value P x)^2) :
    HasDerivAt (fun z => (movingAnchor qH P z).a) (-primaryGain qH P x) x ∧
      HasDerivAt (fun z => (movingAnchor qH P z).y) (tangentRate (value P x) x) x := by
  have hD : HasDerivAt (value P) (-tangentRate (value P x) x) x := by
    convert value_hasDerivAt P x hc using 1
    rw [derivative_rewrite P x hc]
    unfold tangentRate
    ring
  have hY : HasDerivAt (fun z => 2-value P z) (tangentRate (value P x) x) x := by
    simpa using hD.const_sub 2
  have hsq : HasDerivAt (fun z => qH-(2-value P z)^2)
      (0-((2:ℕ):ℝ)*(2-value P x)^(2-1)*tangentRate (value P x) x) x :=
    (hasDerivAt_const x qH).sub (hY.pow 2)
  have hroot := hsq.sqrt hrad.ne'
  have hs : Real.sqrt (qH-(2-value P x)^2)≠0 := (Real.sqrt_pos.mpr hrad).ne'
  constructor
  · have h := hroot.sub_const (1/2)
    have hv : (0-((2:ℕ):ℝ)*(2-value P x)^(2-1)*tangentRate (value P x) x)/
        (2*Real.sqrt (qH-(2-value P x)^2))=-primaryGain qH P x := by
      unfold primaryGain
      field_simp
      ring
    rw [hv] at h
    exact h
  · simpa [movingAnchor,anchorAt] using hD.const_sub (3/2)

theorem lowMixedSlack_hasDerivAt {qH P e x : ℝ} (E : SignedPoint)
    (hc : Real.cos x≠0) (hrad : 0<qH-(2-value P x)^2) :
    HasDerivAt (lowMixedSlack qH P e E) (lowMixedDerivative qH P e x) x := by
  obtain ⟨ha,hy⟩ := movingAnchor_derivatives hc hrad
  have he : HasDerivAt (fun z => e+z) 1 x := by simpa using (hasDerivAt_id x).const_add e
  have hcos : HasDerivAt (fun z => Real.cos (e+z)) (-Real.sin (e+x)*1) x :=
    (Real.hasDerivAt_cos (e+x)).comp x he
  have hsin : HasDerivAt (fun z => Real.sin (e+z)) (Real.cos (e+x)*1) x :=
    (Real.hasDerivAt_sin (e+x)).comp x he
  have h := (((hasDerivAt_const x E.y).fun_add (ha.fun_mul hcos)).fun_add
    (hy.fun_mul hsin)).fun_sub
    ((((hasDerivAt_const x (1:ℝ)).fun_add hcos).fun_add hsin).div_const 2)
  convert h using 1
  · rfl
  · unfold lowMixedDerivative
    ring

theorem lowMixedSlack_actual {qH P e x : ℝ} (E : SignedPoint)
    (he : e+x∈Icc 0 (7/10 : ℝ)) :
    lowMixedSlack qH P e E x=
      quarterProjection E (movingAnchor qH P x) (e+x) 0-edgeWidth (e+x) := by
  rw [edgeWidth_positive_formula he]
  simp [lowMixedSlack,quarterProjection]

/-- The scalar derivative inequality, strict over the positive EH0 error interval. All bounds
concern the anchor H and its own circle. -/
theorem low_mixed_rate {X Y r c s : ℝ}
    (hX : 1≤X ∧ X<3/2) (hY : 168/125<Y ∧ Y≤X)
    (hr : 1<r) (hc : 7648/10000<c) (hs : 0≤ s ∧ s<6443/10000) :
    (Y-1)*c-r*Y/X*c+(r-X+1)*s< -(3/50) := by
  have hX0 : 0<X := by linarith
  have hc0 : 0<c := by linarith
  have hlow := mul_le_mul (show (168/125 : ℝ)≤Y by linarith)
    hc.le (by norm_num : (0:ℝ)≤7648/10000) (by linarith : 0≤Y)
  have hupp := mul_le_mul hX.2.le hs.2.le hs.1 (by norm_num : (0:ℝ)≤3/2)
  have hcoef : X*s-Y*c<0 := by nlinarith
  have hstrict := mul_neg_of_pos_of_neg (sub_pos.mpr hr) hcoef
  have hsort := mul_nonneg (sub_nonneg.mpr hY.2)
    (mul_nonneg (sub_nonneg.mpr hX.1) hc0.le)
  have hnum : X*((Y-1)*c+(r-X+1)*s)-r*Y*c<
      X*(X-2)*(c-s) := by nlinarith
  have hcs : 0<c-s := by linarith
  have hshort := mul_lt_mul_of_pos_right hX.2 hcs
  have hbound : (X-2)*(c-s)< -(3/50) := by nlinarith
  have hboundX := mul_lt_mul_of_pos_left hbound hX0
  have hid : ((Y-1)*c-r*Y/X*c+(r-X+1)*s)*X=
      X*((Y-1)*c+(r-X+1)*s)-r*Y*c := by
    field_simp
    ring
  apply lt_of_mul_lt_mul_right _ hX0.le
  rw [hid]
  linarith

theorem Source.lowMixedDerivative_negative {q t e x : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (A.a-1/2) x) A (-x) 0)
    (he : e+x∈Icc 0 (7/10 : ℝ)) :
    lowMixedDerivative H.circle (A.a-1/2) e x< -(3/50) := by
  let J := I.atAngle hq hx hnot
  have hj := J.cuts hq
  have hD := I.path_cap hq ⟨hx.1.le,hx.2⟩
  have hR : intrinsic (value (A.a-1/2) x) x<qCap := by
    have hh := hj.2.2.2.2.2.2.1.trans_le hq
    simpa [point] using hh
  have hr := (circle_rate_reserve ⟨hD.1,hD.2.1.le⟩
    ⟨hx.1.le,hx.2.trans I.tilt_cap⟩ hR).1
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig he
  have hsort : (movingAnchor H.circle (A.a-1/2) x).y≤(movingAnchor H.circle (A.a-1/2) x).a := by
    have hh := J.H_sorted.2
    rwa [abs_of_nonneg J.H_nonneg] at hh
  have h := low_mixed_rate (X := (movingAnchor H.circle (A.a-1/2) x).a+1/2)
    (Y := (movingAnchor H.circle (A.a-1/2) x).y+1/2)
    ⟨by linarith [hj.2.2.2.1],by linarith [hj.2.2.2.2.1]⟩
    ⟨by linarith [hj.2.2.2.1],by linarith⟩ hr hc ⟨hs0,hs⟩
  have hroot : Real.sqrt (H.circle-(2-value (A.a-1/2) x)^2)=
      (movingAnchor H.circle (A.a-1/2) x).a+1/2 := by
    simp [movingAnchor,anchorAt]
  have hheight : 2-value (A.a-1/2) x=
      (movingAnchor H.circle (A.a-1/2) x).y+1/2 := by
    show 2-value (A.a-1/2) x=(3/2-value (A.a-1/2) x)+1/2
    ring
  have hform : lowMixedDerivative H.circle (A.a-1/2) e x=
      ((movingAnchor H.circle (A.a-1/2) x).y+1/2-1)*Real.cos (e+x)-
        tangentRate (value (A.a-1/2) x) x*((movingAnchor H.circle (A.a-1/2) x).y+1/2)/
          ((movingAnchor H.circle (A.a-1/2) x).a+1/2)*Real.cos (e+x)+
        (tangentRate (value (A.a-1/2) x) x-((movingAnchor H.circle (A.a-1/2) x).a+1/2)+1)*
          Real.sin (e+x) := by
    unfold lowMixedDerivative primaryGain
    rw [hroot,hheight]
    ring
  rw [hform]
  exact h

end AlignedNegative
end SquaresInCircles.Eight
