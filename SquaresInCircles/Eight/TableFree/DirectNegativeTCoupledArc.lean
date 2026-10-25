module

public import SquaresInCircles.Eight.TableFree.DirectNegativeTPositiveDE

/-!
# The aligned D/T/E arc on the original D and E circles

Uncompiled source. E has tangent 1-a_D and follows its own original radial
arc. The contact-speed estimate is valid for the entire short positive EH
interval. The actual D primary gains faster than that speed while BT2 is
unavailable, so either retained EH normal gains a uniform strict reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace DirectNegativeT
open AlignedNegative PrimaryCap OutsideE DirectNegativeE

def coupledTangent (qD P x : ℝ) : ℝ := 1-(movingAnchor qD P x).a

def coupledPoint (kind : ArcKind) (q qD P x : ℝ) : SignedPoint :=
  kind.point q (coupledTangent qD P x)

def coupledSlack (kind : ArcKind) (q qD P e : ℝ) (H : SignedPoint)
    (j : Fin 4) (x : ℝ) : ℝ :=
  mixedSlack kind q H j (e+x) (coupledTangent qD P x)

def coupledDerivative (kind : ArcKind) (q qD P e : ℝ) (H : SignedPoint)
    (j : Fin 4) (x : ℝ) : ℝ :=
  -mixedRate kind q H j (e+x) (coupledTangent qD P x) (primaryGain qD P x)

theorem short_tan_bound {p : ℝ} (hp : p∈Icc 0 (21/100 : ℝ)) :
    0≤Real.sin p/Real.cos p ∧ Real.sin p/Real.cos p<28/125 := by
  have ht := transport_trig (show p∈Icc 0 (7/10 : ℝ) from ⟨hp.1,by linarith [hp.2]⟩)
  have hc : 0<Real.cos p := by linarith [ht.1]
  have hs : Real.sin p≤21/100 :=
    ((le_abs_self _).trans (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg hp.1))).trans hp.2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := p)
  have hp2 := pow_le_pow_left₀ hp.1 hp.2 2
  refine ⟨div_nonneg ht.2.2.1 hc.le,(div_lt_iff₀ hc).2 ?_⟩
  nlinarith

/-- The small DE-contact tangent is the essential improvement over the
full outer-E speed bound. Both radial kinds have speed strictly below one. -/
theorem coupled_speed_bound (kind : ArcKind) {q b p : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap) (hb : b∈Ico 0 (39/250 : ℝ))
    (hp : p∈Icc 0 (21/100 : ℝ)) :
    contactSpeed (kind.primary q b) b (kind.slope q b) p<199/200 := by
  have ht := short_tan_bound hp
  have hc : 0<Real.cos p := transport_cos_pos (by
    rw [abs_of_nonneg hp.1]; linarith [hp.2])
  cases kind with
  | flatCore =>
    have heq : contactSpeed (7/12) b 0 p=1/12+(b+1/2)*(Real.sin p/Real.cos p) := by
      dsimp [contactSpeed]
      field_simp [hc.ne']
      ring
    have hm := mul_le_mul (show b+1/2≤82/125 by linarith [hb.2]) ht.2.le ht.1
      (by norm_num : (0:ℝ)≤82/125)
    simpa only [ArcKind.primary,ArcKind.slope,heq] using
      (show 1/12+(b+1/2)*(Real.sin p/Real.cos p)<199/200 by linarith only [hm])
  | outerCircle =>
    let X := Real.sqrt (q-(b+1/2)^2)
    let Y := b+1/2
    let v := Y/X
    let z := Real.sin p/Real.cos p
    have hY : 1/2≤Y ∧ Y<82/125 := by
      dsimp only [Y]; constructor <;> linarith only [hb.1,hb.2]
    have hY2 : Y^2<(82/125)^2 := pow_lt_pow_left₀ hY.2 (by linarith only [hY.1]) two_ne_zero
    have hY2' : (1/2)^2≤Y^2 := pow_le_pow_left₀ (by norm_num) hY.1 2
    have hqL' : 19577/5000≤q := hqL
    have hqU' : q≤9789/2500 := hqU
    have hrad : (933/500 : ℝ)^2<q-Y^2 := by
      norm_num at hY2 ⊢
      linarith only [hY2,hqL']
    have hrad0 : 0<q-Y^2 := by linarith only [hrad]
    have hX0 : 0<X := Real.sqrt_pos.mpr hrad0
    have hX2 : X^2=q-Y^2 := Real.sq_sqrt hrad0.le
    have hXL : 933/500<X := lt_of_pow_lt_pow_left₀ 2 hX0.le (by rw [hX2]; exact hrad)
    have hXU : X<383/200 := by
      apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
      rw [hX2]
      norm_num at hY2' ⊢
      linarith only [hY2',hqU']
    have hv : 0≤v ∧ v<44/125 := by
      refine ⟨div_nonneg (by linarith only [hY.1]) hX0.le,(div_lt_iff₀ hX0).2 ?_⟩
      linarith only [hY.2,hXL]
    have hz : 0≤z ∧ z<28/125 := ht
    have hvz : 0≤v*z := mul_nonneg hv.1 hz.1
    have hden : 0<1+v*z := by linarith only [hvz]
    have hfrac : v*z/(1+v*z)≤v*z := div_le_self hvz (by linarith only [hvz])
    have heq : contactSpeed (X-1/2) b v p=X-1+v*z/(1+v*z) := by
      have hYeq : b+1/2=v*X := by dsimp only [v,Y]; field_simp
      have hcs : Real.cos p+v*Real.sin p=Real.cos p*(1+v*z) := by
        dsimp only [z]
        field_simp
      have hzc : z*Real.cos p=Real.sin p := div_mul_cancel₀ _ hc.ne'
      have hfr : v*z/(1+v*z)*(1+v*z)=v*z := div_mul_cancel₀ _ hden.ne'
      unfold contactSpeed
      rw [hYeq,hcs,div_eq_iff (mul_pos hc hden).ne']
      linear_combination (-v*X)*hzc-(Real.cos p)*hfr
    have hproduct := mul_le_mul hv.2.le hz.2.le hz.1 (by norm_num : (0:ℝ)≤44/125)
    change contactSpeed (X-1/2) b v p<199/200
    rw [heq]
    linarith only [hXU,hfrac,hproduct]

theorem ArcSource.primary_antitone {q : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) :
    AntitoneOn (kind.primary q) (Icc 0 (-E.y)) := by
  apply antiOn_of_hasDeriv_nonpos (kind.continuous_primary q).continuousOn
  · intro b hb
    exact (I.derivative hqL (Ioo_subset_Icc_self hb)).1
  · intro b hb
    exact neg_nonpos.mpr (I.derivative hqL (Ioo_subset_Icc_self hb)).2.1

theorem ArcSource.mixed_projection_mono {q b p : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hqL : qLow≤q)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10 : ℝ))
    (j : Fin 4) (hj : j=0 ∨ j=1) :
    quarterProjection E H p j≤quarterProjection (kind.point q b) H p j := by
  have hEa : E.a≤kind.primary q b := by
    have hh := ArcSource.primary_antitone I hqL hb
      (show -E.y∈Icc 0 (-E.y) from ⟨neg_nonneg.mpr I.nonpos,le_rfl⟩) hb.2
    have heq : kind.primary q (-E.y)=E.a := congrArg SignedPoint.a I.initial
    rwa [heq] at hh
  have ht := transport_trig hp
  rcases hj with rfl | rfl
  · simp [quarterProjection,ArcKind.point]
    linarith [hb.2]
  · have hprim := mul_nonneg (sub_nonneg.mpr hEa) ht.2.2.1
    have htan := mul_nonneg (show 0≤ -E.y-b by linarith [hb.2])
      (show 0≤Real.cos p by linarith [ht.1])
    simp [quarterProjection,ArcKind.point]
    linarith

theorem coupled_DE_contact (kind : ArcKind) (q qD P x : ℝ) (j : Fin 4)
    (hj : j=2 ∨ j=3) :
    quarterProjection (Dpath qD P x) (coupledPoint kind q qD P x) 0 j=edgeWidth 0 := by
  rcases hj with rfl | rfl <;>
    simp [quarterProjection,Dpath,coupledPoint,coupledTangent,ArcKind.point,
      SignedPoint.reflect,edgeWidth_zero]

theorem coupledSlack_actual (kind : ArcKind) {q qD P e x : ℝ} (H : SignedPoint)
    (j : Fin 4) (hj : j=0 ∨ j=1) (hp : e+x∈Icc 0 (7/10 : ℝ)) :
    coupledSlack kind q qD P e H j x=
      quarterProjection (coupledPoint kind q qD P x) H (e+x) j-edgeWidth (e+x) :=
  mixedSlack_actual kind q H (coupledTangent qD P x) hj hp

theorem ArcSource.coupled_hasDerivAt {q qD P e x : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hqL : qLow≤q)
    (hb : coupledTangent qD P x∈Icc 0 (-E.y))
    (hc : Real.cos x≠0) (hrad : 0<qD-(2-value P x)^2) (j : Fin 4) :
    HasDerivAt (coupledSlack kind q qD P e H j)
      (coupledDerivative kind q qD P e H j x) x := by
  have hD := (movingAnchor_derivatives hc hrad).1
  have hbder : HasDerivAt (coupledTangent qD P) (primaryGain qD P x) x :=
    (hD.const_sub 1).congr_deriv (neg_neg _)
  have hpder : HasDerivAt (fun z : ℝ => e+z) 1 x := by
    simpa using (hasDerivAt_id x).const_add e
  have hcder := (Real.hasDerivAt_cos (e+x)).comp x hpder
  have hsder := (Real.hasDerivAt_sin (e+x)).comp x hpder
  by_cases hj : j=0
  · have hfun : coupledSlack kind q qD P e H j=fun z =>
        (H.a-1/2)*Real.cos (e+z)+(H.y-1/2)*Real.sin (e+z)-coupledTangent qD P z-1/2 := by
      funext z
      simp [coupledSlack,mixedSlack,lowSlack,hj]
    rw [hfun]
    exact ((((hcder.const_mul (H.a-1/2)).fun_add (hsder.const_mul (H.y-1/2))).fun_sub
      hbder).sub_const (1/2)).congr_deriv (by
        simp only [coupledDerivative,mixedRate,hj,lowAngularRate,ite_true]; ring)
  · have ha := (I.derivative hqL hb).1.comp x hbder
    have hfun : coupledSlack kind q qD P e H j=fun z =>
        H.a-1/2+(kind.primary q (coupledTangent qD P z)-1/2)*Real.sin (e+z)-
          (coupledTangent qD P z+1/2)*Real.cos (e+z) := by
      funext z
      simp [coupledSlack,mixedSlack,ehSlack,hj]
    rw [hfun]
    exact (((hasDerivAt_const x (H.a-1/2)).fun_add
      ((ha.sub_const (1/2)).fun_mul hsder)).fun_sub
        ((hbder.add_const (1/2)).fun_mul hcder)).congr_deriv (by
          simp only [coupledDerivative,mixedRate,hj,ite_false,Function.comp_apply]; ring)

theorem Source.coupled_derivative_negative {q t e x : ℝ} {D T B E H : SignedPoint}
    {kind : ArcKind} (I : Source q t D T B) (J : ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0)
    (hb : coupledTangent D.circle (B.a-1/2) x∈Icc 0 (-E.y))
    (hp : e+x∈Icc 0 (21/100 : ℝ)) (j : Fin 4) (hj : j=0 ∨ j=1) :
    coupledDerivative kind q D.circle (B.a-1/2) e H j x< -(1/250) := by
  let a := primaryGain D.circle (B.a-1/2) x
  let b := coupledTangent D.circle (B.a-1/2) x
  have ha : 1<a := I.primary_gain hqU hx hnot
  let K := I.atAngle hqU hx hnot
  have hc := K.cuts hqU
  have hDa : 211/250<(movingAnchor D.circle (B.a-1/2) x).a := by
    have hsort := K.H_sorted.2
    rw [abs_of_nonneg K.H_nonneg] at hsort
    have h := hc.2.2.2.1.trans_le hsort
    rw [SignedPoint.reflect_circle] at h
    exact h
  have hbsmall : b<39/250 := by dsimp only [b,coupledTangent]; linarith only [hDa]
  have hpwide : e+x∈Icc 0 (7/10 : ℝ) := ⟨hp.1,by linarith only [hp.2]⟩
  rcases hj with rfl | rfl
  · have hrate := lowSpeed_bounds hHy hHs hpwide
    have hh : lowAngularRate H (e+x)<2/5 := hrate.2.1.trans_lt hrate.2.2
    simp only [coupledDerivative,mixedRate,ite_true]
    dsimp only [a] at ha
    linarith only [ha,hh]
  · let den := Real.cos (e+x)+kind.slope q b*Real.sin (e+x)
    let U := (kind.primary q b-1/2)*Real.cos (e+x)+(b+1/2)*Real.sin (e+x)
    let β := contactSpeed (kind.primary q b) b (kind.slope q b) (e+x)
    have hgeom := J.geometry hqL hb
    have hv := (J.derivative hqL hb).2
    have hdenβ := contactSpeed_positive hgeom.2.2.2.2.2.1 hb.1 hv.1 hpwide
    have hβ : β<199/200 := coupled_speed_bound kind hqL hqU ⟨hb.1,hbsmall⟩ hp
    have hcos : 97/100<Real.cos (e+x) := by
      have hh := Real.one_sub_sq_div_two_le_cos (x := e+x)
      have hs := pow_le_pow_left₀ hp.1 hp.2 2
      norm_num at hs
      linarith only [hh,hs]
    have hden : 97/100<den := by
      have hprod := mul_nonneg hv.1 (transport_trig hpwide).2.2.1
      dsimp only [den]
      linarith only [hprod,hcos]
    have hid : β*den=U := by
      dsimp only [β,den,U]; unfold contactSpeed; exact div_mul_cancel₀ _ hdenβ.1.ne'
    have hgap := mul_pos (show 0<a-β-1/200 by linarith only [ha,hβ]) hdenβ.1
    have hreserve : 1/250<a*den-U := by linarith only [hgap,hden,hid]
    norm_num only [coupledDerivative,mixedRate,show (1:Fin 4)≠0 by decide,ite_false]
    change -(a*den-U)< -(1/250)
    linarith only [hreserve]

end DirectNegativeT
end SquaresInCircles.Eight.TableFree
