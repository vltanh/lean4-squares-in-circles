module

public import SquaresInCircles.Eight.Owners.Nonpositive.DE2PrimaryBound

/-!
# Eight squares: no original nonpositive E frame lies above H

The primary EH1 source moves on E's own
original circle.  The actual source radial inequality supplies the
primary reserve used in that construction.  Every non-E point, frame,
and unaffected owner is literal at the resulting E=H cycle.  Combining
this with the rotated EH0 gate exhausts the original allowed EH owners.
-/

section
/-!
## A primary E contact above H reaches H on its original circle

The negative EH1 contact puts both the
original tangent and its aligned value below .1.  The original E corner,
rather than a lifted circle, is used throughout.  Retaining the original
primary in the angular estimate supplies a strict projection reserve on
the full frame interval and gives DE3 strict at the actual E=H endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NonpositiveEH1Transport
open NonpositiveEH0Transport

theorem original_root_bounds {E : SignedPoint} {y : ℝ}
    (hEa : 353/500<E.a) (hy : y∈Icc 0 (1/10:ℝ)) :
    (23/20:ℝ)<root E.circle y ∧
      (root E.circle y)^2=E.circle-(y+1/2)^2 := by
  have hsource : (603/500:ℝ)<E.a+1/2 := by linarith
  have hsource2 : (603/500:ℝ)^2<(E.a+1/2)^2 := by nlinarith
  have hminor : (1/2:ℝ)^2≤(|E.y|+1/2)^2 := by nlinarith [abs_nonneg E.y]
  have htarget := pow_le_pow_left₀ (show 0≤y+1/2 by linarith [hy.1])
    (show y+1/2≤3/5 by linarith [hy.2]) 2
  have hrad : (23/20:ℝ)^2<E.circle-(y+1/2)^2 := by
    dsimp [SignedPoint.circle]
    norm_num at htarget hsource2 hminor
    nlinarith
  have hrad0 : 0<E.circle-(y+1/2)^2 := by linarith
  have hs := Real.sq_sqrt hrad0.le
  have hn := Real.sqrt_nonneg (E.circle-(y+1/2)^2)
  refine ⟨?_,hs⟩
  dsimp [root]
  nlinarith

theorem original_primary_value {E : SignedPoint}
    (hEa : 0≤E.a) (hEy : E.y≤0) : primary E.circle (-E.y)=E.a := by
  have he : E.circle-(-E.y+1/2)^2=(E.a+1/2)^2 := by
    simp [SignedPoint.circle,abs_of_nonpos hEy]
  dsimp [primary,root]
  rw [he,Real.sqrt_sq (show 0≤E.a+1/2 by linarith)]
  ring

theorem original_M_hasDerivAt {E : SignedPoint} {α y : ℝ}
    (hEa : 353/500<E.a) (hy : y∈Icc 0 (1/10:ℝ)) :
    HasDerivAt (M E.circle α) (Md E.circle α y) y := by
  have hr := original_root_bounds hEa hy
  have hr0 : 0<root E.circle y := by linarith [hr.1]
  have harg : E.circle-(y+1/2)^2≠0 := by nlinarith [hr.2]
  have hd := ((hasDerivAt_const y E.circle).sub
    (((hasDerivAt_id y).add_const (1/2)).pow 2)).sqrt harg
  have hp : HasDerivAt (primary E.circle) (-((y+1/2)/root E.circle y)) y := by
    convert hd.sub_const (1/2) using 1
    · rfl
    · dsimp [root]
      field_simp [hr0.ne']
      ring
  convert ((hp.sub_const (1/2)).mul_const (Real.sin α)).add
    (((hasDerivAt_id y).sub_const (1/2)).mul_const (Real.cos α)) using 1
  · rfl
  · dsimp [Md]
    ring

theorem original_M_rate {E : SignedPoint} {α y : ℝ}
    (hEa : 353/500<E.a) (hα : α∈Icc 0 (27/100:ℝ)) (hy : y∈Icc 0 (1/10:ℝ)) :
    (41/50:ℝ)<Md E.circle α y := by
  have hr := (original_root_bounds hEa hy).1
  have hr0 : 0<root E.circle y := by linarith
  have hratio : (y+1/2)/root E.circle y<12/23 := by
    apply (div_lt_iff₀ hr0).2
    linarith [hy.2]
  have hs : 0≤Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])
  have hsu := (Real.sin_le hα.1).trans hα.2
  have hprod := mul_le_mul_of_nonneg_right hratio.le hs
  have hsq := pow_le_pow_left₀ hα.1 hα.2 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := α)
  norm_num at hsq
  dsimp [Md]
  nlinarith

theorem original_M_growth {E : SignedPoint} {α b c : ℝ}
    (hEa : 353/500<E.a) (hα : α∈Icc 0 (27/100:ℝ))
    (hb : b∈Icc 0 (1/10:ℝ)) (hc : c∈Icc 0 (1/10:ℝ)) (hbc : b≤c) :
    (41/50)*(c-b)≤M E.circle α c-M E.circle α b := by
  exact derivative_reserve
    (fun y hy => (original_M_hasDerivAt hEa hy).continuousAt.continuousWithinAt)
    (fun y hy => original_M_hasDerivAt hEa (Ioo_subset_Icc_self hy))
    (fun y hy => (original_M_rate hEa hα (Ioo_subset_Icc_self hy)).le) hb hc hbc

theorem original_angular_bounds {E : SignedPoint} {α : ℝ}
    (hEa : 353/500<E.a) (hEy : E.y≤0) (hα : α∈Icc 0 (27/100:ℝ)) :
    -(1/2:ℝ)≤M E.circle α (-E.y) ∧
      N E.circle α (-E.y)≤E.a-73/200 := by
  have hval := original_primary_value (show 0≤E.a by linarith) hEy
  have hs : 0≤Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2,Real.pi_gt_three])
  have hsu := (Real.sin_le hα.1).trans hα.2
  have hsq := pow_le_pow_left₀ hα.1 hα.2 2
  have hc : 0≤Real.cos α := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hcu := Real.cos_le_one α
  have hfirst := mul_nonneg (show 0≤E.a-1/2 by linarith) hs
  have hsecond := mul_nonneg (show 0≤ -E.y by linarith) hc
  have hthird := mul_le_mul_of_nonneg_left hcu (show 0≤E.a-1/2 by linarith)
  have hfourth := mul_nonneg (show 0≤ -E.y by linarith) hs
  simp only [M,N,hval]
  constructor <;> nlinarith

/-- The coefficient of the actual original primary is kept through the
rotation estimate.  A universal 1.016 ceiling would lose this reserve
when E's own circle is smaller than the working circle. -/
theorem original_strict_gain {E : SignedPoint} {α x c : ℝ}
    (hEa : 353/500<E.a) (hEu : E.a<283/200) (hEy : E.y≤0)
    (hα : α∈Icc 0 (27/100:ℝ)) (hx : x∈Ioc 0 (7/10:ℝ))
    (hb : -E.y∈Icc 0 (1/10:ℝ)) (hc : c∈Icc 0 (1/10:ℝ)) (hbc : -E.y≤c)
    (hcontact : (E.a+1/2)*Real.sin x-(-E.y+1/2)*(1-Real.cos x)≤c-(-E.y)) :
    (1483/10000)*Real.sin x<M E.circle α c-M E.circle (α+x) (-E.y) := by
  have hg := original_M_growth hEa hα hb hc hbc
  have hang := original_angular_bounds hEa hEy hα
  have hs : 0<Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hloss : 0≤1-Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  have hcos := AlignedMixedE.cosine_loss ⟨hx.1.le,hx.2⟩
  have hsmall := mul_le_mul_of_nonneg_right
    (show -E.y+1/2≤3/5 by linarith [hb.2]) hloss
  have hm := mul_le_mul_of_nonneg_right hang.1 hloss
  have hn := mul_le_mul_of_nonneg_right hang.2 hs.le
  have ha := mul_lt_mul_of_pos_right hEu hs
  rw [angular_identity]
  nlinarith

/-- The primary above-H source reaches an actual aligned E on exactly
its original circle.  It requires no radial kind or abstract path. -/
theorem endpoint_state {q α x : ℝ} {H D E : SignedPoint}
    (hHu : H.a<11/10) (hEs : E.Sorted)
    (hEa : 353/500<E.a) (hEu : E.a<283/200) (hEy : E.y≤0) (hEc : E.Contained q)
    (hα : α∈Icc 0 (27/100:ℝ)) (hx : x∈Ioc 0 (7/10:ℝ))
    (hsum : α+x≤7/10)
    (hDE : quarterFeasible D E (α+x) 3)
    (hEH : quarterFeasible E H (-x) 1) :
    ∃P : EInteriorGeometry.State,
      EInteriorGeometry.Feasible H.a D.a α q P ∧ P.2.2=α ∧
      EInteriorGeometry.corner P=E.circle ∧
      EInteriorGeometry.W P.2.2<EInteriorGeometry.deValue D.a P ∧
      EInteriorGeometry.W (α-P.2.2)=EInteriorGeometry.ehValue H.a α P := by
  let b : ℝ := -E.y
  let c : ℝ := H.a-1
  have hb0 : 0≤b := by dsimp [b]; linarith
  have hsort : b≤E.a := by simpa [b,abs_of_nonpos hEy] using hEs.2
  have hxsin : 0<Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2,Real.pi_gt_three])
  have hxcos : 0<Real.cos x := by linarith [(transport_trig ⟨hx.1.le,hx.2⟩).1]
  have hphi : 0<Real.sin x+Real.cos x-1 := by
    have hp := mul_pos hxsin hxcos
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hcontact : (E.a+1/2)*Real.sin x-(b+1/2)*(1-Real.cos x)≤c-b := by
    have h : edgeWidth (-x)≤H.a+E.a*Real.sin (-x)+E.y*Real.cos (-x) := hEH
    rw [edgeWidth_negative_formula ⟨hx.1.le,hx.2⟩,Real.cos_neg,Real.sin_neg] at h
    dsimp only [c,b]
    linarith
  have hpos : 0<(E.a+1/2)*Real.sin x-(b+1/2)*(1-Real.cos x) := by
    have h1 := mul_nonneg (sub_nonneg.mpr hsort) hxsin.le
    have h2 := mul_pos (show 0<b+1/2 by linarith) hphi
    nlinarith
  have hbc : b<c := by linarith
  have hc : c∈Icc 0 (1/10:ℝ) := by dsimp [c] at *; constructor <;> linarith
  have hb : b∈Icc 0 (1/10:ℝ) := ⟨hb0,hbc.le.trans hc.2⟩
  have hgain := original_strict_gain hEa hEu hEy hα hx hb hc hbc.le hcontact
  have hsumdom : α+x∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hx.1],hsum⟩
  have hsource : 0≤D.a-1/2+M E.circle (α+x) b := by
    have hval := original_primary_value hEs.1.le hEy
    have h : edgeWidth (α+x)≤D.a+E.a*Real.sin (α+x)-E.y*Real.cos (α+x) := hDE
    rw [edgeWidth_positive_formula hsumdom] at h
    dsimp only [M,b]
    rw [hval]
    linarith
  have htarget : 0<D.a-1/2+M E.circle α c := by
    have hg0 : 0<(1483/10000:ℝ)*Real.sin x := mul_pos (by norm_num) hxsin
    linarith
  let P : EInteriorGeometry.State := (primary E.circle c,c,α)
  have hroot := original_root_bounds hEa hc
  have hcircle : EInteriorGeometry.corner P=E.circle := by
    dsimp [P,EInteriorGeometry.corner,primary]
    linear_combination hroot.2
  have hDEstrict : EInteriorGeometry.W P.2.2<EInteriorGeometry.deValue D.a P := by
    dsimp [EInteriorGeometry.W,EInteriorGeometry.deValue,P,M] at *
    linarith
  have hEHexact : EInteriorGeometry.W (α-P.2.2)=EInteriorGeometry.ehValue H.a α P := by
    simp [P,EInteriorGeometry.W,EInteriorGeometry.ehValue,c]
  refine ⟨P,?_,rfl,hcircle,hDEstrict,hEHexact⟩
  exact {
    b_nonneg := hc.1
    sorted := by change c≤primary E.circle c; dsimp [primary]; linarith [hc.2,hroot.1]
    angle := ⟨hα.1,le_rfl⟩
    circle := hcircle.trans_le hEc
    DE := hDEstrict.le
    EH := hEHexact.le }

end SquaresInCircles.Eight.NonpositiveEH1Transport
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SignedCycle
open Candidate

/-- A primary source above H reaches an actual same-q E=H cycle on
exactly its original E circle.  The endpoint has strict actual DE slack,
and no loss is charged to a circle which was only lifted to a cap. -/
theorem HardInput.nonpositive_above_EH1_endpoint {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHorder : I.cycle.theta H<I.cycle.theta E)
    (hEH1 : I.cycle.Feasible E 1) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      (∀i, (J.cycle.point i).circle=(I.cycle.point i).circle) ∧
      (∀i, i≠D → i≠E → J.witnesses.owner i=I.witnesses.owner i) ∧
      J.cycle.theta E=I.cycle.theta H ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 ∧ 0<J.cycle.slack D 3 := by
  have hb := I.nonpositive_composite_bounds hq hAB hAG hGH hDT hTB hHG hTD
  have hrad := (I.nonpositive_E_radial hq hAB hAG hGH hDT hTB hHG hTD).2
  have hHrad : (I.cycle.point H).y≤(I.cycle.point E).a := by
    have hh := (le_max_left |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonneg I.anchors_normal.H_nonneg] using hh
  have hEa : (353/500:ℝ)<(I.cycle.point E).a := hb.H_tangent.1.trans_le hHrad
  have hEu := (SignedPoint.coordinate_bounds (I.necessary.sorted E)
    (I.necessary.core E) (I.necessary.contained E) hq).2.1
  have hDEorder : I.cycle.theta D≤I.cycle.theta E :=
    (sub_nonneg.mp hb.span_nonneg).trans hEHorder.le
  have hDE := I.nonpositive_DE_primary_of_nonneg hq hAB hAG hGH hDT hTB hHG hTD hDEorder
  let α := I.cycle.theta H-I.cycle.theta D
  let x := I.cycle.theta E-I.cycle.theta H
  have hα : α∈Icc 0 (27/100:ℝ) := ⟨hb.span_nonneg,hb.span_lt.le⟩
  have hx : x∈Ioc 0 (7/10:ℝ) :=
    ⟨sub_pos.mpr hEHorder,(le_abs_self _).trans (I.necessary.spread E H)⟩
  have hsum : α+x≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread E D)
    dsimp [α,x,frameCap] at *
    linarith
  have hDE' : quarterFeasible (I.cycle.point D) (I.cycle.point E) (α+x) 3 := by
    have heq : α+x=I.cycle.theta E-I.cycle.theta D := by dsimp [α,x]; ring
    simpa [Feasible,slack,edge,word,delta,next,D,E,quarterFeasible,sub_nonneg,heq] using hDE
  have hEH' : quarterFeasible (I.cycle.point E) (I.cycle.point H) (-x) 1 := by
    have heq : -x=I.cycle.theta H-I.cycle.theta E := by dsimp [x]; ring
    simpa [Feasible,slack,edge,word,delta,next,E,H,quarterFeasible,sub_nonneg,heq] using hEH1
  obtain ⟨P,hP,hPangle,hPcircle,hPDE,hPEH⟩ :=
    NonpositiveEH1Transport.endpoint_state hb.H_primary.2 (I.necessary.sorted E)
      hEa hEu I.E_nonpos (I.necessary.contained E) hα hx hsum hDE' hEH'
  let J := I.fromNonpositiveEInterior hq hb hP
  have hfixed (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle P i hi
  have hcircle (i : Vertex) : (J.cycle.point i).circle=(I.cycle.point i).circle := by
    by_cases hi : i=E
    · subst i
      exact (eInteriorCycle_circle hP.b_nonneg).trans hPcircle
    · rw [(hfixed i hi).1]
  have howner (i : Vertex) (hiD : i≠D) (hiE : i≠E) :
      J.witnesses.owner i=I.witnesses.owner i := by
    simp [J,HardInput.fromNonpositiveEInterior,Witnesses.eInterior,hiD,hiE]
  have hJEHframe : J.cycle.theta E=I.cycle.theta H := by
    change I.cycle.theta D+P.2.2=I.cycle.theta H
    rw [hPangle]
    dsimp [α]
    ring
  have hJDE : J.cycle.Feasible D 3 := eInteriorCycle_DE (by linarith [hb.span_lt]) hP
  have hJEH : J.cycle.Feasible E 1 := eInteriorCycle_EH (by linarith [hb.span_lt]) hP
  have hstrict : 0<J.cycle.slack D 3 := by
    have hu : P.2.2∈Icc 0 (7/10:ℝ) :=
      ⟨hP.angle.1,by linarith [hP.angle.2,hb.span_lt]⟩
    have hw : EInteriorGeometry.W P.2.2=edgeWidth P.2.2 := by
      rw [edgeWidth_positive_formula hu]
      rfl
    rw [hw] at hPDE
    change 0<(eInteriorCycle I.cycle P).slack D 3
    simpa [eInteriorCycle,slack,edge,word,delta,next,D,E,
      EInteriorGeometry.deValue,quarterProjection,sub_pos] using hPDE
  exact ⟨J,hfixed,hcircle,howner,hJEHframe,hJDE,hJEH,hstrict⟩

private theorem r60_feasible_congr {C C' : SignedCycle} {i : Vertex}
    (h1 : C'.point i=C.point i) (h2 : C'.point (next i)=C.point (next i))
    (h3 : C'.theta i=C.theta i) (h4 : C'.theta (next i)=C.theta (next i)) (j : Fin 4) :
    C'.Feasible i j ↔ C.Feasible i j := by
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

theorem HardInput.nonpositive_above_EH1_impossible {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hEHorder : I.cycle.theta H<I.cycle.theta E)
    (hEH1 : I.cycle.Feasible E 1) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  obtain ⟨J,hfixed,hcircle,howner,hJEHframe,hJDE,hJEH,hstrict⟩ :=
    I.nonpositive_above_EH1_endpoint hcap hAB hAG hGH hDT hTB hHG hTD hEHorder hEH1
  have hH := hfixed H (by decide)
  have hG := hfixed G (by decide)
  have hA := hfixed A (by decide)
  have hB := hfixed B (by decide)
  have hT := hfixed T (by decide)
  have hD := hfixed D (by decide)
  apply J.nonpositive_EH_impossible hqL hq
  · rw [hA.2,hB.2]; exact hAB
  · rw [hA.1,hB.1]; exact hnorm
  · rw [hA.2,hG.2]; exact hAG
  · rw [hG.2,hH.2]; exact hGH
  · rw [hD.2,hT.2]; exact hDT
  · rw [hT.2,hB.2]; exact hTB
  · have hn : next H=G := by decide
    exact (r60_feasible_congr hH.1 (by rw [hn]; exact hG.1) hH.2 (by rw [hn]; exact hG.2) 0).2 hHG
  · have hn : next T=D := by decide
    exact (r60_feasible_congr hT.1 (by rw [hn]; exact hD.1) hT.2 (by rw [hn]; exact hD.2) 2).2 hTD
  · exact hJEHframe.trans hH.2.symm
  · exact hJDE
  · exact hJEH

/-- Exhaustion is over the actual selected original EH owner.  There
is no frame-placement hypothesis on the original E. -/
theorem HardInput.nonpositive_E_le_H {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    I.cycle.theta E≤I.cycle.theta H := by
  by_contra! habove
  have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
    simpa [normalOwners,E] using I.witnesses.allowed E
  rcases hj with hj | hj
  · have hEH0 : I.cycle.Feasible E 0 := by simpa [hj] using I.witnesses.feasible E
    exact I.nonpositive_above_EH0_impossible hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
      habove hEH0
  · have hEH1 : I.cycle.Feasible E 1 := by simpa [hj] using I.witnesses.feasible E
    exact I.nonpositive_above_EH1_impossible hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
      habove hEH1

end SquaresInCircles.Eight.SignedCycle
end
end
end
