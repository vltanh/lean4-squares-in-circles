module

public import SquaresInCircles.Eight.Owners.Critical.EExclusion
public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.Negative.NoncancelingCycle
public import SquaresInCircles.Eight.Owners.Positive.GAOuterSoleReduction
public import SquaresInCircles.Eight.Owners.Sole.PositiveExclusion

/-!
# Eight squares: positive HG0/TD2 alignment retains the original large-side circle

These actual hard-cycle constructors invoke the
unlifted same-circle reserve.  The source large middle primary decreases
by one sixtieth of the original outer error.  Every other anchor, every
original mixed E witness, and the opposite intermediate are unchanged.
-/

section
/-!
## The sole positive DE primary, with either original E sign

A nonpositive E uses the signed sole-DE stress.
A positive outer E is moved only on its original q circle, with every
frame unchanged. Its actual endpoint is either zero tangent or exact
EH0 contact. The complete sharp contact theorem handles the latter.
No E-sign preservation is assumed for the preceding paired transport.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveEContactExclusion
open Candidate PositiveEContact ExceptionalContactStress

theorem moved_owners {q : ℝ} {C : SignedCycle} (O : Replacement q C) {ab : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) :
    ∀ i,O.cycle.Feasible i (CoreEStress.owners ab 2 0 3 0 i) := by
  intro i
  by_cases hiD : i=D
  · subst i; simpa [CoreEStress.owners,D] using O.DE_actual
  · by_cases hiE : i=E
    · subst i; simpa [CoreEStress.owners,E] using O.EH_actual
    · exact (O.other_feasible i hiD hiE _).2 (hf i)

theorem terminal_contact {q : ℝ} {C : SignedCycle} (O : Replacement q C)
    (he : O.point.y=demand (C.point H) (delta C.theta E)) : Contact O.cycle := by
  dsimp [Contact]
  rw [O.theta_eq,O.unchanged H (by decide)]
  have hE : O.cycle.point E=O.point := by simp [Replacement.cycle,replacePoint]
  rw [hE,he]
  dsimp [demand]
  ring

/-- All signs of an actual outer E are covered at the sharp radius.
The strictly positive original G error is the only strict angle input. -/
theorem sole_DE_false {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0<delta C.theta G) (hD : 0≤delta C.theta D)
    (hE : (C.point E).Outer q)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 3 0 i)) : False := by
  by_cases hy : (C.point E).y≤0
  · exact SolePositiveExclusion.sole_DE_false hQL (hq.trans hsharp.2) hC hn hvar hab hG.le hD hy hf
  · have hDE : C.Feasible D 3 := by simpa [CoreEStress.owners,D] using hf D
    have hEH : C.Feasible E 0 := by simpa [CoreEStress.owners,E] using hf E
    obtain ⟨O⟩ := PositiveEContact.replace hQL hC hE (lt_of_not_ge hy).le hD hDE hEH
    have hnec := O.necessary hC
    have hnormal := O.normal hn
    have hvar' : positiveVariation O.cycle.theta≤frameCap := by simpa only [O.theta_eq] using hvar
    have hG' : 0<delta O.cycle.theta G := by simpa only [O.theta_eq] using hG
    have hD' : 0≤delta O.cycle.theta D := by simpa only [O.theta_eq] using hD
    have hf' := moved_owners O hf
    have hEpoint : O.cycle.point E=O.point := by simp [Replacement.cycle,replacePoint]
    rcases O.terminal with hz | hcontact
    · have hy' : (O.cycle.point E).y≤0 := by rw [hEpoint,hz]
      exact SolePositiveExclusion.sole_DE_false hQL (hq.trans hsharp.2) hnec hnormal hvar'
        hab hG'.le hD' hy' hf'
    · have hy' : 0≤(O.cycle.point E).y := by rw [hEpoint]; exact O.nonnegative
      have hzero := ExceptionalEComplete.original_G_zero hd hsharp hQL hq hnec hnormal hvar'
        hab hG'.le hD' hy' (terminal_contact O hcontact) hf'
      linarith

end SquaresInCircles.Eight.PositiveEContactExclusion
end
end
end

section
/-!
## Direct positive noncanceling alignment on the large middle tangent

A remains at its original circle value.  The original
G circle is compared at the largest ordinate permitted by GA0, and the
inverse rotation bounds its transverse complement by A's actual tangent.
This gives a strict reserve on the original H/A composite, with no
temporary lift of A and no loss of an inherited source-circle inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveNoncancelingOuter
open PositiveCancelingOuter HardCancelingOuter

theorem trigonometric_reserve {e : ℝ} (he : e∈Ioc 0 (7/10 : ℝ)) :
    e/30<(17/200)*Real.sin e-(1-Real.cos e)^2/2 := by
  have hs := sin_nine_tenths he
  have he0 : 0<e := he.1
  have he7 : e≤7/10 := he.2
  have hc0 : 0≤1-Real.cos e := sub_nonneg.mpr (Real.cos_le_one e)
  have hc : 1-Real.cos e≤e^2/2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := e)]
  have hcsq := pow_le_pow_left₀ hc0 hc 2
  have he3 := pow_le_pow_left₀ he0.le he7 3
  have he4 := mul_le_mul_of_nonneg_left he3 he0.le
  nlinarith

theorem U_lower {A : SignedPoint} {z e : ℝ}
    (hAa : 1/2<A.a) (hAy : 1/2≤A.y)
    (hz : z∈Icc 0 (7/10 : ℝ)) (he : e∈Icc 0 z)
    (hV : 1/2≤V A z) : 1+(1/2)*Real.sin e≤U A z := by
  have ht := transport_trig hz
  have hU0 : 0≤U A z := by
    exact add_nonneg (mul_nonneg (by linarith) ht.2.2.1)
      (mul_nonneg (by linarith) (by linarith [ht.1]))
  have hY : U A z*Real.cos z-V A z*Real.sin z=A.y+1/2 := by
    dsimp [U,V]
    linear_combination (A.y+1/2)*(Real.sin_sq_add_cos_sq z)
  have hUc := mul_le_mul_of_nonneg_left ht.2.1 hU0
  have hVs := mul_le_mul_of_nonneg_right hV ht.2.2.1
  have hsin : Real.sin e≤Real.sin z :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [he.1,Real.pi_pos])
      (by linarith [hz.2,Real.pi_gt_three]) he.2
  linarith

theorem V_inverse (A : SignedPoint) (Θ e : ℝ) :
    V A Θ=Real.cos e*V A (Θ+e)+Real.sin e*U A (Θ+e) := by
  have hc := Real.cos_sub (Θ+e) e
  have hs := Real.sin_sub (Θ+e) e
  rw [show Θ+e-e=Θ by ring] at hc hs
  dsimp [V,U]
  rw [hc,hs]
  ring

/-- The strict aligned reserve is proved on the unchanged H/A points.
Only the original G needs its normal weak sign in this local theorem. -/
theorem positive_reserve {q Θ e : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hGs : G.Sorted) (hAs : A.Sorted) (hAcore : A.AvoidsCore)
    (hGc : G.Contained q) (hAc : A.Contained q)
    (hGy : G.y≤0) (hAy : 1/2≤A.y)
    (hΘ : 0≤Θ) (he : 0<e) (hspan : Θ+e≤7/10)
    (hHG : zeroFeasible H G e 0)
    (hGA : quarterFeasible G A (-(Θ+e)) 0) :
    1+e/30<PositiveCancelingOuter.F H A Θ := by
  have hz : Θ+e∈Icc 0 (7/10 : ℝ) := ⟨by linarith,hspan⟩
  have he' : e∈Icc 0 (7/10 : ℝ) := ⟨he.le,by linarith⟩
  have hAa := SignedPoint.primary_gt_half hAs hAcore
  have hAu := (SignedPoint.coordinate_bounds hAs hAcore hAc hq).2.1
  have hVupper := V_upper hAa (by linarith : 0≤A.y) hz
  have hGA' : -G.y+1/2≤V A (Θ+e) := by
    have hh := hGA
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hh
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg] at hh
    unfold V
    linarith
  have hV : 1/2≤V A (Θ+e) := by linarith
  have hVU : V A (Θ+e)<183/200 := by linarith
  have hJy0 : 0≤V A (Θ+e)-1/2 := by linarith
  have hJbound : |V A (Θ+e)-1/2|≤diagonalCoordinate q := by
    rw [abs_of_nonneg hJy0]
    linarith [(uniform_circle_reserves hqL hq).1]
  obtain ⟨hJs,hJo,hJcore⟩ := SignedPoint.outerAt_spec hqL hJbound
  obtain ⟨J,hJ_def⟩ : ∃ J : SignedPoint, J=SignedPoint.outerAt q (V A (Θ+e)-1/2) :=
    ⟨_,rfl⟩
  rw [← hJ_def] at hJs hJo hJcore
  have hJy : J.y=V A (Θ+e)-1/2 := by rw [hJ_def]; rfl
  have hJcircle : (J.a+1/2)^2+(V A (Θ+e))^2=q := by
    have h : J.circle=q := hJo
    rw [SignedPoint.circle,hJy,abs_of_nonneg hJy0,sub_add_cancel] at h
    exact h
  have hsupport := sorted_support_mono
    (H := G.reflect) (J := J) ((SignedPoint.reflect_sorted G).mpr hGs) hJs
    (show 0≤G.reflect.y by simp only [SignedPoint.reflect]; linarith)
    (show 0≤J.y by rw [hJy]; exact hJy0)
    (show G.reflect.circle≤J.circle by
      rw [SignedPoint.reflect_circle]; exact hGc.trans_eq hJo.symm)
    (show G.reflect.y≤J.y by rw [hJy]; simp only [SignedPoint.reflect]; linarith)
    he'
  simp only [SignedPoint.reflect] at hsupport
  rw [hJy] at hsupport
  have hw : J.a+1/2<383/200 := by
    have hV2 := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num) hV 2
    have h2 : (J.a+1/2)^2<(383/200)^2 := by
      norm_num [qCap] at hq hV2 ⊢
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h2
  have hU := U_lower hAa hAy hz ⟨he.le,by linarith⟩ hV
  have hgain : Real.sin e*(J.a+1/2-U A (Θ+e)-1)+1-Real.cos e≤
      -(17/200)*Real.sin e+(1-Real.cos e)^2/2 := by
    have hs := (transport_trig he').2.2.1
    have hm := mul_le_mul_of_nonneg_left
      (show J.a+1/2-U A (Θ+e)-1≤ -(17/200)-(1/2)*Real.sin e by linarith) hs
    linarith [Real.sin_sq_add_cos_sq e]
  have hpair : 1≤PositiveCancelingOuter.F H A Θ+
      Real.sin e*(J.a+1/2-U A (Θ+e)-1)+1-Real.cos e := by
    have hh := hHG
    rw [zeroFeasible,edgeWidth_positive_formula he'] at hh
    simp only [zeroProjection,Matrix.cons_val_zero] at hh
    have hid := V_inverse A Θ e
    unfold PositiveCancelingOuter.F
    rw [hid]
    linarith
  have hr := trigonometric_reserve (show e∈Ioc 0 (7/10 : ℝ) from ⟨he,he'.2⟩)
  linarith

theorem positive_aligned_reserve {q Θ e : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hGs : G.Sorted) (hAs : A.Sorted) (hAcore : A.AvoidsCore)
    (hGc : G.Contained q) (hAc : A.Contained q)
    (hGy : G.y≤0) (hAy : 1/2≤A.y)
    (hΘ : 0≤Θ) (he : 0≤e) (hspan : Θ+e≤7/10)
    (hHG : zeroFeasible H G e 0)
    (hGA : quarterFeasible G A (-(Θ+e)) 0) :
    e/30≤quarterProjection (SignedPoint.flat (H.y-1)) A (-Θ) 0-edgeWidth (-Θ) := by
  have hΘ' : Θ∈Icc 0 (7/10 : ℝ) := ⟨hΘ,by linarith⟩
  by_cases he0 : e=0
  · subst e
    have hh := hHG
    have hg := hGA
    simp [zeroFeasible,zeroProjection] at hh
    simp only [add_zero] at hg
    rw [quarterFeasible,edgeWidth_negative_formula hΘ'] at hg
    simp [quarterProjection,Real.sin_neg,Real.cos_neg] at hg
    rw [edgeWidth_negative_formula hΘ']
    simp [quarterProjection,SignedPoint.flat,Real.sin_neg,Real.cos_neg]
    linarith
  · have hh := positive_reserve hqL hq hGs hAs hAcore hGc hAc hGy hAy hΘ
      (lt_of_le_of_ne he (Ne.symm he0)) hspan hHG hGA
    rw [edgeWidth_negative_formula hΘ']
    dsimp [PositiveCancelingOuter.F,V] at hh
    simp [quarterProjection,SignedPoint.flat,Real.sin_neg,Real.cos_neg]
    linarith

theorem actual_G_alignment {q Θ e : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHcore : H.AvoidsCore) (hAcore : A.AvoidsCore)
    (hHc : H.Contained q) (hGc : G.Contained q) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hGy : G.y≤0) (hAy : 1/2≤A.y)
    (hΘ : 0≤Θ) (he : 0≤e) (hspan : Θ+e≤7/10)
    (hHG : zeroFeasible H G e 0)
    (hGA : quarterFeasible G A (-(Θ+e)) 0) :
    Nonempty (GAlignment q H A Θ (Θ-(2/9)*e)) := by
  have hr := positive_aligned_reserve hqL hq hGs hAs hAcore hGc hAc hGy hAy hΘ he hspan hHG hGA
  apply alignment_of_reserve hqL hq hHs hAs hHcore hAcore hHc hAc hHy
    (by linarith : 0≤A.y) ⟨hΘ,by linarith⟩
  · constructor <;> linarith
  · nlinarith

theorem actual_T_alignment {q Θ e : ℝ} {B T D : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBcore : B.AvoidsCore) (hDcore : D.AvoidsCore)
    (hBc : B.Contained q) (hTc : T.Contained q) (hDc : D.Contained q)
    (hBy : 1/2≤ -B.y) (hTy : 0≤T.y) (hDy : D.y≤0)
    (hΘ : 0≤Θ) (he : 0≤e) (hspan : Θ+e≤7/10)
    (hBT : quarterFeasible B T (-(Θ+e)) 2)
    (hTD : zeroFeasible T D e 2) :
    Nonempty (TAlignment q B D Θ (Θ-(2/9)*e)) := by
  have hHG : zeroFeasible D.reflect T.reflect e 0 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect T D e 2).2 hTD
  have hGA : quarterFeasible T.reflect B.reflect (-(Θ+e)) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T (-(Θ+e)) 2).2 hBT
  obtain ⟨O⟩ := actual_G_alignment hqL hq
    (by simpa using hDs) (by simpa using hTs) (by simpa using hBs)
    (by simpa using hDcore) (by simpa using hBcore)
    (by simpa using hDc) (by simpa using hTc) (by simpa using hBc)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr hTy)
    (by simpa [SignedPoint.reflect] using hBy) hΘ he hspan hHG hGA
  exact ⟨NegativeNoncancelingOuter.reflect_alignment O⟩

end SquaresInCircles.Eight.PositiveNoncancelingOuter
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardInput.positive_HG0_large_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H≤I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hlarge : 1/2≤(I.cycle.point A).y)
    (hHG : I.cycle.Feasible H 0) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A)
      ((I.cycle.theta H-I.cycle.theta A)-(2/9)*(I.cycle.theta G-I.cycle.theta H))) := by
  have hspan : (I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H)≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread G A)
    dsimp [frameCap] at hh
    linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      (I.cycle.theta G-I.cycle.theta H) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-((I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H))) 0 := by
    rw [show -((I.cycle.theta H-I.cycle.theta A)+(I.cycle.theta G-I.cycle.theta H))=
      I.cycle.theta A-I.cycle.theta G by ring]
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg]
      using I.GA_hard
  exact PositiveNoncancelingOuter.actual_G_alignment hqL hq
    (I.necessary.sorted H) (I.necessary.sorted G) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained G) (I.necessary.contained A)
    I.anchors_normal.H_nonneg hGy hlarge (sub_nonneg.mpr hAH)
    (sub_nonneg.mpr hHGorder) hspan hHG' hGA'

theorem HardInput.positive_TD2_large_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T≤I.cycle.theta D)
    (hTy : 0≤(I.cycle.point T).y) (hlarge : 1/2≤ -(I.cycle.point B).y)
    (hTD : I.cycle.Feasible T 2) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D)
      ((I.cycle.theta B-I.cycle.theta D)-(2/9)*(I.cycle.theta D-I.cycle.theta T))) := by
  have hspan : (I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T)≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread B T)
    dsimp [frameCap] at hh
    linarith
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta D-I.cycle.theta T) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-((I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T))) 2 := by
    rw [show -((I.cycle.theta B-I.cycle.theta D)+(I.cycle.theta D-I.cycle.theta T))=
      I.cycle.theta T-I.cycle.theta B by ring]
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg]
      using I.BT_hard
  exact PositiveNoncancelingOuter.actual_T_alignment hqL hq
    (I.necessary.sorted B) (I.necessary.sorted T) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core D)
    (I.necessary.contained B) (I.necessary.contained T) (I.necessary.contained D)
    hlarge hTy I.anchors_normal.D_nonpos (sub_nonneg.mpr hDB)
    (sub_nonneg.mpr hTDorder) hspan hBT' hTD'

end SignedCycle
end SquaresInCircles.Eight
end
end
end
