module

public import SquaresInCircles.Eight.TableFree.NegativeNoncancelingOuter

/-!
# Direct positive noncanceling alignment on the large middle tangent

Uncompiled draft.  A remains at its original circle value.  The original
G circle is compared at the largest ordinate permitted by GA0, and the
inverse rotation bounds its transverse complement by A's actual tangent.
This gives a strict reserve on the original H/A composite, with no
temporary lift of A and no loss of an inherited source-circle inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.PositiveNoncancelingOuter
open PositiveCancelingOuter HardCancelingOuter

theorem trigonometric_reserve {e : ℝ} (he : e∈Ioc 0 (7/10 : ℝ)) :
    e/30<(17/200)*Real.sin e-(1-Real.cos e)^2/2 := by
  have hs := sin_nine_tenths he
  have hc0 : 0≤1-Real.cos e := sub_nonneg.mpr (Real.cos_le_one e)
  have hc : 1-Real.cos e≤e^2/2 := by linarith [Real.one_sub_sq_div_two_le_cos e]
  have hcsq := pow_le_pow_left₀ hc0 hc 2
  have he3 := pow_le_pow_left₀ he.1.le he.2 3
  have he4 := mul_le_mul_of_nonneg_left he3 he.1.le
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
  have hAu := (A.coordinate_bounds hAs hAcore hAc hq).2.1
  have hVupper := V_upper hAa (by linarith : 0≤A.y) hz
  have hGA' : -G.y+1/2≤V A (Θ+e) := by
    have hh := hGA
    rw [quarterFeasible,edgeWidth_negative_formula hz] at hh
    simp [quarterProjection,Real.cos_neg,Real.sin_neg] at hh
    dsimp [V]
    linarith
  have hV : 1/2≤V A (Θ+e) := by linarith
  have hVU : V A (Θ+e)<183/200 := by linarith
  let J := SignedPoint.outerAt q (V A (Θ+e)-1/2)
  have hJy0 : 0≤V A (Θ+e)-1/2 := by linarith
  have hJbound : |V A (Θ+e)-1/2|≤diagonalCoordinate q := by
    rw [abs_of_nonneg hJy0]
    linarith [(uniform_circle_reserves hqL hq).1]
  obtain ⟨hJs,hJo,hJcore⟩ := SignedPoint.outerAt_spec hqL hJbound
  have hJcircle : (J.a+1/2)^2+(V A (Θ+e))^2=q := by
    simpa [J,SignedPoint.Outer,SignedPoint.circle,SignedPoint.outerAt,
      abs_of_nonneg hJy0] using hJo
  have hsupport := sorted_support_mono
    (H := G.reflect) (J := J) (by simpa using hGs) hJs
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (show 0≤J.y from hJy0)
    (show G.reflect.circle≤J.circle by simpa using hGc.trans_eq hJo.symm)
    (show G.reflect.y≤J.y by dsimp [SignedPoint.reflect,J,SignedPoint.outerAt]; linarith)
    he'
  have hw : J.a+1/2<383/200 := by
    have hV2 := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num) hV 2
    dsimp [qCap] at hq
    nlinarith [hJs.1]
  have hU := U_lower hAa hAy hz ⟨he.le,by linarith⟩ hV
  have hgain : Real.sin e*(J.a+1/2-U A (Θ+e)-1)+1-Real.cos e≤
      -(17/200)*Real.sin e+(1-Real.cos e)^2/2 := by
    have hs := (transport_trig he').2.2.1
    have hm := mul_le_mul_of_nonneg_left
      (show J.a+1/2-U A (Θ+e)-1≤ -(17/200)-(1/2)*Real.sin e by linarith) hs
    nlinarith [Real.sin_sq_add_cos_sq e]
  have hpair : 1≤PositiveCancelingOuter.F H A Θ+
      Real.sin e*(J.a+1/2-U A (Θ+e)-1)+1-Real.cos e := by
    have hh := hHG
    rw [zeroFeasible,edgeWidth_positive_formula he'] at hh
    simp [zeroProjection] at hh
    have hid := V_inverse A Θ e
    dsimp [SignedPoint.reflect,J,SignedPoint.outerAt] at hsupport
    change G.a*Real.sin e+(-G.y)*Real.cos e≤
      J.a*Real.sin e+(V A (Θ+e)-1/2)*Real.cos e at hsupport
    dsimp [PositiveCancelingOuter.F]
    nlinarith
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

end SquaresInCircles.Eight.TableFree.PositiveNoncancelingOuter
