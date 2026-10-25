module

public import SquaresInCircles.Eight.Owners.Negative.NoncancelingCycle
public import SquaresInCircles.Eight.Owners.Positive.CancelingOuter
public import SquaresInCircles.Eight.Owners.Positive.SmallScalar
public import SquaresInCircles.Eight.Owners.Small.PositiveZeroEndpoint
public import SquaresInCircles.Eight.Owners.Wide.SmallWrongSign
public import SquaresInCircles.Eight.Words.Crossed.SmallWrongSign
public import SquaresInCircles.Eight.Words.Wrong.SignCapture

/-!
# Eight squares: the small positive TD2 alignment at the unchanged original E

Reflection is applied to local necessary
geometry and the already proved invariant endpoint budget.  The local
three-point alignment is then reflected back, producing a new original
hard cycle with only T and B changed.  No reflected E normalization and
no change of the source mixed-edge witnesses is used.
-/

section
/-!
## The signs of the intermediates on the small side after middle alignment

The ordered and the crossed alternatives of the outer frame cover the whole interval `[0.28, 0.5]`
of the middle tangent, and both use the budget of the cycle. So G is negative and T positive
(`HardInput.small_middle_G_negative`, `HardInput.small_middle_T_positive`), with no assumption on
the outer ordering, the opposite intermediate sign or the sign of the outer error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace SignedCycle

theorem HardOuterGeometry.small_middle_G_negative {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGsmall : (I.cycle.point G).y<1/10) : (I.cycle.point G).y<0 := by
  by_contra! hwrong
  by_cases hAH : I.cycle.theta A≤I.cycle.theta H
  · have hTy := I.large_middle_T_positive hq hAB hnorm hTA hAG
      (by linarith [hsmall.2])
    exact I.wide_small_wrong_G_impossible hqL hq hAB hnorm hsmall hTA hAH hTy.le hwrong hGsmall
  · exact I.crossed_small_wrong_G_impossible hqL hq hAB hnorm hsmall hTA hAG
      (lt_of_not_ge hAH) hwrong hGsmall

theorem HardOuterGeometry.small_middle_T_positive {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : -(I.cycle.point B).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hTsmall : -(1/10 : ℝ)<(I.cycle.point T).y) : 0<(I.cycle.point T).y := by
  have hAB' : I.reflected.cycle.theta A=I.reflected.cycle.theta B := by
    change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
    linarith
  have hnorm' : (I.reflected.cycle.point A).y-(I.reflected.cycle.point B).y=1 := by
    change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
    linarith
  have hTA' : I.reflected.cycle.theta T≤I.reflected.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
    linarith
  have hAG' : I.reflected.cycle.theta A≤I.reflected.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta T
    linarith
  have hh := I.reflected.small_middle_G_negative hqL hq hAB' hnorm' hsmall hTA' hAG'
    (show -(I.cycle.point T).y<1/10 by linarith)
  change -(I.cycle.point T).y<0 at hh
  linarith

theorem HardInput.small_middle_G_negative {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) : (I.cycle.point G).y<0 :=
  I.outerGeometry.small_middle_G_negative hqL hq hAB hnorm hsmall hTA hAG
    (I.small_intermediate_signs hq).1

theorem HardInput.small_middle_T_positive {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : -(I.cycle.point B).y∈Icc (7/25 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAG : I.cycle.theta A≤I.cycle.theta G) : 0<(I.cycle.point T).y :=
  I.outerGeometry.small_middle_T_positive hqL hq hAB hnorm hsmall hTA hAG
    (I.small_intermediate_signs hq).2

end SignedCycle
end SquaresInCircles.Eight
end
end
end

section
/-!
## Actual positive small-side alignment without lifting an original anchor

The same original G circle supplies a convex
scalar on its full feasible interval.  The only other scalar endpoint is
an actual zero-G point on that same q-circle, excluded by the unchanged
mixed endpoint budget.  The original H/A composite therefore has strict
slack, part of which is spent on an actual decrease of A's primary.
All other anchors and the opposite intermediate stay fixed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate HardCancelingOuter
namespace SignedCycle

theorem HardOuterGeometry.positive_HG0_small_reserve {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y)
    (hHG : I.cycle.Feasible H 0) :
    0<quarterProjection (SignedPoint.flat ((I.cycle.point H).y-1))
      (I.cycle.point A) (I.cycle.theta A-I.cycle.theta H) 0-
        edgeWidth (I.cycle.theta A-I.cycle.theta H) := by
  obtain ⟨P,hP_def⟩ : ∃ P, P=(I.cycle.point A).a-1/2 := ⟨_,rfl⟩
  obtain ⟨Y,hY_def⟩ : ∃ Y, Y=(I.cycle.point A).y+1/2 := ⟨_,rfl⟩
  obtain ⟨Θ,hΘ_def⟩ : ∃ Θ, Θ=I.cycle.theta H-I.cycle.theta A := ⟨_,rfl⟩
  obtain ⟨e,he_def⟩ : ∃ e, e=I.cycle.theta G-I.cycle.theta H := ⟨_,rfl⟩
  obtain ⟨z,hz_def⟩ : ∃ z, z=I.cycle.theta G-I.cycle.theta A := ⟨_,rfl⟩
  have harg : Θ+e=z := by rw [hΘ_def,he_def,hz_def]; ring
  have he0 : 0<e := by rw [he_def]; exact sub_pos.mpr hHGorder
  have hΘ0 : 0≤Θ := by rw [hΘ_def]; exact sub_nonneg.mpr hAH
  have hz : z∈Icc 0 frameCap :=
    ⟨by linarith only [harg,he0,hΘ0],
      by rw [hz_def]; exact (le_abs_self _).trans (I.necessary.spread G A)⟩
  have hΘ : Θ∈Icc 0 frameCap :=
    ⟨hΘ0,by rw [hΘ_def]; exact (le_abs_self _).trans (I.necessary.spread H A)⟩
  have he : e∈Icc 0 frameCap :=
    ⟨he0.le,by rw [he_def]; exact (le_abs_self _).trans (I.necessary.spread G H)⟩
  have hAa := SignedPoint.primary_gt_half (I.necessary.sorted A) (I.necessary.core A)
  have hAy0 := I.anchors_normal.A_nonneg
  have hAq : (P+1)^2+Y^2≤q := by
    have h : (I.cycle.point A).circle≤q := I.necessary.contained A
    simp only [SignedPoint.circle,abs_of_nonneg hAy0] at h
    rw [hP_def,hY_def]
    linarith only [h]
  have hGA : -(I.cycle.point G).y+1/2≤PositiveSmallScalar.V P Y z := by
    have hf : edgeWidth (I.cycle.theta A-I.cycle.theta G)≤
        quarterProjection (I.cycle.point G) (I.cycle.point A)
          (I.cycle.theta A-I.cycle.theta G) 0 := by
      simpa [Feasible,slack,edge,word,delta,next,G,A,sub_nonneg] using I.GA_hard
    have hd : I.cycle.theta A-I.cycle.theta G= -z := by rw [hz_def]; ring
    rw [hd,edgeWidth_negative_formula hz] at hf
    simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg] at hf
    simp only [PositiveSmallScalar.V]
    rw [hP_def,hY_def]
    linarith only [hf]
  have hV : 1/2≤PositiveSmallScalar.V P Y z := by linarith only [hGA,hGy]
  have hPupper : P≤397/500 := by
    have hAq' := hAq.trans hq
    have hY : 167/200≤Y := by rw [hY_def]; linarith only [hsmall.1]
    have hY2 := pow_le_pow_left₀ (show (0:ℝ)≤167/200 by norm_num) hY 2
    simp only [qCap] at hAq'
    by_contra! hlt
    have h2 := pow_lt_pow_left₀ (show (397/500:ℝ)+1<P+1 by linarith only [hlt])
      (by norm_num) (by decide : (2:ℕ)≠0)
    linarith only [h2,hY2,hAq']
  have hPlower : 1/2≤P := by
    have hVp := PositiveCancelingOuter.V_upper hAa hAy0 hz
    have hV' := hV
    simp only [PositiveCancelingOuter.V] at hVp
    simp only [PositiveSmallScalar.V] at hV'
    rw [hP_def,hY_def] at hV'
    linarith only [hV',hVp,hP_def]
  have S : PositiveSmallScalar.CapData q P Y := {
    P_mem := ⟨hPlower,hPupper⟩
    Y_mem := by rw [hY_def]; constructor <;> linarith only [hsmall.1,hsmall.2]
    circle := hAq
    ceiling := hq }
  obtain ⟨J,hJ_def⟩ : ∃ J, J=(I.cycle.point H).y-1/2+PositiveSmallScalar.V P Y Θ := ⟨_,rfl⟩
  have hpair : 1≤J+PositiveSmallScalar.F q P Y Θ e := by
    have hyR : 0≤PositiveSmallScalar.V P Y z-1/2 := by linarith only [hV]
    have hbound : |PositiveSmallScalar.V P Y z-1/2|≤diagonalCoordinate q := by
      rw [abs_of_nonneg hyR]
      have hVP := PositiveSmallScalar.V_upper S hz
      linarith only [(uniform_circle_reserves hqL hq).1,hVP,hPupper]
    obtain ⟨hRs,hRo,hRc⟩ := SignedPoint.outerAt_spec hqL hbound
    obtain ⟨R,hR⟩ : ∃ R, R=SignedPoint.outerAt q (PositiveSmallScalar.V P Y z-1/2) := ⟨_,rfl⟩
    rw [← hR] at hRs hRo hRc
    have hRy : R.y=PositiveSmallScalar.V P Y z-1/2 := by rw [hR]; rfl
    have hsupport := PositiveCancelingOuter.sorted_support_mono
      (H := (I.cycle.point G).reflect) (J := R)
      (by simpa using I.necessary.sorted G) hRs
      (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
      (show 0≤R.y by rw [hRy]; exact hyR)
      (show (I.cycle.point G).reflect.circle≤R.circle by
        rw [SignedPoint.reflect_circle]
        exact (I.necessary.contained G).trans_eq hRo.symm)
      (show (I.cycle.point G).reflect.y≤R.y by
        rw [hRy]
        simp only [SignedPoint.reflect]
        linarith only [hGA]) he
    have hRa : R.a=PositiveSmallScalar.W q P Y z-1/2 := by
      rw [hR]
      simp only [SignedPoint.outerAt,PositiveSmallScalar.W]
      rw [abs_of_nonneg hyR]
      ring_nf
    have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G) e 0 := by
      rw [he_def]
      simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
    rw [zeroFeasible,edgeWidth_positive_formula he] at hHG'
    simp only [zeroProjection,Matrix.cons_val_zero] at hHG'
    have hinv := PositiveSmallScalar.inverse_identity P Y Θ e
    rw [harg] at hinv
    simp only [SignedPoint.reflect] at hsupport
    rw [hRa,hRy] at hsupport
    rw [hJ_def]
    simp only [PositiveSmallScalar.F,PositiveSmallScalar.T]
    rw [harg]
    linarith only [hHG',hsupport,hinv]
  obtain ⟨Z,hzZ,hZu,hZE,hVinterval⟩ := PositiveSmallScalar.contact_endpoint S hz hV
  obtain ⟨M,hM_def⟩ : ∃ M, M=Z-Θ := ⟨_,rfl⟩
  have hM : 0<M := by rw [hM_def]; linarith only [hzZ,harg,he0]
  have heM : e≤M := by rw [hM_def]; linarith only [hzZ,harg]
  have hMbound : M<2/5 := by rw [hM_def]; linarith only [hZu,hΘ0]
  have hargM : Θ+M=Z := by rw [hM_def]; ring
  have hdom (s : ℝ) (hs : s∈Icc 0 M) :
      Θ+s∈Icc 0 frameCap ∧ 1/2≤PositiveSmallScalar.V P Y (Θ+s) := by
    have hx : Θ+s∈Icc 0 Z := ⟨by linarith only [hs.1,hΘ0],by linarith only [hs.2,hargM]⟩
    exact ⟨⟨hx.1,by simp only [frameCap]; linarith only [hx.2,hZu]⟩,hVinterval _ hx⟩
  have hnoend : ¬1≤J+PositiveSmallScalar.F q P Y Θ M := by
    intro hf
    have hQbound : |(0:ℝ)|≤diagonalCoordinate q := by
      rw [abs_zero]
      linarith only [(uniform_circle_reserves hqL hq).1]
    obtain ⟨hQs,hQo,hQc⟩ := SignedPoint.outerAt_spec hqL hQbound
    obtain ⟨Q,hQ⟩ : ∃ Q, Q=SignedPoint.outerAt q 0 := ⟨_,rfl⟩
    rw [← hQ] at hQs hQo hQc
    have hQy : Q.y=0 := by rw [hQ]; rfl
    have hQa : Q.a=Real.sqrt (q-1/4)-1/2 := by
      rw [hQ]
      simp only [SignedPoint.outerAt,abs_zero,zero_add]
      norm_num
    have hMi : M∈Icc 0 frameCap := by
      simp only [frameCap]; exact ⟨hM.le,by linarith only [hMbound]⟩
    have hZi : Z∈Icc 0 frameCap := by
      simp only [frameCap]; exact ⟨by linarith only [hz.1,hzZ],by linarith only [hZu]⟩
    have hWZ : PositiveSmallScalar.W q P Y Z=Real.sqrt (q-1/4) := by
      simp only [PositiveSmallScalar.W,hZE]
      norm_num
    have hHGQ : zeroFeasible (I.cycle.point H) Q M 0 := by
      have hinv := PositiveSmallScalar.inverse_identity P Y Θ M
      rw [hargM,hZE] at hinv
      rw [hJ_def] at hf
      simp only [PositiveSmallScalar.F,PositiveSmallScalar.T] at hf
      rw [hargM,hWZ] at hf
      rw [zeroFeasible,edgeWidth_positive_formula hMi]
      simp only [zeroProjection,Matrix.cons_val_zero,hQy,zero_mul,sub_zero,hQa]
      linarith only [hf,hinv]
    have hGAQ : quarterFeasible Q (I.cycle.point A) (-Z) 0 := by
      rw [quarterFeasible,edgeWidth_negative_formula hZi]
      simp only [quarterProjection,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg,hQy]
      simp only [PositiveSmallScalar.V] at hZE
      rw [hP_def,hY_def] at hZE
      linarith only [hZE]
    apply I.small_positive_G_zero_impossible (θ := I.cycle.theta A+Z) hq hAB hnorm hsmall
      hTA hAH hTy (I.cycle.point A) Q (I.necessary.sorted A) (I.necessary.core A)
      (I.necessary.contained A) rfl hQo.le hQy
      (by linarith only [hΘ_def,hM,hargM])
      (by linarith only [hZi.2])
    · rw [show I.cycle.theta A+Z-I.cycle.theta H=M by linarith only [hΘ_def,hargM]]
      exact hHGQ
    · rw [show I.cycle.theta A-(I.cycle.theta A+Z)= -Z by ring]
      exact hGAQ
  have heMstrict : e<M := by
    apply lt_of_le_of_ne heM
    intro heq
    exact hnoend (by rw [← heq]; exact hpair)
  have hstrict := strict_endpoint_of_second_derivative
    (f := fun s => -PositiveSmallScalar.F q P Y Θ s)
    (df := fun s => -PositiveSmallScalar.F1 q P Y Θ s)
    (ddf := fun s => -PositiveSmallScalar.F2 q P Y Θ s)
    (by norm_num : (0:ℝ)<3/50) (show e∈Ioo 0 M from ⟨he0,heMstrict⟩)
    (fun s hs => (PositiveSmallScalar.F_hasDerivAt
      (PositiveSmallScalar.point_bounds S (hdom s hs).1 (hdom s hs).2).radicand_pos).fun_neg)
    (fun s hs => (PositiveSmallScalar.F1_hasDerivAt
      (PositiveSmallScalar.point_bounds S (hdom s hs).1 (hdom s hs).2).radicand_pos).fun_neg)
    (fun s hs => by
      have hc := PositiveSmallScalar.curvature_lower S
        (show s∈Icc 0 (2/5 : ℝ) from ⟨hs.1,by linarith only [hs.2,hMbound]⟩)
        (hdom s hs).1 (hdom s hs).2
      linarith only [hc])
  have hJ : 1<J := by
    rcases hstrict with hleft | hright
    · have hzero : PositiveSmallScalar.F q P Y Θ 0=0 := by simp [PositiveSmallScalar.F]
      simp only [hzero] at hleft
      linarith only [hleft,hpair]
    · exact False.elim (hnoend (by linarith only [hright,hpair]))
  have hnegative : I.cycle.theta A-I.cycle.theta H= -Θ := by rw [hΘ_def]; ring
  rw [hnegative,edgeWidth_negative_formula hΘ]
  simp only [quarterProjection,SignedPoint.flat,Matrix.cons_val_zero,Real.cos_neg,Real.sin_neg]
  rw [hJ_def] at hJ
  simp only [PositiveSmallScalar.V] at hJ
  rw [hP_def,hY_def] at hJ
  linarith only [hJ]

/-- The local alignment output uses no sign assertion on E.  Its budget
has already been proved on the actual source and can therefore be
transported by exact reflection. -/
theorem HardOuterGeometry.positive_HG0_small_output {q : ℝ} (I : HardOuterGeometry q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y)
    (hHG : I.cycle.Feasible H 0) :
    ∃ t, t<I.cycle.theta H-I.cycle.theta A ∧
      Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
        (I.cycle.theta H-I.cycle.theta A) t) := by
  let Θ := I.cycle.theta H-I.cycle.theta A
  let r := quarterProjection (SignedPoint.flat ((I.cycle.point H).y-1))
    (I.cycle.point A) (-Θ) 0-edgeWidth (-Θ)
  have hr : 0<r := by
    simpa [r,Θ,neg_sub] using I.positive_HG0_small_reserve hqL hq hAB hnorm
      hsmall hTA hAH hHGorder hGy hTy hHG
  let δ := min (1/2 : ℝ) r
  have hδ : 0<δ := lt_min (by norm_num) hr
  have hδu : δ≤1/2 := min_le_left _ _
  have hδr : δ≤r := min_le_right _ _
  have hΘ : Θ∈Icc 0 (7/10 : ℝ) :=
    ⟨sub_nonneg.mpr hAH,(le_abs_self Θ).trans (I.necessary.spread H A)⟩
  obtain ⟨O⟩ := alignment_of_reserve (t := Θ-δ) hqL hq
    (I.necessary.sorted H) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A)
    (I.necessary.contained H) (I.necessary.contained A)
    I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg hΘ
    (by constructor <;> linarith) (by change (3/20)*(Θ-(Θ-δ))≤r; linarith)
  exact ⟨Θ-δ,by linarith,⟨O⟩⟩

/-- The original source has the strict reserve before any anchor changes. -/
theorem HardInput.positive_HG0_small_reserve {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : (I.cycle.point A).y∈Icc (67/200 : ℝ) (1/2))
    (hTA : I.cycle.theta T≤I.cycle.theta A)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hHGorder : I.cycle.theta H<I.cycle.theta G)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y)
    (hHG : I.cycle.Feasible H 0) :
    0<quarterProjection (SignedPoint.flat ((I.cycle.point H).y-1))
      (I.cycle.point A) (I.cycle.theta A-I.cycle.theta H) 0-
        edgeWidth (I.cycle.theta A-I.cycle.theta H) :=
  I.outerGeometry.positive_HG0_small_reserve hqL hq hAB hnorm hsmall hTA hAH
    hHGorder hGy hTy hHG

end SignedCycle
end SquaresInCircles.Eight
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

theorem HardInput.positive_TD2_small_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hsmall : -(I.cycle.point B).y∈Icc (67/200 : ℝ) (1/2))
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDorder : I.cycle.theta T<I.cycle.theta D)
    (hGy : (I.cycle.point G).y≤0) (hTy : 0≤(I.cycle.point T).y)
    (hTD : I.cycle.Feasible T 2) :
    ∃ t, t<I.cycle.theta B-I.cycle.theta D ∧
      Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
        (I.cycle.theta B-I.cycle.theta D) t) := by
  let J := I.outerGeometry.reflected
  have hJAB : J.cycle.theta A=J.cycle.theta B := by
    change I.cycle.theta B-I.cycle.theta B=I.cycle.theta B-I.cycle.theta A
    linarith
  have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
    linarith
  have hJsmall : (J.cycle.point A).y∈Icc (67/200 : ℝ) (1/2) := hsmall
  have hJTA : J.cycle.theta T≤J.cycle.theta A := by
    change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta B
    linarith
  have hJAH : J.cycle.theta A≤J.cycle.theta H := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta D
    linarith
  have hJHGorder : J.cycle.theta H<J.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta D<I.cycle.theta B-I.cycle.theta T
    linarith
  have hJGy : (J.cycle.point G).y≤0 := by
    change -(I.cycle.point T).y≤0
    linarith
  have hJTy : 0≤(J.cycle.point T).y := by
    change 0≤ -(I.cycle.point G).y
    linarith
  have hJHG : J.cycle.Feasible H 0 := by
    have hh := (reflected_feasible I.cycle H 2).2
      (by simpa [reflectedIndex,next,H,T] using hTD)
    simpa [J,HardOuterGeometry.reflected,HardInput.outerGeometry,reflectedOwner] using hh
  obtain ⟨t,ht,⟨O⟩⟩ := J.positive_HG0_small_output hqL hq hJAB hJnorm hJsmall
    hJTA hJAH hJHGorder hJGy hJTy hJHG
  change t<(I.cycle.theta B-I.cycle.theta D)-
    (I.cycle.theta B-I.cycle.theta B) at ht
  change GAlignment q (I.cycle.point D).reflect (I.cycle.point B).reflect
    ((I.cycle.theta B-I.cycle.theta D)-(I.cycle.theta B-I.cycle.theta B)) t at O
  have O' : GAlignment q (I.cycle.point D).reflect (I.cycle.point B).reflect
      (I.cycle.theta B-I.cycle.theta D) t := by
    simpa only [sub_self,sub_zero] using O
  exact ⟨t,by simpa only [sub_self,sub_zero] using ht,
    ⟨NegativeNoncancelingOuter.reflect_alignment O'⟩⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end
