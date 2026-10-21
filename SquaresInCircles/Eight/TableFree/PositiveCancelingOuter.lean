module

public import SquaresInCircles.Eight.TableFree.HardCancelingOuter

/-!
# The positive canceling outer error at a middle tangent at least one fifth

Uncompiled source draft.  The actual HG2/GA0 pair is supported on the
original H circle.  Sorting makes the circle support increase with H's
minor coordinate before the diagonal.  An exact two-case square
comparison then proves a linear aligned contact reserve.  This is the
whole-domain argument of the signed three-zero note, Section 6.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace PositiveCancelingOuter

def V (A : SignedPoint) (Θ : ℝ) : ℝ :=
  (A.a-1/2)*Real.cos Θ-(A.y+1/2)*Real.sin Θ

def U (A : SignedPoint) (Θ : ℝ) : ℝ :=
  (A.a-1/2)*Real.sin Θ+(A.y+1/2)*Real.cos Θ

def F (H A : SignedPoint) (Θ : ℝ) : ℝ := H.y-1/2+V A Θ
def K (H A : SignedPoint) (Θ : ℝ) : ℝ := H.a-1/2-U A Θ

/-- On the sorted quarter of a circle, increasing the minor coordinate
increases the sum of the two center coordinates.  This also covers an
original point inside the comparison circle. -/
theorem sorted_sum_mono {H J : SignedPoint}
    (hHs : H.Sorted) (hJs : J.Sorted) (hHy : 0≤H.y) (hJy : 0≤J.y)
    (hc : H.circle≤J.circle) (hy : H.y≤J.y) : H.a+H.y≤J.a+J.y := by
  have hHsort : H.y≤H.a := by simpa [abs_of_nonneg hHy] using hHs.2
  have hJsort : J.y≤J.a := by simpa [abs_of_nonneg hJy] using hJs.2
  by_contra! hbad
  have hd : J.y-H.y<H.a-J.a := by linarith
  have hda : 0≤H.a-J.a := by linarith
  have hco : 0<J.y+H.y+1 := by linarith
  have hp := mul_lt_mul_of_pos_right hd hco
  have hq := mul_le_mul_of_nonneg_left
    (show J.y+H.y+1≤H.a+J.a+1 by linarith) hda
  rw [SignedPoint.circle,SignedPoint.circle,abs_of_nonneg hHy,abs_of_nonneg hJy] at hc
  nlinarith

theorem sorted_support_mono {H J : SignedPoint} {e : ℝ}
    (hHs : H.Sorted) (hJs : J.Sorted) (hHy : 0≤H.y) (hJy : 0≤J.y)
    (hc : H.circle≤J.circle) (hy : H.y≤J.y)
    (he : e∈Icc 0 (7/10 : ℝ)) :
    H.a*Real.sin e+H.y*Real.cos e≤J.a*Real.sin e+J.y*Real.cos e := by
  obtain ⟨hcos,hcos1,hs0,hs,hsc⟩ := transport_trig he
  have hsum := sorted_sum_mono hHs hJs hHy hJy hc hy
  have hp := mul_le_mul_of_nonneg_right hsum hs0
  have hq := mul_le_mul_of_nonneg_right hy (sub_nonneg.mpr hsc.le)
  nlinarith

theorem V_upper {A : SignedPoint} {Θ : ℝ} (ha : 1/2<A.a) (hy : 0≤A.y)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) : V A Θ≤A.a-1/2 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hΘ
  have hp := mul_le_mul_of_nonneg_left hc1 (by linarith : 0≤A.a-1/2)
  have hq := mul_nonneg (by linarith : 0≤A.y+1/2) hs0
  unfold V
  linarith

theorem U_ge_tangent {A : SignedPoint} {Θ : ℝ}
    (ha : 1/2<A.a) (hy : 0≤A.y) (hΘ : Θ∈Icc 0 (7/10 : ℝ))
    (hV : 0≤V A Θ) : A.y+1/2≤U A Θ := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hΘ
  have hU : 0≤U A Θ := by
    unfold U
    exact add_nonneg (mul_nonneg (by linarith) hs0)
      (mul_nonneg (by linarith) (by linarith))
  have hv := V_upper ha hy hΘ
  have hsquare := pow_le_pow_left₀ hV hv 2
  have hid : (U A Θ)^2+(V A Θ)^2=(A.a-1/2)^2+(A.y+1/2)^2 := by
    unfold U V
    linear_combination (((A.a-1/2)^2+(A.y+1/2)^2)*Real.sin_sq_add_cos_sq Θ)
  nlinarith

theorem sin_nine_tenths {e : ℝ} (he : e∈Ioc 0 (7/10 : ℝ)) :
    (9/10)*e<Real.sin e := by
  have hs := Real.sin_ge_sub_cube he.1.le
  have hsquare := pow_le_pow_left₀ he.1.le he.2 2
  have hcubic := mul_le_mul_of_nonneg_left hsquare he.1.le
  nlinarith

/-- The original signed G coordinate cancels; no boundary assumption or
circle relaxation on G is made. -/
theorem original_pair {H G A : SignedPoint} {Θ e : ℝ}
    (hΘ : 0≤Θ) (he : 0≤e) (hspan : Θ+e≤7/10)
    (hHG : zeroFeasible H G e 2)
    (hGA : quarterFeasible G A (-(Θ+e)) 0) :
    1≤F H A Θ*Real.cos e+K H A Θ*Real.sin e := by
  have hewide : e∈Icc 0 (7/10 : ℝ) := ⟨he,by linarith⟩
  have hwhole : Θ+e∈Icc 0 (7/10 : ℝ) := ⟨by linarith,hspan⟩
  have hh := hHG
  have hg := hGA
  rw [zeroFeasible,edgeWidth_positive_formula hewide] at hh
  rw [quarterFeasible,edgeWidth_negative_formula hwhole] at hg
  simp [zeroProjection,quarterProjection,Real.sin_neg,Real.cos_neg] at hh hg
  have hid : F H A Θ*Real.cos e+K H A Θ*Real.sin e=
      (A.a-1/2)*Real.cos (Θ+e)-(A.y+1/2)*Real.sin (Θ+e)+
        (H.y-1/2)*Real.cos e+(H.a-1/2)*Real.sin e := by
    simp [F,K,V,U,Real.sin_add,Real.cos_add]
    ring
  rw [hid]
  linarith

/-- The strict linear reserve from the actual same-radius pair. -/
theorem positive_reserve {q Θ e : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hHc : H.Contained q) (hHy : 0≤H.y)
    (hAa : 1/2<A.a) (hAc : A.Contained q) (hAy : 1/5≤A.y)
    (hΘ : 0≤Θ) (he : 0<e) (hspan : Θ+e≤7/10)
    (hHG : zeroFeasible H G e 2)
    (hGA : quarterFeasible G A (-(Θ+e)) 0) : 1+e/20<F H A Θ := by
  have hΘwide : Θ∈Icc 0 (7/10 : ℝ) := ⟨hΘ,by linarith⟩
  have hewide : e∈Icc 0 (7/10 : ℝ) := ⟨he.le,by linarith⟩
  have hpair := original_pair hΘ he.le hspan hHG hGA
  have hCupper := (uniform_circle_reserves hqL hq).2.1
  have hCy := SignedPoint.contained_minor_le_diagonal hHs hHc
  rw [abs_of_nonneg hHy] at hCy
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hΘwide
  obtain ⟨hce,hce1,hse0,hse,hsce⟩ := transport_trig hewide
  have hAy0 : 0≤A.y := by linarith
  have hsin := sin_nine_tenths (show e∈Ioc 0 (7/10 : ℝ) from ⟨he,hewide.2⟩)
  by_contra! hF
  let r : ℝ := 3/2-V A Θ+e/20
  let b : ℝ := min r (diagonalCoordinate q)
  have hHr : H.y≤r := by dsimp [F] at hF; dsimp [r]; linarith
  have hHb : H.y≤b := le_min hHr hCy
  have hb0 : 0≤b := hHy.trans hHb
  have hbC : b≤diagonalCoordinate q := min_le_right _ _
  let J := SignedPoint.outerAt q b
  obtain ⟨hJs,hJo,hJcore⟩ := SignedPoint.outerAt_spec hqL
    (show |b|≤diagonalCoordinate q by rw [abs_of_nonneg hb0]; exact hbC)
  have hJy : J.y=b := rfl
  have hJa : 0<J.a := hJs.1
  have hJcircle : (J.a+1/2)^2+(b+1/2)^2=q := by
    simpa [J,SignedPoint.Outer,SignedPoint.circle,SignedPoint.outerAt,abs_of_nonneg hb0]
      using hJo
  have hsupport := sorted_support_mono hHs hJs hHy
    (show 0≤J.y by simpa [hJy] using hb0)
    (show H.circle≤J.circle from hHc.trans_eq hJo.symm)
    (show H.y≤J.y by simpa [hJy] using hHb) hewide
  have hFJ : F J A Θ≤1+e/20 := by
    have hb : b≤r := min_le_left r (diagonalCoordinate q)
    change J.y-1/2+V A Θ≤1+e/20
    rw [hJy]
    dsimp [r] at hb
    linarith
  have hKJ : K J A Θ< -(1/16 : ℝ) := by
    by_cases hr : r≤diagonalCoordinate q
    · have hbr : b=r := min_eq_left hr
      have hV : 3/5<V A Θ := by dsimp [r] at hr; linarith
      have hU := U_ge_tangent hAa hAy0 hΘwide (by linarith : 0≤V A Θ)
      have hv := V_upper hAa hAy0 hΘwide
      have hX : A.a+1/2<1851/1000 := by
        have hh := hAc.trans hq
        rw [SignedPoint.circle,abs_of_nonneg hAy0] at hh
        dsimp [qCap] at hh
        have hY := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/10)
          (show 7/10≤A.y+1/2 by linarith) 2
        nlinarith
      have hb : 1149/1000<b+1/2 := by
        rw [hbr]
        dsimp [r]
        linarith
      have hbSquare := pow_lt_pow_left₀ (by norm_num : (0:ℝ)≤1149/1000) hb
        (by decide : (2:ℕ)≠0)
      have hJsmall : J.a+1/2<131/80 := by
        dsimp [qCap] at hq
        nlinarith
      unfold K
      linarith
    · have hbr : b=diagonalCoordinate q := min_eq_right (lt_of_not_ge hr).le
      have hdiag : J.a=diagonalCoordinate q := by
        have hq0 : 0≤q := by dsimp [qLow] at hqL; linarith
        have hsqrt := Real.sq_sqrt (show 0≤q/2 by positivity)
        have hsqrt0 := Real.sqrt_nonneg (q/2)
        rw [hbr] at hJcircle
        dsimp [diagonalCoordinate] at hJcircle ⊢
        nlinarith
      have hfirst : 0≤(A.a-1/2)*Real.sin Θ := mul_nonneg (by linarith) hs0
      have hsecond : (21/40 : ℝ)<(A.y+1/2)*Real.cos Θ := by
        have hm := mul_lt_mul_of_pos_left (show 3/4<Real.cos Θ by linarith)
          (show 0<A.y+1/2 by linarith)
        nlinarith
      unfold K U
      rw [hdiag]
      linarith
  have hJpair : F H A Θ*Real.cos e+K H A Θ*Real.sin e≤
      F J A Θ*Real.cos e+K J A Θ*Real.sin e := by
    dsimp [F,K]
    nlinarith
  have hfc := mul_le_mul_of_nonneg_right hFJ (by linarith : 0≤Real.cos e)
  have hks := mul_le_mul_of_nonneg_right hKJ.le hse0
  have hcap := mul_le_mul_of_nonneg_left hce1 (show 0≤1+e/20 by linarith)
  nlinarith

theorem positive_aligned_reserve {q Θ e : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hHc : H.Contained q) (hHy : 0≤H.y)
    (hAa : 1/2<A.a) (hAc : A.Contained q) (hAy : 1/5≤A.y)
    (hΘ : 0≤Θ) (he : 0<e) (hspan : Θ+e≤7/10)
    (hHG : zeroFeasible H G e 2)
    (hGA : quarterFeasible G A (-(Θ+e)) 0) :
    e/20<quarterProjection (SignedPoint.flat (H.y-1)) A (-Θ) 0-edgeWidth (-Θ) := by
  have hh := positive_reserve hqL hq hHs hHc hHy hAa hAc hAy hΘ he hspan hHG hGA
  rw [edgeWidth_negative_formula ⟨hΘ,by linarith⟩]
  simp [quarterProjection,SignedPoint.flat,Real.cos_neg,Real.sin_neg,F,V] at hh ⊢
  linarith

/-- Both signs of the original HG error, with one uniform actual loss
parameter.  The third scalar parameter of `GAlignment` is now a reserve
budget; the comparison G frame is still exactly the original H frame. -/
theorem ordered_G_alignment {q Θ t : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hAs : A.Sorted)
    (hHcore : H.AvoidsCore) (hAcore : A.AvoidsCore)
    (hHc : H.Contained q) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hAy : 1/5≤A.y)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 (7/10 : ℝ))
    (hHG : zeroFeasible H G (t-Θ) 2)
    (hGA : quarterFeasible G A (-t) 0) :
    Nonempty (HardCancelingOuter.GAlignment q H A Θ (Θ-|t-Θ|/3)) := by
  have he : |t-Θ|≤7/10 := by rw [abs_le]; constructor <;> linarith [hΘ.1,hΘ.2,ht.1,ht.2]
  have hres : |t-Θ|/20≤
      quarterProjection (SignedPoint.flat (H.y-1)) A (-Θ) 0-edgeWidth (-Θ) := by
    rcases le_or_gt t Θ with hnegative | hpositive
    · have hh := HardCancelingOuter.actual_aligned_reserve hq hHs hAs hAcore hAc hHy
        (by linarith : 0≤A.y) hΘ ⟨ht.1,hnegative⟩ hHG hGA
      rw [abs_of_nonpos (by linarith : t-Θ≤0)]
      linarith
    · have hh := positive_aligned_reserve hqL hq hHs hHc hHy
        (SignedPoint.primary_gt_half hAs hAcore) hAc hAy hΘ.1
        (sub_pos.mpr hpositive) (by linarith [ht.2]) hHG
        (by simpa [show -(Θ+(t-Θ))= -t by ring] using hGA)
      rw [abs_of_pos (sub_pos.mpr hpositive)]
      exact hh.le
  apply HardCancelingOuter.alignment_of_reserve hqL hq hHs hAs hHcore hAcore
    hHc hAc hHy (by linarith) hΘ
  · constructor <;> linarith [abs_nonneg (t-Θ)]
  · nlinarith

/-- Reflection is confined to B,T,D.  The actual E record and its sign
are not involved in this two-sided canceling comparison. -/
theorem ordered_T_alignment {q Θ t : ℝ} {B T D : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hBs : B.Sorted) (hDs : D.Sorted)
    (hBcore : B.AvoidsCore) (hDcore : D.AvoidsCore)
    (hBc : B.Contained q) (hDc : D.Contained q)
    (hBy : B.y≤ -(1/5 : ℝ)) (hDy : D.y≤0)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 (7/10 : ℝ))
    (hBT : quarterFeasible B T (-t) 2)
    (hTD : zeroFeasible T D (t-Θ) 0) :
    Nonempty (HardCancelingOuter.TAlignment q B D Θ (Θ-|t-Θ|/3)) := by
  have hHG : zeroFeasible D.reflect T.reflect (t-Θ) 2 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect T D (t-Θ) 0).2 hTD
  have hGA : quarterFeasible T.reflect B.reflect (-t) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T (-t) 2).2 hBT
  obtain ⟨O⟩ := ordered_G_alignment hqL hq
    (by simpa using hDs) (by simpa using hBs)
    (by simpa using hDcore) (by simpa using hBcore)
    (by simpa using hDc) (by simpa using hBc)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by dsimp [SignedPoint.reflect]; linarith)
    hΘ ht hHG hGA
  refine ⟨{
    pointT := O.pointG.reflect
    pointB := O.pointA.reflect
    T_eq := by rw [O.G_eq]
    B_eq := by rw [O.A_eq]
    T_sorted := by simpa using O.G_sorted
    T_core := by simpa using O.G_core
    T_contained := by simpa using O.G_contained
    T_normal := by dsimp [SignedPoint.reflect]; linarith [O.G_normal]
    B_sorted := by simpa using O.A_sorted
    B_avoids := by simpa using O.A_avoids
    B_primary := O.A_primary
    B_tangent := by
      have hy := O.A_tangent
      change O.pointA.y= -B.y at hy
      change -O.pointA.y=B.y
      linarith
    B_tangent_lower := by dsimp [SignedPoint.reflect]; linarith [O.A_tangent_upper]
    B_circle := by simpa using O.A_circle
    B_strict := fun h => by simpa using O.A_strict h
    TD_zero := ?_
    TD_two := ?_
    BT_hard := ?_
    BT_reserve := ?_ }⟩
  · simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG 0 2).2 O.HG_two
  · simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG 0 0).2 O.HG_zero
  · simpa [reflectedOwner] using
      (quarterFeasible_reflect O.pointG O.pointA (-Θ) 0).2 O.GA_hard
  · have hid := quarterProjection_reflect O.pointG O.pointA (-Θ) 0
    have hh := O.GA_reserve
    rw [←hid] at hh
    simpa [reflectedOwner] using hh

end PositiveCancelingOuter
end SquaresInCircles.Eight.TableFree
