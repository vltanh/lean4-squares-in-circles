module

public import SquaresInCircles.Eight.TableFree.NegativeNoncancelingBarrier

/-!
# Actual negative HG0 and TD2 transports on the small middle tangent

Uncompiled draft.  The original negative HG0 inequality first forces G's
normal sign.  GA0 then places that same G in the flat part of the true
core.  The actual core supplies the primary threshold used by the
continuous barrier.  A fixed part of its reserve is spent on the
original A circle; reflection is confined to B,T,D on the other side.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeNoncancelingOuter
open PositiveCancelingOuter NegativeNoncancelingBarrier HardCancelingOuter

/-- No G-sign assumption is needed: the actual HG0 axis forces it before
the true-core lower bound on the original G primary is used. -/
theorem original_composite {q Θ t : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap) (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (hHc : H.Contained q) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hAy : 0≤A.y)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hHG : zeroFeasible H G (t-Θ) 0)
    (hGA : quarterFeasible G A (-t) 0) :
    G.y<0 ∧ (7/12 : ℝ)≤G.a ∧ 0≤NegativeNoncancelingBarrier.F H A Θ t := by
  have he : Θ-t∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [ht.2],by linarith [ht.1,hΘ.2]⟩
  have ht' : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,ht.2.trans hΘ.2⟩
  have hte := transport_trig he
  have htt := transport_trig ht'
  have hHu := (H.coordinate_bounds hHs hHcore hHc hq).2.2
  rw [abs_of_nonneg hHy] at hHu
  have hAu := (A.coordinate_bounds hAs hAcore hAc hq).2.1
  have hHG' : edgeWidth (Θ-t)≤H.y-G.a*Real.sin (Θ-t)-G.y*Real.cos (Θ-t) := by
    simpa [zeroFeasible,zeroProjection,show t-Θ= -(Θ-t) by ring,
      Real.sin_neg,Real.cos_neg] using hHG
  have hGA' : edgeWidth t≤G.y+A.a*Real.cos t-A.y*Real.sin t := by
    simpa [quarterFeasible,quarterProjection,Real.sin_neg,Real.cos_neg] using hGA
  have hGn : G.y<0 := by
    by_contra! hbad
    have hfirst := mul_nonneg hGs.1.le hte.2.2.1
    have hsecond := mul_nonneg hbad (show 0≤Real.cos (Θ-t) by linarith [hte.1])
    linarith [edgeWidth_ge_one (Θ-t)]
  have hGsmall : |G.y|<83/200 := by
    rw [abs_of_neg hGn]
    have hac := mul_le_mul_of_nonneg_left htt.2.1 hAs.1.le
    have hys := mul_nonneg hAy htt.2.2.1
    linarith [edgeWidth_ge_one t]
  have hGa : (7/12 : ℝ)≤G.a := by
    have hhalf := SignedPoint.primary_gt_half hGs hGcore
    have hh := hGcore
    rw [SignedPoint.AvoidsCore,SignedPoint.coreDistance,
      max_eq_left (by linarith : 0≤G.a-1/2),
      max_eq_right (by linarith : |G.y|-1/2≤0)] at hh
    nlinarith
  have hcap : -G.y+1/2≤V A t := by
    rw [edgeWidth_positive_formula ht'] at hGA'
    dsimp [V]
    linarith
  have hcapmul := mul_le_mul_of_nonneg_right hcap
    (show 0≤Real.cos (Θ-t) by linarith [hte.1])
  have hcoremul := mul_le_mul_of_nonneg_right hGa hte.2.2.1
  rw [edgeWidth_positive_formula he] at hHG'
  refine ⟨hGn,hGa,?_⟩
  dsimp [NegativeNoncancelingBarrier.F]
  linarith

theorem actual_aligned_reserve {q Θ t : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap) (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (hHc : H.Contained q) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hAy : A.y∈Icc (0:ℝ) (1/2))
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hHG : zeroFeasible H G (t-Θ) 0)
    (hGA : quarterFeasible G A (-t) 0) :
    (Θ-t)/150≤quarterProjection (SignedPoint.flat (H.y-1)) A (-Θ) 0-edgeWidth (-Θ) := by
  have hsource := original_composite hq hHs hGs hAs hHcore hGcore hAcore hHc hAc
    hHy hAy.1 hΘ ht hHG hGA
  have hHu := (H.coordinate_bounds hHs hHcore hHc hq).2.2
  rw [abs_of_nonneg hHy] at hHu
  have hAa := SignedPoint.primary_gt_half hAs hAcore
  have hh := feasible_right_reserve
    (f := NegativeNoncancelingBarrier.F H A Θ) (df := Fd A Θ)
    (l := t) (u := Θ) (b := 0) (k := 1/150) ht.2 (by norm_num)
    (fun z _ => F_hasDerivAt H A Θ z)
    (by
      intro z hz hf
      exact (NegativeNoncancelingBarrier.rate_on_feasible hHu hAa hAy (hAc.trans hq)
        ⟨ht.1.trans hz.1,hz.2⟩ hΘ.2 hf).le)
    hsource.2.2 Θ ⟨ht.2,le_rfl⟩
  have hend : (Θ-t)/150≤NegativeNoncancelingBarrier.F H A Θ Θ := by linarith [hh.2]
  rw [edgeWidth_negative_formula hΘ]
  simp [NegativeNoncancelingBarrier.F,V,quarterProjection,SignedPoint.flat,
    Real.sin_neg,Real.cos_neg] at hend ⊢
  linarith

/-- The actual A primary is lowered by (Theta-t)/300.  Its tangent and
frame, and every datum of H, stay fixed. -/
theorem actual_G_alignment {q Θ t : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (hHc : H.Contained q) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hAy : A.y∈Icc (0:ℝ) (1/2))
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hHG : zeroFeasible H G (t-Θ) 0)
    (hGA : quarterFeasible G A (-t) 0) :
    Nonempty (GAlignment q H A Θ (Θ-(2/45)*(Θ-t))) := by
  have hr := actual_aligned_reserve hq hHs hGs hAs hHcore hGcore hAcore hHc hAc
    hHy hAy hΘ ht hHG hGA
  apply alignment_of_reserve hqL hq hHs hAs hHcore hAcore hHc hAc hHy hAy.1 hΘ
  · constructor <;> linarith [ht.1,ht.2,hΘ.2]
  · nlinarith

/-- This record conversion reflects only the local three-point path.
It does not alter the actual E point or its signed tangent. -/
def reflect_alignment {q Θ t : ℝ} {B D : SignedPoint}
    (O : GAlignment q D.reflect B.reflect Θ t) : TAlignment q B D Θ t where
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
  TD_zero := by
    simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG 0 2).2 O.HG_two
  TD_two := by
    simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG 0 0).2 O.HG_zero
  BT_hard := by
    simpa [reflectedOwner] using
      (quarterFeasible_reflect O.pointG O.pointA (-Θ) 0).2 O.GA_hard
  BT_reserve := by
    have hid := quarterProjection_reflect O.pointG O.pointA (-Θ) 0
    have hh := O.GA_reserve
    rw [←hid] at hh
    simpa [reflectedOwner] using hh

theorem actual_T_alignment {q Θ t : ℝ} {B T D : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBcore : B.AvoidsCore) (hTcore : T.AvoidsCore) (hDcore : D.AvoidsCore)
    (hBc : B.Contained q) (hDc : D.Contained q)
    (hBy : -B.y∈Icc (0:ℝ) (1/2)) (hDy : D.y≤0)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hBT : quarterFeasible B T (-t) 2)
    (hTD : zeroFeasible T D (t-Θ) 2) :
    Nonempty (TAlignment q B D Θ (Θ-(2/45)*(Θ-t))) := by
  have hHG : zeroFeasible D.reflect T.reflect (t-Θ) 0 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect T D (t-Θ) 2).2 hTD
  have hGA : quarterFeasible T.reflect B.reflect (-t) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T (-t) 2).2 hBT
  obtain ⟨O⟩ := actual_G_alignment hqL hq
    (by simpa using hDs) (by simpa using hTs) (by simpa using hBs)
    (by simpa using hDcore) (by simpa using hTcore) (by simpa using hBcore)
    (by simpa using hDc) (by simpa using hBc)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa [SignedPoint.reflect] using hBy) hΘ ht hHG hGA
  exact ⟨reflect_alignment O⟩

end SquaresInCircles.Eight.TableFree.NegativeNoncancelingOuter
