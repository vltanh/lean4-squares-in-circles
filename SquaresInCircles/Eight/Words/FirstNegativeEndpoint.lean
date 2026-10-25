module

public import SquaresInCircles.Eight.Words.FirstNegativeSlack

/-!
# Eight squares: paid first-contact endpoints with the retained high-H bounds

The endpoint (`Source.first_mixed_endpoint`) is the rightmost hard-axis contact, followed by a
contraction paid by its strict mixed margin. Its H tangent stays greater than `.844` and its H
primary below 1. The negative-T transport at the original E uses these bounds, also when both
primary axes start with a negative error.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace AlignedNegative
open PrimaryCap

structure FirstMixedEndpoint {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (E : SignedPoint) (e : ℝ) (j : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  Hpoint : SignedPoint
  Gpoint : SignedPoint
  H_sorted : Hpoint.Sorted
  G_sorted : Gpoint.Sorted
  H_core : Hpoint.AvoidsCore
  G_core : Gpoint.Core
  H_circle_loss : Hpoint.circle<H.circle
  G_inside : Gpoint.circle<q
  H_high : 211/250<Hpoint.y
  H_primary_lt_one : Hpoint.a<1
  G_negative : Gpoint.y<0
  H_nondiagonal : |Hpoint.y|<Hpoint.a
  G_nondiagonal : |Gpoint.y|<Gpoint.a
  G_primary : Gpoint.a=7/12
  H_tangent_decreases : Hpoint.y<H.y
  HG0 : zeroFeasible Hpoint Gpoint 0 0
  HG2 : zeroFeasible Hpoint Gpoint 0 2
  GA0 : quarterFeasible Gpoint A (-angle) 0
  EH : quarterFeasible E Hpoint (e+angle) j
  EH_error : e+angle∈Icc 0 (7/10 : ℝ)
  EH_short : j=1 → e+angle≤11/50

theorem Source.first_mixed_endpoint {q t e : ℝ} {H G A E : SignedPoint}
    (I : Source q t H G A) {j : Fin 4} (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEy : E.y≤0)
    (hj : j=0 ∨ j=1) (he : |e+t|≤7/10)
    (hshort : j=1 → |e+t|≤11/50)
    (hf : quarterFeasible E H (e+t) j) :
    Nonempty (FirstMixedEndpoint I E e j) := by
  obtain ⟨O⟩ := I.first_hard hq
  let x := O.angle
  let P := A.a-1/2
  let H₀ := movingAnchor H.circle P x
  let G₀ := point P x
  let margin := quarterProjection E H₀ (e+x) j-edgeWidth (e+x)
  have hcontact : e+x∈Icc 0 (7/10 : ℝ) ∧ 0<margin ∧
      (j=1 → e+x≤11/50) := by
    rcases hj with hj | hj
    · subst j
      have hh := O.low_mixed_slack hq hEy he hf
      refine ⟨hh.1,?_,by norm_num⟩
      dsimp [margin,H₀,P,x]
      rw [← lowMixedSlack_actual E hh.1]
      exact hh.2
    · subst j
      have hh := O.high_mixed_slack hq hEs hEc hEy (hshort rfl) hf
      have hwide : e+O.angle∈Icc 0 (7/10 : ℝ) :=
        ⟨hh.1.1,by linarith [hh.1.2]⟩
      refine ⟨hwide,?_,fun _ => hh.1.2⟩
      dsimp [margin,H₀,P,x]
      rw [← highMixedSlack_actual E hwide]
      exact hh.2
  obtain ⟨hHs,hHcircle,hHprimary,hHtangent,hHcore,hHy,hHrad⟩ :=
    I.path_geometry hq ⟨O.angle_mem.1,O.angle_mem.2.le⟩
  have hHtangentStrict := I.path_tangent_strict hq O.angle_mem
  have hHsort : H₀.y<H₀.a := by
    have hh := I.H_sorted.2
    rw [abs_of_nonneg I.H_nonneg] at hh
    exact hHtangentStrict.trans_le (hh.trans hHprimary)
  have hHhigh : 211/250<H₀.y := (O.high_anchor hq).2.1
  have hHupper : H₀.a<1 := (O.high_anchor hq).2.2
  let η := min ((H₀.a-H₀.y)/2) (min ((H₀.a-7/12)/2) (margin/2))
  have hη : 0<η := by
    apply lt_min
    · exact div_pos (sub_pos.mpr hHsort) (by norm_num)
    · apply lt_min
      · apply div_pos _ (by norm_num)
        linarith
      · exact div_pos hcontact.2.1 (by norm_num)
  have hηsort : η≤(H₀.a-H₀.y)/2 := min_le_left _ _
  have hηcore : η≤(H₀.a-7/12)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηslack : η≤margin/2 := (min_le_right _ _).trans (min_le_right _ _)
  let H' : SignedPoint := ⟨H₀.a-η,H₀.y⟩
  have hHs' : H'.Sorted := by
    constructor
    · dsimp [H']; linarith
    · dsimp [H']; rw [abs_of_pos hHy]; linarith
  have hHcore' : H'.AvoidsCore := by
    have ha : 7/12≤H'.a := by dsimp [H']; linarith
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith : 0≤H'.a-1/2)]
    have h1 : (1/12:ℝ)≤H'.a-1/2 := by linarith
    have h2 := pow_le_pow_left₀ (by norm_num) h1 2
    linarith [sq_nonneg (max (|H'.y|-1/2) 0)]
  have hHloss : H'.circle<H.circle := by
    have hp : 0<η*(2*(H₀.a+1/2)-η) := by
      apply mul_pos hη
      linarith
    have heq : H₀.circle=H.circle := hHcircle
    rw [← heq]
    dsimp [H',SignedPoint.circle]
    linarith
  obtain ⟨hPlo,hPup,hcap,hDle⟩ := I.cap_data hq
  have hD := I.path_cap hq ⟨O.angle_mem.1,O.angle_mem.2.le⟩
  obtain ⟨hGs,hGcore,hGavoid,hGinside⟩ := point_geometric
    ⟨hPlo,hPup⟩ ⟨O.angle_mem.1,O.angle_mem.2.le.trans I.tilt_cap⟩
    (by linarith [hD.1]) (I.cuts hq).2.2.2.2.2.2.2
  have hGnegative : G₀.y<0 := by dsimp [G₀,point,P,x]; linarith [hD.1]
  have hHnondiagonal : |H'.y|<H'.a := by
    dsimp [H']; rw [abs_of_pos hHy]; linarith
  have hGnondiagonal : |G₀.y|<G₀.a := by
    rw [abs_of_neg hGnegative]
    dsimp [G₀,point,P,x]
    linarith [hD.2.1]
  have hHG0 : zeroFeasible H' G₀ 0 0 := by
    simp [zeroFeasible,zeroProjection,H',H₀,G₀,movingAnchor,anchorAt,point]
    ring_nf
    norm_num
  have hEH : quarterFeasible E H' (e+x) j := by
    have hm : margin=quarterProjection E H₀ (e+x) j-edgeWidth (e+x) := rfl
    rcases hj with hj | hj
    · subst j
      have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (e+x)) hη.le
      change edgeWidth (e+x)≤quarterProjection E H' (e+x) 0
      simp only [quarterProjection,Matrix.cons_val_zero,H'] at hm ⊢
      linarith [hcontact.2.1]
    · subst j
      change edgeWidth (e+x)≤quarterProjection E H' (e+x) 1
      simp only [quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero,H'] at hm ⊢
      linarith [hcontact.2.1]
  exact ⟨{
    angle := x
    angle_mem := O.angle_mem
    Hpoint := H'
    Gpoint := G₀
    H_sorted := hHs'
    G_sorted := hGs
    H_core := hHcore'
    G_core := hGcore
    H_circle_loss := hHloss
    G_inside := hGinside
    H_high := hHhigh
    H_primary_lt_one := by dsimp [H']; linarith
    G_negative := hGnegative
    H_nondiagonal := hHnondiagonal
    G_nondiagonal := hGnondiagonal
    G_primary := rfl
    H_tangent_decreases := hHtangentStrict
    HG0 := hHG0
    HG2 := (zero_owner_tie _ _).1 hHG0
    GA0 := O.hard
    EH := hEH
    EH_error := hcontact.1
    EH_short := hcontact.2.2 }⟩

namespace FirstMixedEndpoint

variable {q t e : ℝ} {H G A E : SignedPoint} {I : Source q t H G A}

end FirstMixedEndpoint
end AlignedNegative
end SquaresInCircles.Eight
