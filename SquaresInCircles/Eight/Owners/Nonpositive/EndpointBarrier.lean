module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.E.ZeroCapEndpoints
public import SquaresInCircles.Eight.Owners.Nonpositive.OuterReduction
public import SquaresInCircles.Eight.Owners.Nonpositive.EZeroCycle

/-!
# Eight squares: the large-A endpoint barrier for negative composites

The circles of A and H and their negative core composite put the primary of H below one when the
tangent of A is at least `1/2` (`large_middle_primary_lt_one`,
`HardInput.nonpositive_large_A_primary_lt_one`). The EH1 contact at zero angle then excludes
`E = H` (`HardInput.nonpositive_large_A_EH_impossible`). With the deletion at zero E, the minimizer
of E reaches DE alignment, every other point and loss unchanged
(`HardInput.reduce_nonpositive_large_A_DE`).
-/

section
/-!
## Minimizing E before the negative outer errors are aligned

The HG0 and TD2 composites give the shared span `27/100` and the bounds on the primary sum of H and
D. The contact curve of E then gives a boundary descendant
(`HardInput.fromNonpositiveEInterior`, `HardInput.reduce_nonpositive_E`) which keeps every other
point, frame, witness and separate circle loss. An interior original E lies strictly outside the
circle of its descendant, whatever its radial slack.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate EInteriorGeometry
namespace SignedCycle

def HardInput.fromNonpositiveEInterior {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hb : NonpositiveChainBounds.Bounds I.cycle) {P : State}
    (hp : EInteriorGeometry.Feasible (I.cycle.point H).a (I.cycle.point D).a
      (I.cycle.theta H-I.cycle.theta D) q P) : HardInput q where
  cycle := eInteriorCycle I.cycle P
  necessary := {
    sorted := by
      intro i
      by_cases hi : i=E
      · subst i
        have ha := primary_lower_wide hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        have hs := strict_sorting_wide hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        exact ⟨by simpa [eInteriorCycle,E] using (show 0<P.1 by linarith),
          by simpa [eInteriorCycle,E,abs_neg,abs_of_nonneg hp.b_nonneg] using hs.le⟩
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.sorted i
    contained := by
      intro i
      by_cases hi : i=E
      · subst i
        change ((eInteriorCycle I.cycle P).point E).circle≤q
        rw [eInteriorCycle_circle hp.b_nonneg]
        exact hp.circle
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.contained i
    core := by
      intro i
      by_cases hi : i=E
      · subst i
        have ha := primary_lower_wide hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
        change (1/12 : ℝ)^2≤(max (P.1-1/2) 0)^2+(max (|-P.2.1|-1/2) 0)^2
        rw [abs_neg,abs_of_nonneg hp.b_nonneg,max_eq_left (by linarith : 0≤P.1-1/2)]
        nlinarith [sq_nonneg (max (P.2.1-1/2) 0)]
      · rw [(eInteriorCycle_unchanged I.cycle P i hi).1]
        exact I.necessary.core i
    spread := eInteriorCycle_spread I.necessary.spread hp.angle }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := by simpa [eInteriorCycle,E] using neg_nonpos.mpr hp.b_nonneg
  witnesses := I.witnesses.eInterior (by linarith [hb.span_lt]) hp
  GA_hard := by
    simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,G,A] using I.GA_hard
  BT_hard := by
    simpa [eInteriorCycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro h
      have hh : I.witnesses.owner H=2 := by simpa [Witnesses.eInterior,H,D,E] using h
      exact I.zero_signs.HG_canceling hh
    TD_canceling := by
      intro h
      have hh : I.witnesses.owner T=0 := by simpa [Witnesses.eInterior,T,D,E] using h
      exact I.zero_signs.TD_canceling hh }
  E_radial := by
    right
    have ha := primary_lower_wide hq ⟨hb.span_nonneg,hb.span_lt.le⟩ hb.primary_sum hp
    change max |(I.cycle.point H).y| |(I.cycle.point D).y|≤P.1
    apply max_le
    · rw [abs_of_nonneg I.anchors_normal.H_nonneg]
      linarith [hb.H_tangent.2]
    · rw [abs_of_nonpos I.anchors_normal.D_nonpos]
      linarith [hb.D_tangent.2]

/-- The boundary reduction of E for nonpositive outer composites: a hard input that differs only at
E, with E on a face `E.y = 0`, `θ_E = θ_D` or `θ_E = θ_H`, the witnesses DE3 and EH1, no anchor
circle larger, and a strict loss when the original E is interior. The relaxation keeps the sign of
E and its two primary mixed witnesses. -/
theorem HardInput.reduce_nonpositive_E {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E∈Icc (I.cycle.theta D) (I.cycle.theta H) ∧
      ((J.cycle.point E).y=0 ∨ J.cycle.theta E=I.cycle.theta D ∨
        J.cycle.theta E=I.cycle.theta H) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (((I.cycle.point E).y<0 ∧ I.cycle.theta D<I.cycle.theta E ∧
        I.cycle.theta E<I.cycle.theta H) → StrictAnchorLoss I.cycle J.cycle) ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hb := I.nonpositive_composite_bounds hq hAB hAG hGH hDT hTB hHG hTD
  have hp := I.E_source_relaxation hDEorder hEHorder hDE hEH
  obtain ⟨P,hP,hcircle,hboundary,hstrict⟩ := exists_boundary_minimum hq
    ⟨hb.span_nonneg,hb.span_lt⟩ hb.H_primary.1 hb.D_primary.1 hb.primary_sum hp
  let J := I.fromNonpositiveEInterior hq hb hP
  have hcircle_source : corner
      ((I.cycle.point E).a,-(I.cycle.point E).y,I.cycle.theta E-I.cycle.theta D)=
      (I.cycle.point E).circle := by
    simp [corner,SignedPoint.circle,abs_of_nonpos I.E_nonpos]
  have hcircleJ : (J.cycle.point E).circle=corner P := eInteriorCycle_circle hP.b_nonneg
  have hunchanged (i : Vertex) (hi : i≠E) :
      J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i :=
    eInteriorCycle_unchanged I.cycle P i hi
  refine ⟨J,hunchanged,?_,?_,?_,?_,eInteriorCycle_DE (by linarith [hb.span_lt]) hP,
    eInteriorCycle_EH (by linarith [hb.span_lt]) hP⟩
  · change I.cycle.theta D+P.2.2∈Icc (I.cycle.theta D) (I.cycle.theta H)
    constructor <;> linarith [hP.angle.1,hP.angle.2]
  · rcases hboundary with hb0 | hδ0 | hε0
    · left
      change -P.2.1=0
      linarith
    · right; left
      change I.cycle.theta D+P.2.2=I.cycle.theta D
      linarith
    · right; right
      change I.cycle.theta D+P.2.2=I.cycle.theta H
      linarith
  · intro i hi
    by_cases hiE : i=E
    · subst i
      rw [hcircleJ,←hcircle_source]
      exact hcircle
    · rw [(hunchanged i hiE).1]
  · rintro ⟨hy,hD,hH⟩
    refine ⟨E,by norm_num [anchorVertices,E],?_⟩
    rw [hcircleJ,←hcircle_source]
    apply hstrict
    exact ⟨by simpa using neg_pos.mpr hy,by constructor <;> linarith⟩

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
namespace NonpositiveEndpointBarrier
open NegativeNoncancelingBarrier

theorem large_middle_primary_lt_one {H A : SignedPoint} {Θ t : ℝ}
    (hHu : H.y<9/10) (hAa : 1/2<A.a) (hAy : 1/2≤A.y)
    (hHc : H.Contained qCap) (hAc : A.Contained qCap)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hf : 0≤F H A Θ t) : H.a<1 := by
  have hAy0 : 0≤A.y := by linarith
  have hsingle := NonpositiveChainBounds.single_contact hHu hAa hAy0 hAc hΘ ht hf
  have hst := (transport_trig (show t∈Icc 0 (7/10 : ℝ) from
    ⟨ht.1,ht.2.trans hΘ.2⟩)).2.2.1
  have hse := (transport_trig (show Θ-t∈Icc 0 (7/10 : ℝ) from
    ⟨by linarith [ht.2],by linarith [ht.1,hΘ.2]⟩)).2.2.1
  have hprod := mul_nonneg (show 0≤A.y+1/2 by linarith) hst
  have hsum : 2≤H.y+A.a := by linarith [hsingle.2.2]
  have hAcircle := hAc
  rw [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy0] at hAcircle
  have hAsq := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num)
    (show 1≤A.y+1/2 by linarith) 2
  have hAu : A.a<151/125 := by
    dsimp [qCap] at hAcircle
    nlinarith
  have hHy : 99/125<H.y := by linarith
  have hHcircle := hHc
  rw [SignedPoint.Contained,SignedPoint.circle,
    abs_of_nonneg (show 0≤H.y by linarith)] at hHcircle
  by_contra! hbad
  have hprimary := pow_le_pow_left₀ (show (0:ℝ)≤3/2 by norm_num)
    (show 3/2≤H.a+1/2 by linarith) 2
  have htangent := pow_le_pow_left₀ (show (0:ℝ)≤323/250 by norm_num)
    (show 323/250≤H.y+1/2 by linarith) 2
  dsimp [qCap] at hHcircle
  nlinarith

end NonpositiveEndpointBarrier

namespace SignedCycle
open Candidate

private theorem r60_feasible_quarter {C : SignedCycle} {i : Vertex} (hw : Candidate.word i≠0)
    (j : Fin 4) : C.Feasible i j ↔
      quarterFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,quarterFeasible,delta,sub_nonneg]

private theorem r60_feasible_congr {C C' : SignedCycle} {i : Vertex}
    (h1 : C'.point i=C.point i) (h2 : C'.point (next i)=C.point (next i))
    (h3 : C'.theta i=C.theta i) (h4 : C'.theta (next i)=C.theta (next i)) (j : Fin 4) :
    C'.Feasible i j ↔ C.Feasible i j := by
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

theorem HardInput.nonpositive_large_A_primary_lt_one {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hHG : I.cycle.Feasible H 0) (hAy : 1/2≤(I.cycle.point A).y) :
    (I.cycle.point H).a<1 := by
  have hHy := (SignedPoint.coordinate_bounds (I.necessary.sorted H)
    (I.necessary.core H) (I.necessary.contained H) hq).2.2
  rw [abs_of_nonneg I.anchors_normal.H_nonneg] at hHy
  exact NonpositiveEndpointBarrier.large_middle_primary_lt_one hHy
    (SignedPoint.primary_gt_half (I.necessary.sorted A) (I.necessary.core A)) hAy
    ((I.necessary.contained H).trans hq) ((I.necessary.contained A).trans hq)
    ⟨by linarith,(le_abs_self _).trans (I.necessary.spread H A)⟩
    ⟨by linarith,by linarith⟩ (I.negative_HG0_composite hq hAG hGH hHG)

/-- With the tangent of A at least `1/2`, E at the frame of H with an EH1 witness is impossible; E
keeps its nonpositive sign and is not reflected. -/
theorem HardInput.nonpositive_large_A_EH_impossible {q : ℝ}
    (I : HardInput q) (hq : q≤qCap)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hHG : I.cycle.Feasible H 0) (hAy : 1/2≤(I.cycle.point A).y)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hEH : I.cycle.Feasible E 1) : False := by
  have hH := I.nonpositive_large_A_primary_lt_one hq hAG hGH hHG hAy
  have hcontact : 1≤(I.cycle.point H).a+(I.cycle.point E).y := by
    have hf := (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) 1).1 hEH
    rw [show next E=H by decide,hEHframe,sub_self] at hf
    simp only [quarterFeasible,quarterProjection,edgeWidth_zero,Real.sin_zero,
      Real.cos_zero] at hf
    simp at hf
    linarith
  linarith [I.E_nonpos]

/-- In the large-A sector, a hard input that differs only at E, with E at the frame of D, the
witnesses DE3 and EH1, no anchor circle larger, and a strict loss when the original E is
interior. -/
theorem HardInput.reduce_nonpositive_large_A_DE {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hAy : 1/2≤(I.cycle.point A).y)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E=J.cycle.theta D ∧ AnchorNonincrease I.cycle J.cycle ∧
      (((I.cycle.point E).y<0 ∧ I.cycle.theta D<I.cycle.theta E ∧
        I.cycle.theta E<I.cycle.theta H) → StrictAnchorLoss I.cycle J.cycle) ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  obtain ⟨J,hfixed,hEorder,hboundary,hnon,hstrict,hJDE,hJEH⟩ :=
    I.reduce_nonpositive_E hq hAB hAG hGH hDT hTB hHG hTD hDEorder hEHorder hDE hEH
  have hH := hfixed H (by decide)
  have hG := hfixed G (by decide)
  have hA := hfixed A (by decide)
  have hB := hfixed B (by decide)
  have hT := hfixed T (by decide)
  have hD := hfixed D (by decide)
  have hJAB : J.cycle.theta A=J.cycle.theta B := by rw [hA.2,hB.2,hAB]
  have hJAG : J.cycle.theta A≤J.cycle.theta G := by rw [hA.2,hG.2]; exact hAG
  have hJGH : J.cycle.theta G≤J.cycle.theta H := by rw [hG.2,hH.2]; exact hGH
  have hJDT : J.cycle.theta D≤J.cycle.theta T := by rw [hD.2,hT.2]; exact hDT
  have hJTB : J.cycle.theta T≤J.cycle.theta B := by rw [hT.2,hB.2]; exact hTB
  have hJHG : J.cycle.Feasible H 0 := by
    have hn : next H=G := by decide
    exact (r60_feasible_congr hH.1 (by rw [hn]; exact hG.1) hH.2 (by rw [hn]; exact hG.2) 0).2 hHG
  have hJTD : J.cycle.Feasible T 2 := by
    have hn : next T=D := by decide
    exact (r60_feasible_congr hT.1 (by rw [hn]; exact hD.1) hT.2 (by rw [hn]; exact hD.2) 2).2 hTD
  have hJAy : 1/2≤(J.cycle.point A).y := by rw [hA.1]; exact hAy
  have hEneq0 : (J.cycle.point E).y≠0 := by
    intro hzero
    exact J.nonpositive_zero_E_impossible hq hJAB hJAG hJGH hJDT hJTB hJHG hJTD hzero
      (by rw [hD.2]; exact hEorder.1) (by rw [hH.2]; exact hEorder.2) hJDE hJEH
  have hEHneq : J.cycle.theta E≠I.cycle.theta H := by
    intro hzero
    exact J.nonpositive_large_A_EH_impossible hq hJAG hJGH hJHG hJAy
      (by rw [hH.2]; exact hzero) hJEH
  have hDEeq : J.cycle.theta E=J.cycle.theta D := by
    rcases hboundary with hz | hd | hh
    · exact False.elim (hEneq0 hz)
    · rw [hD.2]
      exact hd
    · exact False.elim (hEHneq hh)
  exact ⟨J,hfixed,hDEeq,hnon,hstrict,hJDE,hJEH⟩

end SignedCycle
end SquaresInCircles.Eight
end
end
end
