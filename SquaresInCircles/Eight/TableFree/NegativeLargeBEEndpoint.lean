module

public import SquaresInCircles.Eight.TableFree.NegativeLargeDEExclusion

/-!
# The large-B negative sector reaches the original DE alignment

Uncompiled reconstruction.  The signed-E five-anchor exclusion is used
with an explicit algebraic relabeling, not a reflection of HardInput
that would change its E-sign hypothesis.  The subsequent E minimizer
fixes every non-E point and frame, and records a strict original E
circle loss whenever its original DE angle was positive.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate PositiveCancelingOuter

private theorem r60_feasible_zero {C : SignedCycle} {i : Vertex} (hw : Candidate.word i=0)
    (j : Fin 4) : C.Feasible i j ↔
      zeroFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,zeroFeasible,delta,sub_nonneg]

private theorem r60_feasible_quarter {C : SignedCycle} {i : Vertex} (hw : Candidate.word i≠0)
    (j : Fin 4) : C.Feasible i j ↔
      quarterFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,quarterFeasible,delta,sub_nonneg]

private theorem r60_feasible_congr {C C' : SignedCycle} {i : Vertex}
    (h1 : C'.point i=C.point i) (h2 : C'.point (next i)=C.point (next i))
    (h3 : C'.theta i=C.theta i) (h4 : C'.theta (next i)=C.theta (next i)) (j : Fin 4) :
    C'.Feasible i j ↔ C.Feasible i j := by
  simp only [Feasible,slack,edge,delta,h1,h2,h3,h4]

theorem HardInput.nonpositive_large_B_EH_impossible {q : ℝ}
    (I : HardInput q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hGHframe : I.cycle.theta G=I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 2)
    (hBy : 1/2≤ -(I.cycle.point B).y)
    (hEHframe : I.cycle.theta E=I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hHG := I.aligned_HG_zero hGHframe
  have hAG : I.cycle.theta A≤I.cycle.theta G := by rw [hGHframe]; exact hAH
  have hGH : I.cycle.theta G≤I.cycle.theta H := by rw [hGHframe]
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  let t := I.cycle.theta B-I.cycle.theta T
  let u := I.cycle.theta H-I.cycle.theta A
  let e := I.cycle.theta T-I.cycle.theta D
  let α := I.cycle.theta H-I.cycle.theta D
  have ht : 0≤t := sub_nonneg.mpr hTB
  have hu : 0≤u := sub_nonneg.mpr hAH
  have he : 0≤e := sub_nonneg.mpr hDT
  have hsum : t+u+e=α := by dsimp [t,u,e,α]; rw [hAB]; ring
  have hα : α≤27/100 := hb.span_lt.le
  have hDF := I.negative_TD2_composite hcap hDT hTB hTD
  have hHA : NegativeOuterEZero.demand (1-V (I.cycle.point B).reflect t) e≤
      (I.cycle.point D).reflect.y := by
    dsimp [NegativeNoncancelingBarrier.F] at hDF
    rw [show (I.cycle.theta B-I.cycle.theta D)-
      (I.cycle.theta B-I.cycle.theta T)=e by dsimp [e]; ring] at hDF
    change 0≤(I.cycle.point D).reflect.y-1/2+
      (V (I.cycle.point B).reflect t-1)*Real.cos e-(13/12)*Real.sin e at hDF
    dsimp [NegativeOuterEZero.demand]
    linarith
  have hHF := I.negative_HG0_composite hcap hAG hGH hHG
  rw [hGHframe] at hHF
  have hBD : 1+NegativeLargeDEStress.W u≤
      (I.cycle.point A).a*Real.cos u-(I.cycle.point A).y*Real.sin u+
        (I.cycle.point H).y := by
    change 0≤NegativeNoncancelingBarrier.F (I.cycle.point H) (I.cycle.point A) u u at hHF
    simp only [NegativeNoncancelingBarrier.F,sub_self,Real.cos_zero,Real.sin_zero,
      mul_one,mul_zero,sub_zero] at hHF
    dsimp [V,NegativeLargeDEStress.W] at *
    linarith
  have hABsum : 1≤(I.cycle.point B).reflect.y+(I.cycle.point A).y := by
    have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
      simpa [normalOwners,A] using I.witnesses.allowed A
    have hf := (r60_feasible_zero (C := I.cycle) (i := A) (by decide) _).1
      (I.witnesses.feasible A)
    rw [show next A=B by decide,hAB,sub_self] at hf
    simp only [zeroFeasible,zeroProjection_aligned,edgeWidth_zero] at hf
    simp only [SignedPoint.reflect]
    rcases hj with hj | hj <;> rw [hj] at hf <;> simp at hf <;> linarith
  have hDEcontact : 1≤(I.cycle.point H).a+(I.cycle.point E).y := by
    have hf := (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) _).1 hEH
    rw [show next E=H by decide,hEHframe,sub_self] at hf
    simp only [quarterFeasible,quarterProjection,edgeWidth_zero,Real.sin_zero,
      Real.cos_zero] at hf
    simp at hf
    linarith
  have hEHcontact : NegativeLargeDEStress.W α≤
      (I.cycle.point D).reflect.a+(I.cycle.point E).a*Real.sin α-
        (I.cycle.point E).y*Real.cos α := by
    have hαdom : α∈Icc 0 (7/10:ℝ) := ⟨hb.span_nonneg,by linarith⟩
    have hh : edgeWidth α≤(I.cycle.point D).a+
        (I.cycle.point E).a*Real.sin α-(I.cycle.point E).y*Real.cos α := by
      have hf := (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) _).1 hDE
      rw [show next D=E by decide,hEHframe] at hf
      simpa [quarterFeasible,quarterProjection,α] using hf
    rw [edgeWidth_positive_formula hαdom] at hh
    simpa [NegativeLargeDEStress.W,SignedPoint.reflect] using hh
  have hc (i : Vertex) : (I.cycle.point i).Contained qTrial :=
    (I.necessary.contained i).trans hq
  exact NegativeLargeDEExclusion.five_anchor_impossible
    (H := (I.cycle.point D).reflect) (A := (I.cycle.point B).reflect)
    (B := I.cycle.point A) (D := I.cycle.point H) (E := I.cycle.point E)
    ht hu he hsum hα
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.D_nonpos)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
    I.anchors_normal.A_nonneg I.anchors_normal.H_nonneg
    (by simpa using hc D) (by simpa using hc B) (hc A) (hc H) (hc E)
    hHA hABsum (by simpa [SignedPoint.reflect] using hBy) hBD hDEcontact hEHcontact

/-- The actual large-B canonical boundary, with a strict E loss for
every positive original DE split.  All four other anchor circles remain
literal, and the original negative TD composite is retained. -/
theorem HardInput.reduce_nonpositive_large_B_DE {q : ℝ}
    (I : HardInput q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAH : I.cycle.theta A≤I.cycle.theta H)
    (hGHframe : I.cycle.theta G=I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 2)
    (hBy : 1/2≤ -(I.cycle.point B).y)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E=J.cycle.theta D ∧ AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta D<I.cycle.theta E → StrictAnchorLoss I.cycle J.cycle) ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hHG := I.aligned_HG_zero hGHframe
  have hAG : I.cycle.theta A≤I.cycle.theta G := by rw [hGHframe]; exact hAH
  have hGH : I.cycle.theta G≤I.cycle.theta H := by rw [hGHframe]
  have hsourceZero : (I.cycle.point E).y≠0 := by
    intro hz
    exact I.nonpositive_zero_E_impossible hcap hAB hAG hGH hDT hTB hHG hTD hz
      hDEorder hEHorder hDE hEH
  have hsourceEH : I.cycle.theta E≠I.cycle.theta H := by
    intro hz
    exact I.nonpositive_large_B_EH_impossible hq hAB hAH hGHframe hDT hTB hTD hBy hz hDE hEH
  obtain ⟨J,hfixed,hEorder,hboundary,hnon,hstrict,hJDE,hJEH⟩ :=
    I.reduce_nonpositive_E hcap hAB hAG hGH hDT hTB hHG hTD hDEorder hEHorder hDE hEH
  have hH := hfixed H (by decide)
  have hG := hfixed G (by decide)
  have hA := hfixed A (by decide)
  have hB := hfixed B (by decide)
  have hT := hfixed T (by decide)
  have hD := hfixed D (by decide)
  have hJAB : J.cycle.theta A=J.cycle.theta B := by rw [hA.2,hB.2]; exact hAB
  have hJAH : J.cycle.theta A≤J.cycle.theta H := by rw [hA.2,hH.2]; exact hAH
  have hJGH : J.cycle.theta G=J.cycle.theta H := by rw [hG.2,hH.2]; exact hGHframe
  have hJDT : J.cycle.theta D≤J.cycle.theta T := by rw [hD.2,hT.2]; exact hDT
  have hJTB : J.cycle.theta T≤J.cycle.theta B := by rw [hT.2,hB.2]; exact hTB
  have hJTD : J.cycle.Feasible T 2 := by
    have hnT : next T=D := by decide
    exact (r60_feasible_congr hT.1 (by rw [hnT]; exact hD.1) hT.2
      (by rw [hnT]; exact hD.2) 2).2 hTD
  have hJBy : 1/2≤ -(J.cycle.point B).y := by rw [hB.1]; exact hBy
  have hJzero : (J.cycle.point E).y≠0 := by
    intro hz
    exact J.nonpositive_zero_E_impossible hcap hJAB
      (by rw [hJGH]; exact hJAH) (by rw [hJGH]) hJDT hJTB
      (J.aligned_HG_zero hJGH) hJTD hz
      (by rw [hD.2]; exact hEorder.1) (by rw [hH.2]; exact hEorder.2) hJDE hJEH
  have hJEHneq : J.cycle.theta E≠I.cycle.theta H := by
    intro hz
    apply J.nonpositive_large_B_EH_impossible hq hJAB hJAH hJGH hJDT hJTB hJTD hJBy
      (by rw [hH.2]; exact hz) hJDE hJEH
  have hJED : J.cycle.theta E=J.cycle.theta D := by
    rcases hboundary with hz | hd | hh
    · exact False.elim (hJzero hz)
    · rw [hD.2]; exact hd
    · exact False.elim (hJEHneq hh)
  refine ⟨J,hfixed,hJED,hnon,?_,hJDE,hJEH⟩
  intro hDEpos
  have hyneg : (I.cycle.point E).y<0 := by
    by_contra! hy
    exact hsourceZero (le_antisymm I.E_nonpos hy)
  have hEHlt : I.cycle.theta E<I.cycle.theta H := by
    by_contra! hh
    exact hsourceEH (le_antisymm hEHorder hh)
  exact hstrict ⟨hyneg,hDEpos,hEHlt⟩

end SquaresInCircles.Eight.TableFree.SignedCycle
