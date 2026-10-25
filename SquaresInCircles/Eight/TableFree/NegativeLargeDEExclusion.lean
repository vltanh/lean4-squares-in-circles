module

public import SquaresInCircles.Eight.TableFree.NegativeLargeDEEndpoint

/-!
# Original negative large-A chains cannot meet the DE boundary

Uncompiled reconstruction.  The complete five-point weak system implies
a nonpositive exact-norm stress, while its actual fixed-weight simplex
has a positive defect.  The cycle application uses the original HG0,
GA0, AB, BT2, TD, DE3 and EH1 contacts and their original same-radius
circles.  The E tangent is not assigned a sign in the scalar exclusion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace NegativeLargeDEExclusion
open PositiveCancelingOuter NegativeLargeDEStress

/-- No vertex or scalar-positivity premise remains: the weights are
constructed from the actual total angle inside the proof. -/
theorem five_anchor_impossible {H A B D E : SignedPoint} {α t u e : ℝ}
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e)
    (hsum : t+u+e=α) (hα : α≤27/100)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y)
    (hcH : H.Contained qTrial) (hcA : A.Contained qTrial) (hcB : B.Contained qTrial)
    (hcD : D.Contained qTrial) (hcE : E.Contained qTrial)
    (hHA : NegativeOuterEZero.demand (1-V A t) e≤H.y)
    (hAB : 1≤A.y+B.y) (hlarge : 1/2≤A.y)
    (hBD : 1+W u≤B.a*Real.cos u-B.y*Real.sin u+D.y)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) : False := by
  obtain ⟨a,β,ε,ha,hβ,hε,hpositive⟩ :=
    NegativeLargeDEEndpoint.exists_positive_defect ⟨by linarith,hα⟩ ht hu he hsum
  have hnonpositive := five_anchor_defect ha hβ hε ht hu he hsum hα
    hyH hyA hyB hyD hcH hcA hcB hcD hcE hHA hAB hlarge hBD hDE hEH
  linarith

end NegativeLargeDEExclusion

namespace SignedCycle
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

/-- The actual retained negative HG0 composite, with the opposite TD
already aligned, is excluded at E=D when A's original tangent is large.
Only B,D,E are reflected in the scalar coordinates; their actual circles
and the original selected mixed axes are unchanged. -/
theorem HardInput.nonpositive_large_A_DE_impossible {q : ℝ}
    (I : HardInput q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDframe : I.cycle.theta T=I.cycle.theta D)
    (hHG : I.cycle.Feasible H 0)
    (hAy : 1/2≤(I.cycle.point A).y)
    (hDEframe : I.cycle.theta E=I.cycle.theta D)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hTD := I.aligned_TD_two hTDframe
  have hDT : I.cycle.theta D≤I.cycle.theta T := by rw [hTDframe]
  have hTB : I.cycle.theta T≤I.cycle.theta B := by rw [hTDframe]; exact hDB
  have hb := I.nonpositive_composite_bounds hcap hAB hAG hGH hDT hTB hHG hTD
  let t := I.cycle.theta G-I.cycle.theta A
  let u := I.cycle.theta B-I.cycle.theta D
  let e := I.cycle.theta H-I.cycle.theta G
  let α := I.cycle.theta H-I.cycle.theta D
  have ht : 0≤t := sub_nonneg.mpr hAG
  have hu : 0≤u := sub_nonneg.mpr hDB
  have he : 0≤e := sub_nonneg.mpr hGH
  have hsum : t+u+e=α := by dsimp [t,u,e,α]; rw [hAB]; ring
  have hα : α≤27/100 := hb.span_lt.le
  have hHF := I.negative_HG0_composite hcap hAG hGH hHG
  have hHA : NegativeOuterEZero.demand (1-V (I.cycle.point A) t) e≤
      (I.cycle.point H).y := by
    dsimp [NegativeNoncancelingBarrier.F] at hHF
    rw [show (I.cycle.theta H-I.cycle.theta A)-
      (I.cycle.theta G-I.cycle.theta A)=e by dsimp [e]; ring] at hHF
    change 0≤(I.cycle.point H).y-1/2+
      (V (I.cycle.point A) t-1)*Real.cos e-(13/12)*Real.sin e at hHF
    dsimp [NegativeOuterEZero.demand]
    linarith
  have hDF := I.negative_TD2_composite hcap hDT hTB hTD
  rw [hTDframe] at hDF
  have hBD : 1+NegativeLargeDEStress.W u≤
      (I.cycle.point B).reflect.a*Real.cos u-
        (I.cycle.point B).reflect.y*Real.sin u+(I.cycle.point D).reflect.y := by
    change 0≤NegativeNoncancelingBarrier.F
      (I.cycle.point D).reflect (I.cycle.point B).reflect u u at hDF
    simp only [NegativeNoncancelingBarrier.F,sub_self,Real.cos_zero,Real.sin_zero,
      mul_one,mul_zero,sub_zero] at hDF
    dsimp [V,NegativeLargeDEStress.W] at *
    linarith
  have hABsum : 1≤(I.cycle.point A).y+(I.cycle.point B).reflect.y := by
    have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
      simpa [normalOwners,A] using I.witnesses.allowed A
    have hf := (r60_feasible_zero (C := I.cycle) (i := A) (by decide) _).1
      (I.witnesses.feasible A)
    rw [show next A=B by decide,hAB,sub_self] at hf
    simp only [zeroFeasible,zeroProjection_aligned,edgeWidth_zero] at hf
    simp only [SignedPoint.reflect]
    rcases hj with hj | hj <;> rw [hj] at hf <;> simp at hf <;> linarith
  have hDEcontact : 1≤(I.cycle.point D).reflect.a+(I.cycle.point E).reflect.y := by
    have hf := (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) _).1 hDE
    rw [show next D=E by decide,hDEframe,sub_self] at hf
    simp only [quarterFeasible,quarterProjection,edgeWidth_zero,Real.sin_zero,
      Real.cos_zero] at hf
    simp only [SignedPoint.reflect]
    simp at hf
    linarith
  have hEHcontact : NegativeLargeDEStress.W α≤
      (I.cycle.point H).a+(I.cycle.point E).reflect.a*Real.sin α-
        (I.cycle.point E).reflect.y*Real.cos α := by
    have hαdom : α∈Icc 0 (7/10:ℝ) := ⟨hb.span_nonneg,by linarith⟩
    have hh : edgeWidth α≤(I.cycle.point H).a+
        (I.cycle.point E).a*Real.sin α+(I.cycle.point E).y*Real.cos α := by
      have hf := (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) _).1 hEH
      rw [show next E=H by decide,hDEframe] at hf
      simpa [quarterFeasible,quarterProjection,α] using hf
    rw [edgeWidth_positive_formula hαdom] at hh
    simpa [NegativeLargeDEStress.W,SignedPoint.reflect] using hh
  have hc (i : Vertex) : (I.cycle.point i).Contained qTrial :=
    (I.necessary.contained i).trans hq
  exact NegativeLargeDEExclusion.five_anchor_impossible
    (H := I.cycle.point H) (A := I.cycle.point A) (B := (I.cycle.point B).reflect)
    (D := (I.cycle.point D).reflect) (E := (I.cycle.point E).reflect)
    ht hu he hsum hα I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.D_nonpos)
    (hc H) (hc A) (by simpa using hc B) (by simpa using hc D) (by simpa using hc E)
    hHA hABsum hAy hBD hDEcontact hEHcontact

/-- The actual E-only minimizer closes the entire ordered large-A
negative sector.  Its H/A/B/D source circles and TD alignment are literal
throughout; no equality or sharp-radius conclusion is used. -/
theorem HardInput.nonpositive_large_A_ordered_impossible {q : ℝ}
    (I : HardInput q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDB : I.cycle.theta D≤I.cycle.theta B)
    (hTDframe : I.cycle.theta T=I.cycle.theta D)
    (hHG : I.cycle.Feasible H 0)
    (hAy : 1/2≤(I.cycle.point A).y)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hTD := I.aligned_TD_two hTDframe
  obtain ⟨J,hfixed,hED,hnon,hstrict,hJDE,hJEH⟩ :=
    I.reduce_nonpositive_large_A_DE hcap hAB hAG hGH
      (by rw [hTDframe]) (by rw [hTDframe]; exact hDB) hHG hTD hAy
      hDEorder hEHorder hDE hEH
  have hH := hfixed H (by decide)
  have hG := hfixed G (by decide)
  have hA := hfixed A (by decide)
  have hB := hfixed B (by decide)
  have hT := hfixed T (by decide)
  have hD := hfixed D (by decide)
  apply J.nonpositive_large_A_DE_impossible hq
  · rw [hA.2,hB.2]; exact hAB
  · rw [hA.2,hG.2]; exact hAG
  · rw [hG.2,hH.2]; exact hGH
  · rw [hD.2,hB.2]; exact hDB
  · rw [hT.2,hD.2]; exact hTDframe
  · have hnH : next H=G := by decide
    exact (r60_feasible_congr hH.1 (by rw [hnH]; exact hG.1) hH.2
      (by rw [hnH]; exact hG.2) 0).2 hHG
  · rw [hA.1]; exact hAy
  · exact hED
  · exact hJDE
  · exact hJEH

end SignedCycle
end SquaresInCircles.Eight.TableFree
