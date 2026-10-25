module

public import SquaresInCircles.Eight.Owners.E.ZeroCapEndpoints
public import SquaresInCircles.Eight.Owners.E.ZeroGeometry
public import SquaresInCircles.Eight.Owners.Negative.OuterEZero
public import SquaresInCircles.Eight.Owners.Nonpositive.ChainBounds

/-!
# Eight squares: E-zero exclusion with both original negative outer composites

Each actual middle tangent independently selects
error absorption or E-angle deletion.  Both alternatives retain its
original A/B coordinates and circle.  Their conserved angle differences
join at the original aligned AB separator and feed the strict two-cap
comparison.  All outer and E contacts are the original weak witnesses.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace NonpositiveEZeroCycle
open NegativeOuterEZero PositiveCancelingOuter EZeroFunctions

/-- Arbitrary weak radial constraints are allowed on every original
point.  H,A,B,D have nonnegative tangent coordinates in this five-point
statement; the physical cycle below reflects only B and D. -/
theorem five_anchor_impossible {H A B D E : SignedPoint} {t u e f ε δ : ℝ}
    (hHs : H.Sorted) (hDs : D.Sorted) (hEs : E.Sorted)
    (hAa : 1/2<A.a) (hBa : 1/2<B.a)
    (hHy : 0≤H.y) (hAy : 0≤A.y) (hBy : 0≤B.y) (hDy : 0≤D.y)
    (hHc : H.Contained qCap) (hAc : A.Contained qCap) (hBc : B.Contained qCap)
    (hDc : D.Contained qCap) (hEc : E.Contained qCap) (hE0 : E.y=0)
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e) (hf : 0≤f) (hε : 0≤ε) (hδ : 0≤δ)
    (hsum : t+u+e+f=ε+δ) (hspan : ε+δ≤7/10)
    (hHsource : demand (1-V A t) e≤H.y)
    (hDsource : demand (1-V B u) f≤D.y)
    (hAB : 1≤A.y+B.y)
    (hEH : edgeWidth ε≤H.a+E.a*Real.sin ε)
    (hDE : edgeWidth δ≤D.a+E.a*Real.sin δ) : False := by
  have hε' : ε∈Icc 0 (7/10 : ℝ) := ⟨hε,by linarith⟩
  have hδ' : δ∈Icc 0 (7/10 : ℝ) := ⟨hδ,by linarith⟩
  have hHcap := EZeroGeometry.tangent_cap hHs hHy hHc hEs hEc hE0 hε' hEH
  have hDcap := EZeroGeometry.tangent_cap hDs hDy hDc hEs hEc hE0 hδ' hDE
  have hHu : H.y<9/10 := hHcap.trans_lt (EZeroCapped.capped_bounds hε').2
  have hDu : D.y<9/10 := hDcap.trans_lt (EZeroCapped.capped_bounds hδ').2
  obtain ⟨τ,ε',hτ,hε0,hτupper,hεupper,hHangle,hHcontact⟩ :=
    side_cap hHu hAa hAy hAc ht he (by linarith) hε' hHsource hHcap
  obtain ⟨υ,δ',hυ,hδ0,hυupper,hδupper,hDangle,hDcontact⟩ :=
    side_cap hDu hBa hBy hBc hu hf (by linarith) hδ' hDsource hDcap
  have hjoin : τ+υ=ε'+δ' := by linarith
  have hnewspan : ε'+δ'≤7/10 := by linarith
  have hεdom : ε'∈Icc 0 (7/10 : ℝ) := ⟨hε0,by linarith⟩
  have hδdom : δ'∈Icc 0 (7/10 : ℝ) := ⟨hδ0,by linarith⟩
  have hτdom : τ∈Icc 0 (7/10 : ℝ) := ⟨hτ,by linarith⟩
  have hυdom : υ∈Icc 0 (7/10 : ℝ) := ⟨hυ,by linarith⟩
  have hAcircle : (A.a+1/2)^2+(A.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] using hAc
  have hBcircle : (B.a+1/2)^2+(B.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hBy] using hBc
  have hAcontact : 3/2-capped ε'≤
      (A.a+1/2-1)*Real.cos τ-(A.y+1/2)*Real.sin τ := by
    rw [edgeWidth_positive_formula hτdom] at hHcontact
    linarith
  have hBcontact : 3/2-capped δ'≤
      (B.a+1/2-1)*Real.cos υ-(B.y+1/2)*Real.sin υ := by
    rw [edgeWidth_positive_formula hυdom] at hDcontact
    linarith
  have hA := HardSplitCap.cap_majorizes_weak_contact
    (EZeroCapEndpoints.feasible hεdom) hτdom
    (show 0≤A.y+1/2 by linarith) hAcontact hAcircle
  have hB := HardSplitCap.cap_majorizes_weak_contact
    (EZeroCapEndpoints.feasible hδdom) hυdom
    (show 0≤B.y+1/2 by linarith) hBcontact hBcircle
  have hcaps := HardSplitCap.split_endpoint
    (EZeroCapEndpoints.feasible hεdom) (EZeroCapEndpoints.feasible hδdom)
    hτ hυ (by linarith : τ+υ≤7/10)
  rw [hjoin] at hcaps
  have hmax := max_lt_iff.mpr
    ⟨EZeroCapEndpoints.first_endpoint hε0 hδ0 hnewspan,
      EZeroCapEndpoints.second_endpoint hε0 hδ0 hnewspan⟩
  have hstrict := hcaps.trans_lt hmax
  linarith

end NonpositiveEZeroCycle

namespace SignedCycle
open Candidate NegativeOuterEZero PositiveCancelingOuter

private theorem r60_feasible_zero {C : SignedCycle} {i : Vertex} (hw : Candidate.word i=0)
    (j : Fin 4) : C.Feasible i j ↔
      zeroFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,zeroFeasible,delta,sub_nonneg]

private theorem r60_feasible_quarter {C : SignedCycle} {i : Vertex} (hw : Candidate.word i≠0)
    (j : Fin 4) : C.Feasible i j ↔
      quarterFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,quarterFeasible,delta,sub_nonneg]

/-- The actual nonpositive HG0/TD2 sector, including either aligned
boundary, cannot have a zero E tangent between the original H/D frames.
There is no intermediate-sign or frontier-circle premise. -/
theorem HardInput.nonpositive_zero_E_impossible {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hE0 : (I.cycle.point E).y=0)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H)
    (hDE : I.cycle.Feasible D 3) (hEH : I.cycle.Feasible E 1) : False := by
  let t := I.cycle.theta G-I.cycle.theta A
  let u := I.cycle.theta B-I.cycle.theta T
  let e := I.cycle.theta H-I.cycle.theta G
  let f := I.cycle.theta T-I.cycle.theta D
  let ε := I.cycle.theta H-I.cycle.theta E
  let δ := I.cycle.theta E-I.cycle.theta D
  have ht : 0≤t := sub_nonneg.mpr hAG
  have hu : 0≤u := sub_nonneg.mpr hTB
  have he : 0≤e := sub_nonneg.mpr hGH
  have hf : 0≤f := sub_nonneg.mpr hDT
  have hε : 0≤ε := sub_nonneg.mpr hEHorder
  have hδ : 0≤δ := sub_nonneg.mpr hDEorder
  have hsum : t+u+e+f=ε+δ := by
    dsimp [t,u,e,f,ε,δ]
    rw [hAB]
    ring
  have hspan : ε+δ≤7/10 := by
    have hh := (le_abs_self _).trans (I.necessary.spread H D)
    dsimp [ε,δ,frameCap] at *
    linarith
  have hHF := I.negative_HG0_composite hq hAG hGH hHG
  have hDF := I.negative_TD2_composite hq hDT hTB hTD
  have hHsource : demand (1-V (I.cycle.point A) t) e≤(I.cycle.point H).y := by
    dsimp [NegativeNoncancelingBarrier.F] at hHF
    rw [show (I.cycle.theta H-I.cycle.theta A)-
      (I.cycle.theta G-I.cycle.theta A)=e by dsimp [e]; ring] at hHF
    change 0≤(I.cycle.point H).y-1/2+
      (V (I.cycle.point A) t-1)*Real.cos e-(13/12)*Real.sin e at hHF
    dsimp [demand]
    linarith
  have hDsource : demand (1-V (I.cycle.point B).reflect u) f≤(I.cycle.point D).reflect.y := by
    dsimp [NegativeNoncancelingBarrier.F] at hDF
    rw [show (I.cycle.theta B-I.cycle.theta D)-
      (I.cycle.theta B-I.cycle.theta T)=f by dsimp [f]; ring] at hDF
    change 0≤(I.cycle.point D).reflect.y-1/2+
      (V (I.cycle.point B).reflect u-1)*Real.cos f-(13/12)*Real.sin f at hDF
    dsimp [demand]
    linarith
  have hEHcontact : edgeWidth ε≤(I.cycle.point H).a+(I.cycle.point E).a*Real.sin ε := by
    have h := (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) 1).1 hEH
    rw [show next E=H by decide] at h
    simpa [quarterFeasible,quarterProjection,hE0,ε] using h
  have hDEcontact : edgeWidth δ≤(I.cycle.point D).a+(I.cycle.point E).a*Real.sin δ := by
    have h := (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) 3).1 hDE
    rw [show next D=E by decide] at h
    simpa [quarterFeasible,quarterProjection,hE0,δ] using h
  have hABsum : 1≤(I.cycle.point A).y+(I.cycle.point B).reflect.y := by
    have hj : I.witnesses.owner A=0 ∨ I.witnesses.owner A=2 := by
      simpa [normalOwners,A] using I.witnesses.allowed A
    have hf := (r60_feasible_zero (C := I.cycle) (i := A) (by decide) _).1
      (I.witnesses.feasible A)
    rw [show next A=B by decide,hAB,sub_self] at hf
    simp only [zeroFeasible,zeroProjection_aligned,edgeWidth_zero] at hf
    simp only [SignedPoint.reflect]
    rcases hj with hj | hj <;> rw [hj] at hf <;> simp at hf <;> linarith
  have hc (i : Vertex) : (I.cycle.point i).Contained qCap :=
    (I.necessary.contained i).trans hq
  exact NonpositiveEZeroCycle.five_anchor_impossible
    (H := I.cycle.point H) (A := I.cycle.point A) (B := (I.cycle.point B).reflect)
    (D := (I.cycle.point D).reflect) (E := I.cycle.point E)
    (I.necessary.sorted H) (by simpa using I.necessary.sorted D) (I.necessary.sorted E)
    (SignedPoint.primary_gt_half (I.necessary.sorted A) (I.necessary.core A))
    (by simpa [SignedPoint.reflect] using
      SignedPoint.primary_gt_half (I.necessary.sorted B) (I.necessary.core B))
    I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.D_nonpos)
    (hc H) (hc A) (by simpa using hc B) (by simpa using hc D) (hc E) hE0
    ht hu he hf hε hδ hsum hspan hHsource hDsource hABsum
    hEHcontact (by simpa [SignedPoint.reflect] using hDEcontact)

end SignedCycle
end SquaresInCircles.Eight
