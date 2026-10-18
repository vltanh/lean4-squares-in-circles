module

public import SquaresInCircles.Eight.Generated.AffineCovers
public import SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.Enhanced
public import SquaresInCircles.Eight.Candidate.Mismatch

/-! Complete F7/F8 affine-table instances in their dependency order.
All Lean source and generated decision proof scripts remain uncompiled. -/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate.Tables
open Arithmetic
open scoped BigOperators

theorem affineBudgets_fin7 (i : Fin 7) :
    i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by
  revert i; decide

theorem affineBudgets_fin4 (j : Fin 4) : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by
  revert j; decide

theorem affineBudgets_all_axes (a : ForwardAxis) : a∈[.one,.two,.three,.four] := by
  cases a <;> simp

/-- Every table records the radius `Q1` as a rational number. These helpers are
public because the exposed budget definitions below use them. -/
theorem affineBudgets_radius {r : ℚ} (h : r = 1957767069/500000000) :
    (r : ℝ) = Q1 := by
  rw [h, Q1]
  push_cast
  ring

theorem g_lower_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C)
    (hFail : C.tangent G≤ -4/5) : False := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.radius) rfl]
  intro C F hE hFail
  have he : C.tangent 6≤0 := hE
  change C.tangent 1≤ -4/5 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.cuts =
        ![⟨-1,1⟩, ⟨-1,(-4/5)⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.differenceRange =
        ![⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.charge i:ℝ)=charge (0) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.charge =
        ![0, 0, 0, 0, 0, 0, 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.GLowerAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  have ht : SquaresInCircles.Eight.Generated.Affine.GLowerAffine.table.target =
      ![(8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000)] := rfl
  rw [ht] at hbudget
  norm_num [Fin.sum_univ_seven] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem g_upper_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C)
    (hFail : -1/20≤C.tangent G) : False := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.radius) rfl]
  intro C F hE hFail
  have he : C.tangent 6≤0 := hE
  change -1/20≤C.tangent 1 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.cuts =
        ![⟨-1,1⟩, ⟨(-1/20),1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.differenceRange =
        ![⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.charge i:ℝ)=charge (0) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.charge =
        ![0, 0, 0, 0, 0, 0, 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.GUpperAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  have ht : SquaresInCircles.Eight.Generated.Affine.GUpperAffine.table.target =
      ![(8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000)] := rfl
  rw [ht] at hbudget
  norm_num [Fin.sum_univ_seven] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem t_lower_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C)
    (hFail : C.tangent T≤1/20) : False := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.radius) rfl]
  intro C F hE hG hFail
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  change C.tangent 4≤1/20 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.cuts =
        ![⟨-1,1⟩, ⟨(-4/5),(-1/20)⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨-1,(1/20)⟩, ⟨-1,1⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.differenceRange =
        ![⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.charge i:ℝ)=charge (0) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.charge =
        ![0, 0, 0, 0, 0, 0, 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.TLowerAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  have ht : SquaresInCircles.Eight.Generated.Affine.TLowerAffine.table.target =
      ![(561/625), (561/625), (561/625), (561/625), (561/625), (561/625), (561/625)] := rfl
  rw [ht] at hbudget
  norm_num [Fin.sum_univ_seven] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem t_upper_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C)
    (hFail : 4/5≤C.tangent T) : False := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.radius) rfl]
  intro C F hE hG hFail
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  change 4/5≤C.tangent 4 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.cuts =
        ![⟨-1,1⟩, ⟨(-4/5),(-1/20)⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨(4/5),1⟩, ⟨-1,1⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.differenceRange =
        ![⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.charge i:ℝ)=charge (0) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.charge =
        ![0, 0, 0, 0, 0, 0, 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.TUpperAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  have ht : SquaresInCircles.Eight.Generated.Affine.TUpperAffine.table.target =
      ![(8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000)] := rfl
  rw [ht] at hbudget
  norm_num [Fin.sum_univ_seven] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem h_lower_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C)
    (hFail : C.tangent H≤1/2) : False := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.radius) rfl]
  intro C F hE hG hT hFail
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  change C.tangent 0≤1/2 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.cuts =
        ![⟨-1,(1/2)⟩, ⟨(-4/5),(-1/20)⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨(1/20),(4/5)⟩, ⟨-1,1⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.differenceRange =
        ![⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.charge i:ℝ)=charge (0) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.charge =
        ![0, 0, 0, 0, 0, 0, 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.HLowerAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  have ht : SquaresInCircles.Eight.Generated.Affine.HLowerAffine.table.target =
      ![(8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000), (8977/10000)] := rfl
  rw [ht] at hbudget
  norm_num [Fin.sum_univ_seven] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem d_upper_excluded {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C)
    (hFail : -1/2≤C.tangent D) : False := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.radius) rfl]
  intro C F hE hG hT hFail
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  change -1/2≤C.tangent 5 at hFail
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.cuts =
        ![⟨-1,1⟩, ⟨(-4/5),(-1/20)⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨(1/20),(4/5)⟩, ⟨(-1/2),1⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.differenceRange =
        ![⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.charge i:ℝ)=charge (0) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.charge =
        ![0, 0, 0, 0, 0, 0, 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.DUpperAffine.charged_bound C F (0) hb hcuts hdiff haxes
  have hbudget := P.cyclic
  have ht : SquaresInCircles.Eight.Generated.Affine.DUpperAffine.table.target =
      ![(17953/20000), (17953/20000), (17953/20000), (17953/20000), (17953/20000), (17953/20000), (17953/20000)] := rfl
  rw [ht] at hbudget
  norm_num [Fin.sum_univ_seven] at hbudget
  have hpi := two_pi_lt_710_over_113
  linarith

theorem g_cut {C : BoundaryCycle Q1} (F : Frame C) (hE : EHalf C) : GCut C := by
  constructor
  · by_contra! hFail; exact g_lower_excluded F hE hFail
  · by_contra! hFail; exact g_upper_excluded F hE hFail

theorem t_cut {C : BoundaryCycle Q1} (F : Frame C) (hE : EHalf C) (hG : GCut C) : TCut C := by
  constructor
  · by_contra! hFail; exact t_lower_excluded F hE hG hFail
  · by_contra! hFail; exact t_upper_excluded F hE hG hFail

theorem hd_cut {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) : HDCut C := by
  constructor
  · by_contra! hFail; exact h_lower_excluded F hE hG hT hFail
  · by_contra! hFail; exact d_upper_excluded F hE hG hT hFail

noncomputable def coarse_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C)
    : ChargedBound C F (coarseBeta) coarseGamma := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.radius) rfl]
  intro C F hE hG hT
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.cuts =
        ![⟨-1,1⟩, ⟨(-4/5),(-1/20)⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨(1/20),(4/5)⟩, ⟨-1,1⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.differenceRange =
        ![⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.charge i:ℝ)=charge (coarseBeta) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.charge =
        ![(99/5000), 0, (99/5000), (99/5000), (99/5000), (99/5000), 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.charged_bound C F (coarseBeta) hb hcuts hdiff haxes
  have hγ : (fun i => (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.target i:ℝ)) = coarseGamma := by
    have ht : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.target =
        ![(89727/100000), (89727/100000), (89727/100000), (89727/100000), (89727/100000), (89727/100000), (89727/100000)] := rfl
    funext i
    rw [ht]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [coarseGamma]
  rw [hγ] at P
  exact P

noncomputable def middle_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) (hHD : HDCut C)
    (hS : mismatch F.theta≤13/50)
    : ChargedBound C F (1/400) middleGamma := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.radius) rfl]
  intro C F hE hG hT hHD hS
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hhl : 1/2<C.tangent 0 := hHD.1
  have hdu : C.tangent 5< -1/2 := hHD.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.cuts =
        ![⟨(1/2),1⟩, ⟨(-4/5),(-1/20)⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨(1/20),(4/5)⟩, ⟨-1,(-1/2)⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.differenceRange =
        ![⟨(-13/50),(13/50)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-13/50),(13/50)⟩, ⟨(-13/50),(13/50)⟩, ⟨(-13/50),(13/50)⟩, ⟨(-13/50),(13/50)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    have hm : i∈charged → -(13/50:ℝ)≤delta F.theta i ∧ delta F.theta i≤13/50 :=
      fun hi => abs_le.mp ((delta_le_mismatch F.theta hi).trans hS)
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.charge i:ℝ)=charge (1/400) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.charge =
        ![(1/400), 0, (1/400), (1/400), (1/400), (1/400), 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.charged_bound C F (1/400) hb hcuts hdiff haxes
  have hγ : (fun i => (SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.target i:ℝ)) = middleGamma := by
    have ht : SquaresInCircles.Eight.Generated.Affine.Mismatch026To01Affine.table.target =
        ![(448791/500000), (448791/500000), (448791/500000), (448791/500000), (448791/500000), (448791/500000), (448791/500000)] := rfl
    funext i
    rw [ht]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [middleGamma]
  rw [hγ] at P
  exact P

noncomputable def intermediate_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) (hSigns : Signs C)
    (hS : mismatch F.theta≤1/10)
    : ChargedBound C F (1/200) intermediateGamma := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.radius) rfl]
  intro C F hE hG hT hSigns hS
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hhs : 0<C.tangent 0 := hSigns.1
  have hgs : C.tangent 1<0 := hSigns.2.1
  have has : 0<C.tangent 2 := hSigns.2.2.1
  have hbs : C.tangent 3<0 := hSigns.2.2.2.1
  have hts : 0<C.tangent 4 := hSigns.2.2.2.2.1
  have hds : C.tangent 5<0 := hSigns.2.2.2.2.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.cuts =
        ![⟨0,1⟩, ⟨(-4/5),(-1/20)⟩, ⟨0,1⟩, ⟨-1,0⟩, ⟨(1/20),(4/5)⟩, ⟨-1,0⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.differenceRange =
        ![⟨(-1/10),(1/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-1/10),(1/10)⟩, ⟨(-1/10),(1/10)⟩, ⟨(-1/10),(1/10)⟩, ⟨(-1/10),(1/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    have hm : i∈charged → -(1/10:ℝ)≤delta F.theta i ∧ delta F.theta i≤1/10 :=
      fun hi => abs_le.mp ((delta_le_mismatch F.theta hi).trans hS)
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.charge i:ℝ)=charge (1/200) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.charge =
        ![(1/200), 0, (1/200), (1/200), (1/200), (1/200), 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.charged_bound C F (1/200) hb hcuts hdiff haxes
  have hγ : (fun i => (SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.target i:ℝ)) = intermediateGamma := by
    have ht : SquaresInCircles.Eight.Generated.Affine.Mismatch01To015Affine.table.target =
        ![(1121991/1250000), (1121991/1250000), (1121991/1250000), (1121991/1250000), (1121991/1250000), (3590371/4000000), (8975917/10000000)] := rfl
    funext i
    rw [ht]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [intermediateGamma]
  rw [hγ] at P
  exact P

noncomputable def final_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) (hHD : HDCut C) (hSigns : Signs C)
    (hZero : ZeroOwners C) (hQuarter : QuarterOwners C)
    (hS : mismatch F.theta≤3/200)
    : ChargedBound C F (1/20) finalGamma := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.radius) rfl]
  intro C F hE hG hT hHD hSigns hZero hQuarter hS
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hhl : 1/2<C.tangent 0 := hHD.1
  have hdu : C.tangent 5< -1/2 := hHD.2
  have hhs : 0<C.tangent 0 := hSigns.1
  have hgs : C.tangent 1<0 := hSigns.2.1
  have has : 0<C.tangent 2 := hSigns.2.2.1
  have hbs : C.tangent 3<0 := hSigns.2.2.2.1
  have hts : 0<C.tangent 4 := hSigns.2.2.2.2.1
  have hds : C.tangent 5<0 := hSigns.2.2.2.2.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.cuts =
        ![⟨(1/2),1⟩, ⟨(-4/5),(-1/20)⟩, ⟨0,1⟩, ⟨-1,0⟩, ⟨(1/20),(4/5)⟩, ⟨-1,(-1/2)⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.differenceRange =
        ![⟨(-3/200),(3/200)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-3/200),(3/200)⟩, ⟨(-3/200),(3/200)⟩, ⟨(-3/200),(3/200)⟩, ⟨(-3/200),(3/200)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    have hm : i∈charged → -(3/200:ℝ)≤delta F.theta i ∧ delta F.theta i≤3/200 :=
      fun hi => abs_le.mp ((delta_le_mismatch F.theta hi).trans hS)
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · obtain ⟨hc1,hc2⟩ := hm (by decide)
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
    · refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.allowedAxes =
        ![[.one,.three], [.one,.two,.three,.four], [.one,.three], [.three,.four], [.one,.three], [.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j hj
    have hz : i∈zeroEdges → j∈zeroOwners := fun hi => hZero i hi j hj
    have hq : i∈otherQuarterEdges → j∈quarterOwners := fun hi => hQuarter i hi j hj
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases affineBudgets_fin4 j with rfl|rfl|rfl|rfl <;>
      first
      | decide
      | exact absurd (hz (by decide)) (by decide)
      | exact absurd (hq (by decide)) (by decide)
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.charge i:ℝ)=charge (1/20) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.charge =
        ![(1/20), 0, (1/20), (1/20), (1/20), (1/20), 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged]
  have P := SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.charged_bound C F (1/20) hb hcuts hdiff haxes
  have hγ : (fun i => (SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.target i:ℝ)) = finalGamma := by
    have ht : SquaresInCircles.Eight.Generated.Affine.Mismatch015To001Affine.table.target =
        ![(179519/200000), (179519/200000), (179519/200000), (179519/200000), (179519/200000), (179519/200000), (359037/400000)] := rfl
    funext i
    rw [ht]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [finalGamma]
  rw [hγ] at P
  exact P

noncomputable def enhanced_bound {C : BoundaryCycle Q1} (F : Frame C)
    (hE : EHalf C) (hG : GCut C) (hT : TCut C) :
    ChargedBound C F coarseBeta enhancedGamma := by
  revert C
  rw [← affineBudgets_radius (r := SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.radius) rfl]
  intro C F hE hG hT
  have he : C.tangent 6≤0 := hE
  have hgl : -4/5<C.tangent 1 := hG.1
  have hgu : C.tangent 1< -1/20 := hG.2
  have htl : 1/20<C.tangent 4 := hT.1
  have htu : C.tangent 4<4/5 := hT.2
  have hcuts : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.cuts i).Mem (C.tangent i) := by
    have hc : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.cuts =
        ![⟨-1,1⟩, ⟨(-4/5),(-1/20)⟩, ⟨-1,1⟩, ⟨-1,1⟩, ⟨(1/20),(4/5)⟩, ⟨-1,1⟩, ⟨-1,0⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := C.tangent_mem i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have hdiff : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.differenceRange i).Mem (delta F.theta i) := by
    have hd : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.differenceRange =
        ![⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩, ⟨(-7/10),(7/10)⟩] := rfl
    intro i
    obtain ⟨hb1,hb2⟩ := abs_le.mp (F.delta_small i).le
    rw [hd]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      refine ⟨?_,?_⟩ <;> norm_num <;> linarith
  have haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.allowedAxes i := by
    have ha : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.allowedAxes =
        ![[.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four], [.one,.two,.three,.four]] := rfl
    intro i j _
    rw [ha]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact affineBudgets_all_axes _
  have hb : ∀ i, (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.charge i:ℝ)=charge (coarseBeta) i := by
    have hc : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.charge =
        ![(99/5000), 0, (99/5000), (99/5000), (99/5000), (99/5000), 0] := rfl
    intro i
    rw [hc]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [charge,charged,coarseBeta]
  have P := SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.enhanced_charged_bound C F coarseBeta hb hcuts hdiff haxes
  have hγ : (fun i => (SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.enhancedMeta.target i:ℝ)) = enhancedGamma := by
    have ht : SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.target =
        ![(89727/100000), (89727/100000), (89727/100000), (89727/100000), (89727/100000), (89727/100000), (89727/100000)] := rfl
    funext i
    show ((SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.table.target i+SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.enhancement i : ℚ) : ℝ) = enhancedGamma i
    rw [ht]
    rcases affineBudgets_fin7 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [SquaresInCircles.Eight.Generated.Affine.CandidateCoarseMismatch.enhancement,enhancedGamma,coarseGamma,retainedReserve]
  rw [hγ] at P
  exact P

end SquaresInCircles.Eight.Candidate.Tables
