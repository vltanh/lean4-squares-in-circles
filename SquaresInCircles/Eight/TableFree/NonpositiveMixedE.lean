module

public import SquaresInCircles.Eight.TableFree.NonpositiveEndpointBarrier

/-!
# Original mixed E witnesses for the nonpositive composite class

Uncompiled draft.  The original mixed owners exclude a core E at every
frame in the real-frame window.  The .27 shared-chain bound supplies
the strict gap.  For E between D and H, its surviving radial alternative
and sorting upgrade either retained owner to the physical DE3/EH1 axes
at the same original point.  All owner ties remain allowed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace AlignedMixedE

theorem sine_pair_bound_wide {u v : ℝ} (hs : u+v∈Icc 0 (27/100 : ℝ)) :
    Real.sin u+Real.sin v≤2*Real.sin ((u+v)/2) := by
  have hw : (u+v)/2∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hsin := (transport_trig hw).2.2.1
  have hmul := mul_le_mul_of_nonneg_left (Real.cos_le_one ((u-v)/2)) hsin
  have hid : Real.sin u+Real.sin v=
      2*Real.sin ((u+v)/2)*Real.cos ((u-v)/2) := by
    calc
      Real.sin u+Real.sin v=
          Real.sin ((u+v)/2+(u-v)/2)+Real.sin ((u+v)/2-(u-v)/2) := by
        congr 1 <;> congr 1 <;> ring
      _=2*Real.sin ((u+v)/2)*Real.cos ((u-v)/2) := by
        rw [Real.sin_add,Real.sin_sub]
        ring
  rw [hid]
  linarith

theorem short_primary_gap_wide {s : ℝ} (hs : s∈Icc 0 (27/100 : ℝ)) :
    1248/625-(359/500)*Real.sin s<2-Real.sin (s/2) := by
  have hw : s/2∈Icc 0 (7/10 : ℝ) := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hsin := (transport_trig hw).2.2.1
  have hhalf : (s/2)^2≤(27/200 : ℝ)^2 :=
    pow_le_pow_left₀ hw.1 (by linarith [hs.2]) 2
  have hcos : 99/100<Real.cos (s/2) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := s/2)]
  have hprod := mul_nonneg hsin (show 0≤(359/250)*Real.cos (s/2)-1 by linarith)
  have hdouble := Real.sin_two_mul (s/2)
  rw [show 2*(s/2)=s by ring] at hdouble
  nlinarith

theorem core_impossible_wide {H D E : SignedPoint} {u v : ℝ}
    (hHa : 1/2≤H.a) (hDa : 1/2≤D.a)
    (hHy : H.y∈Icc (0:ℝ) 1) (hDy : -D.y∈Icc (0:ℝ) 1)
    (hEa : E.a∈Icc (1/2 : ℝ) (7/12))
    (hEy : E.y∈Icc (-(7/12) : ℝ) 0)
    (hu : |u|≤7/10) (hv : |v|≤7/10)
    (hs : u+v∈Icc 0 (27/100 : ℝ))
    (hsum : H.a+D.a<1248/625-(359/500)*Real.sin (u+v))
    (hDE : quarterFeasible D E u 2 ∨ quarterFeasible D E u 3)
    (hEH : quarterFeasible E H v 0 ∨ quarterFeasible E H v 1) : False := by
  have hpair := core_pair hHa hDa hHy hDy hEa hEy hu hv hDE hEH
  have hsines := sine_pair_bound_wide hs
  have hgap := short_primary_gap_wide hs
  linarith

end AlignedMixedE

namespace SignedCycle
open Candidate AlignedMixedE

private theorem r60_feasible_quarter {C : SignedCycle} {i : Vertex} (hw : Candidate.word i≠0)
    (j : Fin 4) : C.Feasible i j ↔
      quarterFeasible (C.point i) (C.point (next i)) (C.theta (next i)-C.theta i) j := by
  simp only [Feasible,slack,edge,hw,↓reduceIte,quarterFeasible,delta,sub_nonneg]

/-- E's original frame is arbitrary here.  Both original mixed-owner
choices supply the same necessary primary sum before the actual radial
alternative is used. -/
theorem HardInput.nonpositive_E_radial {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    7/12<(I.cycle.point E).a ∧
      max |(I.cycle.point H).y| |(I.cycle.point D).y|≤(I.cycle.point E).a := by
  have hb := I.nonpositive_composite_bounds hq hAB hAG hGH hDT hTB hHG hTD
  have hnot : ¬(I.cycle.point E).a≤7/12 := by
    intro hcore
    have hEhalf := SignedPoint.primary_gt_half (I.necessary.sorted E) (I.necessary.core E)
    have hEminor : -(7/12 : ℝ)≤(I.cycle.point E).y := by
      have hh := (abs_le.mp (I.necessary.sorted E).2).1
      linarith
    have hDowner : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
      simpa [normalOwners,D] using I.witnesses.allowed D
    have hEowner : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [normalOwners,E] using I.witnesses.allowed E
    have hDE : quarterFeasible (I.cycle.point D) (I.cycle.point E)
        (I.cycle.theta E-I.cycle.theta D) 2 ∨
        quarterFeasible (I.cycle.point D) (I.cycle.point E)
        (I.cycle.theta E-I.cycle.theta D) 3 := by
      rcases hDowner with hj | hj
      · left
        have h := (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) _).1
          (I.witnesses.feasible D)
        rwa [show next D=E by decide,hj] at h
      · right
        have h := (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) _).1
          (I.witnesses.feasible D)
        rwa [show next D=E by decide,hj] at h
    have hEH : quarterFeasible (I.cycle.point E) (I.cycle.point H)
        (I.cycle.theta H-I.cycle.theta E) 0 ∨
        quarterFeasible (I.cycle.point E) (I.cycle.point H)
        (I.cycle.theta H-I.cycle.theta E) 1 := by
      rcases hEowner with hj | hj
      · left
        have h := (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) _).1
          (I.witnesses.feasible E)
        rwa [show next E=H by decide,hj] at h
      · right
        have h := (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) _).1
          (I.witnesses.feasible E)
        rwa [show next E=H by decide,hj] at h
    have heq : I.cycle.theta E-I.cycle.theta D+
        (I.cycle.theta H-I.cycle.theta E)=I.cycle.theta H-I.cycle.theta D := by ring
    apply core_impossible_wide hb.H_primary.1.le hb.D_primary.1.le
      ⟨I.anchors_normal.H_nonneg,by linarith [hb.H_tangent.2]⟩
      ⟨by linarith [I.anchors_normal.D_nonpos],by linarith [hb.D_tangent.2]⟩
      ⟨hEhalf.le,hcore⟩ ⟨hEminor,I.E_nonpos⟩
      (I.necessary.spread E D) (I.necessary.spread H E)
      (by rw [heq]; exact ⟨hb.span_nonneg,hb.span_lt.le⟩)
      (by rw [heq]; exact hb.primary_sum) hDE hEH
  exact ⟨lt_of_not_ge hnot,I.E_radial.resolve_left hnot⟩

theorem HardInput.nonpositive_primary_E_witnesses {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) :
    I.cycle.Feasible D 3 ∧ I.cycle.Feasible E 1 := by
  have hrad := (I.nonpositive_E_radial hq hAB hAG hGH hDT hTB hHG hTD).2
  have hDrad : -(I.cycle.point D).y≤(I.cycle.point E).a := by
    have hh := (le_max_right |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonpos I.anchors_normal.D_nonpos] using hh
  have hHrad : (I.cycle.point H).y≤(I.cycle.point E).a := by
    have hh := (le_max_left |(I.cycle.point H).y| |(I.cycle.point D).y|).trans hrad
    simpa [abs_of_nonneg I.anchors_normal.H_nonneg] using hh
  have hu : I.cycle.theta E-I.cycle.theta D∈Icc 0 (7/10 : ℝ) :=
    ⟨sub_nonneg.mpr hDEorder,(le_abs_self _).trans (I.necessary.spread E D)⟩
  have hv : I.cycle.theta H-I.cycle.theta E∈Icc 0 (7/10 : ℝ) :=
    ⟨sub_nonneg.mpr hEHorder,(le_abs_self _).trans (I.necessary.spread H E)⟩
  constructor
  · have hj : I.witnesses.owner D=2 ∨ I.witnesses.owner D=3 := by
      simpa [normalOwners,D] using I.witnesses.allowed D
    rcases hj with hj | hj
    · have hsource : quarterFeasible (I.cycle.point D) (I.cycle.point E)
          (I.cycle.theta E-I.cycle.theta D) 2 := by
        have h := (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) _).1
          (I.witnesses.feasible D)
        rwa [show next D=E by decide,hj] at h
      have hh := DE_primary_of_nonneg (I.necessary.sorted D) (I.necessary.sorted E)
        I.anchors_normal.D_nonpos I.E_nonpos hDrad hu hsource
      exact (r60_feasible_quarter (C := I.cycle) (i := D) (by decide) 3).2
        (by rw [show next D=E by decide]; exact hh)
    · simpa [hj] using I.witnesses.feasible D
  · have hj : I.witnesses.owner E=0 ∨ I.witnesses.owner E=1 := by
      simpa [normalOwners,E] using I.witnesses.allowed E
    rcases hj with hj | hj
    · have hsource : quarterFeasible (I.cycle.point E) (I.cycle.point H)
          (I.cycle.theta H-I.cycle.theta E) 0 := by
        have h := (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) _).1
          (I.witnesses.feasible E)
        rwa [show next E=H by decide,hj] at h
      have hh := EH_primary_of_nonneg (I.necessary.sorted H).1.le
        I.E_nonpos hHrad hv hsource
      exact (r60_feasible_quarter (C := I.cycle) (i := E) (by decide) 1).2
        (by rw [show next E=H by decide]; exact hh)
    · simpa [hj] using I.witnesses.feasible E

/-- All retained original E owners now invoke the actual E-only
reduction.  The source non-E coordinates and circle ledger are unchanged. -/
theorem HardInput.reduce_nonpositive_all_mixed_E {q : ℝ} (I : HardInput q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hDEorder : I.cycle.theta D≤I.cycle.theta E)
    (hEHorder : I.cycle.theta E≤I.cycle.theta H) :
    ∃J : HardInput q,
      (∀i, i≠E → J.cycle.point i=I.cycle.point i ∧ J.cycle.theta i=I.cycle.theta i) ∧
      J.cycle.theta E∈Icc (I.cycle.theta D) (I.cycle.theta H) ∧
      ((J.cycle.point E).y=0 ∨ J.cycle.theta E=I.cycle.theta D ∨
        J.cycle.theta E=I.cycle.theta H) ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (((I.cycle.point E).y<0 ∧ I.cycle.theta D<I.cycle.theta E ∧
        I.cycle.theta E<I.cycle.theta H) → StrictAnchorLoss I.cycle J.cycle) ∧
      J.cycle.Feasible D 3 ∧ J.cycle.Feasible E 1 := by
  have hE := I.nonpositive_primary_E_witnesses hq hAB hAG hGH hDT hTB hHG hTD hDEorder hEHorder
  exact I.reduce_nonpositive_E hq hAB hAG hGH hDT hTB hHG hTD hDEorder hEHorder hE.1 hE.2

end SignedCycle
end SquaresInCircles.Eight.TableFree
