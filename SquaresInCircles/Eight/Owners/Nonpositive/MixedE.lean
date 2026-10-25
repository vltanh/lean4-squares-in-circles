module

public import SquaresInCircles.Eight.Owners.Nonpositive.ChainBounds

/-!
# Eight squares: the mixed witnesses of E for nonpositive composites

The mixed owners exclude a core E at every frame of the window (`core_impossible_wide`), the
shared-chain bound `27/100` giving the strict gap (`short_primary_gap_wide`). So E is outer and
dominates H and D radially (`HardInput.nonpositive_E_radial`); for E between D and H, this and
sorting upgrade either owner to the primary axes DE3 and EH1 at the same point. Ties between owners
are allowed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
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

/-- For any frame of E, `7/12 < E.a` and `max |H.y| |D.y| ≤ E.a`: both choices of mixed owners give
the same necessary primary sum before the radial alternative is used. -/
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

end SignedCycle
end SquaresInCircles.Eight
