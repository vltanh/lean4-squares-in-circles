module

public import SquaresInCircles.Eight.TableFree.SourceEquality
public import SquaresInCircles.Eight.RadiusTransfer
public import SquaresInCircles.Eight.ExactFamily.Stationary

/-!
# Actual original-owner pruning on a stationary boundary source

Uncompiled source draft of Section 5 of
HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md.

The scalar comparisons in SourceEquality are applied here to actual
BoundaryCycle squares and actual weak forward-axis witnesses. The G primary
coordinate is bounded using this same source's true-core avoidance. No outer
radius is assigned to G and no comparison slider is substituted for G.

The stationary coefficient bounds below reuse the existing stationary-data
theorems. No candidate owner/affine table is used in these proofs. The
geometric source-entry theorem supplying the stationary anchors remains the
separate obligation documented in SharpEntry.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open ExactFamily Coordinates

theorem coordinate_half_angle_identities (d : Coordinates) :
    1-d.c=d.s*d.z ∧ (1+d.c)*d.z=d.s := by
  constructor <;>
    dsimp [Coordinates.c,Coordinates.s,halfAngleCos,halfAngleSin] <;>
    field_simp [ne_of_gt (halfAngle_den_pos d.z)] <;> ring

theorem sharp_ga_comparison_bounds :
    -sharpData.y-1/2<11/25 ∧
      (sharpData.x₁-1/2)+(sharpData.h₁+3/2)<71/50 ∧
      0≤(sharpData.x₁-1/2)+(sharpData.h₁+3/2) ∧
      0≤ sharpData.z ∧ sharpData.z<13/200 := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,
    hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hy := sharp_y
  have hz0 := sharpData_stationary.z_pos.le
  have hcz : (1+sharpData.c)*sharpData.z=sharpData.s :=
    (coordinate_half_angle_identities sharpData).2
  have hc99 : (99/100 : ℝ) ≤ sharpData.c := by linarith
  have hs8 : sharpData.s ≤ 1/8 := by linarith
  have hzu : sharpData.z<13/200 := by
    by_contra! h
    have hp := mul_nonneg (sub_nonneg.mpr hc99) (sub_nonneg.mpr h)
    nlinarith
  exact ⟨by linarith,by linarith,by linarith,hz0,hzu⟩

theorem stationary_ga1_not_feasible {q : ℝ} (C : BoundaryCycle q)
    (hf : StationaryFrames sharpData C.square)
    (hA : (C.square 2).center=sharpData.pA)
    (hH : (C.square 0).center=sharpData.pH)
    (hHG : dot sharpData.e (sub (C.square 1).center (C.square 0).center)=1) :
    ¬ (forwardAxis 1).Feasible (C.square 1) (C.square 2) := by
  have hGc : (C.square 1).cosine=sharpData.s := by
    simpa [canonicalCos] using (hf 1).1
  have hGs : (C.square 1).sine= -sharpData.c := by
    simpa [canonicalSin] using (hf 1).2
  have hAc : (C.square 2).cosine=1 := by
    simpa [canonicalCos] using (hf 2).1
  have hAs : (C.square 2).sine=0 := by
    simpa [canonicalSin] using (hf 2).2
  have hGe : dot sharpData.e (C.square 1).center=sharpData.h₁+3/2 := by
    have h := hHG
    rw [dot_sub_right,hH,Coordinates.pH,sharpData.dot_e_inFrame] at h
    linarith
  have hGf : dot sharpData.f (C.square 1).center= -C.a 1 := by
    rw [C.center_eq 1]
    dsimp [dot,Coordinates.f,rotate]
    rw [hGc,hGs]
    linear_combination -(C.a 1)*sharpData.unit
  have hGx : (C.square 1).center.1 =
      (C.a 1)*sharpData.s+(sharpData.h₁+3/2)*sharpData.c := by
    have h := congrArg Prod.fst
      (OriginalDual.frame_reconstruction sharpData (C.square 1).center)
    change sharpData.c*dot sharpData.e (C.square 1).center -
      sharpData.s*dot sharpData.f (C.square 1).center =
        (C.square 1).center.1 at h
    rw [hGe,hGf] at h
    nlinarith
  have hsorted :
      beta (C.square 1) (0,0) ≤ alpha (C.square 1) (0,0) := by
    rw [(C.absolute_coordinates 1).1,(C.absolute_coordinates 1).2]
    exact C.b_le_a 1
  have haG := original_core_primary_reserve (C.core 1) hsorted
  rw [(C.absolute_coordinates 1).1] at haG
  obtain ⟨hbA,hAupper,hApositive,hκ0,hκ⟩ := sharp_ga_comparison_bounds
  have hcontact :
      (sharpData.x₁-1/2)*sharpData.c -
        (-sharpData.y-1/2)*sharpData.s-(sharpData.h₁+3/2) =
        (1+sharpData.c+sharpData.s)/2 := by
    dsimp [Coordinates.h₁]
    ring
  have hless := ga1_strictly_unavailable
    sharpData_stationary.weightDomain.s_pos
    (coordinate_half_angle_identities sharpData).1
    haG hbA hAupper hApositive hκ hκ0 hcontact
  have hprojection :
      (forwardAxis 1).projection (C.square 1) (C.square 2) =
        (sharpData.x₁-1/2)-(C.a 1)*sharpData.s -
          (sharpData.h₁+3/2)*sharpData.c := by
    simp [SignedAxis.projection,SignedAxis.normal,AxisOwner.normal,AxisSign.value,
      forwardAxis,scale,Eight.e,dot,sub,hA,hAc,hAs,hGx,Coordinates.pA]
    ring
  have hthreshold :
      SAT.threshold (C.square 1) (C.square 2) =
        (1+sharpData.c+sharpData.s)/2 := by
    simpa [stationaryWidth,next] using
      threshold_of_stationary_frames sharpData_stationary.weightDomain hf (1 : Vertex)
  intro hfeasible
  change SAT.threshold (C.square 1) (C.square 2) ≤
    (forwardAxis 1).projection (C.square 1) (C.square 2) at hfeasible
  rw [hthreshold,hprojection] at hfeasible
  exact (not_le_of_gt hless) hfeasible

theorem stationary_eh0_not_feasible {q : ℝ} (C : BoundaryCycle q)
    (hf : StationaryFrames sharpData C.square)
    (hE : (C.square 6).center=sharpData.pE)
    (hH : (C.square 0).center=sharpData.pH) :
    ¬ (forwardAxis 0).Feasible (C.square 6) (C.square 0) := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,
    hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hEc : (C.square 6).cosine= -1 := by
    simpa [canonicalCos] using (hf 6).1
  have hEs : (C.square 6).sine=0 := by
    simpa [canonicalSin] using (hf 6).2
  have hgap : -sharpData.h₁-1/2 < -sharpData.x₄-1/2 := by
    linarith
  have hpositive :
      0≤(-sharpData.h₂-1/2)+(-sharpData.y₄-1/2) := by
    dsimp [Coordinates.y₄]
    linarith
  have hcontact :
      (-sharpData.h₂-1/2)+(-sharpData.x₄-1/2)*sharpData.s -
        (-sharpData.y₄-1/2)*sharpData.c =
        (1+sharpData.c+sharpData.s)/2 := by
    dsimp [Coordinates.h₂]
    ring
  have hless := eh0_strictly_unavailable
    sharpData_stationary.weightDomain.s_pos
    (halfAngleCos_le_one sharpData.z) hgap hpositive hcontact
  have hprojection :
      (forwardAxis 0).projection (C.square 6) (C.square 0) =
        (-sharpData.h₂-1/2)*sharpData.c +
          (-sharpData.h₁-1/2)*sharpData.s-(-sharpData.y₄-1/2) := by
    simp [SignedAxis.projection,SignedAxis.normal,AxisOwner.normal,AxisSign.value,
      forwardAxis,scale,Eight.f,dot,sub,hE,hH,hEc,hEs,
      Coordinates.pE,Coordinates.pH,Coordinates.inFrame]
    ring
  have hthreshold :
      SAT.threshold (C.square 6) (C.square 0) =
        (1+sharpData.c+sharpData.s)/2 := by
    simpa [stationaryWidth,next] using
      threshold_of_stationary_frames sharpData_stationary.weightDomain hf (6 : Vertex)
  intro hfeasible
  change SAT.threshold (C.square 6) (C.square 0) ≤
    (forwardAxis 0).projection (C.square 6) (C.square 0) at hfeasible
  rw [hthreshold,hprojection] at hfeasible
  exact (not_le_of_gt hless) hfeasible

/-- The actual global pre-entry owner sets, including both mixed choices. -/
def sourceOwners : Vertex → Finset (Fin 4) :=
  ![{0,2},{0,1},{0,2},{2,3},{0,2},{2,3},{0,1}]

/-- Original hard-source equality removes the two nonstationary mixed
witnesses from every feasible owner, including initially chosen weak ties. -/
theorem terminal_owners_after_source_equality {q : ℝ} (C : BoundaryCycle q)
    (hf : StationaryFrames sharpData C.square)
    (hA : (C.square 2).center=sharpData.pA)
    (hH : (C.square 0).center=sharpData.pH)
    (hE : (C.square 6).center=sharpData.pE)
    (hHG : dot sharpData.e (sub (C.square 1).center (C.square 0).center)=1)
    (ho : Candidate.OwnerRestriction C sourceOwners) :
    Candidate.OwnerRestriction C Candidate.terminalOwners := by
  have hGA := stationary_ga1_not_feasible C hf hA hH hHG
  have hEH := stationary_eh0_not_feasible C hf hE hH
  intro i j hfeasible
  have hj := ho i j hfeasible
  fin_cases i <;> fin_cases j <;>
    simp_all [sourceOwners,Candidate.terminalOwners,next]

theorem selected_normals_after_source_equality {q : ℝ} (C : BoundaryCycle q)
    (F : Candidate.Frame C) (hf : StationaryFrames sharpData C.square)
    (hA : (C.square 2).center=sharpData.pA)
    (hH : (C.square 0).center=sharpData.pH)
    (hE : (C.square 6).center=sharpData.pE)
    (hHG : dot sharpData.e (sub (C.square 1).center (C.square 0).center)=1)
    (ho : Candidate.OwnerRestriction C sourceOwners) :
    ∀ i, (C.selected i).normal (C.square i) (C.square (next i)) =
      stationaryNormal sharpData i := by
  have ht := terminal_owners_after_source_equality C hf hA hH hE hHG ho
  intro i
  obtain ⟨j,hj⟩ := F.forward_complete i (C.selected i) (C.feasible i)
  have hfeasible :
      (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [← hj] using C.feasible i
  rw [hj]
  exact terminal_owner_normal hf i j (ht i j hfeasible)

end SquaresInCircles.Eight.TableFree
