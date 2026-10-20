module

public import SquaresInCircles.Eight.Candidate.DualApplication
public import SquaresInCircles.Eight.Candidate.FramePullback
public import SquaresInCircles.Eight.Generated.AffineBudgets

/-!
# Complete candidate capture and the radius pullback

The affine tables are applied at Q1. All conclusions concerning the real
frame lifts, signed tangents, and initially feasible owners pull back to the
pre-expansion boundary cycle. The positive-error terminal is then evaluated
at that cycle's actual radius.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Candidate

structure Captured {q : ℝ} (C : BoundaryCycle q) (F : Frame C) where
  cuts : TangentCuts C
  mismatch_lt : mismatch F.theta < 1/1000
  zero_owners : ZeroOwners C
  quarter_owners : QuarterOwners C
  owners : OwnerRestriction C terminalOwners
  z : ℝ
  z_lower : 1001/20000 < z
  z_upper : z < 2/25
  tilt_eq : tilt F.theta=2*Real.arctan z
  tilt_lower : 1/10 < tilt F.theta
  tilt_upper : tilt F.theta < 4/25

def capture {C : BoundaryCycle Q1} (F : Frame C) (hE : EHalf C) : Captured C F := by
  have hG := Tables.g_cut F hE
  have hT := Tables.t_cut F hE hG
  let Pcoarse := Tables.coarse_bound F hE hG hT
  have hS04 := coarse_first_contraction Pcoarse
  let Pplus := Tables.enhanced_bound F hE hG hT
  have hS026 := coarse_enhanced_contraction Pcoarse Pplus
  have hHD := Tables.hd_cut F hE hG hT
  let Pmiddle := Tables.middle_bound F hE hG hT hHD hS026.le
  have hS01 := contraction_026_to_01 Pmiddle hS026.le
  have hSigns := signs_of_mismatch F (by norm_num [Q1,Q0]) hS01.le
  let Pintermediate := Tables.intermediate_bound F hE hG hT hSigns hS01.le
  have hS015 := contraction_01_to_015 Pintermediate hS01.le
  have hZero := zero_owners_of_mismatch F (by norm_num [Q1,Q0]) hS04.le
  let hc : TangentCuts C := ⟨hSigns,hE,hG,hT,hHD⟩
  have hQuarter := quarter_owners F (by norm_num [Q1,Q0]) hc hZero hS015.le
  let Pfinal := Tables.final_bound F hE hG hT hHD hSigns hZero hQuarter hS015.le
  have hS001 := contraction_015_to_001 Pfinal hS015.le
  have hOwners := mixed_owners F (by norm_num [Q1,Q0]) hc hZero hQuarter hS001.le
  obtain ⟨z,hzl,hzu,ht,htl,htu⟩ := tilt_window F le_rfl hc hOwners hS001.le
  exact ⟨hc,hS001,hZero,hQuarter,hOwners,z,hzl,hzu,ht,htl,htu⟩

def Captured.pullback {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    {F : Frame D} (K : Captured D F) (hR : RadiusExpansion C D) :
    Captured C (F.pullback hR) where
  cuts := by
    rcases K.cuts with ⟨hs,hE,hG,hT,hHD⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [Signs,← hR.same_tangents] using hs
    · simpa [EHalf,← hR.same_tangents] using hE
    · simpa [GCut,← hR.same_tangents] using hG
    · simpa [TCut,← hR.same_tangents] using hT
    · simpa [HDCut,← hR.same_tangents] using hHD
  mismatch_lt := K.mismatch_lt
  zero_owners i hi j hj := K.zero_owners i hi j (hR.preserves_all_axes i (forwardAxis j) hj)
  quarter_owners i hi j hj := K.quarter_owners i hi j (hR.preserves_all_axes i (forwardAxis j) hj)
  owners i j hj := K.owners i j (hR.preserves_all_axes i (forwardAxis j) hj)
  z := K.z
  z_lower := K.z_lower
  z_upper := K.z_upper
  tilt_eq := K.tilt_eq
  tilt_lower := K.tilt_lower
  tilt_upper := K.tilt_upper

end SquaresInCircles.Eight.Candidate
