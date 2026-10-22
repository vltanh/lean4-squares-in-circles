module

public import SquaresInCircles.Eight.TableFree.GlobalGATargetCycle

/-!
# The high-GA target cut on the unchanged source boundary representative

The literal hand theorem is first proved at Q0 in `GlobalGATargetCycle`.
This final adapter uses the established auxiliary radius expansion:
every original weak axis and its index are retained, as are the tangent
ratio and the common frame. A positive signed coordinate can only grow
under that expansion, so the fixed-circle cut implies the source cut.
Uncompiled source draft; no extra restriction is placed on A or T.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Target
open Candidate

theorem frame_target_small {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) (hE : C.tangent E≤0)
    (j : Fin 4) (hhigh : j=2 ∨ j=3)
    (hGA : (forwardAxis j).Feasible (C.square G) (C.square A)) :
    ((SignedCycle.atFrame F).point A).y<1/2 := by
  let D := FramePhysicalTransport.auxiliary C hq
  have hR : RadiusExpansion C D := FramePhysicalTransport.auxiliary_expansion C hq
  let F' : Candidate.Frame D := FramePhysicalTransport.candidatePushforward F hR le_rfl
  have hE' : D.tangent E≤0 := by rw [hR.same_tangents]; exact hE
  have hGA' : (forwardAxis j).Feasible (D.square G) (D.square A) := by
    have hh := hR.preserves_all_axes G (forwardAxis j) (by simpa [G,A,next] using hGA)
    simpa [G,A,next] using hh
  have hcut := fixed_frame_target_small F' hE' j hhigh hGA'
  have hfactor : 1≤C.expansionFactor Q0 A := C.expansionFactor_ge_one
    ⟨hq.1,hq.2.trans (by norm_num [Q0])⟩ (by norm_num [Q0]) hq.2 A
  have hy : ((SignedCycle.atFrame F').point A).y=
      C.expansionFactor Q0 A*((SignedCycle.atFrame F).point A).y := by
    dsimp [SignedCycle.atFrame,D,FramePhysicalTransport.auxiliary,BoundaryCycle.expand]
    ring
  by_contra! hlarge
  have hm := mul_le_mul_of_nonneg_right hfactor
    (show 0≤((SignedCycle.atFrame F).point A).y by linarith)
  rw [hy] at hcut
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.Target
