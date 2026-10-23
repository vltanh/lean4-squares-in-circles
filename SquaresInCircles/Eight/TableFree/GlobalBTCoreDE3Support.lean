module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Base
public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Concentration
public import SquaresInCircles.Eight.TableFree.GlobalBTDE2Support

/-!
# The original core endpoint and both retained prefix circles

The core marker pays its exact DE3 endpoint term.  The remaining
original T and D support forces give the concentrated scalar for
either original TD owner, with no sign restriction on the forces.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem core_marker_identity (e : State) (he : e.branch.type=0) :
    ZeroPrimary.unsigned e=(7506931/1000000)*(7/12-e.a)+m*e.b := by
  cases hbranch : e.branch <;> simp [hbranch,Branch.type] at he
  all_goals simp [ZeroPrimary.unsigned,hbranch,FramePair.label,m]

theorem core_endpoint_marker (e : State) (he : e.branch.type=0) {t : ℝ}
    (ht : t∈Icc 0 frameCap) :
    endpointWeight t*(7/12)*Real.sin t≤ZeroPrimary.unsigned e+
      endpointWeight t*e.a*Real.sin t-endpointWeight t*e.b*Real.cos t := by
  have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart e he)).2.1
  have hweights := endpointWeight_bounds ht
  have hfirst := mul_nonneg (sub_nonneg.mpr hweights.2.2.2)
    (show 0≤7/12-e.a by linarith)
  have hlast := mul_nonneg (sub_nonneg.mpr hweights.2.2.1) e.b_nonneg
  rw [core_marker_identity e he]
  nlinarith only [hfirst,hlast]

def reduced (b t d e : State) (second : Bool) (c eWeight r s u : ℝ) : ℝ :=
  Real.pi+kappa*(1+transverse b)+quarterDual b t 0 (-r) kappa+
    zeroDual second t d (-s) c+quarterDual d e 3 (-u) eWeight+ZeroPrimary.unsigned e

theorem support (b t d e : State) (second : Bool) {c r s u : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hcore : e.branch.type=0)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) :
    tail second (endpointWeight u) c r s u≤
      reduced b t d e second c (endpointWeight u) r s u := by
  have hty := transverse_of_nonneg t ht
  have hdy := transverse_nonpos_eq d hd
  have hey := transverse_nonpos_eq e he
  have hmarker := core_endpoint_marker e hcore hu
  cases second with
  | false =>
      have hT := mixed_state_support t kappa c r 0
      have hD := mixed_state_support d (endpointWeight u) c 0 s
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hT hD
      dsimp [tail,reduced,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hr,width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg]
      nlinarith only [hT,hD,hmarker]
  | true =>
      have hT := mixed_state_support t kappa c r s
      have hD := mixed_state_support d (endpointWeight u) c 0 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hD
      dsimp [tail,reduced,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hr,width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg]
      nlinarith only [hT,hD,hmarker]

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
