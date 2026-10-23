module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Concentration

/-!
# The intrinsic scalar alternatives forced by the original witnesses

Uncompiled transcription of the last paragraph of Section 3 of the
negative-flat-A / TD2 angle companion. The weight ranges and pair domains
are discharged for the prescribed family. This is the actual original
cycle's necessary inequality, before Sections 4--10 compare its intrinsic
alternatives with the fourteen scalar endpoints.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open Certificate (Family)

def intrinsic (atG : Bool) (k l c s z : ℝ) (i j : Fin 4) : ℝ :=
  baseline atG k l c s z+
    min (Concentration.pure R (diagonal-1/2)
      (pWeights atG k l (PositiveTD.tilted c z) s)
      (qWeights atG k l (PositiveTD.tilted c z) s) 3 i j s z)
      (Concentration.saturated R (diagonal-1/2)
        (pWeights atG k l (PositiveTD.tilted c z) s)
        (qWeights atG k l (PositiveTD.tilted c z) s) 3 i j s z)

theorem original_intrinsic_nonpositive {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Family) (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : aError C atG=-s)
    (hflat : (C.point A).a=7/12)
    (hz : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hhg : hg=0 ∨ hg=2)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) :
    ∃i j,intrinsic atG (Explicit.k f (delta C.theta T))
      (Explicit.l f (delta C.theta T)) (Explicit.c f (delta C.theta T))
      s (delta C.theta T) i j≤0 := by
  let k := Explicit.k f (delta C.theta T)
  let l := Explicit.l f (delta C.theta T)
  let c := Explicit.c f (delta C.theta T)
  have hsf := (Explicit.angle_domain atG hs).2
  have hzf := Explicit.family_frame_domain f hz
  obtain ⟨hk,hG,hB,hc,hm⟩ := Explicit.family_coefficient_domain f atG hz hs
  have hpos := Explicit.family_positive f hz
  have hcoeff := Explicit.ordered_pair_domain f atG hz hs
  have hb := original_budgets hg atG k l c hsf.1 ha hvar hzf.1
  have hlo := original_stress_lower atG hsorted hcontained hq hHy hGy hBy hDy
    hvar hsf ha hflat hzf.1 hhg hk hG hB hc hm
  have hhi := stress_nonpositive atG hpos.1.le hpos.2.1.le hpos.2.2.1 hsf hzf
    hHG hGA hAB hBT hTD hDE hEH
  obtain ⟨i,j,hmin⟩ := Concentration.concentrate R (diagonal-1/2)
    (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
    (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
    (fun i => (blocks C hg atG k l c s i).P)
    (fun i => (blocks C hg atG k l c s i).N) 3
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hcoeff i).1) (fun i => (hcoeff i).2.1) (fun i => (hcoeff i).2.2)
    (fun i => (blocks C hg atG k l c s i).P_nonneg)
    (fun i => (blocks C hg atG k l c s i).N_nonneg)
    hsf hzf hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  refine ⟨i,j,?_⟩
  change intrinsic atG k l c s (delta C.theta T) i j≤0
  dsimp [intrinsic]
  dsimp [k,l,c,Explicit.m] at hmin hlo hhi ⊢
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Source
