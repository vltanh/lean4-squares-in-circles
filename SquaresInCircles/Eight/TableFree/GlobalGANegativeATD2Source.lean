module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2LowSaturated
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2HighSource

/-!
# The complete original negative-flat-A / nonnegative-TD2 exclusion

Uncompiled transcription of the scalar and angle companions. The two
prescribed coefficient families cover the whole original TD interval.
All concentration endpoints are paid internally. A positive original
stress is exposed independently of the original separator witnesses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open Certificate (Family)

theorem family_intrinsic_positive (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (i j : Fin 4) :
    0< intrinsic atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z i j := by
  cases f
  · have hz' : z∈Icc 0 (1/5:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split] at hz
      exact hz
    exact LowSaturated.intrinsic_positive atG hz' hs i j
  · have hz' : z∈Icc (1/5:ℝ) (7/10:ℝ) := by
      norm_num [Certificate.left,Certificate.right,Certificate.split,
        PositiveTD.Certificate.h] at hz
      exact hz
    exact HighSource.intrinsic_positive atG hz' hs i j

theorem family_stress_positive {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (f : Family) (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : aError C atG=-s)
    (hflat : (C.point A).a=7/12)
    (hz : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hhg : hg=0 ∨ hg=2) :
    0<actualStress C hg atG (Explicit.k f (delta C.theta T))
      (Explicit.l f (delta C.theta T)) (Explicit.c f (delta C.theta T)) s := by
  let k := Explicit.k f (delta C.theta T)
  let l := Explicit.l f (delta C.theta T)
  let c := Explicit.c f (delta C.theta T)
  have hsf := (Explicit.angle_domain atG hs).2
  have hzf := Explicit.family_frame_domain f hz
  obtain ⟨hk,hG,hB,hc,hm⟩ := Explicit.family_coefficient_domain f atG hz hs
  have hcoeff := Explicit.ordered_pair_domain f atG hz hs
  have hb := original_budgets hg atG k l c hsf.1 ha hvar hzf.1
  have hlo := original_stress_lower atG hsorted hcontained hq hHy hGy hBy hDy
    hvar hsf ha hflat hzf.1 hhg hk hG hB hc hm
  obtain ⟨i,j,hmin⟩ := Concentration.concentrate R (GlobalGA.Secondary.diagonal-1/2)
    (pWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
    (qWeights atG k l (PositiveTD.tilted c (delta C.theta T)) s)
    (fun i => (blocks C hg atG k l c s i).P)
    (fun i => (blocks C hg atG k l c s i).N) 3
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hcoeff i).1) (fun i => (hcoeff i).2.1) (fun i => (hcoeff i).2.2)
    (fun i => (blocks C hg atG k l c s i).P_nonneg)
    (fun i => (blocks C hg atG k l c s i).N_nonneg)
    hsf hzf hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
  have hp := family_intrinsic_positive f atG hz hs i j
  change 0< intrinsic atG k l c s (delta C.theta T) i j at hp
  dsimp [intrinsic] at hp
  change 0<actualStress C hg atG k l c s
  linarith

theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : aError C atG=-s)
    (hflat : (C.point A).a=7/12) (hz : 0≤delta C.theta T)
    (hhg : hg=0 ∨ hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D 2) (hEH : C.Feasible E 0) : False := by
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hzframe : delta C.theta T∈Icc 0 frameCap :=
    ⟨hz,(le_abs_self _).trans (original_error_bound hvar hn T)⟩
  have hfamily (f : Family)
      (hf : delta C.theta T∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) : False := by
    have hp := family_stress_positive f atG hsorted hcontained hq hHy hGy hBy hDy
      hvar hs ha hflat hf hhg
    have hweights := Explicit.family_positive f hf
    have hnp := stress_nonpositive atG hweights.1.le hweights.2.1.le hweights.2.2.1
      (Explicit.angle_domain atG hs).2 hzframe hHG hGA hAB hBT hTD hDE hEH
    exact (not_le_of_gt hp) hnp
  by_cases hlow : delta C.theta T≤1/5
  · apply hfamily .low
    norm_num [Certificate.left,Certificate.right,Certificate.split]
    exact ⟨hz,hlow⟩
  · apply hfamily .high
    norm_num [Certificate.left,Certificate.right,Certificate.split,PositiveTD.Certificate.h]
    exact ⟨(lt_of_not_ge hlow).le,hzframe.2⟩

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.Source
