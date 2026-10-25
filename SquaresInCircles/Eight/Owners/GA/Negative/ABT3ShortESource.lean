module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3ShortEReference
public import SquaresInCircles.Eight.Owners.GA.Negative.AShortESource

/-!
# Eight squares: the original negative-A / positive-BT3 shorter-E exclusion

Both original A
owners, all four selected E-owner choices, and both BT3 weight families
are dispatched here. The positive reference stress is used only as an
algebraic comparison; every feasibility premise concerns the actual cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.ShortE
open Candidate Secondary SignedStress
open Certificate (Family)

theorem family_minimum_L (f : Family) {z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) :
    NegativeA.ShortE.minimumL≤Explicit.l f z :=
  (Explicit.positive f hz).2.1.le

/-- The whole original necessary cycle is contradictory when the selected
signed E total lies between zero and the single negative A magnitude. -/
theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (ha : Source.aError C atG= -s)
    (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (hcut : (C.point A).y≤ if atG then 39/250 else 1/2)
    (he : PairedE.cycleTotal C de eh∈Icc 0 s)
    (hz : 0≤delta C.theta B) (hhg : hg=0∨hg=2)
    (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  let e := PairedE.cycleTotal C de eh
  let x := s-e
  let C' := reference C atG de eh
  have hsframe := (Explicit.angle_domain atG hs).2
  have hxcut : x∈Icc 0 (Explicit.angleCut atG) :=
    ⟨by dsimp [x,e]; linarith [he.2],by dsimp [x,e]; linarith [he.1,hs.2]⟩
  have hxframe := (Explicit.angle_domain atG hxcut).2
  have hrefvar := NegativeA.ShortE.reference_variation_le atG de eh hs.1 ha he hvar
  have hrefa := NegativeA.ShortE.reference_aError atG de eh ha
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hzframe : delta C.theta B∈Icc 0 frameCap :=
    ⟨hz,(le_abs_self _).trans (original_error_bound hvar hn B)⟩
  have heframe := PairedE.cycle_total_bounds de eh hvar he.1
  have hB := NegativeA.ShortE.gain_coefficient_bounds atG hsorted hcontained hq hBy hAy hcut
    hflat hsframe ha hAB
  have hE := PairedE.selected_charge de eh (hsorted E) (hcontained E) hq
    (original_error_bound hvar hn D) (original_error_bound hvar hn E) heframe
  change TwoPositive.ASupport.charge (PairedE.cycleTotal C de eh)≤
    PairedE.primaryGain (C.point E) de eh (delta C.theta D) (delta C.theta E) at hE
  have hfamily (f : Family)
      (hf : delta C.theta B∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ)) : False := by
    let k := Explicit.k f (delta C.theta B)
    let l := Explicit.l f (delta C.theta B)
    let c := Explicit.m f (delta C.theta B)
    have hp : 0<Source.actualStress C' hg atG k l c x := by
      have hh := Source.family_stress_positive (C:=C') f atG
        (by intro i; exact hsorted i) (by intro i; exact hcontained i) hq
        hHy hGy hBy hDy hrefvar hxcut hrefa hflat
        (by simpa [C'] using hf) hhg
      simpa only [C',reference_B] using hh
    have hgain := NegativeA.ShortE.transfer atG hB hs he (family_minimum_L f hf)
    have hid := stress_identity hg atG de eh k l c hsframe ha hflat he
    have hcomp : Source.actualStress C' hg atG k l c x≤
        actualStress C hg atG de eh k l c x := by
      dsimp [C',x,e]
      rw [hid]
      change 0≤Explicit.l f (delta C.theta B)/Real.cos (s-PairedE.cycleTotal C de eh)*
        (gain (gainCoefficient C atG) s-gain (gainCoefficient C atG)
          (s-PairedE.cycleTotal C de eh))+
        TwoPositive.ASupport.charge (PairedE.cycleTotal C de eh) at hgain
      dsimp [l]
      linarith only [hgain,hE]
    have hpos := Explicit.family_positive f hf
    have hnp := actual_stress_nonpositive atG de eh hpos.1.le hpos.2.1.le
      hpos.2.2.2 hxframe hzframe hHG hGA hAB hBT hTD hDE hEH
    exact (not_le_of_gt (hp.trans_le hcomp)) hnp
  by_cases hlow : delta C.theta B≤1/4
  · exact hfamily .low (by
      norm_num [Certificate.left,Certificate.right,Certificate.split]; exact ⟨hz,hlow⟩)
  · exact hfamily .high (by
      norm_num [Certificate.left,Certificate.right,Certificate.split]
      exact ⟨(lt_of_not_ge hlow).le,by simpa [frameCap] using hzframe.2⟩)

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.ShortE
