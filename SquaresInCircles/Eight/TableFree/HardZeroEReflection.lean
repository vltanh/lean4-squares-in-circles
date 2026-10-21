module

public import SquaresInCircles.Eight.TableFree.NonpositiveAboveE

/-!
# Exact hard-cycle reflection at a zero original E tangent

Uncompiled reconstruction.  A full physical reflection reverses E's
sign, so it is used here only after the actual E tangent is zero.  The
original owners and both hard axes transform by their projection
identities.  The above-H exclusion then rules out a zero E below D;
the ordered E-zero barrier handles the rest of the original frame line.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.SignedCycle
open Candidate

/-- This restricted reflection keeps the E-sign field for a proved
reason.  It does not normalize E after changing any original anchor. -/
def HardInput.reflectZeroE {q : ℝ} (I : HardInput q)
    (hE0 : (I.cycle.point E).y=0) : HardInput q where
  cycle := I.cycle.reflected
  necessary := I.necessary.reflected
  anchors_normal := reflected_normal I.anchors_normal
  E_nonpos := by simp [reflected,reflectedIndex,E,SignedPoint.reflect,hE0]
  witnesses := I.witnesses.reflected
  GA_hard := by
    have hh := (reflected_feasible I.cycle G 2).2
      (by simpa [reflectedIndex,next,G,B] using I.BT_hard)
    simpa [reflectedOwner] using hh
  BT_hard := by
    have hh := (reflected_feasible I.cycle B 0).2
      (by simpa [reflectedIndex,next,B,G] using I.GA_hard)
    simpa [reflectedOwner] using hh
  zero_signs := {
    HG_canceling := by
      intro h
      have hT : I.witnesses.owner T=0 := by
        simpa [Witnesses.reflected,reflectedIndex,next,H,T,reflectedOwner] using h
      have hy := I.zero_signs.TD_canceling hT
      simpa [reflected,reflectedIndex,G,T,SignedPoint.reflect] using neg_neg_of_pos hy
    TD_canceling := by
      intro h
      have hG : I.witnesses.owner H=2 := by
        have hh := h
        fin_cases hj : I.witnesses.owner H <;>
          simp [Witnesses.reflected,reflectedIndex,next,H,T,reflectedOwner,hj] at hh ⊢
      have hy := I.zero_signs.HG_canceling hG
      simpa [reflected,reflectedIndex,G,T,SignedPoint.reflect] using neg_pos.mpr hy }
  E_radial := by
    simpa [reflected,reflectedIndex,H,D,E,SignedPoint.reflect,abs_neg,max_comm]
      using I.E_radial

theorem HardInput.nonpositive_below_zero_E_impossible {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2)
    (hED : I.cycle.theta E<I.cycle.theta D)
    (hE0 : (I.cycle.point E).y=0) : False := by
  let J := I.reflectZeroE hE0
  have hJAB : J.cycle.theta A=J.cycle.theta B := by
    simp [J,HardInput.reflectZeroE,reflected,reflectedIndex,A,B,hAB]
  have hJnorm : (J.cycle.point A).y-(J.cycle.point B).y=1 := by
    change -(I.cycle.point B).y-(-(I.cycle.point A).y)=1
    linarith
  have hJAG : J.cycle.theta A≤J.cycle.theta G := by
    change I.cycle.theta B-I.cycle.theta B≤I.cycle.theta B-I.cycle.theta T
    linarith
  have hJGH : J.cycle.theta G≤J.cycle.theta H := by
    change I.cycle.theta B-I.cycle.theta T≤I.cycle.theta B-I.cycle.theta D
    linarith
  have hJDT : J.cycle.theta D≤J.cycle.theta T := by
    change I.cycle.theta B-I.cycle.theta H≤I.cycle.theta B-I.cycle.theta G
    linarith
  have hJTB : J.cycle.theta T≤J.cycle.theta B := by
    change I.cycle.theta B-I.cycle.theta G≤I.cycle.theta B-I.cycle.theta A
    linarith
  have hJHG : J.cycle.Feasible H 0 := by
    have hh := (reflected_feasible I.cycle H 2).2
      (by simpa [reflectedIndex,next,H,T] using hTD)
    simpa [J,HardInput.reflectZeroE,reflectedOwner] using hh
  have hJTD : J.cycle.Feasible T 2 := by
    have hh := (reflected_feasible I.cycle T 0).2
      (by simpa [reflectedIndex,next,T,H] using hHG)
    simpa [J,HardInput.reflectZeroE,reflectedOwner] using hh
  have horder := J.nonpositive_E_le_H hqL hq hJAB hJnorm hJAG hJGH hJDT hJTB hJHG hJTD
  have horder' : I.cycle.theta D≤I.cycle.theta E := by
    change I.cycle.theta B-I.cycle.theta E≤I.cycle.theta B-I.cycle.theta D at horder
    linarith
  exact (not_le_of_gt hED) horder'

/-- No original zero E tangent survives at any original frame in the
nonpositive-composite sector.  This includes both original mixed-owner
choices and will discharge the tangent floor of the actual E arc. -/
theorem HardInput.nonpositive_E_strict_negative {q : ℝ}
    (I : HardInput q) (hqL : qLow≤q) (hq : q≤qTrial)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hnorm : (I.cycle.point A).y-(I.cycle.point B).y=1)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hHG : I.cycle.Feasible H 0) (hTD : I.cycle.Feasible T 2) :
    (I.cycle.point E).y<0 := by
  by_contra! hnot
  have hE0 : (I.cycle.point E).y=0 := le_antisymm I.E_nonpos hnot
  by_cases hED : I.cycle.theta E<I.cycle.theta D
  · exact I.nonpositive_below_zero_E_impossible hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
      hED hE0
  have hDEorder : I.cycle.theta D≤I.cycle.theta E := le_of_not_gt hED
  have hEHorder := I.nonpositive_E_le_H hqL hq hAB hnorm hAG hGH hDT hTB hHG hTD
  have hcap : q≤qCap := hq.trans (by norm_num [qTrial,qCap])
  have hDE := I.nonpositive_DE_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hDEorder
  have hEH := I.nonpositive_EH_primary_of_nonneg hcap hAB hAG hGH hDT hTB hHG hTD hEHorder
  exact I.nonpositive_zero_E_impossible hcap hAB hAG hGH hDT hTB hHG hTD
    hE0 hDEorder hEHorder hDE hEH

end SquaresInCircles.Eight.TableFree.SignedCycle
