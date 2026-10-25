module

public import SquaresInCircles.Eight.Owners.GA.DSupport
public import SquaresInCircles.Eight.Owners.GA.Owners

/-!
# Eight squares: exact original-axis collection for the secondary high-GA chain

This file collects the seven original weak separators
with the fixed positive weights `(k,l,l,2,2,1,1)`.  A, T, and E cancel
algebraically.  The two HG owners retain their actual different force
formulas; the angular charge vanishes by the seven-cycle incidence law.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.Secondary
open Candidate SignedStress

def baseStress : ℝ :=
  79/8-fullSupport 1 k-fullSupport l k-fullSupport 2 l-3*diagonal

def dIncrement (z d : ℝ) (P : SignedPoint) : ℝ :=
  2*edgeWidth z+edgeWidth d-(dF z d*P.a+dG z d*P.y)+
    charge*(z+d)-(3-3*diagonal)

theorem baseStress_reserve : (627/10000:ℝ)<baseStress := by
  have h := fourCircle_radical_reserve
  norm_num [baseStress,fullSupport,R,k,l,diagonal] at h ⊢
  linarith

theorem actual_dIncrement_nonneg {q z d : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hz : |z|≤frameCap) (hd : |d|≤frameCap) (hsum : |z+d|≤frameCap) :
    0≤dIncrement z d P := by
  have h := actual_D_lower hs hy hc hq hz hd hsum
  dsimp [dIncrement]
  linarith

end SquaresInCircles.Eight.GlobalGA.Secondary
