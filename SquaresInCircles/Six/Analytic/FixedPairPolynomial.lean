import SquaresInCircles.Six.Analytic.FixedPairGap
import SquaresInCircles.Six.Analytic.PairSharpConstants
import SquaresInCircles.Six.Analytic.PairPerturbation

/-!
# Rational-polynomial data for the forced endpoints

The constants are justified in PairSharpConstants. Sin and cos are replaced
by the displayed seventh/sixth degree polynomials, whose uniform errors are
proved in PairTaylorApprox. The final error estimate is proved in the next
module; this file does not assert any endpoint positivity.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair.Polynomial
open Stress Normalization PairTaylor

def rApprox : ℝ := 3687848/10000000
def mApprox : ℝ := 8896970/10000000
def cApprox : ℝ := 1128167/10000000
def circleUpper : ℝ := 16885431/10000000
def radialUpper : ℝ := 11128167/10000000
def baseUpper : ℝ := 709742/10000000

def baseVector (own : Bool) (t : ℝ) : Point := if own then (1,0) else (cosP t,-sinP t)

def northSource (u : Fin 4) (q : ℝ) : Point :=
  ![(-sinP q,-cosP q),(cosP q,-sinP q),(1,0),(0,-1)] u

def westSource (u : Fin 4) (q : ℝ) : Point :=
  ![(1,0),(0,1),(-sinP q,cosP q),(cosP q,sinP q)] u

def northVector (no : Bool) (u : Fin 4) (n w : ℝ) : Point :=
  ((baseVector no n).1+rApprox*(northSource u (n-w)).1,
   (baseVector no n).2+rApprox*(northSource u (n-w)).2)

def westVector (wo : Bool) (u : Fin 4) (n w : ℝ) : Point :=
  ((baseVector wo w).1+rApprox*(westSource u (n-w)).1,
   (baseVector wo w).2+rApprox*(westSource u (n-w)).2-mApprox)

def halfWidth (t : ℝ) : ℝ := 1/2+(|cosP t|+|sinP t|)/2

def thresholdP (n w : ℝ) : ℝ := halfWidth n+halfWidth w+rApprox*halfWidth (n-w)+mApprox/2

def penaltyP (no wo : Bool) (n w : ℝ) : ℝ :=
  (if no then cApprox*(max (sinP n) 0+1-cosP n) else 0)+
  (if wo then cApprox*max (sinP w) 0 else 0)

def northScale (u : Fin 4) : ℝ := if u=0 ∨ u=3 then circleUpper else radialUpper

def linearPart (no wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  thresholdP n w+
    (if u=0 ∨ u=3 then ((northVector no u n w).1-(northVector no u n w).2)/2 else 0)+
    ((westVector wo u n w).1-(westVector wo u n w).2)/2-
    penaltyP no wo n w-baseUpper-line w-(1/1000)*|n|

/-- 1/5000 is paid for the whole-domain analytic perturbation bound, not a
numerical tolerance for accepting an unresolved case. -/
def budget (no wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ := linearPart no wo u n w-1/5000

def northSquare (no : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  (northVector no u n w).1^2+(northVector no u n w).2^2

def westSquare (wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  (westVector wo u n w).1^2+(westVector wo u n w).2^2

def squareN (no : Bool) (u : Fin 4) (n w : ℝ) : ℝ := northScale u^2*northSquare no u n w

def squareW (wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ := circleUpper^2*westSquare wo u n w

lemma constants_close : |rStar-rApprox|≤1/10000000 ∧
    |mStar-mApprox|≤3/10000000 ∧ |cStar-cApprox|≤2/10000000 := by
  have hr := pair_ratio_sharp_bounds
  have hm := pair_multiplier_sharp_bounds
  have hc := pair_central_sharp_bounds
  refine ⟨abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩⟩
  all_goals dsimp [rApprox,mApprox,cApprox]
  all_goals linarith [hr.1,hr.2.1,hm.1,hm.2,hc.1,hc.2]

lemma northScale_bounds (u : Fin 4) :
    0≤northRadius u ∧ northRadius u≤northScale u ∧ 0≤northScale u ∧ northScale u≤17/10 := by
  unfold northRadius northScale
  split_ifs with h
  · refine ⟨Six.radius_pos.le,pair_radius_sharp_bounds.2.le,?_,?_⟩
    all_goals norm_num [circleUpper]
  · refine ⟨by linarith [rhoStar_gt_11_10],pair_rho_sharp_bounds.2.le,?_,?_⟩
    all_goals norm_num [radialUpper]

lemma circle_bounds : 0≤Six.radius ∧ Six.radius≤circleUpper ∧ 0≤circleUpper ∧ circleUpper≤17/10 :=
  ⟨Six.radius_pos.le,pair_radius_sharp_bounds.2.le,by norm_num [circleUpper],by norm_num [circleUpper]⟩

lemma base_bound : pairBase≤baseUpper := pair_base_sharp_upper.le

lemma squareN_nonneg (no : Bool) (u : Fin 4) (n w : ℝ) : 0≤ squareN no u n w := by
  dsimp [squareN,northSquare]
  positivity

lemma squareW_nonneg (wo : Bool) (u : Fin 4) (n w : ℝ) : 0≤ squareW wo u n w := by
  dsimp [squareW,westSquare]
  positivity

end SquaresInCircles.Six.Analytic.FixedPair.Polynomial
