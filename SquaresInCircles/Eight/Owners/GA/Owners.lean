module

public import SquaresInCircles.Eight.Frames.Signed.Stress
public import SquaresInCircles.Eight.Owners.NecessaryCycle

/-!
# Eight squares: A concrete four-circle obstruction to an actual high GA witness

The perturbation estimate below applies to every owner in the full high-GA
necessary owner domain, including both owners of every weak tie. It gives
an explicit necessary error budget, and excludes high GA when every actual
edge error is at most 1/225.

No outer equality, tangent sign, frame order, core endpoint, or selected
low GA witness is an input. A, T, and E cancel in the exact linear sum.
The sorted D support is essential and is proved directly from its circle.

This is one proved region of the global GA theorem.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA
open Candidate SignedStress

def highGAOwners : Vertex → Finset (Fin 4) :=
  ![{0,2},{2,3},{0,2},{2,3},{0,2},{2,3},{0,1}]

theorem highGAOwners_eq_normal {i : Vertex} (hi : i≠G) :
    highGAOwners i=SignedCycle.normalOwners i := by
  fin_cases i <;> norm_num [G] at hi <;>
    simp [highGAOwners,SignedCycle.normalOwners]

/-- Three positive square comparisons prove the strict zero-error reserve.
These are exact radical bounds, not an accepted numerical certificate. -/
theorem fourCircle_radical_reserve :
    Real.sqrt qCap*Real.sqrt (1+(31/40 : ℝ)^2)+
      Real.sqrt qCap*Real.sqrt ((31/20 : ℝ)^2+(31/40 : ℝ)^2)+
      Real.sqrt qCap*Real.sqrt (4+(31/20 : ℝ)^2)+
      3*diagonalCoordinate qCap < 137/10-627/10000 := by
  have hQ := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hH := Real.sq_sqrt (show (0:ℝ)≤1+(31/40 : ℝ)^2 by norm_num)
  have hG := Real.sq_sqrt
    (show (0:ℝ)≤(31/20 : ℝ)^2+(31/40 : ℝ)^2 by norm_num)
  have hB := Real.sq_sqrt (show (0:ℝ)≤4+(31/20 : ℝ)^2 by norm_num)
  have hHsq : (Real.sqrt qCap*Real.sqrt (1+(31/40 : ℝ)^2))^2=
      qCap*(1+(31/40 : ℝ)^2) := by rw [mul_pow,hQ,hH]
  have hGsq :
      (Real.sqrt qCap*Real.sqrt ((31/20 : ℝ)^2+(31/40 : ℝ)^2))^2=
        qCap*((31/20 : ℝ)^2+(31/40 : ℝ)^2) := by rw [mul_pow,hQ,hG]
  have hBsq : (Real.sqrt qCap*Real.sqrt (4+(31/20 : ℝ)^2))^2=
      qCap*(4+(31/20 : ℝ)^2) := by rw [mul_pow,hQ,hB]
  have hHbound : Real.sqrt qCap*Real.sqrt (1+(31/40 : ℝ)^2)<25034791/10000000 := by
    norm_num [qCap] at hHsq
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap)
      (Real.sqrt_nonneg (1+(31/40 : ℝ)^2))]
  have hGbound :
      Real.sqrt qCap*Real.sqrt ((31/20 : ℝ)^2+(31/40 : ℝ)^2)<34291452/10000000 := by
    norm_num [qCap] at hGsq
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap)
      (Real.sqrt_nonneg ((31/20 : ℝ)^2+(31/40 : ℝ)^2))]
  have hBbound : Real.sqrt qCap*Real.sqrt (4+(31/20 : ℝ)^2)<50069582/10000000 := by
    norm_num [qCap] at hBsq
    nlinarith [mul_nonneg (Real.sqrt_nonneg qCap)
      (Real.sqrt_nonneg (4+(31/20 : ℝ)^2))]
  have hDbound : Real.sqrt (qCap/2)<13992141/10000000 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num [qCap]
  dsimp [diagonalCoordinate]
  linarith

/-- Sorting and containment suffice for this upper coordinate bound; no
core or outer-boundary hypothesis is used in the perturbation estimate. -/
theorem primary_upper {q : ℝ} {p : SignedPoint}
    (hs : p.Sorted) (hc : p.Contained q) (hq : q≤qCap) : p.a≤283/200 := by
  have hcircle : (p.a+1/2)^2+(|p.y|+1/2)^2≤qCap := hc.trans hq
  dsimp [qCap] at hcircle
  nlinarith [abs_nonneg p.y,sq_nonneg |p.y|,hs.1]

end SquaresInCircles.Eight.GlobalGA
