import SquaresInCircles.Six.Stress.CandidateStressConstants
import SquaresInCircles.Six.Normalization.CentralSAT

/-!
# The stress of an adjacent pair

The stress of the pair N, W at the angles `n` and `w`, in the frames of the two
squares; the pair E, S is the same at `(-e, -s)`. For each choice of the axes
separating N and W from C, the weights `pairAlpha` and `pairGamma` of C–N and
C–W make the sum of the two weighted normals `(-1, 1)`, as in the model. The
edge N–W has the weight `r*` along one of four axes, and W–D the weight `m*`.
At zero angles, with N–W separated along the axis of the model, the forces are
those of the model. The constant `pairBase`, the piecewise linear `pairLine`
and the diagonal term `diagonalValue` complete the stress.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

/-- The weight of C–N in the stress of the pair N, W. -/
def pairAlpha (northOwn westOwn : Bool) (n w : ℝ) : ℝ :=
  if northOwn then
    if westOwn then (Real.cos w+Real.sin w)/Real.cos (w-n) else 1/Real.cos n
  else if westOwn then (Real.cos w+Real.sin w)/Real.cos w else 1

/-- The weight of C–W in the stress of the pair N, W. -/
def pairGamma (northOwn westOwn : Bool) (n w : ℝ) : ℝ :=
  if northOwn then
    if westOwn then (Real.cos n-Real.sin n)/Real.cos (w-n)
    else (Real.cos n-Real.sin n)/Real.cos n
  else if westOwn then 1/Real.cos w else 1

def pairNorthBase (own : Bool) (n : ℝ) : Point :=
  if own then (1,0) else (Real.cos n,-Real.sin n)

def pairWestBase (own : Bool) (w : ℝ) : Point :=
  if own then (1,0) else (Real.cos w,-Real.sin w)

/-- The normal of N–W in the frame of N, for a separation along the first or
second axis of W (`u = 0, 1`) or of N (`u = 2, 3`), with `q = n - w`. -/
def pairNorthSource (u : Fin 4) (q : ℝ) : Point :=
  ![(-Real.sin q,-Real.cos q),(Real.cos q,-Real.sin q),(1,0),(0,-1)] u

def pairWestSource (u : Fin 4) (q : ℝ) : Point :=
  ![(1,0),(0,1),(-Real.sin q,Real.cos q),(Real.cos q,Real.sin q)] u

def pairNorthForce (no wo : Bool) (u : Fin 4) (n w : ℝ) : Point :=
  (pairAlpha no wo n w*(pairNorthBase no n).1+rStar*(pairNorthSource u (n-w)).1,
   pairAlpha no wo n w*(pairNorthBase no n).2+rStar*(pairNorthSource u (n-w)).2)

def pairWestForce (no wo : Bool) (u : Fin 4) (n w : ℝ) : Point :=
  (pairGamma no wo n w*(pairWestBase wo w).1+rStar*(pairWestSource u (n-w)).1,
   pairGamma no wo n w*(pairWestBase wo w).2+rStar*(pairWestSource u (n-w)).2-mStar)

def pairBase : ℝ := mStar*(1/2-Six.tStar)

/-- A piecewise linear function of the angle of W, of slopes `-73/100` and
`-13/50`, against which the cap term of D is compared. -/
def pairLine (x : ℝ) : ℝ := (73/100)*max (-x) 0-(13/50)*max x 0

def diagonalLocalForce (w s d : ℝ) : Point :=
  (mStar*(Real.sin (d-w)+Real.cos (d-s)),
   mStar*(Real.cos (d-w)-Real.sin (d-s)))

/-- The diagonal term: the angular parts of the thresholds of W–D and D–S with the
weight `m*`, less the support of D; the constant parts `m*/2` are counted with
the pairs. -/
def diagonalValue (w s d : ℝ) : ℝ :=
  mStar*(angularWidth (d-w)+angularWidth (d-s))-
    scalarSupport Six.radius (diagonalLocalForce w s d).1 (diagonalLocalForce w s d).2

lemma pairLine_eq_abs (x : ℝ) : pairLine x=(47/200)*|x|-(99/200)*x := by
  by_cases hx : 0≤x
  · rw [pairLine,max_eq_right (by linarith),max_eq_left hx,abs_of_nonneg hx]
    ring
  · have hx' : x≤0 := (lt_of_not_ge hx).le
    rw [pairLine,max_eq_left (by linarith),max_eq_right hx',abs_of_nonpos hx']
    ring

@[simp] lemma pairLine_zero : pairLine 0=0 := by norm_num [pairLine]

lemma pairLine_sum (w s : ℝ) :
    pairLine w+pairLine (-s)=(47/200)*(|w|+|s|)-(99/100)*((w-s)/2) := by
  rw [pairLine_eq_abs,pairLine_eq_abs,abs_neg]
  ring

@[simp] lemma pairAlpha_zero (no wo : Bool) : pairAlpha no wo 0 0=1 := by
  cases no <;> cases wo <;> norm_num [pairAlpha]

@[simp] lemma pairGamma_zero (no wo : Bool) : pairGamma no wo 0 0=1 := by
  cases no <;> cases wo <;> norm_num [pairGamma]

lemma pair_candidate_forces (no wo : Bool) {u : Fin 4} (hu : u=0 ∨ u=3) :
    pairNorthForce no wo u 0 0=(1,-rStar) ∧
      pairWestForce no wo u 0 0=(1+rStar,-mStar) := by
  rcases hu with rfl | rfl
  all_goals cases no <;> cases wo <;>
    simp [pairNorthForce,pairWestForce,pairNorthBase,pairWestBase,pairNorthSource,pairWestSource]

end SquaresInCircles.Six.Stress
