import SquaresInCircles.Six.Stress.CandidateStressConstants
import SquaresInCircles.Six.Normalization.CentralSAT

/-!
# A common adjacent-pair stress

These are ordinary real-valued definitions and exact resultant identities.
The E/S pair uses the same expressions at (-e,-s). All four central-bit choices
and all four genuine source axes are explicit.

Computational reification is no longer imported here. The common pair lower
bound is a separate obligation; its existing certificate implementation still
requires human-analytic replacement. The definitions and algebra below are
also used independently by the analytic diagonal proof.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress
open Normalization

/-- Weight of C--N in the independent N/W balance. -/
def pairAlpha (northOwn westOwn : Bool) (n w : ℝ) : ℝ :=
  if northOwn then
    if westOwn then (Real.cos w+Real.sin w)/Real.cos (w-n) else 1/Real.cos n
  else if westOwn then (Real.cos w+Real.sin w)/Real.cos w else 1

/-- Weight of C--W in the independent N/W balance. -/
def pairGamma (northOwn westOwn : Bool) (n w : ℝ) : ℝ :=
  if northOwn then
    if westOwn then (Real.cos n-Real.sin n)/Real.cos (w-n)
    else (Real.cos n-Real.sin n)/Real.cos n
  else if westOwn then 1/Real.cos w else 1

def pairNorthBase (own : Bool) (n : ℝ) : Point :=
  if own then (1,0) else (Real.cos n,-Real.sin n)

def pairWestBase (own : Bool) (w : ℝ) : Point :=
  if own then (1,0) else (Real.cos w,-Real.sin w)

/-- Source order W-primary, W-secondary, N-primary, N-secondary. -/
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

def pairThreshold (no wo : Bool) (n w : ℝ) : ℝ :=
  pairAlpha no wo n w*(1/2+angularWidth n)+
    pairGamma no wo n w*(1/2+angularWidth w)+rStar*(1/2+angularWidth (n-w))+mStar/2

/-- Both supports are the proved exact cap/vertex center support. -/
def pairValue (no wo : Bool) (u : Fin 4) (n w : ℝ) : ℝ :=
  pairThreshold no wo n w-
    scalarSupport Six.radius (pairNorthForce no wo u n w).1 (pairNorthForce no wo u n w).2-
    scalarSupport Six.radius (pairWestForce no wo u n w).1 (pairWestForce no wo u n w).2

def pairBase : ℝ := mStar*(1/2-Six.tStar)

/-- The proposed common envelope, whose whole-domain pair proof is separate. -/
def pairLine (x : ℝ) : ℝ := (73/100)*max (-x) 0-(13/50)*max x 0

def diagonalLocalForce (w s d : ℝ) : Point :=
  (mStar*(Real.sin (d-w)+Real.cos (d-s)),
   mStar*(Real.cos (d-w)-Real.sin (d-s)))

/-- The constant halves m/2 of these thresholds belong to the two pair terms. -/
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

lemma pair_trig_signs {n w : ℝ}
    (hn : -3/10≤n ∧ n≤5/12) (hw : -2/3≤w ∧ w≤5/8) :
    0<Real.cos n ∧ 0<Real.cos w ∧ 0<Real.cos (w-n) ∧
      0<Real.cos w+Real.sin w ∧ 0<Real.cos n-Real.sin n := by
  have hcn := Real.cos_pos_of_mem_Ioo
    (show n ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hn.1,hn.2,Real.pi_gt_d2])
  have hcw := Real.cos_pos_of_mem_Ioo
    (show w ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hw.1,hw.2,Real.pi_gt_d2])
  have hdiff := Real.cos_pos_of_mem_Ioo
    (show w-n ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hw.1,hw.2,hn.1,hn.2,Real.pi_gt_d2])
  have hs := Real.sin_pos_of_pos_of_lt_pi
    (show 0<w+Real.pi/4 by linarith [hw.1,Real.pi_gt_d2])
    (show w+Real.pi/4<Real.pi by linarith [hw.2,Real.pi_gt_d2])
  have hc := Real.cos_pos_of_mem_Ioo
    (show n+Real.pi/4 ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hn.1,hn.2,Real.pi_gt_d2])
  rw [Real.sin_add,Real.sin_pi_div_four,Real.cos_pi_div_four] at hs
  rw [Real.cos_add,Real.sin_pi_div_four,Real.cos_pi_div_four] at hc
  have hroot : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsum : 0<Real.cos w+Real.sin w := by nlinarith
  have hsub : 0<Real.cos n-Real.sin n := by nlinarith
  exact ⟨hcn,hcw,hdiff,hsum,hsub⟩

lemma pair_weights_pos (no wo : Bool) {n w : ℝ}
    (hn : -3/10≤n ∧ n≤5/12) (hw : -2/3≤w ∧ w≤5/8) :
    0<pairAlpha no wo n w ∧ 0<pairGamma no wo n w := by
  obtain ⟨hcn,hcw,hcwn,hplus,hminus⟩ := pair_trig_signs hn hw
  cases no <;> cases wo <;> simp only [pairAlpha,pairGamma,Bool.false_eq_true,if_false,if_true]
  all_goals constructor
  all_goals first | positivity | exact div_pos hplus hcwn | exact div_pos hminus hcwn

/-- Exact fixed pair resultant, valid for each of the four central-bit choices. -/
lemma pair_balance (no wo : Bool) {n w : ℝ}
    (hcn : Real.cos n≠0) (hcw : Real.cos w≠0) (hcwn : Real.cos (w-n)≠0) :
    pairGamma no wo n w*(if wo then Real.cos w else 1)+
      pairAlpha no wo n w*(if no then Real.sin n else 0)=1 ∧
    pairGamma no wo n w*(if wo then Real.sin w else 0)-
      pairAlpha no wo n w*(if no then Real.cos n else 1)=-1 := by
  cases no <;> cases wo
  all_goals constructor
  all_goals simp only [pairAlpha,pairGamma,Bool.false_eq_true,if_false,if_true]
  all_goals field_simp [hcn,hcw,hcwn]
  all_goals first
    | ring1
    | rw [Real.cos_sub]
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

lemma pair_alternate_forces (no wo : Bool) {u : Fin 4} (hu : u=1 ∨ u=2) :
    pairNorthForce no wo u 0 0=(1+rStar,0) ∧
      pairWestForce no wo u 0 0=(1,rStar-mStar) := by
  rcases hu with rfl | rfl
  all_goals cases no <;> cases wo <;>
    simp [pairNorthForce,pairWestForce,pairNorthBase,pairWestBase,pairNorthSource,pairWestSource]

@[simp] lemma pairThreshold_zero (no wo : Bool) : pairThreshold no wo 0 0=2+rStar+mStar/2 := by
  simp [pairThreshold,angularWidth]
  ring

end SquaresInCircles.Six.Stress
