import SquaresInCircles.Six.PinAxes
import SquaresInCircles.Six.Stress.SupportExpression

/-!
# The fixed C/W/D/S graph used by every classification row

Square order is C,W,D,S; edge order is W->C, S->C, D->C, W->D, D->S.
D/W and D/S signs are the audited W-to-D and D-to-S signs. Zero-weight edges
impose no selected-axis hypothesis. The fixed strict exclusions are evaluated
at the larger radius R0; this is a stronger exclusion than using R_*.
-/

namespace SquaresInCircles.Six.Stress
open Normalization Normalization.Certificates

abbrev Basis := Fin 4 × Bool

structure FixedSpec where
  weight : Fin 5 → ℚ
  westCardinal : Bool
  southCardinal : Bool
  wdAxis : Fin 8
  dsAxis : Fin 8
  deriving DecidableEq

namespace FixedSpec

def source : Fin 5 → Fin 4 := ![1,3,2,1,2]
def target : Fin 5 → Fin 4 := ![0,0,0,2,3]

def axisSign : Fin 8 → ℚ := ![1,-1,1,-1,1,-1,1,-1]

def wdBasis : Fin 8 → Basis :=
  ![(1,false),(1,false),(1,true),(1,true),(2,false),(2,false),(2,true),(2,true)]

def dsBasis : Fin 8 → Basis :=
  ![(2,false),(2,false),(2,true),(2,true),(3,false),(3,false),(3,true),(3,true)]

def basis (s : FixedSpec) : Fin 5 → Basis :=
  ![if s.westCardinal then (0,false) else (1,false),
    if s.southCardinal then (0,true) else (3,false),
    (2,false),wdBasis s.wdAxis,dsBasis s.dsAxis]

def sign (s : FixedSpec) : Fin 5 → ℚ :=
  ![if s.westCardinal then 1 else -1,if s.southCardinal then 1 else -1,
    -1,axisSign s.wdAxis,axisSign s.dsAxis]

def coefficient (s : FixedSpec) (i : Fin 4) (e : Fin 5) : ℚ :=
  (if target e=i then s.weight e else 0)-(if source e=i then s.weight e else 0)

def valid (s : FixedSpec) : Prop := (∀ e,0≤s.weight e) ∧ (∑ e,s.weight e)=1
instance (s : FixedSpec) : Decidable s.valid := inferInstanceAs (Decidable ((∀ e,0≤s.weight e) ∧ _))

noncomputable section

def phase (w t d : ℝ) : Fin 4 → ℝ := ![0,Real.pi+w,Real.pi+d,3*Real.pi/2+t]

def frame (w t d : ℝ) (i : Fin 4) : UnitSquare := orientedSquare (phase w t d i) 0 0

def basisVector (w t d : ℝ) (a : Basis) : Point :=
  if a.2 then secondary (phase w t d a.1) else primary (phase w t d a.1)

def normal (s : FixedSpec) (w t d : ℝ) (e : Fin 5) : Point :=
  scale (s.sign e : ℝ) (basisVector w t d (s.basis e))

def halfWidths (w t d : ℝ) : Fin 5 → ℝ :=
  ![1/2+angularWidth w,1/2+angularWidth t,1/2+angularWidth d,
    1/2+angularWidth (d-w),1/2+angularWidth (d-t)]

def force (s : FixedSpec) (w t d : ℝ) (i : Fin 4) : Point :=
  (∑ e,(s.coefficient i e : ℝ)*(s.normal w t d e).1,
   ∑ e,(s.coefficient i e : ℝ)*(s.normal w t d e).2)

def threshold (s : FixedSpec) (w t d : ℝ) : ℝ :=
  ∑ e,(s.weight e : ℝ)*halfWidths w t d e

/-- Inactive edges have their own actual projection as threshold. Their weighted
contribution is still zero, and they impose no false geometric requirement. -/
def system (s : FixedSpec) (w t d : ℝ) (S : Fin 4 → UnitSquare) : System 4 5 where
  source := source
  target := target
  normal := s.normal w t d
  weight := fun e => (s.weight e : ℝ)
  threshold := fun e => if s.weight e=0 then
    dot (s.normal w t d e) (sub (S (target e)).center (S (source e)).center)
    else halfWidths w t d e

lemma system_force (s : FixedSpec) (w t d : ℝ) (S : Fin 4 → UnitSquare) (i : Fin 4) :
    (s.system w t d S).force i=s.force w t d i := by
  apply Prod.ext
  all_goals simp only [System.force,system,force,coefficient,Rat.cast_sub,Rat.cast_ite,
    Rat.cast_zero,sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul]

lemma system_threshold (s : FixedSpec) (w t d : ℝ) (S : Fin 4 → UnitSquare) :
    (s.system w t d S).thresholdSum=s.threshold w t d := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : s.weight e=0 <;> simp [System.thresholdSum,system,threshold,h]

lemma system_nonnegative (s : FixedSpec) (hs : s.valid) (w t d : ℝ) (S : Fin 4 → UnitSquare) :
    (s.system w t d S).Nonnegative := by
  intro e
  exact_mod_cast hs.1 e

/-- The support array uses the full central box and exact cap/vertex supports. -/
def support (s : FixedSpec) (w t d : ℝ) : Fin 4 → ℝ :=
  ![Stress.boxSupport c0 (s.force w t d 0),
    exactSupport R0 (frame w t d 1) (s.force w t d 1),
    exactSupport R0 (frame w t d 2) (s.force w t d 2),
    exactSupport R0 (frame w t d 3) (s.force w t d 3)]

def defect (s : FixedSpec) (w t d : ℝ) : ℝ := s.threshold w t d-∑ i,s.support w t d i

lemma nonpos_of_realized (s : FixedSpec) (hs : s.valid) (w t d : ℝ)
    (S : Fin 4 → UnitSquare)
    (hsep : ∀ e, s.weight e≠0 → halfWidths w t d e ≤
      dot (s.normal w t d e) (sub (S (target e)).center (S (source e)).center))
    (hupper : ∀ i,dot (s.force w t d i) (S i).center ≤ s.support w t d i) :
    s.defect w t d ≤ 0 := by
  have hseps : (s.system w t d S).Separates S := by
    intro e
    by_cases h : s.weight e=0
    · simp [system,h]
    · simpa [system,h] using hsep e h
  have h := (s.system w t d S).defect_nonpos S (s.support w t d)
    (s.system_nonnegative hs w t d S) hseps
    (fun i => by simpa only [system_force] using hupper i)
  simpa only [system_threshold,defect] using h

end
end FixedSpec
end SquaresInCircles.Six.Stress
