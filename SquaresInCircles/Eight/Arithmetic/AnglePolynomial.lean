module

public import SquaresInCircles.Eight.Arithmetic.TargetSupport
public import SquaresInCircles.Eight.Arithmetic.RationalBernstein

/-!
# The real meaning of the ten one-angle parameters

The two remainder parameters are chosen separately at each angle.  The other
parameters denote fixed algebraic arc endpoints and π.  Their rational boxes
are obtained from the proved scalar-expression evaluator.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.Arithmetic
namespace AnglePolynomial

def boxes (t : PreparedArc) : QBox 10 :=
  ![⟨3141592653589793238/1000000000000000000,
       3141592653589793239/1000000000000000000⟩,
    ⟨0,1/362880⟩,⟨-1/3628800,0⟩,
    t.aLo.range closedBoxes,t.bLo.range closedBoxes,
    t.aHi.range closedBoxes,t.bHi.range closedBoxes,
    t.ratioLo.range closedBoxes,t.ratioHi.range closedBoxes,
    t.radiusExpr.range closedBoxes]

def env (t : PreparedArc) (es ec : ℝ) : Fin 10 → ℝ :=
  ![Real.pi,es,ec,t.aLo.value,t.bLo.value,t.aHi.value,t.bHi.value,
    t.ratioLo.value,t.ratioHi.value,t.radiusExpr.value]

theorem env_mem {t : PreparedArc} (ht : t.NumericValid) {es ec : ℝ}
    (hs : 0 ≤ es ∧ es ≤ 1/362880) (hc : -1/3628800 ≤ ec ∧ ec ≤ 0) :
    (boxes t).Mem (env t es ec) := by
  intro i
  fin_cases i
  · refine ⟨?_,?_⟩
    · show (((3141592653589793238/1000000000000000000 : ℚ)) : ℝ) ≤ Real.pi
      push_cast
      exact pi_hand_enclosure.1.le
    · show Real.pi ≤ (((3141592653589793239/1000000000000000000 : ℚ)) : ℝ)
      push_cast
      exact pi_hand_enclosure.2.le
  · refine ⟨?_,?_⟩
    · show ((0 : ℚ) : ℝ) ≤ es
      push_cast
      exact hs.1
    · show es ≤ ((1/362880 : ℚ) : ℝ)
      push_cast
      linarith [hs.2]
  · refine ⟨?_,?_⟩
    · show ((-1/3628800 : ℚ) : ℝ) ≤ ec
      push_cast
      linarith [hc.1]
    · show ec ≤ ((0 : ℚ) : ℝ)
      push_cast
      exact hc.2
  · exact t.aLo.closed_sound ht.2.2.1
  · exact t.bLo.closed_sound (t.bLo_valid ht)
  · exact t.aHi.closed_sound ht.2.2.2.1
  · exact t.bHi.closed_sound (t.bHi_valid ht)
  · exact t.ratioLo.closed_sound (t.ratioLo_valid ht)
  · exact t.ratioHi.closed_sound (t.ratioHi_valid ht)
  · exact t.radiusExpr.closed_sound ht.2.2.2.2.1

def param (i : Fin 10) : ParamPoly 10 := .scalar (.var i)

def sine : ParamPoly 10 :=
  .add (.add (.add (.add .angle (.scale (-1/6) (.pow .angle 3)))
    (.scale (1/120) (.pow .angle 5))) (.scale (-1/5040) (.pow .angle 7)))
    (.mul (param 1) (.pow .angle 9))

def cosine : ParamPoly 10 :=
  .add (.add (.add (.add (.add (.constant 1) (.scale (-1/2) (.pow .angle 2)))
    (.scale (1/24) (.pow .angle 4))) (.scale (-1/720) (.pow .angle 6)))
    (.scale (1/40320) (.pow .angle 8))) (.mul (param 2) (.pow .angle 10))

theorem sine_eval {t : PreparedArc} {es ec u : ℝ}
    (hs : Real.sin u=sin7 u+es*u^9) : sine.eval (env t es ec) u = Real.sin u := by
  have he : env t es ec 1 = es := rfl
  rw [hs]
  simp only [sine,param,ParamPoly.eval,ParamPoly.scale,ParamPoly.constant,
    ScalarExpr.eval,he,sin7]
  push_cast
  ring

theorem cosine_eval {t : PreparedArc} {es ec u : ℝ}
    (hc : Real.cos u=cos8 u+ec*u^10) : cosine.eval (env t es ec) u = Real.cos u := by
  have he : env t es ec 2 = ec := rfl
  rw [hc]
  simp only [cosine,param,ParamPoly.eval,ParamPoly.scale,ParamPoly.constant,
    ScalarExpr.eval,he,cos8]
  push_cast
  ring

def signQ (positiveHalf : Bool) : ℚ := if positiveHalf then 1 else -1

def shiftedSine (quarter : ℕ) (positiveHalf : Bool) : ParamPoly 10 :=
  if quarter=0 then .scale (signQ positiveHalf) sine else cosine

def shiftedCosine (quarter : ℕ) (positiveHalf : Bool) : ParamPoly 10 :=
  if quarter=0 then cosine else .scale (-signQ positiveHalf) sine

def phi (quarter : ℕ) (positiveHalf : Bool) (u : ℝ) : ℝ :=
  (quarter : ℝ)*Real.pi/2+(signQ positiveHalf : ℝ)*u

theorem shifted_eval {t : PreparedArc} {es ec u : ℝ} {k : ℕ} {r : Bool}
    (hk : k≤1) (hs : Real.sin u=sin7 u+es*u^9)
    (hc : Real.cos u=cos8 u+ec*u^10) :
    (shiftedSine k r).eval (env t es ec) u = Real.sin (phi k r u) ∧
    (shiftedCosine k r).eval (env t es ec) u = Real.cos (phi k r u) := by
  have hS := sine_eval (t:=t) (ec:=ec) hs
  have hC := cosine_eval (t:=t) (es:=es) hc
  interval_cases k <;> cases r <;>
    simp [shiftedSine,shiftedCosine,signQ,phi,ParamPoly.eval,ParamPoly.scale,
      ParamPoly.constant,ScalarExpr.eval,hS,hC,Real.sin_add,Real.cos_add]

theorem absolute_sum {k : ℕ} {r : Bool} {u : ℝ} (hk : k≤1)
    (hu : 0≤u ∧ u≤4/5) :
    |Real.sin (phi k r u)|+|Real.cos (phi k r u)|=Real.sin u+Real.cos u := by
  have hS : 0≤Real.sin u := by
    have hs := (small_polynomial_trig hu).2.1
    nlinarith [hu.1]
  have hC : 0≤Real.cos u := by linarith [(small_polynomial_trig hu).1]
  interval_cases k <;> cases r <;>
    simp [phi,signQ,Real.sin_add,Real.cos_add,abs_of_nonneg hS,abs_of_nonneg hC,
      add_comm]

end AnglePolynomial
end SquaresInCircles.Eight.Arithmetic
