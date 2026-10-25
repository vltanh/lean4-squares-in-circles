module

public import SquaresInCircles.Eight.TableFree.NegativeLargeDEStress

/-!
# The original five-anchor stress for canonical negative capture

Uncompiled reconstruction of sections 1--2 of
HAND_G5_NEGATIVE_CANONICAL_SMALL_ERROR_CAPTURE.md.

The five points below are the original anchors, with nonnegative
transverse magnitudes.  In particular the E row is collected before
circle support is applied.  The secant coefficient belongs to H, and
the two E constraints are in their original, different frames.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NegativeCaptureStress
open NegativeLargeDECalculus
open PositiveAngularEnvelope (pairNorm)

abbrev W := NegativeLargeDEStress.W
abbrev k := NegativeLargeDEStress.k
abbrev support := NegativeLargeDEStress.support

def η : ℝ := 3/500
def lambda (f α : ℝ) : ℝ := f*Real.cos α+k*Real.sin α
def demand (a f α t u e : ℝ) : ℝ :=
  W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e+
    a+η/2+1+W u+f*W α+lambda f α
def defect (a f α t u e : ℝ) : ℝ := demand a f α t u e-
  (support (Real.cos t) (a+η-Real.sin t)+
    support (Real.cos u) (a-Real.sin u)+support f 1+
    support (lambda f α) (1/Real.cos e)+
    support (f*Real.sin α) (k*Real.sin α))
def constant (a f α : ℝ) : ℝ :=
  3+2*a+η+f+2*lambda f α+f*Real.sin α-
    R*Real.sqrt (f^2+1)-R*Real.sin α*Real.sqrt (f^2+k^2)

/-- The exact original weak inequalities imply the collected stress.
No new intermediate square or new anchor circle is introduced. -/
theorem five_anchor_defect {H A B D E : SignedPoint} {a f α t u e : ℝ}
    (ha : 0≤a) (hf : 0≤f)
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e)
    (hsum : t+u+e=α) (hα : α≤27/100)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y)
    (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hcH : H.Contained qTrial) (hcA : A.Contained qTrial)
    (hcB : B.Contained qTrial) (hcD : D.Contained qTrial)
    (hcE : E.Contained qTrial)
    (hHA : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      H.y/Real.cos e+A.a*Real.cos t-A.y*Real.sin t)
    (hAB : 1≤A.y+B.y) (hlarge : 1/2≤A.y)
    (hBD : 1+W u≤B.a*Real.cos u-B.y*Real.sin u+D.y)
    (hDE : W α≤D.a+E.a*Real.sin α-E.y*Real.cos α)
    (hEH : 1≤H.a+E.y) :
    defect a f α t u e≤0 := by
  have hα' : α∈Icc 0 (27/100 : ℝ) := ⟨by linarith,hα⟩
  have htrig := short_trig hα'
  have hlambda : 0≤lambda f α := by
    exact add_nonneg (mul_nonneg hf (by linarith [htrig.1]))
      (mul_nonneg (by norm_num [k,NegativeLargeDEStress.k]) htrig.2.2.1)
  have hη : 0≤η := by norm_num [η]
  have hAB' := mul_le_mul_of_nonneg_left hAB ha
  have hlarge' := mul_le_mul_of_nonneg_left hlarge hη
  have hDE' := mul_le_mul_of_nonneg_left hDE hf
  have hEH' := mul_le_mul_of_nonneg_left hEH hlambda
  have hA := NegativeLargeDEStress.support_normal hyA hcA
    (Real.cos t) (a+η-Real.sin t)
  have hB := NegativeLargeDEStress.support_normal hyB hcB
    (Real.cos u) (a-Real.sin u)
  have hD := NegativeLargeDEStress.support_normal hyD hcD f 1
  have hH := NegativeLargeDEStress.support_normal hyH hcH (lambda f α) (1/Real.cos e)
  have hE := NegativeLargeDEStress.support_normal hyE hcE
    (f*Real.sin α) (k*Real.sin α)
  have hcancel : lambda f α-f*Real.cos α=k*Real.sin α := by dsimp [lambda]; ring
  have hcancelE := congrArg (fun r : ℝ => r*E.y) hcancel
  have e1 : 1/Real.cos e*H.y=H.y/Real.cos e := by ring
  dsimp only [defect,demand,support]
  linarith

theorem norm_ordinary_identity (p z : ℝ) :
    Real.sqrt ((Real.cos z)^2+(p-Real.sin z)^2)=pairNorm p 1 (-z) := by
  unfold pairNorm
  congr 1
  rw [Real.sin_neg]
  linear_combination Real.sin_sq_add_cos_sq z

/-- All split dependence is confined to these three actual norm terms.
The coefficient lambda remains fixed during both endpoint reductions. -/
theorem defect_decomposition {a f α t u e : ℝ}
    (hα : α∈Icc 0 (27/100 : ℝ)) (he : e∈Icc 0 (27/100 : ℝ)) :
    defect a f α t u e=
      constant a f α+g (a+η) t+g a u+NegativeLargeDECalculus.f (lambda f α) e := by
  have hc : 0<Real.cos e := by linarith [(short_trig he).1]
  rw [f_formula hc]
  dsimp [defect,demand,support,NegativeLargeDEStress.support]
  rw [norm_ordinary_identity,norm_ordinary_identity,
    NegativeLargeDEStress.norm_E_identity hα]
  dsimp [constant,g,W,NegativeLargeDEStress.W,lambda]
  field_simp [hc.ne']
  ring

end SquaresInCircles.Eight.TableFree.NegativeCaptureStress
