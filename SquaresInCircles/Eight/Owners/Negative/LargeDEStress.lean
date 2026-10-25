module

public import SquaresInCircles.Eight.Owners.Negative.LargeDECalculus
public import SquaresInCircles.Eight.Owners.Negative.OuterEZero

/-!
# Eight squares: the actual five-center stress at the negative large-A DE boundary

Each original center contributes once, after both
incident constraints have been collected.  E has an arbitrary signed
tangent; its nonnegative resulting force permits the identical circle
support.  The exact defect is decomposed before any endpoint-specific
circle masses are introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NegativeLargeDEStress
open NegativeLargeDECalculus PositiveCancelingOuter
open PositiveAngularEnvelope (pairNorm)

def η : ℝ := 1/400
def k : ℝ := 307/1000
def W (z : ℝ) : ℝ := (1+Real.cos z+Real.sin z)/2
def d (ε α : ℝ) : ℝ := ε*Real.cos α+k*Real.sin α
def support (X Y : ℝ) : ℝ := R*Real.sqrt (X^2+Y^2)-(X+Y)/2
def demand (a β ε α t u e : ℝ) : ℝ :=
  W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e+
    a+η/2+β*(1+W u)+d ε α+ε*W α
def defect (a β ε α t u e : ℝ) : ℝ := demand a β ε α t u e-
  (support (Real.cos t) (a+η-Real.sin t)+
    support (β*Real.cos u) (a-β*Real.sin u)+support (d ε α) β+
    support ε (1/Real.cos e)+support (ε*Real.sin α) (k*Real.sin α))
def constant (a β ε α : ℝ) : ℝ :=
  1+2*a+η+2*β+2*d ε α+ε+ε*Real.sin α-
    R*Real.sqrt ((d ε α)^2+β^2)-R*Real.sin α*Real.sqrt (ε^2+k^2)

theorem support_normal {P : SignedPoint} (hy : 0≤P.y) (hc : P.Contained qTrial) (X Y : ℝ) :
    X*P.a+Y*P.y≤ support X Y := by
  have hR : 0≤R := by linarith [radius_bounds.1]
  have hc' : P.Contained (R^2) := by rw [radius_sq]; exact hc
  have hh := SignedStress.work_le_signed_support hR hc'
    (sign := 1) (Or.inl rfl) (by simp [abs_of_nonneg hy]) (X,Y)
  simpa [support,SignedStress.work] using hh

/-- This support remains valid for the full signed E domain. -/
theorem support_signed {E : SignedPoint} (hc : E.Contained qTrial) {Y : ℝ}
    (hY : 0≤Y) (X : ℝ) : X*E.a+Y*E.y≤ support X Y := by
  let E' : SignedPoint := ⟨E.a,|E.y|⟩
  have hc' : E'.Contained qTrial := by
    simpa [E',SignedPoint.Contained,SignedPoint.circle,abs_abs] using hc
  have hh := support_normal (show 0≤E'.y from abs_nonneg _) hc' X Y
  have hy := mul_le_mul_of_nonneg_left (le_abs_self E.y) hY
  dsimp [E'] at hh
  linarith

theorem composite_secant {H A : SignedPoint} {t e : ℝ}
    (_ht : t∈Icc 0 (27/100 : ℝ)) (he : e∈Icc 0 (27/100 : ℝ))
    (hsource : NegativeOuterEZero.demand (1-V A t) e≤H.y) :
    W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      H.y/Real.cos e+A.a*Real.cos t-A.y*Real.sin t := by
  have hc : 0<Real.cos e := by linarith [(short_trig he).1]
  rw [Real.tan_eq_sin_div_cos]
  have key : (W t+1/2)*Real.cos e+1/2+(13/12)*Real.sin e≤
      H.y+(A.a*Real.cos t-A.y*Real.sin t)*Real.cos e := by
    dsimp [NegativeOuterEZero.demand,V] at hsource
    dsimp [W]
    linarith
  have e1 : W t+1/2+1/(2*Real.cos e)+(13/12)*(Real.sin e/Real.cos e)=
      ((W t+1/2)*Real.cos e+1/2+(13/12)*Real.sin e)/Real.cos e := by
    field_simp
  have e2 : H.y/Real.cos e+A.a*Real.cos t-A.y*Real.sin t=
      (H.y+(A.a*Real.cos t-A.y*Real.sin t)*Real.cos e)/Real.cos e := by
    field_simp
    ring
  rw [e1,e2]
  exact div_le_div_of_nonneg_right key hc.le

/-- Original weak constraints imply the nonpositive exact-norm defect.
The same stress weights are held fixed on the whole angular simplex. -/
theorem five_anchor_defect {H A B D E : SignedPoint} {a β ε α t u e : ℝ}
    (ha : 0≤a) (hβ : 0≤β) (hε : 0≤ε)
    (ht : 0≤t) (hu : 0≤u) (he : 0≤e)
    (hsum : t+u+e=α) (hα : α≤27/100)
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y)
    (hcH : H.Contained qTrial) (hcA : A.Contained qTrial) (hcB : B.Contained qTrial)
    (hcD : D.Contained qTrial) (hcE : E.Contained qTrial)
    (hHA : NegativeOuterEZero.demand (1-V A t) e≤H.y)
    (hAB : 1≤A.y+B.y) (hlarge : 1/2≤A.y)
    (hBD : 1+W u≤B.a*Real.cos u-B.y*Real.sin u+D.y)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    defect a β ε α t u e≤0 := by
  have ht' : t∈Icc 0 (27/100 : ℝ) := ⟨ht,by linarith⟩
  have he' : e∈Icc 0 (27/100 : ℝ) := ⟨he,by linarith⟩
  have hα' : α∈Icc 0 (27/100 : ℝ) := ⟨by linarith,hα⟩
  have htrig := short_trig hα'
  have hδ : 0≤d ε α := by
    exact add_nonneg (mul_nonneg hε (by linarith [htrig.1]))
      (mul_nonneg (by norm_num [k]) htrig.2.2.1)
  have hEY : 0≤k*Real.sin α := mul_nonneg (by norm_num [k]) htrig.2.2.1
  have hη : 0≤η := by norm_num [η]
  have hHA' := composite_secant ht' he' hHA
  have hAB' := mul_le_mul_of_nonneg_left hAB ha
  have hlarge' := mul_le_mul_of_nonneg_left hlarge hη
  have hBD' := mul_le_mul_of_nonneg_left hBD hβ
  have hDE' := mul_le_mul_of_nonneg_left hDE hδ
  have hEH' := mul_le_mul_of_nonneg_left hEH hε
  have hA := support_normal hyA hcA (Real.cos t) (a+η-Real.sin t)
  have hB := support_normal hyB hcB (β*Real.cos u) (a-β*Real.sin u)
  have hD := support_normal hyD hcD (d ε α) β
  have hH := support_normal hyH hcH ε (1/Real.cos e)
  have hE := support_signed hcE hEY (ε*Real.sin α)
  have hcancel : d ε α-ε*Real.cos α=k*Real.sin α := by dsimp [d]; ring
  have hcancelE := congrArg (fun r : ℝ => r*E.y) hcancel
  have e1 : 1/Real.cos e*H.y=H.y/Real.cos e := by ring
  dsimp only [defect,demand]
  linarith

theorem norm_A_identity (a t : ℝ) :
    Real.sqrt ((Real.cos t)^2+(a+η-Real.sin t)^2)=pairNorm (a+η) 1 (-t) := by
  unfold pairNorm
  congr 1
  rw [Real.sin_neg]
  linear_combination Real.sin_sq_add_cos_sq t

theorem norm_B_identity {β : ℝ} (hβ : 0<β) (a u : ℝ) :
    Real.sqrt ((β*Real.cos u)^2+(a-β*Real.sin u)^2)=β*pairNorm (a/β) 1 (-u) := by
  have he : (β*Real.cos u)^2+(a-β*Real.sin u)^2=
      β^2*((a/β)^2+1^2+2*(a/β)*1*Real.sin (-u)) := by
    rw [Real.sin_neg]
    field_simp [hβ.ne']
    nlinarith [congrArg (fun r : ℝ => β^2*r) (Real.sin_sq_add_cos_sq u),
      congrArg (fun r : ℝ => β^4*r) (Real.sin_sq_add_cos_sq u)]
  rw [he,Real.sqrt_mul (sq_nonneg β),Real.sqrt_sq hβ.le]
  rfl

theorem norm_E_identity {α : ℝ} (hα : α∈Icc 0 (27/100 : ℝ)) (ε : ℝ) :
    Real.sqrt ((ε*Real.sin α)^2+(k*Real.sin α)^2)=
      Real.sin α*Real.sqrt (ε^2+k^2) := by
  rw [show (ε*Real.sin α)^2+(k*Real.sin α)^2=(Real.sin α)^2*(ε^2+k^2) by ring,
    Real.sqrt_mul (sq_nonneg (Real.sin α)),Real.sqrt_sq (short_trig hα).2.2.1]

/-- The exact norm defect separates into two ordinary negative-angle
terms, one secant term and a constant.  No endpoint masses appear. -/
theorem defect_decomposition {a β ε α t u e : ℝ}
    (hβ : 0<β) (hα : α∈Icc 0 (27/100 : ℝ)) (he : e∈Icc 0 (27/100 : ℝ)) :
    defect a β ε α t u e=
      constant a β ε α+g (a+η) t+β*g (a/β) u+NegativeLargeDECalculus.f ε e := by
  have hc : 0<Real.cos e := by linarith [(short_trig he).1]
  rw [f_formula hc]
  dsimp [defect,demand,support]
  rw [norm_A_identity,norm_B_identity hβ,norm_E_identity hα]
  dsimp [constant,g,W,d]
  field_simp [hc.ne']
  ring

end SquaresInCircles.Eight.NegativeLargeDEStress
