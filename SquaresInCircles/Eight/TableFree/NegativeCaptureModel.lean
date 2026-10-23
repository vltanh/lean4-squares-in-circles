module

public import SquaresInCircles.Eight.TableFree.NegativeCaptureShortAngle

/-!
# The rational-constant endpoint model and its actual geometric error

Uncompiled reconstruction.  The model changes only the one fixed angle
3/200.  Its remaining sine and cosine are the exact original total
angle.  The error comparison uses the collected same-circle supports.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree.NegativeCaptureModel
open NegativeCaptureShortAngle

def tVertex (j : Fin 4) (α : ℝ) : ℝ := if j=0 then α else if j=2 then r else 0
def uVertex (j : Fin 4) (α : ℝ) : ℝ := if j=0 ∨ j=1 then 0 else α-r
def eVertex (j : Fin 4) (α : ℝ) : ℝ := if j=1 then α else if j=3 then r else 0

def cT (j : Fin 4) (s c : ℝ) : ℝ := if j=0 then c else if j=2 then χ else 1
def sT (j : Fin 4) (s c : ℝ) : ℝ := if j=0 then s else if j=2 then σ else 0
def cU (j : Fin 4) (s c : ℝ) : ℝ := if j=0 ∨ j=1 then 1 else c*χ+s*σ
def sU (j : Fin 4) (s c : ℝ) : ℝ := if j=0 ∨ j=1 then 0 else s*χ-c*σ
def secE (j : Fin 4) (s c : ℝ) : ℝ := if j=1 then 1/c else if j=3 then 1/χ else 1
def tanE (j : Fin 4) (s c : ℝ) : ℝ := if j=1 then s/c else if j=3 then σ/χ else 0

def demand (j : Fin 4) (a f s c : ℝ) : ℝ :=
  (1+cT j s c+sT j s c)/2+1/2+secE j s c/2+(13/12)*tanE j s c+
    a+(3/500)/2+1+(1+cU j s c+sU j s c)/2+
    f*(1+c+s)/2+f*c+(307/1000)*s

def defect (j : Fin 4) (a f s c : ℝ) : ℝ := demand j a f s c-
  (NegativeCaptureStress.support (cT j s c) (a+3/500-sT j s c)+
    NegativeCaptureStress.support (cU j s c) (a-sU j s c)+
    NegativeCaptureStress.support f 1+
    NegativeCaptureStress.support (f*c+(307/1000)*s) (secE j s c)+
    NegativeCaptureStress.support (f*s) ((307/1000)*s))

theorem trig_errors (j : Fin 4) (α : ℝ) :
    |Real.cos (tVertex j α)-cT j (Real.sin α) (Real.cos α)|≤error ∧
    |Real.sin (tVertex j α)-sT j (Real.sin α) (Real.cos α)|≤error ∧
    |Real.cos (uVertex j α)-cU j (Real.sin α) (Real.cos α)|≤error ∧
    |Real.sin (uVertex j α)-sU j (Real.sin α) (Real.cos α)|≤error ∧
    |1/Real.cos (eVertex j α)-secE j (Real.sin α) (Real.cos α)|≤error ∧
    |Real.tan (eVertex j α)-tanE j (Real.sin α) (Real.cos α)|≤error := by
  have hsin : |Real.sin r-σ|≤error := by dsimp [error]; linarith [sin_close]
  have hcos : |Real.cos r-χ|≤error := by dsimp [error]; linarith [cos_close]
  have hsec : |1/Real.cos r-1/χ|≤error := by dsimp [error]; linarith [sec_close]
  have htan : |Real.tan r-σ/χ|≤error := by dsimp [error]; linarith [tan_close]
  fin_cases j
  · norm_num [tVertex,uVertex,eVertex,cT,sT,cU,sU,secE,tanE,error]
  · norm_num [tVertex,uVertex,eVertex,cT,sT,cU,sU,secE,tanE,error,
      Real.tan_eq_sin_div_cos]
  · simpa [tVertex,uVertex,eVertex,cT,sT,cU,sU,secE,tanE,error] using
      And.intro hcos (And.intro hsin
        (And.intro (shifted_cos_error α) (shifted_sin_error α)))
  · simpa [tVertex,uVertex,eVertex,cT,sT,cU,sU,secE,tanE,error] using
      And.intro (shifted_cos_error α)
        (And.intro (shifted_sin_error α) (And.intro hsec htan))

theorem demand_error (j : Fin 4) (a f α : ℝ) :
    demand j a f (Real.sin α) (Real.cos α)-4*error≤
      NegativeCaptureStress.demand a f α (tVertex j α) (uVertex j α) (eVertex j α) := by
  obtain ⟨htc,hts,huc,hus,hec,hes⟩ := trig_errors j α
  have htc' := (abs_le.mp htc).1
  have hts' := (abs_le.mp hts).1
  have huc' := (abs_le.mp huc).1
  have hus' := (abs_le.mp hus).1
  have hec' := (abs_le.mp hec).1
  have hes' := (abs_le.mp hes).1
  have hhalf : 1/(2*Real.cos (eVertex j α))=(1/Real.cos (eVertex j α))/2 := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  dsimp [demand,NegativeCaptureStress.demand,NegativeCaptureStress.W,
    NegativeLargeDEStress.W,NegativeCaptureStress.η,NegativeCaptureStress.lambda,
    NegativeCaptureStress.k,NegativeLargeDEStress.k]
  rw [hhalf]
  dsimp [error] at *
  linarith

theorem model_le_actual_with_error (j : Fin 4) (a f α : ℝ) :
    defect j a f (Real.sin α) (Real.cos α)-1/100000000≤
      NegativeCaptureStress.defect a f α (tVertex j α) (uVertex j α) (eVertex j α) := by
  obtain ⟨htc,hts,huc,hus,hec,hes⟩ := trig_errors j α
  have hA := support_perturbation (Real.cos (tVertex j α))
    (a+3/500-Real.sin (tVertex j α))
    (cT j (Real.sin α) (Real.cos α)) (a+3/500-sT j (Real.sin α) (Real.cos α))
  have hB := support_perturbation (Real.cos (uVertex j α))
    (a-Real.sin (uVertex j α))
    (cU j (Real.sin α) (Real.cos α)) (a-sU j (Real.sin α) (Real.cos α))
  have hH := support_perturbation (f*Real.cos α+(307/1000)*Real.sin α)
    (1/Real.cos (eVertex j α)) (f*Real.cos α+(307/1000)*Real.sin α)
    (secE j (Real.sin α) (Real.cos α))
  rw [show a+3/500-Real.sin (tVertex j α)-
      (a+3/500-sT j (Real.sin α) (Real.cos α))=
        -(Real.sin (tVertex j α)-sT j (Real.sin α) (Real.cos α)) by ring,
    abs_neg] at hA
  rw [show a-Real.sin (uVertex j α)-(a-sU j (Real.sin α) (Real.cos α))=
      -(Real.sin (uVertex j α)-sU j (Real.sin α) (Real.cos α)) by ring,
    abs_neg] at hB
  simp only [sub_self,abs_zero,zero_add] at hH
  have hd := demand_error j a f α
  dsimp [defect,NegativeCaptureStress.defect,NegativeCaptureStress.η,
    NegativeCaptureStress.lambda,NegativeCaptureStress.k,NegativeLargeDEStress.k]
  dsimp [error] at *
  linarith

/-- The two vertices without the short angle are exactly unchanged. -/
theorem model_eq_actual {j : Fin 4} (hj : j=0 ∨ j=1) (a f α : ℝ) :
    defect j a f (Real.sin α) (Real.cos α)=
      NegativeCaptureStress.defect a f α (tVertex j α) (uVertex j α) (eVertex j α) := by
  rcases hj with rfl | rfl <;>
    simp [defect,demand,tVertex,uVertex,eVertex,cT,sT,cU,sU,secE,tanE,
      NegativeCaptureStress.defect,NegativeCaptureStress.demand,
      NegativeCaptureStress.W,NegativeLargeDEStress.W,NegativeCaptureStress.η,
      NegativeCaptureStress.lambda,NegativeCaptureStress.k,NegativeLargeDEStress.k,
      Real.tan_eq_sin_div_cos] <;> ring

/-- Each intrinsic vertex pays precisely its prescribed error allowance. -/
theorem model_le_actual (j : Fin 4) (a f α : ℝ) :
    defect j a f (Real.sin α) (Real.cos α)-(NegativeCaptureData.delta j:ℝ)≤
      NegativeCaptureStress.defect a f α (tVertex j α) (uVertex j α) (eVertex j α) := by
  by_cases hj : j=0 ∨ j=1
  · rw [NegativeCaptureData.delta,if_pos hj,model_eq_actual hj]
    simp
  · simpa [NegativeCaptureData.delta,hj] using model_le_actual_with_error j a f α

end SquaresInCircles.Eight.TableFree.NegativeCaptureModel
