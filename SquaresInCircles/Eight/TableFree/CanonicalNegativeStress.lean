module

public import SquaresInCircles.Eight.TableFree.NegativeCapture
public import SquaresInCircles.Eight.ExactFamily.CenterCompletion

/-!
# Exact original-circle completion on the canonical negative branch

Uncompiled reconstruction.  The only angular errors in this branch are
t and e, while the other mixed angle is u=alpha-t-e.  Collecting the
five original inequalities directly gives an exact two-error formula.
No auxiliary G/T point or displacement estimate is used in this identity.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CanonicalNegativeStress

structure Parameters where
  a : ℝ
  beta : ℝ
  delta : ℝ
  epsilon : ℝ
  omega : ℝ
  mu : Fin 5 → ℝ

def Parameters.Positive (w : Parameters) : Prop :=
  0≤w.a ∧ 0≤w.beta ∧ 0≤w.delta ∧ 0≤w.epsilon ∧ 0≤w.omega ∧ ∀i,0<w.mu i

abbrev W := NegativeCaptureStress.W
def massSum (w : Parameters) : ℝ := ∑i : Fin 5,w.mu i

/-- Anchor order A,B,D,E,H, all in their original own-frame positive
coordinates.  The original E tangent magnitude is retained. -/
def forces (w : Parameters) (α t u e : ℝ) : Fin 5 → Point := ![
  (w.omega*Real.cos u,w.a-w.omega*Real.sin u),
  (w.beta*Real.cos t,w.a-w.beta*Real.sin t),
  (w.delta,w.beta/Real.cos e),
  (w.epsilon*Real.sin α,w.delta-w.epsilon*Real.cos α),
  (w.epsilon,w.omega)]

def demand (w : Parameters) (α t u e : ℝ) : ℝ :=
  w.omega*(1+W u)+w.a+
    w.beta*(W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e)+
    w.delta+w.epsilon*W α

def circleSupport (q m : ℝ) (F : Point) : ℝ :=
  q*m+normSq F/(4*m)-(F.1+F.2)/2

def defect (q : ℝ) (w : Parameters) (α t u e : ℝ) : ℝ :=
  demand w α t u e-∑i : Fin 5,circleSupport q (w.mu i) (forces w α t u e i)

def work (F : Point) (P : SignedPoint) : ℝ := F.1*P.a+F.2*P.y

def centerSquare (m : ℝ) (F : Point) (P : SignedPoint) : ℝ :=
  m*((P.a+1/2-F.1/(2*m))^2+(P.y+1/2-F.2/(2*m))^2)

def centerLoss (w : Parameters) (α t u e : ℝ) (p : Fin 5 → SignedPoint) : ℝ :=
  ∑i : Fin 5,centerSquare (w.mu i) (forces w α t u e i) (p i)

def circleLoss (q : ℝ) (w : Parameters) (p : Fin 5 → SignedPoint) : ℝ :=
  ∑i : Fin 5,w.mu i*(q-(p i).circle)

theorem center_identity {m : ℝ} (hm : m≠0) (F : Point) {P : SignedPoint}
    (hy : 0≤P.y) (q : ℝ) :
    centerSquare m F P+m*(q-P.circle)=circleSupport q m F-work F P := by
  rw [SignedPoint.circle,abs_of_nonneg hy]
  dsimp [centerSquare,circleSupport,normSq,work]
  field_simp [hm]
  ring

/-- The exact equality retains each source anchor's radial slack. -/
theorem exact_identity {w : Parameters} (hm : ∀i,w.mu i≠0)
    {p : Fin 5 → SignedPoint} (hy : ∀i,0≤(p i).y) (q α t u e : ℝ) :
    defect q w α t u e+centerLoss w α t u e p+circleLoss q w p=
      demand w α t u e-∑i : Fin 5,work (forces w α t u e i) (p i) := by
  have hh := Finset.sum_congr rfl
    (fun i (_ : i∈(Finset.univ : Finset (Fin 5))) =>
      center_identity (hm i) (forces w α t u e i) (hy i) q)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hh
  dsimp [defect,centerLoss,circleLoss]
  linarith

/-- Weighted collection of exactly the five original weak contacts. -/
theorem demand_le_work {w : Parameters} (hw : w.Positive)
    {H A B D E : SignedPoint} {α t u e : ℝ}
    (hHA : 1+W u≤H.y+A.a*Real.cos u-A.y*Real.sin u)
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    demand w α t u e≤∑i : Fin 5,
      work (forces w α t u e i) (![A,B,D,E,H] i) := by
  obtain ⟨ha,hb,hd,he,ho,hm⟩ := hw
  have h1 := mul_le_mul_of_nonneg_left hHA ho
  have h2 := mul_le_mul_of_nonneg_left hAB ha
  have h3 := mul_le_mul_of_nonneg_left hBD hb
  have h4 := mul_le_mul_of_nonneg_left hDE hd
  have h5 := mul_le_mul_of_nonneg_left hEH he
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,forces,work,demand,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero]
  have hdiv : w.beta*(D.y/Real.cos e)=w.beta/Real.cos e*D.y := by ring
  linarith

theorem original_circle_inequality {w : Parameters} (hw : w.Positive)
    {H A B D E : SignedPoint} {q α t u e : ℝ}
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hHA : 1+W u≤H.y+A.a*Real.cos u-A.y*Real.sin u)
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    defect q w α t u e+centerLoss w α t u e ![A,B,D,E,H]+
      circleLoss q w ![A,B,D,E,H]≤0 := by
  have hm : ∀i,w.mu i≠0 := fun i => (hw.2.2.2.2.2 i).ne'
  have hy : ∀i : Fin 5,0≤(![A,B,D,E,H] i).y := by
    intro i
    fin_cases i <;>
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ] <;>
      assumption
  rw [exact_identity hm hy]
  exact sub_nonpos.mpr (demand_le_work hw hHA hAB hBD hDE hEH)

theorem centerLoss_nonneg {w : Parameters} (hw : w.Positive)
    (p : Fin 5 → SignedPoint) (α t u e : ℝ) : 0≤centerLoss w α t u e p := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hw.2.2.2.2.2 i).le (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem circleLoss_nonneg {w : Parameters} (hw : w.Positive)
    {p : Fin 5 → SignedPoint} {q : ℝ} (hc : ∀i,(p i).Contained q) :
    0≤circleLoss q w p := by
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hw.2.2.2.2.2 i).le (sub_nonneg.mpr (hc i)))

theorem circleLoss_positive {w : Parameters} (hw : w.Positive)
    {p : Fin 5 → SignedPoint} {q : ℝ} (hc : ∀i,(p i).Contained q)
    (hstrict : ∃i,(p i).circle<q) : 0<circleLoss q w p := by
  obtain ⟨i,hi⟩ := hstrict
  have hterm : 0<w.mu i*(q-(p i).circle) :=
    mul_pos (hw.2.2.2.2.2 i) (sub_pos.mpr hi)
  exact hterm.trans_le (Finset.single_le_sum
    (fun j (_ : j∈(Finset.univ : Finset (Fin 5))) =>
      mul_nonneg (hw.2.2.2.2.2 j).le (sub_nonneg.mpr (hc j))) (Finset.mem_univ i))

def KA (w : Parameters) : ℝ := w.a*w.omega/(2*w.mu 0)
def KB (w : Parameters) : ℝ := w.a*w.beta/(2*w.mu 1)
def flux (w : Parameters) (α : ℝ) : ℝ := KA w*Real.cos α-w.omega*Real.sin α

def fixedPart (q : ℝ) (w : Parameters) (α : ℝ) : ℝ :=
  2*w.omega+2*w.a+w.beta+2*w.delta+w.epsilon+w.epsilon*Real.sin α-q*massSum w-
    (w.omega^2+w.a^2)/(4*w.mu 0)-(w.beta^2+w.a^2)/(4*w.mu 1)-
    w.delta^2/(4*w.mu 2)-
    ((w.epsilon*Real.sin α)^2+(w.delta-w.epsilon*Real.cos α)^2)/(4*w.mu 3)-
    (w.epsilon^2+w.omega^2)/(4*w.mu 4)

theorem ordinary_norm (omega a z : ℝ) :
    (omega*Real.cos z)^2+(a-omega*Real.sin z)^2=
      omega^2+a^2-2*omega*a*Real.sin z := by
  nlinarith [congrArg (fun x : ℝ => omega^2*x) (Real.sin_sq_add_cos_sq z)]

theorem defect_formula {w : Parameters} (hm : ∀i,w.mu i≠0)
    (q α t u e : ℝ) :
    defect q w α t u e=fixedPart q w α+w.omega*Real.cos u+KA w*Real.sin u+
      w.beta*Real.cos t+KB w*Real.sin t+w.beta/Real.cos e+
      w.beta*(13/12)*Real.tan e-w.beta^2/(4*w.mu 2)*(1/Real.cos e)^2 := by
  simp only [defect,forces,demand,circleSupport,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,normSq]
  rw [ordinary_norm,ordinary_norm]
  dsimp [fixedPart,massSum,KA,KB,W,NegativeCaptureStress.W,NegativeLargeDEStress.W]
  simp only [Fin.sum_univ_five]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def correction (w : Parameters) (α t e : ℝ) : ℝ :=
  w.omega*(Real.cos (α-t-e)-Real.cos α)+KA w*(Real.sin (α-t-e)-Real.sin α)+
    w.beta*(Real.cos t-1)+KB w*Real.sin t+
    w.beta*(1/Real.cos e-1)+w.beta*(13/12)*Real.tan e-
    w.beta^2/(4*w.mu 2)*((1/Real.cos e)^2-1)

/-- Exact correction in the only two errors left by canonicalization. -/
theorem defect_difference {w : Parameters} (hm : ∀i,w.mu i≠0)
    (q α t e : ℝ) :
    defect q w α t (α-t-e) e=defect q w α 0 α 0+correction w α t e := by
  rw [defect_formula hm,defect_formula hm]
  simp only [Real.cos_zero,Real.sin_zero,Real.tan_zero,mul_one,mul_zero,
    div_one,one_div_one,one_pow]
  dsimp [correction]
  ring

theorem defect_radius (w : Parameters) (q q₀ α t u e : ℝ) :
    defect q w α t u e=defect q₀ w α t u e-(q-q₀)*massSum w := by
  simp [defect,circleSupport,massSum,Fin.sum_univ_succ]
  ring

end SquaresInCircles.Eight.TableFree.CanonicalNegativeStress
