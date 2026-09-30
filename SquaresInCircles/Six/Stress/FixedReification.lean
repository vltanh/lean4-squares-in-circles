module
public import SquaresInCircles.Six.Stress.FixedGraph

@[expose] public section

/-!
# Proof-producing expressions for the fixed stresses

Each local force is the exact incidence sum, resolved on the square's frame.
Own-frame basis vectors reduce to 0 and 1 before interval evaluation. This is
an algebraic identity, not a sampled comparison with the geometric evaluator.
-/

namespace SquaresInCircles.Six.Stress.FixedSpec
open ProofTools Normalization Normalization.Certificates

abbrev er {n : ℕ} (q : ℚ) : Expr n := .rat q

def sum5E {n : ℕ} (f : Fin 5 → Expr n) : Expr n := f 0+f 1+f 2+f 3+f 4

def phaseE {n : ℕ} (w t d : Expr n) : Fin 4 → Expr n :=
  ![0,.pi+w,.pi+d,er (3/2)*.pi+t]

def localBasisE {n : ℕ} (w t d : Expr n) (i : Fin 4) (a : Basis) (transverse : Bool) : Expr n :=
  if a.1=i then
    if a.2=transverse then 1 else 0
  else
    let delta := phaseE w t d a.1-phaseE w t d i
    if transverse then (if a.2 then .cos delta else .sin delta)
    else (if a.2 then -.sin delta else .cos delta)

def localForceE {n : ℕ} (s : FixedSpec) (w t d : Expr n) (i : Fin 4) (transverse : Bool) : Expr n :=
  sum5E (fun e => if s.coefficient i e=0 then 0 else
    er (s.coefficient i e)*er (s.sign e)*localBasisE w t d i (s.basis e) transverse)

def halfWidthsE {n : ℕ} (w t d : Expr n) : Fin 5 → Expr n :=
  ![er (1/2)+widthE w,er (1/2)+widthE t,er (1/2)+widthE d,
    er (1/2)+widthE (d-w),er (1/2)+widthE (d-t)]

def thresholdE {n : ℕ} (s : FixedSpec) (w t d : Expr n) : Expr n :=
  sum5E (fun e => if s.weight e=0 then 0 else er (s.weight e)*halfWidthsE w t d e)

def defectE {n : ℕ} (s : FixedSpec) (w t d : Expr n) : Expr n :=
  let R := Expr.sqrt (q0E : Expr n)
  let fx := fun i => localForceE s w t d i false
  let fy := fun i => localForceE s w t d i true
  thresholdE s w t d-
    (Reified.boxSupport c0E (fx 0) (fy 0)+
     Reified.support R (fx 1) (fy 1)+Reified.support R (fx 2) (fy 2)+
     Reified.support R (fx 3) (fy 3))

noncomputable section

lemma denote_sum5E {n : ℕ} (x : Fin n → ℝ) (f : Fin 5 → Expr n) :
    Expr.denote (sum5E f) x=∑ i,Expr.denote (f i) x := by
  simp [sum5E,Expr.denote,Fin.sum_univ_succ]
  ring

@[simp] lemma denote_phaseE {n : ℕ} (x : Fin n → ℝ) (w t d : Expr n) (i : Fin 4) :
    Expr.denote (phaseE w t d i) x=phase (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) i := by
  fin_cases i <;> simp [phaseE,phase,Expr.denote] <;> ring

def localBasis (w t d : ℝ) (i : Fin 4) (a : Basis) (transverse : Bool) : ℝ :=
  let delta := phase w t d a.1-phase w t d i
  if transverse then (if a.2 then Real.cos delta else Real.sin delta)
  else (if a.2 then -Real.sin delta else Real.cos delta)

lemma basis_projectionX (w t d : ℝ) (i : Fin 4) (a : Basis) :
    frameX (frame w t d i) (basisVector w t d a)=localBasis w t d i a false := by
  rcases a with ⟨j,b⟩
  cases b <;> simp [frameX,frame,basisVector,primary,secondary,orientedSquare,
    localBasis,Real.cos_sub,Real.sin_sub] <;> ring

lemma basis_projectionY (w t d : ℝ) (i : Fin 4) (a : Basis) :
    frameY (frame w t d i) (basisVector w t d a)=localBasis w t d i a true := by
  rcases a with ⟨j,b⟩
  cases b <;> simp [frameY,frame,basisVector,primary,secondary,orientedSquare,
    localBasis,Real.cos_sub,Real.sin_sub] <;> ring

lemma frameX_scale (S : UnitSquare) (r : ℝ) (v : Point) : frameX S (scale r v)=r*frameX S v := by
  dsimp [frameX,scale]
  ring

lemma frameY_scale (S : UnitSquare) (r : ℝ) (v : Point) : frameY S (scale r v)=r*frameY S v := by
  dsimp [frameY,scale]
  ring

lemma frameX_sum5 (S : UnitSquare) (c : Fin 5 → ℝ) (v : Fin 5 → Point) :
    frameX S (∑ i,c i*(v i).1,∑ i,c i*(v i).2)=∑ i,c i*frameX S (v i) := by
  simp [frameX,Fin.sum_univ_succ]
  ring

lemma frameY_sum5 (S : UnitSquare) (c : Fin 5 → ℝ) (v : Fin 5 → Point) :
    frameY S (∑ i,c i*(v i).1,∑ i,c i*(v i).2)=∑ i,c i*frameY S (v i) := by
  simp [frameY,Fin.sum_univ_succ]
  ring

lemma force_projectionX (s : FixedSpec) (w t d : ℝ) (i : Fin 4) :
    frameX (frame w t d i) (s.force w t d i)=
      ∑ e,(s.coefficient i e:ℝ)*(s.sign e:ℝ)*localBasis w t d i (s.basis e) false := by
  rw [force,frameX_sum5]
  apply Finset.sum_congr rfl
  intro e _
  rw [normal,frameX_scale,basis_projectionX]
  ring

lemma force_projectionY (s : FixedSpec) (w t d : ℝ) (i : Fin 4) :
    frameY (frame w t d i) (s.force w t d i)=
      ∑ e,(s.coefficient i e:ℝ)*(s.sign e:ℝ)*localBasis w t d i (s.basis e) true := by
  rw [force,frameY_sum5]
  apply Finset.sum_congr rfl
  intro e _
  rw [normal,frameY_scale,basis_projectionY]
  ring

@[simp] lemma denote_localBasisE {n : ℕ} (x : Fin n → ℝ) (w t d : Expr n)
    (i : Fin 4) (a : Basis) (b : Bool) :
    Expr.denote (localBasisE w t d i a b) x=
      localBasis (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) i a b := by
  rcases a with ⟨j,c⟩
  by_cases h : j=i
  · subst j
    cases b <;> cases c <;> simp [localBasisE,localBasis,Expr.denote]
  · cases b <;> cases c <;> simp [localBasisE,localBasis,h,Expr.denote]

lemma denote_localForceE {n : ℕ} (x : Fin n → ℝ) (s : FixedSpec) (w t d : Expr n)
    (i : Fin 4) (b : Bool) :
    Expr.denote (localForceE s w t d i b) x=
      if b then frameY (frame (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) i)
        (s.force (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) i)
      else frameX (frame (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) i)
        (s.force (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) i) := by
  rw [localForceE,denote_sum5E]
  cases b
  all_goals simp only [Bool.false_eq_true,if_false,if_true,force_projectionX,force_projectionY]
  all_goals apply Finset.sum_congr rfl
  all_goals intro e _
  all_goals by_cases h : s.coefficient i e=0
  all_goals simp [h,Expr.denote,denote_localBasisE]

@[simp] lemma denote_halfWidthsE {n : ℕ} (x : Fin n → ℝ) (w t d : Expr n) (e : Fin 5) :
    Expr.denote (halfWidthsE w t d e) x=
      halfWidths (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) e := by
  fin_cases e <;> simp [halfWidthsE,halfWidths,Expr.denote,sub_eq_add_neg]

lemma denote_thresholdE {n : ℕ} (x : Fin n → ℝ) (s : FixedSpec) (w t d : Expr n) :
    Expr.denote (thresholdE s w t d) x=
      s.threshold (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) := by
  rw [thresholdE,denote_sum5E,threshold]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : s.weight e=0 <;> simp [h,Expr.denote]

/-- The finite arithmetic expression is exactly the geometric reverse defect. -/
theorem denote_defectE {n : ℕ} (x : Fin n → ℝ) (s : FixedSpec) (w t d : Expr n) :
    Expr.denote (defectE s w t d) x=
      s.defect (Expr.denote w x) (Expr.denote t x) (Expr.denote d x) := by
  simp only [defectE,Expr.denote,denote_thresholdE,Reified.denote_boxSupport,
    Reified.denote_support,denote_localForceE,if_false,if_true]
  simp only [q0E,Expr.denote,R0,defect,support,exactSupport,Fin.sum_univ_succ]
  simp [frame,phase,frameX,frameY,orientedSquare,Stress.boxSupport,c0E,rhoE,q0E,
    Expr.denote,c0,rho0]
  ring

end
end SquaresInCircles.Six.Stress.FixedSpec
