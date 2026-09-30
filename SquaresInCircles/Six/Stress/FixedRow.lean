module
public import SquaresInCircles.Six.Stress.FixedGeometry
public import SquaresInCircles.Six.ProofTools.Certificate

@[expose] public section

/-!
# Exact closed domains of the fixed-stress rows

Endpoints are affine rational multiples of pi. Each closed box is mapped
exactly from [0,1]^3, with the optional w<=d condition inside the checked
formula. Coverage includes all endpoints. No floating padding enters the Lean
statement, and every checked numerical comparison has a real interpretation.
-/

namespace SquaresInCircles.Six.Stress
open Normalization ProofTools

structure PiBound where
  rational : ℚ
  piCoeff : ℚ
  deriving DecidableEq, Repr

namespace PiBound
noncomputable def value (b : PiBound) : ℝ := (b.rational:ℝ)+(b.piCoeff:ℝ)*Real.pi

def expr {n : ℕ} (b : PiBound) : Expr n :=
  if b.piCoeff=0 then .rat b.rational
  else if b.rational=0 then (.rat b.piCoeff)*.pi
  else (.rat b.rational)+(.rat b.piCoeff)*.pi

@[simp] lemma denote_expr {n : ℕ} (b : PiBound) (x : Fin n → ℝ) : Expr.denote b.expr x=b.value := by
  unfold expr
  split_ifs <;> simp [Expr.denote,value,*]
end PiBound

structure FixedRow where
  key : String
  spec : FixedSpec
  limits : Fin 3 → PiBound × PiBound
  ordered : Bool
  deriving DecidableEq

namespace FixedRow

def affineE (r : FixedRow) (i : Fin 3) : Expr 3 :=
  let low := (r.limits i).1.expr
  let high := (r.limits i).2.expr
  low+(high-low)*Expr.var i

def claim (r : FixedRow) : Formula 3 :=
  let w := r.affineE 0
  let s := r.affineE 1
  let d := r.affineE 2
  .imp (if r.ordered then .le w d else .top) (.lt 0 (r.spec.defectE w s d))

def unitBox : RBox 3 := fun _ => ⟨0,1⟩

def weights (r : FixedRow) (i : Fin 3) : ℚ :=
  if (r.limits i).1=(r.limits i).2 then 0 else 1

def check (r : FixedRow) : Bool := certify r.claim r.weights 0 96 unitBox

noncomputable def InDomain (r : FixedRow) (w s d : ℝ) : Prop :=
  (∀ i : Fin 3, (r.limits i).1.value ≤ ![w,s,d] i ∧ ![w,s,d] i ≤ (r.limits i).2.value) ∧
  (r.ordered=true → w≤d)

lemma inDomain_iff (r : FixedRow) (w s d : ℝ) : r.InDomain w s d ↔
    ((r.limits 0).1.value≤w ∧ w≤(r.limits 0).2.value) ∧
    ((r.limits 1).1.value≤s ∧ s≤(r.limits 1).2.value) ∧
    ((r.limits 2).1.value≤d ∧ d≤(r.limits 2).2.value) ∧
    (r.ordered=true → w≤d) := by
  constructor
  · rintro ⟨h,ho⟩
    exact ⟨h 0,h 1,h 2,ho⟩
  · rintro ⟨h0,h1,h2,ho⟩
    refine ⟨?_,ho⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

/-- A concrete successful kernel computation proves the stated real inequality. -/
theorem positive (r : FixedRow) (hcheck : r.check=true) {w s d : ℝ}
    (hdom : r.InDomain w s d) : 0<r.spec.defect w s d := by
  classical
  choose x hx hpoint using fun i : Fin 3 => segment_parameter (hdom.1 i)
  have hroot : unitBox.Mem x := by
    intro i
    simpa [unitBox,RInterval.Mem] using hx i
  have hvars (i : Fin 3) : Expr.denote (r.affineE i) x=![w,s,d] i := by
    simpa [affineE,Expr.denote,sub_eq_add_neg] using (hpoint i).symm
  have hchecked := certify_sound r.claim r.weights 0 96 hcheck hroot
  have hcondition : Formula.Holds
      (if r.ordered then .le (r.affineE 0) (r.affineE 2) else .top) x := by
    cases h : r.ordered
    · trivial
    · simpa [h,Formula.Holds,hvars] using hdom.2 h
  have hpositive := hchecked hcondition
  simpa only [Formula.Holds,FixedSpec.denote_defectE,Expr.denote,hvars] using hpositive

/-- Final fixed-row interface: actual packing, actual selected separators, exact
domain, and a closed arithmetic proof. -/
theorem excludes (r : FixedRow) (hv : r.spec.valid) (hcheck : r.check=true)
    {R : ℝ} (P : NormalizedPacking R) (hs : r.spec.Realized P)
    (hdom : r.InDomain (P.helperAngle 2) (P.helperAngle 4) P.diagonalAngle) : False := by
  have hp := r.positive hcheck hdom
  have hn := r.spec.defect_nonpos_of_packing hv P hs
  linarith

end FixedRow
end SquaresInCircles.Six.Stress
