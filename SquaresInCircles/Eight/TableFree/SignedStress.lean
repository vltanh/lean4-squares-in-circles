module

public import SquaresInCircles.Eight.TableFree.CircleGeometry
public import SquaresInCircles.Common.DiskSupport

/-!
# Exact signed stresses for the original seven neighboring inequalities

Uncompiled source draft. A stress here is a finite positive weighted sum of
the seven actual signed separators. The force identity is proved before
any support estimate. In particular, a zero force removes a square without
making any assumption about its sign, radial kind, or circle equality.

All coefficients below are formulas in the actual edge angles. There is no
angle subdivision, owner certificate, capture theorem, or stationary input.
The final exclusion rule requires a separately proved positive analytic
defect; the rule itself does not assert such positivity.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree
open Candidate

namespace SignedStress

def previous : Vertex → Vertex := ![6,0,1,2,3,4,5]

@[simp] theorem next_previous (i : Vertex) : next (previous i)=i := by
  fin_cases i <;> rfl

@[simp] theorem previous_next (i : Vertex) : previous (next i)=i := by
  fin_cases i <;> rfl

/-- Coefficients of the source center `(a,y)`, in signed own coordinates. -/
def source (quarter : ℤ) (d : ℝ) (j : Fin 4) : Point :=
  if quarter=0 then
    ![(0,1),(-Real.cos d,Real.sin d),(Real.sin d,Real.cos d),(1,0)] j
  else
    ![(0,1),(Real.sin d,Real.cos d),(Real.cos d,-Real.sin d),(1,0)] j

/-- Coefficients of the target center, with the same physical orientation. -/
def target (quarter : ℤ) (d : ℝ) (j : Fin 4) : Point :=
  if quarter=0 then
    ![(Real.sin d,-Real.cos d),(1,0),(0,-1),(-Real.cos d,-Real.sin d)] j
  else
    ![(Real.cos d,Real.sin d),(1,0),(0,-1),(Real.sin d,-Real.cos d)] j

def work (v : Point) (p : SignedPoint) : ℝ := v.1*p.a+v.2*p.y

def force (C : SignedCycle) (owner : Vertex → Fin 4)
    (weight : Vertex → ℝ) (i : Vertex) : Point :=
  add (scale (weight i) (source (word i) (delta C.theta i) (owner i)))
    (scale (weight (previous i))
      (target (word (previous i)) (delta C.theta (previous i)) (owner (previous i))))

def demand (C : SignedCycle) (weight : Vertex → ℝ) : ℝ :=
  ∑ i, weight i*edgeWidth (delta C.theta i)

/-- The exact far-corner support, allowing either sign of both force entries. -/
def circleSupport (R : ℝ) (v : Point) : ℝ :=
  R*Real.sqrt (v.1^2+v.2^2)-(|v.1|+|v.2|)/2

def defect (C : SignedCycle) (owner : Vertex → Fin 4)
    (weight : Vertex → ℝ) (R : ℝ) : ℝ :=
  demand C weight-∑ i, circleSupport R (force C owner weight i)

theorem edge_linear (C : SignedCycle) (i : Vertex) (j : Fin 4) :
    C.edge i j=work (source (word i) (delta C.theta i) j) (C.point i)+
      work (target (word i) (delta C.theta i) j) (C.point (next i)) := by
  unfold SignedCycle.edge source target
  split_ifs <;> fin_cases j <;>
    simp [zeroProjection,quarterProjection,work] <;> ring

/-- Reindexing the incoming terms is just the seven-cycle incidence law. -/
theorem sum_force_work (C : SignedCycle) (owner : Vertex → Fin 4)
    (weight : Vertex → ℝ) :
    (∑ i, weight i*C.edge i (owner i))=
      ∑ i, work (force C owner weight i) (C.point i) := by
  simp_rw [edge_linear]
  simp only [force,work,add,scale]
  simp [Fin.sum_univ_succ,previous,next]
  ring

/-- Weak contacts remain weak; positivity is only needed for the weights. -/
theorem weighted_separation {C : SignedCycle} {owner : Vertex → Fin 4}
    {weight : Vertex → ℝ} (hw : ∀ i,0≤weight i)
    (hf : ∀ i,C.Feasible i (owner i)) :
    demand C weight≤∑ i,work (force C owner weight i) (C.point i) := by
  rw [← sum_force_work]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  have hi := hf i
  change 0≤C.edge i (owner i)-edgeWidth (delta C.theta i) at hi
  linarith

theorem work_le_circleSupport {p : SignedPoint} {R : ℝ}
    (hR : 0≤R) (hs : p.Sorted) (hc : p.Contained (R^2)) (v : Point) :
    work v p≤circleSupport R v := by
  have hbox : (|p.a|+1/2)^2+(|p.y|+1/2)^2≤R^2 := by
    rw [abs_of_pos hs.1]
    exact hc
  exact box_vertex_support hR hbox v.1 v.2

/-- The stronger one-sided support keeps a known signed tangent rather
than taking an absolute value of its force coefficient. -/
theorem work_le_signed_support {p : SignedPoint} {R : ℝ}
    (hR : 0≤R) (hc : p.Contained (R^2)) {sign : ℝ}
    (hsign : sign=1 ∨ sign= -1) (hy : sign*p.y=|p.y|) (v : Point) :
    work v p≤R*Real.sqrt (v.1^2+v.2^2)-(v.1+sign*v.2)/2 := by
  have hsq : sign^2=1 := by rcases hsign with rfl | rfl <;> norm_num
  have hb := dot_le_radius (v := (v.1,sign*v.2))
    (p := (p.a+1/2,|p.y|+1/2)) hR hc
  have hnorm : v.1^2+(sign*v.2)^2=v.1^2+v.2^2 := by
    rw [mul_pow,hsq,one_mul]
  simp only [dot,vectorLength,normSq,hnorm] at hb
  have hcancel : sign*|p.y|=p.y := by
    rw [← hy]
    calc
      sign*(sign*p.y)=sign^2*p.y := by ring
      _=p.y := by rw [hsq,one_mul]
  have hlinear : v.1*(p.a+1/2)+(sign*v.2)*(|p.y|+1/2)=
      work v p+(v.1+sign*v.2)/2 := by
    dsimp [work]
    linear_combination v.2*hcancel
  linarith

theorem stress_le_zero {C : SignedCycle} {owner : Vertex → Fin 4}
    {weight : Vertex → ℝ} {R : ℝ} (hR : 0≤R)
    (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained (R^2))
    (hw : ∀ i,0≤weight i) (hf : ∀ i,C.Feasible i (owner i)) :
    defect C owner weight R≤0 := by
  have hsep := weighted_separation hw hf
  have hsupport : (∑ i,work (force C owner weight i) (C.point i))≤
      ∑ i,circleSupport R (force C owner weight i) := by
    exact Finset.sum_le_sum fun i _ => work_le_circleSupport hR (hs i) (hc i) _
  unfold defect
  linarith

/-- An analytic estimate may use a larger support radius; the input
points and their actual boundary labels are never moved or relabeled. -/
theorem stress_le_zero_at_cap {C : SignedCycle} {owner : Vertex → Fin 4}
    {weight : Vertex → ℝ} {q Q : ℝ} (hQ : 0≤Q) (hq : q≤Q)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hw : ∀ i,0≤weight i) (hf : ∀ i,C.Feasible i (owner i)) :
    defect C owner weight (Real.sqrt Q)≤0 := by
  apply stress_le_zero (Real.sqrt_nonneg _) hs _ hw hf
  intro i
  rw [Real.sq_sqrt hQ]
  exact (hc i).trans hq

theorem impossible_of_positive_defect {C : SignedCycle} {owner : Vertex → Fin 4}
    {weight : Vertex → ℝ} {R : ℝ} (hR : 0≤R)
    (hs : ∀ i,(C.point i).Sorted)
    (hc : ∀ i,(C.point i).Contained (R^2))
    (hw : ∀ i,0≤weight i) (hf : ∀ i,C.Feasible i (owner i))
    (hpositive : 0<defect C owner weight R) : False :=
  (not_lt_of_ge (stress_le_zero hR hs hc hw hf)) hpositive

@[simp] theorem work_zero (p : SignedPoint) : work (0,0) p=0 := by
  simp [work]

@[simp] theorem circleSupport_zero (R : ℝ) : circleSupport R (0,0)=0 := by
  simp [circleSupport]

theorem force_independent_of_points (C D : SignedCycle)
    (hθ : C.theta=D.theta) (owner : Vertex → Fin 4) (weight : Vertex → ℝ) :
    force C owner weight=force D owner weight := by
  funext i
  simp only [force,hθ]

/-- One may substitute a sharper exact bound for a flat-core point, or
zero for a point whose force cancels. This is an ordinary finite sum. -/
theorem weighted_separation_le {C : SignedCycle} {owner : Vertex → Fin 4}
    {weight bound : Vertex → ℝ} (hw : ∀ i,0≤weight i)
    (hf : ∀ i,C.Feasible i (owner i))
    (hb : ∀ i,work (force C owner weight i) (C.point i)≤bound i) :
    demand C weight≤∑ i,bound i :=
  (weighted_separation hw hf).trans (Finset.sum_le_sum fun i _ => hb i)

end SignedStress
end SquaresInCircles.Eight.TableFree
