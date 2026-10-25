module

public import SquaresInCircles.Common.DiskSupport
public import SquaresInCircles.Eight.Frames.Signed.Coordinates

/-!
# Eight squares: signed stresses on the seven-cycle

A stress puts nonnegative weights on the seven edges of a signed cycle, each along the axis of
its owner. The slack of an edge is linear in its two signed points, with coefficients that are
formulas in the frame step of the edge (`source`, `target`, `edge_linear`), so the weighted sum
of the projections is the sum of the works of the forces on the seven points (`force`,
`sum_force_work`), and the weighted separations give `demand ≤ ∑ works`
(`weighted_separation`). The work of a force on a point contained at the level `R²` is at most
the far-corner support `circleSupport R v`, for either sign of both entries
(`work_le_circleSupport`), and at most a sharper one-sided support when the sign of the tangent
of the point is known (`work_le_signed_support`); a zero force contributes nothing, whatever the
sign, the radial kind or the circle of its point. The demand less the supports is the `defect`;
a stress excludes a configuration once its defect is proved positive (`weighted_separation_le`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open Candidate

namespace SignedStress

def previous : Vertex → Vertex := ![6,0,1,2,3,4,5]

@[simp] theorem next_previous (i : Vertex) : next (previous i)=i := by
  fin_cases i <;> rfl

@[simp] theorem previous_next (i : Vertex) : previous (next i)=i := by
  fin_cases i <;> rfl

/-- Coefficients of the source centre `(a, y)`, in the signed coordinates of its own frame. -/
def source (quarter : ℤ) (d : ℝ) (j : Fin 4) : Point :=
  if quarter=0 then
    ![(0,1),(-Real.cos d,Real.sin d),(Real.sin d,Real.cos d),(1,0)] j
  else
    ![(0,1),(Real.sin d,Real.cos d),(Real.cos d,-Real.sin d),(1,0)] j

/-- Coefficients of the target centre, in the same orientation. -/
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

/-- The far-corner support `R |v| - (|v₁| + |v₂|)/2`, for either sign of both entries of `v`. -/
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

/-- The weighted sum of the projections is the sum of the works of the forces: each edge acts on
its two ends. -/
theorem sum_force_work (C : SignedCycle) (owner : Vertex → Fin 4)
    (weight : Vertex → ℝ) :
    (∑ i, weight i*C.edge i (owner i))=
      ∑ i, work (force C owner weight i) (C.point i) := by
  simp_rw [edge_linear]
  simp only [force,work,add,scale]
  simp [Fin.sum_univ_succ,previous,next]
  ring

/-- With nonnegative weights and feasible owners, the demand is at most the sum of the works; the
contacts may be weak. -/
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

/-- When the sign of the tangent of the point is known, the work is at most the one-sided support
`R |v| - (v₁ + sign · v₂)/2`. -/
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

@[simp] theorem work_zero (p : SignedPoint) : work (0,0) p=0 := by
  simp [work]

@[simp] theorem circleSupport_zero (R : ℝ) : circleSupport R (0,0)=0 := by
  simp [circleSupport]

/-- The demand is at most the sum of any bounds of the works, such as a sharper bound for a point
on the flat side of the core, or `0` for a point whose force cancels. -/
theorem weighted_separation_le {C : SignedCycle} {owner : Vertex → Fin 4}
    {weight bound : Vertex → ℝ} (hw : ∀ i,0≤weight i)
    (hf : ∀ i,C.Feasible i (owner i))
    (hb : ∀ i,work (force C owner weight i) (C.point i)≤bound i) :
    demand C weight≤∑ i,bound i :=
  (weighted_separation hw hf).trans (Finset.sum_le_sum fun i _ => hb i)

end SignedStress
end SquaresInCircles.Eight
