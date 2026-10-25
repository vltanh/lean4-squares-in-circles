module

public import SquaresInCircles.Eight.Boundary.Candidate.Geometry

/-!
# Eight squares: signed coordinates of the seven-cycle

A signed point `(a, y)` stands for the centre of a square with coordinates `(a, -y)` in the frame
of the square (`SignedPoint`, `SignedPoint.square`); keeping `y` signed lets G, T or E pass
through `y = 0` without a change of frame. A point is sorted when `0 < a` and `|y| ≤ a`; it is
contained at the level `q`, outer, on the core, or on the boundary at that level (`Sorted`,
`Contained`, `Outer`, `Core`, `Boundary`), and the reflection `y ↦ -y` keeps all of these.

A signed cycle (`SignedCycle`) has a signed point and a real frame angle at each of the seven
positions H, G, A, B, T, D, E; `Candidate.word` records which neighbouring frames differ by a
quarter turn. The projections of an edge on its four forward axes (`zeroProjection`,
`quarterProjection`), less the width `edgeWidth`, are its slacks (`SignedCycle.slack`), and these
are the separating-axis slacks of the squares (`atFrame_slack`, `Physical/Cycle.lean`). A
boundary cycle with a candidate frame gives a signed cycle whose points are sorted, contained,
outside the core and on the boundary (`atFrame`, `atFrame_sorted`, `atFrame_contained`,
`atFrame_core`, `atFrame_boundary`). Reflecting a cycle and reversing its order gives a signed
cycle in which the owner `j` becomes `reflectedOwner j` (`reflected`, `reflected_feasible`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open Candidate

/-- The coordinates of a centre in the frame of its square; the second coordinate is `-y`. -/
@[ext] structure SignedPoint where
  a : ℝ
  y : ℝ
  deriving Inhabited

namespace SignedPoint

def circle (p : SignedPoint) : ℝ :=
  (p.a + 1/2)^2 + (|p.y| + 1/2)^2

def coreDistance (p : SignedPoint) : ℝ :=
  (max (p.a-1/2) 0)^2 + (max (|p.y|-1/2) 0)^2

def Sorted (p : SignedPoint) : Prop := 0 < p.a ∧ |p.y| ≤ p.a

def Contained (q : ℝ) (p : SignedPoint) : Prop := p.circle ≤ q

def AvoidsCore (p : SignedPoint) : Prop := (1/12 : ℝ)^2 ≤ p.coreDistance

def Outer (q : ℝ) (p : SignedPoint) : Prop := p.circle = q

def Core (p : SignedPoint) : Prop := p.coreDistance = (1/12 : ℝ)^2

def Boundary (q : ℝ) (p : SignedPoint) : Prop := p.Outer q ∨ p.Core

def reflect (p : SignedPoint) : SignedPoint := ⟨p.a,-p.y⟩

@[simp] theorem reflect_reflect (p : SignedPoint) : p.reflect.reflect=p := by
  cases p
  simp [reflect]

@[simp] theorem reflect_circle (p : SignedPoint) : p.reflect.circle=p.circle := by
  simp [reflect,circle]

@[simp] theorem reflect_coreDistance (p : SignedPoint) :
    p.reflect.coreDistance=p.coreDistance := by
  simp [reflect,coreDistance]

@[simp] theorem reflect_sorted (p : SignedPoint) : p.reflect.Sorted ↔ p.Sorted := by
  simp [reflect,Sorted]

@[simp] theorem reflect_contained (p : SignedPoint) (q : ℝ) :
    p.reflect.Contained q ↔ p.Contained q := by
  simp [Contained]

@[simp] theorem reflect_avoidsCore (p : SignedPoint) :
    p.reflect.AvoidsCore ↔ p.AvoidsCore := by
  simp [AvoidsCore]

@[simp] theorem reflect_outer (p : SignedPoint) (q : ℝ) :
    p.reflect.Outer q ↔ p.Outer q := by
  simp [Outer]

@[simp] theorem reflect_core (p : SignedPoint) : p.reflect.Core ↔ p.Core := by
  simp [Core]

@[simp] theorem reflect_boundary (p : SignedPoint) (q : ℝ) :
    p.reflect.Boundary q ↔ p.Boundary q := by
  simp [Boundary]

/-- The square with this signed centre and the frame angle `t`. -/
def square (p : SignedPoint) (t : ℝ) : UnitSquare where
  center := (p.a*Real.cos t+p.y*Real.sin t,
    p.a*Real.sin t-p.y*Real.cos t)
  cosine := Real.cos t
  sine := Real.sin t
  unit := by nlinarith [Real.sin_sq_add_cos_sq t]

@[simp] theorem square_center (p : SignedPoint) (t : ℝ) :
    (p.square t).center=rotate (p.square t) (p.a,-p.y) := by
  ext <;> simp [square,rotate] <;> ring

@[simp] theorem square_alpha {p : SignedPoint} (hp : p.Sorted) (t : ℝ) :
    SquaresInCircles.alpha (p.square t) (0,0)=p.a := by
  have hid : localX (p.square t) (0,0)= -p.a := by
    simp only [localX,square]
    linear_combination (-p.a)*Real.sin_sq_add_cos_sq t
  rw [SquaresInCircles.alpha,hid,abs_neg,abs_of_pos hp.1]

@[simp] theorem square_beta (p : SignedPoint) (t : ℝ) :
    SquaresInCircles.beta (p.square t) (0,0)=|p.y| := by
  have hid : localY (p.square t) (0,0)=p.y := by
    simp only [localY,square]
    linear_combination p.y*Real.sin_sq_add_cos_sq t
  rw [SquaresInCircles.beta,hid]

theorem square_contained_iff {p : SignedPoint} (hp : p.Sorted) (q t : ℝ) :
    SqContained q (p.square t) ↔ p.Contained q := by
  simp [SqContained,square_alpha hp,square_beta,Contained,circle,
    SquaresInCircles.phi]

end SignedPoint

/-- The width is periodic under a quarter turn. -/
def edgeWidth (d : ℝ) : ℝ := pairWidth d

@[simp] theorem edgeWidth_zero : edgeWidth 0=1 := by
  norm_num [edgeWidth,pairWidth]

@[simp] theorem edgeWidth_neg (d : ℝ) : edgeWidth (-d)=edgeWidth d := by
  simp [edgeWidth,pairWidth]

@[simp] theorem edgeWidth_quarter (d : ℝ) :
    pairWidth (Real.pi/2+d)=edgeWidth d := by
  have hs : Real.sin (Real.pi/2+d)=Real.cos d := by
    rw [add_comm]; exact Real.sin_add_pi_div_two d
  have hc : Real.cos (Real.pi/2+d)= -Real.sin d := by
    rw [add_comm]; exact Real.cos_add_pi_div_two d
  rw [edgeWidth,pairWidth,pairWidth,hs,hc,abs_neg]
  ring

theorem edgeWidth_ge_one (d : ℝ) : 1 ≤ edgeWidth d := by
  have h := one_le_abs_cos_add_abs_sin d
  unfold edgeWidth pairWidth
  linarith

/-- On an edge with quarter increment zero, the projections on the four forward axes, in the
order sourceY, targetX, targetY, -sourceX. -/
def zeroProjection (p r : SignedPoint) (d : ℝ) : Fin 4 → ℝ :=
  ![p.y+r.a*Real.sin d-r.y*Real.cos d,
    r.a-p.a*Real.cos d+p.y*Real.sin d,
    p.a*Real.sin d+p.y*Real.cos d-r.y,
    p.a-r.a*Real.cos d-r.y*Real.sin d]

def quarterProjection (p r : SignedPoint) (d : ℝ) : Fin 4 → ℝ :=
  ![p.y+r.a*Real.cos d+r.y*Real.sin d,
    r.a+p.a*Real.sin d+p.y*Real.cos d,
    p.a*Real.cos d-p.y*Real.sin d-r.y,
    p.a+r.a*Real.sin d-r.y*Real.cos d]

def zeroFeasible (p r : SignedPoint) (d : ℝ) (j : Fin 4) : Prop :=
  edgeWidth d ≤ zeroProjection p r d j

def quarterFeasible (p r : SignedPoint) (d : ℝ) (j : Fin 4) : Prop :=
  edgeWidth d ≤ quarterProjection p r d j

@[simp] theorem zeroProjection_aligned (p r : SignedPoint) :
    zeroProjection p r 0=![p.y-r.y,r.a-p.a,p.y-r.y,p.a-r.a] := by
  funext j
  fin_cases j <;> simp [zeroProjection]

@[simp] theorem quarterProjection_aligned (p r : SignedPoint) :
    quarterProjection p r 0=![p.y+r.a,r.a+p.y,p.a-r.y,p.a-r.y] := by
  funext j
  fin_cases j <;> simp [quarterProjection,add_comm]

theorem zero_owner_tie (p r : SignedPoint) :
    zeroFeasible p r 0 0 ↔ zeroFeasible p r 0 2 := by
  simp [zeroFeasible]

theorem quarter_low_tie (p r : SignedPoint) :
    quarterFeasible p r 0 0 ↔ quarterFeasible p r 0 1 := by
  simp [quarterFeasible,add_comm]

theorem quarter_high_tie (p r : SignedPoint) :
    quarterFeasible p r 0 2 ↔ quarterFeasible p r 0 3 := by
  simp [quarterFeasible]

/-- The owner that the reflection with the reversal of the roles makes of the owner `j`. -/
def reflectedOwner (j : Fin 4) : Fin 4 := ![2,3,0,1] j

@[simp] theorem reflectedOwner_involutive (j : Fin 4) :
    reflectedOwner (reflectedOwner j)=j := by
  fin_cases j <;> rfl

theorem zeroProjection_reflect (p r : SignedPoint) (d : ℝ) (j : Fin 4) :
    zeroProjection r.reflect p.reflect d (reflectedOwner j)=
      zeroProjection p r d j := by
  fin_cases j <;> simp [zeroProjection,SignedPoint.reflect,reflectedOwner] <;> ring

theorem quarterProjection_reflect (p r : SignedPoint) (d : ℝ) (j : Fin 4) :
    quarterProjection r.reflect p.reflect d (reflectedOwner j)=
      quarterProjection p r d j := by
  fin_cases j <;> simp [quarterProjection,SignedPoint.reflect,reflectedOwner] <;> ring

theorem zeroFeasible_reflect (p r : SignedPoint) (d : ℝ) (j : Fin 4) :
    zeroFeasible r.reflect p.reflect d (reflectedOwner j) ↔
      zeroFeasible p r d j := by
  simp only [zeroFeasible,zeroProjection_reflect]

theorem quarterFeasible_reflect (p r : SignedPoint) (d : ℝ) (j : Fin 4) :
    quarterFeasible r.reflect p.reflect d (reflectedOwner j) ↔
      quarterFeasible p r d j := by
  simp only [quarterFeasible,quarterProjection_reflect]

structure SignedCycle where
  point : Vertex → SignedPoint
  theta : Vertex → ℝ

namespace SignedCycle

def edge (C : SignedCycle) (i : Vertex) (j : Fin 4) : ℝ :=
  if Candidate.word i=0 then
    zeroProjection (C.point i) (C.point (next i)) (delta C.theta i) j
  else quarterProjection (C.point i) (C.point (next i)) (delta C.theta i) j

def slack (C : SignedCycle) (i : Vertex) (j : Fin 4) : ℝ :=
  C.edge i j-edgeWidth (delta C.theta i)

def Feasible (C : SignedCycle) (i : Vertex) (j : Fin 4) : Prop := 0 ≤ C.slack i j

def atFrame {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C) : SignedCycle :=
  ⟨fun i => ⟨C.a i,C.sigma i*C.b i⟩,F.theta⟩

/-- The slack of the signed cycle is the separating-axis margin `Candidate.margin` of the boundary
cycle. -/
theorem atFrame_slack {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (i : Vertex) (j : Fin 4) :
    (atFrame F).slack i j=Candidate.margin C F.theta i j := by
  fin_cases i <;> fin_cases j <;>
    simp [atFrame,slack,edge,zeroProjection,quarterProjection,
      Candidate.margin,forwardMargin,Candidate.phi,Candidate.word,
      edgeWidth,pairWidth,Real.cos_add,Real.sin_add] <;> ring

theorem atFrame_feasible {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (i : Vertex) (j : Fin 4) :
    (atFrame F).Feasible i j ↔
      (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
  rw [Feasible,atFrame_slack]
  exact (F.margin_nonneg_iff i j).symm

theorem atFrame_sorted {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (i : Vertex) : ((atFrame F).point i).Sorted := by
  refine ⟨C.a_pos i,?_⟩
  show |C.sigma i*C.b i| ≤ C.a i
  rw [signed_b_abs]
  exact C.b_le_a i

theorem atFrame_contained {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (i : Vertex) : ((atFrame F).point i).Contained q := by
  show (C.a i+1/2)^2+(|C.sigma i*C.b i|+1/2)^2 ≤ q
  rw [signed_b_abs]
  exact canonical_containment C i

theorem atFrame_core {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (i : Vertex) : ((atFrame F).point i).AvoidsCore := by
  show (1/12 : ℝ)^2 ≤ (max (C.a i-1/2) 0)^2+(max (|C.sigma i*C.b i|-1/2) 0)^2
  rw [signed_b_abs]
  exact canonical_core_distance C i

/-- The points lie on the boundary; the side and the corner of the core curve both contain their
common end. -/
theorem atFrame_boundary {q : ℝ} {C : BoundaryCycle q} (F : Candidate.Frame C)
    (i : Vertex) : ((atFrame F).point i).Boundary q := by
  have h := C.boundary i
  have hab : |((atFrame F).point i).y|=C.b i := signed_b_abs C i
  cases hk : C.kind i with
  | outer =>
      left
      rw [hk] at h
      show (C.a i+1/2)^2+(|((atFrame F).point i).y|+1/2)^2=q
      rw [hab]
      exact h
  | coreSide =>
      right
      rw [hk] at h
      obtain ⟨ha,hb⟩ := h
      show (max (C.a i-1/2) 0)^2+(max (|((atFrame F).point i).y|-1/2) 0)^2=(1/12 : ℝ)^2
      rw [hab,ha,max_eq_right (by linarith : C.b i-1/2 ≤ 0)]
      norm_num
  | coreCorner =>
      right
      rw [hk] at h
      obtain ⟨hb,hc⟩ := h
      show (max (C.a i-1/2) 0)^2+(max (|((atFrame F).point i).y|-1/2) 0)^2=(1/12 : ℝ)^2
      rw [hab,max_eq_left (by linarith [C.b_le_a i] : 0 ≤ C.a i-1/2),
        max_eq_left (by linarith : 0 ≤ C.b i-1/2)]
      exact hc

/-- The reflection of the cycle reverses the order: it exchanges H and D, G and T, A and B, and
fixes E, whose sign is not normalized again. -/
def reflectedIndex : Vertex → Vertex := ![5,4,3,2,1,0,6]

def reflected (C : SignedCycle) : SignedCycle where
  point i := (C.point (reflectedIndex i)).reflect
  theta i := C.theta B-C.theta (reflectedIndex i)

@[simp] theorem reflectedIndex_involutive (i : Vertex) :
    reflectedIndex (reflectedIndex i)=i := by
  fin_cases i <;> rfl

theorem reflectedIndex_next (i : Vertex) :
    next (reflectedIndex (next i))=reflectedIndex i := by
  fin_cases i <;> decide

theorem reflected_word (i : Vertex) :
    Candidate.word (reflectedIndex (next i))=Candidate.word i := by
  fin_cases i <;> rfl

theorem reflected_delta (C : SignedCycle) (i : Vertex) :
    delta C.reflected.theta i=delta C.theta (reflectedIndex (next i)) := by
  dsimp [reflected,delta]
  rw [reflectedIndex_next]
  ring

theorem reflected_slack (C : SignedCycle) (i : Vertex) (j : Fin 4) :
    C.reflected.slack i (reflectedOwner j)=
      C.slack (reflectedIndex (next i)) j := by
  simp only [slack,edge,reflected_delta,reflected_word]
  by_cases hi : Candidate.word i=0
  · rw [ite_eq_left hi,ite_eq_left hi]
    simp only [reflected,reflectedIndex_next,zeroProjection_reflect]
  · rw [ite_eq_right hi,ite_eq_right hi]
    simp only [reflected,reflectedIndex_next,quarterProjection_reflect]

theorem reflected_feasible (C : SignedCycle) (i : Vertex) (j : Fin 4) :
    C.reflected.Feasible i (reflectedOwner j) ↔
      C.Feasible (reflectedIndex (next i)) j := by
  simp only [Feasible,reflected_slack]

end SignedCycle
end SquaresInCircles.Eight