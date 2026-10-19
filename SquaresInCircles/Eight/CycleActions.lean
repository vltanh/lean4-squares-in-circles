module

public import SquaresInCircles.Eight.BoundaryGeometry

/-!
# Eight squares: the dihedral actions on a cycle

A `CycleAction` renumbers the seven squares by a cyclic shift, possibly reversed, and moves the
plane by a rotation about the origin, preceded by the reflection in the diagonal when the order
is reversed. These motions keep containment, the core and the separations
(`motionSquare_contained`, `reflectedAxis_feasible_iff`), and they turn neighbour cycles, polar
orders, boundary cycles, radius expansions and quarter lifts into objects of the same kind
(`CycleAction.neighbor`, `CycleAction.polarOrder`, `CycleAction.boundary`,
`CycleAction.radiusExpansion`, `QuarterLift.act`).

Reindexing a reflected cycle reverses both endpoints of an edge: the witness of the edge is
first reversed, and then the sign of its secondary axis is reflected (`CycleAction.axis`). The
real centre directions are lifted with an explicit wrap integer (`CycleAction.lift`), so the
integer quarter words transform by the action on the edges (`CycleAction.quarter_increment`),
not on the vertices. The file ends with a quarter lift from the bound on the frame costs
(`quarterLift_of_cost`) and its pullback through a radius expansion (`QuarterLift.pullback`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight

def reflectionSign (b : Bool) : ℝ := if b then -1 else 1

def reflectionSignInt (b : Bool) : ℤ := if b then -1 else 1

def reflectionSquare (b : Bool) (K : UnitSquare) : UnitSquare :=
  if b then reflectDiagonalSquare K else K

def reflectionPoint (b : Bool) (p : Point) : Point :=
  if b then diagonalPoint p else p

def motionPoint (θ : ℝ) (b : Bool) (p : Point) : Point :=
  (frameEquiv (0,0) (θ:Direction)).symm (reflectionPoint b p)

def motionInverse (θ : ℝ) (b : Bool) (p : Point) : Point :=
  reflectionPoint b (frameEquiv (0,0) (θ:Direction) p)

def motionSquare (θ : ℝ) (b : Bool) (K : UnitSquare) : UnitSquare :=
  pullSquare (0,0) (θ:Direction) (reflectionSquare b K)

lemma motionSquare_center (θ : ℝ) (b : Bool) (K : UnitSquare) :
    (motionSquare θ b K).center=motionPoint θ b K.center := by
  cases b <;> rfl

lemma motion_right_inverse (θ : ℝ) (b : Bool) (p : Point) :
    motionPoint θ b (motionInverse θ b p)=p := by
  cases b <;> simp [motionInverse,motionPoint,reflectionPoint,-frameEquiv_apply]

lemma motionSquare_open (θ : ℝ) (b : Bool) (K : UnitSquare) (p : Point) :
    openSquare (motionSquare θ b K) p ↔ openSquare K (motionInverse θ b p) := by
  cases b <;> simp [motionSquare,reflectionSquare,motionInverse,reflectionPoint,
    pullSquare_open,reflectDiagonal_open]

lemma motionSquare_closed (θ : ℝ) (b : Bool) (K : UnitSquare) (p : Point) :
    closedSquare (motionSquare θ b K) p ↔ closedSquare K (motionInverse θ b p) := by
  cases b <;> simp [motionSquare,reflectionSquare,motionInverse,reflectionPoint,
    pullSquare_closed,reflectDiagonal_closed]

/-- The motion in coordinates: the inverse rotation applied to the reflected point. -/
lemma CycleActions.motionPoint_eq (θ : ℝ) (b : Bool) (p : Point) :
    motionPoint θ b p=
      (Real.cos θ*(reflectionPoint b p).1+Real.sin θ*(reflectionPoint b p).2,
       -Real.sin θ*(reflectionPoint b p).1+Real.cos θ*(reflectionPoint b p).2) := by
  apply Prod.ext <;> simp [motionPoint,frameEquiv]

lemma motionPoint_norm (θ : ℝ) (b : Bool) (p : Point) :
    normSq (motionPoint θ b p)=normSq p := by
  cases b <;> simp [CycleActions.motionPoint_eq,reflectionPoint,diagonalPoint,normSq] <;>
    linear_combination (p.1^2+p.2^2)*Real.sin_sq_add_cos_sq θ

lemma motionInverse_norm (θ : ℝ) (b : Bool) (p : Point) :
    normSq (motionInverse θ b p)=normSq p := by
  have h := motionPoint_norm θ b (motionInverse θ b p)
  rw [motion_right_inverse] at h
  exact h.symm

lemma motionPoint_sub (θ : ℝ) (b : Bool) (p r : Point) :
    motionPoint θ b (sub p r)=sub (motionPoint θ b p) (motionPoint θ b r) := by
  cases b <;> apply Prod.ext <;>
    simp [motionPoint,reflectionPoint,diagonalPoint,frameEquiv,pointInDirection,sub] <;> ring

lemma motionPoint_dot (θ : ℝ) (b : Bool) (p r : Point) :
    dot (motionPoint θ b p) (motionPoint θ b r)=dot p r := by
  cases b <;> simp [CycleActions.motionPoint_eq,reflectionPoint,diagonalPoint,dot] <;>
    linear_combination (p.1*r.1+p.2*r.2)*Real.sin_sq_add_cos_sq θ

lemma motionSquare_contained {q : ℝ} (θ : ℝ) (b : Bool) {K : UnitSquare}
    (h : SqContained q K) : SqContained q (motionSquare θ b K) := by
  have hq : 0 ≤ q := by exact (show 0 ≤ phi (alpha K (0,0)) (beta K (0,0)) by unfold phi; positivity).trans h
  apply (SqContained.iff_points hq _).2
  intro p hp
  have hh := (SqContained.iff_points hq K).1 h _ ((motionSquare_closed θ b K p).1 hp)
  rwa [motionInverse_norm] at hh

lemma motionSquare_core (θ : ℝ) (b : Bool) {K : UnitSquare}
    (h : CoreAvoiding K) : CoreAvoiding (motionSquare θ b K) := by
  intro p hp
  have hh := h _ ((motionSquare_closed θ b K p).1 hp)
  rwa [motionInverse_norm] at hh

lemma motionSquare_containsCore (θ : ℝ) (b : Bool) {K : UnitSquare}
    (h : ContainsCore K) : ContainsCore (motionSquare θ b K) := by
  intro p hp
  apply (motionSquare_open θ b K p).2
  exact h _ (by simpa [motionInverse_norm] using hp)

lemma motionSquare_sameFrame (θ : ℝ) (b : Bool) {K J : UnitSquare}
    (h : SameFrame K J) : SameFrame (motionSquare θ b K) (motionSquare θ b J) := by
  cases b <;> simp [SameFrame,motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,h.1,h.2]

def reflectedAxis (b : Bool) (a : SignedAxis) : SignedAxis :=
  if b then match a.owner with
    | .sourceX | .targetX => a
    | .sourceY | .targetY => ⟨a.owner,a.sign.flip⟩
  else a

lemma reflectedAxis_normal (θ : ℝ) (b : Bool) (a : SignedAxis) (K J : UnitSquare) :
    (reflectedAxis b a).normal (motionSquare θ b K) (motionSquare θ b J)=
      motionPoint θ b (a.normal K J) := by
  cases b <;> cases a with
  | mk owner sign =>
    cases owner <;> cases sign <;> apply Prod.ext <;>
      simp [reflectedAxis,motionSquare,motionPoint,reflectionSquare,reflectionPoint,
        pullSquare,reflectDiagonalSquare,diagonalPoint,frameEquiv,pointInDirection,
        SignedAxis.normal,AxisOwner.normal,AxisSign.value,AxisSign.flip,e,f,scale] <;> ring

lemma motionSquare_relativeC (θ : ℝ) (b : Bool) (K J : UnitSquare) :
    relativeC (motionSquare θ b K) (motionSquare θ b J)=relativeC K J := by
  cases b <;> simp [motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,relativeC] <;>
    linear_combination (K.cosine*J.cosine+K.sine*J.sine)*Real.sin_sq_add_cos_sq θ

lemma motionSquare_relativeS (θ : ℝ) (b : Bool) (K J : UnitSquare) :
    relativeS (motionSquare θ b K) (motionSquare θ b J)=reflectionSign b*relativeS K J := by
  cases b
  · simp [motionSquare,reflectionSquare,pullSquare,relativeS,reflectionSign]
    linear_combination (K.cosine*J.sine-K.sine*J.cosine)*Real.sin_sq_add_cos_sq θ
  · simp [motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,relativeS,reflectionSign]
    linear_combination (K.sine*J.cosine-K.cosine*J.sine)*Real.sin_sq_add_cos_sq θ

lemma motionSquare_threshold (θ : ℝ) (b : Bool) (K J : UnitSquare) :
    SAT.threshold (motionSquare θ b K) (motionSquare θ b J)=SAT.threshold K J := by
  rw [SAT.threshold,motionSquare_relativeC,motionSquare_relativeS]
  cases b <;> simp [reflectionSign,SAT.threshold]

lemma reflectedAxis_projection (θ : ℝ) (b : Bool) (a : SignedAxis) (K J : UnitSquare) :
    (reflectedAxis b a).projection (motionSquare θ b K) (motionSquare θ b J)=a.projection K J := by
  unfold SignedAxis.projection
  rw [reflectedAxis_normal,motionSquare_center,motionSquare_center,← motionPoint_sub,motionPoint_dot]

lemma reflectedAxis_feasible_iff (θ : ℝ) (b : Bool) (a : SignedAxis) (K J : UnitSquare) :
    (reflectedAxis b a).Feasible (motionSquare θ b K) (motionSquare θ b J) ↔ a.Feasible K J := by
  simp only [SignedAxis.Feasible,reflectedAxis_projection,motionSquare_threshold]

structure CycleAction where
  shift : Vertex
  reversed : Bool
  rotation : ℝ

def CycleAction.index (G : CycleAction) : Equiv.Perm Vertex where
  toFun i := if G.reversed then G.shift-i else i+G.shift
  invFun i := if G.reversed then G.shift-i else i-G.shift
  left_inv i := by cases h : G.reversed <;> simp [h] <;> abel
  right_inv i := by cases h : G.reversed <;> simp [h] <;> abel

def CycleAction.edge (G : CycleAction) (i : Vertex) : Vertex :=
  if G.reversed then G.index (next i) else G.index i

def CycleAction.wrap (G : CycleAction) (i : Vertex) : ℤ :=
  if G.reversed then if (G.index 0).val<(G.index i).val then 1 else 0
  else if (G.index i).val<(G.index 0).val then 1 else 0

def CycleAction.lift (G : CycleAction) (β : Vertex → ℝ) (i : Vertex) : ℝ :=
  reflectionSign G.reversed*β (G.index i)+(G.wrap i:ℝ)*(2*Real.pi)+
    (if G.reversed then Real.pi/2 else 0)-G.rotation

def CycleAction.axis (G : CycleAction) (a : SignedAxis) : SignedAxis :=
  reflectedAxis G.reversed (if G.reversed then a.reverse else a)

lemma CycleAction.index_next (G : CycleAction) (i : Vertex) :
    G.index (next i)=if G.reversed then prev (G.index i) else next (G.index i) := by
  cases h : G.reversed <;> simp [CycleAction.index,next,prev,h] <;> abel

lemma CycleAction.edge_endpoints (G : CycleAction) (i : Vertex) :
    (if G.reversed then (G.index (next i),G.index i) else (G.index i,G.index (next i)))=
      (G.edge i,next (G.edge i)) := by
  cases h : G.reversed <;> simp [CycleAction.edge,h,G.index_next,next_prev]

/-- The wrap table over all shifts, orientations and edges: the wrap integer
jumps exactly on the edge whose image crosses the last edge. -/
lemma CycleActions.wrap_table : ∀ (s : Vertex) (rev : Bool) (i : Vertex),
    (CycleAction.wrap ⟨s,rev,0⟩ (next i)-CycleAction.wrap ⟨s,rev,0⟩ i+(if i=6 then 1 else 0) : ℤ)=
      if CycleAction.edge ⟨s,rev,0⟩ i=6 then 1 else 0 := by
  decide

lemma CycleActions.wrap_step (G : CycleAction) (i : Vertex) :
    G.wrap (next i)-G.wrap i+(if i=6 then 1 else 0)=if G.edge i=6 then 1 else 0 :=
  CycleActions.wrap_table G.shift G.reversed i

lemma CycleAction.lift_gap (G : CycleAction) (β : Vertex → ℝ) (i : Vertex) :
    angleGap (G.lift β) i=angleGap β (G.edge i) := by
  have hw : ((G.wrap (next i):ℝ)-(G.wrap i:ℝ)+(if i=6 then 1 else 0))=
      if G.edge i=6 then 1 else 0 := by
    have h := congrArg (fun z : ℤ => (z:ℝ)) (CycleActions.wrap_step G i)
    push_cast [apply_ite (fun z : ℤ => (z:ℝ))] at h
    exact h
  have hgap : angleGap (G.lift β) i=reflectionSign G.reversed*(β (G.index (next i))-β (G.index i))+
      ((G.wrap (next i):ℝ)-(G.wrap i:ℝ)+(if i=6 then 1 else 0))*(2*Real.pi) := by
    simp only [angleGap,CycleAction.lift]
    split_ifs <;> ring
  rw [hgap,hw]
  have he := G.edge_endpoints i
  cases h : G.reversed
  · simp only [h,Bool.false_eq_true,ite_false,Prod.mk.injEq] at he
    rw [he.1,he.2]
    simp only [angleGap,reflectionSign,Bool.false_eq_true,ite_false]
    split_ifs <;> ring
  · simp only [h,ite_true,Prod.mk.injEq] at he
    rw [he.1,he.2]
    simp only [angleGap,reflectionSign,ite_true]
    split_ifs <;> ring

lemma CycleAction.lift_cos (G : CycleAction) (β : Vertex → ℝ) (i : Vertex) :
    Real.cos (G.lift β i)=Real.cos
      (reflectionSign G.reversed*β (G.index i)+(if G.reversed then Real.pi/2 else 0)-G.rotation) := by
  cases h : G.reversed <;>
    simp [CycleAction.lift,CycleAction.wrap,h,reflectionSign] <;>
    split <;> simp [Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub] <;> ring

lemma CycleAction.lift_sin (G : CycleAction) (β : Vertex → ℝ) (i : Vertex) :
    Real.sin (G.lift β i)=Real.sin
      (reflectionSign G.reversed*β (G.index i)+(if G.reversed then Real.pi/2 else 0)-G.rotation) := by
  cases h : G.reversed <;>
    simp [CycleAction.lift,CycleAction.wrap,h,reflectionSign] <;>
    split <;> simp [Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub] <;> ring

lemma motionPoint_polar (θ : ℝ) (b : Bool) (r β : ℝ) :
    motionPoint θ b (r*Real.cos β,r*Real.sin β)=
      (r*Real.cos (reflectionSign b*β+(if b then Real.pi/2 else 0)-θ),
       r*Real.sin (reflectionSign b*β+(if b then Real.pi/2 else 0)-θ)) := by
  cases b <;> apply Prod.ext <;>
    simp [motionPoint,reflectionPoint,reflectionSign,diagonalPoint,frameEquiv,pointInDirection,
      Real.cos_sub,Real.sin_sub,Real.cos_add,Real.sin_add] <;> ring

lemma motionSquare_rotate (θ : ℝ) (b : Bool) (K : UnitSquare) (a c : ℝ) :
    motionPoint θ b (rotate K (a,c))=
      rotate (motionSquare θ b K) (a,reflectionSign b*c) := by
  cases b <;> apply Prod.ext <;>
    simp [motionPoint,motionSquare,reflectionSquare,reflectionPoint,reflectionSign,
      diagonalPoint,frameEquiv,pointInDirection,pullSquare,reflectDiagonalSquare,rotate] <;> ring

lemma CycleAction.pair_feasible {q : ℝ} (G : CycleAction) (C : NeighborCycle q)
    (i : Vertex) (a : SignedAxis) (ha : a.Feasible (C.square (G.edge i)) (C.square (next (G.edge i)))) :
    (G.axis a).Feasible (motionSquare G.rotation G.reversed (C.square (G.index i)))
      (motionSquare G.rotation G.reversed (C.square (G.index (next i)))) := by
  have he := G.edge_endpoints i
  cases h : G.reversed
  · simp only [h,Bool.false_eq_true,ite_false,Prod.mk.injEq] at he
    simpa [CycleAction.axis,h,he.1,he.2] using
      (reflectedAxis_feasible_iff G.rotation false a _ _).2 ha
  · simp only [h,ite_true,Prod.mk.injEq] at he
    have hr := (reverse_feasible_iff a _ _).2 ha
    simpa [CycleAction.axis,h,he.1,he.2] using
      (reflectedAxis_feasible_iff G.rotation true a.reverse _ _).2 hr

def CycleAction.neighbor {q : ℝ} (G : CycleAction) (C : NeighborCycle q) : NeighborCycle q where
  square i := motionSquare G.rotation G.reversed (C.square (G.index i))
  contained i := motionSquare_contained G.rotation G.reversed (C.contained (G.index i))
  core i := motionSquare_core G.rotation G.reversed (C.core (G.index i))
  selected i := G.axis (C.selected (G.edge i))
  feasible i := G.pair_feasible C i _ (C.feasible (G.edge i))

def CycleAction.polarOrder {q : ℝ} (G : CycleAction) {C : NeighborCycle q} (O : PolarOrder C) :
    PolarOrder (G.neighbor C) where
  beta := G.lift O.beta
  center_cos i := by
    have hc : (C.square (G.index i)).center=
        (Real.sqrt (normSq (C.square (G.index i)).center)*Real.cos (O.beta (G.index i)),
         Real.sqrt (normSq (C.square (G.index i)).center)*Real.sin (O.beta (G.index i))) :=
      Prod.ext (O.center_cos _) (O.center_sin _)
    have hp := motionPoint_polar G.rotation G.reversed
      (Real.sqrt (normSq (C.square (G.index i)).center)) (O.beta (G.index i))
    rw [← hc] at hp
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center.1=
      Real.sqrt (normSq (motionSquare G.rotation G.reversed (C.square (G.index i))).center)*
        Real.cos (G.lift O.beta i)
    rw [motionSquare_center,motionPoint_norm,G.lift_cos,hp]
  center_sin i := by
    have hc : (C.square (G.index i)).center=
        (Real.sqrt (normSq (C.square (G.index i)).center)*Real.cos (O.beta (G.index i)),
         Real.sqrt (normSq (C.square (G.index i)).center)*Real.sin (O.beta (G.index i))) :=
      Prod.ext (O.center_cos _) (O.center_sin _)
    have hp := motionPoint_polar G.rotation G.reversed
      (Real.sqrt (normSq (C.square (G.index i)).center)) (O.beta (G.index i))
    rw [← hc] at hp
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center.2=
      Real.sqrt (normSq (motionSquare G.rotation G.reversed (C.square (G.index i))).center)*
        Real.sin (G.lift O.beta i)
    rw [motionSquare_center,motionPoint_norm,G.lift_sin,hp]
  positive i := by rw [G.lift_gap]; exact O.positive _
  below_pi i := by rw [G.lift_gap]; exact O.below_pi _

def CycleAction.boundary {q : ℝ} (G : CycleAction) (C : BoundaryCycle q) : BoundaryCycle q where
  toNeighborCycle := G.neighbor C.toNeighborCycle
  kind i := C.kind (G.index i)
  a i := C.a (G.index i)
  b i := C.b (G.index i)
  sigma i := reflectionSign G.reversed*C.sigma (G.index i)
  a_pos i := C.a_pos _
  b_nonneg i := C.b_nonneg _
  b_le_a i := C.b_le_a _
  sigma_sign i := by
    cases h : G.reversed <;> rcases C.sigma_sign (G.index i) with hs|hs <;>
      simp [reflectionSign,h,hs]
  center_eq i := by
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center=
      rotate (motionSquare G.rotation G.reversed (C.square (G.index i)))
        (C.a (G.index i),-(reflectionSign G.reversed*C.sigma (G.index i))*C.b (G.index i))
    rw [motionSquare_center,C.center_eq,motionSquare_rotate]
    congr 2
    ring
  boundary i := C.boundary _
  beta := G.lift C.beta
  center_cos i := by
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center.1=_
    have hc : (C.square (G.index i)).center=
        (Real.sqrt (C.a (G.index i)^2+C.b (G.index i)^2)*Real.cos (C.beta (G.index i)),
         Real.sqrt (C.a (G.index i)^2+C.b (G.index i)^2)*Real.sin (C.beta (G.index i))) :=
      Prod.ext (C.center_cos _) (C.center_sin _)
    rw [motionSquare_center,G.lift_cos,hc,motionPoint_polar]
  center_sin i := by
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center.2=_
    have hc : (C.square (G.index i)).center=
        (Real.sqrt (C.a (G.index i)^2+C.b (G.index i)^2)*Real.cos (C.beta (G.index i)),
         Real.sqrt (C.a (G.index i)^2+C.b (G.index i)^2)*Real.sin (C.beta (G.index i))) :=
      Prod.ext (C.center_cos _) (C.center_sin _)
    rw [motionSquare_center,G.lift_sin,hc,motionPoint_polar]
  frame_cos i := by
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).cosine=_
    have ht : Real.arctan (reflectionSign G.reversed*C.sigma (G.index i)*C.b (G.index i)/
        C.a (G.index i))=reflectionSign G.reversed*Real.arctan (C.sigma (G.index i)*
        C.b (G.index i)/C.a (G.index i)) := by
      cases G.reversed <;> simp [reflectionSign,neg_div,Real.arctan_neg]
    have harg : G.lift C.beta i+Real.arctan (reflectionSign G.reversed*C.sigma (G.index i)*
        C.b (G.index i)/C.a (G.index i))=
        reflectionSign G.reversed*(C.beta (G.index i)+Real.arctan (C.sigma (G.index i)*
          C.b (G.index i)/C.a (G.index i)))+(if G.reversed then Real.pi/2 else 0)-G.rotation+
          (G.wrap i:ℝ)*(2*Real.pi) := by
      rw [ht,CycleAction.lift]
      ring
    rw [harg,Real.cos_add_int_mul_two_pi]
    cases h : G.reversed
    · simp only [motionSquare,reflectionSquare,pullSquare,Bool.false_eq_true,ite_false,
        Real.Angle.cos_coe,Real.Angle.sin_coe,C.frame_cos,C.frame_sin,reflectionSign,one_mul,
        add_zero]
      rw [Real.cos_sub]
      ring
    · simp only [motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,ite_true,
        Real.Angle.cos_coe,Real.Angle.sin_coe,C.frame_cos,C.frame_sin,reflectionSign]
      rw [show -1*(C.beta (G.index i)+Real.arctan (C.sigma (G.index i)*C.b (G.index i)/
          C.a (G.index i)))+Real.pi/2-G.rotation=Real.pi/2-((C.beta (G.index i)+
          Real.arctan (C.sigma (G.index i)*C.b (G.index i)/C.a (G.index i)))+G.rotation) by ring,
        Real.cos_pi_div_two_sub,Real.sin_add (C.beta (G.index i)+Real.arctan (C.sigma (G.index i)*
          C.b (G.index i)/C.a (G.index i))) G.rotation]
      ring
  frame_sin i := by
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).sine=_
    have ht : Real.arctan (reflectionSign G.reversed*C.sigma (G.index i)*C.b (G.index i)/
        C.a (G.index i))=reflectionSign G.reversed*Real.arctan (C.sigma (G.index i)*
        C.b (G.index i)/C.a (G.index i)) := by
      cases G.reversed <;> simp [reflectionSign,neg_div,Real.arctan_neg]
    have harg : G.lift C.beta i+Real.arctan (reflectionSign G.reversed*C.sigma (G.index i)*
        C.b (G.index i)/C.a (G.index i))=
        reflectionSign G.reversed*(C.beta (G.index i)+Real.arctan (C.sigma (G.index i)*
          C.b (G.index i)/C.a (G.index i)))+(if G.reversed then Real.pi/2 else 0)-G.rotation+
          (G.wrap i:ℝ)*(2*Real.pi) := by
      rw [ht,CycleAction.lift]
      ring
    rw [harg,Real.sin_add_int_mul_two_pi]
    cases h : G.reversed
    · simp only [motionSquare,reflectionSquare,pullSquare,Bool.false_eq_true,ite_false,
        Real.Angle.cos_coe,Real.Angle.sin_coe,C.frame_cos,C.frame_sin,reflectionSign,one_mul,
        add_zero]
      rw [Real.sin_sub]
      ring
    · simp only [motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,ite_true,
        Real.Angle.cos_coe,Real.Angle.sin_coe,C.frame_cos,C.frame_sin,reflectionSign]
      rw [show -1*(C.beta (G.index i)+Real.arctan (C.sigma (G.index i)*C.b (G.index i)/
          C.a (G.index i)))+Real.pi/2-G.rotation=Real.pi/2-((C.beta (G.index i)+
          Real.arctan (C.sigma (G.index i)*C.b (G.index i)/C.a (G.index i)))+G.rotation) by ring,
        Real.sin_pi_div_two_sub,Real.cos_add (C.beta (G.index i)+Real.arctan (C.sigma (G.index i)*
          C.b (G.index i)/C.a (G.index i))) G.rotation]
      ring
  gap_pos i := by rw [G.lift_gap]; exact C.gap_pos _
  gap_lt_pi i := by rw [G.lift_gap]; exact C.gap_lt_pi _

lemma CycleAction.tangent {q : ℝ} (G : CycleAction) (C : BoundaryCycle q) (i : Vertex) :
    (G.boundary C).tangent i=reflectionSign G.reversed*C.tangent (G.index i) := by
  dsimp [BoundaryCycle.tangent,CycleAction.boundary]
  ring

lemma CycleAction.alpha {q : ℝ} (G : CycleAction) (C : BoundaryCycle q) (i : Vertex) :
    (G.boundary C).alpha i=reflectionSign G.reversed*C.alpha (G.index i) := by
  unfold BoundaryCycle.alpha
  rw [G.tangent]
  cases h : G.reversed <;> simp [reflectionSign,h,Real.arctan_neg]

lemma CycleAction.canonical {q : ℝ} (G : CycleAction) (C : BoundaryCycle q) (i : Vertex) :
    (G.boundary C).canonicalAngle i=
      reflectionSign G.reversed*C.canonicalAngle (G.index i)+(G.wrap i:ℝ)*(2*Real.pi)+
        (if G.reversed then Real.pi/2 else 0)-G.rotation := by
  rw [BoundaryCycle.canonicalAngle,G.alpha]
  dsimp [CycleAction.boundary,CycleAction.lift,BoundaryCycle.canonicalAngle]
  ring

lemma CycleAction.axis_involutive (G : CycleAction) (a : SignedAxis) : G.axis (G.axis a)=a := by
  rcases G with ⟨s,rev,rot⟩
  rcases a with ⟨owner,sign⟩
  cases rev <;> cases owner <;> cases sign <;> rfl

lemma CycleAction.axis_feasible_iff {q : ℝ} (G : CycleAction) (C : BoundaryCycle q)
    (i : Vertex) (a : SignedAxis) :
    (G.axis a).Feasible ((G.boundary C).square i) ((G.boundary C).square (next i)) ↔
      a.Feasible (C.square (G.edge i)) (C.square (next (G.edge i))) := by
  change (G.axis a).Feasible (motionSquare G.rotation G.reversed (C.square (G.index i)))
      (motionSquare G.rotation G.reversed (C.square (G.index (next i)))) ↔ _
  have he := G.edge_endpoints i
  cases h : G.reversed
  · simp only [h,Bool.false_eq_true,ite_false,Prod.mk.injEq] at he
    rw [← he.2,← he.1]
    simpa [CycleAction.axis,h] using reflectedAxis_feasible_iff G.rotation false a _ _
  · simp only [h,ite_true,Prod.mk.injEq] at he
    rw [← he.2,← he.1]
    simpa [CycleAction.axis,h] using
      (reflectedAxis_feasible_iff G.rotation true a.reverse _ _).trans (reverse_feasible_iff a _ _)

def CycleAction.radiusExpansion {q r : ℝ} (G : CycleAction) {C : BoundaryCycle q} {D : BoundaryCycle r}
    (h : RadiusExpansion C D) : RadiusExpansion (G.boundary C) (G.boundary D) where
  same_kind := by funext i; exact congrFun h.same_kind (G.index i)
  same_frames i := motionSquare_sameFrame _ _ (h.same_frames (G.index i))
  same_rays := by simp only [CycleAction.boundary,h.same_rays]
  same_tangents := by funext i; rw [G.tangent,G.tangent,h.same_tangents]
  preserves_all_axes i a ha := by
    have hsource := (G.axis_feasible_iff C i (G.axis a)).1 (by simpa [G.axis_involutive] using ha)
    have htarget := h.preserves_all_axes (G.edge i) (G.axis a) hsource
    simpa [G.axis_involutive] using (G.axis_feasible_iff D i (G.axis a)).2 htarget

def CycleAction.quarter (G : CycleAction) (m : Vertex → ℤ) (i : Vertex) : ℤ :=
  reflectionSignInt G.reversed*m (G.index i)+4*G.wrap i+(if G.reversed then 1 else 0)

lemma CycleAction.quarter_increment (G : CycleAction) (m : Vertex → ℤ) (i : Vertex) :
    integerQuarterIncrement (G.quarter m) i=integerQuarterIncrement m (G.edge i) := by
  have hgap : integerQuarterIncrement (G.quarter m) i=
      reflectionSignInt G.reversed*(m (G.index (next i))-m (G.index i))+
      4*(G.wrap (next i)-G.wrap i+(if i=6 then 1 else 0)) := by
    simp only [integerQuarterIncrement,CycleAction.quarter]
    split_ifs <;> ring
  rw [hgap,CycleActions.wrap_step]
  have he := G.edge_endpoints i
  cases h : G.reversed
  · simp only [h,Bool.false_eq_true,ite_false,Prod.mk.injEq] at he
    rw [he.1,he.2]
    simp only [integerQuarterIncrement,reflectionSignInt,Bool.false_eq_true,ite_false]
    split_ifs <;> ring
  · simp only [h,ite_true,Prod.mk.injEq] at he
    rw [he.1,he.2]
    simp only [integerQuarterIncrement,reflectionSignInt,ite_true]
    split_ifs <;> ring

def QuarterLift.act {q : ℝ} {C : BoundaryCycle q} (F : QuarterLift C) (G : CycleAction) :
    QuarterLift (G.boundary C) where
  theta i := reflectionSign G.reversed*F.theta (G.index i)-G.rotation
  quarter := G.quarter F.quarter
  left := (if G.reversed then -F.left-F.diameter else F.left)-G.rotation
  diameter := F.diameter
  small := F.small
  theta_range i := by
    have h := F.theta_range (G.index i)
    cases hb : G.reversed <;> simp [hb,reflectionSign] <;> constructor <;> linarith
  represents i := by
    have h := F.represents (G.index i)
    change (G.boundary C).canonicalAngle i=_
    rw [G.canonical]
    cases hb : G.reversed <;>
      simp only [CycleAction.quarter,reflectionSign,reflectionSignInt,hb,ite_true,ite_false,
        Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_neg,Int.cast_one] <;>
      dsimp [BoundaryCycle.canonicalAngle] at * <;> linarith

lemma quarterLift_of_cost {q : ℝ} (C : BoundaryCycle q)
    (hcost : (∑ i,periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i))<10394/25425) :
    Nonempty (QuarterLift C) := by
  obtain ⟨F⟩ := physical_frame_lift_of_cost C.canonicalAngle hcost
  exact ⟨⟨F.theta,F.quarter,F.left,F.diameter,F.small,F.theta_range,F.represents⟩⟩

def QuarterLift.pullback {q r : ℝ} {C : BoundaryCycle q} {D : BoundaryCycle r}
    (F : QuarterLift D) (h : RadiusExpansion C D) : QuarterLift C where
  theta := F.theta
  quarter := F.quarter
  left := F.left
  diameter := F.diameter
  small := F.small
  theta_range := F.theta_range
  represents i := by
    simpa [BoundaryCycle.alpha,h.same_rays,h.same_tangents] using F.represents i

end SquaresInCircles.Eight
