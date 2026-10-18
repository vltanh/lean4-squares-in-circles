module

public import SquaresInCircles.Eight.BoundaryGeometry

/-!
# Actual dihedral actions on the seven-cycle

Reindexing a reflected cycle reverses both endpoints of an edge. Its selected
axis is first reversed and then its secondary-axis sign is reflected. The
real polar lift includes the explicit wrap integer; integer quarter words
therefore transform as edges, rather than as vertex labels.

Uncompiled source draft.
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

lemma motion_left_inverse (θ : ℝ) (b : Bool) (p : Point) :
    motionInverse θ b (motionPoint θ b p)=p := by
  cases b <;> simp [motionInverse,motionPoint,reflectionPoint]

lemma motion_right_inverse (θ : ℝ) (b : Bool) (p : Point) :
    motionPoint θ b (motionInverse θ b p)=p := by
  cases b <;> simp [motionInverse,motionPoint,reflectionPoint]

lemma motionSquare_open (θ : ℝ) (b : Bool) (K : UnitSquare) (p : Point) :
    openSquare (motionSquare θ b K) p ↔ openSquare K (motionInverse θ b p) := by
  cases b <;> simp [motionSquare,reflectionSquare,motionInverse,reflectionPoint,
    pullSquare_open,reflectDiagonal_open]

lemma motionSquare_closed (θ : ℝ) (b : Bool) (K : UnitSquare) (p : Point) :
    closedSquare (motionSquare θ b K) p ↔ closedSquare K (motionInverse θ b p) := by
  cases b <;> simp [motionSquare,reflectionSquare,motionInverse,reflectionPoint,
    pullSquare_closed,reflectDiagonal_closed]

lemma motionPoint_norm (θ : ℝ) (b : Bool) (p : Point) :
    normSq (motionPoint θ b p)=normSq p := by
  cases b <;>
    dsimp [motionPoint,reflectionPoint,diagonalPoint,frameEquiv,pointInDirection,normSq] <;>
    simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] <;>
    nlinarith [congrArg (fun z : ℝ => (p.1^2+p.2^2)*z) (Real.sin_sq_add_cos_sq θ)]

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
  cases b <;>
    dsimp [motionPoint,reflectionPoint,diagonalPoint,frameEquiv,pointInDirection,dot] <;>
    simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] <;>
    nlinarith [congrArg (fun z : ℝ => (p.1*r.1+p.2*r.2)*z) (Real.sin_sq_add_cos_sq θ)]

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

lemma reflectedAxis_involutive (b : Bool) (a : SignedAxis) :
    reflectedAxis b (reflectedAxis b a)=a := by
  cases b <;> cases a with
  | mk owner sign => cases owner <;> cases sign <;> rfl

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
  cases b <;>
    dsimp [motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,relativeC] <;>
    simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] <;>
    nlinarith [congrArg (fun z : ℝ => (K.cosine*J.cosine+K.sine*J.sine)*z)
      (Real.sin_sq_add_cos_sq θ)]

lemma motionSquare_relativeS (θ : ℝ) (b : Bool) (K J : UnitSquare) :
    relativeS (motionSquare θ b K) (motionSquare θ b J)=reflectionSign b*relativeS K J := by
  cases b <;>
    dsimp [motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,relativeS,reflectionSign] <;>
    simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] <;>
    nlinarith [congrArg (fun z : ℝ => (K.cosine*J.sine-K.sine*J.cosine)*z)
      (Real.sin_sq_add_cos_sq θ)]

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

lemma CycleAction.lift_gap (G : CycleAction) (β : Vertex → ℝ) (i : Vertex) :
    angleGap (G.lift β) i=angleGap β (G.edge i) := by
  rcases G with ⟨shift,rev,rot⟩
  cases rev <;> fin_cases shift <;> fin_cases i <;>
    norm_num [CycleAction.lift,CycleAction.index,CycleAction.edge,CycleAction.wrap,
      reflectionSign,angleGap,next] <;> ring

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
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center.1=_
    rw [motionSquare_center,motionPoint_norm,G.lift_cos,hc,motionPoint_polar]
  center_sin i := by
    have hc : (C.square (G.index i)).center=
        (Real.sqrt (normSq (C.square (G.index i)).center)*Real.cos (O.beta (G.index i)),
         Real.sqrt (normSq (C.square (G.index i)).center)*Real.sin (O.beta (G.index i))) :=
      Prod.ext (O.center_cos _) (O.center_sin _)
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center.2=_
    rw [motionSquare_center,motionPoint_norm,G.lift_sin,hc,motionPoint_polar]
  gap_pos i := by rw [G.lift_gap]; exact O.gap_pos _
  gap_lt_pi i := by rw [G.lift_gap]; exact O.gap_lt_pi _

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
    rw [motionSquare_center,C.center_eq,motionSquare_rotate]
    congr 1
    apply Prod.ext <;> dsimp <;> ring
  boundary i := C.boundary _
  beta := G.lift C.beta
  center_cos i := by
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center.1=_
    have hc : (C.square (G.index i)).center=
        (C.radius (G.index i)*Real.cos (C.beta (G.index i)),
         C.radius (G.index i)*Real.sin (C.beta (G.index i))) := Prod.ext (C.center_cos _) (C.center_sin _)
    rw [motionSquare_center,G.lift_cos,hc,motionPoint_polar]
  center_sin i := by
    change (motionSquare G.rotation G.reversed (C.square (G.index i))).center.2=_
    have hc : (C.square (G.index i)).center=
        (C.radius (G.index i)*Real.cos (C.beta (G.index i)),
         C.radius (G.index i)*Real.sin (C.beta (G.index i))) := Prod.ext (C.center_cos _) (C.center_sin _)
    rw [motionSquare_center,G.lift_sin,hc,motionPoint_polar]
  frame_cos i := by
    cases h : G.reversed <;>
      simp [motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,C.frame_cos,C.frame_sin,
        CycleAction.lift,CycleAction.wrap,reflectionSign,h,Real.arctan_neg,
        Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub] <;>
      split <;> simp [Real.cos_add,Real.sin_add] <;> ring
  frame_sin i := by
    cases h : G.reversed <;>
      simp [motionSquare,reflectionSquare,pullSquare,reflectDiagonalSquare,C.frame_cos,C.frame_sin,
        CycleAction.lift,CycleAction.wrap,reflectionSign,h,Real.arctan_neg,
        Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub] <;>
      split <;> simp [Real.cos_add,Real.sin_add] <;> ring
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
  cases h : G.reversed <;> cases a with
  | mk owner sign => cases owner <;> cases sign <;> simp [CycleAction.axis,reflectedAxis,SignedAxis.reverse,AxisOwner.swap,AxisSign.flip,h]

lemma CycleAction.axis_feasible_iff {q : ℝ} (G : CycleAction) (C : BoundaryCycle q)
    (i : Vertex) (a : SignedAxis) :
    (G.axis a).Feasible ((G.boundary C).square i) ((G.boundary C).square (next i)) ↔
      a.Feasible (C.square (G.edge i)) (C.square (next (G.edge i))) := by
  have he := G.edge_endpoints i
  cases h : G.reversed
  · simp only [h,Bool.false_eq_true,ite_false,Prod.mk.injEq] at he
    simpa [CycleAction.boundary,CycleAction.neighbor,CycleAction.axis,h,he.1,he.2]
      using reflectedAxis_feasible_iff G.rotation false a _ _
  · simp only [h,ite_true,Prod.mk.injEq] at he
    simpa [CycleAction.boundary,CycleAction.neighbor,CycleAction.axis,h,he.1,he.2]
      using (reflectedAxis_feasible_iff G.rotation true a.reverse _ _).trans
        (reverse_feasible_iff a _ _)

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
  rcases G with ⟨shift,rev,rot⟩
  cases rev <;> fin_cases shift <;> fin_cases i <;>
    norm_num [CycleAction.quarter,CycleAction.index,CycleAction.edge,CycleAction.wrap,
      reflectionSignInt,integerQuarterIncrement,next] <;> ring

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
