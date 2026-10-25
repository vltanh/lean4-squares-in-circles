module

public import SquaresInCircles.Eight.Arithmetic.CorePairGeometry
public import SquaresInCircles.Eight.Boundary.Geometry

/-!
# Eight squares: the four types and the states of the frame pairs

A state (`State`) lies on one of five branches: the side and the corner of the core curve, and the
low, middle and high parts of the outer circle of the level `Q0`, cut at the tangents `b/a = 1/4`
and `3/7` (`Branch`, `TypeMem`); the two core branches form the type `0`, the outer ones the
types `1`, `2` and `3` (`Branch.type`). A state records only its branch, its sign, its coordinates
`b ≤ a` on the branch (`radialA`) and the cut of its type. Its offset is `± arctan (b/a)` and its
label the affine function `label` of its branch, with its sign; the cost of a pair at the angle
`φ` between the frames is `φ - (9/50) periodicFrameCost φ` plus the label of the source minus that
of the target (`State.cost`), and a forward axis `j` separates the pair when its margin is
nonnegative (`State.Feasible`). Reversing the pair turns the axes of the target into axes of the
source (`State.target_primary_reverse`, `State.target_secondary_reverse`).

Each vertex of a boundary cycle at `Q0` gives one state (`branchOf`, `stateOf`), whose gap at the
angle between the frames is the gap of the centre directions (`stateOf_gap`), and every forward
axis that separates two consecutive squares, ties included, is feasible for their states
(`stateOf_feasible`). Two core vertices satisfy the pair inequality (`core_cycle_pair`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FramePair

inductive Branch | coreSide | coreCorner | low | middle | high
  deriving DecidableEq, Repr

instance : Fintype Branch where
  elems := {.coreSide, .coreCorner, .low, .middle, .high}
  complete x := by cases x <;> decide

def Branch.type : Branch → Fin 4
  | .coreSide | .coreCorner => 0
  | .low => 1
  | .middle => 2
  | .high => 3

def Branch.lower : Branch → ℝ
  | .coreCorner => 1/2
  | _ => 0

def Branch.upper : Branch → ℝ
  | .coreSide => 1/2
  | .coreCorner => 14/25
  | .low | .middle | .high => 9/10

def sign (positive : Bool) : ℝ := if positive then 1 else -1

@[simp] theorem sign_not (p : Bool) : sign (!p)= -sign p := by
  cases p <;> norm_num [sign]

theorem sign_cases (p : Bool) : sign p=1 ∨ sign p= -1 := by
  cases p <;> simp [sign]

def radialA (s : Branch) (b : ℝ) : ℝ :=
  match s with
  | .coreSide => 7/12
  | .coreCorner => 1/2+Real.sqrt ((1/12:ℝ)^2-(b-1/2)^2)
  | .low | .middle | .high => Real.sqrt (Q0-(b+1/2)^2)-1/2

def a0 : ℝ := Real.sqrt (Q0-1/4)-1/2
def c0 : ℝ := Real.sqrt (Q0/2)-1/2

def label (s : Branch) (a b : ℝ) : ℝ :=
  match s with
  | .coreSide | .coreCorner => (7506931/1000000)*(7/12-a)+(269343/250000)*b
  | .low => (3231/8000)*(a-a0)+(217813/200000)*b
  | .middle => -85723/40000+(1489593/1000000)*a+(1580219/1000000)*b
  | .high => Real.pi/4-(8898/15625)*(a-c0)+(195443/500000)*(b-c0)

def TypeMem (s : Branch) (a b : ℝ) : Prop :=
  match s with
  | .coreSide | .coreCorner => True
  | .low => 4*b≤a
  | .middle => a≤4*b ∧ 7*b≤3*a
  | .high => 3*a≤7*b

structure State where
  branch : Branch
  positive : Bool
  a : ℝ
  b : ℝ
  a_eq : a=radialA branch b
  b_mem : b∈Icc branch.lower branch.upper
  canonical : b≤a
  type_mem : TypeMem branch a b

def State.flip (s : State) : State := { s with positive := !s.positive }
def State.offset (s : State) : ℝ := sign s.positive*Real.arctan (s.b/s.a)
def State.signedLabel (s : State) : ℝ := sign s.positive*label s.branch s.a s.b
def State.gap (s t : State) (φ : ℝ) : ℝ := φ+s.offset-t.offset
def State.cost (s t : State) (φ : ℝ) : ℝ :=
  φ-(9/50)*periodicFrameCost φ+s.signedLabel-t.signedLabel

def State.Feasible (s t : State) (j : Fin 4) (φ : ℝ) : Prop :=
  0≤forwardMargin j s.a s.b t.a t.b (sign s.positive) (sign t.positive) φ

theorem State.b_nonneg (s : State) : 0≤ s.b := by
  have hh := s.b_mem.1
  cases hb : s.branch <;> simp [hb,Branch.lower] at hh <;> linarith

theorem State.b_upper (s : State) : s.b≤9/10 := by
  have hh := s.b_mem.2
  cases hb : s.branch <;> simp [hb,Branch.upper] at hh <;> linarith

theorem State.outer_eq (s : State) (hs : s.branch.type≠0) :
    (s.a+1/2)^2+(s.b+1/2)^2=Q0 := by
  have hb := s.b_nonneg
  have hbu := s.b_upper
  have hsqr := pow_le_pow_left₀ (show 0≤s.b+1/2 by linarith)
    (show s.b+1/2≤7/5 by linarith) 2
  have hrad : 0≤Q0-(s.b+1/2)^2 := by norm_num [Q0] at *; nlinarith
  have hroot := Real.sq_sqrt hrad
  have he := s.a_eq
  cases hbr : s.branch <;> simp [hbr,Branch.type] at hs
  all_goals
    simp only [hbr,radialA] at he
    rw [he,sub_add_cancel,hroot]
    ring

theorem State.a_pos (s : State) : 0<s.a := by
  have hb := s.b_nonneg
  have he := s.a_eq
  cases hbr : s.branch with
  | coreSide =>
      simp only [hbr,radialA] at he
      rw [he]
      norm_num
  | coreCorner =>
      simp only [hbr,radialA] at he
      nlinarith [Real.sqrt_nonneg ((1/12:ℝ)^2-(s.b-1/2)^2)]
  | low | middle | high =>
      have hs : s.branch.type≠0 := by simp [hbr,Branch.type]
      have hc := s.outer_eq hs
      have hbu := s.b_upper
      have hsq := pow_le_pow_left₀ (show 0≤ s.b+1/2 by linarith)
        (show s.b+1/2≤7/5 by linarith) 2
      have ha0 : 0≤ s.a := hb.trans s.canonical
      norm_num [Q0] at hc
      nlinarith

theorem State.offset_range (s : State) :
    -(Real.pi/4)≤ s.offset ∧ s.offset≤Real.pi/4 := by
  have hr : s.b/s.a∈Icc 0 1 :=
    ⟨div_nonneg s.b_nonneg s.a_pos.le,(div_le_one s.a_pos).2 s.canonical⟩
  have h0 : 0≤Real.arctan (s.b/s.a) := by
    simpa using Real.arctan_mono hr.1
  have h1 : Real.arctan (s.b/s.a)≤Real.pi/4 := by
    simpa [Real.arctan_one] using Real.arctan_mono hr.2
  rcases sign_cases s.positive with hs | hs
  · simp only [State.offset,hs,one_mul]
    exact ⟨by linarith [Real.pi_pos],h1⟩
  · simp only [State.offset,hs,neg_one_mul]
    constructor <;> linarith

@[simp] theorem State.flip_offset (s : State) : s.flip.offset= -s.offset := by
  simp [State.flip,State.offset]

@[simp] theorem State.flip_label (s : State) : s.flip.signedLabel= -s.signedLabel := by
  simp [State.flip,State.signedLabel]

@[simp] theorem State.reverse_gap (s t : State) (φ : ℝ) :
    t.flip.gap s.flip φ=s.gap t φ := by
  simp [State.gap]
  ring

@[simp] theorem State.reverse_cost (s t : State) (φ : ℝ) :
    t.flip.cost s.flip φ=s.cost t φ := by
  simp [State.cost]
  ring

theorem State.target_primary_reverse (s t : State) (φ : ℝ) :
    s.Feasible t 1 φ ↔ t.flip.Feasible s.flip 3 φ := by
  simp [State.Feasible,State.flip,forwardMargin,sign_not,
    sub_eq_add_neg,mul_comm,mul_left_comm,
    add_comm,add_left_comm,add_assoc]

theorem State.target_secondary_reverse (s t : State) (φ : ℝ) :
    s.Feasible t 2 φ ↔ t.flip.Feasible s.flip 0 φ := by
  simp [State.Feasible,State.flip,forwardMargin,sign_not,
    sub_eq_add_neg,mul_comm,mul_left_comm,
    add_comm,add_left_comm,add_assoc]

theorem gamma_symmetric (s t : Branch) :
    handGamma t.type s.type=handGamma s.type t.type := by
  cases s <;> cases t <;> norm_num [Branch.type,handGamma,handGammaNumerator]

def branchOf (C : BoundaryCycle Q0) (i : Vertex) : Branch :=
  match C.kind i with
  | .coreSide => .coreSide
  | .coreCorner => .coreCorner
  | .outer => if 4*C.b i≤C.a i then .low
      else if 7*C.b i≤3*C.a i then .middle else .high

theorem branchOf_core_iff (C : BoundaryCycle Q0) (i : Vertex) :
    (branchOf C i).type=0 ↔ C.kind i≠.outer := by
  cases hk : C.kind i with
  | outer =>
      simp only [branchOf,hk]
      split_ifs <;> norm_num [Branch.type]
  | coreSide => simp [branchOf,hk,Branch.type]
  | coreCorner => simp [branchOf,hk,Branch.type]

def signOf (C : BoundaryCycle Q0) (i : Vertex) : Bool :=
  if C.sigma i=1 then true else false

theorem signOf_spec (C : BoundaryCycle Q0) (i : Vertex) : sign (signOf C i)=C.sigma i := by
  rcases C.sigma_sign i with h | h <;> norm_num [signOf,sign,h]

theorem branchOf_spec (C : BoundaryCycle Q0) (i : Vertex) :
    C.a i=radialA (branchOf C i) (C.b i) ∧
      C.b i∈Icc (branchOf C i).lower (branchOf C i).upper ∧
        TypeMem (branchOf C i) (C.a i) (C.b i) := by
  have ha := C.a_pos i
  have hb := C.b_nonneg i
  have hab := C.b_le_a i
  have hbU := (Candidate.canonical_bounds C le_rfl i).2.2.2
  have hboundary := C.boundary i
  cases hk : C.kind i with
  | outer =>
      have he : (C.a i+1/2)^2+(C.b i+1/2)^2=Q0 := by
        simpa [BoundaryState,hk,SquaresInCircles.phi] using hboundary
      have hr : Real.sqrt (Q0-(C.b i+1/2)^2)=C.a i+1/2 := by
        rw [show Q0-(C.b i+1/2)^2=(C.a i+1/2)^2 by linarith,
          Real.sqrt_sq_eq_abs,abs_of_pos (by linarith)]
      have hA : C.a i=radialA .low (C.b i) := by
        simp only [radialA]
        rw [hr]
        ring
      simp only [branchOf,hk]
      split_ifs with hl hm
      · exact ⟨hA,⟨hb,hbU.le⟩,hl⟩
      · exact ⟨hA,⟨hb,hbU.le⟩,⟨(lt_of_not_ge hl).le,hm⟩⟩
      · exact ⟨hA,⟨hb,hbU.le⟩,(lt_of_not_ge hm).le⟩
  | coreSide =>
      have hc : C.a i=7/12 ∧ C.b i≤1/2 := by
        simpa [BoundaryState,hk] using hboundary
      exact ⟨by simpa [branchOf,hk,radialA] using hc.1,
        by simpa [branchOf,hk,Branch.lower,Branch.upper] using And.intro hb hc.2,
        by simp [branchOf,hk,TypeMem]⟩
  | coreCorner =>
      have hc : 1/2≤C.b i ∧ (C.a i-1/2)^2+(C.b i-1/2)^2=(1/12:ℝ)^2 := by
        simpa [BoundaryState,hk] using hboundary
      have hap : 0≤C.a i-1/2 := by linarith [hc.1]
      have hr : Real.sqrt ((1/12:ℝ)^2-(C.b i-1/2)^2)=C.a i-1/2 := by
        rw [show (1/12:ℝ)^2-(C.b i-1/2)^2=(C.a i-1/2)^2 by linarith [hc.2],
          Real.sqrt_sq_eq_abs,abs_of_nonneg hap]
      have hb' : C.b i≤14/25 := by
        have hs : (C.b i-1/2)^2≤(C.a i-1/2)^2 :=
          pow_le_pow_left₀ (by linarith [hc.1]) (by linarith) 2
        nlinarith [hc.2]
      refine ⟨?_,
        by simpa [branchOf,hk,Branch.lower,Branch.upper] using And.intro hc.1 hb',
        by simp [branchOf,hk,TypeMem]⟩
      simp only [branchOf,hk,radialA]
      rw [hr]
      ring

/-- The state of a vertex of the cycle. Its branch and its sign are fixed once, also at a cut
between two types or at a tie of the signs. -/
def stateOf (C : BoundaryCycle Q0) (i : Vertex) : State where
  branch := branchOf C i
  positive := signOf C i
  a := C.a i
  b := C.b i
  a_eq := (branchOf_spec C i).1
  b_mem := (branchOf_spec C i).2.1
  canonical := C.b_le_a i
  type_mem := (branchOf_spec C i).2.2

theorem stateOf_offset (C : BoundaryCycle Q0) (i : Vertex) :
    (stateOf C i).offset=C.alpha i := by
  simp only [State.offset,stateOf,signOf_spec,BoundaryCycle.alpha,BoundaryCycle.tangent]
  rcases C.sigma_sign i with h | h <;> simp [h,neg_div,Real.arctan_neg]

theorem stateOf_core_label (C : BoundaryCycle Q0) (i : Vertex)
    (hk : C.kind i≠.outer) :
    (stateOf C i).signedLabel=C.sigma i*CorePairGeometry.label CorePairGeometry.K CorePairGeometry.g (C.a i) (C.b i) := by
  cases he : C.kind i with
  | outer => exact False.elim (hk he)
  | coreSide | coreCorner =>
      simp [State.signedLabel,stateOf,branchOf,he,signOf_spec,label,
        CorePairGeometry.label,CorePairGeometry.K,CorePairGeometry.g]

def pairAngle (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  C.canonicalAngle (next i)-C.canonicalAngle i+if i=6 then 2*Real.pi else 0

theorem pairAngle_gap (C : BoundaryCycle Q0) (i : Vertex) :
    pairAngle C i=angleGap C.beta i+C.alpha (next i)-C.alpha i := by
  simp only [pairAngle,angleGap,BoundaryCycle.canonicalAngle]
  ring

theorem pairAngle_trig (C : BoundaryCycle Q0) (i : Vertex) :
    relativeC (C.square i) (C.square (next i))=Real.cos (pairAngle C i) ∧
    relativeS (C.square i) (C.square (next i))=Real.sin (pairAngle C i) := by
  have hc : relativeC (C.square i) (C.square (next i))=
      Real.cos (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    rw [relativeC,C.frame_cos i,C.frame_sin i,C.frame_cos (next i),C.frame_sin (next i),
      Real.cos_sub]
    simp only [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,BoundaryCycle.tangent]
    ring
  have hs : relativeS (C.square i) (C.square (next i))=
      Real.sin (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    rw [relativeS,C.frame_cos i,C.frame_sin i,C.frame_cos (next i),C.frame_sin (next i),
      Real.sin_sub]
    simp only [BoundaryCycle.canonicalAngle,BoundaryCycle.alpha,BoundaryCycle.tangent]
    ring
  rw [hc,hs]
  by_cases hi : i=6 <;> simp [pairAngle,hi]

theorem pairAngle_charge (C : BoundaryCycle Q0) (i : Vertex) :
    periodicFrameCost (pairAngle C i)=
      periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i) := by
  by_cases hi : i=6
  · have hh := periodicFrameCost_int_quarter
      (C.canonicalAngle (next i)-C.canonicalAngle i) 4
    convert hh using 1
    congr 1
    simp only [pairAngle,hi,ite_true]
    norm_num <;> ring
  · simp [pairAngle,hi]

theorem stateOf_gap (C : BoundaryCycle Q0) (i : Vertex) :
    (stateOf C i).gap (stateOf C (next i)) (pairAngle C i)=angleGap C.beta i := by
  rw [State.gap,stateOf_offset,stateOf_offset,pairAngle_gap]
  ring

theorem stateOf_gap_bounds (C : BoundaryCycle Q0) (i : Vertex) :
    19/25<(stateOf C i).gap (stateOf C (next i)) (pairAngle C i) ∧
      (stateOf C i).gap (stateOf C (next i)) (pairAngle C i)<3*Real.pi/4 := by
  rw [stateOf_gap]
  exact ⟨boundary_gap_lower C le_rfl i,boundary_gap_upper C le_rfl i⟩

/-- Every forward axis that separates two consecutive squares is feasible for their states, ties
included. -/
theorem stateOf_feasible (C : BoundaryCycle Q0) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (stateOf C i).Feasible (stateOf C (next i)) j (pairAngle C i) := by
  have hm := canonical_margin_identity j _ _ _ _ _ _ _ _ (pairAngle C i)
    (C.center_eq i) (C.center_eq (next i)) (pairAngle_trig C i).1 (pairAngle_trig C i).2
  have hh : 0≤forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (C.sigma i) (C.sigma (next i)) (pairAngle C i) := by
    rw [← hm]
    exact sub_nonneg.mpr hj
  simpa only [State.Feasible,stateOf,signOf_spec] using hh

theorem stateOf_cost (C : BoundaryCycle Q0) (i : Vertex) :
    (stateOf C i).cost (stateOf C (next i)) (pairAngle C i)=
      angleGap C.beta i-
        (9/50)*periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i)+
          (C.alpha (next i)-(stateOf C (next i)).signedLabel)-
            (C.alpha i-(stateOf C i).signedLabel) := by
  rw [State.cost,pairAngle_charge,pairAngle_gap]
  ring

theorem core_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : (branchOf C i).type=0) (hj : (branchOf C (next i)).type=0) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  have hci := (branchOf_core_iff C i).mp hi
  have hcj := (branchOf_core_iff C (next i)).mp hj
  have hh := CorePairGeometry.core_cost (Or.inl ⟨rfl,rfl⟩) C i hci hcj
  have hch := CorePairGeometry.charge_upper (C.canonicalAngle (next i)-C.canonicalAngle i)
  have hg : handGamma 0 0=23/25 := by norm_num [handGamma,handGammaNumerator]
  rw [stateOf_cost,stateOf_core_label C i hci,stateOf_core_label C (next i) hcj,hi,hj,hg]
  linarith

end SquaresInCircles.Eight.FramePair
