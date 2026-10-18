module

public import SquaresInCircles.Eight.Arithmetic.RealBox
public import SquaresInCircles.Eight.BoundaryGeometry
public import SquaresInCircles.Eight.Frames

/-!
# The continuous four-type pair table, with its geometric meaning

The four labels and all sixteen constants are those in
`HAND_EXTERIOR_FRAME_CONCENTRATION.md`, section 2.  The closed core side and
closed core corner are kept as separate analytic charts; L, M and H are
the three closed outer tangent ranges.  A vertex chooses its chart and
sign once, and its resulting label is used on both incident edges.

The finite problems below contain the actual radial square roots, signed
labels, physical center gap, and original source-axis separating margin.
No table consequence is an assumption of the continuous theorem.  The
closed-box compiler can close a leaf only by excluding one of these
necessary geometric inequalities or by proving the actual corrected cost
strictly positive.  Reflection and reversal supply both target axes.

Uncompiled source draft: the ordinary `decide` proof scripts are deliberately
unevaluated.  Their rational reductions, resource costs, and all Lean
elaboration remain for the requested later audit.  No external replay or
report supplies a proof term here.
-/

@[expose] public section
open scoped BigOperators

namespace SquaresInCircles.Eight.Arithmetic.FourType

open RealBox

/-- Five analytic charts for the four geometric types.  The two core
charts have the same label and the same matrix index. -/
inductive Branch | coreSide | coreCorner | low | middle | high
  deriving DecidableEq, Fintype, Repr

def Branch.type : Branch → Fin 4
  | .coreSide | .coreCorner => 0
  | .low => 1 | .middle => 2 | .high => 3

def Branch.bBox : Branch → QInterval
  | .coreSide => ⟨0,1/2⟩
  | .coreCorner => ⟨1/2,14/25⟩
  | .low | .middle | .high => ⟨0,9/10⟩

def signQ (positive : Bool) : ℚ := if positive then 1 else -1
def sign (positive : Bool) : ℝ := if positive then 1 else -1

@[simp] theorem signQ_cast (p : Bool) : (signQ p : ℝ)=sign p := by
  cases p <;> norm_num [signQ,sign]

@[simp] theorem sign_not (p : Bool) : sign (!p)= -sign p := by
  cases p <;> norm_num [sign]

noncomputable def radialA (s : Branch) (b : ℝ) : ℝ :=
  match s with
  | .coreSide => 7/12
  | .coreCorner => 1/2+Real.sqrt ((1/12:ℝ)^2-(b-1/2)^2)
  | .low | .middle | .high => Real.sqrt (Q0-(b+1/2)^2)-1/2

noncomputable def a0 : ℝ := Real.sqrt (Q0-1/4)-1/2
noncomputable def c0 : ℝ := Real.sqrt (Q0/2)-1/2

/-- Exact positive-half labels, including the constant terms. -/
noncomputable def label (s : Branch) (a b : ℝ) : ℝ :=
  match s with
  | .coreSide | .coreCorner => (7506931/1000000)*(7/12-a)+(269343/250000)*b
  | .low => (3231/8000)*(a-a0)+(217813/200000)*b
  | .middle => -85723/40000+(1489593/1000000)*a+(1580219/1000000)*b
  | .high => Real.pi/4-(8898/15625)*(a-c0)+(195443/500000)*(b-c0)

/-- Multiplication removes the strictly positive denominator from each
tangent-type restriction.  Every chart includes both of its endpoints. -/
def TypeMem (s : Branch) (a b : ℝ) : Prop :=
  match s with
  | .coreSide | .coreCorner => True
  | .low => 4*b ≤ a
  | .middle => a ≤ 4*b ∧ 7*b ≤ 3*a
  | .high => 3*a ≤ 7*b

def q {n : ℕ} (r : ℚ) : Expr n := .const r

def radialExpr {n : ℕ} (s : Branch) (b : Expr n) : Expr n :=
  match s with
  | .coreSide => q (7/12)
  | .coreCorner => q (1/2) + .sqrt (q (1/144)-(b-q (1/2))^2)
  | .low | .middle | .high => .sqrt (q (9789/2500)-(b+q (1/2))^2)-q (1/2)

def a0Expr {n : ℕ} : Expr n := .sqrt (q (9789/2500-1/4))-q (1/2)
def c0Expr {n : ℕ} : Expr n := .sqrt (q (9789/5000))-q (1/2)

def labelExpr {n : ℕ} (s : Branch) (a b : Expr n) : Expr n :=
  match s with
  | .coreSide | .coreCorner => q (7506931/1000000)*(q (7/12)-a)+q (269343/250000)*b
  | .low => q (3231/8000)*(a-a0Expr)+q (217813/200000)*b
  | .middle => q (-85723/40000)+q (1489593/1000000)*a+q (1580219/1000000)*b
  | .high => q (1/4) * .pi-q (8898/15625)*(a-c0Expr)+q (195443/500000)*(b-c0Expr)

def cutsExpr {n : ℕ} (s : Branch) (a b : Expr n) : List (Expr n) :=
  match s with
  | .coreSide | .coreCorner => []
  | .low => [a-q 4*b]
  | .middle => [q 4*b-a,q 3*a-q 7*b]
  | .high => [q 7*b-q 3*a]

def widthExpr {n : ℕ} (φ : Expr n) : Expr n :=
  q (1/2)*(q 1 + .abs (.sin φ) + .abs (.cos φ))

def chargeExpr {n : ℕ} (φ : Expr n) : Expr n :=
  q (1/2)*(.abs (.sin φ) + .abs (.cos φ)-q 1)

def sourceAxis (four : Bool) : Fin 4 := if four then 3 else 0

def marginExpr {n : ℕ} (p r four : Bool) (a b A B φ : Expr n) : Expr n :=
  if four then a-A * .cos φ-q (signQ r)*B * .sin φ-widthExpr φ
  else q (signQ p)*b+A * .sin φ-q (signQ r)*B * .cos φ-widthExpr φ

def gapExpr {n : ℕ} (p r : Bool) (a b A B φ : Expr n) : Expr n :=
  φ+q (signQ p) * .atan (b/a)-q (signQ r) * .atan (B/A)

def gammaQ (s t : Branch) : ℚ := handGammaNumerator s.type t.type/10000

def costExpr {n : ℕ} (s t : Branch) (p r : Bool)
    (a b A B φ : Expr n) : Expr n :=
  φ-q (9/50)*chargeExpr φ+q (signQ p)*labelExpr s a b-
    q (signQ r)*labelExpr t A B-q (gammaQ s t)

/-- Coordinates are the two secondary coordinates and the unwrapped
relative frame angle.  The physical gap remains an exact hypothesis. -/
def problem (s t : Branch) (p r four : Bool) : Problem 3 :=
  let b : Expr 3 := .var 0
  let B : Expr 3 := .var 1
  let φ : Expr 3 := .var 2
  let a := radialExpr s b
  let A := radialExpr t B
  let δ := gapExpr p r a b A B φ
  { hypotheses := [a-b,A-B,δ-q (19/25),q (3/4) * .pi-δ,
        marginExpr p r four a b A B φ] ++ (cutsExpr s a b ++ cutsExpr t A B)
    conclusion := costExpr s t p r a b A B φ }

def domain (s t : Branch) : Box 3 := ![s.bBox,t.bBox,⟨-1,4⟩]

/-- Closed rational subdivision depth.  This is a source parameter, not
the output of an executed checker. -/
def depth : ℕ := 96

/- The 25 declarations in the following block each bind all eight sign/
source-axis choices to one ordered pair of analytic charts.  Thus the
original 128 type/sign/source-axis branches are all represented; splitting
the core curve increases the analytic chart count to 200. -/

-- BEGIN FINITE FOUR-TYPE PROOF SCRIPTS

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreSide_coreSide_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreSide .coreSide p r four)
        (domain .coreSide .coreSide)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreSide_coreCorner_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreSide .coreCorner p r four)
        (domain .coreSide .coreCorner)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreSide_low_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreSide .low p r four)
        (domain .coreSide .low)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreSide_middle_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreSide .middle p r four)
        (domain .coreSide .middle)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreSide_high_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreSide .high p r four)
        (domain .coreSide .high)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreCorner_coreSide_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreCorner .coreSide p r four)
        (domain .coreCorner .coreSide)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreCorner_coreCorner_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreCorner .coreCorner p r four)
        (domain .coreCorner .coreCorner)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreCorner_low_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreCorner .low p r four)
        (domain .coreCorner .low)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreCorner_middle_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreCorner .middle p r four)
        (domain .coreCorner .middle)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem coreCorner_high_certificates :
    ∀ p r four : Bool,
      certify depth (problem .coreCorner .high p r four)
        (domain .coreCorner .high)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem low_coreSide_certificates :
    ∀ p r four : Bool,
      certify depth (problem .low .coreSide p r four)
        (domain .low .coreSide)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem low_coreCorner_certificates :
    ∀ p r four : Bool,
      certify depth (problem .low .coreCorner p r four)
        (domain .low .coreCorner)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem low_low_certificates :
    ∀ p r four : Bool,
      certify depth (problem .low .low p r four)
        (domain .low .low)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem low_middle_certificates :
    ∀ p r four : Bool,
      certify depth (problem .low .middle p r four)
        (domain .low .middle)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem low_high_certificates :
    ∀ p r four : Bool,
      certify depth (problem .low .high p r four)
        (domain .low .high)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem middle_coreSide_certificates :
    ∀ p r four : Bool,
      certify depth (problem .middle .coreSide p r four)
        (domain .middle .coreSide)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem middle_coreCorner_certificates :
    ∀ p r four : Bool,
      certify depth (problem .middle .coreCorner p r four)
        (domain .middle .coreCorner)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem middle_low_certificates :
    ∀ p r four : Bool,
      certify depth (problem .middle .low p r four)
        (domain .middle .low)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem middle_middle_certificates :
    ∀ p r four : Bool,
      certify depth (problem .middle .middle p r four)
        (domain .middle .middle)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem middle_high_certificates :
    ∀ p r four : Bool,
      certify depth (problem .middle .high p r four)
        (domain .middle .high)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem high_coreSide_certificates :
    ∀ p r four : Bool,
      certify depth (problem .high .coreSide p r four)
        (domain .high .coreSide)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem high_coreCorner_certificates :
    ∀ p r four : Bool,
      certify depth (problem .high .coreCorner p r four)
        (domain .high .coreCorner)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem high_low_certificates :
    ∀ p r four : Bool,
      certify depth (problem .high .low p r four)
        (domain .high .low)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem high_middle_certificates :
    ∀ p r four : Bool,
      certify depth (problem .high .middle p r four)
        (domain .high .middle)=true := by
  decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem high_high_certificates :
    ∀ p r four : Bool,
      certify depth (problem .high .high p r four)
        (domain .high .high)=true := by
  decide

theorem source_axis_certificates (s t : Branch) (p r four : Bool) :
    certify depth (problem s t p r four) (domain s t)=true := by
  cases s <;> cases t
  · exact coreSide_coreSide_certificates p r four
  · exact coreSide_coreCorner_certificates p r four
  · exact coreSide_low_certificates p r four
  · exact coreSide_middle_certificates p r four
  · exact coreSide_high_certificates p r four
  · exact coreCorner_coreSide_certificates p r four
  · exact coreCorner_coreCorner_certificates p r four
  · exact coreCorner_low_certificates p r four
  · exact coreCorner_middle_certificates p r four
  · exact coreCorner_high_certificates p r four
  · exact low_coreSide_certificates p r four
  · exact low_coreCorner_certificates p r four
  · exact low_low_certificates p r four
  · exact low_middle_certificates p r four
  · exact low_high_certificates p r four
  · exact middle_coreSide_certificates p r four
  · exact middle_coreCorner_certificates p r four
  · exact middle_low_certificates p r four
  · exact middle_middle_certificates p r four
  · exact middle_high_certificates p r four
  · exact high_coreSide_certificates p r four
  · exact high_coreCorner_certificates p r four
  · exact high_low_certificates p r four
  · exact high_middle_certificates p r four
  · exact high_high_certificates p r four

-- END FINITE FOUR-TYPE PROOF SCRIPTS

@[simp] theorem radialExpr_eval {n : ℕ} (s : Branch) (b : Expr n) (env : Fin n → ℝ) :
    Expr.eval env (radialExpr s b)=radialA s (Expr.eval env b) := by
  cases s <;> norm_num [radialExpr,radialA,q,Expr.eval,Q0]

@[simp] theorem a0Expr_eval {n : ℕ} (env : Fin n → ℝ) :
    Expr.eval env (a0Expr : Expr n)=a0 := by
  norm_num [a0Expr,a0,q,Expr.eval,Q0]

@[simp] theorem c0Expr_eval {n : ℕ} (env : Fin n → ℝ) :
    Expr.eval env (c0Expr : Expr n)=c0 := by
  norm_num [c0Expr,c0,q,Expr.eval,Q0]

@[simp] theorem labelExpr_eval {n : ℕ} (s : Branch) (a b : Expr n) (env : Fin n → ℝ) :
    Expr.eval env (labelExpr s a b)=label s (Expr.eval env a) (Expr.eval env b) := by
  cases s <;> simp [labelExpr,label,q,Expr.eval,a0Expr_eval,c0Expr_eval] <;> ring

theorem cutsExpr_sound {n : ℕ} (s : Branch) (a b : Expr n) (env : Fin n → ℝ)
    (h : TypeMem s (Expr.eval env a) (Expr.eval env b)) :
    ∀ e ∈ cutsExpr s a b,0 ≤ Expr.eval env e := by
  cases s <;> simp only [cutsExpr,TypeMem,List.mem_cons,List.not_mem_nil,
    or_false] at *
  · tauto
  · tauto
  · rintro e rfl
    simp only [q,Expr.eval]
    linarith
  · intro e he
    rcases he with rfl | rfl <;> simp only [q,Expr.eval] <;> linarith [h.1,h.2]
  · rintro e rfl
    simp only [q,Expr.eval]
    linarith

@[simp] theorem widthExpr_eval {n : ℕ} (φ : Expr n) (env : Fin n → ℝ) :
    Expr.eval env (widthExpr φ)=pairWidth (Expr.eval env φ) := by
  simp only [widthExpr,q,Expr.eval,pairWidth]
  push_cast
  ring

@[simp] theorem chargeExpr_eval {n : ℕ} (φ : Expr n) (env : Fin n → ℝ) :
    Expr.eval env (chargeExpr φ)=periodicFrameCost (Expr.eval env φ) := by
  simp only [chargeExpr,q,Expr.eval,periodicFrameCost]
  push_cast
  ring

@[simp] theorem marginExpr_eval {n : ℕ} (p r four : Bool)
    (a b A B φ : Expr n) (env : Fin n → ℝ) :
    Expr.eval env (marginExpr p r four a b A B φ)=
      SquaresInCircles.Eight.forwardMargin (sourceAxis four)
        (Expr.eval env a) (Expr.eval env b) (Expr.eval env A) (Expr.eval env B)
        (sign p) (sign r) (Expr.eval env φ) := by
  cases four <;> simp [marginExpr,sourceAxis,SquaresInCircles.Eight.forwardMargin,
    q,Expr.eval,signQ_cast,widthExpr_eval]

@[simp] theorem gapExpr_eval {n : ℕ} (p r : Bool)
    (a b A B φ : Expr n) (env : Fin n → ℝ) :
    Expr.eval env (gapExpr p r a b A B φ)=Expr.eval env φ+
      sign p*Real.arctan (Expr.eval env b/Expr.eval env a)-
      sign r*Real.arctan (Expr.eval env B/Expr.eval env A) := by
  simp [gapExpr,q,Expr.eval,div_eq_mul_inv]

@[simp] theorem gammaQ_cast (s t : Branch) :
    (gammaQ s t : ℝ)=handGamma s.type t.type := by
  simp [gammaQ,handGamma]

@[simp] theorem costExpr_eval {n : ℕ} (s t : Branch) (p r : Bool)
    (a b A B φ : Expr n) (env : Fin n → ℝ) :
    Expr.eval env (costExpr s t p r a b A B φ)=
      Expr.eval env φ-(9/50)*periodicFrameCost (Expr.eval env φ)+
        sign p*label s (Expr.eval env a) (Expr.eval env b)-
        sign r*label t (Expr.eval env A) (Expr.eval env B)-handGamma s.type t.type := by
  simp [costExpr,q,Expr.eval,chargeExpr_eval,labelExpr_eval,gammaQ_cast]

/-- An actual closed chart point.  None of its fields is a pair inequality. -/
structure State where
  branch : Branch
  positive : Bool
  a : ℝ
  b : ℝ
  a_eq : a=radialA branch b
  b_mem : branch.bBox.Mem b
  canonical : b ≤ a
  type_mem : TypeMem branch a b

def State.flip (s : State) : State := { s with positive := !s.positive }

noncomputable def State.offset (s : State) : ℝ := sign s.positive*Real.arctan (s.b/s.a)
noncomputable def State.signedLabel (s : State) : ℝ := sign s.positive*label s.branch s.a s.b
noncomputable def State.gap (s t : State) (φ : ℝ) : ℝ := φ+s.offset-t.offset
noncomputable def State.cost (s t : State) (φ : ℝ) : ℝ :=
  φ-(9/50)*periodicFrameCost φ+s.signedLabel-t.signedLabel

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

theorem gamma_symmetric (s t : Branch) :
    handGamma t.type s.type=handGamma s.type t.type := by
  cases s <;> cases t <;> norm_num [Branch.type,handGamma,handGammaNumerator]

/-- Soundness of each source-axis problem, on every point of its full
closed state box and its closed physical angular domain. -/
theorem source_pair (s t : State) (four : Bool) (φ : ℝ)
    (hφ : -1 ≤ φ ∧ φ ≤ 4)
    (hgap : 19/25 ≤ s.gap t φ ∧ s.gap t φ ≤ 3*Real.pi/4)
    (haxis : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis four)
      s.a s.b t.a t.b (sign s.positive) (sign t.positive) φ) :
    handGamma s.branch.type t.branch.type < s.cost t φ := by
  let env : Fin 3 → ℝ := ![s.b,t.b,φ]
  let a : Expr 3 := radialExpr s.branch (.var 0)
  let A : Expr 3 := radialExpr t.branch (.var 1)
  have ha : Expr.eval env a=s.a := by simpa [a,env,Expr.eval] using s.a_eq.symm
  have hA : Expr.eval env A=t.a := by simpa [A,env,Expr.eval] using t.a_eq.symm
  have hbox : ∀ i,(domain s.branch t.branch i).Mem (env i) := by
    intro i
    fin_cases i
    · simpa [domain,env] using s.b_mem
    · simpa [domain,env] using t.b_mem
    · simpa [domain,env,QInterval.Mem] using hφ
  have hcuts := cutsExpr_sound s.branch a (.var 0) env (by simpa [ha,env,Expr.eval] using s.type_mem)
  have hCuts := cutsExpr_sound t.branch A (.var 1) env (by simpa [hA,env,Expr.eval] using t.type_mem)
  have hhyps : ∀ e ∈ (problem s.branch t.branch s.positive t.positive four).hypotheses,
      0 ≤ Expr.eval env e := by
    intro e he
    change e ∈ ([a - .var 0,A - .var 1,
      gapExpr s.positive t.positive a (.var 0) A (.var 1) (.var 2)-q (19/25),
      q (3/4) * .pi-gapExpr s.positive t.positive a (.var 0) A (.var 1) (.var 2),
      marginExpr s.positive t.positive four a (.var 0) A (.var 1) (.var 2)] ++
      (cutsExpr s.branch a (.var 0) ++ cutsExpr t.branch A (.var 1))) at he
    simp only [List.mem_append] at he
    rcases he with he | (he | he)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      · simpa [Expr.eval,ha,env] using sub_nonneg.mpr s.canonical
      · simpa [Expr.eval,hA,env] using sub_nonneg.mpr t.canonical
      · simpa [Expr.eval,q,ha,hA,env,State.gap,State.offset,gapExpr_eval]
          using sub_nonneg.mpr hgap.1
      · have hh : 0 ≤ (3/4:ℝ)*Real.pi-s.gap t φ := by linarith [hgap.2]
        simpa [Expr.eval,q,ha,hA,env,State.gap,State.offset,gapExpr_eval] using hh
      · simpa [marginExpr_eval,ha,hA,env,Expr.eval] using haxis
    · exact hcuts e he
    · exact hCuts e he
  have h := RealBox.certify_sound
    (source_axis_certificates s.branch t.branch s.positive t.positive four) env hbox hhyps
  change 0 < Expr.eval env (costExpr s.branch t.branch s.positive t.positive
    a (.var 0) A (.var 1) (.var 2)) at h
  rw [costExpr_eval,ha,hA] at h
  simpa [env,Expr.eval,State.cost,State.signedLabel] using (sub_pos.mp h)

/-- Original target axes are covered by reflected reversal, with both
vertex signs and both vertex labels transported together. -/
theorem pair (s t : State) (j : Fin 4) (φ : ℝ)
    (hφ : -1 ≤ φ ∧ φ ≤ 4)
    (hgap : 19/25 ≤ s.gap t φ ∧ s.gap t φ ≤ 3*Real.pi/4)
    (haxis : 0 ≤ SquaresInCircles.Eight.forwardMargin j
      s.a s.b t.a t.b (sign s.positive) (sign t.positive) φ) :
    handGamma s.branch.type t.branch.type < s.cost t φ := by
  fin_cases j
  · exact source_pair s t false φ hφ hgap haxis
  · have hm : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis true)
        t.flip.a t.flip.b s.flip.a s.flip.b
        (sign t.flip.positive) (sign s.flip.positive) φ := by
      simpa [sourceAxis,State.flip,sign_not,SquaresInCircles.Eight.forwardMargin,
        sub_eq_add_neg,mul_add,add_mul,mul_comm,mul_left_comm,mul_assoc,
        add_comm,add_left_comm,add_assoc] using haxis
    have hh := source_pair t.flip s.flip true φ hφ (by simpa using hgap) hm
    change handGamma t.branch.type s.branch.type < t.flip.cost s.flip φ at hh
    rw [State.reverse_cost,gamma_symmetric] at hh
    exact hh
  · have hm : 0 ≤ SquaresInCircles.Eight.forwardMargin (sourceAxis false)
        t.flip.a t.flip.b s.flip.a s.flip.b
        (sign t.flip.positive) (sign s.flip.positive) φ := by
      simpa [sourceAxis,State.flip,sign_not,SquaresInCircles.Eight.forwardMargin,
        sub_eq_add_neg,mul_add,add_mul,mul_comm,mul_left_comm,mul_assoc,
        add_comm,add_left_comm,add_assoc] using haxis
    have hh := source_pair t.flip s.flip false φ hφ (by simpa using hgap) hm
    change handGamma t.branch.type s.branch.type < t.flip.cost s.flip φ at hh
    rw [State.reverse_cost,gamma_symmetric] at hh
    exact hh
  · exact source_pair s t true φ hφ hgap haxis

noncomputable def branchOf (C : BoundaryCycle Q0) (i : Vertex) : Branch :=
  match C.kind i with
  | .coreSide => .coreSide
  | .coreCorner => .coreCorner
  | .outer => if 4*C.b i ≤ C.a i then .low
      else if 7*C.b i ≤ 3*C.a i then .middle else .high

noncomputable def signOf (C : BoundaryCycle Q0) (i : Vertex) : Bool :=
  if C.sigma i=1 then true else false

theorem signOf_spec (C : BoundaryCycle Q0) (i : Vertex) : sign (signOf C i)=C.sigma i := by
  rcases C.sigma_sign i with h | h <;> simp [signOf,sign,h]

theorem branchOf_spec (C : BoundaryCycle Q0) (i : Vertex) :
    C.a i=radialA (branchOf C i) (C.b i) ∧
      (branchOf C i).bBox.Mem (C.b i) ∧ TypeMem (branchOf C i) (C.a i) (C.b i) := by
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
      simp only [branchOf,hk]
      split_ifs with hl hm
      · exact ⟨by simp [radialA,hr],
          by simpa [Branch.bBox,QInterval.Mem] using And.intro hb hbU.le,hl⟩
      · exact ⟨by simp [radialA,hr],
          by simpa [Branch.bBox,QInterval.Mem] using And.intro hb hbU.le,
          ⟨(lt_of_not_ge hl).le,hm⟩⟩
      · exact ⟨by simp [radialA,hr],
          by simpa [Branch.bBox,QInterval.Mem] using And.intro hb hbU.le,
          (lt_of_not_ge hm).le⟩
  | coreSide =>
      have hc : C.a i=7/12 ∧ C.b i ≤ 1/2 := by
        simpa [BoundaryState,hk] using hboundary
      exact ⟨by simpa [branchOf,hk,radialA] using hc.1,
        by simpa [branchOf,hk,Branch.bBox,QInterval.Mem] using And.intro hb hc.2,
        by simp [branchOf,hk,TypeMem]⟩
  | coreCorner =>
      have hc : 1/2 ≤ C.b i ∧ (C.a i-1/2)^2+(C.b i-1/2)^2=(1/12:ℝ)^2 := by
        simpa [BoundaryState,hk] using hboundary
      have hap : 0 ≤ C.a i-1/2 := by linarith [hc.1]
      have hr : Real.sqrt ((1/12:ℝ)^2-(C.b i-1/2)^2)=C.a i-1/2 := by
        rw [show (1/12:ℝ)^2-(C.b i-1/2)^2=(C.a i-1/2)^2 by linarith [hc.2],
          Real.sqrt_sq_eq_abs,abs_of_nonneg hap]
      have hb' : C.b i ≤ 14/25 := by
        have hs : (C.b i-1/2)^2 ≤ (C.a i-1/2)^2 :=
          pow_le_pow_left₀ (by linarith [hc.1]) (by linarith) 2
        nlinarith [hc.2]
      exact ⟨by simp [branchOf,hk,radialA,hr],
        by simpa [branchOf,hk,Branch.bBox,QInterval.Mem] using And.intro hc.1 hb',
        by simp [branchOf,hk,TypeMem]⟩

/-- One consistent representative for a vertex, before either incident
pair is considered. -/
noncomputable def stateOf (C : BoundaryCycle Q0) (i : Vertex) : State where
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
  rcases C.sigma_sign i with h | h <;>
    simp [h,neg_div,Real.arctan_neg]

/-- The last edge includes its genuine full-turn winding. -/
noncomputable def pairAngle (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  C.canonicalAngle (next i)-C.canonicalAngle i+if i=6 then 2*Real.pi else 0

theorem pairAngle_gap (C : BoundaryCycle Q0) (i : Vertex) :
    pairAngle C i=angleGap C.beta i+C.alpha (next i)-C.alpha i := by
  simp only [pairAngle,angleGap,BoundaryCycle.canonicalAngle]
  ring

theorem pairAngle_trig (C : BoundaryCycle Q0) (i : Vertex) :
    relativeC (C.square i) (C.square (next i))=Real.cos (pairAngle C i) ∧
    relativeS (C.square i) (C.square (next i))=Real.sin (pairAngle C i) := by
  have hci : (C.square i).cosine=Real.cos (C.canonicalAngle i) := C.frame_cos i
  have hsi : (C.square i).sine=Real.sin (C.canonicalAngle i) := C.frame_sin i
  have hcj : (C.square (next i)).cosine=Real.cos (C.canonicalAngle (next i)) := C.frame_cos _
  have hsj : (C.square (next i)).sine=Real.sin (C.canonicalAngle (next i)) := C.frame_sin _
  have hc : relativeC (C.square i) (C.square (next i))=
      Real.cos (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeC,hci,hsi,hcj,hsj,Real.cos_sub] <;> ring
  have hs : relativeS (C.square i) (C.square (next i))=
      Real.sin (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeS,hci,hsi,hcj,hsj,Real.sin_sub] <;> ring
  by_cases hi : i=6 <;>
    simpa [pairAngle,hi,Real.cos_add,Real.sin_add] using And.intro hc hs

theorem pairAngle_charge (C : BoundaryCycle Q0) (i : Vertex) :
    periodicFrameCost (pairAngle C i)=
      periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i) := by
  by_cases hi : i=6
  · have h := periodicFrameCost_int_quarter
      (C.canonicalAngle (next i)-C.canonicalAngle i) 4
    convert h using 1
    congr 1
    simp only [pairAngle,hi,if_true]
    norm_num <;> ring
  · simp [pairAngle,hi]

theorem pairAngle_mem (C : BoundaryCycle Q0) (i : Vertex) :
    -1 ≤ pairAngle C i ∧ pairAngle C i ≤ 4 := by
  have hl := boundary_gap_lower C le_rfl i
  have hu := boundary_gap_upper C le_rfl i
  have hα := C.alpha_range i
  have hA := C.alpha_range (next i)
  rw [pairAngle_gap]
  constructor <;> linarith [pi_lt_22_over_7]

/-- The four-type inequality for every actual retained forward axis. -/
theorem cycle_pair (C : BoundaryCycle Q0) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type <
      angleGap C.beta i-
        (9/50)*periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i)+
        (C.alpha (next i)-(stateOf C (next i)).signedLabel)-
        (C.alpha i-(stateOf C i).signedLabel) := by
  have hm := canonical_margin_identity j _ _ _ _ _ _ _ _ (pairAngle C i)
    (C.center_eq i) (C.center_eq (next i)) (pairAngle_trig C i).1 (pairAngle_trig C i).2
  have hmargin : 0 ≤ SquaresInCircles.Eight.forwardMargin j
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (C.sigma i) (C.sigma (next i))
      (pairAngle C i) := by
    rw [← hm]
    exact sub_nonneg.mpr hj
  have hgap : (stateOf C i).gap (stateOf C (next i)) (pairAngle C i)=angleGap C.beta i := by
    rw [State.gap,stateOf_offset,stateOf_offset,pairAngle_gap]
    ring
  have hh := pair (stateOf C i) (stateOf C (next i)) j (pairAngle C i)
    (pairAngle_mem C i)
    (by rw [hgap]; exact ⟨(boundary_gap_lower C le_rfl i).le,(boundary_gap_upper C le_rfl i).le⟩)
    (by simpa only [stateOf,signOf_spec] using hmargin)
  change handGamma (branchOf C i).type (branchOf C (next i)).type <
    (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) at hh
  unfold State.cost at hh
  rw [pairAngle_charge,pairAngle_gap] at hh
  linarith

end SquaresInCircles.Eight.Arithmetic.FourType

namespace SquaresInCircles.Eight

/-- Complete actual continuous four-type pair bridge.  Type and marker
are chosen once per vertex.  Every originally feasible signed axis is
covered, including simultaneous feasible ties. -/
theorem four_type_pair_bound (C : BoundaryCycle Q0) :
    ∃ τ : Vertex → Fin 4, ∃ ψ : Vertex → ℝ, ∀ i,
      handGamma (τ i) (τ (next i)) <
        angleGap C.beta i-
          (9/50)*periodicFrameCost (C.canonicalAngle (next i)-C.canonicalAngle i)+
          ψ (next i)-ψ i := by
  let τ : Vertex → Fin 4 := fun i => (Arithmetic.FourType.branchOf C i).type
  let ψ : Vertex → ℝ := fun i => C.alpha i-(Arithmetic.FourType.stateOf C i).signedLabel
  refine ⟨τ,ψ,?_⟩
  intro i
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have hh := C.feasible i
  rw [hj] at hh
  exact Arithmetic.FourType.cycle_pair C i j hh

end SquaresInCircles.Eight
