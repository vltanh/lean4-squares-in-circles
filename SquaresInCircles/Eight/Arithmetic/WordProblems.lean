module

public import SquaresInCircles.Eight.Arithmetic.RealBox
public import SquaresInCircles.Eight.BoundaryGeometry

/-!
# Exact closed-domain problems for all six wrong quarter words

The three common increment costs and the two role-label systems are kept
separate. The first wrong word uses `c+p*a+sigma*q*b`; the second uses
`sigma*(c+p*a+q*b+r*b^2+s*a*b)`. The distinction is part of the expression
syntax and of the real evaluation identities below.

The core side and corner are separate CLOSED source/target branches.
No radial necklace, sampled representative, preferred owner, or external
verification report is a premise of these problems.
-/

@[expose] public section
namespace SquaresInCircles.Eight.WordProblems
open Arithmetic Arithmetic.RealBox

abbrev E := Expr 3

def sign (positive : Bool) : ℚ := if positive then 1 else -1

def transverseBox : RadialKind→QInterval
  | .outer => ⟨0,9/10⟩
  | .coreSide => ⟨0,1/2⟩
  | .coreCorner => ⟨1/2,14/25⟩

def primary (kind : RadialKind) (b : E) : E :=
  match kind with
  | .outer => (.sqrt ((.const (9789/2500))-(b+(.const (1/2)))^2))-(.const (1/2))
  | .coreSide => .const (7/12)
  | .coreCorner => (.const (1/2))+(.sqrt ((.const (1/144))-(b-(.const (1/2)))^2))

noncomputable def primaryValue (kind : RadialKind) (b : ℝ) : ℝ :=
  match kind with
  | .outer => Real.sqrt ((9789/2500)-(b+1/2)^2)-1/2
  | .coreSide => 7/12
  | .coreCorner => 1/2+Real.sqrt ((1/144)-(b-1/2)^2)

lemma primary_eval (kind : RadialKind) (b : E) (env : Fin 3→ℝ) :
    (primary kind b).eval env=primaryValue kind (b.eval env) := by
  cases kind <;> simp [primary,primaryValue,Expr.eval]

lemma actual_primary {a b : ℝ} (k : RadialKind) (ha : 1/2<a)
    (hb : 0≤b) (hba : b≤a) (hs : BoundaryState Q0 k a b) :
    a=primaryValue k b ∧ (transverseBox k).Mem b := by
  cases k with
  | outer =>
      have he : (a+1/2)^2+(b+1/2)^2=9789/2500 := by
        simpa [BoundaryState,SquaresInCircles.phi,Q0] using hs
      have hnon : 0≤(9789/2500:ℝ)-(b+1/2)^2 := by nlinarith [sq_nonneg (a+1/2)]
      have hroot := Real.sq_sqrt hnon
      have hroot0 := Real.sqrt_nonneg ((9789/2500:ℝ)-(b+1/2)^2)
      have hbu : b<9/10 := by nlinarith [sq_nonneg (a-b)]
      exact ⟨by dsimp [primaryValue]; nlinarith,⟨hb,hbu.le⟩⟩
  | coreSide =>
      obtain ⟨hA,hB⟩ := hs
      exact ⟨hA,⟨hb,hB⟩⟩
  | coreCorner =>
      obtain ⟨hB,he⟩ := hs
      have hnon : 0≤(1/144:ℝ)-(b-1/2)^2 := by nlinarith [sq_nonneg (a-1/2)]
      have hroot := Real.sq_sqrt hnon
      have hroot0 := Real.sqrt_nonneg ((1/144:ℝ)-(b-1/2)^2)
      have hbu : b<14/25 := by nlinarith [sq_nonneg (a-b)]
      exact ⟨by dsimp [primaryValue]; nlinarith,⟨hB,hbu.le⟩⟩

def phase (quarter : Fin 3) : E := .var 2+(.const ((quarter.val:ℚ)/2))*.pi

def signedAngle (kind : RadialKind) (positive : Bool) (b : E) : E :=
  (.const (sign positive))*(.atan (b/(primary kind b)))

def margin (axis : Fin 4) (a b A B : E) (positive targetPositive : Bool) (φ : E) : E :=
  let σ := Expr.const (sign positive)
  let τ := Expr.const (sign targetPositive)
  let W := (1+(.abs (.sin φ))+(.abs (.cos φ)))/2
  ![σ*b+A*(.sin φ)-τ*B*(.cos φ)-W,
    A-a*(.cos φ)+σ*b*(.sin φ)-W,
    a*(.sin φ)+σ*b*(.cos φ)-τ*B-W,
    a-A*(.cos φ)-τ*B*(.sin φ)-W] axis

lemma margin_eval (axis : Fin 4) (a b A B φ : E) (σ τ : Bool) (env : Fin 3→ℝ) :
    (margin axis a b A B σ τ φ).eval env =
      forwardMargin axis (a.eval env) (b.eval env) (A.eval env) (B.eval env)
        (sign σ) (sign τ) (φ.eval env) := by
  fin_cases axis <;> simp [margin,Expr.eval,forwardMargin,pairWidth]

/-- All hypotheses are necessary inequalities on the original real pair. -/
def pairHypotheses (k : Fin 3) (source target : RadialKind)
    (σ τ : Bool) (axis : Fin 4) : List E :=
  let b := Expr.var 0
  let B := Expr.var 1
  let a := primary source b
  let A := primary target B
  let φ := phase k
  let δ := φ+signedAngle source σ b-signedAngle target τ B
  [a-b,A-B,a-(.const (1/2)),A-(.const (1/2)),
    δ-(.const (19/25)),(.const (3/4))*.pi-δ,
    margin axis a b A B σ τ φ]

def pairBox (source target : RadialKind) : Box 3 :=
  ![transverseBox source,transverseBox target,⟨-7/10,7/10⟩]

/-- Four complete state/axis classes are impossible geometrically.
The first two use only the full zero-quarter frame range; the secondary
classes use the core projection bound at every angle. This predicate
contains no row index, numerical partition, or computed success flag. -/
def CoreSeparatorExcluded (k : Fin 3) (source target : RadialKind)
    (σ τ : Bool) (axis : Fin 4) : Prop :=
  (k=0 ∧ ((axis=1 ∧ target≠.outer) ∨ (axis=3 ∧ source≠.outer))) ∨
    (axis=0 ∧ σ=false ∧ target≠.outer) ∨
    (axis=2 ∧ τ=true ∧ source≠.outer)

instance (k : Fin 3) (source target : RadialKind) (σ τ : Bool) (axis : Fin 4) :
    Decidable (CoreSeparatorExcluded k source target σ τ axis) := by
  unfold CoreSeparatorExcluded
  infer_instance

def commonLabel (kind : RadialKind) (σ : Bool) (b : E) : E :=
  let a := primary kind b
  let unsigned := if kind=.outer then
      (.const (-9/100))+(.const (13/200))*a+(.const (203/200))*b
    else (.const (73/10))*((.const (7/12))-a)+(.const (291/250))*b
  (.const (sign σ))*unsigned

def commonGamma (k : Fin 3) : ℚ := ![391/400,157/200,163/200] k

def commonProblem (k : Fin 3) (source target : RadialKind)
    (σ τ : Bool) (axis : Fin 4) : Problem 3 where
  hypotheses := pairHypotheses k source target σ τ axis
  conclusion := phase k+commonLabel source σ (.var 0)-commonLabel target τ (.var 1)-
    (.const (commonGamma k))

inductive WrongWord | short | second
  deriving DecidableEq, Fintype, Repr

def wrongWord : WrongWord→QuarterWord
  | .short => ![0,0,1,0,1,1,1]
  | .second => ![0,0,1,1,0,1,1]

def allowed (w : WrongWord) (i : Vertex) (σ τ : Bool) : Prop :=
  (i=0→σ=true) ∧ (i=2→σ=false) ∧
  (next i=0→τ=true) ∧ (next i=2→τ=false) ∧
  (wrongWord w i=0→¬(σ=false ∧ τ=true))
instance (w : WrongWord) (i : Vertex) (σ τ : Bool) : Decidable (allowed w i σ τ) := by
  unfold allowed; infer_instance

/-- Exact coefficients from `short_hand_labels.json`, denominator 100000.
The missing signs at roles 0 and 2 are unreachable by `allowed`; zeros keep
the lookup total and do not certify either excluded sign. -/
def shortCoefficients : Vertex→Fin 2→Fin 2→Fin 3→ℤ :=
  ![![![![0,0,0],![0,0,94766]],![![0,0,0],![3177,0,108816]]],![![![24463,-13422,103828],![6130,0,99940]],![![-14041,0,62095],![25648,0,62095]]],![![![-2623,9133,88074],![0,0,0]],![![11680,0,113855],![0,0,0]]],![![![50866,-33147,113360],![-68803,51554,119909]],![![-15540,0,62750],![4149,0,104729]]],![![![-23483,19335,76744],![6294,0,71553]],![![3897,0,104073],![25812,0,58829]]],![![![29579,-20967,83048],![2448,0,86884]],![![1027,0,95269],![2448,0,99195]]],![![![-18660,18602,80996],![-20704,21826,83472]],![![7651,0,99173],![9072,0,95324]]]]

/-- Exact quadratic coefficients with the source reflection identity expanded.
The entire signed polynomial is multiplied by sigma for this label system. -/
def secondCoefficients : Vertex→Fin 2→Fin 2→Fin 5→ℤ :=
  ![![![![394,0,33945,0,39635],![2478,0,93015,2363,-11055]],![![19911,0,63607,0,0],![125,0,103981,0,0]]],![![![0,-26,83194,-11864,17627],![0,-26,83194,-11864,17627]],![![19555,0,63132,0,0],![19555,0,63132,0,0]]],![![![2478,0,93015,2363,-11055],![394,0,33945,0,39635]],![![125,0,103981,0,0],![19911,0,63607,0,0]]],![![![1670,0,242322,-91744,-95769],![0,-1025,16031,0,63457]],![![22042,-34492,98439,-5334,0],![-1449,0,104240,0,0]]],![![![0,-2112,29090,0,44642],![3965,0,385510,-149748,-189442]],![![16823,0,62312,0,0],![4970,0,94831,0,0]]],![![![3965,0,385510,-149748,-189442],![0,-2112,29090,0,44642]],![![4970,0,94831,0,0],![16823,0,62312,0,0]]],![![![0,-1025,16031,0,63457],![1670,0,242322,-91744,-95769]],![![-1449,0,104240,0,0],![22042,-34492,98439,-5334,0]]]]

def radialIndex (kind : RadialKind) : Fin 2 := if kind=.outer then 0 else 1
def signIndex (σ : Bool) : Fin 2 := if σ then 1 else 0

def wrongLabel (w : WrongWord) (i : Vertex) (kind : RadialKind) (σ : Bool) (b : E) : E :=
  let a := primary kind b
  match w with
  | .short =>
      let v := shortCoefficients i (radialIndex kind) (signIndex σ)
      (.const ((v 0:ℚ)/100000))+(.const ((v 1:ℚ)/100000))*a+
        (.const (sign σ*(v 2:ℚ)/100000))*b
  | .second =>
      let v := secondCoefficients i (radialIndex kind) (signIndex σ)
      (.const (sign σ))*((.const ((v 0:ℚ)/100000))+
        (.const ((v 1:ℚ)/100000))*a+(.const ((v 2:ℚ)/100000))*b+
        (.const ((v 3:ℚ)/100000))*b^2+(.const ((v 4:ℚ)/100000))*a*b)

def wrongGamma (w : WrongWord) (i : Vertex) : ℚ :=
  if w=.short ∧ i=2 then 359/400 else 17953/20000

def wrongProblem (w : WrongWord) (i : Vertex) (source target : RadialKind)
    (σ τ : Bool) (axis : Fin 4) : Problem 3 where
  hypotheses := pairHypotheses (wrongWord w i) source target σ τ axis
  conclusion := phase (wrongWord w i)+wrongLabel w i source σ (.var 0)-
    wrongLabel w (next i) target τ (.var 1)-(.const (wrongGamma w i))

lemma local_environment (source target : RadialKind) (σ τ : Bool) (k : Fin 3) (axis : Fin 4)
    {a b A B d : ℝ} (ha : 1/2<a) (hA : 1/2<A)
    (hb : 0≤b) (hB : 0≤B) (hba : b≤a) (hBA : B≤A)
    (hsource : BoundaryState Q0 source a b) (htarget : BoundaryState Q0 target A B)
    (hd : |d|≤7/10)
    (hgap : 19/25≤d+(k.val:ℝ)*Real.pi/2+
        (sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A) ∧
      d+(k.val:ℝ)*Real.pi/2+
        (sign σ:ℝ)*Real.arctan (b/a)-(sign τ:ℝ)*Real.arctan (B/A)≤3*Real.pi/4)
    (haxis : 0≤forwardMargin axis a b A B (sign σ) (sign τ) (d+(k.val:ℝ)*Real.pi/2)) :
    (pairBox source target).Mem ![b,B,d] ∧
      (∀e∈pairHypotheses k source target σ τ axis,0≤e.eval ![b,B,d]) := by
  obtain ⟨hea,hboxb⟩ := actual_primary source ha hb hba hsource
  obtain ⟨heA,hboxB⟩ := actual_primary target hA hB hBA htarget
  have hp : (phase k).eval ![b,B,d]=d+(k.val:ℝ)*Real.pi/2 := by
    simp [phase,Expr.eval]
    ring
  have hs : (primary source (.var 0)).eval ![b,B,d]=a := by
    simpa [Expr.eval] using hea.symm
  have ht : (primary target (.var 1)).eval ![b,B,d]=A := by
    simpa [Expr.eval] using heA.symm
  constructor
  · intro i
    fin_cases i
    · exact hboxb
    · exact hboxB
    · exact abs_le.mp hd
  · intro e he
    simp only [pairHypotheses,List.mem_cons,List.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [Expr.eval,hs,ht,primary_eval,← hea,← heA,phase,
      signedAngle,margin_eval] at *
    all_goals norm_num at *
    all_goals first | linarith [hgap.1,hgap.2] | exact haxis

set_option maxRecDepth 200000 in
theorem all_original_case_count (w : WrongWord) :
    (Finset.univ.filter (fun p : Vertex×Bool×Bool => allowed w p.1 p.2.1 p.2.2)).card=19 := by
  cases w <;> decide

end SquaresInCircles.Eight.WordProblems
