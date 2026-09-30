import SquaresInCircles.Six.Normalization.PinReflection
import SquaresInCircles.Six.Normalization.Certificates.Semantics

/-!
# Cardinal-helper angle windows in the actual labelled packing

These are the six relevant pin/cardinal cases of the supplied L3-prime
checks. The concrete computations have Lean `decide` proof bodies and the
same exact-rational mirror has completed all six. No certificate flag is an
input to the exported geometric statements.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SquaresInCircles.Six.Normalization
open Certificates ProofTools

noncomputable def cardinalCenter : CentralAxis → ℝ
  | .east => 0
  | .north => Real.pi/2
  | .west => Real.pi
  | .south => 3*Real.pi/2
  | _ => 0

def cardinalCenterE {n : ℕ} : CentralAxis → Expr n
  | .east => 0
  | .north => .pi/2
  | .west => .pi
  | .south => r (3/2)*.pi
  | _ => 0

def cardinalCasePin : Fin 6 → Fin 5 := ![0,1,2,3,3,4]
def cardinalCaseAxis : Fin 6 → CentralAxis := ![.east,.north,.west,.west,.south,.south]

def cardinalWindowFormula (j : Fin 6) : Formula 3 :=
  let i := cardinalCasePin j
  let k := cardinalCaseAxis j
  let t := Expr.var 0
  let a := Expr.var 1
  let b := Expr.var 2
  .imp (.all [.le (r (1/2)) a,.le (.abs b) a,.le (containE a b) q0E,
    .lt 0 (pinMarginE t a b (pinE i).1 (pinE i).2),
    .le 0 (upperE k t a b 0 c0E 0 c0E)])
    (.conj (.lt (r (-2/5)) (t-cardinalCenterE k))
      (.lt (t-cardinalCenterE k) (r (2/5))))

theorem cardinalWindow_checked (j : Fin 6) :
    certify (cardinalWindowFormula j) (fun _ => 1) 0 64
      (windowRoot (cardinalCasePin j)) = true := by
  fin_cases j <;> decide

@[simp] lemma denote_cardinalCenterE {n : ℕ} (x : Fin n → ℝ) (k : CentralAxis) :
    Expr.denote (cardinalCenterE k : Expr n) x = cardinalCenter k := by
  cases k <;> simp [cardinalCenterE,Expr.denote,cardinalCenter,div_eq_mul_inv,mul_assoc]

noncomputable section

lemma PinPacking.window_near_center {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    -Real.pi ≤ P.phase i-phaseCenter i ∧ P.phase i-phaseCenter i ≤ Real.pi := by
  have h := P.window i
  fin_cases i <;> norm_num [windowLower,windowUpper] at h <;>
    constructor <;> linarith [h.1,h.2,Real.pi_gt_d2]

/-- N25 in each of the six pin/cardinal cases, before D is forced OWN. -/
theorem PinPacking.cardinal_angle {R : ℝ} (P : PinPacking R) (j : Fin 6)
    (hk : 0 ≤ centralMargin (cardinalCaseAxis j)
      (P.phase (cardinalCasePin j)) (P.radial (cardinalCasePin j))
      (P.transverse (cardinalCasePin j)) P.center.1 P.center.2) :
    |P.phase (cardinalCasePin j)-cardinalCenter (cardinalCaseAxis j)| < 2/5 := by
  let i := cardinalCasePin j
  let k := cardinalCaseAxis j
  let x : Fin 3 → ℝ := ![P.phase i,P.radial i,P.transverse i]
  have hx := windowRoot_mem i (P.window_near_center i) (P.contained i)
  have hc := certify_sound (cardinalWindowFormula j) (fun _ => 1) 0 64
    (cardinalWindow_checked j) hx
  have hu := hk.trans (centralMargin_le_upper P.box.1 P.box.2 (cardinalCaseAxis j))
  have hpin : 0 < pinMargin (P.phase i) (P.radial i) (P.transverse i) (fixedPin i) :=
    pinMargin_pos_iff.mpr (P.pin i)
  have hinput : Formula.Holds
      (.all [.le (r (1/2)) (.var 1),.le (.abs (.var 2)) (.var 1),
        .le (containE (.var 1) (.var 2)) q0E,
        .lt 0 (pinMarginE (.var 0) (.var 1) (.var 2) (pinE i).1 (pinE i).2),
        .le 0 (upperE k (.var 0) (.var 1) (.var 2) 0 c0E 0 c0E)]) x := by
    simpa [x,Formula.all,Formula.Holds,Expr.denote,containE,phi] using
      And.intro (P.contained i).half_le (And.intro (P.contained i).u_le
        (And.intro (P.contained i).containment (And.intro hpin hu)))
  have hr := hc hinput
  apply abs_lt.mpr
  simpa [i,k,x,Formula.Holds,Expr.denote] using hr

/-- The one global D reflection rules out its south-cardinal alternative. -/
theorem PinPacking.D_south_negative {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) :
    centralMargin .south (P.phase 3) (P.radial 3) (P.transverse 3) P.center.1 P.center.2 < 0 := by
  by_contra! h
  have hh := P.cardinal_angle 4 h
  have hl := (abs_lt.mp hh).1
  norm_num [cardinalCasePin,cardinalCaseAxis,cardinalCenter] at hl
  linarith [Real.pi_gt_d2]

def matchingCardinal : Fin 5 → CentralAxis := ![.east,.north,.west,.west,.south]

/-- N21: the matching cardinal separator or OWN, after D's half-window choice. -/
theorem PinPacking.two_choice {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) (i : Fin 5) :
    0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 ∨
      0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 := by
  obtain ⟨k,hk⟩ := P.separator i
  have ha := P.allowed_separator i k hk
  by_cases hc : k=matchingCardinal i
  · exact Or.inl (by simpa [hc] using hk)
  by_cases ho : k=.own
  · exact Or.inr (by simpa [ho] using hk)
  have hlast : i=3 ∧ k=.south := by
    fin_cases i <;> cases k <;> simp [matchingCardinal,allowed] at *
  rcases hlast with ⟨rfl,rfl⟩
  linarith [P.D_south_negative hD]

/-- Cardinal is preferred on ties: OWN is selected precisely when the cardinal
margin is strictly negative. -/
def PinPacking.canonicalOwn {R : ℝ} (P : PinPacking R) (i : Fin 5) : Bool :=
  decide (centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
    P.center.1 P.center.2 < 0)

lemma PinPacking.canonicalOwn_eq_true {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    P.canonicalOwn i = true ↔
      centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 < 0 := by simp [PinPacking.canonicalOwn]

lemma PinPacking.canonicalOwn_eq_false {R : ℝ} (P : PinPacking R) (i : Fin 5) :
    P.canonicalOwn i = false ↔
      0 ≤ centralMargin (matchingCardinal i) (P.phase i) (P.radial i) (P.transverse i)
        P.center.1 P.center.2 := by simp [PinPacking.canonicalOwn,not_lt]

lemma PinPacking.own_of_canonicalOwn {R : ℝ} (P : PinPacking R)
    (hD : P.phase 3 ≤ 5*Real.pi/4) (i : Fin 5) (hi : P.canonicalOwn i = true) :
    0 ≤ centralMargin .own (P.phase i) (P.radial i) (P.transverse i) P.center.1 P.center.2 := by
  have hh := (P.canonicalOwn_eq_true i).mp hi
  rcases P.two_choice hD i with h | h
  · linarith
  · exact h

end
end SquaresInCircles.Six.Normalization
