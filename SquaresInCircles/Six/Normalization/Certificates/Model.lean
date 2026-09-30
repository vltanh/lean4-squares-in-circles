import SquaresInCircles.Six.Normalization.RelaxedCentral
import SquaresInCircles.Six.Normalization.PinData
import SquaresInCircles.Six.ProofTools.Certificate

/-!
# Historical reified normalization predicates

This exploratory computational model is not an analytic proof dependency.
Ordinary pin, phase and window definitions live in PinData. Analytic geometry
imports PinData without importing this evaluator or its finite checks.
-/

namespace SquaresInCircles.Six.Normalization.Certificates
open ProofTools

abbrev r {n : ℕ} (q : ℚ) : Expr n := .rat q

def q0E {n : ℕ} : Expr n := r (142559/50000)
def rhoE {n : ℕ} : Expr n := .sqrt (q0E-r (1/4))-r (1/2)
def c0E {n : ℕ} : Expr n := rhoE-1

def widthE {n : ℕ} (t : Expr n) : Expr n := (.abs (.cos t)+.abs (.sin t))/2

def xE {n : ℕ} (t a b : Expr n) : Expr n := a * .cos t-b * .sin t
def yE {n : ℕ} (t a b : Expr n) : Expr n := a * .sin t+b * .cos t

def containE {n : ℕ} (a b : Expr n) : Expr n :=
  .sq (a+r (1/2)) + .sq (.abs b+r (1/2))

def lowE {n : ℕ} (l h v : Expr n) : Expr n := .min (l*v) (h*v)
def highE {n : ℕ} (l h v : Expr n) : Expr n := .max (l*v) (h*v)

def upperE {n : ℕ} (k : CentralAxis) (t a b xl xh yl yh : Expr n) : Expr n :=
  match k with
  | .own => a-r (1/2)-lowE xl xh (.cos t)-lowE yl yh (.sin t)-widthE t
  | .secPlus => b-r (1/2)-lowE xl xh (-.sin t)-lowE yl yh (.cos t)-widthE t
  | .secMinus => highE xl xh (-.sin t)+highE yl yh (.cos t)-r (1/2)-widthE t-b
  | .east => xE t a b-widthE t-xl-r (1/2)
  | .west => xh-r (1/2)-xE t a b-widthE t
  | .north => yE t a b-widthE t-yl-r (1/2)
  | .south => yh-r (1/2)-yE t a b-widthE t

def labelE {n : ℕ} (a u : Expr n) : Expr n :=
  .min (.min (r (5/4)*u) (.pi/6+(u-r (1/2))/3+r (3/4)*(1-a))) (.pi/4)

def pinE {n : ℕ} (i : Fin 5) : Expr n × Expr n :=
  ![(r (9/10),0),(0,r (9/10)),
    (r (9/10) * .cos (r (11/12) * .pi),r (9/10) * .sin (r (11/12) * .pi)),
    (r (9/10) * .cos (r (5/4) * .pi),r (9/10) * .sin (r (5/4) * .pi)),
    (r (9/10) * .cos (r (19/12) * .pi),r (9/10) * .sin (r (19/12) * .pi))] i

def pinMarginE {n : ℕ} (t a b qx qy : Expr n) : Expr n :=
  r (1/2)-.max (.abs (qx * .cos t+qy * .sin t-a))
    (.abs (-qx * .sin t+qy * .cos t-b))

def basicE {n : ℕ} (t a b xl xh yl yh : Expr n) : Formula n :=
  .all [.le (r (1/2)) a,.le (.abs b) a,.le (containE a b) q0E,
    .any (CentralAxis.all.map (fun k => .le 0 (upperE k t a b xl xh yl yh)))]

def baseRoot : RBox 3 :=
  ![⟨-22/7,22/7⟩,⟨1/2,1113/1000⟩,⟨-7/10,7/10⟩]

def pinCoverFormula : Formula 3 :=
  let t := Expr.var 0
  let a := Expr.var 1
  let b := Expr.var 2
  .imp (basicE t a b 0 c0E 0 c0E)
    (.any ((List.finRange 5).map (fun i =>
      .lt (r (1/100)) (pinMarginE t a b (pinE i).1 (pinE i).2))))

def centerE {n : ℕ} (i : Fin 5) : Expr n := ![0,.pi/2,.pi,r (5/4)*.pi,r (3/2)*.pi] i

def windowPhaseRoot : Fin 5 → RInterval :=
  ![⟨-22/7,22/7⟩,⟨-11/7,33/7⟩,⟨0,44/7⟩,⟨3/4,71/10⟩,⟨3/2,8⟩]

def windowRoot (i : Fin 5) : RBox 3 :=
  ![windowPhaseRoot i,⟨1/2,1113/1000⟩,⟨-7/10,7/10⟩]

def windowFormula (i : Fin 5) : Formula 3 :=
  let t := Expr.var 0
  let a := Expr.var 1
  let b := Expr.var 2
  .imp (.conj (basicE t a b 0 c0E 0 c0E)
    (.lt 0 (pinMarginE t a b (pinE i).1 (pinE i).2)))
    (.all ([.lt (r (windowLower i)) (t-centerE i),.lt (t-centerE i) (r (windowUpper i))] ++
      (CentralAxis.all.filter (fun k => k ∉ allowed i)).map
        (fun k => .lt (upperE k t a b 0 c0E 0 c0E) 0)))

def arcOutsideE {n : ℕ} (m : Expr n) (am ap : ℚ) : Formula n :=
  .all (([-1,0,1] : List ℤ).map (fun k =>
    .disj (.le (m+r (2*k)*.pi) (r (-am))) (.le (r ap) (m+r (2*k)*.pi))))

def coneFormula (xl xh yl yh : Expr 3) (am ap : ℚ) : Formula 3 :=
  let t := Expr.var 0
  let a := Expr.var 1
  let b := Expr.var 2
  let outsideEast := Formula.disj (.lt t (-.pi/4)) (.lt (.pi/4) t)
  let possible := Formula.any (CentralAxis.all.filterMap (fun k =>
    match k with
    | .east => none
    | .own => some (.conj outsideEast (.le 0 (upperE k t a b xl xh yl yh)))
    | _ => some (.le 0 (upperE k t a b xl xh yl yh))))
  .imp (.all [.le (r (1/2)) a,.le (.abs b) a,.le (containE a b) q0E,possible])
    (.all [.imp (.le 0 b) (arcOutsideE (t+labelE a (.abs b)) am ap),
      .imp (.le b 0) (arcOutsideE (t-labelE a (.abs b)) am ap)])

def gridEdgeE {n : ℕ} (k : ℕ) : Expr n := c0E+(r (1/2)-c0E)*r ((k : ℚ)/8)
noncomputable def gridEdge (k : ℕ) : ℝ := c0+(1/2-c0)*(k:ℝ)/8

def coneA1Formula : Formula 3 := coneFormula c0E (r (1/2)) 0 c0E (99/100) (61/50)
def coneA2Formula (i j : Fin 8) : Formula 3 :=
  coneFormula (gridEdgeE i.val) (gridEdgeE (i.val+1))
    (gridEdgeE j.val) (gridEdgeE (j.val+1)) (27/50) (39/25)

def movingRoot : RBox 4 :=
  ![⟨-5/12,3/10⟩,⟨177/200,1113/1000⟩,⟨-117/250,117/250⟩,⟨0,113/1000⟩]

def movingFormula : Formula 4 :=
  let t := Expr.var 0
  let a := Expr.var 1
  let b := Expr.var 2
  let cx := Expr.var 3
  .imp (.all [.le (r (1/2)) a,.le (.abs b) a,.le (containE a b) q0E,
    .le cx c0E,.le 0 (upperE .own t a b cx cx 0 c0E)])
    (.lt (r (1/20)) (pinMarginE t a b (1+cx) 0))

def pairMarginE {n : ℕ} (i : Fin 4) (t a b T A B : Expr n) : Expr n :=
  let d := T-t
  let c := Expr.cos d
  let s := Expr.sin d
  let h := r (1/2)+widthE d
  ![.abs (A*c-B*s-a)-h,.abs (A*s+B*c-b)-h,
    .abs (A-a*c-b*s)-h,.abs (B+a*s-b*c)-h] i

def wdRoot : RBox 6 :=
  ![⟨2474/1000,3767/1000⟩,⟨177/200,1113/1000⟩,⟨-117/250,117/250⟩,
    ⟨2741/1000,3927/1000⟩,⟨177/200,1113/1000⟩,⟨-117/250,117/250⟩]

def wdFormula : Formula 6 :=
  let t := Expr.var 0
  let a := Expr.var 1
  let b := Expr.var 2
  let T := Expr.var 3
  let A := Expr.var 4
  let B := Expr.var 5
  .disj (.lt t T) (.neg (.all [basicE t a b 0 c0E 0 c0E,basicE T A B 0 c0E 0 c0E,
    .lt 0 (pinMarginE t a b (pinE 2).1 (pinE 2).2),
    .lt 0 (pinMarginE T A B (pinE 3).1 (pinE 3).2),
    .any ((List.finRange 4).map (fun i => .le 0 (pairMarginE i t a b T A B)))]))

section RealInterpretation
variable {n : ℕ} (x : Fin n → ℝ)

@[simp] lemma denote_q0E : Expr.denote (q0E : Expr n) x = Q0 := by
  norm_num [q0E,Expr.denote,Q0]
@[simp] lemma denote_rhoE : Expr.denote (rhoE : Expr n) x = rho0 := by
  simp [rhoE,Expr.denote,rho0]
@[simp] lemma denote_c0E : Expr.denote (c0E : Expr n) x = c0 := by
  simp [c0E,Expr.denote,c0]

@[simp] lemma denote_widthE (t : Expr n) : Expr.denote (widthE t) x = angularWidth (Expr.denote t x) := by
  simp [widthE,Expr.denote,angularWidth,div_eq_mul_inv]
@[simp] lemma denote_xE (t a b : Expr n) :
    Expr.denote (xE t a b) x = centerX (Expr.denote t x) (Expr.denote a x) (Expr.denote b x) := by
  simp [xE,Expr.denote,centerX,sub_eq_add_neg]
@[simp] lemma denote_yE (t a b : Expr n) :
    Expr.denote (yE t a b) x = centerY (Expr.denote t x) (Expr.denote a x) (Expr.denote b x) := by
  simp [yE,Expr.denote,centerY]

@[simp] lemma denote_upperE (k : CentralAxis) (t a b xl xh yl yh : Expr n) :
    Expr.denote (upperE k t a b xl xh yl yh) x =
      centralUpper k (Expr.denote t x) (Expr.denote a x) (Expr.denote b x)
        (Expr.denote xl x) (Expr.denote xh x) (Expr.denote yl x) (Expr.denote yh x) := by
  cases k <;> simp [upperE,lowE,highE,Expr.denote,centralUpper,linearLow,linearHigh,
    widthE,xE,yE,angularWidth,centerX,centerY,div_eq_mul_inv,sub_eq_add_neg]

@[simp] lemma denote_labelE (a u : Expr n) :
    Expr.denote (labelE a u) x = Seven.label (Expr.denote a x) (Expr.denote u x) := by
  simp [labelE,Expr.denote,Seven.label,Seven.axial,Seven.side,div_eq_mul_inv,
    sub_eq_add_neg,mul_assoc,mul_comm,mul_left_comm]

@[simp] lemma denote_pinE (i : Fin 5) :
    (Expr.denote (pinE i).1 x,Expr.denote (pinE i).2 x) = fixedPin i := by
  fin_cases i <;> norm_num [pinE,fixedPin,Expr.denote]

@[simp] lemma denote_pinMarginE (t a b qx qy : Expr n) :
    Expr.denote (pinMarginE t a b qx qy) x =
      pinMargin (Expr.denote t x) (Expr.denote a x) (Expr.denote b x)
        (Expr.denote qx x,Expr.denote qy x) := by
  simp [pinMarginE,Expr.denote,pinMargin,div_eq_mul_inv,sub_eq_add_neg]

@[simp] lemma denote_centerE (i : Fin 5) : Expr.denote (centerE i : Expr n) x = phaseCenter i := by
  fin_cases i <;> norm_num [centerE,phaseCenter,Expr.denote]

@[simp] lemma denote_gridEdgeE (k : ℕ) : Expr.denote (gridEdgeE k : Expr n) x = gridEdge k := by
  simp [gridEdgeE,gridEdge,Expr.denote,div_eq_mul_inv,sub_eq_add_neg,mul_assoc]

end RealInterpretation
end SquaresInCircles.Six.Normalization.Certificates
