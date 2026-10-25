module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Data.Int.Star
public import SquaresInCircles.Eight.Owners.Positive.ScalarPolynomials
public import SquaresInCircles.Eight.Owners.Sole.ECoefficients
public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein

/-!
# Eight squares: explicit whole-interval polynomials for the sole-E endpoints

These are the eighteen sole-EH scalars and the six
additional sole-DE scalars in the two hand proofs. The masses are built
by three rational Newton steps at the left endpoint, followed by cubic
truncation. Every identity and reserve is a kernel arithmetic proof
which has not been run. No numerical samples or external replay occur.

The polynomial bounds are kept separate from their trigonometric and
radical transfer. Their presence alone is not a geometric exclusion.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SoleScalarPolynomials
open Polynomial WholeIntervalPolynomial SoleECoefficients

inductive ScalarCase where
  | lowE | lowG
  | middleE (i : Fin 4) | middleG (i : Fin 4)
  | highE (i : Fin 4) | highG (i : Fin 4)
  | lowDE | middleDE (i : Fin 4) | highDEH
  deriving DecidableEq

instance : Fintype ScalarCase where
  elems := {.lowE, .lowG, .lowDE, .highDEH} ∪
    Finset.univ.image ScalarCase.middleE ∪
    Finset.univ.image ScalarCase.middleG ∪
    Finset.univ.image ScalarCase.highE ∪
    Finset.univ.image ScalarCase.highG ∪
    Finset.univ.image ScalarCase.middleDE
  complete x := by cases x <;> simp

def band : ScalarCase → Band
  | .lowE | .lowG | .lowDE => .low
  | .middleE _ | .middleG _ | .middleDE _ => .middle
  | _ => .high

def origin : Band → ℚ
  | .low => 0 | .middle => 1/5 | .high => 7/20

def length : Band → ℚ
  | .low => 1/5 | .middle => 3/20 | .high => 7/20

def negativeIndex : ScalarCase → Fin 4
  | .lowE | .lowG | .lowDE => 2
  | .middleE i | .middleG i | .highE i | .highG i | .middleDE i => i
  | .highDEH => 0

def atG : ScalarCase → Bool
  | .lowG | .middleG _ | .highG _ | .highDEH => true
  | _ => false

def isDE : ScalarCase → Bool
  | .lowDE | .middleDE _ => true
  | _ => false

def radiusUpper : ℚ := 989385433/500000000
def axisUpper : ℚ := 1414558471/1000000000
def margin : ℚ := 1/100000000

def parameter (b : Band) : ℚ[X] := C (origin b)+X
def sine (b : Band) : ℚ[X] := PositiveScalarPolynomials.sine.comp (parameter b)
def cosine (b : Band) : ℚ[X] := PositiveScalarPolynomials.cosine.comp (parameter b)
def halfSine (b : Band) : ℚ[X] :=
  PositiveScalarPolynomials.sine.comp (C (1/2)*parameter b)

def k : Band → ℚ[X]
  | .low => C (17253/20000)+C (11/20)*X+C (3/10)*X^2
  | .middle => C (983/1000)+C (1/10)*X-C (3/10)*X^2
  | .high => C (1017/1000)-C (1/50)*parameter .high

def c : Band → ℚ[X]
  | .low => k .low+C (3/10)*X
  | .middle => C (209/200)+C (13/20)*X-C (3/2)*X^2
  | .high => C (113/100)

def ell : Band → ℚ[X]
  | .low => C (50521/100000)+C (823/1000)*X+C (7/10)*X^2
  | .middle => C (349/500)+C (9/10)*X-X^2
  | .high => C (7/10)+C (9/25)*parameter .high

def g : Band → ℚ[X]
  | .low => C (8/25)
  | .middle => C (31/100)
  | .high => C (27/100)+C (2/25)*parameter .high

def eta : Band → ℚ[X]
  | .low => C (131/500)+C (267/1000)*X+C (1/10)*X^2
  | .middle => C (319/1000)+C (1/5)*X
  | .high => C (7/20)

def n (b : Band) : ℚ[X] := k b*(cosine b+g b*sine b)
def p (b : Band) : ℚ[X] := if b=.high then 1 else cosine b+eta b*sine b
def r (b : Band) : ℚ[X] := cosine b+C (7/10)*sine b

def first (s : ScalarCase) : Fin 4 → ℚ[X] :=
  let b := band s
  if atG s then ![1,k b,ell b,1]
  else if isDE s then ![r b,k b,ell b,1]
  else ![1,k b,ell b,p b]

def second (s : ScalarCase) : Fin 4 → ℚ[X] :=
  let b := band s
  ![if atG s then n b else k b,ell b,c b,c b]

def nu (s : ScalarCase) : ℚ[X] :=
  let b := band s
  if s=.highDEH then C (53/50)
  else ![if atG s then n b else if isDE s then r b else k b,ell b,c b,c b]
    (negativeIndex s)

def outside (s : ScalarCase) : ℚ[X] :=
  let b := band s
  (if atG s then
      3+2*ell b+3*c b+k b*(1+2*cosine b+(1+2*g b)*sine b)
    else if isDE s then
      3*k b+2*ell b+3*c b+1+C (1/2)*cosine b+
        C (1/2-axisUpper)*sine b+C (3/2)*r b
    else if b=.high then
      3+sine b-C (2*radiusUpper)*halfSine b+3*k b+2*ell b+3*c b
    else
      3*k b+2*ell b+3*c b+1+2*cosine b+(1+2*eta b)*sine b)+
    nu s*(cosine b-1)

def squaredNorm (s : ScalarCase) (i : Fin 4) : ℚ[X] :=
  (first s i)^2+(second s i)^2-
    (if i=negativeIndex s then 2*first s i*second s i*sine (band s) else 0)

def rowSquare (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if hi : i.val<4 then squaredNorm s ⟨i.val,hi⟩
  else if atG s then 1+(g (band s))^2
  else if isDE s=true ∨ band s=.high then 1 else 1+(eta (band s))^2

def rowWeight (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if i.val<4 then 1 else if atG s then k (band s)*sine (band s)
  else if isDE s=true ∨ band s=.high then 0 else sine (band s)

def truncateThree (v : ℚ[X]) : ℚ[X] :=
  C (v.coeff 0)+C (v.coeff 1)*X+C (v.coeff 2)*X^2+C (v.coeff 3)*X^3

def newton (v : ℚ) : ℕ → ℚ
  | 0 => 1
  | j+1 => (newton v j+v/newton v j)/2

def newtonMass (v : ℚ[X]) : ℚ[X] :=
  let v0 := v.coeff 0
  let w := C (1/v0)*(truncateThree v-C v0)
  truncateThree (C (newton v0 3)*(1+C (1/2)*w-C (1/8)*w^2+C (1/16)*w^3))

def massAt (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  if i.val=4 ∧ (isDE s=true ∨ band s=.high) ∧ atG s=false then 1
  else newtonMass (rowSquare s i)

def mass (s : ScalarCase) : ℚ[X] := ∏i : Fin 5,massAt s i
def massExcept (s : ScalarCase) (i : Fin 5) : ℚ[X] :=
  ∏j : Fin 5,if j=i then 1 else massAt s j

def certificate (s : ScalarCase) : ℚ[X] :=
  2*(outside s-C margin)*mass s-C radiusUpper*
    ∑i : Fin 5,rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i

def degree : ScalarCase → ℕ
  | .lowDE => 41
  | _ => 46

theorem length_pos (b : Band) : 0<length b := by cases b <;> norm_num [length]

theorem local_parameter {b : Band} {t : ℝ} (ht : t∈domain b) :
    t-(origin b:ℝ)∈Set.Icc 0 (length b:ℝ) := by
  cases b <;> norm_num [domain,origin,length,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

/-! ### Kernel certificates

Each polynomial of this file is mirrored by a scaled integer coefficient list
(`PolynomialCertificates`). Lists are divided by the gcd of their entries after
every composite step, which keeps the integers short. The Newton steps of
`newtonMass` are carried out on integer numerators and denominators. -/

section Certificates
open WholeIntervalPolynomial.Certificate

/-! #### Kernel arithmetic on coefficient lists

The centering and Chebyshev lists of `PolynomialCertificates` and the bounds `lowerZ`,
`upperZ`, written with the recursors and the integer operations themselves: the kernel reduces
them in fewer steps. Each equals its model. -/

namespace SFast

/-- `l + m`. -/
def addF (l : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun m => m)
    (fun x t ih m => List.casesOn (motive := fun _ => List ℤ) m (x :: t)
      (fun y m' => Int.add x y :: ih m')) l

theorem addF_eq : ∀ l m : List ℤ, addF l m = Certificate.add l m
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: t, y :: m => by
    show Int.add x y :: addF t m = (x+y) :: Certificate.add t m
    rw [addF_eq t m]; rfl

/-- `c • l`. -/
def smulF (c : ℤ) (l : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun x _ ih => Int.mul c x :: ih) l

theorem smulF_eq (c : ℤ) : ∀ l : List ℤ, smulF c l = Certificate.smul c l
  | [] => rfl
  | x :: l => by
    show Int.mul c x :: smulF c l = (c*x) :: Certificate.smul c l
    rw [smulF_eq c l]; rfl

/-- `p • l + q • m`, in one pass. -/
def lincF (p q : ℤ) (l : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun m => smulF q m)
    (fun x t ih m => List.casesOn (motive := fun _ => List ℤ) m (smulF p (x :: t))
      (fun y m' => Int.add (Int.mul p x) (Int.mul q y) :: ih m')) l

theorem lincF_eq (p q : ℤ) : ∀ l m : List ℤ, lincF p q l m = Certificate.add (Certificate.smul p l) (Certificate.smul q m)
  | [], m => by
    show smulF q m = _
    rw [smulF_eq]; rfl
  | x :: t, [] => by
    show smulF p (x :: t) = _
    rw [smulF_eq]; rfl
  | x :: t, y :: m => by
    show Int.add (Int.mul p x) (Int.mul q y) :: lincF p q t m = (p*x+q*y) :: Certificate.add (Certificate.smul p t) (Certificate.smul q m)
    rw [lincF_eq p q t m]; rfl

/-- `a • m + acc`, in one pass. -/
def axpyF (a : ℤ) (m : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun acc => acc)
    (fun x _ ih acc => List.casesOn (motive := fun _ => List ℤ) acc (Int.mul a x :: ih [])
      (fun y acc' => Int.add (Int.mul a x) y :: ih acc')) m

theorem add_nil_right : ∀ l : List ℤ, Certificate.add l [] = l
  | [] => rfl
  | _ :: _ => rfl

theorem axpyF_eq (a : ℤ) : ∀ m acc : List ℤ, axpyF a m acc = Certificate.add (Certificate.smul a m) acc
  | [], _ => rfl
  | x :: m, [] => by
    show Int.mul a x :: axpyF a m [] = (a*x) :: Certificate.smul a m
    rw [axpyF_eq a m [],add_nil_right]; rfl
  | x :: m, y :: acc => by
    show Int.add (Int.mul a x) y :: axpyF a m acc = (a*x+y) :: Certificate.add (Certificate.smul a m) acc
    rw [axpyF_eq a m acc]; rfl

/-- `l * m`, row by row. -/
def mulF (l m : List ℤ) : List ℤ :=
  List.casesOn (motive := fun _ => List ℤ) m []
    (fun _ _ => List.rec (motive := fun _ => List ℤ) [] (fun a _ ih => axpyF a m (0 :: ih)) l)

theorem mulF_eq : ∀ l m : List ℤ, mulF l m = Certificate.mul l m
  | _, [] => by cases ‹List ℤ› <;> rfl
  | [], _ :: _ => rfl
  | a :: l, b :: m => by
    show axpyF a (b :: m) (0 :: mulF l (b :: m)) = _
    rw [axpyF_eq,mulF_eq l (b :: m)]; rfl

/-- `l ^ n`. -/
def powF (l : List ℤ) (n : ℕ) : List ℤ :=
  Nat.rec (motive := fun _ => List ℤ) [1] (fun _ ih => mulF ih l) n

theorem powF_eq (l : List ℤ) : ∀ n : ℕ, powF l n = Certificate.pow l n
  | 0 => rfl
  | n+1 => by
    show mulF (powF l n) l = Certificate.mul (Certificate.pow l n) l
    rw [powF_eq l n,mulF_eq]

/-- The coefficients `a_k num^k den^(n-k)` from index `i` on. -/
def prescaleF (num den n : ℕ) (l : List ℤ) : ℕ → List ℤ :=
  List.rec (motive := fun _ => ℕ → List ℤ) (fun _ => [])
    (fun a _ ih i => Int.mul a (Int.ofNat (Nat.mul (Nat.pow num i) (Nat.pow den (Nat.sub n i))))
      :: ih (Nat.succ i)) l

theorem prescaleF_eq (num den n : ℕ) : ∀ (l : List ℤ) (i : ℕ),
    prescaleF num den n l i = Certificate.prescale num den n i l
  | [], _ => rfl
  | a :: l, i => by
    show _ :: prescaleF num den n l (i+1) = _
    rw [prescaleF_eq num den n l (i+1)]; rfl

/-- Multiplication by `1+X` of `c :: z`, from `z` on. -/
def shiftAuxF (z : List ℤ) : ℤ → List ℤ :=
  List.rec (motive := fun _ => ℤ → List ℤ) (fun c => [c]) (fun x _ ih c => Int.add x c :: ih x) z

theorem shiftAuxF_eq : ∀ (z : List ℤ) (c : ℤ), shiftAuxF z c = Certificate.add z (c :: z)
  | [], _ => rfl
  | x :: z, c => by
    show Int.add x c :: shiftAuxF z x = (x+c) :: Certificate.add z (x :: z)
    rw [shiftAuxF_eq z x]; rfl

/-- Multiplication by `s+tX` of `c :: z`, from `z` on. -/
def affAuxF (s t : ℤ) (z : List ℤ) : ℤ → List ℤ :=
  List.rec (motive := fun _ => ℤ → List ℤ) (fun c => [Int.mul t c])
    (fun x _ ih c => Int.add (Int.mul s x) (Int.mul t c) :: ih x) z

theorem affAuxF_eq (s t : ℤ) : ∀ (z : List ℤ) (c : ℤ), affAuxF s t z c = Certificate.affMulAux s t c z
  | [], _ => rfl
  | x :: z, c => by
    show Int.add (Int.mul s x) (Int.mul t c) :: affAuxF s t z x = _
    rw [affAuxF_eq s t z x]; rfl

/-- `compAff`, by Horner's rule; additions only when `s = t = 1`. -/
def compAffF (s t : ℤ) (l : List ℤ) : List ℤ :=
  if s=1 ∧ t=1 then
    List.rec (motive := fun _ => List ℤ) []
      (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
        (fun x z => Int.add b x :: shiftAuxF z x)) l
  else
    List.rec (motive := fun _ => List ℤ) []
      (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
        (fun x z => Int.add b (Int.mul s x) :: affAuxF s t z x)) l

theorem compAffF_eq (s t : ℤ) (l : List ℤ) : compAffF s t l = Certificate.compAff s t l := by
  unfold compAffF
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    induction l with
    | nil => rfl
    | cons b l ih =>
      show List.casesOn (motive := fun _ => List ℤ) (List.rec (motive := fun _ => List ℤ) []
        (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
          (fun x z => Int.add b x :: shiftAuxF z x)) l) [b]
        (fun x z => Int.add b x :: shiftAuxF z x) = Certificate.add [b] (Certificate.affMul 1 1 (Certificate.compAff 1 1 l))
      rw [ih]
      rcases hc : Certificate.compAff 1 1 l with _ | ⟨x,z⟩
      · rfl
      · show Int.add b x :: shiftAuxF z x = Certificate.add [b] (Certificate.affMul 1 1 (x :: z))
        rw [Certificate.affMul,ite_eq_left ⟨rfl,rfl⟩,Certificate.shiftMul,shiftAuxF_eq]
        show Int.add b x :: _ = (b+(x+0)) :: Certificate.add [] (Certificate.add z (x :: z))
        rw [Int.add_zero]; rfl
  · induction l with
    | nil => rfl
    | cons b l ih =>
      show List.casesOn (motive := fun _ => List ℤ) (List.rec (motive := fun _ => List ℤ) []
        (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
          (fun x z => Int.add b (Int.mul s x) :: affAuxF s t z x)) l) [b]
        (fun x z => Int.add b (Int.mul s x) :: affAuxF s t z x) = Certificate.add [b] (Certificate.affMul s t (Certificate.compAff s t l))
      rw [ih]
      rcases hc : Certificate.compAff s t l with _ | ⟨x,z⟩
      · show [b] = Certificate.add [b] (Certificate.affMul s t [])
        rw [Certificate.affMul,ite_eq_right h]; rfl
      · show Int.add b (Int.mul s x) :: affAuxF s t z x = Certificate.add [b] (Certificate.affMul s t (x :: z))
        rw [Certificate.affMul,ite_eq_right h,affAuxF_eq]; rfl

/-- `centerList`. -/
def centerF (num den : ℕ) (s t : ℤ) (l : List ℤ) : List ℤ :=
  compAffF s t (prescaleF num den (l.length-1) l 0)

theorem centerF_eq (num den : ℕ) (s t : ℤ) (l : List ℤ) :
    centerF num den s t l = Certificate.centerList num den s t l := by
  rw [centerF,compAffF_eq,prescaleF_eq]; rfl

/-- `twoX`. -/
def twoXF (u : List ℤ) : List ℤ :=
  List.casesOn (motive := fun _ => List ℤ) u [] (fun u0 t => addF t (0 :: Int.mul 2 u0 :: t))

theorem twoXF_eq : ∀ u : List ℤ, twoXF u = Certificate.twoX u
  | [] => rfl
  | u0 :: t => by
    show addF t (0 :: Int.mul 2 u0 :: t) = Certificate.add t (0 :: (2*u0) :: t)
    rw [addF_eq]; rfl

/-- `chebList` and `2 ^ length`. -/
def chebPair (l : List ℤ) : List ℤ × ℕ :=
  List.rec (motive := fun _ => List ℤ × ℕ) ([],1)
    (fun a _ ih => (addF [Int.mul a (Int.ofNat ih.2)] (twoXF ih.1),Nat.mul 2 ih.2)) l

theorem chebPair_eq : ∀ l : List ℤ, chebPair l = (Certificate.chebList l,2^l.length)
  | [] => rfl
  | a :: l => by
    show (addF [Int.mul a (Int.ofNat (chebPair l).2)] (twoXF (chebPair l).1),
      Nat.mul 2 (chebPair l).2) = _
    rw [chebPair_eq l,addF_eq,twoXF_eq,Certificate.chebList,List.length_cons,pow_succ,Nat.mul_comm]
    rfl

/-- `chebList`. -/
def chebF (l : List ℤ) : List ℤ := (chebPair l).1

theorem chebF_eq (l : List ℤ) : chebF l = Certificate.chebList l := by
  rw [chebF,chebPair_eq]

/-- The sum of the absolute values. -/
def sumAbsF (l : List ℤ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add (Int.natAbs x) ih) l

theorem sumAbsF_eq_sum {t : List ℤ} {D : ℕ} (h : t.length≤D) :
    ((sumAbsF t:ℕ):ℤ)=∑ j : Fin D,|t.getD j.val 0| := by
  induction t generalizing D with
  | nil => simp [sumAbsF]
  | cons x t ih =>
    obtain ⟨D,rfl⟩ : ∃ D',D=D'+1 := ⟨D-1,by simp at h; omega⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,List.getD_cons_zero,Fin.val_succ,List.getD_cons_succ]
    rw [← ih (by simp at h; omega)]
    show (((Int.natAbs x+sumAbsF t:ℕ)):ℤ)=_
    push_cast
    rfl

/-- `lowerZ` of a list, from its first entry and the rest. -/
def lowL (l : List ℤ) : ℤ :=
  List.casesOn (motive := fun _ => ℤ) l 0 (fun b t => Int.sub b (Int.ofNat (sumAbsF t)))

/-- `upperZ` of a list. -/
def upL (l : List ℤ) : ℤ :=
  List.casesOn (motive := fun _ => ℤ) l 0 (fun b t => Int.add b (Int.ofNat (sumAbsF t)))

theorem lowL_eq {l : List ℤ} {D : ℕ} (h : l.length≤D+1) :
    Certificate.lowerZ D (fun j => l.getD j 0)=lowL l := by
  cases l with
  | nil => simp [Certificate.lowerZ,lowL]
  | cons b t =>
    simp only [Certificate.lowerZ,List.getD_cons_zero,List.getD_cons_succ]
    rw [← sumAbsF_eq_sum (by simp at h; omega)]
    rfl

theorem upL_eq {l : List ℤ} {D : ℕ} (h : l.length≤D+1) :
    Certificate.upperZ D (fun j => l.getD j 0)=upL l := by
  cases l with
  | nil => simp [Certificate.upperZ,upL]
  | cons b t =>
    simp only [Certificate.upperZ,List.getD_cons_zero,List.getD_cons_succ]
    rw [← sumAbsF_eq_sum (by simp at h; omega)]
    rfl

end SFast


/-- `Scaled.add`, `Scaled.sub`, `Scaled.mul` and `Scaled.pow` with the kernel lists. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.addK
    (a b : Scaled) : Scaled := ⟨SFast.lincF b.s a.s a.l b.l,a.s*b.s⟩
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.subK
    (a b : Scaled) : Scaled := ⟨SFast.lincF b.s (-(a.s:ℤ)) a.l b.l,a.s*b.s⟩
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.mulK
    (a b : Scaled) : Scaled := ⟨SFast.mulF a.l b.l,a.s*b.s⟩
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.powK
    (a : Scaled) (n : ℕ) : Scaled := ⟨SFast.powF a.l n,a.s^n⟩

private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.addK
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.addK b).Rep (p+q) := by
  have h := ha.add hb
  rwa [Scaled.add,← SFast.lincF_eq] at h

private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.subK
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.subK b).Rep (p-q) := by
  have h := ha.sub hb
  rwa [Scaled.sub,← SFast.lincF_eq] at h

private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.mulK
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.mulK b).Rep (p*q) := by
  have h := ha.mul hb
  rwa [Scaled.mul,← SFast.mulF_eq] at h

private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.powK
    {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (n : ℕ) : (a.powK n).Rep (p^n) := by
  have h := ha.pow n
  rwa [Scaled.pow,← SFast.powF_eq] at h


/-! #### Dividing a scaled list by the gcd of its entries -/

private def gcdAcc : List ℤ → ℕ → ℕ
  | [],g => g
  | x :: l,g => gcdAcc l (Nat.gcd x.natAbs g)

private theorem gcdAcc_dvd_acc : ∀ (l : List ℤ) (g : ℕ),gcdAcc l g∣g
  | [],_ => dvd_rfl
  | _ :: l,_ => (gcdAcc_dvd_acc l _).trans (Nat.gcd_dvd_right _ _)

private theorem gcdAcc_dvd_mem : ∀ (l : List ℤ) (g : ℕ),∀ x∈l,((gcdAcc l g:ℕ):ℤ)∣x
  | [],_,_,hx => by simp at hx
  | _ :: l,_,x,hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Int.natCast_dvd.2 ((gcdAcc_dvd_acc l _).trans (Nat.gcd_dvd_left _ _))
    · exact gcdAcc_dvd_mem l _ x hx

private theorem toPoly_map_div (g : ℤ) : ∀ l : List ℤ,(∀ x∈l,g∣x) →
    toPoly l=C (g:ℚ)*toPoly (l.map (fun x => x/g))
  | [],_ => by simp [toPoly]
  | x :: l,h => by
    have hx : (x:ℚ)=(g:ℚ)*((x/g:ℤ):ℚ) := by
      rw [← Int.cast_mul,Int.mul_ediv_cancel' (h x List.mem_cons_self)]
    rw [List.map_cons,toPoly,toPoly,
      toPoly_map_div g l (fun y hy => h y (List.mem_cons_of_mem _ hy)),hx,C_mul]
    ring

private theorem toPoly_map_div_zero : ∀ l : List ℤ,toPoly (l.map (fun x => x/(0:ℤ)))=0
  | [] => by simp [toPoly]
  | x :: l => by rw [List.map_cons,toPoly,toPoly_map_div_zero l,Int.ediv_zero]; simp

/-- Trailing zeros removed. -/
private def trim : List ℤ → List ℤ
  | [] => []
  | x :: l => match trim l with
    | [] => if x=0 then [] else [x]
    | y :: t => x :: y :: t

private theorem toPoly_trim : ∀ l : List ℤ,toPoly (trim l)=toPoly l
  | [] => rfl
  | x :: l => by
    have ih := toPoly_trim l
    simp only [trim]
    split
    · rename_i h
      rw [h] at ih
      change (0:ℚ[X])=toPoly l at ih
      change _=C (x:ℚ)+X*toPoly l
      rw [← ih]
      split_ifs with hx
      · rw [hx]; simp [toPoly]
      · change C (x:ℚ)+X*0=_
        rfl
    · rename_i y t h
      rw [h] at ih
      change C (x:ℚ)+X*toPoly (y :: t)=C (x:ℚ)+X*toPoly l
      rw [ih]

/-- The list divided by the gcd of its entries and its scale, without trailing zeros. -/
private def nrm (a : Scaled) : Scaled :=
  ⟨trim (a.l.map (fun x => x/((gcdAcc a.l a.s:ℕ):ℤ))),a.s/gcdAcc a.l a.s⟩

private theorem rep_nrm {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : (nrm a).Rep p := by
  unfold Scaled.Rep at *
  rw [nrm,toPoly_trim]
  have h1 := toPoly_map_div ((gcdAcc a.l a.s:ℕ):ℤ) a.l (gcdAcc_dvd_mem a.l a.s)
  have h2 : gcdAcc a.l a.s∣a.s := gcdAcc_dvd_acc a.l a.s
  generalize gcdAcc a.l a.s=g at h1 h2
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hs : a.s=0 := Nat.eq_zero_of_zero_dvd h2
    simp only [Nat.cast_zero,Nat.div_zero,map_zero,zero_mul] at h1 ⊢
    exact toPoly_map_div_zero a.l
  · have hgq : (g:ℚ)≠0 := by exact_mod_cast hg.ne'
    have hdiv : ((a.s/g:ℕ):ℚ)=(a.s:ℚ)/g := Nat.cast_div h2 hgq
    apply mul_left_cancel₀ (show (C (g:ℚ):ℚ[X])≠0 from C_ne_zero.2 hgq)
    push_cast at h1
    rw [← h1,ha,hdiv,← mul_assoc,← C_mul,mul_div_cancel₀ _ hgq]

/-! #### Coefficients of a represented polynomial -/

private theorem rep_coeff_mul {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (j : ℕ) :
    (a.s:ℚ)*p.coeff j=(a.l.getD j 0:ℚ) := by
  have h := congrArg (fun q : ℚ[X] => q.coeff j) ha
  simp only [coeff_toPoly,coeff_C_mul] at h
  exact h.symm

/-- `truncateThree`: the first four coefficients. -/
private def trunc4 (a : Scaled) : Scaled :=
  ⟨[a.l.getD 0 0,a.l.getD 1 0,a.l.getD 2 0,a.l.getD 3 0],a.s⟩

private theorem rep_trunc4 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (trunc4 a).Rep (truncateThree p) := by
  unfold Scaled.Rep trunc4 truncateThree
  simp only [toPoly]
  rw [← rep_coeff_mul ha 0,← rep_coeff_mul ha 1,← rep_coeff_mul ha 2,← rep_coeff_mul ha 3]
  simp only [C_mul,mul_zero,add_zero]
  ring

/-- `C (p.coeff 0)`. -/
private def const0 (a : Scaled) : Scaled := ⟨[a.l.getD 0 0],a.s⟩

private theorem rep_const0 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) :
    (const0 a).Rep (C (p.coeff 0)) := by
  unfold Scaled.Rep const0
  simp only [toPoly,mul_zero,add_zero]
  rw [← rep_coeff_mul ha 0,C_mul]

/-- `C (1/p.coeff 0)`, when the constant coefficient is positive. -/
private def inv0 (a : Scaled) : Scaled := ⟨[(a.s:ℤ)],(a.l.getD 0 0).toNat⟩

private theorem rep_inv0 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p)
    (hl : 0<a.l.getD 0 0) (hs : a.s≠0) : (inv0 a).Rep (C (1/p.coeff 0)) := by
  unfold Scaled.Rep inv0
  have h := rep_coeff_mul ha 0
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hl' : ((a.l.getD 0 0).toNat:ℚ)=(a.l.getD 0 0:ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hl.le
  have hp : p.coeff 0=(a.l.getD 0 0:ℚ)/a.s := by field_simp; linarith
  have hl0 : (a.l.getD 0 0:ℚ)≠0 := by exact_mod_cast hl.ne'
  simp only [toPoly,mul_zero,add_zero,Int.cast_natCast]
  rw [← C_mul,hl',hp]
  congr 1
  field_simp

/-- Integer numerator and denominator of the Newton iterates for `l0/s`. -/
private def newtonPair (l0 : ℤ) (s : ℕ) : ℕ → ℤ × ℕ
  | 0 => (1,1)
  | j+1 =>
    let x := newtonPair l0 s j
    (x.1^2*s+l0*x.2^2,2*x.1.toNat*x.2*s)

private theorem newtonPair_spec {l0 : ℤ} {s : ℕ} (hl : 0<l0) (hs : 0<s) :
    ∀ j,0<(newtonPair l0 s j).1 ∧ 0<(newtonPair l0 s j).2 ∧
      newton ((l0:ℚ)/s) j=((newtonPair l0 s j).1:ℚ)/(newtonPair l0 s j).2
  | 0 => by simp [newtonPair,newton]
  | j+1 => by
    obtain ⟨h1,h2,h3⟩ := newtonPair_spec hl hs j
    simp only [newtonPair,newton]
    generalize newtonPair l0 s j=x at h1 h2 h3 ⊢
    obtain ⟨P,Q⟩ := x
    simp only at h1 h2 h3 ⊢
    have hP : ((P.toNat:ℕ):ℚ)=(P:ℚ) := by exact_mod_cast Int.toNat_of_nonneg h1.le
    have hPn : 0<P.toNat := by omega
    have hQz : (0:ℤ)<(Q:ℤ) := by exact_mod_cast h2
    refine ⟨add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) (Int.natCast_nonneg _))
      (mul_pos hl (pow_pos hQz 2)),Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos hPn) h2) hs,?_⟩
    rw [h3]
    push_cast
    rw [hP]
    have hP0 : (P:ℚ)≠0 := by exact_mod_cast h1.ne'
    have hQ0 : (Q:ℚ)≠0 := by exact_mod_cast h2.ne'
    have hs0 : (s:ℚ)≠0 := by exact_mod_cast hs.ne'
    field_simp

/-- `C (newton (p.coeff 0) 3)`. -/
private def newton3 (a : Scaled) : Scaled :=
  ⟨[(newtonPair (a.l.getD 0 0) a.s 3).1],(newtonPair (a.l.getD 0 0) a.s 3).2⟩

private theorem rep_newton3 {a : Scaled} {p : ℚ[X]} (ha : a.Rep p)
    (hl : 0<a.l.getD 0 0) (hs : a.s≠0) : (newton3 a).Rep (C (newton (p.coeff 0) 3)) := by
  unfold Scaled.Rep newton3
  have h := rep_coeff_mul ha 0
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hp : p.coeff 0=(a.l.getD 0 0:ℚ)/a.s := by field_simp; linarith
  obtain ⟨_,h2,h3⟩ := newtonPair_spec hl (Nat.pos_of_ne_zero hs) 3
  have hQ : ((newtonPair (a.l.getD 0 0) a.s 3).2:ℚ)≠0 := by exact_mod_cast h2.ne'
  simp only [toPoly,mul_zero,add_zero]
  rw [hp,h3,← C_mul]
  congr 1
  field_simp

private def newtonMassS (a : Scaled) : Scaled :=
  let w := nrm ((inv0 a).mulK ((trunc4 a).subK (const0 a)))
  nrm (trunc4 ((newton3 a).mulK ((((Scaled.ofNat 1).addK ((Scaled.const (1/2)).mulK w)).subK
    ((Scaled.const (1/8)).mulK (w.pow 2))).addK ((Scaled.const (1/16)).mulK (w.pow 3)))))

private theorem rep_newtonMass {a : Scaled} {p : ℚ[X]} (ha : a.Rep p)
    (hl : 0<a.l.getD 0 0) (hs : a.s≠0) : (newtonMassS a).Rep (newtonMass p) := by
  have hw := rep_nrm ((rep_inv0 ha hl hs).mulK ((rep_trunc4 ha).subK (rep_const0 ha)))
  exact rep_nrm (rep_trunc4 ((rep_newton3 ha hl hs).mulK ((((Scaled.rep_one).addK
    ((Scaled.rep_const _).mulK hw)).subK ((Scaled.rep_const _).mulK (hw.pow 2))).addK
    ((Scaled.rep_const _).mulK (hw.pow 3)))))

end Certificates

section Certificates2
open WholeIntervalPolynomial.Certificate

/-! #### The band polynomials -/

private def sineB : Scaled :=
  nrm ((((((((Scaled.var).subK ((Scaled.const (1/6)).mulK ((Scaled.var).powK 3))).addK
    ((Scaled.const (1/120)).mulK ((Scaled.var).powK 5))).subK
    ((Scaled.const (1/5040)).mulK ((Scaled.var).powK 7))).addK
    ((Scaled.const (1/362880)).mulK ((Scaled.var).powK 9))).subK
    ((Scaled.const (1/39916800)).mulK ((Scaled.var).powK 11))).addK
    ((Scaled.const (1/6227020800)).mulK ((Scaled.var).powK 13))).subK
    ((Scaled.const (1/1307674368000)).mulK ((Scaled.var).powK 15)))

private theorem rep_sineB : sineB.Rep PositiveScalarPolynomials.sine :=
  rep_nrm ((((((((Scaled.rep_var).subK ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 3))).addK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 5))).subK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 7))).addK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 9))).subK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 11))).addK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 13))).subK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 15)))

private def cosineB : Scaled :=
  nrm (((((((((Scaled.ofNat 1).subK ((Scaled.const (1/2)).mulK ((Scaled.var).powK 2))).addK
    ((Scaled.const (1/24)).mulK ((Scaled.var).powK 4))).subK
    ((Scaled.const (1/720)).mulK ((Scaled.var).powK 6))).addK
    ((Scaled.const (1/40320)).mulK ((Scaled.var).powK 8))).subK
    ((Scaled.const (1/3628800)).mulK ((Scaled.var).powK 10))).addK
    ((Scaled.const (1/479001600)).mulK ((Scaled.var).powK 12))).subK
    ((Scaled.const (1/87178291200)).mulK ((Scaled.var).powK 14))).addK
    ((Scaled.const (1/20922789888000)).mulK ((Scaled.var).powK 16)))

private theorem rep_cosineB : cosineB.Rep PositiveScalarPolynomials.cosine :=
  rep_nrm (((((((((Scaled.rep_one).subK ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 2))).addK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 4))).subK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 6))).addK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 8))).subK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 10))).addK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 12))).subK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 14))).addK
    ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 16)))

private theorem comp_parameter (b : Band) (p : ℚ[X]) :
    p.comp (parameter b)=centered (origin b-1) (origin b+1) p := by
  have e1 : (origin b-1+(origin b+1))/2=origin b := by ring
  have e2 : (origin b+1-(origin b-1))/2=(1:ℚ) := by ring
  rw [centered,affine,e1,e2,map_one,one_mul,parameter]

private theorem comp_half (b : Band) (p : ℚ[X]) :
    p.comp (C (1/2)*parameter b)=centered (origin b/2-1/2) (origin b/2+1/2) p := by
  have e1 : (origin b/2-1/2+(origin b/2+1/2))/2=1/2*origin b := by ring
  have e2 : (origin b/2+1/2-(origin b/2-1/2))/2=(1/2:ℚ) := by ring
  rw [centered,affine,e1,e2,parameter,mul_add,← C_mul]

private def sinB : Band → Scaled
  | .low => nrm (sineB.center 1 1 0 1)
  | .middle => nrm (sineB.center 1 5 1 5)
  | .high => nrm (sineB.center 1 20 7 20)

private theorem rep_sinB (b : Band) : (sinB b).Rep (sine b) := by
  rw [sine,comp_parameter]
  cases b <;> exact rep_nrm (rep_sineB.centered _ _ _ _ (by norm_num) (by norm_num [origin])
    (by norm_num [origin]))

private def cosB : Band → Scaled
  | .low => nrm (cosineB.center 1 1 0 1)
  | .middle => nrm (cosineB.center 1 5 1 5)
  | .high => nrm (cosineB.center 1 20 7 20)

private theorem rep_cosB (b : Band) : (cosB b).Rep (cosine b) := by
  rw [cosine,comp_parameter]
  cases b <;> exact rep_nrm (rep_cosineB.centered _ _ _ _ (by norm_num) (by norm_num [origin])
    (by norm_num [origin]))

private def halfSinB : Band → Scaled
  | .low => nrm (sineB.center 1 2 0 1)
  | .middle => nrm (sineB.center 1 10 1 5)
  | .high => nrm (sineB.center 1 40 7 20)

private theorem rep_halfSinB (b : Band) : (halfSinB b).Rep (halfSine b) := by
  rw [halfSine,comp_half]
  cases b <;> exact rep_nrm (rep_sineB.centered _ _ _ _ (by norm_num) (by norm_num [origin])
    (by norm_num [origin]))

private def parHighS : Scaled := (Scaled.const (7/20)).addK (Scaled.var)

private theorem rep_par : parHighS.Rep (parameter .high) :=
  (Scaled.rep_const _).addK (Scaled.rep_var)

private def kS : Band → Scaled
  | .low => ((Scaled.const (17253/20000)).addK ((Scaled.const (11/20)).mulK (Scaled.var))).addK
      ((Scaled.const (3/10)).mulK ((Scaled.var).powK 2))
  | .middle => ((Scaled.const (983/1000)).addK ((Scaled.const (1/10)).mulK (Scaled.var))).subK
      ((Scaled.const (3/10)).mulK ((Scaled.var).powK 2))
  | .high => (Scaled.const (1017/1000)).subK ((Scaled.const (1/50)).mulK (parHighS))

private theorem rep_k : ∀ b,(kS b).Rep (k b)
  | .low => ((Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (Scaled.rep_var))).addK
      ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 2))
  | .middle => ((Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (Scaled.rep_var))).subK
      ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 2))
  | .high => (Scaled.rep_const _).subK ((Scaled.rep_const _).mulK (rep_par))

private def cS : Band → Scaled
  | .low => (kS .low).addK ((Scaled.const (3/10)).mulK (Scaled.var))
  | .middle => ((Scaled.const (209/200)).addK ((Scaled.const (13/20)).mulK (Scaled.var))).subK
      ((Scaled.const (3/2)).mulK ((Scaled.var).powK 2))
  | .high => Scaled.const (113/100)

private theorem rep_c : ∀ b,(cS b).Rep (c b)
  | .low => (rep_k .low).addK ((Scaled.rep_const _).mulK (Scaled.rep_var))
  | .middle => ((Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (Scaled.rep_var))).subK
      ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 2))
  | .high => Scaled.rep_const _

private def ellS : Band → Scaled
  | .low => ((Scaled.const (50521/100000)).addK ((Scaled.const (823/1000)).mulK (Scaled.var))).addK
      ((Scaled.const (7/10)).mulK ((Scaled.var).powK 2))
  | .middle => ((Scaled.const (349/500)).addK ((Scaled.const (9/10)).mulK (Scaled.var))).subK
      ((Scaled.var).powK 2)
  | .high => (Scaled.const (7/10)).addK ((Scaled.const (9/25)).mulK (parHighS))

private theorem rep_ell : ∀ b,(ellS b).Rep (ell b)
  | .low => ((Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (Scaled.rep_var))).addK
      ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 2))
  | .middle => ((Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (Scaled.rep_var))).subK
      ((Scaled.rep_var).powK 2)
  | .high => (Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (rep_par))

private def gS : Band → Scaled
  | .low => Scaled.const (8/25)
  | .middle => Scaled.const (31/100)
  | .high => (Scaled.const (27/100)).addK ((Scaled.const (2/25)).mulK (parHighS))

private theorem rep_g : ∀ b,(gS b).Rep (g b)
  | .low => Scaled.rep_const _
  | .middle => Scaled.rep_const _
  | .high => (Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (rep_par))

private def etaS : Band → Scaled
  | .low => ((Scaled.const (131/500)).addK ((Scaled.const (267/1000)).mulK (Scaled.var))).addK
      ((Scaled.const (1/10)).mulK ((Scaled.var).powK 2))
  | .middle => (Scaled.const (319/1000)).addK ((Scaled.const (1/5)).mulK (Scaled.var))
  | .high => Scaled.const (7/20)

private theorem rep_eta : ∀ b,(etaS b).Rep (eta b)
  | .low => ((Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (Scaled.rep_var))).addK
      ((Scaled.rep_const _).mulK ((Scaled.rep_var).powK 2))
  | .middle => (Scaled.rep_const _).addK ((Scaled.rep_const _).mulK (Scaled.rep_var))
  | .high => Scaled.rep_const _

private def nS (b : Band) : Scaled := nrm ((kS b).mulK ((cosB b).addK ((gS b).mulK (sinB b))))

private theorem rep_n (b : Band) : (nS b).Rep (n b) :=
  rep_nrm ((rep_k b).mulK ((rep_cosB b).addK ((rep_g b).mulK (rep_sinB b))))

private def pS (b : Band) : Scaled :=
  if b=.high then Scaled.ofNat 1 else nrm ((cosB b).addK ((etaS b).mulK (sinB b)))

private theorem rep_p (b : Band) : (pS b).Rep (p b) := by
  unfold pS p
  split_ifs
  · exact Scaled.rep_one
  · exact rep_nrm ((rep_cosB b).addK ((rep_eta b).mulK (rep_sinB b)))

private def rS (b : Band) : Scaled := nrm ((cosB b).addK ((Scaled.const (7/10)).mulK (sinB b)))

private theorem rep_r (b : Band) : (rS b).Rep (r b) :=
  rep_nrm ((rep_cosB b).addK ((Scaled.rep_const _).mulK (rep_sinB b)))

/-! #### The scalar cases -/

private def firstS (s : ScalarCase) : Fin 4 → Scaled :=
  if atG s then ![Scaled.ofNat 1,kS (band s),ellS (band s),Scaled.ofNat 1]
  else if isDE s then ![rS (band s),kS (band s),ellS (band s),Scaled.ofNat 1]
  else ![Scaled.ofNat 1,kS (band s),ellS (band s),pS (band s)]

private theorem rep_ite {c : Prop} [Decidable c] {a b : Scaled} {p q : ℚ[X]}
    (ha : a.Rep p) (hb : b.Rep q) : (if c then a else b).Rep (if c then p else q) := by
  split_ifs
  · exact ha
  · exact hb

private theorem rep_vec4 {a0 a1 a2 a3 : Scaled} {p0 p1 p2 p3 : ℚ[X]} (h0 : a0.Rep p0)
    (h1 : a1.Rep p1) (h2 : a2.Rep p2) (h3 : a3.Rep p3) (j : Fin 4) :
    (![a0,a1,a2,a3] j).Rep (![p0,p1,p2,p3] j) := by
  fin_cases j
  exacts [h0,h1,h2,h3]

private theorem rep_first (s : ScalarCase) (i : Fin 4) : (firstS s i).Rep (first s i) := by
  have h := rep_ite (c := atG s=true)
    (rep_vec4 Scaled.rep_one (rep_k (band s)) (rep_ell (band s)) Scaled.rep_one i)
    (rep_ite (c := isDE s=true)
      (rep_vec4 (rep_r (band s)) (rep_k (band s)) (rep_ell (band s)) Scaled.rep_one i)
      (rep_vec4 Scaled.rep_one (rep_k (band s)) (rep_ell (band s)) (rep_p (band s)) i))
  simp only [firstS,first]
  split_ifs at h ⊢ <;> exact h

private def secondS (s : ScalarCase) : Fin 4 → Scaled :=
  ![if atG s then nS (band s) else kS (band s),ellS (band s),cS (band s),cS (band s)]

private theorem rep_second (s : ScalarCase) (i : Fin 4) : (secondS s i).Rep (second s i) :=
  rep_vec4 (rep_ite (rep_n (band s)) (rep_k (band s))) (rep_ell (band s)) (rep_c (band s))
    (rep_c (band s)) i

private def nuS (s : ScalarCase) : Scaled :=
  if s=.highDEH then Scaled.const (53/50)
  else ![if atG s then nS (band s) else if isDE s then rS (band s) else kS (band s),
    ellS (band s),cS (band s),cS (band s)] (negativeIndex s)

private theorem rep_nu (s : ScalarCase) : (nuS s).Rep (nu s) :=
  rep_ite (Scaled.rep_const _) (rep_vec4 (rep_ite (rep_n (band s))
    (rep_ite (rep_r (band s)) (rep_k (band s)))) (rep_ell (band s)) (rep_c (band s))
    (rep_c (band s)) (negativeIndex s))

private def outsideS (s : ScalarCase) : Scaled :=
  let b := band s
  nrm (((if atG s then
      (((Scaled.ofNat 3).addK ((Scaled.ofNat 2).mulK (ellS b))).addK ((Scaled.ofNat 3).mulK (cS b))).addK
        ((kS b).mulK (((Scaled.ofNat 1).addK ((Scaled.ofNat 2).mulK (cosB b))).addK
          (((Scaled.ofNat 1).addK ((Scaled.ofNat 2).mulK (gS b))).mulK (sinB b))))
    else if isDE s then
      (((((((Scaled.ofNat 3).mulK (kS b)).addK ((Scaled.ofNat 2).mulK (ellS b))).addK
        ((Scaled.ofNat 3).mulK (cS b))).addK (Scaled.ofNat 1)).addK
        ((Scaled.const (1/2)).mulK (cosB b))).addK
        ((Scaled.const (1/2-axisUpper)).mulK (sinB b))).addK ((Scaled.const (3/2)).mulK (rS b))
    else if b=.high then
      (((((Scaled.ofNat 3).addK (sinB b)).subK
        ((Scaled.const (2*radiusUpper)).mulK (halfSinB b))).addK ((Scaled.ofNat 3).mulK (kS b))).addK
        ((Scaled.ofNat 2).mulK (ellS b))).addK ((Scaled.ofNat 3).mulK (cS b))
    else
      ((((((Scaled.ofNat 3).mulK (kS b)).addK ((Scaled.ofNat 2).mulK (ellS b))).addK
        ((Scaled.ofNat 3).mulK (cS b))).addK (Scaled.ofNat 1)).addK
        ((Scaled.ofNat 2).mulK (cosB b))).addK
        (((Scaled.ofNat 1).addK ((Scaled.ofNat 2).mulK (etaS b))).mulK (sinB b)))).addK
    ((nuS s).mulK ((cosB b).subK (Scaled.ofNat 1))))

private theorem rep_outside (s : ScalarCase) : (outsideS s).Rep (outside s) := by
  simp only [outsideS,outside]
  apply rep_nrm
  have hnu := (rep_nu s).mulK ((rep_cosB (band s)).subK (Scaled.rep_one))
  split_ifs
  · exact ((((Scaled.rep_ofNat 3).addK ((Scaled.rep_ofNat 2).mulK (rep_ell _))).addK
      ((Scaled.rep_ofNat 3).mulK (rep_c _))).addK ((rep_k _).mulK (((Scaled.rep_one).addK
      ((Scaled.rep_ofNat 2).mulK (rep_cosB _))).addK (((Scaled.rep_one).addK
      ((Scaled.rep_ofNat 2).mulK (rep_g _))).mulK (rep_sinB _))))).addK hnu
  · exact ((((((((Scaled.rep_ofNat 3).mulK (rep_k _)).addK ((Scaled.rep_ofNat 2).mulK (rep_ell _))).addK
      ((Scaled.rep_ofNat 3).mulK (rep_c _))).addK (Scaled.rep_one)).addK
      ((Scaled.rep_const _).mulK (rep_cosB _))).addK ((Scaled.rep_const _).mulK (rep_sinB _))).addK
      ((Scaled.rep_const _).mulK (rep_r _))).addK hnu
  · exact ((((((Scaled.rep_ofNat 3).addK (rep_sinB _)).subK
      ((Scaled.rep_const _).mulK (rep_halfSinB _))).addK ((Scaled.rep_ofNat 3).mulK (rep_k _))).addK
      ((Scaled.rep_ofNat 2).mulK (rep_ell _))).addK ((Scaled.rep_ofNat 3).mulK (rep_c _))).addK hnu
  · exact (((((((Scaled.rep_ofNat 3).mulK (rep_k _)).addK ((Scaled.rep_ofNat 2).mulK (rep_ell _))).addK
      ((Scaled.rep_ofNat 3).mulK (rep_c _))).addK (Scaled.rep_one)).addK
      ((Scaled.rep_ofNat 2).mulK (rep_cosB _))).addK (((Scaled.rep_one).addK
      ((Scaled.rep_ofNat 2).mulK (rep_eta _))).mulK (rep_sinB _))).addK hnu

private def squaredNormS (s : ScalarCase) (i : Fin 4) : Scaled :=
  (((firstS s i).powK 2).addK ((secondS s i).powK 2)).subK
    (if i=negativeIndex s then
      (((Scaled.ofNat 2).mulK (firstS s i)).mulK (secondS s i)).mulK (sinB (band s))
    else ⟨[],1⟩)

private theorem rep_squaredNorm (s : ScalarCase) (i : Fin 4) :
    (squaredNormS s i).Rep (squaredNorm s i) := by
  simp only [squaredNormS,squaredNorm]
  split_ifs
  · exact (((rep_first s i).powK 2).addK ((rep_second s i).powK 2)).subK
      ((((Scaled.rep_ofNat 2).mulK (rep_first s i)).mulK (rep_second s i)).mulK (rep_sinB _))
  · exact (((rep_first s i).powK 2).addK ((rep_second s i).powK 2)).subK Scaled.rep_zero

private def rowSquareS (s : ScalarCase) (i : Fin 5) : Scaled :=
  nrm (if hi : i.val<4 then squaredNormS s ⟨i.val,hi⟩
    else if atG s then (Scaled.ofNat 1).addK ((gS (band s)).powK 2)
    else if isDE s=true ∨ band s=.high then Scaled.ofNat 1
    else (Scaled.ofNat 1).addK ((etaS (band s)).powK 2))

private theorem rep_rowSquare (s : ScalarCase) (i : Fin 5) :
    (rowSquareS s i).Rep (rowSquare s i) := by
  simp only [rowSquareS,rowSquare]
  apply rep_nrm
  split_ifs
  · exact rep_squaredNorm s _
  · exact (Scaled.rep_one).addK ((rep_g _).powK 2)
  · exact Scaled.rep_one
  · exact (Scaled.rep_one).addK ((rep_eta _).powK 2)

private def rowWeightS (s : ScalarCase) (i : Fin 5) : Scaled :=
  if i.val<4 then Scaled.ofNat 1 else if atG s then (kS (band s)).mulK (sinB (band s))
  else if isDE s=true ∨ band s=.high then ⟨[],1⟩ else sinB (band s)

private theorem rep_rowWeight (s : ScalarCase) (i : Fin 5) :
    (rowWeightS s i).Rep (rowWeight s i) := by
  simp only [rowWeightS,rowWeight]
  split_ifs
  · exact Scaled.rep_one
  · exact (rep_k _).mulK (rep_sinB _)
  · exact Scaled.rep_zero
  · exact rep_sinB _

/-- The rows have positive constant terms and nonzero scales. -/
private def RowsOk (s : ScalarCase) : Prop :=
  ∀ i : Fin 5,0<(rowSquareS s i).l.getD 0 0 ∧ (rowSquareS s i).s≠0

private def massAtS (s : ScalarCase) (i : Fin 5) : Scaled :=
  if i.val=4 ∧ (isDE s=true ∨ band s=.high) ∧ atG s=false then Scaled.ofNat 1
  else newtonMassS (rowSquareS s i)

private theorem rep_massAt {s : ScalarCase} (h : RowsOk s) (i : Fin 5) :
    (massAtS s i).Rep (massAt s i) := by
  simp only [massAtS,massAt]
  split_ifs
  · exact Scaled.rep_one
  · exact rep_newtonMass (rep_rowSquare s i) (h i).1 (h i).2

private def massS (s : ScalarCase) : Scaled :=
  nrm (((((massAtS s 0).mulK (massAtS s 1)).mulK (massAtS s 2)).mulK (massAtS s 3)).mulK
    (massAtS s 4))

private theorem rep_mass {s : ScalarCase} (h : RowsOk s) : (massS s).Rep (mass s) := by
  rw [mass,Fin.prod_univ_five]
  exact rep_nrm (((((rep_massAt h 0).mulK (rep_massAt h 1)).mulK (rep_massAt h 2)).mulK
    (rep_massAt h 3)).mulK (rep_massAt h 4))

private def massExceptS (s : ScalarCase) (i : Fin 5) : Scaled :=
  nrm (((((if (0:Fin 5)=i then Scaled.ofNat 1 else massAtS s 0).mulK
    (if (1:Fin 5)=i then Scaled.ofNat 1 else massAtS s 1)).mulK
    (if (2:Fin 5)=i then Scaled.ofNat 1 else massAtS s 2)).mulK
    (if (3:Fin 5)=i then Scaled.ofNat 1 else massAtS s 3)).mulK
    (if (4:Fin 5)=i then Scaled.ofNat 1 else massAtS s 4))

private theorem rep_massExcept {s : ScalarCase} (h : RowsOk s) (i : Fin 5) :
    (massExceptS s i).Rep (massExcept s i) := by
  rw [massExcept,Fin.prod_univ_five]
  exact rep_nrm (((((rep_ite Scaled.rep_one (rep_massAt h 0)).mulK
    (rep_ite Scaled.rep_one (rep_massAt h 1))).mulK (rep_ite Scaled.rep_one (rep_massAt h 2))).mulK
    (rep_ite Scaled.rep_one (rep_massAt h 3))).mulK (rep_ite Scaled.rep_one (rep_massAt h 4)))

private def termS (s : ScalarCase) (i : Fin 5) : Scaled :=
  ((rowWeightS s i).mulK ((rowSquareS s i).addK ((massAtS s i).powK 2))).mulK (massExceptS s i)

private def certificateS (s : ScalarCase) : Scaled :=
  nrm ((((Scaled.ofNat 2).mulK ((outsideS s).subK (Scaled.const margin))).mulK (massS s)).subK
    ((Scaled.const radiusUpper).mulK (((((termS s 0).addK (termS s 1)).addK (termS s 2)).addK
      (termS s 3)).addK (termS s 4))))

private theorem rep_certificate {s : ScalarCase} (h : RowsOk s) :
    (certificateS s).Rep (certificate s) := by
  have ht (i : Fin 5) : (termS s i).Rep
      (rowWeight s i*(rowSquare s i+(massAt s i)^2)*massExcept s i) :=
    ((rep_rowWeight s i).mulK ((rep_rowSquare s i).addK ((rep_massAt h i).powK 2))).mulK
      (rep_massExcept h i)
  rw [certificate,Fin.sum_univ_five]
  exact rep_nrm ((((Scaled.rep_ofNat 2).mulK ((rep_outside s).subK (Scaled.rep_const _))).mulK
    (rep_mass h)).subK ((Scaled.rep_const _).mulK (((((ht 0).addK (ht 1)).addK (ht 2)).addK
      (ht 3)).addK (ht 4))))

/-- `Scaled.center`, with `SFast.centerF`. -/
private def centerS (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨SFast.centerF num den s t c.l,c.s*den^(c.l.length-1)⟩

private theorem rep_centerS {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (centerS c num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  have h := hc.centered num den s t hden hm hh
  rwa [Scaled.center,← SFast.centerF_eq] at h

/-- Centering on the band interval `[0,length b]`. -/
private def centerB (b : Band) (a : Scaled) : Scaled :=
  match b with
  | .low => nrm (centerS a 1 10 1 1)
  | .middle => nrm (centerS a 3 40 1 1)
  | .high => nrm (centerS a 7 40 1 1)

private theorem rep_centerB (b : Band) {a : Scaled} {q : ℚ[X]} (ha : a.Rep q) :
    (centerB b a).Rep (centered 0 (length b) q) := by
  cases b <;> exact rep_nrm (rep_centerS ha _ _ _ _ (by norm_num) (by norm_num [length])
    (by norm_num [length]))

end Certificates2

section Certificates3
open WholeIntervalPolynomial.Certificate

/-! #### Reserves as integer comparisons -/

private abbrev LowerOk (c : Scaled) (D n d : ℕ) : Prop :=
  (SFast.chebF c.l).length≤D+1 ∧
    (n:ℤ)*((c.s:ℤ)*2^c.l.length)<2*(d:ℤ)*SFast.lowL (SFast.chebF c.l)

private abbrev UpperOk (c : Scaled) (D n d : ℕ) : Prop :=
  (SFast.chebF c.l).length≤D+1 ∧
    2*(d:ℤ)*SFast.upL (SFast.chebF c.l)<(n:ℤ)*((c.s:ℤ)*2^c.l.length)

private theorem lowerOn_gt {c : Scaled} {a b r : ℚ} {q : ℚ[X]} {D n d : ℕ}
    (hc : c.Rep (centered a b q)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (hr : r=(n:ℚ)/d) (hd : 0<d) (h : LowerOk c D n d) : r<lowerOn D a b q := by
  rw [lowerOn_eq_of_rep hc hs hl,← SFast.chebF_eq,SFast.lowL_eq h.1,hr,
    div_lt_div_iff₀ (by exact_mod_cast hd) (scale_pos hs)]
  have h' := (Int.cast_lt (R := ℚ)).mpr h.2
  push_cast at h'
  linarith

private theorem upperOn_lt {c : Scaled} {a b r : ℚ} {q : ℚ[X]} {D n d : ℕ}
    (hc : c.Rep (centered a b q)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (hr : r=(n:ℚ)/d) (hd : 0<d) (h : UpperOk c D n d) : upperOn D a b q<r := by
  rw [upperOn_eq_of_rep hc hs hl,← SFast.chebF_eq,SFast.upL_eq h.1,hr,
    div_lt_div_iff₀ (scale_pos hs) (by exact_mod_cast hd)]
  have h' := (Int.cast_lt (R := ℚ)).mpr h.2
  push_cast at h'
  linarith

/-- The kernel facts for the five rows of one case. -/
private abbrev RowFacts (s : ScalarCase) (i : Fin 5) : Prop :=
  (0<(rowSquareS s i).l.getD 0 0 ∧ (rowSquareS s i).s≠0) ∧
  ((centerB (band s) (rowSquareS s i)).s≠0 ∧
    (centerB (band s) (rowSquareS s i)).l.length≤38+1 ∧
    LowerOk (centerB (band s) (rowSquareS s i)) 38 1 4 ∧
    UpperOk (centerB (band s) (rowSquareS s i)) 38 6 1) ∧
  ((centerB (band s) (massAtS s i)).s≠0 ∧
    (centerB (band s) (massAtS s i)).l.length≤3+1 ∧
    LowerOk (centerB (band s) (massAtS s i)) 3 4 5 ∧
    UpperOk (centerB (band s) (massAtS s i)) 3 3 1)

/-- The kernel facts for the certificate of one case. -/
private abbrev CertFacts (s : ScalarCase) : Prop :=
  (centerB (band s) (certificateS s)).s≠0 ∧
  (centerB (band s) (certificateS s)).l.length≤degree s+1 ∧
  (s≠.lowDE → LowerOk (centerB (band s) (certificateS s)) (degree s) 1 100000)

/-! One kernel computation per case: the rows, the masses and the certificate. -/

private theorem facts_lowE : (∀ i : Fin 5,RowFacts .lowE i) ∧ CertFacts .lowE := by
  decide +kernel

private theorem facts_lowG : (∀ i : Fin 5,RowFacts .lowG i) ∧ CertFacts .lowG := by
  decide +kernel

private theorem facts_middleE0 : (∀ i : Fin 5,RowFacts (.middleE 0) i) ∧ CertFacts (.middleE 0) := by
  decide +kernel

private theorem facts_middleE1 : (∀ i : Fin 5,RowFacts (.middleE 1) i) ∧ CertFacts (.middleE 1) := by
  decide +kernel

private theorem facts_middleE2 : (∀ i : Fin 5,RowFacts (.middleE 2) i) ∧ CertFacts (.middleE 2) := by
  decide +kernel

private theorem facts_middleE3 : (∀ i : Fin 5,RowFacts (.middleE 3) i) ∧ CertFacts (.middleE 3) := by
  decide +kernel

private theorem facts_middleG0 : (∀ i : Fin 5,RowFacts (.middleG 0) i) ∧ CertFacts (.middleG 0) := by
  decide +kernel

private theorem facts_middleG1 : (∀ i : Fin 5,RowFacts (.middleG 1) i) ∧ CertFacts (.middleG 1) := by
  decide +kernel

private theorem facts_middleG2 : (∀ i : Fin 5,RowFacts (.middleG 2) i) ∧ CertFacts (.middleG 2) := by
  decide +kernel

private theorem facts_middleG3 : (∀ i : Fin 5,RowFacts (.middleG 3) i) ∧ CertFacts (.middleG 3) := by
  decide +kernel

private theorem facts_highE0 : (∀ i : Fin 5,RowFacts (.highE 0) i) ∧ CertFacts (.highE 0) := by
  decide +kernel

private theorem facts_highE1 : (∀ i : Fin 5,RowFacts (.highE 1) i) ∧ CertFacts (.highE 1) := by
  decide +kernel

private theorem facts_highE2 : (∀ i : Fin 5,RowFacts (.highE 2) i) ∧ CertFacts (.highE 2) := by
  decide +kernel

private theorem facts_highE3 : (∀ i : Fin 5,RowFacts (.highE 3) i) ∧ CertFacts (.highE 3) := by
  decide +kernel

private theorem facts_highG0 : (∀ i : Fin 5,RowFacts (.highG 0) i) ∧ CertFacts (.highG 0) := by
  decide +kernel

private theorem facts_highG1 : (∀ i : Fin 5,RowFacts (.highG 1) i) ∧ CertFacts (.highG 1) := by
  decide +kernel

private theorem facts_highG2 : (∀ i : Fin 5,RowFacts (.highG 2) i) ∧ CertFacts (.highG 2) := by
  decide +kernel

private theorem facts_highG3 : (∀ i : Fin 5,RowFacts (.highG 3) i) ∧ CertFacts (.highG 3) := by
  decide +kernel

private theorem facts_lowDE : (∀ i : Fin 5,RowFacts .lowDE i) ∧ CertFacts .lowDE := by
  decide +kernel

private theorem facts_middleDE0 : (∀ i : Fin 5,RowFacts (.middleDE 0) i) ∧ CertFacts (.middleDE 0) := by
  decide +kernel

private theorem facts_middleDE1 : (∀ i : Fin 5,RowFacts (.middleDE 1) i) ∧ CertFacts (.middleDE 1) := by
  decide +kernel

private theorem facts_middleDE2 : (∀ i : Fin 5,RowFacts (.middleDE 2) i) ∧ CertFacts (.middleDE 2) := by
  decide +kernel

private theorem facts_middleDE3 : (∀ i : Fin 5,RowFacts (.middleDE 3) i) ∧ CertFacts (.middleDE 3) := by
  decide +kernel

private theorem facts_highDEH : (∀ i : Fin 5,RowFacts .highDEH i) ∧ CertFacts .highDEH := by
  decide +kernel

private theorem case_facts (s : ScalarCase) : (∀ i : Fin 5,RowFacts s i) ∧ CertFacts s := by
  rcases s with _|_|j|j|j|j|_|j|_
  · exact facts_lowE
  · exact facts_lowG
  · fin_cases j
    exacts [facts_middleE0,facts_middleE1,facts_middleE2,facts_middleE3]
  · fin_cases j
    exacts [facts_middleG0,facts_middleG1,facts_middleG2,facts_middleG3]
  · fin_cases j
    exacts [facts_highE0,facts_highE1,facts_highE2,facts_highE3]
  · fin_cases j
    exacts [facts_highG0,facts_highG1,facts_highG2,facts_highG3]
  · exact facts_lowDE
  · fin_cases j
    exacts [facts_middleDE0,facts_middleDE1,facts_middleDE2,facts_middleDE3]
  · exact facts_highDEH

private theorem row_facts (s : ScalarCase) (i : Fin 5) : RowFacts s i := (case_facts s).1 i

private theorem rows_ok (s : ScalarCase) : RowsOk s := fun i => (row_facts s i).1

private theorem cert_facts (s : ScalarCase) : CertFacts s := (case_facts s).2

/-! #### Bernstein coefficients -/

private theorem bern_monomial {D : ℕ} {b : ℚ} (hb : b≠0) {j : ℕ} (hj : j≤D) :
    ∑ i : Fin (D+1),C (b^j*(Nat.choose i.val j:ℚ)/(Nat.choose D j:ℚ))*
      WholeIntervalBernstein.basis D b i=X^j := by
  simp only [WholeIntervalBernstein.basis]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (b^j*(Nat.choose i j:ℚ)/(Nat.choose D j:ℚ))*
    (C ((Nat.choose D i:ℚ)/b^D)*X^i*(C b-X)^(D-i))) (D+1)]
  rw [← Finset.sum_range_add_sum_Ico _ (show j≤D+1 by omega)]
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [Finset.mem_range] at hi
    rw [Nat.choose_eq_zero_of_lt hi]
    simp),zero_add,Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ m∈Finset.range (D+1-j),
      C (b^j*(Nat.choose (j+m) j:ℚ)/(Nat.choose D j:ℚ))*
        (C ((Nat.choose D (j+m):ℚ)/b^D)*X^(j+m)*(C b-X)^(D-(j+m)))=
      C (b^j/b^D)*X^j*(X^m*(C b-X)^(D-j-m)*((D-j).choose m:ℚ[X])) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hc := Nat.choose_mul (n := D) (k := j+m) (s := j) (by omega)
    rw [show j+m-j=m by omega] at hc
    have hcq : (D.choose (j+m):ℚ)*((j+m).choose j:ℚ)=(D.choose j:ℚ)*((D-j).choose m:ℚ) := by
      exact_mod_cast hc
    have hDj : (D.choose j:ℚ)≠0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    have hbD : b^D≠0 := pow_ne_zero _ hb
    have hab : b^j*((j+m).choose j:ℚ)/(D.choose j:ℚ)*((D.choose (j+m):ℚ)/b^D)=
        b^j/b^D*((D-j).choose m:ℚ) := by
      rw [show b^j*((j+m).choose j:ℚ)/(D.choose j:ℚ)*((D.choose (j+m):ℚ)/b^D)=
        b^j/b^D*((D.choose (j+m):ℚ)*((j+m).choose j:ℚ)/(D.choose j:ℚ)) by ring,hcq,
        mul_div_cancel_left₀ _ hDj]
    rw [show D-(j+m)=D-j-m by omega,← C_eq_natCast,pow_add]
    calc _=C (b^j*((j+m).choose j:ℚ)/(D.choose j:ℚ)*((D.choose (j+m):ℚ)/b^D))*
          (X^j*X^m*(C b-X)^(D-j-m)) := by rw [C_mul]; ring
      _=_ := by rw [hab,C_mul]; ring
  rw [Finset.sum_congr rfl hterm,← Finset.mul_sum,show D+1-j=D-j+1 by omega,← add_pow,
    add_sub_cancel,← C_pow,mul_comm (C (b^j/b^D)*X^j),← mul_assoc,← C_mul]
  have hone : b^(D-j)*(b^j/b^D)=1 := by
    rw [← mul_div_assoc,← pow_add,Nat.sub_add_cancel hj,div_self (pow_ne_zero _ hb)]
  rw [hone,map_one,one_mul]

private theorem bern_expansion {D : ℕ} {b : ℚ} (hb : b≠0) {q : ℚ[X]} (hq : q.natDegree≤D) :
    q=WholeIntervalBernstein.expansion D b q := by
  have hco (i : Fin (D+1)) : WholeIntervalBernstein.coefficient D b q i=
      ∑ j∈Finset.range (D+1),q.coeff j*(b^j*(Nat.choose i.val j:ℚ)/(Nat.choose D j:ℚ)) := by
    unfold WholeIntervalBernstein.coefficient
    rw [← Finset.sum_range_add_sum_Ico _ (show i.val+1≤D+1 by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun j hj => by
      rw [Finset.mem_Ico] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp),add_zero]
    refine Finset.sum_congr rfl (fun j _ => by ring)
  simp only [WholeIntervalBernstein.expansion,hco,map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow' (n := D+1) (by omega)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [← bern_monomial hb (by simp at hj; omega),Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul]
  ring

/-- The Bernstein coefficients on `[0,1/5]`, times `s*D!*5^D`. -/
private def bernZ (D : ℕ) (l : List ℤ) (i : ℕ) : ℤ :=
  ∑ j∈Finset.range (i+1),l.getD j 0*5^(D-j)*(i.descFactorial j:ℤ)*((D-j).factorial:ℤ)

private theorem bern_coeff {a : Scaled} {q : ℚ[X]} (ha : a.Rep q) (hs : a.s≠0) {D : ℕ}
    (i : Fin (D+1)) :
    WholeIntervalBernstein.coefficient D (1/5) q i=(bernZ D a.l i:ℚ)/(a.s*D.factorial*5^D) := by
  unfold WholeIntervalBernstein.coefficient bernZ
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j≤D := by have := i.isLt; simp at hj; omega
  have hs' : (a.s:ℚ)≠0 := by exact_mod_cast hs
  have hq : q.coeff j=(a.l.getD j 0:ℚ)/a.s := by
    have h := rep_coeff_mul ha j
    field_simp
    linarith
  have h1 : ((i:ℕ).descFactorial j:ℚ)=(j.factorial:ℚ)*((i:ℕ).choose j:ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose _ _
  have h2 : (D.factorial:ℚ)=(D.choose j:ℚ)*(j.factorial:ℚ)*((D-j).factorial:ℚ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hj').symm
  have h3 : (5:ℚ)^D=5^(D-j)*5^j := by rw [← pow_add,Nat.sub_add_cancel hj']
  have hc : (D.choose j:ℚ)≠0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  have hf1 : (j.factorial:ℚ)≠0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hf2 : ((D-j).factorial:ℚ)≠0 := by exact_mod_cast (Nat.factorial_pos (D-j)).ne'
  rw [hq,h1,h2,h3,div_pow,one_pow]
  field_simp

private abbrev BernOk (c : Scaled) (D n d : ℕ) (i : ℕ) : Prop :=
  (n:ℤ)*((c.s:ℤ)*(D.factorial:ℤ)*5^D)≤(d:ℤ)*bernZ D c.l i

private theorem lowDE_facts :
    (certificateS .lowDE).s≠0 ∧ (certificateS .lowDE).l.length≤41+1 ∧
      ∀ i : Fin 42,BernOk (certificateS .lowDE) 41 1 500 i := by
  decide +kernel

end Certificates3

/- These exact reductions are deliberately unrun. Their inputs are the
displayed rational formulas, not a stored angle or state enumeration. -/
theorem certificate_identity (s : ScalarCase) :
    centered 0 (length (band s)) (certificate s)=
      expansion (degree s) (centered 0 (length (band s)) (certificate s)) := by
  exact (rep_centerB _ (rep_certificate (rows_ok s))).eq_expansion (cert_facts s).1
    (cert_facts s).2.1

theorem certificate_reserve (s : ScalarCase) (hs : s≠.lowDE) :
    (1/100000 : ℚ)<lowerOn (degree s) 0 (length (band s)) (certificate s) := by
  exact lowerOn_gt (rep_centerB _ (rep_certificate (rows_ok s))) (cert_facts s).1
    (cert_facts s).2.1 (by norm_num) (by norm_num) ((cert_facts s).2.2 hs)

theorem lowDE_identity : certificate .lowDE=
    WholeIntervalBernstein.expansion 41 (1/5) (certificate .lowDE) := by
  have h := rep_certificate (rows_ok .lowDE)
  exact bern_expansion (by norm_num)
    ((h.natDegree_le lowDE_facts.1).trans (by have := lowDE_facts.2.1; omega))

theorem lowDE_partition :
    (∑i : Fin 42,WholeIntervalBernstein.basis 41 (1/5) i)=1 := by
  have h := bern_monomial (D := 41) (b := 1/5) (by norm_num) (j := 0) (by norm_num)
  simpa using h

theorem lowDE_reserve (i : Fin 42) :
    (1/500 : ℚ)≤WholeIntervalBernstein.coefficient 41 (1/5) (certificate .lowDE) i := by
  have h := rep_certificate (rows_ok .lowDE)
  rw [bern_coeff h lowDE_facts.1 i,le_div_iff₀ (by
    have := Nat.pos_of_ne_zero lowDE_facts.1
    positivity)]
  have h' := (Int.cast_le (R := ℚ)).mpr (lowDE_facts.2.2 i)
  push_cast at h'
  norm_num at h' ⊢
  linarith

theorem mass_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length (band s)) (massAt s i)=
      expansion 3 (centered 0 (length (band s)) (massAt s i)) := by
  exact (rep_centerB _ (rep_massAt (rows_ok s) i)).eq_expansion (row_facts s i).2.2.1
    (row_facts s i).2.2.2.1

theorem mass_reserves (s : ScalarCase) (i : Fin 5) :
    (4/5 : ℚ)<lowerOn 3 0 (length (band s)) (massAt s i) ∧
      upperOn 3 0 (length (band s)) (massAt s i)<3 := by
  have hc := rep_centerB (band s) (rep_massAt (rows_ok s) i)
  obtain ⟨h1,h2,h3,h4⟩ := (row_facts s i).2.2
  exact ⟨lowerOn_gt hc h1 h2 (by norm_num) (by norm_num) h3,
    upperOn_lt hc h1 h2 (by norm_num) (by norm_num) h4⟩

theorem square_identity (s : ScalarCase) (i : Fin 5) :
    centered 0 (length (band s)) (rowSquare s i)=
      expansion 38 (centered 0 (length (band s)) (rowSquare s i)) := by
  exact (rep_centerB _ (rep_rowSquare s i)).eq_expansion (row_facts s i).2.1.1
    (row_facts s i).2.1.2.1

theorem square_reserves (s : ScalarCase) (i : Fin 5) :
    (1/4 : ℚ)<lowerOn 38 0 (length (band s)) (rowSquare s i) ∧
      upperOn 38 0 (length (band s)) (rowSquare s i)<6 := by
  have hc := rep_centerB (band s) (rep_rowSquare s i)
  obtain ⟨h1,h2,h3,h4⟩ := (row_facts s i).2.1
  exact ⟨lowerOn_gt hc h1 h2 (by norm_num) (by norm_num) h3,
    upperOn_lt hc h1 h2 (by norm_num) (by norm_num) h4⟩

theorem certificate_positive (s : ScalarCase) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) : 0<aeval z (certificate s) := by
  by_cases hs : s=.lowDE
  · subst s
    have hh := WholeIntervalBernstein.lower_on_interval (by norm_num : (0:ℚ)<1/5)
      lowDE_identity lowDE_partition lowDE_reserve hz
    norm_num at hh
    linarith
  · have hz' : z∈Set.Icc ((0:ℚ):ℝ) (length (band s):ℝ) := by simpa using hz
    have hh := positive_on_interval (length_pos (band s)) (certificate_identity s)
      (certificate_reserve s hs) hz'
    norm_num at hh
    linarith

theorem mass_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) :
    4/5<aeval z (massAt s i) ∧ aeval z (massAt s i)<3 := by
  have hz' : z∈Set.Icc ((0:ℚ):ℝ) (length (band s):ℝ) := by simpa using hz
  have hh := interval_bounds (length_pos (band s)) (mass_identity s i) hz'
  have hl : (4/5 : ℝ)<(lowerOn 3 0 (length (band s)) (massAt s i):ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).1
    push_cast at h
    exact h
  have hu : (upperOn 3 0 (length (band s)) (massAt s i):ℝ)<(3:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (mass_reserves s i).2
    push_cast at h
    exact h
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem square_bounds (s : ScalarCase) (i : Fin 5) {z : ℝ}
    (hz : z∈Set.Icc 0 (length (band s):ℝ)) :
    1/4<aeval z (rowSquare s i) ∧ aeval z (rowSquare s i)<6 := by
  have hz' : z∈Set.Icc ((0:ℚ):ℝ) (length (band s):ℝ) := by simpa using hz
  have hh := interval_bounds (length_pos (band s)) (square_identity s i) hz'
  have hl : (1/4 : ℝ)<(lowerOn 38 0 (length (band s)) (rowSquare s i):ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).1
    push_cast at h
    exact h
  have hu : (upperOn 38 0 (length (band s)) (rowSquare s i):ℝ)<(6:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (square_reserves s i).2
    push_cast at h
    exact h
  exact ⟨hl.trans_le hh.1,hh.2.trans_lt hu⟩

theorem radius_upper : Real.sqrt qTrial<(radiusUpper:ℝ) := by
  have hs := Real.sq_sqrt (show 0≤qTrial by norm_num [qTrial])
  have hn := Real.sqrt_nonneg qTrial
  norm_num [qTrial,radiusUpper] at *
  nlinarith

theorem axis_upper : axisCoordinate qTrial<(axisUpper:ℝ) := by
  have hs := Real.sq_sqrt (show 0≤qTrial-1/4 by norm_num [qTrial])
  have hn := Real.sqrt_nonneg (qTrial-1/4)
  norm_num [axisCoordinate,qTrial,axisUpper] at *
  nlinarith

end SquaresInCircles.Eight.SoleScalarPolynomials
