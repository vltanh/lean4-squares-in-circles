module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor
public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: the seven explicit rational scalar polynomials

The polynomial builders
are the formulas in the note. The exact identities and rational reserves
below use kernel reduction (`decide`), never `native_decide`, external
arithmetic, or a sampled acceptance predicate. They have not been run.

These theorems establish polynomial positivity. Applying them to the
original trigonometric scalars additionally requires the Taylor and radical
transfer; polynomial positivity by itself is not that geometric exclusion.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.PositiveScalarPolynomials
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

/-! ### Kernel arithmetic on coefficient lists

The list operations of `PolynomialCertificates`, written with the recursors and the integer
operations themselves: the kernel reduces them in fewer steps. Each equals its model. -/

namespace Fast

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

end Fast

/-- `Scaled.add`, in one pass. -/
def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.addF (a b : Scaled) :
    Scaled := ⟨Fast.lincF b.s a.s a.l b.l,a.s*b.s⟩
/-- `Scaled.sub`, in one pass. -/
def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.subF (a b : Scaled) :
    Scaled := ⟨Fast.lincF b.s (-(a.s:ℤ)) a.l b.l,a.s*b.s⟩
/-- `Scaled.neg`. -/
def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.negF (a : Scaled) :
    Scaled := ⟨Fast.smulF (-1) a.l,a.s⟩
/-- `Scaled.mul`. -/
def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.mulF (a b : Scaled) :
    Scaled := ⟨Fast.mulF a.l b.l,a.s*b.s⟩
/-- `Scaled.pow`. -/
def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.powF (a : Scaled)
    (n : ℕ) : Scaled := ⟨Fast.powF a.l n,a.s^n⟩
/-- `Scaled.center`. -/
def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.centerF (c : Scaled)
    (num den : ℕ) (s t : ℤ) : Scaled := ⟨Fast.centerF num den s t c.l,c.s*den^(c.l.length-1)⟩
namespace Fast

theorem Scaled.addF_eq (a b : Scaled) : a.addF b=a.add b := by
  simp only [Scaled.addF,Scaled.add,lincF_eq]

theorem Scaled.subF_eq (a b : Scaled) : a.subF b=a.sub b := by
  simp only [Scaled.subF,Scaled.sub,lincF_eq]

theorem Scaled.negF_eq (a : Scaled) : a.negF=a.neg := by
  simp only [Scaled.negF,Scaled.neg,smulF_eq]

theorem Scaled.mulF_eq (a b : Scaled) : a.mulF b=a.mul b := by
  simp only [Scaled.mulF,Scaled.mul,Fast.mulF_eq]

theorem Scaled.powF_eq (a : Scaled) (n : ℕ) : a.powF n=a.pow n := by
  simp only [Scaled.powF,Scaled.pow,Fast.powF_eq]

theorem Scaled.centerF_eq (c : Scaled) (num den : ℕ) (s t : ℤ) :
    c.centerF num den s t=c.center num den s t := by
  simp only [Scaled.centerF,Scaled.center,Fast.centerF_eq]

end Fast

open Fast

theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.addF
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.addF b).Rep (p+q) := by
  rw [Fast.Scaled.addF_eq]; exact ha.add hb

theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.subF
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.subF b).Rep (p-q) := by
  rw [Fast.Scaled.subF_eq]; exact ha.sub hb

theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.negF
    {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.negF.Rep (-p) := by
  rw [Fast.Scaled.negF_eq]; exact ha.neg

theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.mulF
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.mulF b).Rep (p*q) := by
  rw [Fast.Scaled.mulF_eq]; exact ha.mul hb

theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.powF
    {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (n : ℕ) : (a.powF n).Rep (p^n) := by
  rw [Fast.Scaled.powF_eq]; exact ha.pow n

theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.centeredF
    {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ) {a b : ℚ} (hden : den≠0)
    (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (c.centerF num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  rw [Fast.Scaled.centerF_eq]; exact hc.centered num den s t hden hm hh

/-- The integer form of a lower reserve `n/d < lowerOn`. -/
theorem lt_lowerOn_of_int {c : Scaled} {a b r : ℚ} {q : ℚ[X]} {D n d : ℕ}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b q)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (hl' : (chebF c.l).length≤D+1) (hr : r=(n:ℚ)/d) (hd : 0<d)
    (h : (n:ℤ)*((c.s:ℤ)*Int.ofNat (Nat.pow 2 c.l.length))<2*(d:ℤ)*lowL (chebF c.l)) :
    r<lowerOn D a b q := by
  rw [lowerOn_eq_of_rep hc hs hl,← chebF_eq,lowL_eq hl',hr,
    div_lt_div_iff₀ (by exact_mod_cast hd) (scale_pos hs)]
  have h' := (Int.cast_lt (R := ℚ)).mpr h
  push_cast [Int.ofNat_eq_natCast,Nat.pow_eq] at h'
  linarith

/-- The integer form of an upper reserve `upperOn < n/d`. -/
theorem upperOn_lt_of_int {c : Scaled} {a b r : ℚ} {q : ℚ[X]} {D n d : ℕ}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b q)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (hl' : (chebF c.l).length≤D+1) (hr : r=(n:ℚ)/d) (hd : 0<d)
    (h : 2*(d:ℤ)*upL (chebF c.l)<(n:ℤ)*((c.s:ℤ)*Int.ofNat (Nat.pow 2 c.l.length))) :
    upperOn D a b q<r := by
  rw [upperOn_eq_of_rep hc hs hl,← chebF_eq,upL_eq hl',hr,
    div_lt_div_iff₀ (scale_pos hs) (by exact_mod_cast hd)]
  have h' := (Int.cast_lt (R := ℚ)).mpr h
  push_cast [Int.ofNat_eq_natCast,Nat.pow_eq] at h'
  linarith


inductive ScalarCase where
  | PV | PL | PE | NV | NL | NE | NET
  deriving DecidableEq

instance : Fintype ScalarCase where
  elems := {.PV, .PL, .PE, .NV, .NL, .NE, .NET}
  complete x := by cases x <;> decide

def k : ℚ := 863/1000
def h : ℚ := 7/10
def radiusUpper : ℚ := 494696877/250000000
def epsilon : ℚ := 1/1000000000000

def sine : ℚ[X] :=
  X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7+
    C (1/362880)*X^9-C (1/39916800)*X^11+
    C (1/6227020800)*X^13-C (1/1307674368000)*X^15

def cosine : ℚ[X] :=
  1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+
    C (1/40320)*X^8-C (1/3628800)*X^10+
    C (1/479001600)*X^12-C (1/87178291200)*X^14+
    C (1/20922789888000)*X^16

def isP : ScalarCase → Bool
  | .PV | .PL | .PE => true
  | _ => false

def isV : ScalarCase → Bool
  | .PV | .NV => true
  | _ => false

def l (c : ScalarCase) : ℚ[X] :=
  if isP c then C (1263/2500)+C (49/100)*X-C (27/250)*X^2
  else C (2527/5000)+C (11/20)*X-C (1/5)*X^2

def cWeight (c : ScalarCase) : ℚ[X] :=
  if isP c then C k else C k+C (7/20)*X-C (3/20)*X^2

def eta (c : ScalarCase) : ℚ[X] :=
  if isP c then C (1/4)+C (329/2000)*X else C (19/50)

def lambda (c : ScalarCase) : ℚ[X] :=
  if isP c then C (103/100) else C (1111/1250)+C (1/5)*X

def n (c : ScalarCase) : ℚ[X] := C k*(cosine+eta c*sine)

structure RadicalRow where
  v : ℚ[X]
  a : ℚ[X]
  w : ℚ[X]
  deriving DecidableEq

def dummy : RadicalRow := ⟨0,1,0⟩

def constantRow : RadicalRow :=
  ⟨C (1+k^2),C ((21+20*k)/29),2⟩

def klRow (c : ScalarCase) : RadicalRow :=
  ⟨C (k^2)+(l c)^2,C (1/5)*(C (4*k)+3*l c),1⟩

def tiltedRow (c : ScalarCase) : RadicalRow :=
  ⟨(l c)^2+(n c)^2,C (1/5)*(3*l c+4*n c),1⟩

def primaryRow (c : ScalarCase) : RadicalRow :=
  ⟨1+(eta c)^2,C (1/25)*(24+7*eta c),C k*sine⟩

def HRow (c : ScalarCase) : RadicalRow :=
  ⟨1+(n c)^2,C (1/29)*(21+20*n c),1⟩

def BRow (c : ScalarCase) : RadicalRow :=
  ⟨(l c)^2+(cWeight c)^2,C (1/5)*(3*l c+4*cWeight c),1⟩

def DRow (c : ScalarCase) : RadicalRow :=
  ⟨1+(cWeight c)^2,C (1/29)*(21+20*cWeight c),1⟩

def VRow (c : ScalarCase) : RadicalRow :=
  ⟨C (k^2)+(l c)^2-C (2*k)*l c*sine,
    1-C (1/5)*X-C (33/100)*X^2,1⟩

/-- The fifth P row has zero weight and unit mass; it keeps the product
formula uniform without altering any scalar or degree. -/
def rows (c : ScalarCase) : Fin 5 → RadicalRow :=
  if isP c then
    if isV c then ![constantRow,tiltedRow c,primaryRow c,VRow c,dummy]
    else ![constantRow,klRow c,tiltedRow c,primaryRow c,dummy]
  else if isV c then ![HRow c,BRow c,DRow c,primaryRow c,VRow c]
    else ![HRow c,klRow c,BRow c,DRow c,primaryRow c]

def jCharge : ℚ[X] :=
  -C (1/12)*sine.comp (C h-X)-C (13/12)*(1-cosine.comp (C h-X))

def demand (c : ScalarCase) : ℚ[X] :=
  3+2*l c+3*cWeight c+C k*(1+2*cosine+(1+2*eta c)*sine)+
    match c with
    | .PV | .NV => C k*(cosine-1)
    | .PL | .NL => lambda c*X
    | .PE | .NE => jCharge+l c-C (87/1250)
    | .NET => jCharge+C h*lambda c

def mass (c : ScalarCase) : ℚ[X] := ∏ i : Fin 5,(rows c i).a

def massExcept (c : ScalarCase) (i : Fin 5) : ℚ[X] :=
  ∏ j : Fin 5,if j=i then 1 else (rows c j).a

def certificate (c : ScalarCase) : ℚ[X] :=
  2*(demand c-C epsilon)*mass c-
    C radiusUpper*∑ i : Fin 5,(rows c i).w*((rows c i).v+(rows c i).a^2)*massExcept c i

def degree (c : ScalarCase) : ℕ := if isP c then 35 else 38

def reserve : ScalarCase → ℚ
  | .PV => 87/10000
  | .PL => 167/50000
  | .PE => 579/25000
  | .NV => 1173/100000
  | .NL => 469/50000
  | .NE => 1961/12500
  | .NET => 14079/100000

/-- Build a `Scaled` representation of a polynomial written with `+`, `-`, `*`,
powers, `C`, `X` and numerals, following its syntax; local hypotheses
`Scaled.Rep _ q` are used for the pieces `q` they name. -/
local syntax "repT" : tactic
local macro_rules | `(tactic| repT) => `(tactic| first
  | with_reducible assumption
  | (with_reducible apply Scaled.Rep.mulF; repT; repT)
  | (with_reducible apply Scaled.Rep.addF; repT; repT)
  | (with_reducible apply Scaled.Rep.subF; repT; repT)
  | (with_reducible apply Scaled.Rep.powF; repT)
  | (with_reducible apply Scaled.Rep.negF; repT)
  | with_reducible exact Scaled.rep_const _
  | with_reducible exact Scaled.rep_var
  | with_reducible exact Scaled.rep_zero
  | with_reducible exact Scaled.rep_one
  | with_reducible exact Scaled.rep_ofNat _
  | with_reducible exact Scaled.rep_natCast _)

/-- Unfold a certificate or a row down to the pieces `l`, `cWeight`, `eta`,
`lambda`, `n`, `sine`, `cosine` and their compositions with `h-X`. -/
local macro "unfoldOuter" : tactic => `(tactic| simp only [certificate,demand,mass,massExcept,
  rows,constantRow,klRow,tiltedRow,primaryRow,HRow,BRow,DRow,VRow,dummy,jCharge,isP,isV,
  Fin.sum_univ_five,Fin.prod_univ_five,Matrix.cons_val_zero,
  Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
  Matrix.head_cons,Matrix.tail_cons,Fin.isValue,Fin.reduceFinMk,Fin.reduceEq,eq_self_iff_true,
  Bool.false_eq_true,↓reduceIte])

local macro "unfoldComp" : tactic => `(tactic| simp only [sine,cosine,add_comp,sub_comp,mul_comp,
  pow_comp,neg_comp,C_comp,X_comp,one_comp,ofNat_comp,natCast_comp])

/-! The representations of the shared pieces, built once. -/

private def sineR : {x : Scaled // x.Rep sine} := ⟨_,by simp only [sine]; repT⟩
private def cosineR : {x : Scaled // x.Rep cosine} := ⟨_,by simp only [cosine]; repT⟩
private def sineHR : {x : Scaled // x.Rep (sine.comp (C h-X))} := ⟨_,by unfoldComp; repT⟩
private def cosineHR : {x : Scaled // x.Rep (cosine.comp (C h-X))} := ⟨_,by unfoldComp; repT⟩

private def lR (c : ScalarCase) : {x : Scaled // x.Rep (l c)} :=
  if hc : isP c=true then ⟨_,by rw [l,ite_eq_left hc]; repT⟩
  else ⟨_,by rw [l,ite_eq_right hc]; repT⟩
private def cWeightR (c : ScalarCase) : {x : Scaled // x.Rep (cWeight c)} :=
  if hc : isP c=true then ⟨_,by rw [cWeight,ite_eq_left hc]; repT⟩
  else ⟨_,by rw [cWeight,ite_eq_right hc]; repT⟩
private def etaR (c : ScalarCase) : {x : Scaled // x.Rep (eta c)} :=
  if hc : isP c=true then ⟨_,by rw [eta,ite_eq_left hc]; repT⟩
  else ⟨_,by rw [eta,ite_eq_right hc]; repT⟩
private def lambdaR (c : ScalarCase) : {x : Scaled // x.Rep (lambda c)} :=
  if hc : isP c=true then ⟨_,by rw [lambda,ite_eq_left hc]; repT⟩
  else ⟨_,by rw [lambda,ite_eq_right hc]; repT⟩
private def nR (c : ScalarCase) : {x : Scaled // x.Rep (n c)} :=
  ⟨_,by
    have _hs := sineR.2
    have _hc := cosineR.2
    have _he := (etaR c).2
    simp only [n]; repT⟩

/-- Representations of the shared pieces of case `c`, as local hypotheses. -/
local macro "leaves " c:term : tactic => `(tactic| (
    have _hs := sineR.2
    have _hc := cosineR.2
    have _hsh := sineHR.2
    have _hch := cosineHR.2
    have _hl := (lR $c).2
    have _hw := (cWeightR $c).2
    have _he := (etaR $c).2
    have _hm := (lambdaR $c).2
    have _hn := (nR $c).2))

/-- The kernel facts of a centered certificate list `c`. -/
private abbrev CertOK (c : Scaled) (D n d : ℕ) : Prop :=
  c.s≠0 ∧ c.l.length≤D+1 ∧ (Fast.chebF c.l).length≤D+1 ∧
    (n:ℤ)*((c.s:ℤ)*Int.ofNat (Nat.pow 2 c.l.length))<2*(d:ℤ)*Fast.lowL (Fast.chebF c.l)

private theorem cert_of {c : Scaled} {p : ℚ[X]} {D n d : ℕ} {ρ : ℚ}
    (hc : c.Rep (centered 0 h p)) (hr : ρ=(n:ℚ)/d) (hd : 0<d) (hf : CertOK c D n d) :
    centered 0 h p=expansion D (centered 0 h p) ∧ ρ<lowerOn D 0 h p :=
  ⟨hc.eq_expansion hf.1 hf.2.1,lt_lowerOn_of_int hc hf.1 hf.2.1 hf.2.2.1 hr hd hf.2.2.2⟩

/-! The finite reductions below are kernel computations on integer lists,
one declaration per case. -/

private theorem cert_PV :
    centered 0 h (certificate .PV)=expansion (degree .PV) (centered 0 h (certificate .PV)) ∧
      reserve .PV<lowerOn (degree .PV) 0 h (certificate .PV) := by
  leaves .PV
  exact cert_of (n := 87) (d := 10000) (Scaled.Rep.centeredF (p := certificate .PV)
    (by unfoldOuter; repT) 7 20 1 1 (a := 0) (b := h) (by norm_num [h]) (by norm_num [h])
    (by norm_num [h])) (by norm_num [reserve]) (by norm_num) (by decide +kernel)

private theorem cert_PL :
    centered 0 h (certificate .PL)=expansion (degree .PL) (centered 0 h (certificate .PL)) ∧
      reserve .PL<lowerOn (degree .PL) 0 h (certificate .PL) := by
  leaves .PL
  exact cert_of (n := 167) (d := 50000) (Scaled.Rep.centeredF (p := certificate .PL)
    (by unfoldOuter; repT) 7 20 1 1 (a := 0) (b := h) (by norm_num [h]) (by norm_num [h])
    (by norm_num [h])) (by norm_num [reserve]) (by norm_num) (by decide +kernel)

private theorem cert_PE :
    centered 0 h (certificate .PE)=expansion (degree .PE) (centered 0 h (certificate .PE)) ∧
      reserve .PE<lowerOn (degree .PE) 0 h (certificate .PE) := by
  leaves .PE
  exact cert_of (n := 579) (d := 25000) (Scaled.Rep.centeredF (p := certificate .PE)
    (by unfoldOuter; repT) 7 20 1 1 (a := 0) (b := h) (by norm_num [h]) (by norm_num [h])
    (by norm_num [h])) (by norm_num [reserve]) (by norm_num) (by decide +kernel)

private theorem cert_NV :
    centered 0 h (certificate .NV)=expansion (degree .NV) (centered 0 h (certificate .NV)) ∧
      reserve .NV<lowerOn (degree .NV) 0 h (certificate .NV) := by
  leaves .NV
  exact cert_of (n := 1173) (d := 100000) (Scaled.Rep.centeredF (p := certificate .NV)
    (by unfoldOuter; repT) 7 20 1 1 (a := 0) (b := h) (by norm_num [h]) (by norm_num [h])
    (by norm_num [h])) (by norm_num [reserve]) (by norm_num) (by decide +kernel)

private theorem cert_NL :
    centered 0 h (certificate .NL)=expansion (degree .NL) (centered 0 h (certificate .NL)) ∧
      reserve .NL<lowerOn (degree .NL) 0 h (certificate .NL) := by
  leaves .NL
  exact cert_of (n := 469) (d := 50000) (Scaled.Rep.centeredF (p := certificate .NL)
    (by unfoldOuter; repT) 7 20 1 1 (a := 0) (b := h) (by norm_num [h]) (by norm_num [h])
    (by norm_num [h])) (by norm_num [reserve]) (by norm_num) (by decide +kernel)

private theorem cert_NE :
    centered 0 h (certificate .NE)=expansion (degree .NE) (centered 0 h (certificate .NE)) ∧
      reserve .NE<lowerOn (degree .NE) 0 h (certificate .NE) := by
  leaves .NE
  exact cert_of (n := 1961) (d := 12500) (Scaled.Rep.centeredF (p := certificate .NE)
    (by unfoldOuter; repT) 7 20 1 1 (a := 0) (b := h) (by norm_num [h]) (by norm_num [h])
    (by norm_num [h])) (by norm_num [reserve]) (by norm_num) (by decide +kernel)

private theorem cert_NET :
    centered 0 h (certificate .NET)=expansion (degree .NET) (centered 0 h (certificate .NET)) ∧
      reserve .NET<lowerOn (degree .NET) 0 h (certificate .NET) := by
  leaves .NET
  exact cert_of (n := 14079) (d := 100000) (Scaled.Rep.centeredF (p := certificate .NET)
    (by unfoldOuter; repT) 7 20 1 1 (a := 0) (b := h) (by norm_num [h]) (by norm_num [h])
    (by norm_num [h])) (by norm_num [reserve]) (by norm_num) (by decide +kernel)

theorem certificate_identity (c : ScalarCase) :
    centered 0 h (certificate c)=expansion (degree c) (centered 0 h (certificate c)) := by
  cases c
  exacts [cert_PV.1,cert_PL.1,cert_PE.1,cert_NV.1,cert_NL.1,cert_NE.1,cert_NET.1]

theorem certificate_reserve (c : ScalarCase) :
    reserve c<lowerOn (degree c) 0 h (certificate c) := by
  cases c
  exacts [cert_PV.2,cert_PL.2,cert_PE.2,cert_NV.2,cert_NL.2,cert_NE.2,cert_NET.2]

/-- The expansion identity and the two reserves of one mass polynomial. -/
private def MassOK (p : ℚ[X]) : Prop :=
  centered 0 h p=expansion 16 (centered 0 h p) ∧
    69/100<lowerOn 16 0 h p ∧ upperOn 16 0 h p<3/2

/-- The kernel facts of a centered mass list `c`. -/
private abbrev MassFacts (c : Scaled) : Prop :=
  c.s≠0 ∧ c.l.length≤16+1 ∧ (Fast.chebF c.l).length≤16+1 ∧
    (69:ℤ)*((c.s:ℤ)*Int.ofNat (Nat.pow 2 c.l.length))<2*100*Fast.lowL (Fast.chebF c.l) ∧
    2*2*Fast.upL (Fast.chebF c.l)<(3:ℤ)*((c.s:ℤ)*Int.ofNat (Nat.pow 2 c.l.length))

private theorem massOK_of {c : Scaled} {p : ℚ[X]} (hc : c.Rep (centered 0 h p)) (hf : MassFacts c) :
    MassOK p :=
  ⟨hc.eq_expansion hf.1 hf.2.1,
    lt_lowerOn_of_int (n := 69) (d := 100) hc hf.1 hf.2.1 hf.2.2.1 (by norm_num) (by norm_num)
      hf.2.2.2.1,
    upperOn_lt_of_int (n := 3) (d := 2) hc hf.1 hf.2.1 hf.2.2.1 (by norm_num) (by norm_num)
      hf.2.2.2.2⟩

/-- The eleven distinct mass polynomials. -/
private theorem mass_C : MassOK constantRow.a := by
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_KP : MassOK (klRow .PV).a := by
  leaves .PV
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_TP : MassOK (tiltedRow .PV).a := by
  leaves .PV
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_PP : MassOK (primaryRow .PV).a := by
  leaves .PV
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_V : MassOK (VRow .PV).a := by
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_D : MassOK dummy.a := by
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_H : MassOK (HRow .NV).a := by
  leaves .NV
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_KN : MassOK (klRow .NV).a := by
  leaves .NV
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_B : MassOK (BRow .NV).a := by
  leaves .NV
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_DN : MassOK (DRow .NV).a := by
  leaves .NV
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)
private theorem mass_PN : MassOK (primaryRow .NV).a := by
  leaves .NV
  exact massOK_of (Scaled.Rep.centeredF (by unfoldOuter; repT) 7 20 1 1 (by norm_num [h])
    (by norm_num [h]) (by norm_num [h])) (by decide +kernel)

private theorem mass_rows (c : ScalarCase) (i : Fin 5) : MassOK (rows c i).a := by
  cases c <;> fin_cases i
  exacts [mass_C,mass_TP,mass_PP,mass_V,mass_D,
    mass_C,mass_KP,mass_TP,mass_PP,mass_D,
    mass_C,mass_KP,mass_TP,mass_PP,mass_D,
    mass_H,mass_B,mass_DN,mass_PN,mass_V,
    mass_H,mass_KN,mass_B,mass_DN,mass_PN,
    mass_H,mass_KN,mass_B,mass_DN,mass_PN,
    mass_H,mass_KN,mass_B,mass_DN,mass_PN]

theorem mass_identity (c : ScalarCase) (i : Fin 5) :
    centered 0 h (rows c i).a=expansion 16 (centered 0 h (rows c i).a) :=
  (mass_rows c i).1

theorem mass_reserves (c : ScalarCase) (i : Fin 5) :
    69/100<lowerOn 16 0 h (rows c i).a ∧
      upperOn 16 0 h (rows c i).a<3/2 :=
  (mass_rows c i).2

theorem reserve_pos (c : ScalarCase) : (0:ℚ)<reserve c := by cases c <;> norm_num [reserve]

theorem certificate_positive (c : ScalarCase) {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap) : 0<aeval d (certificate c) := by
  have hd' : d∈Set.Icc ((0:ℚ):ℝ) (h:ℝ) := by simpa [h,frameCap] using hd
  have h := positive_on_interval (by norm_num [h]) (certificate_identity c)
    (certificate_reserve c) hd'
  have hr : (0:ℝ)<(reserve c:ℝ) := by exact_mod_cast reserve_pos c
  exact hr.trans h

theorem mass_positive (c : ScalarCase) (i : Fin 5) {d : ℝ}
    (hd : d∈Set.Icc 0 frameCap) :
    69/100<aeval d (rows c i).a ∧ aeval d (rows c i).a<3/2 := by
  have hd' : d∈Set.Icc ((0:ℚ):ℝ) (h:ℝ) := by simpa [h,frameCap] using hd
  have hb := interval_bounds (by norm_num [h]) (mass_identity c i) hd'
  have hlo : (69/100 : ℝ)<(lowerOn 16 0 h (rows c i).a:ℝ) := by
    have h1 := Rat.cast_lt (K := ℝ) |>.mpr (mass_reserves c i).1
    rwa [show ((69/100 : ℚ) : ℝ)=69/100 by norm_num] at h1
  have hhi : (upperOn 16 0 h (rows c i).a:ℝ)<(3/2 : ℝ) := by
    have h1 := Rat.cast_lt (K := ℝ) |>.mpr (mass_reserves c i).2
    rwa [show ((3/2 : ℚ) : ℝ)=3/2 by norm_num] at h1
  exact ⟨hlo.trans_le hb.1,hb.2.trans_lt hhi⟩

theorem radiusUpper_sq_gt : qCap<(radiusUpper:ℝ)^2 := by norm_num [qCap,radiusUpper]

theorem sine_eval (x : ℝ) : aeval x sine=HighOrderTaylor.S15 x := by
  simp [sine,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7]
  ring

theorem cosine_eval (x : ℝ) : aeval x cosine=HighOrderTaylor.C16 x := by
  simp [cosine,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.cos10,Arithmetic.cos8]
  ring

end SquaresInCircles.Eight.PositiveScalarPolynomials
