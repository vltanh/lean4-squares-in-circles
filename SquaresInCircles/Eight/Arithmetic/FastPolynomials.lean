module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates

/-!
# Eight squares: fast kernel arithmetic on integer coefficient lists

The certificates of `PolynomialCertificates` compute on integer coefficient lists. This module
writes their operations with the recursors (`List.rec`, `Nat.rec`) and the integer operations
themselves (`Int.add`, `Int.mul`, `Nat.pow`, ...), which the kernel reduces in fewer steps than
the definitions by pattern matching. Each operation equals its model.

* `Fast.addF`, `smulF`, `lincF` (`p • l + q • m` in one pass), `mulF`, `powF`, `centerF`
  (`centerList` by Horner's rule, with additions only when `s = t = 1`) and `chebF`
  (`chebList`); `Fast.addF_eq`, ... identify them with the operations of `PolynomialCertificates`.
* `Fast.lowL l` and `Fast.upL l` compute `lowerZ` and `upperZ` of the list `l` by one sum of
  absolute values (`Fast.lowL_eq`, `Fast.upL_eq`).
* `Scaled.addF`, `subF`, `negF`, `mulF`, `powF` and `centerF` are `Scaled.add`, ... with these
  lists: `ha.addF hb : (a.addF b).Rep (p+q)`, ..., and
  `hc.centeredF num den s t hden hm hh : (c.centerF num den s t).Rep (centered a b p)`.
* `Scaled.normF a` divides the list and the scale of `a` by the gcd of all of them and drops the
  trailing zeros (`ha.normF : a.normF.Rep p`). Dividing out the common factor after a composite
  step keeps the integers short. It is worth it on short lists of moderate integers: the kernels
  outside Lean multiply integers of thousands of bits quickly but take their gcd slowly, so a
  long result such as a final numerator is cheaper left undivided.
* `lt_lowerOn_of_int` and `upperOn_lt_of_int` reduce a reserve `n/d < lowerOn D a b q` or
  `upperOn D a b q < n/d` to one integer comparison. The comparison takes the power
  `2^c.l.length` in `ℤ`: the kernel evaluates a natural-number operation on the data (`Nat.pow`,
  `Nat.div`, ...) as soon as it compares two such statements that are not syntactically equal.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate
open Polynomial

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

/-- `c • l`, with `c` the right factor of each product. -/
def smulF (c : ℤ) (l : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun x _ ih => Int.mul x c :: ih) l

theorem smulF_eq (c : ℤ) : ∀ l : List ℤ, smulF c l = Certificate.smul c l
  | [] => rfl
  | x :: l => by
    show (x*c) :: smulF c l = (c*x) :: Certificate.smul c l
    rw [smulF_eq c l,Int.mul_comm]

/-- `p • l + q • m`, in one pass, with `p` and `q` the right factors of the products. -/
def lincF (p q : ℤ) (l : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun m => smulF q m)
    (fun x t ih m => List.casesOn (motive := fun _ => List ℤ) m (smulF p (x :: t))
      (fun y m' => Int.add (Int.mul x p) (Int.mul y q) :: ih m')) l

theorem lincF_eq (p q : ℤ) : ∀ l m : List ℤ,
    lincF p q l m = Certificate.add (Certificate.smul p l) (Certificate.smul q m)
  | [], m => by
    show smulF q m = _
    rw [smulF_eq]; rfl
  | x :: t, [] => by
    show smulF p (x :: t) = _
    rw [smulF_eq]; rfl
  | x :: t, y :: m => by
    show (x*p+y*q) :: lincF p q t m =
      (p*x+q*y) :: Certificate.add (Certificate.smul p t) (Certificate.smul q m)
    rw [lincF_eq p q t m,Int.mul_comm x p,Int.mul_comm y q]

/-- `a • m + acc`, in one pass. -/
def axpyF (a : ℤ) (m : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun acc => acc)
    (fun x _ ih acc => List.casesOn (motive := fun _ => List ℤ) acc (Int.mul a x :: ih [])
      (fun y acc' => Int.add (Int.mul a x) y :: ih acc')) m

theorem add_nil_right : ∀ l : List ℤ, Certificate.add l [] = l
  | [] => rfl
  | _ :: _ => rfl

theorem axpyF_eq (a : ℤ) : ∀ m acc : List ℤ,
    axpyF a m acc = Certificate.add (Certificate.smul a m) acc
  | [], _ => rfl
  | x :: m, [] => by
    show Int.mul a x :: axpyF a m [] = (a*x) :: Certificate.smul a m
    rw [axpyF_eq a m [],add_nil_right]; rfl
  | x :: m, y :: acc => by
    show Int.add (Int.mul a x) y :: axpyF a m acc =
      (a*x+y) :: Certificate.add (Certificate.smul a m) acc
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
  List.rec (motive := fun _ => ℤ → List ℤ) (fun c => [c])
    (fun x _ ih c => Int.add x c :: ih x) z

theorem shiftAuxF_eq : ∀ (z : List ℤ) (c : ℤ), shiftAuxF z c = Certificate.add z (c :: z)
  | [], _ => rfl
  | x :: z, c => by
    show Int.add x c :: shiftAuxF z x = (x+c) :: Certificate.add z (x :: z)
    rw [shiftAuxF_eq z x]; rfl

/-- Multiplication by `s+tX` of `c :: z`, from `z` on. -/
def affAuxF (s t : ℤ) (z : List ℤ) : ℤ → List ℤ :=
  List.rec (motive := fun _ => ℤ → List ℤ) (fun c => [Int.mul c t])
    (fun x _ ih c => Int.add (Int.mul x s) (Int.mul c t) :: ih x) z

theorem affAuxF_eq (s t : ℤ) : ∀ (z : List ℤ) (c : ℤ),
    affAuxF s t z c = Certificate.affMulAux s t c z
  | [], c => by
    show [c*t] = [t*c]
    rw [Int.mul_comm]
  | x :: z, c => by
    show (x*s+c*t) :: affAuxF s t z x = (s*x+t*c) :: Certificate.affMulAux s t x z
    rw [affAuxF_eq s t z x,Int.mul_comm x s,Int.mul_comm c t]

/-- `compAff`, by Horner's rule; additions only when `s = t = 1`. -/
def compAffF (s t : ℤ) (l : List ℤ) : List ℤ :=
  if s=1 ∧ t=1 then
    List.rec (motive := fun _ => List ℤ) []
      (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
        (fun x z => Int.add b x :: shiftAuxF z x)) l
  else
    List.rec (motive := fun _ => List ℤ) []
      (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
        (fun x z => Int.add b (Int.mul x s) :: affAuxF s t z x)) l

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
        (fun x z => Int.add b x :: shiftAuxF z x) =
          Certificate.add [b] (Certificate.affMul 1 1 (Certificate.compAff 1 1 l))
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
          (fun x z => Int.add b (Int.mul x s) :: affAuxF s t z x)) l) [b]
        (fun x z => Int.add b (Int.mul x s) :: affAuxF s t z x) =
          Certificate.add [b] (Certificate.affMul s t (Certificate.compAff s t l))
      rw [ih]
      rcases hc : Certificate.compAff s t l with _ | ⟨x,z⟩
      · show [b] = Certificate.add [b] (Certificate.affMul s t [])
        rw [Certificate.affMul,ite_eq_right h]; rfl
      · show Int.add b (Int.mul x s) :: affAuxF s t z x =
          Certificate.add [b] (Certificate.affMul s t (x :: z))
        rw [Certificate.affMul,ite_eq_right h,affAuxF_eq]
        show (b+x*s) :: Certificate.affMulAux s t x z =
          (b+s*x) :: Certificate.add [] (Certificate.affMulAux s t x z)
        rw [Int.mul_comm x s]; rfl

/-- `centerList`. -/
def centerF (num den : ℕ) (s t : ℤ) (l : List ℤ) : List ℤ :=
  compAffF s t (prescaleF num den (l.length-1) l 0)

theorem centerF_eq (num den : ℕ) (s t : ℤ) (l : List ℤ) :
    centerF num den s t l = Certificate.centerList num den s t l := by
  rw [centerF,compAffF_eq,prescaleF_eq]; rfl

/-- `twoX`. -/
def twoXF (u : List ℤ) : List ℤ :=
  List.casesOn (motive := fun _ => List ℤ) u [] (fun u0 t => addF t (0 :: Int.mul u0 2 :: t))

theorem twoXF_eq : ∀ u : List ℤ, twoXF u = Certificate.twoX u
  | [] => rfl
  | u0 :: t => by
    show addF t (0 :: (u0*2) :: t) = Certificate.add t (0 :: (2*u0) :: t)
    rw [addF_eq,Int.mul_comm]

/-- `chebList` and `2 ^ length`. -/
def chebPair (l : List ℤ) : List ℤ × ℕ :=
  List.rec (motive := fun _ => List ℤ × ℕ) ([],1)
    (fun a _ ih => (addF [Int.mul a (Int.ofNat ih.2)] (twoXF ih.1),Nat.mul 2 ih.2)) l

theorem chebPair_eq : ∀ l : List ℤ, chebPair l = (Certificate.chebList l,2^l.length)
  | [] => rfl
  | a :: l => by
    show (addF [Int.mul a (Int.ofNat (chebPair l).2)] (twoXF (chebPair l).1),
      Nat.mul 2 (chebPair l).2) = _
    rw [chebPair_eq l,addF_eq,twoXF_eq,Certificate.chebList,List.length_cons,pow_succ,
      Nat.mul_comm]
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

/-! ### Dividing by the common factor -/

/-- The gcd of `g` and the entries of `l`. -/
def gcdF (l : List ℤ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun g => g) (fun x _ ih g => ih (Nat.gcd x.natAbs g)) l

theorem gcdF_dvd : ∀ (l : List ℤ) (g : ℕ), gcdF l g∣g ∧ ∀ x∈l,((gcdF l g:ℕ):ℤ)∣x
  | [],_ => ⟨dvd_rfl,fun _ hx => by simp at hx⟩
  | y :: l,g => by
    obtain ⟨h1,h2⟩ := gcdF_dvd l (Nat.gcd y.natAbs g)
    show gcdF l (Nat.gcd y.natAbs g)∣g ∧
      ∀ x∈y :: l,((gcdF l (Nat.gcd y.natAbs g):ℕ):ℤ)∣x
    refine ⟨h1.trans (Nat.gcd_dvd_right _ _),fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Int.natCast_dvd.2 (h1.trans (Nat.gcd_dvd_left _ _))
    · exact h2 x hx

/-- The entries of `l` divided by `d`. -/
def divF (d : ℤ) (l : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun x _ ih => Int.ediv x d :: ih) l

theorem toPoly_divF (d : ℤ) :
    ∀ l : List ℤ,(∀ x∈l,d∣x) → C (d:ℚ)*toPoly (divF d l)=toPoly l
  | [],_ => by
    show C (d:ℚ)*toPoly []=toPoly []
    simp [toPoly]
  | x :: l,h => by
    have ih := toPoly_divF d l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx : (d:ℚ)*((x/d:ℤ):ℚ)=(x:ℚ) := by
      exact_mod_cast Int.mul_ediv_cancel' (h x List.mem_cons_self)
    show C (d:ℚ)*toPoly (x/d :: divF d l)=toPoly (x :: l)
    simp only [toPoly]
    rw [← ih,← hx,map_mul]
    ring

theorem toPoly_divF_zero : ∀ l : List ℤ,toPoly (divF 0 l)=0
  | [] => by
    show toPoly []=0
    simp [toPoly]
  | x :: l => by
    show toPoly (x/0 :: divF 0 l)=0
    rw [Int.ediv_zero,toPoly,toPoly_divF_zero l]
    simp

/-- `l` without its trailing zeros. -/
def trimF (l : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) []
    (fun x _ ih => List.casesOn (motive := fun _ => List ℤ) ih (if x=0 then [] else [x])
      (fun y t => x :: y :: t)) l

theorem toPoly_trimF : ∀ l : List ℤ,toPoly (trimF l)=toPoly l
  | [] => rfl
  | x :: l => by
    have ih := toPoly_trimF l
    show toPoly (List.casesOn (motive := fun _ => List ℤ) (trimF l) (if x=0 then [] else [x])
      (fun y t => x :: y :: t))=toPoly (x :: l)
    generalize trimF l=r at ih ⊢
    cases r with
    | nil =>
      show toPoly (if x=0 then [] else [x])=C (x:ℚ)+X*toPoly l
      rw [← ih]
      split_ifs with hx
      · simp [toPoly,hx]
      · simp [toPoly]
    | cons y t =>
      show C (x:ℚ)+X*toPoly (y :: t)=C (x:ℚ)+X*toPoly l
      rw [ih]

end Fast

/-! ### Scaled lists -/

/-- `Scaled.add`, in one pass. -/
def Scaled.addF (a b : Scaled) : Scaled := ⟨Fast.lincF b.s a.s a.l b.l,a.s*b.s⟩
/-- `Scaled.sub`, in one pass. -/
def Scaled.subF (a b : Scaled) : Scaled := ⟨Fast.lincF b.s (-(a.s:ℤ)) a.l b.l,a.s*b.s⟩
/-- `Scaled.neg`. -/
def Scaled.negF (a : Scaled) : Scaled := ⟨Fast.smulF (-1) a.l,a.s⟩
/-- `Scaled.mul`, with the entries of the factor of smaller scale (the shorter integers) as the
right factors of the products. -/
def Scaled.mulF (a b : Scaled) : Scaled :=
  ⟨if b.s≤a.s then Fast.mulF a.l b.l else Fast.mulF b.l a.l,a.s*b.s⟩
/-- `Scaled.pow`. -/
def Scaled.powF (a : Scaled) (n : ℕ) : Scaled := ⟨Fast.powF a.l n,a.s^n⟩
/-- `Scaled.center`. -/
def Scaled.centerF (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨Fast.centerF num den s t c.l,c.s*den^(c.l.length-1)⟩
/-- The list and the scale divided by their gcd, without trailing zeros. -/
def Scaled.normF (a : Scaled) : Scaled :=
  ⟨Fast.trimF (Fast.divF ((Fast.gcdF a.l a.s:ℕ):ℤ) a.l),a.s/Fast.gcdF a.l a.s⟩

theorem Scaled.addF_eq (a b : Scaled) : a.addF b=a.add b := by
  simp only [Scaled.addF,Scaled.add,Fast.lincF_eq]

theorem Scaled.subF_eq (a b : Scaled) : a.subF b=a.sub b := by
  simp only [Scaled.subF,Scaled.sub,Fast.lincF_eq]

theorem Scaled.negF_eq (a : Scaled) : a.negF=a.neg := by
  simp only [Scaled.negF,Scaled.neg,Fast.smulF_eq]

theorem Scaled.powF_eq (a : Scaled) (n : ℕ) : a.powF n=a.pow n := by
  simp only [Scaled.powF,Scaled.pow,Fast.powF_eq]

theorem Scaled.centerF_eq (c : Scaled) (num den : ℕ) (s t : ℤ) :
    c.centerF num den s t=c.center num den s t := by
  simp only [Scaled.centerF,Scaled.center,Fast.centerF_eq]

theorem Scaled.Rep.addF {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.addF b).Rep (p+q) := by
  rw [Scaled.addF_eq]; exact ha.add hb

theorem Scaled.Rep.subF {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.subF b).Rep (p-q) := by
  rw [Scaled.subF_eq]; exact ha.sub hb

theorem Scaled.Rep.negF {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.negF.Rep (-p) := by
  rw [Scaled.negF_eq]; exact ha.neg

theorem Scaled.Rep.mulF {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) :
    (a.mulF b).Rep (p*q) := by
  unfold Scaled.Rep at *
  unfold Scaled.mulF
  split_ifs <;> simp only [Fast.mulF_eq,toPoly_mul,ha,hb,Nat.cast_mul,map_mul] <;> ring

theorem Scaled.Rep.powF {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (n : ℕ) :
    (a.powF n).Rep (p^n) := by
  rw [Scaled.powF_eq]; exact ha.pow n

theorem Scaled.Rep.centeredF {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (num den : ℕ) (s t : ℤ)
    {a b : ℚ} (hden : den≠0) (hm : (a+b)/2=num*s/den) (hh : (b-a)/2=num*t/den) :
    (c.centerF num den s t).Rep (WholeIntervalPolynomial.centered a b p) := by
  rw [Scaled.centerF_eq]; exact hc.centered num den s t hden hm hh

theorem Scaled.Rep.normF {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) : a.normF.Rep p := by
  unfold Scaled.Rep at *
  obtain ⟨h2,h3⟩ := Fast.gcdF_dvd a.l a.s
  have h1 := Fast.toPoly_divF _ a.l h3
  show toPoly (Fast.trimF (Fast.divF ((Fast.gcdF a.l a.s:ℕ):ℤ) a.l))=
    C ((a.s/Fast.gcdF a.l a.s:ℕ):ℚ)*p
  rw [Fast.toPoly_trimF]
  generalize Fast.gcdF a.l a.s=g at h1 h2 h3 ⊢
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp only [Nat.cast_zero,Nat.div_zero,map_zero,zero_mul]
    exact Fast.toPoly_divF_zero a.l
  · have hgq : (g:ℚ)≠0 := by exact_mod_cast hg.ne'
    have hdiv : ((a.s/g:ℕ):ℚ)=(a.s:ℚ)/g := Nat.cast_div h2 hgq
    apply mul_left_cancel₀ (show (C (g:ℚ):ℚ[X])≠0 from C_ne_zero.2 hgq)
    push_cast at h1
    rw [h1,ha,hdiv,← mul_assoc,← C_mul,mul_div_cancel₀ _ hgq]

/-! ### Reserves as integer comparisons -/

/-- The integer form of a lower reserve `n/d < lowerOn`. -/
theorem lt_lowerOn_of_int {c : Scaled} {a b r : ℚ} {q : ℚ[X]} {D n d : ℕ}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b q)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (hl' : (Fast.chebF c.l).length≤D+1) (hr : r=(n:ℚ)/d) (hd : 0<d)
    (h : (n:ℤ)*((c.s:ℤ)*2^c.l.length)<2*(d:ℤ)*Fast.lowL (Fast.chebF c.l)) :
    r<lowerOn D a b q := by
  rw [lowerOn_eq_of_rep hc hs hl,← Fast.chebF_eq,Fast.lowL_eq hl',hr,
    div_lt_div_iff₀ (by exact_mod_cast hd) (scale_pos hs)]
  have h' := (Int.cast_lt (R := ℚ)).mpr h
  push_cast at h'
  linarith

/-- The integer form of an upper reserve `upperOn < n/d`. -/
theorem upperOn_lt_of_int {c : Scaled} {a b r : ℚ} {q : ℚ[X]} {D n d : ℕ}
    (hc : c.Rep (WholeIntervalPolynomial.centered a b q)) (hs : c.s≠0) (hl : c.l.length≤D+1)
    (hl' : (Fast.chebF c.l).length≤D+1) (hr : r=(n:ℚ)/d) (hd : 0<d)
    (h : 2*(d:ℤ)*Fast.upL (Fast.chebF c.l)<(n:ℤ)*((c.s:ℤ)*2^c.l.length)) :
    upperOn D a b q<r := by
  rw [upperOn_eq_of_rep hc hs hl,← Fast.chebF_eq,Fast.upL_eq hl',hr,
    div_lt_div_iff₀ (scale_pos hs) (by exact_mod_cast hd)]
  have h' := (Int.cast_lt (R := ℚ)).mpr h
  push_cast at h'
  linarith

end SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate
