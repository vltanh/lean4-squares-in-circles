module

public import Mathlib.Algebra.Order.Floor.Semifield
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3PolynomialData

/-!
# Eight squares: whole-interval positivity of all EH1/BT3 endpoint numerators

Each exact finite transform
covers its full native interval. The two small-high H/G alternatives
retain their constant and first quotient. Every other numerator uses
its stated coefficient-norm reserve directly, with no angular mesh.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Certificate
open WholeIntervalPolynomial
open WholeIntervalPolynomial.Certificate (Scaled lowerOn_eq_of_rep lowerZ chebList toPoly)
open PositiveTD.Certificate (S9 S11 C10 C12)

/-! #### Kernel list arithmetic

The list operations of `PolynomialCertificates`, written with the recursors and the integer
operations themselves: the kernel reduces them in fewer steps. Each equals its model. -/

private def addF (l : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun m => m)
    (fun x t ih m => List.casesOn (motive := fun _ => List ℤ) m (x :: t)
      (fun y m' => Int.add x y :: ih m')) l

private theorem addF_eq : ∀ l m : List ℤ,addF l m=WholeIntervalPolynomial.Certificate.add l m
  | [],_ => rfl
  | _ :: _,[] => rfl
  | x :: t,y :: m => by
    show Int.add x y :: addF t m=(x+y) :: WholeIntervalPolynomial.Certificate.add t m
    rw [addF_eq t m]; rfl

private def smulF (c : ℤ) (l : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun x _ ih => Int.mul c x :: ih) l

private theorem smulF_eq (c : ℤ) : ∀ l : List ℤ,smulF c l=WholeIntervalPolynomial.Certificate.smul c l
  | [] => rfl
  | x :: l => by
    show Int.mul c x :: smulF c l=(c*x) :: WholeIntervalPolynomial.Certificate.smul c l
    rw [smulF_eq c l]; rfl

/-- `p • l + q • m`, in one pass. -/
private def lincF (p q : ℤ) (l : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun m => smulF q m)
    (fun x t ih m => List.casesOn (motive := fun _ => List ℤ) m (smulF p (x :: t))
      (fun y m' => Int.add (Int.mul p x) (Int.mul q y) :: ih m')) l

private theorem lincF_eq (p q : ℤ) : ∀ l m : List ℤ,lincF p q l m=
    WholeIntervalPolynomial.Certificate.add (WholeIntervalPolynomial.Certificate.smul p l)
      (WholeIntervalPolynomial.Certificate.smul q m)
  | [],m => by
    show smulF q m=_
    rw [smulF_eq]; rfl
  | x :: t,[] => by
    show smulF p (x :: t)=_
    rw [smulF_eq]; rfl
  | x :: t,y :: m => by
    show Int.add (Int.mul p x) (Int.mul q y) :: lincF p q t m=(p*x+q*y) ::
      WholeIntervalPolynomial.Certificate.add (WholeIntervalPolynomial.Certificate.smul p t)
        (WholeIntervalPolynomial.Certificate.smul q m)
    rw [lincF_eq p q t m]; rfl

/-- `a • m + acc`, in one pass. -/
private def axpyF (a : ℤ) (m : List ℤ) : List ℤ → List ℤ :=
  List.rec (motive := fun _ => List ℤ → List ℤ) (fun acc => acc)
    (fun x _ ih acc => List.casesOn (motive := fun _ => List ℤ) acc (Int.mul a x :: ih [])
      (fun y acc' => Int.add (Int.mul a x) y :: ih acc')) m

private theorem addC_nil_right : ∀ l : List ℤ,WholeIntervalPolynomial.Certificate.add l []=l
  | [] => rfl
  | _ :: _ => rfl

private theorem axpyF_eq (a : ℤ) : ∀ m acc : List ℤ,axpyF a m acc=
    WholeIntervalPolynomial.Certificate.add (WholeIntervalPolynomial.Certificate.smul a m) acc
  | [],_ => rfl
  | x :: m,[] => by
    show Int.mul a x :: axpyF a m []=(a*x) :: WholeIntervalPolynomial.Certificate.smul a m
    rw [axpyF_eq a m [],addC_nil_right]; rfl
  | x :: m,y :: acc => by
    show Int.add (Int.mul a x) y :: axpyF a m acc=(a*x+y) ::
      WholeIntervalPolynomial.Certificate.add (WholeIntervalPolynomial.Certificate.smul a m) acc
    rw [axpyF_eq a m acc]; rfl

/-- `l * m`, row by row. -/
private def mulF (l m : List ℤ) : List ℤ :=
  List.casesOn (motive := fun _ => List ℤ) m []
    (fun _ _ => List.rec (motive := fun _ => List ℤ) [] (fun a _ ih => axpyF a m (0 :: ih)) l)

private theorem mulF_eq : ∀ l m : List ℤ,mulF l m=WholeIntervalPolynomial.Certificate.mul l m
  | _,[] => by cases ‹List ℤ› <;> rfl
  | [],_ :: _ => rfl
  | a :: l,b :: m => by
    show axpyF a (b :: m) (0 :: mulF l (b :: m))=_
    rw [axpyF_eq,mulF_eq l (b :: m)]; rfl

private def prescaleF (num den n : ℕ) (l : List ℤ) : ℕ → List ℤ :=
  List.rec (motive := fun _ => ℕ → List ℤ) (fun _ => [])
    (fun a _ ih i => Int.mul a (Int.ofNat (Nat.mul (Nat.pow num i) (Nat.pow den (Nat.sub n i))))
      :: ih (Nat.succ i)) l

private theorem prescaleF_eq (num den n : ℕ) : ∀ (l : List ℤ) (i : ℕ),
    prescaleF num den n l i=WholeIntervalPolynomial.Certificate.prescale num den n i l
  | [],_ => rfl
  | a :: l,i => by
    show _ :: prescaleF num den n l (i+1)=_
    rw [prescaleF_eq num den n l (i+1)]; rfl

private def shiftAuxF (z : List ℤ) : ℤ → List ℤ :=
  List.rec (motive := fun _ => ℤ → List ℤ) (fun c => [c]) (fun x _ ih c => Int.add x c :: ih x) z

private theorem shiftAuxF_eq : ∀ (z : List ℤ) (c : ℤ),
    shiftAuxF z c=WholeIntervalPolynomial.Certificate.add z (c :: z)
  | [],_ => rfl
  | x :: z,c => by
    show Int.add x c :: shiftAuxF z x=(x+c) :: WholeIntervalPolynomial.Certificate.add z (x :: z)
    rw [shiftAuxF_eq z x]; rfl

private def affAuxF (s t : ℤ) (z : List ℤ) : ℤ → List ℤ :=
  List.rec (motive := fun _ => ℤ → List ℤ) (fun c => [Int.mul t c])
    (fun x _ ih c => Int.add (Int.mul s x) (Int.mul t c) :: ih x) z

private theorem affAuxF_eq (s t : ℤ) : ∀ (z : List ℤ) (c : ℤ),
    affAuxF s t z c=WholeIntervalPolynomial.Certificate.affMulAux s t c z
  | [],_ => rfl
  | x :: z,c => by
    show Int.add (Int.mul s x) (Int.mul t c) :: affAuxF s t z x=_
    rw [affAuxF_eq s t z x]; rfl

private def compAffF (s t : ℤ) (l : List ℤ) : List ℤ :=
  if s=1 ∧ t=1 then
    List.rec (motive := fun _ => List ℤ) []
      (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
        (fun x z => Int.add b x :: shiftAuxF z x)) l
  else
    List.rec (motive := fun _ => List ℤ) []
      (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
        (fun x z => Int.add b (Int.mul s x) :: affAuxF s t z x)) l

private theorem compAffF_eq (s t : ℤ) (l : List ℤ) :
    compAffF s t l=WholeIntervalPolynomial.Certificate.compAff s t l := by
  unfold compAffF
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    induction l with
    | nil => rfl
    | cons b l ih =>
      show List.casesOn (motive := fun _ => List ℤ) (List.rec (motive := fun _ => List ℤ) []
        (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
          (fun x z => Int.add b x :: shiftAuxF z x)) l) [b]
        (fun x z => Int.add b x :: shiftAuxF z x)=WholeIntervalPolynomial.Certificate.add [b]
          (WholeIntervalPolynomial.Certificate.affMul 1 1
            (WholeIntervalPolynomial.Certificate.compAff 1 1 l))
      rw [ih]
      rcases hc : WholeIntervalPolynomial.Certificate.compAff 1 1 l with _ | ⟨x,z⟩
      · rfl
      · show Int.add b x :: shiftAuxF z x=WholeIntervalPolynomial.Certificate.add [b]
          (WholeIntervalPolynomial.Certificate.affMul 1 1 (x :: z))
        rw [WholeIntervalPolynomial.Certificate.affMul,ite_eq_left ⟨rfl,rfl⟩,
          WholeIntervalPolynomial.Certificate.shiftMul,shiftAuxF_eq]
        show Int.add b x :: _=(b+(x+0)) :: WholeIntervalPolynomial.Certificate.add []
          (WholeIntervalPolynomial.Certificate.add z (x :: z))
        rw [Int.add_zero]; rfl
  · induction l with
    | nil => rfl
    | cons b l ih =>
      show List.casesOn (motive := fun _ => List ℤ) (List.rec (motive := fun _ => List ℤ) []
        (fun b _ ih => List.casesOn (motive := fun _ => List ℤ) ih [b]
          (fun x z => Int.add b (Int.mul s x) :: affAuxF s t z x)) l) [b]
        (fun x z => Int.add b (Int.mul s x) :: affAuxF s t z x)=
          WholeIntervalPolynomial.Certificate.add [b] (WholeIntervalPolynomial.Certificate.affMul s t
            (WholeIntervalPolynomial.Certificate.compAff s t l))
      rw [ih]
      rcases hc : WholeIntervalPolynomial.Certificate.compAff s t l with _ | ⟨x,z⟩
      · show [b]=WholeIntervalPolynomial.Certificate.add [b]
          (WholeIntervalPolynomial.Certificate.affMul s t [])
        rw [WholeIntervalPolynomial.Certificate.affMul,ite_eq_right h]; rfl
      · show Int.add b (Int.mul s x) :: affAuxF s t z x=WholeIntervalPolynomial.Certificate.add [b]
          (WholeIntervalPolynomial.Certificate.affMul s t (x :: z))
        rw [WholeIntervalPolynomial.Certificate.affMul,ite_eq_right h,affAuxF_eq]; rfl

/-- `Scaled.center`, with the fast list operations. -/
private def centerS (c : Scaled) (num den : ℕ) (s t : ℤ) : Scaled :=
  ⟨compAffF s t (prescaleF num den (c.l.length-1) c.l 0),c.s*den^(c.l.length-1)⟩

private theorem centerS_eq (c : Scaled) (num den : ℕ) (s t : ℤ) :
    centerS c num den s t=c.center num den s t := by
  rw [centerS,compAffF_eq,prescaleF_eq]; rfl

private def twoXF (u : List ℤ) : List ℤ :=
  List.casesOn (motive := fun _ => List ℤ) u [] (fun u0 t => addF t (0 :: Int.mul 2 u0 :: t))

private theorem twoXF_eq : ∀ u : List ℤ,twoXF u=WholeIntervalPolynomial.Certificate.twoX u
  | [] => rfl
  | u0 :: t => by
    show addF t (0 :: Int.mul 2 u0 :: t)=WholeIntervalPolynomial.Certificate.add t (0 :: (2*u0) :: t)
    rw [addF_eq]; rfl

private def chebPair (l : List ℤ) : List ℤ × ℕ :=
  List.rec (motive := fun _ => List ℤ × ℕ) ([],1)
    (fun a _ ih => (addF [Int.mul a (Int.ofNat ih.2)] (twoXF ih.1),Nat.mul 2 ih.2)) l

private theorem chebPair_eq : ∀ l : List ℤ,
    chebPair l=(WholeIntervalPolynomial.Certificate.chebList l,2^l.length)
  | [] => rfl
  | a :: l => by
    show (addF [Int.mul a (Int.ofNat (chebPair l).2)] (twoXF (chebPair l).1),
      Nat.mul 2 (chebPair l).2)=_
    rw [chebPair_eq l,addF_eq,twoXF_eq,WholeIntervalPolynomial.Certificate.chebList,
      List.length_cons,pow_succ,Nat.mul_comm]
    rfl

private def chebF (l : List ℤ) : List ℤ := (chebPair l).1

private theorem chebF_eq (l : List ℤ) : chebF l=WholeIntervalPolynomial.Certificate.chebList l := by
  rw [chebF,chebPair_eq]

private def sumAbsF (l : List ℤ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add (Int.natAbs x) ih) l

private theorem sumAbsF_eq_sum {t : List ℤ} {D : ℕ} (h : t.length≤D) :
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
private def lowL (l : List ℤ) : ℤ :=
  List.casesOn (motive := fun _ => ℤ) l 0 (fun b t => Int.sub b (Int.ofNat (sumAbsF t)))

private theorem lowL_eq {l : List ℤ} {D : ℕ} (h : l.length≤D+1) :
    WholeIntervalPolynomial.Certificate.lowerZ D (fun j => l.getD j 0)=lowL l := by
  cases l with
  | nil => simp [WholeIntervalPolynomial.Certificate.lowerZ,lowL]
  | cons b t =>
    simp only [WholeIntervalPolynomial.Certificate.lowerZ,List.getD_cons_zero,List.getD_cons_succ]
    rw [← sumAbsF_eq_sum (by simp at h; omega)]
    rfl

private def powF (l : List ℤ) (n : ℕ) : List ℤ :=
  Nat.rec (motive := fun _ => List ℤ) [1] (fun _ ih => mulF ih l) n

private theorem powF_eq (l : List ℤ) : ∀ n : ℕ,powF l n=WholeIntervalPolynomial.Certificate.pow l n
  | 0 => rfl
  | n+1 => by
    show mulF (powF l n) l=WholeIntervalPolynomial.Certificate.mul (WholeIntervalPolynomial.Certificate.pow l n) l
    rw [powF_eq l n,mulF_eq]

/-- `Scaled.add`, `Scaled.sub`, `Scaled.mul` and `Scaled.pow` with the fast list operations. -/
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.fadd
    (a b : Scaled) : Scaled := ⟨lincF b.s a.s a.l b.l,a.s*b.s⟩
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.fsub
    (a b : Scaled) : Scaled := ⟨lincF b.s (-(a.s:ℤ)) a.l b.l,a.s*b.s⟩
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.fmul
    (a b : Scaled) : Scaled := ⟨mulF a.l b.l,a.s*b.s⟩
private def _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.fpow
    (a : Scaled) (n : ℕ) : Scaled := ⟨powF a.l n,a.s^n⟩
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.fadd
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.fadd b).Rep (p+q) := by
  have e : a.fadd b=a.add b := by
    show (⟨lincF b.s a.s a.l b.l,a.s*b.s⟩ : Scaled)=a.add b
    rw [lincF_eq]; rfl
  rw [e]; exact ha.add hb
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.fsub
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.fsub b).Rep (p-q) := by
  have e : a.fsub b=a.sub b := by
    show (⟨lincF b.s (-(a.s:ℤ)) a.l b.l,a.s*b.s⟩ : Scaled)=a.sub b
    rw [lincF_eq]; rfl
  rw [e]; exact ha.sub hb
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.fmul
    {a b : Scaled} {p q : ℚ[X]} (ha : a.Rep p) (hb : b.Rep q) : (a.fmul b).Rep (p*q) := by
  have e : a.fmul b=a.mul b := by
    show (⟨mulF a.l b.l,a.s*b.s⟩ : Scaled)=a.mul b
    rw [mulF_eq]; rfl
  rw [e]; exact ha.mul hb
private theorem _root_.SquaresInCircles.Eight.WholeIntervalPolynomial.Certificate.Scaled.Rep.fpow
    {a : Scaled} {p : ℚ[X]} (ha : a.Rep p) (n : ℕ) : (a.fpow n).Rep (p^n) := by
  have e : a.fpow n=a.pow n := by
    show (⟨powF a.l n,a.s^n⟩ : Scaled)=a.pow n
    rw [powF_eq]; rfl
  rw [e]; exact ha.pow n

/-! ### Scaled-list helpers: gcd normalization, truncation, fractions -/

private def r76gcd (g : ℕ) (l : List ℤ) : ℕ := l.foldl (fun g x => Nat.gcd g x.natAbs) g

private theorem r76gcd_dvd : ∀ (l : List ℤ) (g : ℕ),
    r76gcd g l ∣ g ∧ ∀ x ∈ l,((r76gcd g l:ℕ):ℤ) ∣ x
  | [],g => by simp [r76gcd]
  | a :: t,g => by
    have ih := r76gcd_dvd t (Nat.gcd g a.natAbs)
    have he : r76gcd g (a :: t)=r76gcd (Nat.gcd g a.natAbs) t := rfl
    rw [he]
    refine ⟨ih.1.trans (Nat.gcd_dvd_left _ _),?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl|hx
    · exact Int.natCast_dvd.2 (ih.1.trans (Nat.gcd_dvd_right _ _))
    · exact ih.2 x hx

private theorem r76toPoly_map_div (g : ℤ) : ∀ l : List ℤ,(∀ x ∈ l,g ∣ x) →
    C (g:ℚ)*toPoly (l.map (fun x => x/g))=toPoly l
  | [],_ => by simp [toPoly]
  | a :: t,h => by
    have ih := r76toPoly_map_div g t (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha : ((a/g:ℤ):ℚ)*(g:ℚ)=(a:ℚ) := by
      exact_mod_cast Int.ediv_mul_cancel (h a (List.mem_cons_self))
    simp only [List.map_cons,toPoly]
    rw [mul_add,← ih,← map_mul,mul_comm (g:ℚ),ha]
    ring

/-- Division by the common gcd of the scale and the entries. -/
private def r76normS (c : Scaled) : Scaled :=
  if r76gcd c.s c.l=0 then c else
    ⟨c.l.map (fun x => x/((r76gcd c.s c.l:ℕ):ℤ)),c.s/r76gcd c.s c.l⟩

private theorem r76normS_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r76normS c).Rep p := by
  unfold r76normS
  split_ifs with hg
  · exact hc
  obtain ⟨hs,hl⟩ := r76gcd_dvd c.l c.s
  unfold Scaled.Rep at *
  have h1 := r76toPoly_map_div _ c.l hl
  have hgq : ((r76gcd c.s c.l:ℕ):ℚ)≠0 := by exact_mod_cast hg
  have hs' : ((c.s/r76gcd c.s c.l:ℕ):ℚ)*(r76gcd c.s c.l:ℕ)=c.s := by
    exact_mod_cast Nat.div_mul_cancel hs
  apply mul_left_cancel₀ (show C ((r76gcd c.s c.l:ℕ):ℚ)≠0 from C_ne_zero.2 hgq)
  push_cast at h1 ⊢
  rw [h1,hc,← mul_assoc,← map_mul,mul_comm _ ((c.s/r76gcd c.s c.l:ℕ):ℚ)]
  rw [hs']

private def r76gcdF (l : List ℤ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun g => g) (fun x _ ih g => ih (Nat.gcd g x.natAbs)) l
private theorem r76gcdF_eq : ∀ (l : List ℤ) (g : ℕ),r76gcdF l g=r76gcd g l
  | [],_ => rfl
  | x :: l,g => r76gcdF_eq l (Nat.gcd g x.natAbs)
private def divF (d : ℤ) (l : List ℤ) : List ℤ :=
  List.rec (motive := fun _ => List ℤ) [] (fun x _ ih => x/d :: ih) l
private theorem divF_eq (d : ℤ) : ∀ l : List ℤ,divF d l=l.map (fun x => x/d)
  | [] => rfl
  | x :: l => by
    show x/d :: divF d l=_
    rw [divF_eq d l]; rfl
/-- `r76normS`, with the fast list operations. -/
private def r76norm (c : Scaled) : Scaled :=
  if r76gcdF c.l c.s=0 then c else ⟨divF ((r76gcdF c.l c.s:ℕ):ℤ) c.l,c.s/r76gcdF c.l c.s⟩
private theorem r76norm_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) : (r76norm c).Rep p := by
  have e : r76norm c=r76normS c := by simp only [r76norm,r76normS,r76gcdF_eq,divF_eq]
  rw [e]; exact r76normS_rep hc

/-- The first four entries. -/
private def r76trunc (c : Scaled) : Scaled := ⟨c.l.take 4,c.s⟩

private theorem r76trunc_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) :
    (r76trunc c).Rep (truncate3 p) := by
  unfold Scaled.Rep at *
  ext n
  have hco := congrArg (fun q => q.coeff n) hc
  simp only [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul] at hco
  rw [WholeIntervalPolynomial.Certificate.coeff_toPoly,coeff_C_mul]
  simp only [r76trunc,truncate3,Fin.sum_univ_four,
    Fin.val_zero,Fin.val_one,Fin.val_two,coeff_add,coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 4 with hn|hn
  · interval_cases n <;> simpa [List.getD_eq_getElem?_getD] using hco
  · have ht : (c.l.take 4).getD n 0=0 := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [ht]
    simp [show n≠0 by omega,show n≠1 by omega,show n≠2 by omega,show n≠3 by omega]

private theorem r76frac_rep (a : ℤ) (b : ℕ) (hb : b≠0) :
    (⟨[a],b⟩ : Scaled).Rep (C ((a:ℚ)/b)) := by
  unfold Scaled.Rep
  simp only [toPoly,mul_zero,add_zero,← map_mul]
  congr 1
  field_simp

/-- The rounded square root, reduced to one integer square root. -/
private theorem r76root12 {a : ℤ} {b n : ℕ} (hb : b≠0) (ha : 0≤a)
    (hn : n*n≤a.toNat*1000000000000000000000000/b ∧ a.toNat*1000000000000000000000000/b<(n+1)*(n+1)) :
    root12 ((a:ℚ)/b)=((if 4*a*1000000000000000000000000<(2*(n:ℤ)+1)^2*b then n else n+1 : ℕ):ℚ)/
      1000000000000 := by
  have hb' : (0:ℚ)<b := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hq0 : 0≤(a:ℚ)/b := div_nonneg (by exact_mod_cast ha) hb'.le
  have hfl : ((a:ℚ)/b).num.natAbs*1000000000000000000000000/((a:ℚ)/b).den=
      a.toNat*1000000000000000000000000/b := by
    have e1 : ((((a:ℚ)/b).num.natAbs:ℕ):ℚ)=(((a:ℚ)/b).num:ℚ) := by
      rw [Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.2 hq0)]
    have e2 : ((a.toNat:ℕ):ℚ)=(a:ℚ) := by exact_mod_cast Int.toNat_of_nonneg ha
    have hx : ((((a:ℚ)/b).num.natAbs*1000000000000000000000000:ℕ):ℚ)/(((a:ℚ)/b).den:ℕ)=
        ((a.toNat*1000000000000000000000000:ℕ):ℚ)/(b:ℕ) := by
      rw [Nat.cast_mul,Nat.cast_mul,e1,e2,mul_div_right_comm,Rat.num_div_den]
      ring
    rw [← Nat.floor_div_eq_div (K:=ℚ),← Nat.floor_div_eq_div (K:=ℚ),hx]
  have key : ((a:ℚ)/b*1000000000000000000000000<((n:ℚ)+1/2)^2)↔
      (4*a*1000000000000000000000000<(2*(n:ℤ)+1)^2*b) := by
    rw [← @Int.cast_lt ℚ]
    push_cast
    rw [div_mul_eq_mul_div,div_lt_iff₀ hb']
    constructor <;> intro h <;>
      linarith [show ((2*(n:ℚ)+1)^2*b)=4*(((n:ℚ)+1/2)^2*b) by ring]
  unfold root12
  simp only [hfl,(Nat.eq_sqrt.2 hn).symm]
  congr 2
  exact if_congr key rfl rfl

/-! ### Taylor polynomials composed with a represented polynomial -/

private def r76S9of (v : Scaled) : Scaled := r76norm
  ((((v.fsub ((Scaled.const (1/6)).fmul (v.fpow 3))).fadd
    ((Scaled.const (1/120)).fmul (v.fpow 5))).fsub
    ((Scaled.const (1/5040)).fmul (v.fpow 7))).fadd
    ((Scaled.const (1/362880)).fmul (v.fpow 9)))

private theorem r76S9of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76S9of v).Rep (S9.comp q) := by
  have e : S9.comp q=q-C (1/6)*q^3+C (1/120)*q^5-C (1/5040)*q^7+C (1/362880)*q^9 := by
    simp only [S9,PositiveTD.Certificate.S5,sub_comp,add_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact r76norm_rep ((((hv.fsub ((Scaled.rep_const _).fmul (hv.fpow 3))).fadd
    ((Scaled.rep_const _).fmul (hv.fpow 5))).fsub
    ((Scaled.rep_const _).fmul (hv.fpow 7))).fadd
    ((Scaled.rep_const _).fmul (hv.fpow 9)))

private def r76S11of (v : Scaled) : Scaled := r76norm
  ((r76S9of v).fsub ((Scaled.const (1/39916800)).fmul (v.fpow 11)))

private theorem r76S11of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76S11of v).Rep (S11.comp q) := by
  have e : S11.comp q=S9.comp q-C (1/39916800)*q^11 := by
    simp only [S11,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact r76norm_rep ((r76S9of_rep hv).fsub ((Scaled.rep_const _).fmul (hv.fpow 11)))

private def r76C10of (v : Scaled) : Scaled := r76norm
  (((((((Scaled.ofNat 1).fsub ((Scaled.const (1/2)).fmul (v.fpow 2))).fadd
    ((Scaled.const (1/24)).fmul (v.fpow 4))).fsub
    ((Scaled.const (1/720)).fmul (v.fpow 6))).fadd
    ((Scaled.const (1/40320)).fmul (v.fpow 8))).fsub
    ((Scaled.const (1/3628800)).fmul (v.fpow 10))))

private theorem r76C10of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76C10of v).Rep (C10.comp q) := by
  have e : C10.comp q=1-C (1/2)*q^2+C (1/24)*q^4-C (1/720)*q^6+C (1/40320)*q^8-
      C (1/3628800)*q^10 := by
    simp only [C10,PositiveTD.Certificate.C4,sub_comp,add_comp,mul_comp,C_comp,X_comp,pow_comp,
      one_comp]
  rw [e]
  exact r76norm_rep (((((Scaled.rep_one.fsub ((Scaled.rep_const _).fmul (hv.fpow 2))).fadd
    ((Scaled.rep_const _).fmul (hv.fpow 4))).fsub
    ((Scaled.rep_const _).fmul (hv.fpow 6))).fadd
    ((Scaled.rep_const _).fmul (hv.fpow 8))).fsub
    ((Scaled.rep_const _).fmul (hv.fpow 10)))

private def r76C12of (v : Scaled) : Scaled := r76norm
  ((r76C10of v).fadd ((Scaled.const (1/479001600)).fmul (v.fpow 12)))

private theorem r76C12of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76C12of v).Rep (C12.comp q) := by
  have e : C12.comp q=C10.comp q+C (1/479001600)*q^12 := by
    simp only [C12,add_comp,mul_comp,C_comp,X_comp,pow_comp]
  rw [e]
  exact r76norm_rep ((r76C10of_rep hv).fadd ((Scaled.rep_const _).fmul (hv.fpow 12)))

/-! ### The row data -/

private def r76theta (r : Row) : Scaled := Scaled.var.fadd (Scaled.const (left r))

private theorem r76theta_rep (r : Row) : (r76theta r).Rep (theta r) :=
  Scaled.rep_var.fadd (Scaled.rep_const _)

private def r76kB : Family→Scaled→Scaled
  | .smallLow,v => (Scaled.const (2933/5000)).fadd ((Scaled.const (1239/2500)).fmul v)
  | .smallHigh,v => (((Scaled.const (1673/2500)).fadd
      ((Scaled.const (2609/5000)).fmul (v.fsub (Scaled.const (1/6))))).fsub
      ((Scaled.const (1489/2500)).fmul ((v.fsub (Scaled.const (1/6))).fpow 2))).fadd
      ((Scaled.const (527/1250)).fmul ((v.fsub (Scaled.const (1/6))).fpow 3))
  | .farLow,_ => Scaled.const (121/200)
  | .farHigh,v => (Scaled.const (101/200)).fadd ((Scaled.const (2/5)).fmul v)

private theorem r76kB_rep (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76kB f v).Rep ((kBase f).comp q) := by
  cases f <;> simp only [kBase,r76kB,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  · exact (Scaled.rep_const _).fadd ((Scaled.rep_const _).fmul hv)
  · exact (((Scaled.rep_const _).fadd ((Scaled.rep_const _).fmul (hv.fsub (Scaled.rep_const _)))).fsub
      ((Scaled.rep_const _).fmul ((hv.fsub (Scaled.rep_const _)).fpow 2))).fadd
      ((Scaled.rep_const _).fmul ((hv.fsub (Scaled.rep_const _)).fpow 3))
  · exact Scaled.rep_const _
  · exact (Scaled.rep_const _).fadd ((Scaled.rep_const _).fmul hv)

private def r76lB : Family→Scaled→Scaled
  | .smallLow,_ => Scaled.ofNat 1
  | .smallHigh,v => (((Scaled.ofNat 1).fadd
      ((Scaled.const (7/400)).fmul (v.fsub (Scaled.const (1/6))))).fsub
      ((Scaled.const (2733/2500)).fmul ((v.fsub (Scaled.const (1/6))).fpow 2))).fadd
      ((Scaled.const (639/500)).fmul ((v.fsub (Scaled.const (1/6))).fpow 3))
  | .farLow,v => (Scaled.ofNat 1).fsub ((Scaled.const (9/25)).fmul v)
  | .farHigh,v => (Scaled.const (381/400)).fsub ((Scaled.const (17/100)).fmul v)

private theorem r76lB_rep (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76lB f v).Rep ((lBase f).comp q) := by
  cases f <;> simp only [lBase,r76lB,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp,one_comp]
  · exact Scaled.rep_one
  · exact ((Scaled.rep_one.fadd ((Scaled.rep_const _).fmul (hv.fsub (Scaled.rep_const _)))).fsub
      ((Scaled.rep_const _).fmul ((hv.fsub (Scaled.rep_const _)).fpow 2))).fadd
      ((Scaled.rep_const _).fmul ((hv.fsub (Scaled.rep_const _)).fpow 3))
  · exact Scaled.rep_one.fsub ((Scaled.rep_const _).fmul hv)
  · exact (Scaled.rep_const _).fsub ((Scaled.rep_const _).fmul hv)

private def r76mB : Family→Scaled→Scaled
  | .smallLow,v => (Scaled.const (5821/5000)).fsub ((Scaled.const (4437/5000)).fmul v)
  | .smallHigh,v => (((Scaled.const (10163/10000)).fsub
      ((Scaled.const (209/10000)).fmul (v.fsub (Scaled.const (1/6))))).fsub
      ((Scaled.const (5743/5000)).fmul ((v.fsub (Scaled.const (1/6))).fpow 2))).fadd
      ((Scaled.const (14069/10000)).fmul ((v.fsub (Scaled.const (1/6))).fpow 3))
  | .farLow,v => (Scaled.const (111/100)).fsub ((Scaled.const (77/100)).fmul v)
  | .farHigh,v => (Scaled.const (1929/2000)).fsub ((Scaled.const (47/250)).fmul v)

private theorem r76mB_rep (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76mB f v).Rep ((mBase f).comp q) := by
  cases f <;> simp only [mBase,r76mB,add_comp,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  · exact (Scaled.rep_const _).fsub ((Scaled.rep_const _).fmul hv)
  · exact (((Scaled.rep_const _).fsub ((Scaled.rep_const _).fmul (hv.fsub (Scaled.rep_const _)))).fsub
      ((Scaled.rep_const _).fmul ((hv.fsub (Scaled.rep_const _)).fpow 2))).fadd
      ((Scaled.rep_const _).fmul ((hv.fsub (Scaled.rep_const _)).fpow 3))
  · exact (Scaled.rep_const _).fsub ((Scaled.rep_const _).fmul hv)
  · exact (Scaled.rep_const _).fsub ((Scaled.rep_const _).fmul hv)

private def r76k (r : Row) : Scaled := r76norm (r76kB (family r) (r76theta r))
private def r76l (r : Row) : Scaled := r76norm (r76lB (family r) (r76theta r))
private def r76m (r : Row) : Scaled := r76norm (r76mB (family r) (r76theta r))

private theorem r76k_rep (r : Row) : (r76k r).Rep (k r) :=
  r76norm_rep (r76kB_rep _ (r76theta_rep r))
private theorem r76l_rep (r : Row) : (r76l r).Rep (l r) :=
  r76norm_rep (r76lB_rep _ (r76theta_rep r))
private theorem r76m_rep (r : Row) : (r76m r).Rep (m r) :=
  r76norm_rep (r76mB_rep _ (r76theta_rep r))

private def r76s (r : Row) : Scaled :=
  if equal r then r76theta r else match r with
    | .farHigh _ true => Scaled.const (1/4)
    | _ => Scaled.const (1/10)

private theorem r76s_rep (r : Row) : (r76s r).Rep (s r) := by
  rcases r with _|_|i|i|i|_|⟨i,_|_⟩
  · exact r76theta_rep _
  all_goals first
    | exact r76theta_rep _
    | exact Scaled.rep_const _

private def r76d (r : Row) : Scaled :=
  if positive r then (r76s r).fsub (r76theta r) else (r76theta r).fsub (r76s r)

private theorem r76d_rep (r : Row) : (r76d r).Rep (d r) := by
  unfold r76d d
  split_ifs
  · exact (r76s_rep r).fsub (r76theta_rep r)
  · exact (r76theta_rep r).fsub (r76s_rep r)

private def r76J0of (v : Scaled) : Scaled :=
  ((Scaled.const (1/2)).fmul ((r76C10of v).fsub (Scaled.ofNat 1))).fadd
    ((Scaled.const (1/2-abar)).fmul (r76S9of v))

private theorem r76J0of_rep {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76J0of v).Rep (J0.comp q) := by
  have e : J0.comp q=C (1/2)*(C10.comp q-1)+C (1/2-abar)*S9.comp q := by
    simp only [J0,add_comp,sub_comp,mul_comp,C_comp,one_comp]
  rw [e]
  exact ((Scaled.rep_const _).fmul ((r76C10of_rep hv).fsub Scaled.rep_one)).fadd
    ((Scaled.rep_const _).fmul (r76S9of_rep hv))

private def r76JB : Family→Scaled→Scaled
  | .smallHigh,v => (r76J0of v).fsub ((Scaled.const (43/500)).fmul ((v.fsub (Scaled.const (1/6))).fpow 4))
  | .farHigh,v => (r76J0of v).fsub ((Scaled.const (151/500)).fmul ((v.fsub (Scaled.const (1/6))).fpow 6))
  | .smallLow,v => r76J0of v
  | .farLow,v => r76J0of v

private theorem r76JB_rep (f : Family) {v : Scaled} {q : ℚ[X]} (hv : v.Rep q) :
    (r76JB f v).Rep ((JBase f).comp q) := by
  cases f <;> simp only [JBase,r76JB,sub_comp,mul_comp,C_comp,X_comp,pow_comp]
  · exact r76J0of_rep hv
  · exact (r76J0of_rep hv).fsub ((Scaled.rep_const _).fmul ((hv.fsub (Scaled.rep_const _)).fpow 4))
  · exact r76J0of_rep hv
  · exact (r76J0of_rep hv).fsub ((Scaled.rep_const _).fmul ((hv.fsub (Scaled.rep_const _)).fpow 6))

private def r76J (r : Row) : Scaled := r76norm (r76JB (family r) (r76theta r))

private theorem r76J_rep (r : Row) : (r76J r).Rep (J r) :=
  r76norm_rep (r76JB_rep _ (r76theta_rep r))

private def r76qStar (r : Row) : Scaled :=
  r76norm ((r76l r).fadd ((Scaled.const (3/20)).fmul ((Scaled.const h).fsub (r76theta r))))

private theorem r76qStar_rep (r : Row) : (r76qStar r).Rep (qStar r) :=
  r76norm_rep ((r76l_rep r).fadd ((Scaled.rep_const _).fmul ((Scaled.rep_const _).fsub (r76theta_rep r))))

private def r76cUpper (r : Row) : Split→Scaled
  | .atA => r76m r
  | .atT => r76norm ((r76m r).fmul ((r76C12of (r76theta r)).fadd
      ((Scaled.const eta).fmul (r76S9of (r76theta r)))))

private theorem r76cUpper_rep (r : Row) : ∀ ep,(r76cUpper r ep).Rep (cUpper r ep)
  | .atA => r76m_rep r
  | .atT => r76norm_rep ((r76m_rep r).fmul ((r76C12of_rep (r76theta_rep r)).fadd
      ((Scaled.rep_const _).fmul (r76S9of_rep (r76theta_rep r)))))

private def r76head (c0 : ℚ) (r : Row) : Scaled :=
  (((Scaled.const 2).fmul (r76k r)).fadd ((Scaled.const 3).fmul (r76l r))).fadd (Scaled.const c0)

private theorem r76head_rep (c0 : ℚ) (r : Row) :
    (r76head c0 r).Rep (C 2*k r+C 3*l r+C c0) :=
  (((Scaled.rep_const _).fmul (r76k_rep r)).fadd ((Scaled.rep_const _).fmul (r76l_rep r))).fadd
    (Scaled.rep_const _)

private def r76tail (a b : ℚ) (r : Row) : Scaled :=
  ((Scaled.ofNat 1).fadd ((Scaled.const a).fmul (r76C10of (r76theta r)))).fadd
    ((Scaled.const b).fmul (r76S9of (r76theta r)))

private theorem r76tail_rep (a b : ℚ) (r : Row) :
    (r76tail a b r).Rep (1+C a*C10.comp (theta r)+C b*S9.comp (theta r)) :=
  (Scaled.rep_one.fadd ((Scaled.rep_const _).fmul (r76C10of_rep (r76theta_rep r)))).fadd
    ((Scaled.rep_const _).fmul (r76S9of_rep (r76theta_rep r)))

private def r76baseA (c0 c1 : ℚ) (r : Row) : Scaled :=
  ((r76head c0 r).fadd ((Scaled.const c1).fmul (r76m r))).fadd ((r76l r).fmul (r76J r))

private theorem r76baseA_rep (c0 c1 : ℚ) (r : Row) :
    (r76baseA c0 c1 r).Rep (C 2*k r+C 3*l r+C c0+C c1*m r+l r*J r) :=
  ((r76head_rep c0 r).fadd ((Scaled.rep_const _).fmul (r76m_rep r))).fadd
    ((r76l_rep r).fmul (r76J_rep r))

private def r76baseT (c0 a b : ℚ) (r : Row) : Scaled :=
  (r76head c0 r).fadd ((r76m r).fmul (r76tail a b r))

private theorem r76baseT_rep (c0 a b : ℚ) (r : Row) :
    (r76baseT c0 a b r).Rep (C 2*k r+C 3*l r+C c0+
      m r*(1+C a*C10.comp (theta r)+C b*S9.comp (theta r))) :=
  (r76head_rep c0 r).fadd ((r76m_rep r).fmul (r76tail_rep a b r))

private def r76base (r : Row) (ep : Split) : Scaled :=
  r76norm (if family r=.smallLow then
    match ep with
    | .atA => r76baseA (5/2-cbar) (5/2-cbar) r
    | .atT => r76baseT (5/2-cbar) (3/2-cbar) (1/2+eta*(1-cbar)-sigmabar) r
  else
    match ep with
    | .atA => r76baseA 3 3 r
    | .atT => r76baseT 3 2 (1/2+(3/2)*eta-sigmabar) r)

private theorem r76base_rep (r : Row) (ep : Split) : (r76base r ep).Rep (base r ep) := by
  unfold r76base base
  apply r76norm_rep
  split_ifs <;> cases ep
  · exact r76baseA_rep _ _ r
  · exact r76baseT_rep _ _ _ r
  · exact r76baseA_rep _ _ r
  · exact r76baseT_rep _ _ _ r

private def r76g (r : Row) : Scaled :=
  r76norm (((Scaled.const (13/12)).fmul (r76S11of (r76s r))).fadd
    ((Scaled.const (82/125)).fmul ((r76C10of (r76s r)).fsub (Scaled.ofNat 1))))

private theorem r76g_rep (r : Row) : (r76g r).Rep (g r) :=
  r76norm_rep (((Scaled.rep_const _).fmul (r76S11of_rep (r76s_rep r))).fadd
    ((Scaled.rep_const _).fmul ((r76C10of_rep (r76s_rep r)).fsub Scaled.rep_one)))

private def r76gainLower (r : Row) : Scaled :=
  if far (family r) then r76norm (((Scaled.const (201/200)).fmul (r76g r)).fsub
    (Scaled.const (11/50000))) else r76g r

private theorem r76gainLower_rep (r : Row) : (r76gainLower r).Rep (gainLower r) := by
  unfold r76gainLower gainLower
  split_ifs
  · exact r76norm_rep (((Scaled.rep_const _).fmul (r76g_rep r)).fsub (Scaled.rep_const _))
  · exact r76g_rep r

private def r76smaller (r : Row) : Fin 4→Scaled := ![r76k r,r76k r,r76l r,Scaled.ofNat 1]
private def r76larger (r : Row) : Fin 4→Scaled := ![Scaled.ofNat 1,r76l r,r76qStar r,Scaled.ofNat 1]

private theorem r76smaller_rep (r : Row) (i : Fin 4) : (r76smaller r i).Rep (smaller r i) := by
  fin_cases i
  exacts [r76k_rep r,r76k_rep r,r76l_rep r,Scaled.rep_one]

private theorem r76larger_rep (r : Row) (i : Fin 4) : (r76larger r i).Rep (larger r i) := by
  fin_cases i
  exacts [Scaled.rep_one,r76l_rep r,r76qStar_rep r,Scaled.rep_one]

private def r76extra (r : Row) : Scaled :=
  if equal r then ⟨[],1⟩ else if positive r then
    r76norm (((r76smaller r (index r)).fmul
      (((r76C10of (r76d r)).fadd (r76S11of (r76d r))).fsub (Scaled.ofNat 1))).fsub
      ((Scaled.const (1/200)).fmul (r76d r)))
  else r76norm ((r76larger r (index r)).fmul ((r76C10of (r76d r)).fsub (Scaled.ofNat 1)))

private theorem r76extra_rep (r : Row) : (r76extra r).Rep
    (if equal r then 0 else if positive r then positiveExtra r else negativeExtra r) := by
  unfold r76extra
  split_ifs
  · exact Scaled.rep_zero
  · exact r76norm_rep (((r76smaller_rep r (index r)).fmul
      (((r76C10of_rep (r76d_rep r)).fadd (r76S11of_rep (r76d_rep r))).fsub Scaled.rep_one)).fsub
      ((Scaled.rep_const _).fmul (r76d_rep r)))
  · exact r76norm_rep ((r76larger_rep r (index r)).fmul
      ((r76C10of_rep (r76d_rep r)).fsub Scaled.rep_one))

private def r76A (r : Row) (ep : Split) : Scaled :=
  r76norm (((r76base r ep).fadd (r76gainLower r)).fadd (r76extra r))

private theorem r76A_rep (r : Row) (ep : Split) : (r76A r ep).Rep (A r ep) :=
  r76norm_rep (((r76base_rep r ep).fadd (r76gainLower_rep r)).fadd (r76extra_rep r))

private def r76normZero (r : Row) (ep : Split) : Fin 4→Scaled :=
  ![(Scaled.ofNat 1).fadd ((r76k r).fpow 2),((r76k r).fpow 2).fadd ((r76l r).fpow 2),
    ((r76l r).fpow 2).fadd ((r76m r).fpow 2),(Scaled.ofNat 1).fadd ((r76cUpper r ep).fpow 2)]

private theorem r76normZero_rep (r : Row) (ep : Split) (i : Fin 4) :
    (r76normZero r ep i).Rep (normZero r ep i) := by
  fin_cases i
  exacts [Scaled.rep_one.fadd ((r76k_rep r).fpow 2),((r76k_rep r).fpow 2).fadd ((r76l_rep r).fpow 2),
    ((r76l_rep r).fpow 2).fadd ((r76m_rep r).fpow 2),Scaled.rep_one.fadd ((r76cUpper_rep r ep).fpow 2)]

private def r76product (r : Row) (ep : Split) : Fin 4→Scaled :=
  ![r76k r,(r76k r).fmul (r76l r),(r76l r).fmul (r76m r),r76cUpper r ep]

private theorem r76product_rep (r : Row) (ep : Split) (i : Fin 4) :
    (r76product r ep i).Rep (product r ep i) := by
  fin_cases i
  exacts [r76k_rep r,(r76k_rep r).fmul (r76l_rep r),(r76l_rep r).fmul (r76m_rep r),r76cUpper_rep r ep]

private def r76P (r : Row) (ep : Split) (i : Fin 4) : Scaled :=
  if active r i then r76norm ((r76normZero r ep i).fadd
    (if equal r∨i≠index r then ⟨[],1⟩
    else if positive r then ((Scaled.const 2).fmul (r76product r ep i)).fmul (r76S9of (r76d r))
    else (((Scaled.const 2).neg.fmul (r76product r ep i)).fmul (r76S11of (r76d r)))))
  else ⟨[],1⟩

private theorem r76P_rep (r : Row) (ep : Split) (i : Fin 4) : (r76P r ep i).Rep (P r ep i) := by
  unfold r76P P
  split_ifs
  · exact r76norm_rep ((r76normZero_rep r ep i).fadd Scaled.rep_zero)
  · exact r76norm_rep ((r76normZero_rep r ep i).fadd (((Scaled.rep_const _).fmul
      (r76product_rep r ep i)).fmul (r76S9of_rep (r76d_rep r))))
  · exact r76norm_rep ((r76normZero_rep r ep i).fadd ((((Scaled.rep_const _).neg).fmul
      (r76product_rep r ep i)).fmul (r76S11of_rep (r76d_rep r))))
  · exact Scaled.rep_zero

/-! ### The masses -/

private def r76w (c : Scaled) : Scaled :=
  r76norm ((⟨[(c.s:ℤ)],(c.l.getD 0 0).toNat⟩ : Scaled).fmul
    ((r76trunc c).fsub ⟨[c.l.getD 0 0],c.s⟩))

private theorem r76eval0 {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0) :
    p.eval 0=((c.l.getD 0 0:ℤ):ℚ)/c.s := by
  rw [← coeff_zero_eq_eval_zero,hc.coeff hs 0]

private theorem r76w_rep {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (hs : c.s≠0)
    (ha : 0<c.l.getD 0 0) :
    (r76w c).Rep (C (1/p.eval 0)*(truncate3 p-C (p.eval 0))) := by
  have h0 := r76eval0 hc hs
  have ht : ((((c.l.getD 0 0).toNat:ℕ):ℤ):ℚ)=((c.l.getD 0 0:ℤ):ℚ) := by
    rw [Int.toNat_of_nonneg ha.le]
  have hinv : (1:ℚ)/p.eval 0=(((c.s:ℕ):ℤ):ℚ)/(((c.l.getD 0 0).toNat:ℕ):ℚ) := by
    rw [h0,one_div_div,Int.cast_natCast,← ht,Int.cast_natCast]
  rw [hinv,h0]
  exact r76norm_rep ((r76frac_rep _ _ (by omega)).fmul ((r76trunc_rep hc).fsub (r76frac_rep _ _ hs)))

private def r76rhoJ (c : Scaled) (n : ℕ) : ℕ :=
  if 4*(c.l.getD 0 0)*1000000000000000000000000<(2*(n:ℤ)+1)^2*c.s then n else n+1

private def r76massB (c : Scaled) (n : ℕ) : Scaled :=
  r76norm ((⟨[(r76rhoJ c n:ℤ)],1000000000000⟩ : Scaled).fmul (r76trunc
    ((((Scaled.ofNat 1).fadd ((Scaled.const (1/2)).fmul (r76w c))).fsub
      ((Scaled.const (1/8)).fmul ((r76w c).fpow 2))).fadd
      ((Scaled.const (1/16)).fmul ((r76w c).fpow 3)))))

private theorem r76massB_rep {c : Scaled} {p : ℚ[X]} {n : ℕ} (hc : c.Rep p) (hs : c.s≠0)
    (ha : 0<c.l.getD 0 0)
    (hn : n*n≤(c.l.getD 0 0).toNat*1000000000000000000000000/c.s ∧
      (c.l.getD 0 0).toNat*1000000000000000000000000/c.s<(n+1)*(n+1)) :
    (r76massB c n).Rep (C (root12 (p.eval 0))*truncate3
      (1+C (1/2)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))-
        C (1/8)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))^2+
        C (1/16)*(C (1/p.eval 0)*(truncate3 p-C (p.eval 0)))^3)) := by
  have hρ : root12 (p.eval 0)=(((r76rhoJ c n:ℕ):ℤ):ℚ)/((1000000000000:ℕ):ℚ) := by
    rw [r76eval0 hc hs,r76root12 hs ha.le hn,Int.cast_natCast]
    rfl
  have hw := r76w_rep hc hs ha
  rw [hρ]
  exact r76norm_rep ((r76frac_rep _ _ (by norm_num)).fmul (r76trunc_rep (((Scaled.rep_one.fadd
    ((Scaled.rep_const _).fmul hw)).fsub ((Scaled.rep_const _).fmul (hw.fpow 2))).fadd
    ((Scaled.rep_const _).fmul (hw.fpow 3)))))

/-- The facts about `P` at zero that the mass representation uses. -/
private def r76PFact (r : Row) (ep : Split) (i : Fin 4) (n : ℕ) : Prop :=
  active r i → (r76P r ep i).s≠0 ∧ 0<(r76P r ep i).l.getD 0 0 ∧
    n*n≤((r76P r ep i).l.getD 0 0).toNat*1000000000000000000000000/(r76P r ep i).s ∧
    ((r76P r ep i).l.getD 0 0).toNat*1000000000000000000000000/(r76P r ep i).s<(n+1)*(n+1)

private def r76mass (r : Row) (ep : Split) (i : Fin 4) (n : ℕ) : Scaled :=
  if active r i then r76massB (r76P r ep i) n else Scaled.ofNat 1

private theorem r76mass_rep (r : Row) (ep : Split) (i : Fin 4) (n : ℕ) (h : r76PFact r ep i n) :
    (r76mass r ep i n).Rep (mass r ep i) := by
  unfold r76mass mass
  split_ifs with ha
  · obtain ⟨h1,h2,h3,h4⟩ := h ha
    exact r76massB_rep (r76P_rep r ep i) h1 h2 ⟨h3,h4⟩
  · exact Scaled.rep_one

/-! ### The numerators -/

private theorem r76erase (f : Fin 4→ℚ[X]) :
    ∏ j∈Finset.univ.erase (0:Fin 4),f j=f 1*f 2*f 3 ∧
    ∏ j∈Finset.univ.erase (1:Fin 4),f j=f 0*f 2*f 3 ∧
    ∏ j∈Finset.univ.erase (2:Fin 4),f j=f 0*f 1*f 3 ∧
    ∏ j∈Finset.univ.erase (3:Fin 4),f j=f 0*f 1*f 2 := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [show Finset.univ.erase (0:Fin 4)={1,2,3} by decide]; simp; ring
  · rw [show Finset.univ.erase (1:Fin 4)={0,2,3} by decide]; simp; ring
  · rw [show Finset.univ.erase (2:Fin 4)={0,1,3} by decide]; simp; ring
  · rw [show Finset.univ.erase (3:Fin 4)={0,1,2} by decide]; simp; ring

private def r76T (r : Row) (ep : Split) (i : Fin 4) (Mi o : Scaled) : Scaled :=
  if active r i then ((r76P r ep i).fadd (Mi.fpow 2)).fmul o else ⟨[],1⟩

private theorem r76T_rep (r : Row) (ep : Split) (i : Fin 4) {Mi o : Scaled} {q : ℚ[X]}
    (hM : Mi.Rep (mass r ep i)) (ho : o.Rep q) :
    (r76T r ep i Mi o).Rep (if active r i then (P r ep i+(mass r ep i)^2)*q else 0) := by
  unfold r76T
  split_ifs
  · exact ((r76P_rep r ep i).fadd (hM.fpow 2)).fmul ho
  · exact Scaled.rep_zero

private def r76numB (r : Row) (ep : Split) (M : Fin 4→Scaled) : Scaled :=
  r76norm ((((Scaled.const 2).fmul (r76A r ep)).fmul ((((M 0).fmul (M 1)).fmul (M 2)).fmul (M 3))).fsub
    ((Scaled.const Rbar).fmul ((((r76T r ep 0 (M 0) (((M 1).fmul (M 2)).fmul (M 3))).fadd
      (r76T r ep 1 (M 1) (((M 0).fmul (M 2)).fmul (M 3)))).fadd
      (r76T r ep 2 (M 2) (((M 0).fmul (M 1)).fmul (M 3)))).fadd
      (r76T r ep 3 (M 3) (((M 0).fmul (M 1)).fmul (M 2))))))

private theorem r76numB_rep (r : Row) (ep : Split) {M : Fin 4→Scaled}
    (hM : ∀ i,(M i).Rep (mass r ep i)) : (r76numB r ep M).Rep (numerator r ep) := by
  obtain ⟨e0,e1,e2,e3⟩ := r76erase (mass r ep)
  unfold numerator
  rw [Fin.prod_univ_four,Fin.sum_univ_four,e0,e1,e2,e3]
  exact r76norm_rep ((((Scaled.rep_const _).fmul (r76A_rep r ep)).fmul
    ((((hM 0).fmul (hM 1)).fmul (hM 2)).fmul (hM 3))).fsub
    ((Scaled.rep_const _).fmul ((((r76T_rep r ep 0 (hM 0) (((hM 1).fmul (hM 2)).fmul (hM 3))).fadd
      (r76T_rep r ep 1 (hM 1) (((hM 0).fmul (hM 2)).fmul (hM 3)))).fadd
      (r76T_rep r ep 2 (hM 2) (((hM 0).fmul (hM 1)).fmul (hM 3)))).fadd
      (r76T_rep r ep 3 (hM 3) (((hM 0).fmul (hM 1)).fmul (hM 2))))))

/-! ### Integer certificates -/

/-- The whole-interval certificate from one integer computation. -/
private theorem r76cert {c : Scaled} {lo hi : ℚ} {p : ℚ[X]} {D : ℕ}
    (hq : c.Rep (WholeIntervalPolynomial.centered lo hi p)) {a : ℤ} {b : ℕ}
    (h : c.s≠0 ∧ c.l.length≤D+1 ∧ b≠0 ∧ (chebF c.l).length≤D+1 ∧
      a*((c.s*2^c.l.length:ℕ):ℤ)<2*lowL (chebF c.l)*b) :
    WholeIntervalPolynomial.centered lo hi p=expansion D (WholeIntervalPolynomial.centered lo hi p) ∧
      (a:ℚ)/b<lowerOn D lo hi p := by
  refine ⟨hq.eq_expansion h.1 h.2.1,?_⟩
  rw [lowerOn_eq_of_rep hq h.1 h.2.1]
  have hM : (0:ℚ)<(c.s:ℚ)*2^c.l.length := by
    have : (0:ℚ)<c.s := by exact_mod_cast Nat.pos_of_ne_zero h.1
    positivity
  have hb : (0:ℚ)<b := by exact_mod_cast Nat.pos_of_ne_zero h.2.2.1
  rw [show ((lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ)/((c.s:ℚ)*2^c.l.length/2)=
    (2*(lowerZ D (fun j => (chebList c.l).getD j 0):ℤ):ℚ)/((c.s:ℚ)*2^c.l.length) by
      field_simp,div_lt_div_iff₀ hb hM]
  have h4 := h.2.2.2.2
  rw [← lowL_eq h.2.2.2.1,chebF_eq] at h4
  exact_mod_cast h4

private def r76wn : Row→ℕ
  | .lowEqual => 1 | .lowNegative => 1 | .smallHigh _ => 4 | .farPositive _ => 1
  | .farNegative _ => 3 | .farEqual => 3 | .farHigh _ _ => 9
private def r76wd : Row→ℕ
  | .lowEqual => 20 | .lowNegative => 30 | .smallHigh _ => 15 | .farPositive _ => 20
  | .farNegative _ => 40 | .farEqual => 40 | .farHigh _ _ => 40

private theorem r76centered {c : Scaled} {p : ℚ[X]} (hc : c.Rep p) (r : Row) :
    (centerS c (r76wn r) (r76wd r) 1 1).Rep (centered 0 (width r) p) := by
  rw [centerS_eq]
  apply hc.centered _ _ 1 1 <;> cases r <;> norm_num [r76wn,r76wd,width,left,right]

private def r76n : Row→Split→Fin 4→ℕ
  | .lowEqual,.atA => ![1159353078229,1159353078229,1534718749478,0]
  | .lowEqual,.atT => ![1159353078229,1159353078229,1534718749478,0]
  | .lowNegative,.atA => ![1185200213297,1185200213297,1468541525323,0]
  | .lowNegative,.atT => ![1185200213297,1185200213297,1468541525323,0]
  | .farEqual,.atA => ![1168770721741,1138121698237,1412934888804,1437737458648]
  | .farEqual,.atT => ![1168770721741,1138121698237,1412934888804,1455844098859]
  | .smallHigh i,.atA => (![![1165619171288,1203257511923,1425785990252,1425785990252],![1203257511923,1165619171288,1425785990252,1425785990252],![1203257511923,1203257511923,1377482985861,1425785990252]] : Fin 3→Fin 4→ℕ) i
  | .smallHigh i,.atT => (![![1165619171288,1203257511923,1425785990252,1451171530871],![1203257511923,1165619171288,1425785990252,1451171530871],![1203257511923,1203257511923,1377482985861,1451171530871]] : Fin 3→Fin 4→ℕ) i
  | .farPositive i,.atA => (![![1219353695259,1168770721741,1494021418855,1494021418855],![1168770721741,1168770721741,1566438694924,1494021418855],![1168770721741,1168770721741,1494021418855,1566438694924]] : Fin 3→Fin 4→ℕ) i
  | .farPositive i,.atT => (![![1219353695259,1168770721741,1494021418855,1494021418855],![1168770721741,1168770721741,1566438694924,1494021418855],![1168770721741,1168770721741,1494021418855,1566438694924]] : Fin 3→Fin 4→ℕ) i
  | .farNegative i,.atA => (![![1168770721741,1138121698237,1412934888804,1437737458648],![1168770721741,1138121698237,1412934888804,1437737458648]] : Fin 2→Fin 4→ℕ) i
  | .farNegative i,.atT => (![![1168770721741,1138121698237,1412934888804,1455844098859],![1168770721741,1138121698237,1412934888804,1455844098859]] : Fin 2→Fin 4→ℕ) i
  | .farHigh i true,.atA => (![![1168770721741,1092760266481,1292248524858,1357131625893],![1168770721741,1092760266481,1292248524858,1357131625893],![1168770721741,1092760266481,1292248524858,1357131625893]] : Fin 3→Fin 4→ℕ) i
  | .farHigh i true,.atT => (![![1168770721741,1092760266481,1292248524858,1383095713878],![1168770721741,1092760266481,1292248524858,1383095713878],![1168770721741,1092760266481,1292248524858,1383095713878]] : Fin 3→Fin 4→ℕ) i
  | .farHigh i false,.atA => (![![1088671143967,1092760266481,1292248524858,1357131625893],![1168770721741,1014681562034,1292248524858,1357131625893],![1168770721741,1092760266481,1191791502104,1357131625893]] : Fin 3→Fin 4→ℕ) i
  | .farHigh i false,.atT => (![![1088671143967,1092760266481,1292248524858,1383095713878],![1168770721741,1014681562034,1292248524858,1383095713878],![1168770721741,1092760266481,1191791502104,1383095713878]] : Fin 3→Fin 4→ℕ) i


private def r76M (r : Row) (ep : Split) (i : Fin 4) : Scaled := r76mass r ep i (r76n r ep i)
private def r76num (r : Row) (ep : Split) : Scaled := r76numB r ep (r76M r ep)

private def r76mr (r : Row) (i : Fin 4) : ℤ×ℕ :=
  if active r i then
    match family r with
    | .smallLow => (23,20) | .smallHigh => (83,100) | .farLow => (101,100) | .farHigh => (3,4)
  else (0,1)
private def r76rr (r : Row) : ℤ×ℕ :=
  match family r with
  | .smallLow => (49,10000) | .smallHigh => (27,500) | .farLow => (61,5000) | .farHigh => (29,2500)

/-- The integer facts of one row and split, checked by one kernel evaluation. -/
private abbrev r76Facts (r : Row) (ep : Split) : Prop :=
  (∀ i,active r i → (r76P r ep i).s≠0 ∧ 0<(r76P r ep i).l.getD 0 0 ∧
    r76n r ep i*r76n r ep i≤((r76P r ep i).l.getD 0 0).toNat*1000000000000000000000000/
      (r76P r ep i).s ∧
    ((r76P r ep i).l.getD 0 0).toNat*1000000000000000000000000/(r76P r ep i).s<
      (r76n r ep i+1)*(r76n r ep i+1) ∧
    0<r76rhoJ (r76P r ep i) (r76n r ep i) ∧
    (2*(r76rhoJ (r76P r ep i) (r76n r ep i):ℤ)-1)^2*(r76P r ep i).s≤
      4*(r76P r ep i).l.getD 0 0*1000000000000000000000000 ∧
    4*(r76P r ep i).l.getD 0 0*1000000000000000000000000<
      (2*(r76rhoJ (r76P r ep i) (r76n r ep i):ℤ)+1)^2*(r76P r ep i).s) ∧
  (∀ i,(centerS (r76M r ep i) (r76wn r) (r76wd r) 1 1).s≠0 ∧
    (centerS (r76M r ep i) (r76wn r) (r76wd r) 1 1).l.length≤3+1 ∧ (r76mr r i).2≠0 ∧
    (chebF (centerS (r76M r ep i) (r76wn r) (r76wd r) 1 1).l).length≤3+1 ∧
    (r76mr r i).1*(((centerS (r76M r ep i) (r76wn r) (r76wd r) 1 1).s*
      2^(centerS (r76M r ep i) (r76wn r) (r76wd r) 1 1).l.length:ℕ):ℤ)<
      2*lowL (chebF (centerS (r76M r ep i) (r76wn r) (r76wd r) 1 1).l)*
        (r76mr r i).2) ∧
  (affineCertificate r=false →
    (centerS (r76num r ep) (r76wn r) (r76wd r) 1 1).s≠0 ∧
    (centerS (r76num r ep) (r76wn r) (r76wd r) 1 1).l.length≤39+1 ∧ (r76rr r).2≠0 ∧
    (chebF (centerS (r76num r ep) (r76wn r) (r76wd r) 1 1).l).length≤39+1 ∧
    (r76rr r).1*(((centerS (r76num r ep) (r76wn r) (r76wd r) 1 1).s*
      2^(centerS (r76num r ep) (r76wn r) (r76wd r) 1 1).l.length:ℕ):ℤ)<
      2*lowL (chebF (centerS (r76num r ep) (r76wn r) (r76wd r) 1 1).l)*
        (r76rr r).2) ∧
  (affineCertificate r=true →
    (r76num r ep).s≠0 ∧ (r76num r ep).l.length≤40 ∧
    13*((r76num r ep).s:ℤ)<2000*(r76num r ep).l.getD 0 0 ∧
    (centerS (r76num r ep).divX (r76wn r) (r76wd r) 1 1).s≠0 ∧
    (centerS (r76num r ep).divX (r76wn r) (r76wd r) 1 1).l.length≤38+1 ∧ (250:ℕ)≠0 ∧
    (chebF (centerS (r76num r ep).divX (r76wn r) (r76wd r) 1 1).l).length≤38+1 ∧
    (1:ℤ)*(((centerS (r76num r ep).divX (r76wn r) (r76wd r) 1 1).s*
      2^(centerS (r76num r ep).divX (r76wn r) (r76wd r) 1 1).l.length:ℕ):ℤ)<
      2*lowL (chebF (centerS (r76num r ep).divX (r76wn r) (r76wd r) 1 1).l)*
        (250:ℕ))

/-! ### The kernel checks, one row at a time

Both splits of a row share their masses and most of their numerator, so they are checked in
one kernel evaluation. -/

private abbrev r76Both (r : Row) : Prop := r76Facts r .atA ∧ r76Facts r .atT

set_option synthInstance.maxSize 4096 in
private theorem r76f_lowEqual : r76Both .lowEqual := by
  decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_lowNegative : r76Both .lowNegative := by
  decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farEqual : r76Both .farEqual := by
  decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_smallHigh (i : Fin 3) : r76Both (.smallHigh i) := by
  fin_cases i <;> decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farPositive (i : Fin 3) : r76Both (.farPositive i) := by
  fin_cases i <;> decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farNegative (i : Fin 2) : r76Both (.farNegative i) := by
  fin_cases i <;> decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farHigh_false (i : Fin 3) : r76Both (.farHigh i false) := by
  fin_cases i <;> decide +kernel
set_option synthInstance.maxSize 4096 in
private theorem r76f_farHigh_true (i : Fin 3) : r76Both (.farHigh i true) := by
  fin_cases i <;> decide +kernel

private theorem r76facts (r : Row) (ep : Split) : r76Facts r ep := by
  have h : r76Both r := by
    rcases r with _|_|i|i|i|_|⟨i,_|_⟩
    · exact r76f_lowEqual
    · exact r76f_lowNegative
    · exact r76f_smallHigh i
    · exact r76f_farPositive i
    · exact r76f_farNegative i
    · exact r76f_farEqual
    · exact r76f_farHigh_false i
    · exact r76f_farHigh_true i
  cases ep
  · exact h.1
  · exact h.2


/-! ### From the integer facts to the stated certificates -/

private theorem r76M_rep (r : Row) (ep : Split) (i : Fin 4) : (r76M r ep i).Rep (mass r ep i) :=
  r76mass_rep r ep i _ (fun ha => by
    obtain ⟨h1,h2,h3,h4,-⟩ := (r76facts r ep).1 i ha
    exact ⟨h1,h2,h3,h4⟩)

private theorem r76num_rep (r : Row) (ep : Split) : (r76num r ep).Rep (numerator r ep) :=
  r76numB_rep r ep (r76M_rep r ep)

private theorem r76mr_eq (r : Row) (i : Fin 4) :
    (if active r i then massReserve r else 0)=(((r76mr r i).1:ℤ):ℚ)/((r76mr r i).2:ℕ) := by
  unfold r76mr massReserve
  split_ifs
  · cases family r <;> norm_num
  · norm_num

private theorem r76rr_eq (r : Row) : reserve r=(((r76rr r).1:ℤ):ℚ)/((r76rr r).2:ℕ) := by
  unfold r76rr reserve
  cases family r <;> norm_num

private theorem r76quot {p : ℚ[X]} (hp : p.natDegree≤39) :
    (∑i : Fin 39,C (p.coeff (i.val+1))*X^i.val)=divX p := by
  ext n
  rw [finsetSum_coeff,coeff_divX]
  simp only [coeff_C_mul_X_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => if n=i then p.coeff (i+1) else 0) 39,
    Finset.sum_ite_eq]
  split_ifs with hn
  · rfl
  · rw [Finset.mem_range,not_lt] at hn
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem mass_certificate : ∀r : Row,∀ep : Split,∀i : Fin 4,
    centered 0 (width r) (mass r ep i)=expansion 3 (centered 0 (width r) (mass r ep i)) ∧
    (if active r i then massReserve r else 0)<lowerOn 3 0 (width r) (mass r ep i) := by
  intro r ep i
  rw [r76mr_eq]
  exact r76cert (r76centered (r76M_rep r ep i) r) ((r76facts r ep).2.1 i)

theorem direct_certificate : ∀r : Row,∀ep : Split,affineCertificate r=false →
    centered 0 (width r) (numerator r ep)=
      expansion 39 (centered 0 (width r) (numerator r ep)) ∧
    reserve r<lowerOn 39 0 (width r) (numerator r ep) := by
  intro r ep ha
  rw [r76rr_eq]
  exact r76cert (r76centered (r76num_rep r ep) r) ((r76facts r ep).2.2.1 ha)

theorem affine_certificate : ∀r : Row,∀ep : Split,affineCertificate r=true →
    numerator r ep=C ((numerator r ep).coeff 0)+X*quotient r ep ∧
    (13/2000:ℚ)<(numerator r ep).coeff 0 ∧
    centered 0 (width r) (quotient r ep)=
      expansion 38 (centered 0 (width r) (quotient r ep)) ∧
    (1/250:ℚ)<lowerOn 38 0 (width r) (quotient r ep) := by
  intro r ep ha
  obtain ⟨h1,h2,h3,h4⟩ := (r76facts r ep).2.2.2 ha
  have hN := r76num_rep r ep
  have hq : quotient r ep=divX (numerator r ep) :=
    r76quot ((hN.natDegree_le h1).trans (by omega))
  have hc := r76cert (r76centered hN.divX r) h4
  rw [hq]
  refine ⟨(X_mul_divX_add _).symm.trans (add_comm _ _),?_,hc.1,?_⟩
  · rw [hN.coeff h1 0]
    have hs : (0:ℚ)<(r76num r ep).s := by exact_mod_cast Nat.pos_of_ne_zero h1
    rw [lt_div_iff₀ hs]
    have h3' : ((13*((r76num r ep).s:ℤ):ℤ):ℚ)<((2000*(r76num r ep).l.getD 0 0:ℤ):ℚ) := by
      exact_mod_cast h3
    push_cast at h3'
    linarith
  · have h := hc.2
    norm_num at h
    exact h

theorem mass_positive (r : Row) (ep : Split) (i : Fin 4) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : 0<aeval x (mass r ep i) := by
  have hc := mass_certificate r ep i
  have hh := positive_on_interval (interval_positive r) hc.1 hc.2
    (show x∈Icc ((0:ℚ):ℝ) (width r:ℝ) by simpa using hx)
  have hreserve : (0:ℝ)≤((if active r i then massReserve r else 0:ℚ):ℝ) := by
    split_ifs
    · cases r <;> norm_num [massReserve,family]
    · norm_num
  exact hreserve.trans_lt hh

theorem numerator_positive (r : Row) (ep : Split) {x : ℝ}
    (hx : x∈Icc 0 (width r:ℝ)) : 0<aeval x (numerator r ep) := by
  have hx' : x∈Icc ((0:ℚ):ℝ) (width r:ℝ) := by simpa using hx
  cases ha : affineCertificate r
  · have hc := direct_certificate r ep ha
    have hh := positive_on_interval (interval_positive r) hc.1 hc.2 hx'
    have hr : (0:ℝ)<(reserve r:ℝ) := by cases r <;> norm_num [reserve,family]
    exact hr.trans hh
  · have hc := affine_certificate r ep ha
    have hq := positive_on_interval (interval_positive r) hc.2.2.1 hc.2.2.2 hx'
    have hconst : (13/2000:ℝ)<((numerator r ep).coeff 0:ℝ) := by
      have h := (Rat.cast_lt (K:=ℝ)).mpr hc.2.1
      rwa [show (((13/2000:ℚ)):ℝ)=13/2000 by norm_num] at h
    have he := congrArg (fun p : ℚ[X] => aeval x p) hc.1
    simp only [map_add,map_mul,aeval_C,aeval_X,eq_ratCast] at he
    have hm := mul_nonneg hx.1 (show 0≤aeval x (quotient r ep) by linarith)
    linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.Certificate
