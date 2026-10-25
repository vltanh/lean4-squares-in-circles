module

public import Mathlib.Algebra.Order.Ring.Star
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTPolynomials
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTSupport

/-!
# Eight squares: actual contact coefficients and their scalar charges

H and the TD B block retain the maximum of their
two actual coefficients during concentration. Only afterward is the
high B coefficient enlarged to m+.03, and the H scalar is selected
between its two already proved full-square inequalities.
-/

section
/-!
## Ordinary blocks at an EH0 contact with positive T

The EH angle stays in the H block. The D block is written with its only ordinary coefficient
first: the same signed block with its two arguments exchanged (`swap`, `swap_data`), so no owner
changes. With the budgets of the cycle (`original_budgets`), the common concentration theorem
takes the angular endpoint inequalities of the critical strip and of its outside
(`block_minorant`, `original_lower`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTBlocks
open Candidate ActualOrdinaryBlocks ActualCoreEBlocks PositiveAngularEnvelope
open SingleAngleConcavity ExceptionalPositiveTStress

structure Weights where
  n : ℝ
  k : ℝ
  ell : ℝ
  b : ℝ
  d : ℝ
  p : ℝ

def first (w : Weights) : Fin 4 → ℝ := ![w.p,w.k,w.ell,1]
def second (w : Weights) : Fin 4 → ℝ := ![w.n,w.ell,w.b,w.d]
def small (w : Weights) (i : Fin 4) : ℝ := min (first w i) (second w i)
def large (w : Weights) (i : Fin 4) : ℝ := max (first w i) (second w i)
def single (td : Bool) : Fin 4 → Bool := ![false,true,!td,true]
def negative (w : Weights) (td : Bool) : Fin 4 → ℝ :=
  ![max w.p w.n,w.ell,if td then max w.ell w.b else w.ell,w.d]
def rawBlocks (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) : Fin 4 → Block :=
  SoleEStress.blocks C ab (btOwner td) (tdOwner td) 3 0 w.n w.k w.ell w.b w.d 1 w.p
def swap (B : Block) : Block := ⟨B.beta,B.alpha,B.v,B.u⟩
def blocks (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) (i : Fin 4) : Block :=
  if i=3 then swap (rawBlocks C ab td w i) else rawBlocks C ab td w i
def increment (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) (R : ℝ) : ℝ :=
  SoleEStress.increment C ab (btOwner td) (tdOwner td) 3 0 w.n w.k w.ell w.b w.d 1 w.p R

theorem small_le_large (w : Weights) (i : Fin 4) : small w i≤large w i := min_le_max
theorem negative_between (w : Weights) (td : Bool) (i : Fin 4) :
    small w i≤negative w td i ∧ negative w td i≤large w i := by
  fin_cases i <;> cases td <;>
    simp [small,large,negative,first,second]
theorem mixed_negative (w : Weights) (td : Bool) (i : Fin 4) (hi : single td i=false) :
    negative w td i=large w i := by
  fin_cases i <;> cases td <;> simp_all [single,negative,large,first,second]
theorem pure_eq (w : Weights) (td : Bool) (R u : ℝ) (i : Fin 4) :
    pure (single td i) R (small w i) (large w i) (negative w td i) u=
      Vnu R (small w i) (large w i) (negative w td i) u := by
  cases hi : single td i
  · rw [mixed_negative w td i hi]
    rfl
  · rfl
theorem norm_eq (w : Weights) (u : ℝ) (i : Fin 4) :
    pairNorm (small w i) (large w i) u=pairNorm (first w i) (second w i) u := by
  rcases le_total (first w i) (second w i) with h | h
  · simp [small,large,min_eq_left h,max_eq_right h]
  · simp [small,large,min_eq_right h,max_eq_left h,pairNorm_symm]
theorem swap_data (B : Block) (R : ℝ) :
    (swap B).p=B.p ∧ (swap B).q=B.q ∧ (swap B).P=B.P ∧
    (swap B).N=B.N ∧ (swap B).increment R=B.increment R := by
  simp [swap,Block.p,Block.q,Block.P,Block.N,Block.increment,min_comm,max_comm,
    pairNorm_symm,add_comm]
theorem coefficients (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) (i : Fin 4) :
    (blocks C ab td w i).p=small w i ∧ (blocks C ab td w i).q=large w i := by
  fin_cases i <;> simp [blocks,rawBlocks,swap,SoleEStress.blocks,Block.p,Block.q,
    small,large,first,second,min_comm,max_comm]
theorem single_data (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights)
    (i : Fin 4) (hi : single td i=true) :
    (blocks C ab td w i).v=0 ∧ (blocks C ab td w i).alpha=negative w td i := by
  fin_cases i <;> cases td <;>
    simp_all [single,blocks,rawBlocks,swap,SoleEStress.blocks,negative,
      btOwner,tdOwner,ordinaryDE,ordinaryEH]
theorem parts (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights) (i : Fin 4) :
    (blocks C ab td w i).P=
      (ActualCoreEBlocks.blocks C ab (btOwner td) (tdOwner td) 3 0 w.n w.k w.ell w.b w.d i).P ∧
    (blocks C ab td w i).N=
      (ActualCoreEBlocks.blocks C ab (btOwner td) (tdOwner td) 3 0 w.n w.k w.ell w.b w.d i).N := by
  fin_cases i <;> simp [blocks,rawBlocks,swap,SoleEStress.blocks,ActualCoreEBlocks.blocks,
    Block.P,Block.N,add_comm]
theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (td : Bool) (w : Weights) {t : ℝ} (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤primary C td)
    (htotal : delta C.theta G+delta C.theta D+primary C td=t) :
    t∈Icc 0 frameCap ∧ (∑i,(blocks C ab td w i).P)≤frameCap-t ∧
      (∑i,(blocks C ab td w i).N)=t+∑i,(blocks C ab td w i).P := by
  have hBT : btOwner td=3 → 0≤delta C.theta B := by cases td <;> simp_all [btOwner,primary]
  have hTD : tdOwner td=2 → 0≤delta C.theta T := by cases td <;> simp_all [tdOwner,primary]
  have hremoved : removed C (btOwner td) (tdOwner td)=delta C.theta G+primary C td := by
    cases td <;> simp [removed,btOwner,tdOwner,primary]
  have hEtotal : eTotal C 3 0=delta C.theta D := by simp [eTotal,primaryDE,primaryEH]
  have hh := ActualCoreEBlocks.block_budgets hab (bt_cases td) (td_cases td)
    (Or.inr rfl) (Or.inl rfl) w.n w.k w.ell w.b w.d hvar hG hBT hTD
    (by simpa only [hEtotal] using hD)
  have hP := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => (parts C ab td w i).1)
  have hN := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => (parts C ab td w i).2)
  rw [hEtotal,hremoved] at hh
  refine ⟨⟨by linarith,by linarith [hh.2.1.2]⟩,?_,?_⟩
  · rw [hP]
    linarith [hh.2.2.1]
  · rw [hN,hP]
    linarith [hh.2.2.2]
theorem single_parts (C : SignedCycle) (ab : Fin 4) (td : Bool) (w : Weights)
    (i : Fin 4) (hi : single td i=true) :
    (blocks C ab td w i).P=0 ∨ (blocks C ab td w i).N=0 := by
  have hv := (single_data C ab td w i hi).1
  by_cases hu : 0≤(blocks C ab td w i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right (show -(blocks C ab td w i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]
theorem angles_small {C : SignedCycle} (ab : Fin 4) (td : Bool) (w : Weights)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 4) :
    |(blocks C ab td w i).u|≤frameCap ∧ |(blocks C ab td w i).v|≤frameCap := by
  have hzero : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hzero' : (0:ℝ)≤frameCap := by norm_num [frameCap]
  have hA : |if ab=0 then 0 else delta C.theta A|≤frameCap := by
    split_ifs <;> first | exact hzero | exact ha A
  have hB : |if ab=0 then delta C.theta A else 0|≤frameCap := by
    split_ifs <;> first | exact hzero | exact ha A
  fin_cases i <;> cases td <;>
    simp [blocks,rawBlocks,swap,SoleEStress.blocks,btOwner,tdOwner,ordinaryDE,ordinaryEH,
      ha H,ha B,ha T,ha E,hzero',hA,hB]
theorem block_minorant {C : SignedCycle} {ab : Fin 4} {td : Bool} {w : Weights} {R t : ℝ}
    (ht : 0≤t) (hp : ∀ i,0<small w i) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab td w i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab td w i).N)=t+∑i,(blocks C ab td w i).P) (i : Fin 4) :
    F (single td i) R (small w i) (large w i) (negative w td i)
      (blocks C ab td w i).P (blocks C ab td w i).N≤(blocks C ab td w i).increment R := by
  obtain ⟨hpi,hqi⟩ := coefficients C ab td w i
  have hPi := Finset.single_le_sum (fun j _ => (blocks C ab td w j).P_nonneg) (Finset.mem_univ i)
  have hNi := Finset.single_le_sum (fun j _ => (blocks C ab td w j).N_nonneg) (Finset.mem_univ i)
  cases hi : single td i
  · have hh := (blocks C ab td w i).minorant R
      (by rw [hpi]; exact (hp i).le) (by linarith) (by linarith)
    rw [mixed_negative w td i hi]
    simpa only [F,hi,Bool.false_eq_true,↓reduceIte,hpi,hqi] using hh
  · obtain ⟨hv,hnu⟩ := single_data C ab td w i hi
    have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab td w i) R hv
      (angles_small ab td w ha i).1
    simpa only [hi,hpi,hqi,hnu] using hh
theorem increment_eq {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (td : Bool) (w : Weights) (R : ℝ) :
    increment C ab td w R=∑i,(blocks C ab td w i).increment R := by
  rw [increment,SoleEStress.increment_eq C hab (bt_cases td) (td_cases td)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [blocks]
  split_ifs
  · exact (swap_data (rawBlocks C ab td w i) R).2.2.2.2.symm
  · rfl

theorem original_lower {C : SignedCycle} {ab : Fin 4} (td : Bool) (w : Weights)
    {R t L : ℝ} (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQU : R^2≤qCap)
    (hp : ∀ i,0<small w i) (hhalf : ∀ i,large w i≤2*small w i)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤primary C td)
    (htotal : delta C.theta G+delta C.theta D+primary C td=t)
    (hpure : ∀ i,L≤pure (single td i) R (small w i) (large w i) (negative w td i) t)
    (hsame : ∀ i,single td i=false → L≤OrdinaryAngleConcentration.M R (small w i) (large w i) t)
    (hseparated : ∀ i j,i≠j → L≤OrdinaryAngleConcavity.U R (small w i) (large w i) (frameCap-t)+
      pure (single td j) R (small w j) (large w j) (negative w td j) frameCap) :
    L≤ increment C ab td w R := by
  obtain ⟨ht,hP,hN⟩ := original_budgets hab td w hvar hG hD hT htotal
  have henvelope := SingleAngleConcentration.lower_from_endpoints (single td) R
    (small w) (large w) (negative w td)
    (fun i => (blocks C ab td w i).P) (fun i => (blocks C ab td w i).N)
    hR hQU hp (small_le_large w) hhalf (fun i => (negative_between w td i).1)
    (fun i => (blocks C ab td w i).P_nonneg) (fun i => (blocks C ab td w i).N_nonneg)
    ht hP hN (single_parts C ab td w) hpure hsame hseparated
  have hminor := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_minorant (R := R) ht.1 hp ha hP hN i)
  rw [increment_eq hab td w R]
  exact henvelope.trans hminor

end SquaresInCircles.Eight.ExceptionalPositiveTBlocks
end
end
end

section
/-!
## Radical transfer for the four positive-T contact families

The complete polynomial lower bound transfers to
the original radical expression because every majorized root occurs
with a nonpositive coefficient. Radius monotonicity then restores the
actual common ceiling, without changing any original point or axis.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTScalar
open ExceptionalPositiveTScalarModel ExceptionalPositiveTPolynomials TensorPolynomialEnclosure
open ExceptionalContactStress ExceptionalContactSupport

section r54_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
@[simp] private theorem r54_value_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
@[simp] private theorem r54_value_neg : Expression.value v (-a)=-Expression.value v a := rfl
@[simp] private theorem r54_value_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
@[simp] private theorem r54_value_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
@[simp] private theorem r54_value_pow (n : ℕ) :
    Expression.value v (a^n)=Expression.value v a^n := rfl
@[simp] private theorem r54_value_one : Expression.value v (1 : Expression ι)=1 := by
  show (((1:ℕ):ℚ):ℝ)=1
  norm_num
@[simp] private theorem r54_value_two : Expression.value v (2 : Expression ι)=2 := by
  show (((2:ℕ):ℚ):ℝ)=2
  norm_num
@[simp] private theorem r54_value_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
@[simp] private theorem r54_value_ite (P : Prop) [Decidable P] :
    Expression.value v (if P then a else b)=
      if P then Expression.value v a else Expression.value v b := by
  split_ifs <;> rfl
end r54_value

@[simp] private theorem r54_value_lit (w : Fin 10 → ℝ) (r : ℚ) :
    Expression.value w (lit r)=(r:ℝ) := rfl
@[simp] private theorem r54_value_var (w : Fin 10 → ℝ) (i : Fin 10) :
    Expression.value w (var i)=w i := rfl
section r54_inputs
variable (s : ScalarCase) (t z : ℝ)
@[simp] private theorem r54_inputs_0 : inputs s t z 0=t := rfl
@[simp] private theorem r54_inputs_1 : inputs s t z 1=z := rfl
@[simp] private theorem r54_inputs_2 : inputs s t z 2=Real.sin (x s t z) := rfl
@[simp] private theorem r54_inputs_3 : inputs s t z 3=Real.cos (x s t z) := rfl
@[simp] private theorem r54_inputs_4 : inputs s t z 4=Real.sin z := rfl
@[simp] private theorem r54_inputs_5 : inputs s t z 5=Real.cos z := rfl
@[simp] private theorem r54_inputs_6 :
    inputs s t z 6=Real.sin (ExceptionalPositiveTScalarModel.e s t z) := rfl
@[simp] private theorem r54_inputs_7 :
    inputs s t z 7=Real.cos (ExceptionalPositiveTScalarModel.e s t z) := rfl
@[simp] private theorem r54_inputs_8 : inputs s t z 8=Real.sin t := rfl
@[simp] private theorem r54_inputs_9 : inputs s t z 9=Real.cos t := rfl
end r54_inputs

@[simp] theorem KE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (KE f)=K f t := by
  cases f <;> norm_num [KE,K,tE,inputs,Expression.value]
@[simp] theorem LE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (LE f)=L f t := by
  cases f <;> norm_num [ExceptionalPositiveTPolynomials.LE,L,tE,inputs,Expression.value] <;> ring
@[simp] theorem CE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (CE f)=C f t := by
  cases f <;> norm_num [CE,C,tE,inputs,Expression.value]
  ring
@[simp] theorem etaE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (etaE f)=eta f t := by
  cases f <;> norm_num [etaE,eta,tE,inputs,Expression.value]
  ring
@[simp] theorem kE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (kE f)=k f t z := by
  simp [kE,k,zE]
@[simp] theorem ellE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (ellE f)=ell f t z := by
  simp [ellE,ell,zE]
@[simp] theorem cE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (cE f)=c f t z := by
  simp [cE,c,zE]
@[simp] theorem nE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (nE s)=n s t z := by
  simp [nE,n,tilt,cx,sx]
@[simp] theorem mE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (mE s)=m s t z := by
  simp [mE,m,tilt,cz,sz]
@[simp] theorem pE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (pE s)=p s t z := by
  simp [pE,p,tilt,ce,se]
@[simp] theorem firstE_value (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (firstE s i)=first s t z i := by
  fin_cases i <;> simp [firstE,first]
@[simp] theorem secondE_value (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (secondE s i)=second s t z i := by
  fin_cases i <;> simp [secondE,second]
@[simp] theorem nuE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (nuE s)=nu s t z := by
  rcases s with ⟨f,td,atG,i,h⟩
  fin_cases i <;> simp [nuE,nu,Expression.value]
@[simp] theorem squareE_value (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (squareE s i)=square s t z i := by
  simp [squareE,square,st]

def rootArgument (s : ScalarCase) (t z : ℝ) (i : Fin 5) : ℝ :=
  if hi : i.val<4 then square s t z ⟨i.val,hi⟩ else 1+(eta s.family t)^2
@[simp] theorem rootSquare_value (s : ScalarCase) (t z : ℝ) (i : Fin 5) :
    Expression.value (inputs s t z) (rootSquare s i)=rootArgument s t z i := by
  dsimp [rootSquare,rootArgument]
  split_ifs <;> simp [Expression.value]
def upper (s : ScalarCase) (t z : ℝ) (i : Fin 5) : ℝ :=
  Expression.value (inputs s t z) (rootExpression s i)
@[simp] theorem rootExpression_value (s : ScalarCase) (t z : ℝ) (i : Fin 5) :
    Expression.value (inputs s t z) (rootExpression s i)=upper s t z i := rfl
theorem rootArgument_nonneg (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 5) :
    0≤rootArgument s t z i := by
  dsimp [rootArgument]
  split_ifs
  · exact square_nonneg s ht hz _
  · positivity
theorem root_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 5) :
    Real.sqrt (rootArgument s t z i)≤upper s t z i := by
  have h := Expression.sqrt_le_value (inputs s t z) («variables» s) (rootSquare s i)
    (by simpa using rootArgument_nonneg s ht hz i) (seeds_positive s i)
  simpa only [rootSquare_value,upper,rootExpression] using h

theorem expression_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (expression s)=
      k s.family t z*(1+2*Real.cos (x s t z)+(1+2*eta s.family t)*Real.sin (x s t z))+
      c s.family t z*(1+2*Real.cos z+(1+2*eta s.family t)*Real.sin z)+2*ell s.family t z+
      1+2*Real.cos (ExceptionalPositiveTScalarModel.e s t z)+(1+2*eta s.family t)*Real.sin (ExceptionalPositiveTScalarModel.e s t z)-
      (radiusUpper:ℝ)*(k s.family t z*Real.sin (x s t z)+
        c s.family t z*Real.sin z+Real.sin (ExceptionalPositiveTScalarModel.e s t z))*upper s t z 4+
      nu s t z*(Real.cos t-1)-(radiusUpper:ℝ)*
        (upper s t z 0+upper s t z 1+upper s t z 2+upper s t z 3) := by
  simp [expression,baseExpression,cx,sx,cz,sz,ce,se,ct]
  ring

theorem model_le_actual (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    Expression.value (inputs s t z) (expression s)≤value s (radiusUpper:ℝ) t z := by
  obtain ⟨hk,hl,hc,hη⟩ := coefficient_positive ht hz
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  have hsx := (transport_trig hx).2.2.1
  have hsz := (transport_trig hz').2.2.1
  have hse := (transport_trig he).2.2.1
  have hr : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper,SoleTScalarModel.radiusUpper]
  have hroot := root_lower s ht hz 4
  norm_num [rootArgument] at hroot
  have hmul := mul_le_mul_of_nonneg_left hroot
    (mul_nonneg hr (add_nonneg (add_nonneg (mul_nonneg hk.le hsx)
      (mul_nonneg hc.le hsz)) hse))
  have h0 := root_lower s ht hz 0
  have h1 := root_lower s ht hz 1
  have h2 := root_lower s ht hz 2
  have h3 := root_lower s ht hz 3
  norm_num [rootArgument] at h0 h1 h2 h3
  have hsum' := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) hr
  rw [expression_value]
  dsimp [ExceptionalPositiveTScalarModel.value,contactScalar]
  rw [Fin.sum_univ_four]
  linarith

theorem square_coordinates (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    ∃ X Y : ℝ,|X|≤1 ∧ |Y|≤1 ∧ parameterValue s.family X=t ∧
      secondValue s.family X Y=z := by
  let a : ℝ := (left s.family:ℝ)
  let b : ℝ := (right s.family:ℝ)
  have hab : a<b := by simp only [a,b]; exact_mod_cast (interval_order s.family).2.1
  have hwidth : 0<b-a := by linarith
  have hta : a≤t := ht.1
  have htb : t≤b := ht.2
  let X : ℝ := (2*t-a-b)/(b-a)
  have hX : |X|≤1 := by
    apply abs_le.mpr
    dsimp [X]
    constructor
    · apply (le_div_iff₀ hwidth).2
      linarith
    · apply (div_le_iff₀ hwidth).2
      linarith
  have htX : parameterValue s.family X=t := by
    change (a+b)/2+(b-a)/2*((2*t-a-b)/(b-a))=t
    field_simp [hwidth.ne']
    ring
  by_cases ht0 : t=0
  · have hz0 : z=0 := by linarith [hz.1,hz.2]
    refine ⟨X,0,hX,by norm_num,htX,?_⟩
    simp [secondValue,htX,ht0,hz0]
  · have htpos : 0<t := lt_of_le_of_ne (hz.1.trans hz.2) (Ne.symm ht0)
    let Y : ℝ := 2*z/t-1
    have hY : |Y|≤1 := by
      apply abs_le.mpr
      constructor
      · have hh : 0≤2*z/t := div_nonneg (by linarith [hz.1]) htpos.le
        dsimp [Y]
        linarith
      · have hh : 2*z/t≤2 := (div_le_iff₀ htpos).2 (by linarith [hz.2])
        dsimp [Y]
        linarith
    refine ⟨X,Y,hX,hY,htX,?_⟩
    rw [secondValue,htX]
    dsimp [Y]
    field_simp [ht0]
    ring

theorem conservative_positive (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    (77/1000000:ℝ)<value s (radiusUpper:ℝ) t z := by
  obtain ⟨X,Y,hX,hY,htX,hzY⟩ := square_coordinates s ht hz
  have hp := model_positive s hX hY
  rw [htX,hzY] at hp
  exact hp.trans_le (model_le_actual s ht hz)

theorem antitone_radius (s : ScalarCase) {t z R R' : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (hR : R≤R') :
    value s R' t z≤value s R t z := by
  obtain ⟨hk,hl,hc,hη⟩ := coefficient_positive ht hz
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  have hroot := Real.sqrt_nonneg (1+(eta s.family t)^2)
  have hG := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (mul_nonneg hk.le (transport_trig hx).2.2.1) hroot)
  have hT := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (mul_nonneg hc.le (transport_trig hz').2.2.1) hroot)
  have hE := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (transport_trig he).2.2.1 hroot)
  have hsum : 0≤∑ i : Fin 4,Real.sqrt (square s t z i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hnorm := mul_nonneg (sub_nonneg.mpr hR) hsum
  dsimp [ExceptionalPositiveTScalarModel.value,contactScalar]
  nlinarith

theorem actual_radius_positive (s : ScalarCase) {q t z : ℝ}
    (hq : q≤qTrial) (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    (77/1000000:ℝ)<value s (Real.sqrt q) t z := by
  have hR := (Real.sqrt_le_sqrt hq).trans SoleTScalarModel.radius_upper.le
  exact (conservative_positive s ht hz).trans_le (antitone_radius s ht hz hR)

end SquaresInCircles.Eight.ExceptionalPositiveTScalar
end
end
end

section
/-!
## Coefficient correlations of the positive-T contact blocks

The ranges of the coefficients on the whole square, with the H ratio that an unaligned contact
requires (`ratio_lower`, `pair_upper`, `larger_lower`, `smaller_lower`). Every comparison is an
exact polynomial reduction; the cases are the coefficient families and the block indices, and the
thirty-one tests are checked on packed Taylor models (`tests_nonnegative`).
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTCoefficients
open ExceptionalPositiveTScalarModel ExceptionalPositiveTPolynomials
open TensorPolynomialEnclosure TensorWholeIntervalPolynomial

def cap : Family → ℚ
  | .lowZero | .lowAfter => 21/20
  | .middle => 559/500
  | .high => 1131/1000
def largeFloor : Family → ℚ
  | .lowZero | .lowAfter => 431/500
  | .middle => 911/1000
  | .high => 0
def smallFloor (f : Family) (i : Fin 4) : ℚ :=
  match f with
  | .middle => if i=0 ∨ i=3 then 911/1000 else 0
  | .high => 731/1000
  | _ => 0
def ratioE (f : Family) (i : Fin 4) : Expr :=
  match f with
  | .lowZero | .lowAfter => if i=0 then lit (41/50)
      else if i=2 then lit (117/200)+lit (1/5)*tE else lit (117/200)
  | .middle => if i=1 then lit (31/50) else if i=2 then lit (2/3) else lit (71/100)
  | .high => lit (71/100)
def witnessE (s : ScalarCase) (i : Fin 4) : Expr :=
  if i=0 ∨ i=2 then secondE s i else firstE s i

inductive Test where
  | ratioFirst (i : Fin 4) | ratioSecond (i : Fin 4)
  | upperFirst (i : Fin 4) | upperSecond (i : Fin 4)
  | larger (i : Fin 4) | smallerFirst (i : Fin 4) | smallerSecond (i : Fin 4)
  | middleAUpper | middleALower | mixedB
  deriving DecidableEq

instance : Fintype Test where
  elems := {.middleAUpper, .middleALower, .mixedB} ∪
    Finset.univ.image Test.ratioFirst ∪
    Finset.univ.image Test.ratioSecond ∪
    Finset.univ.image Test.upperFirst ∪
    Finset.univ.image Test.upperSecond ∪
    Finset.univ.image Test.larger ∪
    Finset.univ.image Test.smallerFirst ∪
    Finset.univ.image Test.smallerSecond
  complete x := by cases x <;> simp
def test (s : ScalarCase) : Test → Expr
  | .ratioFirst i => firstE s i-ratioE s.family i*secondE s i
  | .ratioSecond i => secondE s i-ratioE s.family i*firstE s i
  | .upperFirst i => lit (cap s.family)-firstE s i
  | .upperSecond i => lit (cap s.family)-secondE s i
  | .larger i => witnessE s i-lit (largeFloor s.family)
  | .smallerFirst i => firstE s i-lit (smallFloor s.family i)
  | .smallerSecond i => secondE s i-lit (smallFloor s.family i)
  | .middleAUpper => if s.family=.middle then lit (203/250)*kE s.family-ellE s.family else 0
  | .middleALower => if s.family=.middle then ellE s.family-lit (159/250) else 0
  | .mixedB => mE s+(if s.family=.high then lit (3/100) else 0)-ellE s.family
def canonical (s : ScalarCase) : ScalarCase := {s with negative:=0,hCoefficient:=false}
def testEnclosure (s : ScalarCase) (j : Test) : Enclosure :=
  Expression.enclose («variables» (canonical s)) (test (canonical s) j)

theorem identity (f : Family) (td atG : Bool) (j : Test) :
    (testEnclosure ⟨f,td,atG,0,false⟩ j).polynomial=
      TensorWholeIntervalBernstein.expansion 16 (testEnclosure ⟨f,td,atG,0,false⟩ j).polynomial :=
  r54_expansion ((r54_enclose_bounded (r54_variables_bounded _) _).mono (by norm_num))
/-! ### The packed certificate

Each test is mirrored by an `IE` expression, evaluated by the packed Taylor models of
`ExceptionalPositiveTPolynomials`, and the kernel checks that its degree-10 Bernstein coefficients
are nonnegative, in natural-number arithmetic. -/

section packed
open PackedModels

def capI : Family → IExpr
  | .lowZero | .lowAfter => lq 21 20
  | .middle => lq 559 500
  | .high => lq 1131 1000
def largeFloorI : Family → IExpr
  | .lowZero | .lowAfter => lq 431 500
  | .middle => lq 911 1000
  | .high => .lit (.num 0)
def smallFloorI (f : Family) (i : Fin 4) : IExpr :=
  match f with
  | .middle => if i=0 ∨ i=3 then lq 911 1000 else .lit (.num 0)
  | .high => lq 731 1000
  | _ => .lit (.num 0)
def ratioI (f : Family) (i : Fin 4) : IExpr :=
  match f with
  | .lowZero | .lowAfter => if i=0 then lq 41 50
      else if i=2 then lq 117 200+lq 1 5*tI else lq 117 200
  | .middle => if i=1 then lq 31 50 else if i=2 then lq 2 3 else lq 71 100
  | .high => lq 71 100
def witnessI (f : Family) (td : Bool) (i : Fin 4) : IExpr :=
  if i=0 ∨ i=2 then secondI f td i else firstI f i
def testI (f : Family) (td : Bool) : Test → IExpr
  | .ratioFirst i => firstI f i-ratioI f i*secondI f td i
  | .ratioSecond i => secondI f td i-ratioI f i*firstI f i
  | .upperFirst i => capI f-firstI f i
  | .upperSecond i => capI f-secondI f td i
  | .larger i => witnessI f td i-largeFloorI f
  | .smallerFirst i => firstI f i-smallFloorI f i
  | .smallerSecond i => secondI f td i-smallFloorI f i
  | .middleAUpper => if f=.middle then lq 203 250*kI f-ellI f else 0
  | .middleALower => if f=.middle then ellI f-lq 159 250 else 0
  | .mixedB => mI f+(if f=.high then lq 3 100 else 0)-ellI f

theorem testI_eq (f : Family) (td atG : Bool) (j : Test) :
    (testI f td j).toExpressionWith inputFormulas=test ⟨f,td,atG,0,false⟩ j := by
  cases f <;> cases td <;> rcases j with (i|i|i|i|i|i|i|_|_|_) <;> (try fin_cases i) <;> rfl

/-- The thirty-one tests. -/
def allTests : List Test :=
  ([0,1,2,3] : List (Fin 4)).flatMap (fun i => [.ratioFirst i,.ratioSecond i,.upperFirst i,
    .upperSecond i,.larger i,.smallerFirst i,.smallerSecond i])++
    [.middleAUpper,.middleALower,.mixedB]

theorem mem_allTests (j : Test) : j∈allTests := by
  rcases j with (i|i|i|i|i|i|i|_|_|_) <;> (try fin_cases i) <;> decide

/-- The models of the inputs (the roots do not occur). -/
def testModels (f : Family) (atG : Bool) : Fin 10 ⊕ Fin 5 → Model :=
  Sum.elim (inputModels f atG) fun _ => zeroModel config

/-- Everything the kernel checks for one test. -/
def testCheck (f : Family) (td atG : Bool) (j : Test) : Bool :=
  check config 10 (testModels f atG) (testI f td j) 0 1 false && (testI f td j).poly &&
    (testI f td j).seedFree

theorem tests_check (f : Family) (td atG : Bool) : allTests.all (testCheck f td atG)=true := by
  cases f <;> cases td <;> cases atG <;> decide +kernel

theorem reserve (f : Family) (td atG : Bool) (j : Test) {X Y : ℝ} (hX : |X|≤1) (hY : |Y|≤1) :
    0≤Expression.value (inputs ⟨f,td,atG,0,false⟩ (parameterValue f X) (secondValue f X Y))
      (test ⟨f,td,atG,0,false⟩ j) := by
  have hc := List.all_eq_true.mp (tests_check f td atG) j (mem_allTests j)
  simp only [testCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨hm,hp⟩,hf⟩ := hc
  set v := inputs ⟨f,td,atG,0,false⟩ (parameterValue f X) (secondValue f X Y)
  have hw : ∀ k,(testModels f atG k).Contains config X Y ((inputFormulas k).value v) := by
    rintro (k|k)
    · exact inputModels_contain ⟨f,td,atG,0,false⟩ hX hY k
    · show (zeroModel config).Contains config X Y (Expression.value v 0)
      rw [value_zero]
      exact zeroModel_contains config X Y
  have h := check_le config_valid hm hX hY hw (IE.seedsOK_of_seedFree _ hf)
  rw [← testI_eq f td atG j,IE.value_toExpressionWith _ _ _ (IE.isPoly_of_poly _ hp)]
  simpa using h

end packed

open ExceptionalPositiveTScalar

section r54_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
@[simp] private theorem r54_value_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
@[simp] private theorem r54_value_neg : Expression.value v (-a)=-Expression.value v a := rfl
@[simp] private theorem r54_value_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
@[simp] private theorem r54_value_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
@[simp] private theorem r54_value_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
@[simp] private theorem r54_value_ite (P : Prop) [Decidable P] :
    Expression.value v (if P then a else b)=
      if P then Expression.value v a else Expression.value v b := by
  split_ifs <;> rfl
end r54_value

@[simp] private theorem r54_value_lit (w : Fin 10 → ℝ) (r : ℚ) :
    Expression.value w (lit r)=(r:ℝ) := rfl
@[simp] private theorem r54_value_var (w : Fin 10 → ℝ) (i : Fin 10) :
    Expression.value w (var i)=w i := rfl
@[simp] private theorem r54_inputs_0 (s : ScalarCase) (t z : ℝ) : inputs s t z 0=t := rfl

def ratio (f : Family) (t : ℝ) (i : Fin 4) : ℝ :=
  match f with
  | .lowZero | .lowAfter => if i=0 then 41/50
      else if i=2 then 117/200+1/5*t else 117/200
  | .middle => if i=1 then 31/50 else if i=2 then 2/3 else 71/100
  | .high => 71/100
@[simp] theorem ratioE_value (s : ScalarCase) (f : Family) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (ratioE f i)=ratio f t i := by
  cases f <;> simp [ratioE,ratio,tE]

theorem tests_nonnegative (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (j : Test) :
    0≤Expression.value (inputs s t z) (test s j) := by
  obtain ⟨X,Y,hX,hY,htX,hzY⟩ := square_coordinates s ht hz
  have h := reserve s.family s.td s.atG j hX hY
  have hinput : inputs ⟨s.family,s.td,s.atG,0,false⟩ t z=inputs s t z := rfl
  have htest : test ⟨s.family,s.td,s.atG,0,false⟩ j=test s j := by cases j <;> rfl
  rw [htX,hzY,hinput,htest] at h
  exact h

theorem ratio_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    ratio s.family t i*max (first s t z i) (second s t z i)≤
      min (first s t z i) (second s t z i) := by
  have h1 := tests_nonnegative s ht hz (.ratioFirst i)
  have h2 := tests_nonnegative s ht hz (.ratioSecond i)
  simp only [test,r54_value_sub,r54_value_mul,firstE_value,secondE_value,ratioE_value] at h1 h2
  rcases le_total (first s t z i) (second s t z i) with h | h
  · rw [max_eq_right h,min_eq_left h]
    linarith
  · rw [max_eq_left h,min_eq_right h]
    linarith
theorem pair_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    max (first s t z i) (second s t z i)≤(cap s.family:ℝ) := by
  have h1 := tests_nonnegative s ht hz (.upperFirst i)
  have h2 := tests_nonnegative s ht hz (.upperSecond i)
  simp only [test,r54_value_sub,r54_value_lit,firstE_value,secondE_value] at h1 h2
  exact max_le (by linarith) (by linarith)
theorem larger_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    (largeFloor s.family:ℝ)≤ max (first s t z i) (second s t z i) := by
  have h := tests_nonnegative s ht hz (.larger i)
  simp only [test,witnessE,r54_value_sub,r54_value_lit,r54_value_ite] at h
  split_ifs at h
  · rw [secondE_value] at h
    exact (by linarith : (largeFloor s.family:ℝ) ≤ second s t z i).trans (le_max_right _ _)
  · rw [firstE_value] at h
    exact (by linarith : (largeFloor s.family:ℝ) ≤ first s t z i).trans (le_max_left _ _)
theorem smaller_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    (smallFloor s.family i:ℝ)≤ min (first s t z i) (second s t z i) := by
  have h1 := tests_nonnegative s ht hz (.smallerFirst i)
  have h2 := tests_nonnegative s ht hz (.smallerSecond i)
  simp only [test,r54_value_sub,r54_value_lit,firstE_value,secondE_value] at h1 h2
  exact le_min (by linarith) (by linarith)
theorem scalar_B_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    max (ell s.family t z) (m s t z)≤ m s t z+(if s.family=.high then 3/100 else 0) := by
  have h := tests_nonnegative s ht hz .mixedB
  simp [test] at h
  apply max_le (by linarith)
  split_ifs <;> linarith
theorem middle_A (s : ScalarCase) {t z : ℝ} (hf : s.family=.middle)
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    (159/250:ℝ)≤ell s.family t z ∧ ell s.family t z≤(203/250)*k s.family t z := by
  have h1 := tests_nonnegative s ht hz .middleALower
  have h2 := tests_nonnegative s ht hz .middleAUpper
  simp [test,hf] at h1 h2
  rw [hf]
  exact ⟨by linarith,by linarith⟩
theorem half_ratio (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 4) :
    max (first s t z i) (second s t z i)≤2*min (first s t z i) (second s t z i) := by
  have hr := ratio_lower s ht hz i
  have hpos := (weights_positive s ht hz).2.2.2.1 i
  have hmax : 0 < max (first s t z i) (second s t z i) := hpos.trans_le (le_max_left _ _)
  have hratio : (1/2:ℝ)≤ratio s.family t i := by
    have ht0 := (angle ht).1
    cases s.family <;> dsimp [ratio] <;> first | (split_ifs <;> linarith) | linarith
  have hh := mul_le_mul_of_nonneg_right hratio hmax.le
  linarith

end SquaresInCircles.Eight.ExceptionalPositiveTCoefficients
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExceptionalPositiveTOrdinaryData
open ExceptionalPositiveTScalarModel ExceptionalPositiveTCoefficients
open PositiveAngularEnvelope OrdinaryAngleConcavity SingleAngleConcavity

def weights (s : ScalarCase) (t z : ℝ) : ExceptionalPositiveTBlocks.Weights :=
  ⟨n s t z,k s.family t z,ell s.family t z,
    if s.td then m s t z else c s.family t z,
    if s.td then c s.family t z else m s t z,p s t z⟩
def small (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  ExceptionalPositiveTBlocks.small (weights s t z) i
def large (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ℝ :=
  ExceptionalPositiveTBlocks.large (weights s t z) i
def single (s : ScalarCase) : Fin 4 → Bool := ExceptionalPositiveTBlocks.single s.td
def actualNu (s : ScalarCase) (t z : ℝ) : Fin 4 → ℝ :=
  ExceptionalPositiveTBlocks.negative (weights s t z) s.td

theorem small_eq (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i=min (first s t z i) (second s t z i) := rfl
theorem large_eq (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    large s t z i=max (first s t z i) (second s t z i) := rfl
theorem small_pos (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) : 0<small s t z i := by
  obtain ⟨_,_,_,ha,hb⟩ := weights_positive s ht hz
  exact lt_min (ha i) (hb i)
theorem small_le_large (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i≤large s t z i := min_le_max
theorem nu_between (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    small s t z i≤actualNu s t z i ∧ actualNu s t z i≤large s t z i :=
  ExceptionalPositiveTBlocks.negative_between (weights s t z) s.td i
theorem pure_eq (s : ScalarCase) (R t z u : ℝ) (i : Fin 4) :
    pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) u=
      Vnu R (small s t z i) (large s t z i) (actualNu s t z i) u :=
  ExceptionalPositiveTBlocks.pure_eq (weights s t z) s.td R u i
theorem norm_eq (s : ScalarCase) (t z u : ℝ) (i : Fin 4) :
    pairNorm (small s t z i) (large s t z i) u=pairNorm (first s t z i) (second s t z i) u :=
  ExceptionalPositiveTBlocks.norm_eq (weights s t z) u i

theorem middle_A_data (s : ScalarCase) {t z : ℝ} (hf : s.family=.middle)
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) :
    small s t z 1=ell s.family t z ∧ large s t z 1=k s.family t z ∧
    actualNu s t z 1=ell s.family t z ∧
    ell s.family t z/k s.family t z∈Icc (31/50:ℝ) (203/250) := by
  have hk := (coefficient_positive ht hz).1
  have hdata := middle_A s hf ht hz
  have horder : ell s.family t z≤k s.family t z := by nlinarith
  have hr := ratio_lower s ht hz 1
  have hs : small s t z 1=ell s.family t z := by
    simp [small_eq,first,second,min_eq_right horder]
  have hl : large s t z 1=k s.family t z := by
    simp [large_eq,first,second,max_eq_left horder]
  have hr' : (31/50)*k s.family t z≤ell s.family t z := by
    have e1 : first s t z 1=k s.family t z := rfl
    have e2 : second s t z 1=ell s.family t z := rfl
    have e3 : ratio s.family t 1=31/50 := by rw [hf]; simp [ratio]
    rw [e1,e2,e3,max_eq_left horder,min_eq_right horder] at hr
    exact hr
  refine ⟨hs,hl,rfl,?_,?_⟩
  · exact (le_div_iff₀ hk).2 hr'
  · exact (div_le_iff₀ hk).2 hdata.2

def baseline (s : ScalarCase) (R t z : ℝ) : ℝ :=
  k s.family t z*ExceptionalContactSupport.contactScalar R (eta s.family t) (x s t z)+
    c s.family t z*ExceptionalContactSupport.contactScalar R (eta s.family t) z+
    2*ell s.family t z+ExceptionalContactSupport.contactScalar R (eta s.family t) (ExceptionalPositiveTScalarModel.e s t z)-
      R*∑i,pairNorm (first s t z i) (second s t z i) 0

def chooseH (s : ScalarCase) (t z : ℝ) : Bool := by
  classical
  exact decide (n s t z≤p s t z)
def charged (s : ScalarCase) (t z : ℝ) (i : Fin 4) : ScalarCase :=
  {s with negative:=i,hCoefficient:=chooseH s t z}

theorem scalar_identity (s : ScalarCase) (R t z : ℝ) (i : Fin 4) (h : Bool) :
    value {s with negative:=i,hCoefficient:=h} R t z=baseline s R t z+
      Vnu R (small s t z i) (large s t z i)
        (nu {s with negative:=i,hCoefficient:=h} t z) t := by
  rw [Vnu,norm_eq,norm_eq]
  fin_cases i <;>
    simp [value,baseline,square,nu,first,second,x,ExceptionalPositiveTScalarModel.e,n,m,p,pairNorm,
      Fin.sum_univ_succ,Real.sin_neg] <;> ring

theorem scalar_nu_upper (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    actualNu s t z i≤nu (charged s t z i) t z := by
  have hB := scalar_B_upper s ht hz
  fin_cases i
  · by_cases h : n s t z≤p s t z
    · simp [actualNu,ExceptionalPositiveTBlocks.negative,weights,nu,charged,chooseH,h]
      exact le_rfl
    · have hp : p s t z≤n s t z := (lt_of_not_ge h).le
      simp [actualNu,ExceptionalPositiveTBlocks.negative,weights,nu,charged,chooseH,h,
        max_eq_right hp]
      exact le_rfl
  · rfl
  · cases htd : s.td
    · simp [actualNu,ExceptionalPositiveTBlocks.negative,weights,nu,charged,htd]
    · simpa [actualNu,ExceptionalPositiveTBlocks.negative,weights,nu,charged,htd,m] using hB
  · rfl

theorem pure_scalar_lower (s : ScalarCase) {R t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Icc 0 t) (i : Fin 4) :
    value (charged s t z i) R t z≤baseline s R t z+
      pure (single s i) R (small s t z i) (large s t z i) (actualNu s t z i) t := by
  rw [charged,scalar_identity,pure_eq]
  have hh := mul_le_mul_of_nonpos_right (scalar_nu_upper s ht hz i)
    (show Real.cos t-1≤0 by linarith [Real.cos_le_one t])
  rw [charged] at hh
  dsimp [Vnu]
  linarith

end SquaresInCircles.Eight.ExceptionalPositiveTOrdinaryData
end
end
end
