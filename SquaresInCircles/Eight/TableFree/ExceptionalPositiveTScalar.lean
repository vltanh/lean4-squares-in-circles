module

public import SquaresInCircles.Eight.TableFree.ExceptionalPositiveTPolynomials

/-!
# Radical transfer for the four positive-T contact families

Uncompiled source. The complete polynomial lower bound transfers to
the original radical expression because every majorized root occurs
with a nonpositive coefficient. Radius monotonicity then restores the
actual common ceiling, without changing any original point or axis.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalPositiveTScalar
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
  cases f <;> norm_num [KE,K,tE,inputs,Expression.value] <;> ring
@[simp] theorem LE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (LE f)=L f t := by
  cases f <;> norm_num [ExceptionalPositiveTPolynomials.LE,L,tE,inputs,Expression.value] <;> ring
@[simp] theorem CE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (CE f)=C f t := by
  cases f <;> norm_num [CE,C,tE,inputs,Expression.value] <;> ring
@[simp] theorem etaE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (etaE f)=eta f t := by
  cases f <;> norm_num [etaE,eta,tE,inputs,Expression.value] <;> ring
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
  fin_cases i <;> simp [firstE,first,Expression.value]
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

end SquaresInCircles.Eight.TableFree.ExceptionalPositiveTScalar
