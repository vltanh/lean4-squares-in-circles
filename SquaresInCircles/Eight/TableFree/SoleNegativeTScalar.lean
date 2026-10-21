module

public import SquaresInCircles.Eight.TableFree.SoleNegativeTPolynomials

/-!
# Strict negative-T endpoint scalars at the actual common radius

Uncompiled source. Every radical majorant is global and every discarded
polynomial coefficient is retained in the enclosure error. The full
intrinsic intervals, including both endpoints, are mapped to the complete
parameter square. No negative-T geometry is inferred from this scalar layer.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleNegativeTScalar
open SoleTScalarModel SolePositiveTPolynomials SoleNegativeTScalarModel
open SoleNegativeTPolynomials TensorPolynomialEnclosure

@[simp] theorem kE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (kE f)=k f t 0 := by
  cases f <;> norm_num [kE,k,KE,K,tE,zE,inputs,Expression.value] <;> ring
@[simp] theorem ellE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (ellE f)=ell f t 0 := by
  cases f <;> norm_num [ellE,ell,LE,L,tE,zE,inputs,Expression.value] <;> ring
@[simp] theorem cE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (cE f)=c f t 0 := by
  cases f <;> norm_num [cE,c,CE,C,KE,K,tE,zE,inputs,Expression.value] <;> ring
@[simp] theorem gE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (gE f)=g f t := by
  cases f <;> norm_num [gE,g,tE,inputs,Expression.value]
@[simp] theorem epsilonE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (epsilonE f)=epsilon f t := by
  cases f <;> norm_num [epsilonE,epsilon,tE,inputs,Expression.value] <;> ring
@[simp] theorem etaE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) etaE=eta t := by simp [etaE,eta,tE,inputs,Expression.value]
@[simp] theorem lambdaE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (lambdaE f)=lambda f := by simp [lambdaE,lambda,Expression.value]
@[simp] theorem nE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (nE (scalar s))=n (scalar s) t 0 := by
  simp [nE,n,Expression.value,cx,sx,inputs,scalar]
@[simp] theorem mE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (mE (scalar s))=m (scalar s) t 0 := by
  simp [mE,m,Expression.value,cz,sz,inputs,scalar]
@[simp] theorem pE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (pE (scalar s))=p (scalar s) t 0 := by
  simp [pE,p,Expression.value,ce,se,inputs,scalar]
@[simp] theorem firstE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (firstE (scalar s) i)=first (scalar s) t 0 i := by
  fin_cases i <;> simp [firstE,first,scalar]
@[simp] theorem secondE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (secondE (scalar s) i)=second (scalar s) t 0 i := by
  fin_cases i <;> simp [secondE,second,scalar]
@[simp] theorem nuE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (nuE (scalar s))=nu (scalar s) t 0 := by
  have hi : index s.row∈(Finset.univ : Finset (Fin 4)) := Finset.mem_univ _
  generalize he : index s.row=i
  fin_cases i <;> simp [nuE,nu,scalar,he,Expression.value]
@[simp] theorem squareE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (squareE (scalar s) i)=SoleNegativeTScalarModel.square s t i := by
  simp [squareE,SoleNegativeTScalarModel.square,Expression.value,st,inputs,scalar]
@[simp] theorem correctionE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (correctionE s)=correction s t := by
  simp [correctionE,correction,Expression.value]
@[simp] theorem removedE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (removedE s)=removed s.row t := by
  simp [removedE,removed,Expression.value,tE,inputs]
@[simp] theorem coefficientE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (coefficientE s)=coefficient s t := by
  simp [coefficientE,coefficient,Expression.value]

def rootArgument (s : Case) (t : ℝ) (i : Fin 7) : ℝ :=
  if hi : i.val<4 then SoleNegativeTScalarModel.square s t ⟨i.val,hi⟩
  else if i.val=4 then 1+(g (family s.row) t)^2
  else if i.val=5 then 1+(eta t)^2 else 1+(epsilon (family s.row) t)^2

@[simp] theorem rootSquare_value (s : Case) (t : ℝ) (i : Fin 7) :
    Expression.value (inputs s t) (rootSquare (scalar s) i)=rootArgument s t i := by
  dsimp [rootSquare,rootArgument]
  split_ifs <;> simp [Expression.value,scalar]

def upper (s : Case) (t : ℝ) (i : Fin 7) : ℝ :=
  Expression.value (inputs s t) (SoleNegativeTPolynomials.rootExpression s i)

theorem root_lower (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) (i : Fin 7) :
    Real.sqrt (rootArgument s t i)≤upper s t i := by
  have hnon : 0≤rootArgument s t i := by
    dsimp [rootArgument]
    split_ifs
    · exact SoleNegativeTScalarModel.square_nonneg s ht _
    all_goals positivity
  have hh := Expression.sqrt_le_value (inputs s t) (variables s) (rootSquare (scalar s) i)
    (by simpa using hnon) (seeds_positive s i)
  simpa only [rootSquare_value,upper,SoleNegativeTPolynomials.rootExpression] using hh

def upperETerm (s : Case) (t : ℝ) : ℝ :=
  if tiltedE (family s.row) then
    1+2*Real.cos (e (scalar s) t 0)+(1+2*epsilon (family s.row) t)*Real.sin (e (scalar s) t 0)-
      (radiusUpper:ℝ)*Real.sin (e (scalar s) t 0)*upper s t 6
  else if isDE (family s.row) then
    1+Real.cos (e (scalar s) t 0)/2+(1-(axisUpper:ℝ))*Real.sin (e (scalar s) t 0)+3/2*(5/4)
  else 3+Real.sin (e (scalar s) t 0)-2*(radiusUpper:ℝ)*Real.sin (e (scalar s) t 0/2)

theorem expression_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (expression s)=
      k (family s.row) t 0*(1+2*Real.cos (x (scalar s) t 0)+
        (1+2*g (family s.row) t)*Real.sin (x (scalar s) t 0))+
      3*c (family s.row) t 0+2*ell (family s.row) t 0-
        (radiusUpper:ℝ)*k (family s.row) t 0*Real.sin (x (scalar s) t 0)*upper s t 4+
      upperETerm s t+correction s t+(21/20)*c (family s.row) t 0*removed s.row t+
        coefficient s t*(Real.cos (SoleNegativeTScalarModel.angle s.row t)-1)-
          (radiusUpper:ℝ)*(upper s t 0+upper s t 1+upper s t 2+upper s t 3) := by
  simp [expression,baseExpression,eExpression,upperETerm,upper,Expression.value,
    cx,sx,ce,se,ct,shalf,inputs]
  split_ifs <;> ring

theorem model_le_actual (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    Expression.value (inputs s t) (expression s)≤
      SoleNegativeTScalarModel.value s (radiusUpper:ℝ) (axisUpper:ℝ) t := by
  have hf := family_mem ht
  have hz : (0:ℝ)∈Set.Icc 0 t := ⟨le_rfl,(angles ht).1.1⟩
  have hk := (coefficient_positive hf hz).1
  have hx := (split_angles (scalar s) hf hz).2.1
  have he := (split_angles (scalar s) hf hz).2.2
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hG := root_lower s ht 4
  have hE := root_lower s ht 6
  norm_num [rootArgument] at hG hE
  have hGp := mul_le_mul_of_nonneg_left hG
    (mul_nonneg (mul_nonneg hR hk.le) (transport_trig hx).2.2.1)
  have hEp := mul_le_mul_of_nonneg_left hE
    (mul_nonneg hR (transport_trig he).2.2.1)
  have hanchor (i : Fin 4) : Real.sqrt (SoleNegativeTScalarModel.square s t i)≤
      upper s t ⟨i.val,by omega⟩ := by
    simpa [rootArgument,i.isLt] using root_lower s ht ⟨i.val,by omega⟩
  have hsum := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hanchor i)) hR
  rw [expression_value]
  dsimp [SoleNegativeTScalarModel.value,upperETerm,eTerm,primaryCoefficient,scalar]
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ] at hsum ⊢
  split_ifs <;> nlinarith

theorem parameter_surjective (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    ∃ X : ℝ,|X|≤1 ∧ parameterValue s.row X=t := by
  let a : ℝ := (SoleNegativeTScalarModel.left s.row:ℝ)
  let b : ℝ := (SoleNegativeTScalarModel.right s.row:ℝ)
  have hab : a<b := by exact_mod_cast (SoleNegativeTScalarModel.interval_order s.row).2.1
  have hgap : 0<b-a := by linarith
  let X : ℝ := (2*t-a-b)/(b-a)
  have hX : |X|≤1 := by
    apply abs_le.mpr
    dsimp [X]
    constructor
    · apply (le_div_iff₀ hgap).2
      linarith [ht.1]
    · apply (div_le_iff₀ hgap).2
      linarith [ht.2]
  refine ⟨X,hX,?_⟩
  change (a+b)/2+(b-a)/2*((2*t-a-b)/(b-a))=t
  field_simp [hgap.ne']
  ring

theorem conservative_positive (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    0<SoleNegativeTScalarModel.value s (radiusUpper:ℝ) (axisUpper:ℝ) t := by
  obtain ⟨X,hX,hXt⟩ := parameter_surjective s ht
  have hh := model_positive s hX (show |(0:ℝ)|≤1 by norm_num)
  rw [hXt] at hh
  exact hh.trans_le (model_le_actual s ht)

theorem antitone_parameters (s : Case) {t R R' M M' : ℝ}
    (ht : t∈SoleNegativeTScalarModel.domain s.row) (hR : R≤R') (hM : M≤M') :
    SoleNegativeTScalarModel.value s R' M' t≤SoleNegativeTScalarModel.value s R M t := by
  have hf := family_mem ht
  have hz : (0:ℝ)∈Set.Icc 0 t := ⟨le_rfl,(angles ht).1.1⟩
  have hk := (coefficient_positive hf hz).1
  have hx := (split_angles (scalar s) hf hz).2.1
  have he := (split_angles (scalar s) hf hz).2.2
  have hhalf : e (scalar s) t 0/2∈Set.Icc 0 frameCap :=
    ⟨by linarith [he.1],by linarith [he.1,he.2]⟩
  have hG := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (mul_nonneg hk.le (transport_trig hx).2.2.1)
      (Real.sqrt_nonneg (1+(g (family s.row) t)^2)))
  have hE := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (transport_trig he).2.2.1 (Real.sqrt_nonneg (1+(epsilon (family s.row) t)^2)))
  have hhalf' := mul_nonneg (sub_nonneg.mpr hR) (transport_trig hhalf).2.2.1
  have haxis := mul_nonneg (sub_nonneg.mpr hM) (transport_trig he).2.2.1
  have hsum : 0≤∑i : Fin 4,Real.sqrt (SoleNegativeTScalarModel.square s t i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hnorm := mul_nonneg (sub_nonneg.mpr hR) hsum
  dsimp [SoleNegativeTScalarModel.value,eTerm,primaryCoefficient,scalar]
  split_ifs <;> nlinarith

theorem actual_radius_positive (s : Case) {q t : ℝ}
    (hq : q≤qTrial) (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    0<SoleNegativeTScalarModel.value s (Real.sqrt q) (Real.sqrt (q-1/4)) t := by
  have hR := (Real.sqrt_le_sqrt hq).trans SoleTScalarModel.radius_upper.le
  have hM := (Real.sqrt_le_sqrt (sub_le_sub_right hq (1/4))).trans SoleTScalarModel.axis_upper.le
  exact (conservative_positive s ht).trans_le (antitone_parameters s ht hR hM)

end SquaresInCircles.Eight.TableFree.SoleNegativeTScalar
