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

section r64_value
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
@[simp] private theorem r64_value_add :
    Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
@[simp] private theorem r64_value_neg : Expression.value v (-a)=-Expression.value v a := rfl
@[simp] private theorem r64_value_sub :
    Expression.value v (a-b)=Expression.value v a-Expression.value v b := by
  show Expression.value v a+-Expression.value v b=_
  ring
@[simp] private theorem r64_value_mul :
    Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
@[simp] private theorem r64_value_pow (n : ℕ) :
    Expression.value v (a^n)=Expression.value v a^n := rfl
@[simp] private theorem r64_value_one : Expression.value v (1 : Expression ι)=1 := by
  show (((1:ℕ):ℚ):ℝ)=1
  norm_num
@[simp] private theorem r64_value_two : Expression.value v (2 : Expression ι)=2 := by
  show (((2:ℕ):ℚ):ℝ)=2
  norm_num
@[simp] private theorem r64_value_three : Expression.value v (3 : Expression ι)=3 := by
  show (((3:ℕ):ℚ):ℝ)=3
  norm_num
@[simp] private theorem r64_value_zero : Expression.value v (0 : Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  norm_num
@[simp] private theorem r64_value_ite (P : Prop) [Decidable P] :
    Expression.value v (if P then a else b)=
      if P then Expression.value v a else Expression.value v b := by
  split_ifs <;> rfl
end r64_value

@[simp] private theorem r64_value_lit (w : Fin 11 → ℝ) (r : ℚ) :
    Expression.value w (lit r)=(r:ℝ) := rfl
@[simp] private theorem r64_value_var (w : Fin 11 → ℝ) (i : Fin 11) :
    Expression.value w (var i)=w i := rfl
section r64_inputs
variable (s : Case) (t : ℝ)
@[simp] private theorem r64_inputs_0 : SoleNegativeTPolynomials.inputs s t 0=t := rfl
@[simp] private theorem r64_inputs_1 : SoleNegativeTPolynomials.inputs s t 1=0 := rfl
@[simp] private theorem r64_inputs_2 :
    SoleNegativeTPolynomials.inputs s t 2=Real.sin (x (scalar s) t 0) := rfl
@[simp] private theorem r64_inputs_3 :
    SoleNegativeTPolynomials.inputs s t 3=Real.cos (x (scalar s) t 0) := rfl
@[simp] private theorem r64_inputs_4 : SoleNegativeTPolynomials.inputs s t 4=0 := rfl
@[simp] private theorem r64_inputs_5 : SoleNegativeTPolynomials.inputs s t 5=1 := rfl
@[simp] private theorem r64_inputs_6 :
    SoleNegativeTPolynomials.inputs s t 6=Real.sin (SoleTScalarModel.e (scalar s) t 0) := rfl
@[simp] private theorem r64_inputs_7 :
    SoleNegativeTPolynomials.inputs s t 7=Real.cos (SoleTScalarModel.e (scalar s) t 0) := rfl
@[simp] private theorem r64_inputs_8 :
    SoleNegativeTPolynomials.inputs s t 8=Real.sin (SoleNegativeTScalarModel.angle s.row t) := rfl
@[simp] private theorem r64_inputs_9 :
    SoleNegativeTPolynomials.inputs s t 9=Real.cos (SoleNegativeTScalarModel.angle s.row t) := rfl
@[simp] private theorem r64_inputs_10 :
    SoleNegativeTPolynomials.inputs s t 10=Real.sin (SoleTScalarModel.e (scalar s) t 0/2) := rfl
end r64_inputs
@[simp] private theorem r64_scalar_family (s : Case) : (scalar s).family=family s.row := rfl
@[simp] private theorem r64_scalar_td (s : Case) : (scalar s).td=true := rfl
@[simp] private theorem r64_scalar_atG (s : Case) : (scalar s).atG=s.atG := rfl
@[simp] private theorem r64_scalar_negative (s : Case) : (scalar s).negative=index s.row := rfl

@[simp] theorem kE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (kE f)=k f t 0 := by
  cases f <;> norm_num [kE,k,KE,K,tE,zE]
@[simp] theorem ellE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (ellE f)=ell f t 0 := by
  cases f <;> norm_num [ellE,ell,SolePositiveTPolynomials.LE,L,tE,zE]
@[simp] theorem cE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (cE f)=c f t 0 := by
  cases f <;> norm_num [cE,c,CE,SoleTScalarModel.C,KE,K,tE,zE]
@[simp] theorem gE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (gE f)=g f t := by
  cases f <;> norm_num [gE,g,tE]
@[simp] theorem epsilonE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (epsilonE f)=epsilon f t := by
  cases f <;> norm_num [epsilonE,epsilon,tE]
@[simp] theorem etaE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) etaE=eta t := by
  norm_num [etaE,eta,tE]
@[simp] theorem lambdaE_value (s : Case) (f : Family) (t : ℝ) :
    Expression.value (inputs s t) (lambdaE f)=lambda f := by
  unfold lambdaE lambda
  split_ifs <;> norm_num
@[simp] theorem nE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (nE (scalar s))=n (scalar s) t 0 := by
  simp [nE,n,cx,sx]
@[simp] theorem mE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (mE (scalar s))=m (scalar s) t 0 := by
  simp [mE,m,cz,sz]
@[simp] theorem pE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (pE (scalar s))=p (scalar s) t 0 := by
  unfold pE p
  split_ifs <;> simp [ce,se]
@[simp] theorem firstE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (firstE (scalar s) i)=first (scalar s) t 0 i := by
  fin_cases i <;> simp [firstE,first]
@[simp] theorem secondE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (secondE (scalar s) i)=second (scalar s) t 0 i := by
  fin_cases i <;> simp [secondE,second]
@[simp] theorem nuE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (nuE (scalar s))=nu (scalar s) t 0 := by
  unfold nuE nu
  generalize (scalar s).negative=j
  fin_cases j <;> simp
  split_ifs <;> norm_num
@[simp] theorem squareE_value (s : Case) (t : ℝ) (i : Fin 4) :
    Expression.value (inputs s t) (squareE (scalar s) i)=SoleNegativeTScalarModel.square s t i := by
  unfold squareE SoleNegativeTScalarModel.square
  simp only [r64_value_sub,r64_value_add,r64_value_pow,firstE_value,secondE_value]
  split_ifs <;> simp_all [st]
@[simp] theorem correctionE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (correctionE s)=correction s t := by
  unfold correctionE correction
  split_ifs <;> simp
@[simp] theorem removedE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (removedE s)=removed s.row t := by
  unfold removedE removed
  split_ifs <;> norm_num [tE]
@[simp] theorem coefficientE_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (coefficientE s)=coefficient s t := by
  unfold coefficientE coefficient
  split_ifs <;> simp

def rootArgument (s : Case) (t : ℝ) (i : Fin 7) : ℝ :=
  if hi : i.val<4 then SoleNegativeTScalarModel.square s t ⟨i.val,hi⟩
  else if i.val=4 then 1+(g (family s.row) t)^2
  else if i.val=5 then 1+(eta t)^2 else 1+(epsilon (family s.row) t)^2

@[simp] theorem rootSquare_value (s : Case) (t : ℝ) (i : Fin 7) :
    Expression.value (inputs s t) (rootSquare (scalar s) i)=rootArgument s t i := by
  unfold rootSquare rootArgument
  split_ifs <;> simp

def upper (s : Case) (t : ℝ) (i : Fin 7) : ℝ :=
  Expression.value (inputs s t) (SoleNegativeTPolynomials.rootExpression s i)

theorem root_lower (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) (i : Fin 7) :
    Real.sqrt (rootArgument s t i)≤upper s t i := by
  have hnon : 0≤rootArgument s t i := by
    dsimp [rootArgument]
    split_ifs
    · exact SoleNegativeTScalarModel.square_nonneg s ht _
    all_goals positivity
  have hh := Expression.sqrt_le_value (inputs s t) («variables» s) (rootSquare (scalar s) i)
    (by simpa using hnon) (seeds_positive s i)
  simpa only [rootSquare_value,upper,SoleNegativeTPolynomials.rootExpression] using hh

def upperETerm (s : Case) (t : ℝ) : ℝ :=
  if tiltedE (family s.row) then
    1+2*Real.cos (SoleTScalarModel.e (scalar s) t 0)+(1+2*epsilon (family s.row) t)*Real.sin (SoleTScalarModel.e (scalar s) t 0)-
      (radiusUpper:ℝ)*Real.sin (SoleTScalarModel.e (scalar s) t 0)*upper s t 6
  else if isDE (family s.row) then
    1+Real.cos (SoleTScalarModel.e (scalar s) t 0)/2+(1-(axisUpper:ℝ))*Real.sin (SoleTScalarModel.e (scalar s) t 0)+3/2*(5/4)
  else 3+Real.sin (SoleTScalarModel.e (scalar s) t 0)-2*(radiusUpper:ℝ)*Real.sin (SoleTScalarModel.e (scalar s) t 0/2)

theorem expression_value (s : Case) (t : ℝ) :
    Expression.value (inputs s t) (expression s)=
      k (family s.row) t 0*(1+2*Real.cos (x (scalar s) t 0)+
        (1+2*g (family s.row) t)*Real.sin (x (scalar s) t 0))+
      3*c (family s.row) t 0+2*ell (family s.row) t 0-
        (radiusUpper:ℝ)*k (family s.row) t 0*Real.sin (x (scalar s) t 0)*upper s t 4+
      upperETerm s t+correction s t+(21/20)*c (family s.row) t 0*removed s.row t+
        coefficient s t*(Real.cos (SoleNegativeTScalarModel.angle s.row t)-1)-
          (radiusUpper:ℝ)*(upper s t 0+upper s t 1+upper s t 2+upper s t 3) := by
  have hU : ∀ i,Expression.value (inputs s t) (SoleNegativeTPolynomials.rootExpression s i)=
      upper s t i := fun _ => rfl
  unfold SoleNegativeTPolynomials.expression SoleNegativeTPolynomials.baseExpression
    SoleNegativeTPolynomials.eExpression upperETerm
  split_ifs <;>
  simp only [hU,r64_value_sub,r64_value_add,r64_value_mul,
    r64_value_one,r64_value_two,r64_value_three,r64_value_lit,r64_value_var,cx,sx,ce,se,ct,shalf,
    r64_inputs_2,r64_inputs_3,r64_inputs_6,r64_inputs_7,r64_inputs_9,r64_inputs_10,kE_value,
    gE_value,cE_value,ellE_value,epsilonE_value,correctionE_value,removedE_value,
    coefficientE_value] <;> push_cast <;> ring

theorem model_le_actual (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    Expression.value (inputs s t) (expression s)≤
      SoleNegativeTScalarModel.value s (radiusUpper:ℝ) (axisUpper:ℝ) t := by
  have hf := family_mem ht
  have hz : (0:ℝ)∈Set.Icc 0 t := ⟨le_rfl,(angles ht).1.1⟩
  have hk := (coefficient_positive hf hz).1
  have hx := (split_angles (scalar s) hf hz).2.1
  have he := (split_angles (scalar s) hf hz).2.2
  have hR : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hG : Real.sqrt (1+(g (family s.row) t)^2)≤upper s t 4 := by
    simpa [rootArgument] using root_lower s ht 4
  have hE : Real.sqrt (1+(epsilon (family s.row) t)^2)≤upper s t 6 := by
    simpa [rootArgument] using root_lower s ht 6
  have hGp := mul_le_mul_of_nonneg_left hG
    (mul_nonneg (mul_nonneg hR hk.le) (transport_trig hx).2.2.1)
  have hEp := mul_le_mul_of_nonneg_left hE (mul_nonneg hR (transport_trig he).2.2.1)
  have h0 : Real.sqrt (SoleNegativeTScalarModel.square s t 0)≤upper s t 0 := by
    simpa [rootArgument] using root_lower s ht 0
  have h1 : Real.sqrt (SoleNegativeTScalarModel.square s t 1)≤upper s t 1 := by
    simpa [rootArgument] using root_lower s ht 1
  have h2 : Real.sqrt (SoleNegativeTScalarModel.square s t 2)≤upper s t 2 := by
    simpa [rootArgument] using root_lower s ht 2
  have h3 : Real.sqrt (SoleNegativeTScalarModel.square s t 3)≤upper s t 3 := by
    simpa [rootArgument] using root_lower s ht 3
  have hsum := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) hR
  rw [expression_value]
  simp only [SoleNegativeTScalarModel.value,upperETerm,eTerm,primaryCoefficient,
    Fin.sum_univ_four,r64_scalar_family]
  by_cases hT : tiltedE (family s.row)=true <;> by_cases hD : isDE (family s.row)=true <;>
    simp only [hT,hD,Bool.false_eq_true,↓reduceIte] <;> linarith

theorem parameter_surjective (s : Case) {t : ℝ} (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    ∃ X : ℝ,|X|≤1 ∧ parameterValue s.row X=t := by
  obtain ⟨a,ha⟩ : ∃ a : ℝ,a=(SoleNegativeTScalarModel.left s.row:ℝ) := ⟨_,rfl⟩
  obtain ⟨b,hb⟩ : ∃ b : ℝ,b=(SoleNegativeTScalarModel.right s.row:ℝ) := ⟨_,rfl⟩
  have hab : a<b := by
    rw [ha,hb]
    exact_mod_cast (SoleNegativeTScalarModel.interval_order s.row).2.1
  have hgap : 0<b-a := by linarith
  have ht' : a≤t ∧ t≤b := by
    rw [ha,hb]
    exact ht
  refine ⟨(2*t-a-b)/(b-a),?_,?_⟩
  · apply abs_le.mpr
    constructor
    · rw [le_div_iff₀ hgap]
      linarith [ht'.1]
    · rw [div_le_iff₀ hgap]
      linarith [ht'.2]
  · rw [SoleNegativeTPolynomials.parameterValue,← ha,← hb]
    field_simp
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
  have hhalf : SoleTScalarModel.e (scalar s) t 0/2∈Set.Icc 0 frameCap := by
    have he' := he
    simp only [frameCap,Set.mem_Icc] at he' ⊢
    constructor <;> linarith [he'.1,he'.2]
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
  simp only [SoleNegativeTScalarModel.value,eTerm,primaryCoefficient,r64_scalar_family]
  by_cases hT : tiltedE (family s.row)=true <;> by_cases hD : isDE (family s.row)=true <;>
    simp only [hT,hD,Bool.false_eq_true,↓reduceIte] <;> nlinarith

theorem actual_radius_positive (s : Case) {q t : ℝ}
    (hq : q≤qTrial) (ht : t∈SoleNegativeTScalarModel.domain s.row) :
    0<SoleNegativeTScalarModel.value s (Real.sqrt q) (Real.sqrt (q-1/4)) t := by
  have hR := (Real.sqrt_le_sqrt hq).trans SoleTScalarModel.radius_upper.le
  have hM := (Real.sqrt_le_sqrt (sub_le_sub_right hq (1/4))).trans SoleTScalarModel.axis_upper.le
  exact (conservative_positive s ht).trans_le (antitone_parameters s ht hR hM)

end SquaresInCircles.Eight.TableFree.SoleNegativeTScalar
