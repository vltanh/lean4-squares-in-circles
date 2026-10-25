module

public import SquaresInCircles.Eight.Owners.Sole.PositiveTPolynomials

/-!
# Eight squares: actual radical scalar inequalities for a positive T primary

The rational polynomial encloses a global upper
majorant for each radical. Every radical has a nonpositive coefficient,
so the polynomial lower bound transfers to the original scalar. The
last theorem uses the actual radius and its actual axis coordinate.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SolePositiveTScalar
open SoleTScalarModel SolePositiveTPolynomials TensorPolynomialEnclosure

section r65_helpers
variable {ι : Type*} (v : ι → ℝ) (a b : Expression ι)
private theorem r65_add : Expression.value v (a+b)=Expression.value v a+Expression.value v b := rfl
private theorem r65_sub : Expression.value v (a-b)=Expression.value v a-Expression.value v b :=
  (sub_eq_add_neg _ _).symm
private theorem r65_mul : Expression.value v (a*b)=Expression.value v a*Expression.value v b := rfl
private theorem r65_pow (n : ℕ) : Expression.value v (a^n)=Expression.value v a^n := rfl
private theorem r65_lit (r : ℚ) : Expression.value v (.literal r)=(r:ℝ) := rfl
private theorem r65_var (i : ι) : Expression.value v (.variable i)=v i := rfl
private theorem r65_zero : Expression.value v (0:Expression ι)=0 := by
  show (((0:ℕ):ℚ):ℝ)=0
  simp
private theorem r65_one : Expression.value v (1:Expression ι)=1 := by
  show (((1:ℕ):ℚ):ℝ)=1
  simp
private theorem r65_two : Expression.value v (2:Expression ι)=2 := by
  show (((2:ℕ):ℚ):ℝ)=2
  norm_num
private theorem r65_three : Expression.value v (3:Expression ι)=3 := by
  show (((3:ℕ):ℚ):ℝ)=3
  norm_num
private theorem r65_ite (c : Prop) [Decidable c] :
    Expression.value v (if c then a else b)=
      if c then Expression.value v a else Expression.value v b := by
  split_ifs <;> rfl
end r65_helpers

section r65_inputs
variable (s : ScalarCase) (t z : ℝ)
private theorem r65_in0 : inputs s t z 0=t := rfl
private theorem r65_in1 : inputs s t z 1=z := rfl
private theorem r65_in2 : inputs s t z 2=Real.sin (x s t z) := rfl
private theorem r65_in3 : inputs s t z 3=Real.cos (x s t z) := rfl
private theorem r65_in4 : inputs s t z 4=Real.sin z := rfl
private theorem r65_in5 : inputs s t z 5=Real.cos z := rfl
private theorem r65_in6 : inputs s t z 6=Real.sin (SoleTScalarModel.e s t z) := rfl
private theorem r65_in7 : inputs s t z 7=Real.cos (SoleTScalarModel.e s t z) := rfl
private theorem r65_in8 : inputs s t z 8=Real.sin t := rfl
private theorem r65_in9 : inputs s t z 9=Real.cos t := rfl
private theorem r65_in10 : inputs s t z 10=Real.sin (SoleTScalarModel.e s t z/2) := rfl
end r65_inputs

@[simp] theorem KE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (KE f)=K f t := by
  cases f <;>
    simp only [KE,K,tE,r65_add,r65_sub,r65_mul,r65_pow,r65_lit,r65_var,lit,var,r65_in0] <;>
    push_cast <;> ring

@[simp] theorem LE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (LE f)=L f t := by
  cases f <;>
    simp only [SolePositiveTPolynomials.LE,L,tE,r65_add,r65_sub,r65_mul,r65_pow,r65_lit,
      r65_var,lit,var,r65_in0] <;>
    push_cast <;> ring

@[simp] theorem CE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (CE f)=C f t := by
  cases f <;>
    simp only [CE,C,KE,K,tE,r65_add,r65_sub,r65_mul,r65_pow,r65_lit,r65_var,lit,var,
      r65_in0] <;>
    push_cast <;> ring

@[simp] theorem gE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (gE f)=g f t := by
  cases f <;> norm_num [gE,g,tE,inputs,Expression.value]

@[simp] theorem epsilonE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (epsilonE f)=epsilon f t := by
  cases f <;>
    simp only [epsilonE,epsilon,tE,r65_add,r65_sub,r65_mul,r65_pow,r65_lit,r65_var,
      r65_zero,lit,var,r65_in0] <;>
    push_cast <;> ring

@[simp] theorem kE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (kE f)=k f t z := by
  simp only [kE,k,zE,KE_value,r65_add,r65_mul,r65_lit,r65_var,lit,var,r65_in1]
  push_cast
  ring

@[simp] theorem ellE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (ellE f)=ell f t z := by
  simp only [ellE,ell,zE,LE_value,r65_sub,r65_mul,r65_lit,r65_var,lit,var,r65_in1]
  push_cast
  ring

@[simp] theorem cE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (cE f)=c f t z := by
  simp only [cE,c,zE,CE_value,r65_sub,r65_mul,r65_lit,r65_var,lit,var,r65_in1]
  push_cast
  ring

@[simp] theorem etaE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) etaE=eta t := by
  simp [etaE,eta,Expression.value,tE,inputs]

@[simp] theorem lambdaE_value (s : ScalarCase) (f : Family) (t z : ℝ) :
    Expression.value (inputs s t z) (lambdaE f)=lambda f := by
  simp only [lambdaE,lambda,r65_lit,r65_one,r65_ite,lit]
  split_ifs <;> norm_num

@[simp] theorem nE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (nE s)=n s t z := by
  simp only [nE,n,cx,sx,kE_value,gE_value,r65_add,r65_mul,r65_var,var,r65_in2,r65_in3]

@[simp] theorem mE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (mE s)=m s t z := by
  simp only [mE,m,cz,sz,cE_value,etaE_value,r65_add,r65_mul,r65_var,var,r65_in4,r65_in5]

@[simp] theorem pE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (pE s)=p s t z := by
  simp only [pE,p,ce,se,epsilonE_value,r65_add,r65_mul,r65_var,r65_one,r65_ite,var,
    r65_in6,r65_in7]

@[simp] theorem firstE_value (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (firstE s i)=first s t z i := by
  fin_cases i <;> simp [firstE,first]

@[simp] theorem secondE_value (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (secondE s i)=second s t z i := by
  fin_cases i <;> simp [secondE,second,r65_ite]

@[simp] theorem nuE_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (nuE s)=nu s t z := by
  rcases s with ⟨f,td,atG,i⟩
  fin_cases i <;> simp [nuE,nu,r65_ite,r65_lit]

@[simp] theorem squareE_value (s : ScalarCase) (t z : ℝ) (i : Fin 4) :
    Expression.value (inputs s t z) (squareE s i)=square s t z i := by
  simp only [squareE,square,st,firstE_value,secondE_value,r65_add,r65_sub,r65_mul,r65_pow,
    r65_var,r65_zero,r65_two,r65_ite,var,r65_in8]

def rootArgument (s : ScalarCase) (t z : ℝ) (i : Fin 7) : ℝ :=
  if hi : i.val<4 then square s t z ⟨i.val,hi⟩
  else if i.val=4 then 1+(g s.family t)^2
  else if i.val=5 then 1+(eta t)^2 else 1+(epsilon s.family t)^2

@[simp] theorem rootSquare_value (s : ScalarCase) (t z : ℝ) (i : Fin 7) :
    Expression.value (inputs s t z) (rootSquare s i)=rootArgument s t z i := by
  dsimp only [rootSquare,rootArgument]
  split_ifs <;>
    simp only [squareE_value,gE_value,etaE_value,epsilonE_value,r65_add,r65_pow,r65_one]

def upper (s : ScalarCase) (t z : ℝ) (i : Fin 7) : ℝ :=
  Expression.value (inputs s t z) (rootExpression s i)

@[simp] theorem rootExpression_value (s : ScalarCase) (t z : ℝ) (i : Fin 7) :
    Expression.value (inputs s t z) (rootExpression s i)=upper s t z i := rfl

theorem rootArgument_nonneg (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 7) :
    0≤rootArgument s t z i := by
  dsimp [rootArgument]
  split_ifs
  · exact square_nonneg s ht hz _
  all_goals positivity

theorem root_lower (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (i : Fin 7) :
    Real.sqrt (rootArgument s t z i)≤upper s t z i := by
  have h := Expression.sqrt_le_value (inputs s t z) («variables» s) (rootSquare s i)
    (by simpa using rootArgument_nonneg s ht hz i) (seeds_positive s i)
  simpa only [rootSquare_value,upper,rootExpression] using h

def upperETerm (s : ScalarCase) (t z : ℝ) : ℝ :=
  if tiltedE s.family then
    1+2*Real.cos (SoleTScalarModel.e s t z)+(1+2*epsilon s.family t)*Real.sin (SoleTScalarModel.e s t z)-
      (radiusUpper:ℝ)*Real.sin (SoleTScalarModel.e s t z)*upper s t z 6
  else if isDE s.family then
    1+Real.cos (SoleTScalarModel.e s t z)/2+(1-(axisUpper:ℝ))*Real.sin (SoleTScalarModel.e s t z)+3/2*(5/4)
  else 3+Real.sin (SoleTScalarModel.e s t z)-2*(radiusUpper:ℝ)*Real.sin (SoleTScalarModel.e s t z/2)

theorem expression_value (s : ScalarCase) (t z : ℝ) :
    Expression.value (inputs s t z) (expression s)=
      k s.family t z*(1+2*Real.cos (x s t z)+(1+2*g s.family t)*Real.sin (x s t z))+
      c s.family t z*(1+2*Real.cos z+(1+2*eta t)*Real.sin z)+2*ell s.family t z-
      (radiusUpper:ℝ)*(k s.family t z*Real.sin (x s t z)*upper s t z 4+
        c s.family t z*Real.sin z*upper s t z 5)+upperETerm s t z+
      nu s t z*(Real.cos t-1)-(radiusUpper:ℝ)*
        (upper s t z 0+upper s t z 1+upper s t z 2+upper s t z 3) := by
  unfold expression baseExpression eExpression upperETerm
  split_ifs <;>
    simp only [cx,sx,cz,sz,ce,se,ct,shalf,kE_value,cE_value,ellE_value,gE_value,etaE_value,
      epsilonE_value,nuE_value,rootExpression_value,r65_add,r65_sub,r65_mul,r65_lit,r65_var,
      r65_one,r65_two,r65_three,lit,var,r65_in2,r65_in3,r65_in4,r65_in5,r65_in6,r65_in7,
      r65_in9,r65_in10] <;>
    push_cast <;> ring

theorem upperETerm_le (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    upperETerm s t z≤eTerm s (radiusUpper:ℝ) (axisUpper:ℝ) t z := by
  have hsin := (transport_trig (split_angles s ht hz).2.2).2.2.1
  have hr : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hroot := root_lower s ht hz 6
  norm_num [rootArgument] at hroot
  have hh := mul_le_mul_of_nonneg_left hroot (mul_nonneg hr hsin)
  dsimp [upperETerm,eTerm,primaryCoefficient]
  split_ifs <;> nlinarith

theorem model_le_actual (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    Expression.value (inputs s t z) (expression s)≤
      value s (radiusUpper:ℝ) (axisUpper:ℝ) t z := by
  obtain ⟨hk,hl,hc,hg,he,hη⟩ := coefficient_positive ht hz
  obtain ⟨hz',hx,he'⟩ := split_angles s ht hz
  have hsx := (transport_trig hx).2.2.1
  have hsz := (transport_trig hz').2.2.1
  have hr : (0:ℝ)≤(radiusUpper:ℝ) := by norm_num [radiusUpper]
  have hG := root_lower s ht hz 4
  have hT := root_lower s ht hz 5
  change Real.sqrt (1+(g s.family t)^2)≤upper s t z 4 at hG
  change Real.sqrt (1+(eta t)^2)≤upper s t z 5 at hT
  have hGp := mul_le_mul_of_nonneg_left hG (mul_nonneg hr (mul_nonneg hk.le hsx))
  have hTp := mul_le_mul_of_nonneg_left hT (mul_nonneg hr (mul_nonneg hc.le hsz))
  have h0 := root_lower s ht hz 0
  have h1 := root_lower s ht hz 1
  have h2 := root_lower s ht hz 2
  have h3 := root_lower s ht hz 3
  change Real.sqrt (square s t z 0)≤upper s t z 0 at h0
  change Real.sqrt (square s t z 1)≤upper s t z 1 at h1
  change Real.sqrt (square s t z 2)≤upper s t z 2 at h2
  change Real.sqrt (square s t z 3)≤upper s t z 3 at h3
  have hsum' := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) hr
  have hE := upperETerm_le s ht hz
  rw [expression_value]
  simp only [value,primaryCoefficient,Fin.sum_univ_four]
  linarith

theorem square_coordinates (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    ∃ X Y : ℝ,|X|≤1 ∧ |Y|≤1 ∧ parameterValue s.family X=t ∧
      secondValue s.family X Y=z := by
  let a : ℝ := (left s.family:ℝ)
  let b : ℝ := (right s.family:ℝ)
  have hab : a<b := by
    have h : ((left s.family:ℚ):ℝ)<((right s.family:ℚ):ℝ) := by
      exact_mod_cast (interval_order s.family).2.1
    exact h
  have hwidth : 0<b-a := by linarith
  have hta : a≤t := ht.1
  have htb : t≤b := ht.2
  let X : ℝ := (2*t-a-b)/(b-a)
  have hX : |X|≤1 := by
    apply abs_le.mpr
    dsimp only [X]
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
        dsimp only [Y]
        linarith
      · have hh : 2*z/t≤2 := (div_le_iff₀ htpos).2 (by linarith [hz.2])
        dsimp only [Y]
        linarith
    refine ⟨X,Y,hX,hY,htX,?_⟩
    rw [secondValue,htX]
    dsimp only [Y]
    field_simp [ht0]
    ring

theorem conservative_positive (s : ScalarCase) {t z : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    (1/10000:ℝ)<value s (radiusUpper:ℝ) (axisUpper:ℝ) t z := by
  obtain ⟨X,Y,hX,hY,htX,hzY⟩ := square_coordinates s ht hz
  have hp := model_positive s hX hY
  rw [htX,hzY] at hp
  exact hp.trans_le (model_le_actual s ht hz)

theorem antitone_parameters (s : ScalarCase) {t z R R' M M' : ℝ}
    (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) (hR : R≤R') (hM : M≤M') :
    value s R' M' t z≤value s R M t z := by
  obtain ⟨hk,hl,hc,hg,hε,hη⟩ := coefficient_positive ht hz
  obtain ⟨hz',hx,he⟩ := split_angles s ht hz
  have hsx := (transport_trig hx).2.2.1
  have hsz := (transport_trig hz').2.2.1
  have hse := (transport_trig he).2.2.1
  have heh : SoleTScalarModel.e s t z/2∈Set.Icc 0 frameCap := by
    have h1 := he.1
    have h2 := he.2
    simp only [frameCap] at h2 ⊢
    constructor <;> linarith
  have hsh := (transport_trig heh).2.2.1
  have hG := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (mul_nonneg hk.le hsx) (Real.sqrt_nonneg (1+(g s.family t)^2)))
  have hT := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg (mul_nonneg hc.le hsz) (Real.sqrt_nonneg (1+(eta t)^2)))
  have hE := mul_nonneg (sub_nonneg.mpr hR)
    (mul_nonneg hse (Real.sqrt_nonneg (1+(epsilon s.family t)^2)))
  have hhigh := mul_nonneg (sub_nonneg.mpr hR) hsh
  have haxis := mul_nonneg (sub_nonneg.mpr hM) hse
  have hsum : 0≤∑ i : Fin 4,Real.sqrt (square s t z i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hnorm := mul_nonneg (sub_nonneg.mpr hR) hsum
  simp only [value,eTerm,primaryCoefficient]
  split_ifs <;> linarith

/-- This is a strict scalar assertion at the actual common q. The
original configuration is never moved to the rational comparison cap. -/
theorem actual_radius_positive (s : ScalarCase) {q t z : ℝ}
    (hq : q≤qTrial) (ht : t∈domain s.family) (hz : z∈Set.Icc 0 t) :
    (1/10000:ℝ)<value s (Real.sqrt q) (Real.sqrt (q-1/4)) t z := by
  have hR := (Real.sqrt_le_sqrt hq).trans radius_upper.le
  have hM := (Real.sqrt_le_sqrt (sub_le_sub_right hq (1/4))).trans axis_upper.le
  exact (conservative_positive s ht hz).trans_le (antitone_parameters s ht hz hR hM)

end SquaresInCircles.Eight.SolePositiveTScalar
