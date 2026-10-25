module

public import SquaresInCircles.Eight.Owners.Contact.ArcMinimum
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeData

/-!
# Eight squares: the remaining affine-source interior contact

The original target-stationarity equation identifies the full-circle
support point. Its explicit coordinate curve remains in the physical
contact region near an interior original point. The reduced angular
cost has strict negative curvature by the written N'' >= -N/4 identity.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Norm
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)
open SecondWord (U W outer_domain U_positive UW_circle)

abbrev R : ℝ := Real.sqrt Q0
def A : ℝ := (v 2)^2+(t 2)^2+(q 2)^2
def C : ℝ := -2*q 2*t 2
def D : ℝ := -2*q 2*v 2
def X (x : ℝ) : ℝ := v 2-q 2*Real.sin x
def Y (x : ℝ) : ℝ := t 2-q 2*Real.cos x
def N (x : ℝ) : ℝ := CircularNorm.norm A C D x
def ND (x : ℝ) : ℝ := CircularNorm.d1 A C D x
def NDD (x : ℝ) : ℝ := CircularNorm.d2 A C D x
def horizontal (x : ℝ) : ℝ := -R*X x/N x
def vertical (x : ℝ) : ℝ := -R*Y x/N x
def height (x : ℝ) : ℝ := vertical x-1/2
def value (x : ℝ) : ℝ :=
  x+c 2+(q 2-v 2-t 2)/2+q 2*(Real.sin x+Real.cos x)-R*N x
def first (x : ℝ) : ℝ := 1+q 2*(Real.cos x-Real.sin x)-R*ND x
def second (x : ℝ) : ℝ := -q 2*(Real.sin x+Real.cos x)-R*NDD x

lemma radius_bounds : 0<R ∧ R<2 ∧ R^2=Q0 := by
  have hp : (0:ℝ)<Q0 := by norm_num [Q0]
  have he := Real.sq_sqrt hp.le
  exact ⟨Real.sqrt_pos.mpr hp,(Real.sqrt_lt' (by norm_num)).2 (by norm_num [Q0]),he⟩

lemma projection_bounds (x : ℝ) :
    -(443/500:ℝ)<v 2*Real.sin x+t 2*Real.cos x ∧
      v 2*Real.sin x+t 2*Real.cos x<443/500 := by
  have hs := sq_nonneg (v 2*Real.cos x-t 2*Real.sin x)
  have hid : (v 2*Real.sin x+t 2*Real.cos x)^2+
      (v 2*Real.cos x-t 2*Real.sin x)^2=(v 2)^2+(t 2)^2 := by
    linear_combination ((v 2)^2+(t 2)^2)*(Real.sin_sq_add_cos_sq x)
  have he : (v 2)^2+(t 2)^2<(443/500:ℝ)^2 := by norm_num [v,t]
  constructor <;> nlinarith

lemma energy_formula (x : ℝ) :
    CircularNorm.energy A C D x=A-2*q 2*(v 2*Real.sin x+t 2*Real.cos x) := by
  dsimp [CircularNorm.energy,C,D]
  ring

lemma energy_positive (x : ℝ) : 0<CircularNorm.energy A C D x := by
  rw [energy_formula]
  have hp := (projection_bounds x).2
  norm_num [A,v,t,q] at *
  linarith

lemma norm_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (energy_positive x)

lemma norm_square (x : ℝ) : (N x)^2=(X x)^2+(Y x)^2 := by
  rw [N,CircularNorm.norm_sq (energy_positive x).le]
  dsimp [CircularNorm.energy,A,C,D,X,Y]
  linear_combination (-(q 2)^2)*(Real.sin_sq_add_cos_sq x)

lemma norm_upper (x : ℝ) : N x<(943/500:ℝ) := by
  have hs := CircularNorm.norm_sq (energy_positive x).le
  rw [energy_formula] at hs
  have hp := (projection_bounds x).1
  have hsq : (N x)^2<(943/500:ℝ)^2 := by
    show (CircularNorm.norm A C D x)^2<_
    rw [hs]
    norm_num [A,v,t,q] at hp ⊢
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

lemma norm_hasDerivAt (x : ℝ) : HasDerivAt N (ND x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive x)
lemma first_norm_hasDerivAt (x : ℝ) : HasDerivAt ND (NDD x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive x)

lemma value_hasDerivAt (x : ℝ) : HasDerivAt value (first x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y+c 2+(q 2-v 2-t 2)/2) 1 x := by
    simpa using ((hasDerivAt_id x).add_const (c 2)).add_const ((q 2-v 2-t 2)/2)
  have h2 : HasDerivAt (fun y => q 2*(Real.sin y+Real.cos y))
      (q 2*(Real.cos x+-Real.sin x)) x :=
    ((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul (q 2)
  have h3 : HasDerivAt (fun y => R*N y) (R*ND x) x := (norm_hasDerivAt x).const_mul R
  have h := (h1.fun_add h2).fun_sub h3
  have he : value=fun y => y+c 2+(q 2-v 2-t 2)/2+q 2*(Real.sin y+Real.cos y)-R*N y := rfl
  rw [he]
  convert h using 1
  simp only [first]
  ring

lemma first_hasDerivAt (x : ℝ) : HasDerivAt first (second x) x := by
  have h2 : HasDerivAt (fun y => q 2*(Real.cos y-Real.sin y))
      (q 2*(-Real.sin x-Real.cos x)) x :=
    ((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul (q 2)
  have h3 : HasDerivAt (fun y => R*ND y) (R*NDD x) x := (first_norm_hasDerivAt x).const_mul R
  have h := (h2.const_add 1).fun_sub h3
  have he : first=fun y => 1+q 2*(Real.cos y-Real.sin y)-R*ND y := rfl
  rw [he]
  convert h using 1
  simp only [second]
  ring

lemma second_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : second x≤-(1/20:ℝ) := by
  have hcoef : C^2+D^2≤A^2 := by norm_num [A,C,D,v,t,q]
  have hcurv : -N x/4≤NDD x := CircularNorm.curvature_lower (energy_positive x) hcoef
  have ht := positive_trig hx
  have hsum : 1≤Real.sin x+Real.cos x := ht.2.2.2.2.2
  have hN := norm_upper x
  have hNp := norm_positive x
  have hR := radius_bounds
  have hproduct : R*N x<2*(943/500:ℝ) :=
    (mul_lt_mul_of_pos_right hR.2.1 hNp).trans
      (mul_lt_mul_of_pos_left hN (by norm_num))
  have hweighted := mul_le_mul_of_nonneg_left hcurv hR.1.le
  have hq : q 2=9994/10000 := by norm_num [q]
  simp only [second]
  rw [hq]
  linarith

lemma X_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) : X x<0 := by
  have hs := (positive_trig hx).2.2.1
  norm_num [X,v,q]
  linarith

lemma original_parallel {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusTarget 2 B x=0) : Y x*U B=X x*W B := by
  have hu := U_positive (outer_domain hd.1)
  dsimp [plusTarget,h,l,plusK,SecondWord.OppositeZero.plusK] at hstat
  norm_num [p] at hstat
  change t 2-v 2*(W B/U B)-q 2*(Real.cos x-(W B/U B)*Real.sin x)=0 at hstat
  field_simp [hu.ne'] at hstat
  dsimp [X,Y]
  nlinarith only [hstat]

lemma original_coordinates {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusTarget 2 B x=0) : horizontal x=U B ∧ vertical x=W B := by
  have hp := original_parallel hd hstat
  have hc := UW_circle (outer_domain hd.1)
  have hn := norm_square x
  have hN := norm_positive x
  have hR := radius_bounds
  have hU := U_positive (outer_domain hd.1)
  have hX := X_negative hd.2.1
  have he : (N x*U B)^2=(R*X x)^2 := by
    linear_combination (U B)^2*hn+(X x)^2*hc+
      (Y x*U B+X x*W B)*hp-(X x)^2*hR.2.2
  have hRX : 0< -R*X x := by
    have hh := mul_pos hR.1 (neg_pos.mpr hX)
    linarith
  have hu : -R*X x=N x*U B :=
    (pow_left_inj₀ hRX.le (mul_pos hN hU).le two_ne_zero).1 (by rw [he]; ring)
  have hhor : horizontal x=U B := by
    unfold horizontal
    apply (div_eq_iff hN.ne').2
    linarith
  have hvert : vertical x=W B := by
    unfold vertical
    apply (div_eq_iff hN.ne').2
    have heq : U B*(-R*Y x-N x*W B)=0 := by linear_combination (-R)*hp+(W B)*hu
    have hz := (mul_eq_zero.mp heq).resolve_left hU.ne'
    linarith
  exact ⟨hhor,hvert⟩

lemma original_height {B x : ℝ} (hd : PlusDomain B x)
    (hstat : plusTarget 2 B x=0) : height x=B := by
  rw [height,(original_coordinates hd hstat).2]
  dsimp [W]
  ring

lemma circle (x : ℝ) : (horizontal x)^2+(vertical x)^2=Q0 := by
  have hn := norm_square x
  have hN := norm_positive x
  dsimp [horizontal,vertical]
  field_simp [hN.ne']
  nlinarith [radius_bounds.2.2]

lemma height_continuous : Continuous height := by
  have hN : Continuous N :=
    continuous_iff_continuousAt.2 (fun x => (norm_hasDerivAt x).continuousAt)
  have hY : Continuous Y := by
    show Continuous fun x => t 2-q 2*Real.cos x
    fun_prop
  have he : height=fun x => -R*Y x/N x-1/2 := rfl
  rw [he]
  exact ((continuous_const.mul hY).div hN (fun x => (norm_positive x).ne')).sub continuous_const

lemma curve_state {x : ℝ} (hx : x∈Icc 0 (7/10))
    (hb : height x∈Icc 0 outerDiagonal) :
    OuterState (horizontal x-1/2) (height x) := by
  have hH : 0<horizontal x :=
    div_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos radius_bounds.1) (X_negative hx))
      (norm_positive x)
  have hV : 1/2≤vertical x := by dsimp [height] at hb; linarith [hb.1]
  have hVU : vertical x≤horizontal x := by
    have hvsq := pow_le_pow_left₀ (by linarith : 0≤vertical x)
      (show vertical x≤outerDiagonal+1/2 by dsimp [height] at hb; linarith [hb.2]) 2
    nlinarith [circle x,diagonal_circle]
  refine ⟨hb.1,?_,?_⟩
  · dsimp [height]
    linarith
  · dsimp [height]
    nlinarith [circle x]

lemma curve_value {x : ℝ} (hx : x∈Icc 0 (7/10))
    (hb : height x∈Icc 0 outerDiagonal) : plusCost 2 (height x) x=value x := by
  have hs := curve_state hx hb
  have ha := (ShortOuterOne.SameContact.actual_arc hs).1
  have hsupport : X x*horizontal x+Y x*vertical x= -R*N x := by
    have hN := (norm_positive x).ne'
    have he : X x*horizontal x+Y x*vertical x= -R*((X x)^2+(Y x)^2)/N x := by
      simp only [horizontal,vertical]
      ring
    rw [he,←norm_square x]
    field_simp
  dsimp [plusCost,source,target,SecondWord.RoleLabel.outer,SecondWord.RoleLabel.eval]
  norm_num [p]
  rw [ha]
  dsimp [plus,SecondWord.OppositeZero.plus]
  rw [ha]
  dsimp [value,height,X,Y] at *
  nlinarith only [hsupport]

/-- A physical stationary target in row 2 has a feasible strictly concave angular curve. -/
theorem interior_not_minimum {B x : ℝ} (hd : PlusDomain B x)
    (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hb : plus B x∈Ioo 0 outerDiagonal) (hstat : plusTarget 2 B x=0)
    (hmin : ∀C y, PlusDomain C y → plusCost 2 B x≤plusCost 2 C y) : False := by
  let O : Set ℝ := Ioo 0 (7/10) ∩ height ⁻¹' Ioo 0 outerDiagonal ∩
    (fun y => plus (height y) y) ⁻¹' Ioo 0 outerDiagonal
  have hplus : Continuous (fun y => plus (height y) y) := by
    have hh := height_continuous
    dsimp [plus,SecondWord.OppositeZero.plus,arc]
    fun_prop
  have hO : IsOpen O :=
    (isOpen_Ioo.inter (isOpen_Ioo.preimage height_continuous)).inter
      (isOpen_Ioo.preimage hplus)
  have hxO : x∈O := by simpa [O,original_height hd hstat] using And.intro (And.intro hx hB) hb
  apply not_minimum_on_strictly_concave_curve
    (s := {p : ℝ×ℝ | PlusDomain p.1 p.2})
    (cost := fun p => plusCost 2 p.1 p.2) (p := (B,x))
    (fun p hp => hmin p.1 p.2 hp)
    (curve := fun y => (height y,y)) (value := value) (dvalue := first) (ddvalue := second)
    hO hxO (by norm_num : (0:ℝ)<1/20)
    (by simp [original_height hd hstat])
  · intro y hy
    exact ⟨Ioo_subset_Icc_self hy.1.2,Ioo_subset_Icc_self hy.1.1,Ioo_subset_Icc_self hy.2⟩
  · intro y hy
    exact curve_value (Ioo_subset_Icc_self hy.1.1) (Ioo_subset_Icc_self hy.1.2)
  · exact fun y _ => value_hasDerivAt y
  · exact fun y _ => first_hasDerivAt y
  · exact fun y hy => second_negative (Ioo_subset_Icc_self hy.1.1)

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Positive.Norm
