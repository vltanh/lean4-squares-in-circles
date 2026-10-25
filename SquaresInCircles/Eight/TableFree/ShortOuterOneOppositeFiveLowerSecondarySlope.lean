module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveLowerSecondaryCurvature

/-!
# The whole-angle axial slope bound for the lower secondary contact

Uncompiled transcription of equations (13)--(16) of
`HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md`.
The rotated horizontal projection is compared to 3/(2 T0) by the
written squared-difference identity. Its remaining bracket is one
decreasing quadratic on the entire sine interval. This supplies the
uniform axial derivative bound for both literal coefficient tuples.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerSecondary
open CommonQuarter CorePairGeometry Arithmetic

def rotationU (u : ℝ) : ℝ := Real.cos u*axialZ u+Real.sin u*axialT u
def rotationV (u : ℝ) : ℝ := -Real.sin u*axialZ u+Real.cos u*axialT u
def ak (u : ℝ) : ℝ := (Real.cos u+2)/(Real.cos u+1)
def rho0 : ℝ := 3/(2*T0)
def bracket (u : ℝ) : ℝ := 2*rho0*(axialT u)^2-
  Q0*Real.sin u*(1+ak u/T0^2)
def quadratic (s : ℝ) : ℝ :=
  2*(29/25)*(T0^2+(3/2)*s^2)-Q0*s*(1+(157/100)/T0^2)

lemma T0_positive : 0<T0 := by linarith [T0_bounds.1]
lemma rho0_lower : (29/25:ℝ)<rho0 := by
  rw [rho0,lt_div_iff₀ (show 0<2*T0 by linarith [T0_bounds.1])]
  linarith [T0_bounds.2]
lemma rho0_sq : rho0^2*T0^2=9/4 := by
  dsimp [rho0]
  field_simp [T0_positive.ne']
  ring

lemma ak_bounds {u : ℝ} (hu : u∈Icc 0 cap) : (3/2:ℝ)≤ak u ∧ ak u<157/100 := by
  have ht := small_trig hu
  have hd : 0<Real.cos u+1 := by linarith [ht.1]
  constructor
  · rw [ak,le_div_iff₀ hd]
    linarith [ht.2.1]
  · rw [ak,div_lt_iff₀ hd]
    linarith [ht.1]

lemma axial_radical_identity {u : ℝ} (hu : u∈Icc 0 cap) :
    (axialT u)^2=T0^2+ak u*(Real.sin u)^2 := by
  have hk : Real.cos u+1≠0 := by linarith [(small_trig hu).1]
  have hroot := axialT_sq (small_angle hu)
  have ha : ak u*(Real.cos u+1)=Real.cos u+2 := by
    dsimp [ak]
    field_simp [hk]
  have he : ((axialT u)^2-T0^2)*(Real.cos u+1)=
      (Real.cos u+2)*(Real.sin u)^2 := by
    rw [hroot,T0_sq]
    dsimp [axialZ]
    linear_combination -(Real.cos u+2)*(Real.sin_sq_add_cos_sq u)
  have hz : ((axialT u)^2-T0^2-ak u*(Real.sin u)^2)*(Real.cos u+1)=0 := by
    linear_combination he-(Real.sin u)^2*ha
  rcases mul_eq_zero.mp hz with hh | hh
  · linarith
  · exact (hk hh).elim

lemma squared_projection_identity {u : ℝ} (hu : u∈Icc 0 cap) :
    (Real.cos u*axialZ u)^2-((rho0-Real.sin u)*axialT u)^2=Real.sin u*bracket u := by
  have hcircle : (Real.cos u)^2+(Real.sin u)^2=1 := by linarith [Real.sin_sq_add_cos_sq u]
  have hz : (axialZ u)^2+(axialT u)^2=Q0 := by linarith [axialT_sq (small_angle hu)]
  have hT := axial_radical_identity hu
  have hr := rho0_sq
  have hbase := T0_sq
  have hquot : (axialZ u)^2-rho0^2*(axialT u)^2=
      -Q0*ak u*(Real.sin u)^2/T0^2 := by
    apply (eq_div_iff (pow_ne_zero 2 T0_positive.ne')).2
    linear_combination T0^2*hz-(axialT u)^2*hbase-(axialT u)^2*hr-Q0*hT
  calc
    (Real.cos u*axialZ u)^2-((rho0-Real.sin u)*axialT u)^2=
      ((Real.cos u)^2+(Real.sin u)^2)*(axialZ u)^2-rho0^2*(axialT u)^2+
        2*rho0*Real.sin u*(axialT u)^2-(Real.sin u)^2*((axialZ u)^2+(axialT u)^2) := by ring
    _=(axialZ u)^2-rho0^2*(axialT u)^2+
        2*rho0*Real.sin u*(axialT u)^2-(Real.sin u)^2*Q0 := by rw [hcircle,hz]; ring
    _=Real.sin u*bracket u := by rw [hquot]; dsimp [bracket]; ring

lemma quadratic_positive {s : ℝ} (hs : s∈Icc 0 (13/20:ℝ)) : 0<quadratic s := by
  have href : (0:ℝ)<quadratic (13/20) := by norm_num [quadratic,T0_sq,Q0]
  have hf : 0≤Q0*(1+(157/100)/T0^2)-(87/25)*(s+13/20) := by
    rw [T0_sq]
    norm_num [Q0]
    linarith [hs.2]
  have hp := mul_nonneg (show 0≤(13/20:ℝ)-s by linarith [hs.2]) hf
  have he : quadratic s-quadratic (13/20)=
      (13/20-s)*(Q0*(1+(157/100)/T0^2)-(87/25)*(s+13/20)) := by
    dsimp [quadratic]
    ring
  linarith

lemma bracket_positive {u : ℝ} (hu : u∈Icc 0 cap) : 0<bracket u := by
  have ht := small_trig hu
  have hA := ak_bounds hu
  have hT := axial_radical_identity hu
  have hAlow := mul_le_mul_of_nonneg_right hA.1 (sq_nonneg (Real.sin u))
  have hTlow : T0^2+(3/2)*(Real.sin u)^2≤(axialT u)^2 := by linarith
  have hrho := mul_le_mul_of_nonneg_right rho0_lower.le (show 0≤2*(axialT u)^2 by positivity)
  have hroot := mul_le_mul_of_nonneg_left hTlow (by norm_num : (0:ℝ)≤2*(29/25))
  have hAdiv := div_le_div_of_nonneg_right hA.2.le (sq_nonneg T0)
  have hneg := mul_le_mul_of_nonneg_left hAdiv
    (mul_nonneg (by norm_num [Q0] : 0≤Q0) ht.2.2.1)
  have hquad := quadratic_positive ⟨ht.2.2.1,ht.2.2.2.le⟩
  dsimp [bracket,quadratic] at *
  nlinarith only [hrho,hroot,hneg,hquad]

lemma horizontal_ratio {u : ℝ} (hu : u∈Icc 0 cap) : rho0≤rotationU u/axialT u := by
  have ht := small_trig hu
  have hT := axialT_positive (small_angle hu)
  have hZ : 0<axialZ u := by dsimp [axialZ]; linarith [ht.1]
  have hleft := mul_pos (show 0<Real.cos u by linarith [ht.1]) hZ
  have hright := mul_pos (show 0<rho0-Real.sin u by linarith [rho0_lower,ht.2.2.2]) hT
  have hid := squared_projection_identity hu
  have hsq := mul_nonneg ht.2.2.1 (bracket_positive hu).le
  have hroot : (rho0-Real.sin u)*axialT u≤Real.cos u*axialZ u := by nlinarith only [hid,hsq,hleft,hright]
  apply (le_div_iff₀ hT).2
  dsimp [rotationU]
  nlinarith only [hroot]

lemma vertical_ratio {u : ℝ} (hu : u∈Icc 0 cap) : rotationV u/axialT u≤1 := by
  have ht := small_trig hu
  have hT := axialT_positive (small_angle hu)
  have hZ : 0≤axialZ u := by dsimp [axialZ]; linarith [ht.1]
  have hk := mul_le_mul_of_nonneg_right ht.2.1 hT.le
  have hs := mul_nonneg ht.2.2.1 hZ
  apply (div_le_one hT).2
  dsimp [rotationV]
  linarith

lemma first_axial_identity (r : Bool) {u : ℝ} (hu : u∈Icc 0 cap) :
    first r (1/2) u=(-p r)/(2*X0)-q r+t r*(rotationU u/axialT u)-P r*(rotationV u/axialT u) := by
  have hT := axialT_positive (small_angle hu)
  have hX : 0<X0 := by linarith [X0_bounds.1]
  have h1 : rootD (1/2)=-(1/2)/X0 := by rw [rootD,root_half]
  have h2 : rootD (Z (1/2) u)=-axialZ u/axialT u := rfl
  simp only [first,h1,h2,D,E,rotationU,rotationV]
  field_simp
  ring

lemma fixed_slope (r : Bool) : (-3/125:ℝ)<(-p r)/(2*X0)-q r+3*t r/(2*T0)-P r := by
  have hp : 0≤-p r := by linarith [(coefficient_bounds r).2.1]
  have ht : 0≤3*t r := by linarith [(coefficient_bounds r).2.2.2.2.2.2.1]
  have hX : 0<2*X0 := by linarith [X0_bounds.1]
  have hT : 0<2*T0 := by linarith [T0_bounds.1]
  have hx := div_le_div_of_nonneg_left hp hX
    (show 2*X0≤2*(1914575672/1000000000:ℝ) by linarith [X0_bounds.2])
  have hv := div_le_div_of_nonneg_left ht hT
    (show 2*T0≤2*(1290581265/1000000000:ℝ) by linarith [T0_bounds.2])
  have hfixed : (-3/125:ℝ)<(-p r)/(2*(1914575672/1000000000:ℝ))-q r+
      3*t r/(2*(1290581265/1000000000:ℝ))-P r := by
    cases r <;> norm_num [p,q,P,t,pQ,qQ,PQ,tQ]
  linarith

theorem first_axial_lower (r : Bool) {u : ℝ} (hu : u∈Icc 0 cap) : (-3/125:ℝ)<first r (1/2) u := by
  have hU := mul_le_mul_of_nonneg_left (horizontal_ratio hu)
    (show 0≤t r by linarith [(coefficient_bounds r).2.2.2.2.2.2.1])
  have hV := mul_le_mul_of_nonneg_left (vertical_ratio hu)
    (show 0≤P r by linarith [(coefficient_bounds r).2.2.2.2.1])
  rw [first_axial_identity r hu]
  have hh := fixed_slope r
  have e : t r*rho0=3*t r/(2*T0) := by dsimp [rho0]; ring
  rw [e] at hU
  rw [mul_one] at hV
  linarith only [hU,hV,hh]

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerSecondary
