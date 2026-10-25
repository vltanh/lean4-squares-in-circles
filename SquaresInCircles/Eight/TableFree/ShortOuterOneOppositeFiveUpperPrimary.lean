module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveData

/-!
# Both upper primary owners on opposite edge five

Uncompiled transcription of Section 4.2 of
`HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md`.
The literal multipliers .776 and .774 give the two written full-circle
supports. The unit-vector projection bounds the norm derivative on
the entire angle half; only the initial two radicals are evaluated.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.UpperPrimary
open CommonQuarter CorePairGeometry Arithmetic

def weight : Bool→ℝ | false => 97/125 | true => 387/500
def sourceNorm (r : Bool) : ℝ := Real.sqrt ((weight r-p r)^2+(q r)^2)
def source (r : Bool) : ℝ := (weight r-p r+q r)/2-radius*sourceNorm r
def energy (r : Bool) (u : ℝ) : ℝ :=
  (P r)^2+(t r)^2+(weight r)^2+2*weight r*(P r*Real.sin u-t r*Real.cos u)
def norm (r : Bool) (u : ℝ) : ℝ := Real.sqrt (energy r u)
def projection (r : Bool) (u : ℝ) : ℝ := P r*Real.cos u+t r*Real.sin u
def value (r : Bool) (u : ℝ) : ℝ := Real.pi/2+u+c+source r+
  (weight r+P r+t r)/2+weight r*Real.sin u-radius*norm r u
def first (r : Bool) (u : ℝ) : ℝ :=
  1+weight r*Real.cos u-radius*weight r*projection r u/norm r u
def sourceUpper : Bool→ℝ | false => 322223/250000 | true => 162083/125000
def targetUpper : Bool→ℝ | false => 226021/1000000 | true => 27143/125000

lemma weight_bounds (r : Bool) : 0<weight r ∧ weight r≤97/125 := by
  cases r <;> norm_num [weight]

lemma energy_squares (r : Bool) (u : ℝ) : energy r u=
    (P r+weight r*Real.sin u)^2+(t r-weight r*Real.cos u)^2 := by
  dsimp [energy]
  linear_combination -(weight r)^2*(Real.sin_sq_add_cos_sq u)

lemma energy_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<energy r u := by
  have hfirst : 0<P r+weight r*Real.sin u := by
    have hh := mul_nonneg (weight_bounds r).1.le (positive_trig hu).2.2.1
    linarith [(coefficient_bounds r).2.2.2.2.1]
  rw [energy_squares]
  nlinarith [sq_nonneg (t r-weight r*Real.cos u)]
lemma norm_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<norm r u :=
  Real.sqrt_pos.2 (energy_positive r hu)
lemma norm_sq (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : (norm r u)^2=energy r u :=
  Real.sq_sqrt (energy_positive r hu).le

lemma energy_hasDerivAt (r : Bool) (u : ℝ) :
    HasDerivAt (energy r) (2*weight r*projection r u) u := by
  have hh := ((((Real.hasDerivAt_sin u).const_mul (P r)).fun_sub
    ((Real.hasDerivAt_cos u).const_mul (t r))).const_mul (2*weight r)).const_add
      ((P r)^2+(t r)^2+(weight r)^2)
  exact hh.congr_deriv (by simp only [projection]; ring)

lemma norm_hasDerivAt (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    HasDerivAt (norm r) (weight r*projection r u/norm r u) u := by
  have hh := (energy_hasDerivAt r u).sqrt (energy_positive r hu).ne'
  exact hh.congr_deriv (by rw [norm]; ring)

lemma value_hasDerivAt (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    HasDerivAt (value r) (first r u) u := by
  have hh := ((((((hasDerivAt_id' u).const_add (Real.pi/2)).add_const c).add_const (source r)
    ).add_const ((weight r+P r+t r)/2)).fun_add ((Real.hasDerivAt_sin u).const_mul (weight r))).fun_sub
      ((norm_hasDerivAt r hu).const_mul radius)
  exact hh.congr_deriv (by simp only [first]; ring)

lemma projection_le_norm (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) :
    projection r u≤norm r u := by
  have he : (projection r u)^2+(P r*Real.sin u-t r*Real.cos u+weight r)^2=energy r u := by
    dsimp [projection,energy]
    linear_combination ((P r)^2+(t r)^2)*(Real.sin_sq_add_cos_sq u)
  nlinarith [sq_nonneg (P r*Real.sin u-t r*Real.cos u+weight r),norm_sq r hu,
    norm_positive r hu]

lemma first_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<first r u := by
  have hn := norm_positive r hu
  have hprojection := (div_le_one hn).2 (projection_le_norm r hu)
  have hprod := mul_le_mul_of_nonneg_left hprojection
    (mul_nonneg RoleFour.radius_positive.le (weight_bounds r).1.le)
  have hR := mul_lt_mul_of_pos_right RoleFour.radius_upper (weight_bounds r).1
  have hc := mul_lt_mul_of_pos_left (show (19/25:ℝ)<Real.cos u by linarith [(positive_trig hu).1])
    (weight_bounds r).1
  have hw := mul_le_mul_of_nonneg_right (weight_bounds r).2
    (by norm_num : (0:ℝ)≤1978788/1000000-19/25)
  have e : radius*weight r*projection r u/norm r u=
      RoleFour.radius*weight r*(projection r u/norm r u) := by ring
  dsimp only [first]
  rw [e]
  linarith only [hprod,hR,hc,hw]

lemma monotone (r : Bool) : MonotoneOn (value r) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun u hu => (value_hasDerivAt r hu).continuousAt.continuousWithinAt)
    (fun u hu => value_hasDerivAt r (Ioo_subset_Icc_self hu))
    (fun u hu => (first_positive r (Ioo_subset_Icc_self hu)).le)

lemma initial_radicals (r : Bool) : sourceNorm r<sourceUpper r ∧ norm r 0<targetUpper r := by
  have hsrc := Real.sq_sqrt (show 0≤(weight r-p r)^2+(q r)^2 by positivity)
  have hsrc0 := Real.sqrt_nonneg ((weight r-p r)^2+(q r)^2)
  have htgt := norm_sq r (by norm_num : (0:ℝ)∈Icc 0 (7/10))
  have htgt0 := norm_positive r (by norm_num : (0:ℝ)∈Icc 0 (7/10))
  cases r <;> norm_num [sourceNorm,sourceUpper,targetUpper,energy,weight,p,q,P,t,pQ,qQ,PQ,tQ] at hsrc hsrc0 htgt ⊢ <;>
    constructor <;> nlinarith

lemma initial (r : Bool) : (1123/1250:ℝ)<value r 0 := by
  have hpi : (314159/200000:ℝ)<Real.pi/2 := by linarith [pi_hand_enclosure.1]
  have hsrc := mul_lt_mul'' RoleFour.radius_upper (initial_radicals r).1
    RoleFour.radius_positive.le (Real.sqrt_nonneg _)
  have htgt := mul_lt_mul'' RoleFour.radius_upper (initial_radicals r).2
    RoleFour.radius_positive.le (norm_positive r (by norm_num : (0:ℝ)∈Icc 0 (7/10))).le
  cases r <;> norm_num [value,source,c,p,q,P,t,pQ,qQ,PQ,tQ,weight,sourceUpper,targetUpper] at hsrc htgt ⊢ <;>
    linarith

lemma original_lower (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : (1+Real.cos u+Real.sin u)/2≤a+A*Real.sin u-B*Real.cos u) :
    value r u≤Real.pi/2+u+c+p r*a-q r*b-P r*A-t r*B := by
  have hsrc := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
    (X:=p r-weight r) (Y:=-(q r)) hs
  have htgt := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
    (X:=-(P r)-weight r*Real.sin u) (Y:=weight r*Real.cos u-t r) ht
  have hsep := mul_le_mul_of_nonneg_left hm (weight_bounds r).1.le
  have hsrad : (p r-weight r)^2+(-(q r))^2=(weight r-p r)^2+(q r)^2 := by ring
  have htrad : (-(P r)-weight r*Real.sin u)^2+(weight r*Real.cos u-t r)^2=energy r u := by
    rw [energy_squares]
    ring
  rw [hsrad] at hsrc
  rw [htrad] at htgt
  dsimp [value,source,sourceNorm,norm]
  nlinarith only [hsrc,htgt,hsep]

theorem original (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : (1+Real.cos u+Real.sin u)/2≤a+A*Real.sin u-B*Real.cos u) :
    (1123/1250:ℝ)<Real.pi/2+u+c+p r*a-q r*b-P r*A-t r*B :=
  ((initial r).trans_le ((monotone r) (by norm_num) hu hu.1)).trans_le
    (original_lower r hs ht hu hm)

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.UpperPrimary
