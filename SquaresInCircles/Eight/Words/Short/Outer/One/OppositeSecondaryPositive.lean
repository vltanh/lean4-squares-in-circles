module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeSecondaryData

/-!
# Eight squares: the common positive-half quadratic for opposite secondary owners

The exact expansion of the derivative numerator retains both circle
components. The displayed concave quadratic is positive between its
two rational endpoints, proving monotonicity on the entire angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary.Positive
open CommonQuarter CorePairGeometry Arithmetic

def h (r : Row) (x : ℝ) : ℝ := P r*Real.cos x+t r*Real.sin x
def g (r : Row) (x : ℝ) : ℝ := t r*Real.cos x-P r*Real.sin x
def A (r : Row) : ℝ := P r+(weight r)^2-radiusUpper*weight r*t r
def B (r : Row) : ℝ := t r-(weight r)^2+radiusUpper*weight r*P r
def quadraticC (r : Row) : ℝ := -weight r*(P r+t r)-A r/2
def quadratic (r : Row) (s : ℝ) : ℝ :=
  weight r*(1+P r)+A r+(B r+(191/250:ℝ)*weight r*(t r-P r))*s+quadraticC r*s^2
def quadraticD (r : Row) (s : ℝ) : ℝ :=
  B r+(191/250:ℝ)*weight r*(t r-P r)+2*quadraticC r*s
def J (r : Row) (x : ℝ) : ℝ :=
  (1+weight r*(Real.cos x-Real.sin x))*(weight r+h r x)-radiusUpper*weight r*g r x

lemma coefficients (r : Row) : A r< -(33/50:ℝ) ∧ quadraticC r< -(29/100:ℝ) ∧
    (39/200:ℝ)<quadratic r 0 ∧ (41/1000:ℝ)<quadratic r (129/200) := by
  fin_cases r <;> norm_num [A,B,quadraticC,quadratic,radiusUpper,weight,P,t]

lemma quadratic_hasDerivAt (r : Row) (s : ℝ) :
    HasDerivAt (quadratic r) (quadraticD r s) s := by
  have h := (((hasDerivAt_id' s).const_mul (B r+(191/250:ℝ)*weight r*(t r-P r))).const_add
    (weight r*(1+P r)+A r)).fun_add ((hasDerivAt_pow 2 s).const_mul (quadraticC r))
  convert h using 1
  · funext y
    simp only [quadratic]
  · simp only [quadraticD]
    norm_num
    ring

lemma quadraticD_hasDerivAt (r : Row) (s : ℝ) :
    HasDerivAt (quadraticD r) (2*quadraticC r) s := by
  have h := ((hasDerivAt_id' s).const_mul (2*quadraticC r)).const_add
    (B r+(191/250:ℝ)*weight r*(t r-P r))
  exact h.congr_deriv (by ring)

lemma quadratic_lower (r : Row) {s : ℝ} (hs : s∈Icc 0 (129/200:ℝ)) :
    (41/1000:ℝ)<quadratic r s := by
  have hc : ConcaveOn ℝ (Icc 0 (129/200:ℝ)) (quadratic r) := concave_of_deriv2
    (fun y _ => quadratic_hasDerivAt r y) (fun y _ => quadraticD_hasDerivAt r y)
    (fun y _ => by linarith [(coefficients r).2.1])
  apply concave_gt_of_endpoints hc hs
  · linarith [(coefficients r).2.2.1]
  · exact (coefficients r).2.2.2

lemma rotation_positive (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<g r x ∧ 0<weight r+h r x := by
  have ht := positive_trig hx
  fin_cases r <;> norm_num [g,h,weight,P,t] <;>
    constructor <;> linarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1]

lemma norm_projection (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r true x)^2=(weight r+h r x)^2+(g r x)^2 := by
  have hn := norm_sq r true hx
  dsimp [h,g,Unit.direction] at *
  linear_combination hn-((P r)^2+(t r)^2)*(Real.sin_sq_add_cos_sq x)

lemma norm_above_shift (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    weight r+h r x≤N r true x := by
  have hn := norm_projection r hx
  nlinarith [sq_nonneg (g r x),norm_positive r true hx,(rotation_positive r hx).2]

lemma first_formula (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    first r true x=1+weight r*(Real.cos x-Real.sin x)-radius*weight r*g r x/N r true x := by
  have hn := norm_positive r true hx
  have hdir : Unit.direction true=1 := by simp [Unit.direction]
  have hN : CircularNorm.norm (normA r) (normB r) (normC r true) x=N r true x := rfl
  have hd : CircularNorm.d1 (normA r) (normB r) (normC r true) x=
      weight r*g r x/N r true x := by
    rw [CircularNorm.d1,hN]
    simp only [CircularNorm.slope,normB,normC,hdir,g]
    field_simp
    ring
  rw [first,hd,hdir]
  ring

lemma J_expansion (r : Row) (x : ℝ) : J r x=
    weight r*(1+P r)+A r*Real.cos x+B r*Real.sin x-
      weight r*(P r+t r)*(Real.sin x)^2+
        weight r*(t r-P r)*Real.sin x*Real.cos x := by
  dsimp [J,A,B,h,g]
  linear_combination weight r*P r*(Real.sin_sq_add_cos_sq x)

lemma J_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    quadratic r (Real.sin x)≤J r x := by
  have ht := positive_trig hx
  have hcos : Real.cos x≤1-(Real.sin x)^2/2 := by
    nlinarith [sq_nonneg (1-Real.cos x),Real.sin_sq_add_cos_sq x]
  have hA := mul_le_mul_of_nonpos_left hcos (show A r≤0 by linarith [(coefficients r).1])
  have hcoef : 0≤weight r*(t r-P r)*Real.sin x :=
    mul_nonneg (mul_nonneg (coefficient_bounds r).1.le (coefficient_bounds r).2.2.2.le) ht.2.2.1
  have hcross := mul_le_mul_of_nonneg_left (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) hcoef
  rw [J_expansion]
  dsimp [quadratic,quadraticC]
  nlinarith only [hA,hcross]

lemma first_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    J r x/(weight r+h r x)≤first r true x := by
  have hg := (rotation_positive r hx).1
  have hh := (rotation_positive r hx).2
  have hn := norm_positive r true hx
  have hnum : 0≤radius*weight r*g r x :=
    mul_nonneg (mul_nonneg RoleFour.radius_positive.le (coefficient_bounds r).1.le) hg.le
  have hncomp := div_le_div_of_nonneg_left hnum hh (norm_above_shift r hx)
  have hR : radius≤radiusUpper := by
    have h := RoleFour.radius_upper
    rw [show radiusUpper=(1978788/1000000:ℝ) by norm_num [radiusUpper]]
    exact h.le
  have hnumcomp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hR (coefficient_bounds r).1.le) hg.le
  have hnumcomp' := div_le_div_of_nonneg_right hnumcomp hh.le
  have hquot : J r x/(weight r+h r x)=
      1+weight r*(Real.cos x-Real.sin x)-radiusUpper*weight r*g r x/(weight r+h r x) := by
    dsimp [J]
    field_simp [hh.ne']
  rw [hquot,first_formula r hx]
  linarith

lemma first_positive (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<first r true x := by
  have ht := positive_trig hx
  have hs : Real.sin x∈Icc 0 (129/200:ℝ) :=
    ⟨ht.2.2.1,by linarith [ht.2.2.2.1]⟩
  have hJ : 0<J r x := by linarith [quadratic_lower r hs,J_lower r hx]
  exact (div_pos hJ (rotation_positive r hx).2).trans_le (first_lower r hx)

theorem value_monotone (r : Row) : MonotoneOn (value r true) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
  (fun x hx => (value_hasDerivAt r true hx).continuousAt.continuousWithinAt)
  (fun x hx => value_hasDerivAt r true (Ioo_subset_Icc_self hx))
  (fun x hx => (first_positive r (Ioo_subset_Icc_self hx)).le)

end SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary.Positive
