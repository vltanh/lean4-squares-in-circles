module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveUpperPrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryNegativeGeometry

/-!
# Eight squares: all six original opposite-sign secondary owners

The original axes one and three are each kept (`original_owner`). Reflection and reversal
recover the latter using their adjacent labels. Both angle halves, all state endpoints and every
weak owner tie are included, with the distinct edge-two threshold unchanged (`normalized`,
`actual_owner`).
-/

section
/-!
## The fixed opposite-secondary endpoint arithmetic

The six source bounds (`sourceLower`) and the two six-entry norm bounds (`initialNormUpper`,
`finalNormUpper`) are exact rationals. Every norm bound is derived from its squared norm; only the
two scalar endpoints occur.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary.Endpoint
open CommonQuarter CorePairGeometry Arithmetic

def sourceLower : Row→ℝ :=
  ![129190084/1000000000,-729270342/1000000000,273508205/1000000000,0,263139366/1000000000,0]
def initialNormUpper : Row→ℝ :=
  ![1880509701/1000000000,1350400957/1000000000,1332148407/1000000000,
    1176679496/1000000000,1452999491/1000000000,1241873719/1000000000]
def finalNormUpper : Row→ℝ :=
  ![1366936046/1000000000,778595795/1000000000,802609647/1000000000,
    640396588/1000000000,875421590/1000000000,681426094/1000000000]
def initialLower : Row→ℝ :=
  ![89758/100000,89835/100000,89810/100000,89811/100000,89813/100000,92987/100000]

lemma source_lower (r : Row) : sourceLower r≤ sourceBound r := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have haxial : sourceLower r≤p r*outerAxial := by
    fin_cases r <;> norm_num [sourceLower,p] <;> linarith
  have hd' : (899214065/1000000000:ℝ)<outerDiagonal := by
    rw [outerDiagonal,lt_sub_iff_add_lt,Real.lt_sqrt (by norm_num)]
    norm_num [Q0]
  have hdiagonal : r≠1→sourceLower r≤(p r+weight r-q r)*outerDiagonal := by
    intro hr
    fin_cases r <;> first | exact absurd rfl hr | (norm_num [sourceLower,p,q,weight]; linarith)
  by_cases hr : r=1
  · simpa [sourceBound,hr] using haxial
  · rw [sourceBound]
    simp only [hr,↓reduceIte]
    exact le_min haxial (hdiagonal hr)

lemma initial_norm (r : Row) (high : Bool) : N r high 0< initialNormUpper r := by
  have hn := norm_initial r high
  have hp := norm_positive r high (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  fin_cases r <;> norm_num [initialNormUpper,P,t,weight] at hn ⊢ <;> nlinarith

lemma final_norm (r : Row) : N r false (7/10)<finalNormUpper r := by
  have hn := norm_sq r false (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hp := norm_positive r false (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have ht := RoleFour.fine_cap_trig
  fin_cases r <;> norm_num [finalNormUpper,P,t,weight,Unit.direction] at hn ⊢ <;>
    nlinarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

lemma initial_product (r : Row) (high : Bool) :
    radius*N r high 0<radiusUpper*initialNormUpper r := by
  have hR : radius≤radiusUpper := by
    have h := RoleFour.radius_upper
    rw [show radiusUpper=(1978788/1000000:ℝ) by norm_num [radiusUpper]]
    exact h.le
  exact (mul_le_mul_of_nonneg_right hR
    (norm_positive r high (show (0:ℝ)∈Icc 0 (7/10) by norm_num)).le).trans_lt
      (mul_lt_mul_of_pos_left (initial_norm r high) (by norm_num [radiusUpper] : (0:ℝ)<radiusUpper))

lemma final_product (r : Row) : radius*N r false (7/10)<radiusUpper*finalNormUpper r := by
  have hR : radius≤radiusUpper := by
    have h := RoleFour.radius_upper
    rw [show radiusUpper=(1978788/1000000:ℝ) by norm_num [radiusUpper]]
    exact h.le
  exact (mul_le_mul_of_nonneg_right hR
    (norm_positive r false (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num)).le).trans_lt
      (mul_lt_mul_of_pos_left (final_norm r) (by norm_num [radiusUpper] : (0:ℝ)<radiusUpper))

lemma initial_value (r : Row) (high : Bool) : initialLower r<value r high 0 := by
  have hs := source_lower r
  have hn := initial_product r high
  have hp := pi_hand_enclosure.1
  fin_cases r <;> norm_num [value,c,P,t,weight,sourceLower,initialNormUpper,
    initialLower,radiusUpper] at hs hn ⊢ <;> linarith

lemma initial_threshold (r : Row) (high : Bool) : threshold r<value r high 0 := by
  have hh := initial_value r high
  have hle : threshold r≤ initialLower r := by fin_cases r <;> norm_num [threshold,initialLower]
  exact hle.trans_lt hh

lemma final_value (r : Row) : (497/500:ℝ)<value r false (7/10) := by
  have hs := source_lower r
  have hn := final_product r
  have hp := pi_hand_enclosure.1
  have hc := RoleFour.fine_cap_trig.2.2.1
  fin_cases r <;> norm_num [value,c,P,t,weight,Unit.direction,sourceLower,
    finalNormUpper,radiusUpper] at hs hn ⊢ <;> linarith

lemma initial_curvature_reserve (r : Row) : (11/1000:ℝ)<4*weight r-radius*N r false 0 := by
  have hh := initial_product r false
  have hrat : (11/1000:ℝ)<4*weight r-radiusUpper*initialNormUpper r := by
    fin_cases r <;> norm_num [weight,radiusUpper,initialNormUpper]
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary.Endpoint
end
end
end

section
/-!
## Whole negative-half concavity of the opposite secondary supports

The exact squared-norm difference retains the cosine factor. The two
signs of the fixed coefficient use the stated bounds for 1-cos, giving
N(u) ≤ N(0) cos(u). The circle-norm identity then proves concavity on
the entire original negative angle half.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary.Negative
open CommonQuarter CorePairGeometry Arithmetic

def D (r : Row) : ℝ := if 0≤P r then (P r+weight r)^2+(t r)^2-weight r*P r
  else (P r+weight r)^2+(t r)^2-2*weight r*P r/(441/250)

lemma coefficients (r : Row) : 0<D r ∧ (267/1000:ℝ)<2*weight r*t r-(129/200)*D r := by
  fin_cases r <;> norm_num [D,P,t,weight]

lemma norm_defect (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r false x)^2-(N r false 0)^2*(Real.cos x)^2=
      (N r false 0)^2*(Real.sin x)^2-2*weight r*P r*(1-Real.cos x)-
        2*weight r*t r*Real.sin x := by
  have hn := norm_sq r false hx
  have h0 := norm_initial r false
  dsimp [Unit.direction] at hn
  linear_combination hn-h0-(N r false 0)^2*(Real.sin_sq_add_cos_sq x)

lemma cos_defect_bounds {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (Real.sin x)^2/2≤1-Real.cos x ∧ 1-Real.cos x≤(Real.sin x)^2/(441/250:ℝ) := by
  have ht := positive_trig hx
  have hc := Real.sin_sq_add_cos_sq x
  have hnonneg : 0≤1-Real.cos x := by linarith [ht.2.1]
  have hp := mul_nonneg hnonneg (show 0≤Real.cos x-191/250 by linarith [ht.1])
  constructor
  · nlinarith [sq_nonneg (1-Real.cos x)]
  · norm_num
    nlinarith

lemma norm_defect_upper (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r false x)^2-(N r false 0)^2*(Real.cos x)^2≤
      Real.sin x*(D r*Real.sin x-2*weight r*t r) := by
  have hdef := norm_defect r hx
  have hc := cos_defect_bounds hx
  have h0 := norm_initial r false
  have h0s := congrArg (fun z : ℝ => z*(Real.sin x)^2) h0
  by_cases hP : 0≤P r
  · have hcoef : -2*weight r*P r≤0 := by
      have hp := mul_nonneg (coefficient_bounds r).1.le hP
      nlinarith
    have hm := mul_le_mul_of_nonpos_left hc.1 hcoef
    rw [D,ite_eq_left hP]
    nlinarith only [hdef,hm,h0s]
  · have hcoef : 0≤-2*weight r*P r := by
      have hp := mul_nonpos_of_nonneg_of_nonpos (coefficient_bounds r).1.le (le_of_not_ge hP)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hc.2 hcoef
    rw [D,ite_eq_right hP]
    nlinarith only [hdef,hm,h0s]

lemma norm_cos_bound (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    N r false x≤N r false 0*Real.cos x := by
  have ht := positive_trig hx
  have hcoef := coefficients r
  have hsin : Real.sin x≤(129/200:ℝ) := by linarith [ht.2.2.2.1]
  have hDs := mul_le_mul_of_nonneg_left hsin hcoef.1.le
  have hinside : D r*Real.sin x-2*weight r*t r≤0 := by linarith [hcoef.2]
  have hright := mul_nonpos_of_nonneg_of_nonpos ht.2.2.1 hinside
  have hdef := norm_defect_upper r hx
  have hN0 := norm_positive r false (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  have hN := norm_positive r false hx
  have hrightPos := mul_pos hN0 (show 0<Real.cos x by linarith [ht.1])
  nlinarith

lemma curvature_negative (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) : second r false x<0 := by
  have hcoef : (normB r)^2+(normC r false)^2≤(normA r)^2 := by
    fin_cases r <;> norm_num [normA,normB,normC,P,t,weight,Unit.direction]
  have hn := CircularNorm.curvature_lower (norm_energy_positive r false hx) hcoef
  have hm := mul_le_mul_of_nonneg_left hn RoleFour.radius_positive.le
  have hmul : -radius*N r false x/4≤radius*CircularNorm.d2 (normA r) (normB r) (normC r false) x := by
    have e : N r false x=CircularNorm.norm (normA r) (normB r) (normC r false) x := rfl
    rw [e]
    linarith [hm]
  have hnorm := mul_le_mul_of_nonneg_left (norm_cos_bound r hx) RoleFour.radius_positive.le
  have hreserve := Endpoint.initial_curvature_reserve r
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  have hnegative := mul_neg_of_pos_of_neg hc
    (show -weight r+radius*N r false 0/4<0 by linarith)
  dsimp [second,Unit.direction]
  nlinarith only [hmul,hnorm,hnegative]

theorem value_concave (r : Row) : ConcaveOn ℝ (Icc 0 (7/10)) (value r false) :=
  concave_of_deriv2 (fun _ hx => value_hasDerivAt r false hx)
    (fun _ hx => first_hasDerivAt r false hx) (fun _ hx => (curvature_negative r hx).le)

theorem value_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) : threshold r<value r false x := by
  apply concave_gt_of_endpoints (value_concave r) hx
  · exact Endpoint.initial_threshold r false
  · have hh := Endpoint.final_value r
    have hth : threshold r≤(497/500:ℝ) := by fin_cases r <;> norm_num [threshold]
    exact hth.trans_lt hh

end SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary.Negative
end
end
end

section
/-!
## The common positive-half quadratic for opposite secondary owners

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
  (fun _ hx => (value_hasDerivAt r true hx).continuousAt.continuousWithinAt)
  (fun _ hx => value_hasDerivAt r true (Ioo_subset_Icc_self hx))
  (fun _ hx => (first_positive r (Ioo_subset_Icc_self hx)).le)

end SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary.Positive
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

lemma margin (high : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 (Unit.angle high x)) :
    (1+Real.cos x+Real.sin x)/2≤ -b+A*Real.cos x+Unit.direction high*B*Real.sin x := by
  have hw := quarter_width (x:=Unit.direction high*x)
    (by cases high <;> simpa [Unit.direction,abs_of_nonneg hx.1,abs_neg] using hx.2)
  have hs := (positive_trig hx).2.2.1
  cases high <;>
    norm_num [Unit.angle,Unit.direction,Eight.forwardMargin,Real.sin_add,Real.cos_add,
      Real.sin_neg,Real.cos_neg,abs_of_nonneg hs,abs_neg] at hm hw ⊢ <;> linarith

theorem normalized (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 φ) :
    threshold r<φ+c r+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hm' := margin high hx hm
  have hv : threshold r<value r high x := by
    cases high
    · exact Negative.value_lower r hx
    · exact (Endpoint.initial_threshold r true).trans_le
        (Positive.value_monotone r (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1)
  exact hv.trans_le (original_support r high hs ht hm')

def OriginalOwner (i : Vertex) (j : Fin 4) : Prop := (i=2 ∨ i=4 ∨ i=6) ∧ (j=0 ∨ j=2)

theorem original_owner (i : Vertex) (j : Fin 4) (hrole : OriginalOwner i j)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (WordProblems.wrongGamma .short i:ℝ)<φ+wrongValue .short i .outer false a b-
      wrongValue .short (next i) .outer true A B := by
  rcases hrole with ⟨hi,hj⟩
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl
  · have hh := normalized 0 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 1 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 2 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 3 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 4 hs ht hφ hm
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith
  · have hh := normalized 5 ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
      threshold,c,p,q,P,t] at *
    linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (_hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true) (j : Fin 4)
    (hrole : OriginalOwner i j)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hm := original_margin C F hgap i j howner
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hh := original_owner i j hrole hsource htarget
    hφ (by simpa [hσ,hτ,WordProblems.sign] using hm)
  simpa only [wrongMarker,hs,ht,hσ,hτ] using hh

end SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary
end
end
end
