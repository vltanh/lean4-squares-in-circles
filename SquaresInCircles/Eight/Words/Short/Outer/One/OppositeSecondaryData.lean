module

public import SquaresInCircles.Eight.Words.Short.Outer.One.RoleFourNorm
public import SquaresInCircles.Eight.Words.Short.Outer.One.UnitScalars
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositePositiveCap

/-!
# Eight squares: the six exact opposite-sign secondary supports

Each row retains its own fixed multiplier and its literal adjacent
role coefficients. Source supports are the two concave endpoints,
except for the single negative-primary row whose source increases.
The concluding support inequality uses the original weak separator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport
open SameContact (arc ratio)

abbrev Row := Fin 6
def c : Row→ℝ := ![6618/10000,6618/10000,-25931/100000,-25931/100000,-1866/10000,-1866/10000]
def p : Row→ℝ := ![9133/100000,-51554/100000,19335/100000,0,18602/100000,0]
def q : Row→ℝ := ![88074/100000,119909/100000,76744/100000,86884/100000,80996/100000,94766/100000]
def P : Row→ℝ := ![51554/100000,-9133/100000,0,-19335/100000,0,-18602/100000]
def t : Row→ℝ := ![119909/100000,88074/100000,86884/100000,76744/100000,94766/100000,80996/100000]
def weight : Row→ℝ := ![93308/100000,111499/100000,100982/100000,108532/100000,110143/100000,112741/100000]
def threshold (r : Row) : ℝ := if r.val<2 then 359/400 else 17953/20000
def source (r : Row) (b : ℝ) : ℝ := p r*arc b+(weight r-q r)*b
def sourceBound (r : Row) : ℝ := if r=1 then p r*outerAxial
  else min (p r*outerAxial) ((p r+weight r-q r)*outerDiagonal)
abbrev radius := RoleFour.radius
def radiusUpper : ℝ := 494697/250000
def normA (r : Row) : ℝ := (P r)^2+(t r)^2+(weight r)^2
def normB (r : Row) : ℝ := 2*weight r*P r
def normC (r : Row) (high : Bool) : ℝ := 2*weight r*Unit.direction high*t r
def N (r : Row) (high : Bool) (x : ℝ) : ℝ := CircularNorm.norm (normA r) (normB r) (normC r high) x
def value (r : Row) (high : Bool) (x : ℝ) : ℝ :=
  Real.pi/2+Unit.direction high*x+c r+sourceBound r+(weight r+P r+t r)/2+
    weight r*Real.cos x+(1+Unit.direction high)/2*weight r*Real.sin x-radius*N r high x
def first (r : Row) (high : Bool) (x : ℝ) : ℝ :=
  Unit.direction high-weight r*Real.sin x+(1+Unit.direction high)/2*weight r*Real.cos x-
    radius*CircularNorm.d1 (normA r) (normB r) (normC r high) x
def second (r : Row) (high : Bool) (x : ℝ) : ℝ :=
  -weight r*Real.cos x-(1+Unit.direction high)/2*weight r*Real.sin x-
    radius*CircularNorm.d2 (normA r) (normB r) (normC r high) x

lemma coefficient_bounds (r : Row) : 0<weight r ∧ 0<t r ∧ 0<weight r+min (P r) 0 ∧ 0<t r-P r := by
  fin_cases r <;> norm_num [weight,t,P]

lemma fine_ratio_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (5223/20000:ℝ)<ratio b := by
  have hU := SecondWord.U_positive (SameContact.outer_domain hb)
  dsimp only [SecondWord.U] at hU
  have hA := (outer_bounds (SameContact.arc_state hb)).2.1
  have ha := ShortOuterZero.fine_axial_bounds.2
  change (5223/20000:ℝ)<(b+1/2)/(arc b+1/2)
  apply (lt_div_iff₀ hU).2
  linarith [hb.1]

lemma source_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (source r) (-p r*ratio b+weight r-q r) b := by
  have h := ((SameContact.arc_hasDerivAt (SameContact.outer_domain hb)).const_mul (p r)).fun_add
    ((hasDerivAt_id' b).const_mul (weight r-q r))
  exact h.congr_deriv (by ring)

lemma negative_source_monotone : MonotoneOn (source 1) (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun b hb => (source_hasDerivAt 1 hb).continuousAt.continuousWithinAt)
    (fun b hb => source_hasDerivAt 1 (Ioo_subset_Icc_self hb))
  intro b hb
  have hr := fine_ratio_lower (Ioo_subset_Icc_self hb)
  norm_num [p,weight,q]
  linarith

lemma source_support (r : Row) {a b : ℝ} (hs : OuterState a b) :
    sourceBound r≤p r*a+(weight r-q r)*b := by
  by_cases hrow : r=1
  · subst r
    have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
    have hh := negative_source_monotone
      (show (0:ℝ)∈Icc 0 outerDiagonal from ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩)
      hb hb.1
    simpa [sourceBound,source,SameContact.arc_zero,(SameContact.actual_arc hs).1] using hh
  · have hp : 0≤p r := by
      fin_cases r <;> first | exact absurd rfl hrow | norm_num [p]
    dsimp only [sourceBound]
    simp only [hrow,↓reduceIte]
    exact outer_concave_lower hs hp (min_le_left _ _) (by
      have hh := min_le_right (p r*outerAxial) ((p r+weight r-q r)*outerDiagonal)
      nlinarith only [hh])

lemma norm_energy_identity (r : Row) (high : Bool) (x : ℝ) :
    CircularNorm.energy (normA r) (normB r) (normC r high) x=
      (P r+weight r*Real.cos x)^2+(t r+Unit.direction high*weight r*Real.sin x)^2 := by
  cases high <;> dsimp [CircularNorm.energy,normA,normB,normC,Unit.direction] <;>
    linear_combination -(weight r)^2*(Real.sin_sq_add_cos_sq x)

lemma negative_vertical (r : Row) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (67/1000:ℝ)<t r-weight r*Real.sin x := by
  have ht := (positive_trig hx).2.2.2.1
  fin_cases r <;> norm_num [t,weight] <;> linarith

lemma norm_energy_positive (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<CircularNorm.energy (normA r) (normB r) (normC r high) x := by
  rw [norm_energy_identity]
  have hv : 0<t r+Unit.direction high*weight r*Real.sin x := by
    cases high
    · norm_num [Unit.direction]
      linarith [negative_vertical r hx]
    · have hs := mul_nonneg (coefficient_bounds r).1.le (positive_trig hx).2.2.1
      norm_num [Unit.direction]
      linarith [(coefficient_bounds r).2.1]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hv)

lemma norm_positive (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<N r high x :=
  CircularNorm.norm_pos (norm_energy_positive r high hx)

lemma norm_sq (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N r high x)^2=(P r)^2+(t r)^2+(weight r)^2+
      2*weight r*(P r*Real.cos x+Unit.direction high*t r*Real.sin x) := by
  have hh := CircularNorm.norm_sq (norm_energy_positive r high hx).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy,normA,normB,normC] <;> ring

lemma norm_initial (r : Row) (high : Bool) :
    (N r high 0)^2=(P r+weight r)^2+(t r)^2 := by
  have hh := norm_sq r high (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
  norm_num at hh
  nlinarith only [hh]

lemma value_hasDerivAt (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (value r high) (first r high x) x := by
  have h := (((((hasDerivAt_id' x).const_mul (Unit.direction high)).const_add
    (Real.pi/2+c r+sourceBound r+(weight r+P r+t r)/2)).fun_add
      ((Real.hasDerivAt_cos x).const_mul (weight r))).fun_add
        ((Real.hasDerivAt_sin x).const_mul ((1+Unit.direction high)/2*weight r))).fun_sub
          ((CircularNorm.norm_hasDerivAt (norm_energy_positive r high hx)).const_mul radius)
  convert h using 1
  · funext y
    simp only [value,N]
    ring
  · simp only [first]
    ring

lemma first_hasDerivAt (r : Row) (high : Bool) {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt (first r high) (second r high x) x := by
  have h := (((((Real.hasDerivAt_sin x).const_mul (weight r)).neg).const_add
    (Unit.direction high)).fun_add
      ((Real.hasDerivAt_cos x).const_mul ((1+Unit.direction high)/2*weight r))).fun_sub
        ((CircularNorm.d1_hasDerivAt (norm_energy_positive r high hx)).const_mul radius)
  convert h using 1
  · funext y
    simp only [first,Pi.neg_apply]
    ring
  · simp only [second]
    ring

lemma norm_coefficients (r : Row) (high : Bool) (x : ℝ) :
    Real.sqrt ((-P r-weight r*Real.cos x)^2+
      (-t r-Unit.direction high*weight r*Real.sin x)^2)=N r high x := by
  unfold N CircularNorm.norm
  rw [norm_energy_identity]
  congr 1
  ring

theorem original_support (r : Row) (high : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hm : (1+Real.cos x+Real.sin x)/2≤ -b+A*Real.cos x+Unit.direction high*B*Real.sin x) :
    value r high x≤Real.pi/2+Unit.direction high*x+c r+p r*a-q r*b-P r*A-t r*B := by
  have hmargin := mul_le_mul_of_nonneg_left hm (coefficient_bounds r).1.le
  have hsource := source_support r hs
  have htarget := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
    (X:=-P r-weight r*Real.cos x) (Y:=-t r-Unit.direction high*weight r*Real.sin x) ht
  rw [norm_coefficients] at htarget
  dsimp [value]
  nlinarith only [hmargin,hsource,htarget]

end SquaresInCircles.Eight.ShortOuterOne.OppositeSecondary
