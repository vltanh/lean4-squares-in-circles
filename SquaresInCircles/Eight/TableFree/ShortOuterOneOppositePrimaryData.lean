module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameData
public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterReferences
public import SquaresInCircles.Eight.TableFree.WrongWordCircleSupport

/-!
# Literal data for the six original opposite primary owners

Uncompiled transcription of the three opposite-primary hand notes.
The row order is (edge 2, axis 2), (edge 2, axis 4), then the same two
axes on edges 4 and 6. Axis 2 is reflected and reversed exactly once;
the resulting source-primary separator has signs (-,+). No original
owner is reselected.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

abbrev Row := Fin 6
def c : Row→ℝ := ![6618/10000,6618/10000,-25931/100000,-25931/100000,-1866/10000,-1866/10000]
def p : Row→ℝ := ![-51554/100000,9133/100000,0,19335/100000,0,18602/100000]
def q : Row→ℝ := ![119909/100000,88074/100000,86884/100000,76744/100000,94766/100000,80996/100000]
def P : Row→ℝ := ![-9133/100000,51554/100000,-19335/100000,0,-18602/100000,0]
def t : Row→ℝ := ![88074/100000,119909/100000,76744/100000,86884/100000,80996/100000,94766/100000]
def threshold (r : Row) : ℝ := if r<2 then 359/400 else 17953/20000
def rho : ℝ := 1/(2*(outerAxial+1/2))
def width (x : ℝ) : ℝ := (1+Real.cos x+Real.sin x)/2
def cost (r : Row) (high : Bool) (a b A B x : ℝ) : ℝ :=
  Unit.angle high x+c r+p r*a-q r*b-P r*A-t r*B
def source (r : Row) (a : ℝ) : ℝ := p r*a-q r*arc a
def sourceD (r : Row) (a : ℝ) : ℝ := p r+q r*ratio a
def sourceDD (r : Row) (a : ℝ) : ℝ := q r*ratioD a
def target (r : Row) (B : ℝ) : ℝ := -P r*arc B-t r*B
def targetD (r : Row) (B : ℝ) : ℝ := P r*ratio B-t r

theorem coefficients (r : Row) :
    (76744/100000:ℝ)≤q r ∧ q r≤119909/100000 ∧
      (68355/100000:ℝ)≤p r+q r ∧
      -(19335/100000:ℝ)≤P r ∧ P r≤51554/100000 ∧ 0<t r ∧ P r<t r := by
  fin_cases r <;> norm_num [p,q,P,t]

theorem rho_bounds : (5223/20000:ℝ)<rho ∧ rho<131/500 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hh : 0<2*(outerAxial+1/2) := by linarith [ha.1]
  constructor
  · apply (lt_div_iff₀ hh).2
    linarith [ha.2]
  · apply (div_lt_iff₀ hh).2
    linarith [ha.1]

theorem rho_identity : (outerAxial+1/2)*rho=1/2 := by
  have h : outerAxial+1/2≠0 := (by linarith [outer_endpoint_bounds.1] : (0:ℝ)<outerAxial+1/2).ne'
  rw [rho,mul_one_div,mul_comm 2,div_mul_eq_div_div,div_self h]

theorem ratio_zero : ratio 0=rho := by
  rw [ratio,SameContact.arc_zero,rho,zero_add,div_div]

theorem ratio_diagonal : ratio outerDiagonal=1 := by
  rw [ratio,SameContact.arc_diagonal]
  exact div_self (by linarith [outer_endpoint_bounds.2.2.1])

theorem target_ratio {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : rho≤ratio B ∧ ratio B≤1 := by
  have hlo := SameContact.ratio_monotone
    (show (0:ℝ)∈Icc 0 outerAxial from ⟨le_rfl,by linarith [outer_endpoint_bounds.1]⟩)
    (SameContact.outer_domain hB) hB.1
  rw [ratio_zero] at hlo
  have hs := SameContact.arc_state hB
  have hp := SameContact.shifted_positive (SameContact.outer_domain hB)
  exact ⟨hlo,(div_le_one hp).2 (by linarith [hs.2.1])⟩

theorem source_hasDerivAt (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (source r) (sourceD r a) a := by
  have hh := ((hasDerivAt_id' a).const_mul (p r)).fun_sub
    ((SameContact.arc_hasDerivAt (Same.primary_domain ha)).const_mul (q r))
  exact hh.congr_deriv (by simp only [sourceD]; ring)
theorem sourceD_hasDerivAt (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (sourceD r) (sourceDD r a) a :=
  ((SameContact.ratio_hasDerivAt (Same.primary_domain ha)).const_mul (q r)).const_add (p r)
theorem sourceD_lower (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) : p r+q r≤ sourceD r a := by
  have hh := mul_le_mul_of_nonneg_left (Same.primary_ratio_lower ha)
    (show 0≤q r by linarith [(coefficients r).1])
  dsimp [sourceD]
  linarith
theorem source_monotone (r : Row) : MonotoneOn (source r) (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (source_hasDerivAt r ha).continuousAt.continuousWithinAt)
    (fun a ha => source_hasDerivAt r (Ioo_subset_Icc_self ha))
    (fun a ha => by linarith [sourceD_lower r (Ioo_subset_Icc_self ha),(coefficients r).2.2.1])
theorem source_identity (r : Row) {a b : ℝ} (hs : OuterState a b) : source r a=p r*a-q r*b := by
  rw [source,(SameContact.actual_arc hs).2]

theorem target_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (target r) (targetD r B) B := by
  have hh := ((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).const_mul (-P r)).fun_sub
    ((hasDerivAt_id' B).const_mul (t r))
  exact hh.congr_deriv (by simp only [targetD]; ring)
theorem targetD_negative (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : targetD r B<0 := by
  have hrat := target_ratio hB
  have hpos : 0≤ratio B := by linarith [hrat.1,rho_bounds.1]
  by_cases hP : P r≤0
  · have hh := mul_nonpos_of_nonpos_of_nonneg hP hpos
    dsimp [targetD]
    linarith [(coefficients r).2.2.2.2.2.1]
  · have hh := mul_le_mul_of_nonneg_left hrat.2 (lt_of_not_ge hP).le
    dsimp [targetD]
    linarith [(coefficients r).2.2.2.2.2.2]
theorem target_antitone (r : Row) : AntitoneOn (target r) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun B hB => (target_hasDerivAt r hB).continuousAt.continuousWithinAt)
    (fun B hB => target_hasDerivAt r (Ioo_subset_Icc_self hB))
    (fun B hB => (targetD_negative r (Ioo_subset_Icc_self hB)).le)

theorem normalized_margin (high : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Unit.angle high x)) :
    width x≤a+Unit.direction high*A*Real.sin x-B*Real.cos x := by
  have hw := quarter_width (x:=Unit.direction high*x)
    (by cases high <;> simpa [Unit.direction,abs_of_nonneg hx.1,abs_neg] using hx.2)
  have hs := (positive_trig hx).2.2.1
  cases high <;>
    norm_num [width,Unit.angle,Unit.direction,Eight.forwardMargin,Real.sin_add,Real.cos_add,
      Real.sin_neg,Real.cos_neg,abs_of_nonneg hs,abs_neg] at hm hw ⊢ <;> linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary
