module

public import SquaresInCircles.Eight.Frames.High.HighVaryingReferences
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCorePrimaryPositive

/-!
# Eight squares: the six original negative-core primary rows and their source circle

The continued primary chart is the original shifted circle, including
its axial endpoint. Its increasing source label also applies below the
physical diagonal when an actual contact requires that continuation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives Reference

def Remaining (r : Row) : Prop := sourcePositive r=false ∧ targetPositive r=false
def lowerAngle : ℝ := Real.pi/2-7/10
def HeightRange (u : ℝ) : Prop := u∈Icc (33/25) (17/10)
def SourceDomain (a : ℝ) : Prop := a∈Icc (41/50) outerAxial
def v (u : ℝ) : ℝ := Real.sqrt (Q0-u^2)
def M (r : Row) (a : ℝ) : ℝ := ocP r*a-ocQ r*(v (a+1/2)-1/2)
def M1 (r : Row) (a : ℝ) : ℝ := ocP r+ocQ r*(a+1/2)/v (a+1/2)
def M2 (r : Row) (a : ℝ) : ℝ := ocQ r*Q0/(v (a+1/2))^3

theorem remaining_iff (r : Row) : Remaining r↔r=0 ∨ r=4 ∨ r=11 ∨ r=12 ∨ r=19 ∨ r=23 := by
  fin_cases r <;> norm_num [Remaining,sourcePositive,targetPositive]

theorem coefficients (r : Row) (hr : Remaining r) :
    (767/1000:ℝ)<ocQ r ∧ 0<ocG r ∧ ocG r<1139/1000 ∧
      -(263/1000)*ocQ r<ocP r ∧ ocP r<(253/1000)*ocQ r := by
  rcases (remaining_iff r).1 hr with rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [ocP,ocQ,ocG]

theorem primary_cost (r : Row) (hr : Remaining r) (a b A B φ : ℝ) :
    outerCoreCost r a b A B φ=φ+ocC r+ocP r*a-ocQ r*b+ocG r*B := by
  simp [outerCoreCost,sourceSign,targetSign,WordProblems.sign,hr.1,hr.2]
  ring
theorem primary_separator (r : Row) (hr : Remaining r) (a b A B φ : ℝ) :
    sourcePrimary r a b A B φ↔pairWidth φ≤a-A*Real.cos φ+B*Real.sin φ := by
  simp [sourcePrimary,targetSign,WordProblems.sign,hr.2]

theorem source_radicand {a : ℝ} (ha : SourceDomain a) : 1/4≤Q0-(a+1/2)^2 := by
  have hax := axial_circle
  have hprod := mul_nonneg (show 0≤outerAxial-a by linarith [ha.2])
    (show 0≤outerAxial+a+1 by linarith [ha.1,outer_endpoint_bounds.1])
  nlinarith
theorem source_v_positive {a : ℝ} (ha : SourceDomain a) : 0<v (a+1/2) := by
  exact Real.sqrt_pos.mpr (by linarith [source_radicand ha])
theorem source_v_square {a : ℝ} (ha : SourceDomain a) : (v (a+1/2))^2=Q0-(a+1/2)^2 :=
  Real.sq_sqrt (by linarith [source_radicand ha])
theorem source_v_bounds {a : ℝ} (ha : SourceDomain a) :
    1/2≤v (a+1/2) ∧ v (a+1/2)<59/40 ∧ (89/100)*v (a+1/2)<a+1/2 := by
  have hp := source_v_positive ha
  have hsq := source_v_square ha
  have hrad := source_radicand ha
  have hu : (33/25:ℝ)≤a+1/2 := by linarith [ha.1]
  have hu2 := mul_nonneg (show 0≤a+1/2-33/25 by linarith)
    (show 0≤a+1/2+33/25 by linarith)
  norm_num [Q0] at hsq hrad
  refine ⟨?_,?_,?_⟩
  · by_contra! h
    nlinarith [mul_lt_mul'' h h hp.le hp.le]
  · by_contra! h
    nlinarith [mul_le_mul h h (by norm_num) hp.le]
  · by_contra! h
    nlinarith [mul_le_mul h h (by linarith) (by linarith)]

theorem height_source_domain {u : ℝ} (hu : HeightRange u) : SourceDomain (u-1/2) := by
  constructor
  · linarith [hu.1]
  · linarith [hu.2,ShortOuterZero.fine_axial_bounds.1]
theorem height_v_bounds {u : ℝ} (hu : HeightRange u) : (101/100:ℝ)<v u ∧ v u<59/40 := by
  have hd := height_source_domain hu
  have hp := source_v_positive hd
  have he := source_v_square hd
  have hb := source_v_bounds hd
  simp only [sub_add_cancel] at hp he hb
  have hu2 := mul_nonneg (show 0≤17/10-u by linarith [hu.2])
    (show 0≤17/10+u by linarith [hu.1])
  norm_num [Q0] at he
  exact ⟨by nlinarith,hb.2.1⟩

theorem v_hasDerivAt {u : ℝ} (hu : 0<Q0-u^2) : HasDerivAt v (-u/v u) u := by
  convert (((hasDerivAt_const u Q0).sub ((hasDerivAt_id u).pow 2)).sqrt (ne_of_gt hu)) using 1
  · rfl
  · dsimp [v]
    field_simp [(Real.sqrt_pos.mpr hu).ne']
    ring
theorem M_hasDerivAt (r : Row) {a : ℝ} (ha : SourceDomain a) :
    HasDerivAt (M r) (M1 r a) a := by
  have hv : HasDerivAt (fun x => v (x+1/2)) (-(a+1/2)/v (a+1/2)) a :=
    HasDerivAt.comp_add_const a (1/2) (v_hasDerivAt (by linarith [source_radicand ha]))
  have h : HasDerivAt (fun x => ocP r*x-ocQ r*(v (x+1/2)-1/2))
      (ocP r*1-ocQ r*(-(a+1/2)/v (a+1/2))) a :=
    ((hasDerivAt_id' a).const_mul (ocP r)).sub ((hv.sub_const (1/2)).const_mul (ocQ r))
  exact h.congr_deriv (by simp only [M1]; ring)
theorem M1_hasDerivAt (r : Row) {a : ℝ} (ha : SourceDomain a) :
    HasDerivAt (M1 r) (M2 r a) a := by
  have hp := source_v_positive ha
  have he := source_v_square ha
  have hv : HasDerivAt (fun x => v (x+1/2)) (-(a+1/2)/v (a+1/2)) a :=
    HasDerivAt.comp_add_const a (1/2) (v_hasDerivAt (by linarith [source_radicand ha]))
  have h : HasDerivAt (fun x => ocP r+ocQ r*(x+1/2)/v (x+1/2))
      (0+(ocQ r*1*v (a+1/2)-ocQ r*(a+1/2)*(-(a+1/2)/v (a+1/2)))/v (a+1/2)^2) a :=
    (hasDerivAt_const a (ocP r)).add
      ((((hasDerivAt_id' a).add_const (1/2)).const_mul (ocQ r)).div hv hp.ne')
  refine h.congr_deriv ?_
  simp only [M2]
  generalize v (a+1/2) = w at hp he ⊢
  rw [show Q0=w^2+(a+1/2)^2 by linarith]
  field_simp
  ring
theorem M1_positive (r : Row) (hr : Remaining r) {a : ℝ} (ha : SourceDomain a) : 0<M1 r a := by
  have hc := coefficients r hr
  have hv := source_v_positive ha
  have hb := (source_v_bounds ha).2.2
  have hq := mul_lt_mul_of_pos_left hb (show 0<ocQ r by linarith [hc.1])
  have h1 : ocQ r*(89/100)<ocQ r*(a+1/2)/v (a+1/2) := by
    rw [lt_div_iff₀ hv]
    linarith
  simp only [M1]
  linarith [hc.1,hc.2.2.2.1]
theorem M_monotone (r : Row) (hr : Remaining r) : MonotoneOn (M r) (Icc (41/50) outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (M_hasDerivAt r ha).continuousAt.continuousWithinAt)
    (fun a ha => M_hasDerivAt r (Ioo_subset_Icc_self ha))
    (fun a ha => (M1_positive r hr (Ioo_subset_Icc_self ha)).le)

theorem source_identity (r : Row) {a b : ℝ} (hs : OuterState a b) :
    M r a=ocP r*a-ocQ r*b := by
  have hb : 0≤b+1/2 := by linarith [hs.1]
  have he : Q0-(a+1/2)^2=(b+1/2)^2 := by linarith [hs.2.2]
  dsimp [M,v]
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hb]
  ring
theorem actual_source_domain {a b : ℝ} (hs : OuterState a b) : SourceDomain a := by
  have hb := outer_bounds hs
  exact ⟨by linarith [hb.1,ShortMixedZero.fine_diagonal_bounds.1],hb.2.1⟩
theorem source_diagonal (r : Row) : M r outerDiagonal=(ocP r-ocQ r)*outerDiagonal := by
  have h := source_identity r (a:=outerDiagonal) (b:=outerDiagonal)
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl,by nlinarith [diagonal_circle]⟩
  nlinarith [h]

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative
