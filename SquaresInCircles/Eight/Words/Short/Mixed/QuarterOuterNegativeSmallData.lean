module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeGeometry

/-!
# Eight squares: the two small-slope side families and their intrinsic diagonal event

The only transition is where the active side join reaches the original
source diagonal. The source label decreases along the original active
contact until that diagonal or the target side join is reached.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SmallSide
open CommonQuarter CorePairGeometry Arithmetic Reference

def Rows (r : Row) : Prop := r=0∨r=11
def c0 : ℝ := 13/12
def eventSine : ℝ := (outerDiagonal-1/2)/c0
def IsEvent (e : ℝ) : Prop := e∈Icc 0 (2/5) ∧ Real.sin e=eventSine
def height (x B : ℝ) : ℝ := 1/2+c0*Real.sin x+(1/2-B)*Real.cos x
def cost (r : Row) (x B : ℝ) : ℝ := angle false x+ocC r+M r (height x B)+ocG r*B
def first (r : Row) (x B : ℝ) : ℝ := -M1 r (height x B)*Real.cos x+ocG r
def diagonalB (x : ℝ) : ℝ :=
  1/2-(outerDiagonal-1/2)/Real.cos x+c0*(Real.sin x/Real.cos x)
def diagonalCost (r : Row) (x : ℝ) : ℝ :=
  angle false x+ocC r+(ocP r-ocQ r)*outerDiagonal+ocG r*diagonalB x
def diagonalFirst (r : Row) (x : ℝ) : ℝ :=
  -1+ocG r*(c0-(outerDiagonal-1/2)*Real.sin x)/(Real.cos x)^2

theorem rows_remaining (r : Row) (hr : Rows r) : Remaining r := by
  rcases hr with rfl|rfl <;> norm_num [Remaining,sourcePositive,targetPositive]
theorem coefficient_reserves (r : Row) (hr : Rows r) :
    0<ocP r+ocQ r ∧ ocG r≤251/400 ∧
      ocG r<(191/250)*(ocP r+ocQ r) := by
  rcases hr with rfl|rfl <;> norm_num [ocP,ocQ,ocG]

theorem eventSine_bounds : 0<eventSine ∧ eventSine<37/100 := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [eventSine,c0]
  constructor <;> linarith [hd.1,hd.2]
theorem event_exists : ∃e,IsEvent e := by
  have hright : eventSine<Real.sin (2/5) :=
    eventSine_bounds.2.trans (by linarith [CorePrimaryPositive.sine_reference])
  obtain ⟨e,he,hzero⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤2/5)
    Real.continuous_sin.continuousOn
    (show eventSine∈Icc (Real.sin 0) (Real.sin (2/5)) by
      simpa using ⟨eventSine_bounds.1.le,hright.le⟩)
  exact ⟨e,he,hzero⟩
theorem event_domain {e : ℝ} (he : IsEvent e) : e∈Icc 0 (7/10) :=
  ⟨he.1.1,he.1.2.trans (by norm_num)⟩
theorem event_identity {e : ℝ} (he : IsEvent e) : c0*Real.sin e=outerDiagonal-1/2 := by
  rw [he.2]
  simp only [eventSine,c0]
  ring

theorem event_early {e : ℝ} (he : IsEvent e) : angle false e∈earlyAngles := by
  have hcos : Real.cos (6/5)<eventSine := by
    have hc := (cosine (by norm_num : (0:ℝ)≤6/5)).mem.2
    have hup : (cosine (by norm_num : (0:ℝ)≤6/5)).hi<(363/1000:ℝ) := by mixed_fixed
    have hd := ShortMixedZero.fine_diagonal_bounds.1
    dsimp [eventSine,c0]
    linarith
  have hp : Real.pi/2-6/5∈Icc 0 (7/10) := by
    constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]
  have hs : Real.sin (Real.pi/2-6/5)=Real.cos (6/5) := Real.sin_pi_div_two_sub (6/5)
  have hp_lt : Real.pi/2-6/5<e := by
    by_contra hn
    have hh := sin_mono (event_domain he) hp (le_of_not_gt hn)
    rw [he.2,hs] at hh
    linarith
  simp only [earlyAngles,angle,direction,lowerAngle,Bool.false_eq_true,↓reduceIte]
  constructor <;> linarith [he.1.2]

theorem height_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) : Antitone (height x) := by
  intro B D hBD
  have hc : 0≤Real.cos x := by linarith [(positive_trig hx).1]
  have hp := mul_le_mul_of_nonneg_right hBD hc
  dsimp [height]
  linarith
theorem height_zero {x : ℝ} (hx : x∈Icc 0 (7/10)) : 1≤height x 0 := by
  have ht := positive_trig hx
  have hc : 0≤Real.cos x := by linarith [ht.1]
  have hs : 0≤Real.sin x := ht.2.2.1
  have hsc := mul_nonneg hs hc
  have hu : 1≤Real.sin x+Real.cos x := by nlinarith [Real.sin_sq_add_cos_sq x]
  dsimp [height,c0]
  nlinarith
theorem diagonal_contact {x : ℝ} (hx : x∈Icc 0 (7/10)) : height x (diagonalB x)=outerDiagonal := by
  have hc : Real.cos x≠0 := ne_of_gt (by linarith [(positive_trig hx).1])
  dsimp [height,diagonalB]
  field_simp [hc]
  ring
theorem join_after_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    outerDiagonal≤height x (1/2) := by
  have hx0 : x∈Icc 0 (7/10) := ⟨(event_domain he).1.trans hx.1,hx.2⟩
  have hs := sin_mono (event_domain he) hx0 hx.1
  have hh := event_identity he
  dsimp [height,c0] at *
  nlinarith
theorem diagonal_at_event {e : ℝ} (he : IsEvent e) : diagonalB e=1/2 := by
  have hc : Real.cos e≠0 := ne_of_gt (by linarith [(positive_trig (event_domain he)).1])
  have hh := event_identity he
  dsimp [diagonalB]
  field_simp [hc]
  nlinarith

theorem source_slope (r : Row) (hr : Rows r) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    ocP r+ocQ r≤M1 r a := by
  have hd : SourceDomain a := ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.1],ha.2⟩
  have hv := source_v_positive hd
  have he := source_v_square hd
  have hu : 0≤a+1/2 := by linarith [ha.1,outer_endpoint_bounds.2.2.1]
  have hsq := mul_nonneg (sub_nonneg.mpr ha.1)
    (show 0≤a+outerDiagonal+1 by linarith [ha.1,outer_endpoint_bounds.2.2.1])
  have hratio : v (a+1/2)≤a+1/2 := by nlinarith [diagonal_circle]
  have hq : 0≤ocQ r := by linarith [(coefficients r (rows_remaining r hr)).1]
  have hp := mul_le_mul_of_nonneg_left hratio hq
  have hdiv : ocQ r≤ocQ r*(a+1/2)/v (a+1/2) := (le_div_iff₀ hv).2 hp
  dsimp [M1]
  linarith
theorem first_negative (r : Row) (hr : Rows r) {x B : ℝ}
    (hx : x∈Icc 0 (7/10)) (hh : height x B∈Icc outerDiagonal outerAxial) : first r x B<0 := by
  have hc := (positive_trig hx).1
  have hs := source_slope r hr hh
  have hp := mul_le_mul_of_nonneg_right hs (show 0≤Real.cos x by linarith)
  have hq := mul_lt_mul_of_pos_left hc (coefficient_reserves r hr).1
  dsimp [first]
  linarith [(coefficient_reserves r hr).1,(coefficient_reserves r hr).2.2]
theorem cost_hasDerivAt (r : Row) {x B : ℝ} (hh : SourceDomain (height x B)) :
    HasDerivAt (cost r x) (first r x B) B := by
  have hh' : HasDerivAt (height x) (-Real.cos x) B :=
    ((((hasDerivAt_id' B).const_sub (1/2)).mul_const (Real.cos x)).const_add
      (1/2+c0*Real.sin x)).congr_deriv (by ring)
  have h := (((M_hasDerivAt r hh).comp B hh').const_add (angle false x+ocC r)).fun_add
    ((hasDerivAt_id' B).const_mul (ocG r))
  exact h.congr_deriv (by simp only [first]; ring)

theorem active_descent (r : Row) (hr : Rows r) {x B D : ℝ}
    (hx : x∈Icc 0 (7/10)) (hBD : B≤D) (hl : outerDiagonal≤height x D)
    (hu : height x B≤outerAxial) : cost r x D≤cost r x B := by
  have hheight (Z : ℝ) (hZ : Z∈Icc B D) : height x Z∈Icc outerDiagonal outerAxial :=
    ⟨hl.trans (height_antitone hx hZ.2),(height_antitone hx hZ.1).trans hu⟩
  have hdomain (Z : ℝ) (hZ : Z∈Icc B D) : SourceDomain (height x Z) :=
    ⟨by linarith [(hheight Z hZ).1,outer_endpoint_bounds.2.2.1],(hheight Z hZ).2⟩
  have hm : AntitoneOn (cost r x) (Icc B D) :=
    antiOn_of_hasDeriv_nonpos
      (fun Z hZ => (cost_hasDerivAt r (hdomain Z hZ)).continuousAt.continuousWithinAt)
      (fun Z hZ => cost_hasDerivAt r (hdomain Z (Ioo_subset_Icc_self hZ)))
      (fun Z hZ => (first_negative r hr hx (hheight Z (Ioo_subset_Icc_self hZ))).le)
  exact hm ⟨le_rfl,hBD⟩ ⟨hBD,le_rfl⟩ hBD

theorem original_height (r : Row) (hr : Rows r) {a b B x : ℝ}
    (hx : x∈Icc 0 (7/10)) (hm : sourcePrimary r a b (7/12) B (angle false x)) : height x B≤a := by
  rw [primary_separator r (rows_remaining r hr)] at hm
  rw [angle_width false hx,angle_sin,angle_cos] at hm
  simp only [direction,Bool.false_eq_true,↓reduceIte] at hm
  dsimp [height,c0]
  linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.SmallSide
