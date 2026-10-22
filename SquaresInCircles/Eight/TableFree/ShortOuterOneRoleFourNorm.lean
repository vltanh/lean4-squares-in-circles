module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneRoleFourScalars

/-!
# The intrinsic support transition for role four

Uncompiled transcription of Section 2.2 of
`HAND_SHORT_WORD_ROLE_FOUR_POSITIVE_QUARTER_WITHOUT_TABLES.md`.
The diagonal/full-circle transition is the unique zero of the actual
coefficient difference. The full-circle branch is concave throughout
the interval from that transition to the final angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.RoleFour
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)

def transition (x : ℝ) : ℝ := weight*(Real.cos x+Real.sin x)-target
def transitionD (x : ℝ) : ℝ := weight*(Real.cos x-Real.sin x)
def IsEvent (e : ℝ) : Prop := e∈Ioo 0 (3/10) ∧ transition e=0

lemma transition_hasDerivAt (x : ℝ) : HasDerivAt transition (transitionD x) x := by
  convert (((Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x)).const_mul weight).
    sub_const target using 1 <;> dsimp [transition,transitionD] <;> ring

lemma transition_strictMono : StrictMonoOn transition (Icc 0 (7/10)) := by
  apply strict_increase_of_reserve
    (fun y _ => (transition_hasDerivAt y).continuousAt.continuousWithinAt)
    (fun y _ => transition_hasDerivAt y) (show (0:ℝ)<2/25 by norm_num)
  intro y hy
  have ht := positive_trig (Ioo_subset_Icc_self hy)
  dsimp [transitionD,weight]
  linarith [ht.1,ht.2.2.2.1]

lemma transition_endpoints : transition 0<0 ∧ (26/1000:ℝ)<transition (3/10) := by
  constructor
  · norm_num [transition,weight,target]
  · let B := (((Interval.point weight).mul
      ((cosBox (3/10) (by norm_num)).add (sinBox (3/10) (by norm_num)))).sub
        (Interval.point target))
    have hb : (26/1000:ℝ)<B.lo := by
      norm_num [B,weight,target,SecondWord.SameZero.PJ.Reference.sinBox,
        SecondWord.SameZero.PJ.Reference.cosBox,Interval.of_bounds,Interval.point,
        Interval.add,Interval.sub,Interval.neg,Interval.mul,
        HighOrderTaylor.S17,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
        HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
        sin9,sin7,cos10,cos8]
    exact hb.trans_le B.mem.1

theorem exists_event : ∃e,IsEvent e := by
  have hc : Continuous transition := by dsimp [transition]; fun_prop
  obtain ⟨e,he,heq⟩ := intermediate_value_Icc (show (0:ℝ)≤3/10 by norm_num)
    hc.continuousOn (show (0:ℝ)∈Icc (transition 0) (transition (3/10)) from
      ⟨transition_endpoints.1.le,by linarith [transition_endpoints.2]⟩)
  have hl : 0<e := lt_of_le_of_ne he.1 (by
    intro h
    rw [←h] at heq
    linarith [transition_endpoints.1])
  have hu : e<3/10 := lt_of_le_of_ne he.2 (by
    intro h
    rw [h] at heq
    linarith [transition_endpoints.2])
  exact ⟨e,⟨hl,hu⟩,heq⟩

lemma event_angle {e : ℝ} (he : IsEvent e) : e∈Icc 0 (7/10) :=
  ⟨he.1.1.le,by linarith [he.1.2]⟩

lemma event_identity {e : ℝ} (he : IsEvent e) :
    weight*(Real.cos e+Real.sin e)=target := by
  have hh := he.2
  dsimp [transition] at hh
  linarith

lemma event_unique {e f : ℝ} (he : IsEvent e) (hf : IsEvent f) : e=f := by
  rcases lt_trichotomy e f with h | h | h
  · have hh := transition_strictMono (event_angle he) (event_angle hf) h
    rw [he.2,hf.2] at hh
    exact False.elim (lt_irrefl _ hh)
  · exact h
  · have hh := transition_strictMono (event_angle hf) (event_angle he) h
    rw [he.2,hf.2] at hh
    exact False.elim (lt_irrefl _ hh)

lemma before_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    weight*(Real.cos x+Real.sin x)≤target := by
  have hh := transition_strictMono.monotoneOn
    (show x∈Icc 0 (7/10) from ⟨hx.1,hx.2.trans (event_angle he).2⟩)
    (event_angle he) hx.2
  rw [he.2] at hh
  dsimp [transition] at hh
  linarith

abbrev radius : ℝ := Real.sqrt Q0
def normA : ℝ := weight^2+target^2
def normC : ℝ := -2*weight*target
def N (x : ℝ) : ℝ := CircularNorm.norm normA 0 normC x
def normValue (x : ℝ) : ℝ :=
  Real.pi/2-x+constant+(weight+target)/2+weight*Real.cos x-radius*N x
def normFirst (x : ℝ) : ℝ :=
  -1-weight*Real.sin x-radius*CircularNorm.d1 normA 0 normC x
def normSecond (x : ℝ) : ℝ :=
  -weight*Real.cos x-radius*CircularNorm.d2 normA 0 normC x

lemma radius_positive : 0<radius := Real.sqrt_pos.mpr (by norm_num [Q0])
lemma radius_sq : radius^2=Q0 := Real.sq_sqrt (by norm_num [Q0])
lemma radius_upper : radius<(1978788/1000000:ℝ) := by
  have hR := radius_sq
  norm_num [Q0] at hR
  nlinarith [radius_positive]

lemma norm_energy_positive (x : ℝ) : 0<CircularNorm.energy normA 0 normC x := by
  have hs := Real.sin_le_one x
  norm_num [CircularNorm.energy,normA,normC,weight,target] at *
  linarith

lemma norm_positive (x : ℝ) : 0<N x := CircularNorm.norm_pos (norm_energy_positive x)
lemma norm_sq (x : ℝ) : (N x)^2=weight^2+target^2-2*weight*target*Real.sin x := by
  simpa [N,CircularNorm.energy,normA,normC] using
    CircularNorm.norm_sq (norm_energy_positive x).le

lemma norm_antitone : AntitoneOn N (Icc 0 (7/10)) := by
  intro x hx y hy hxy
  have hs := sin_mono hx hy hxy
  have hNx := norm_sq x
  have hNy := norm_sq y
  norm_num [weight,target] at *
  nlinarith [norm_positive x,norm_positive y]

lemma event_norm_square {e : ℝ} (he : IsEvent e) :
    (N e)^2=2*weight^2*(Real.cos e)^2 := by
  have hn := norm_sq e
  have hc := Real.sin_sq_add_cos_sq e
  have heq := event_identity he
  linear_combination hn-weight^2*hc-
    (target+weight*Real.cos e-weight*Real.sin e)*heq

lemma norm_after_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (N x)^2≤2*weight^2 := by
  have hh := norm_antitone (event_angle he) ⟨he.1.1.le.trans hx.1,hx.2⟩ hx.1
  have hs := event_norm_square he
  have hc := Real.sin_sq_add_cos_sq e
  have hstep : (N x)^2≤(N e)^2 := by nlinarith [norm_positive x,norm_positive e]
  have hcoef := mul_nonneg (show 0≤2*weight^2 by positivity) (sq_nonneg (Real.sin e))
  nlinarith

lemma radius_norm_after_event {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    radius*N x/4<(7/10:ℝ)*weight := by
  have hh := mul_le_mul_of_nonneg_left (norm_after_event he hx)
    (show 0≤Q0 by norm_num [Q0])
  have hsq : (radius*N x)^2≤2*Q0*weight^2 := by
    rw [mul_pow,radius_sq]
    nlinarith only [hh]
  norm_num [weight,Q0] at *
  nlinarith [mul_pos radius_positive (norm_positive x)]

lemma normValue_hasDerivAt (x : ℝ) : HasDerivAt normValue (normFirst x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+constant+(weight+target)/2)).add
      ((Real.hasDerivAt_cos x).const_mul weight)).sub
        ((CircularNorm.norm_hasDerivAt (norm_energy_positive x)).const_mul radius)) using 1 <;>
    dsimp [normValue,normFirst,N] <;> ring

lemma normFirst_hasDerivAt (x : ℝ) : HasDerivAt normFirst (normSecond x) x := by
  convert ((((Real.hasDerivAt_sin x).const_mul weight).neg).const_add (-1)).sub
    ((CircularNorm.d1_hasDerivAt (norm_energy_positive x)).const_mul radius) using 1 <;>
    dsimp [normFirst,normSecond] <;> ring

lemma normValue_concave {e : ℝ} (he : IsEvent e) :
    ConcaveOn ℝ (Icc e (7/10)) normValue := by
  apply concave_of_deriv2 (fun x _ => normValue_hasDerivAt x)
    (fun x _ => normFirst_hasDerivAt x)
  intro x hx
  have hc := CircularNorm.curvature_lower (norm_energy_positive x)
    (show (0:ℝ)^2+normC^2≤normA^2 by norm_num [normC,normA,weight,target])
  have hmul := mul_le_mul_of_nonneg_left hc radius_positive.le
  have hcap := radius_norm_after_event he hx
  have ht := positive_trig (show x∈Icc 0 (7/10) from ⟨he.1.1.le.trans hx.1,hx.2⟩)
  have hmul' : -radius*N x/4≤radius*CircularNorm.d2 normA 0 normC x := by
    simpa only [←mul_div_assoc,neg_mul,mul_neg] using hmul
  dsimp [normSecond,weight] at *
  linarith [ht.1]

lemma normValue_at_event {e : ℝ} (he : IsEvent e) : normValue e=diagonal e := by
  have hN := event_norm_square he
  have hdiag := diagonal_circle
  have hprod : radius*N e=2*(outerDiagonal+1/2)*weight*Real.cos e := by
    have hsq : (radius*N e)^2=(2*(outerDiagonal+1/2)*weight*Real.cos e)^2 := by
      calc
        (radius*N e)^2=Q0*(N e)^2 := by rw [mul_pow,radius_sq]
        _=2*(outerDiagonal+1/2)^2*(2*weight^2*(Real.cos e)^2) := by rw [hN,←hdiag]
        _=(2*(outerDiagonal+1/2)*weight*Real.cos e)^2 := by ring
    have hright : 0≤2*(outerDiagonal+1/2)*weight*Real.cos e :=
      mul_nonneg (by dsimp [weight]; linarith [outer_endpoint_bounds.2.2.1])
        (by linarith [(positive_trig (event_angle he)).1])
    nlinarith [mul_pos radius_positive (norm_positive e)]
  have heq := event_identity he
  dsimp [normValue,diagonal]
  linear_combination -hprod-(outerDiagonal+1/2)*heq

lemma norm_final_upper : N (7/10)<(682546867/1000000000:ℝ) := by
  have hh := norm_sq (7/10)
  have hs := fine_cap_trig.1
  norm_num [weight,target] at hh
  nlinarith [norm_positive (7/10)]

lemma normValue_final : (89809/100000:ℝ)<normValue (7/10) := by
  have hprod : radius*N (7/10)<(1978788/1000000:ℝ)*(682546867/1000000000) :=
    (mul_le_mul_of_nonneg_right radius_upper.le (norm_positive (7/10)).le).trans_lt
      (mul_lt_mul_of_pos_left norm_final_upper (by norm_num))
  have hp := pi_hand_enclosure.1
  have hc := fine_cap_trig.2.2.1
  dsimp [normValue,weight,target,constant]
  linarith

lemma normValue_lower {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) :
    (89809/100000:ℝ)<normValue x := by
  apply concave_gt_of_endpoints (normValue_concave he) hx
  · rw [normValue_at_event he]
    linarith [diagonal_lower (event_angle he)]
  · exact normValue_final

end SquaresInCircles.Eight.TableFree.ShortOuterOne.RoleFour
