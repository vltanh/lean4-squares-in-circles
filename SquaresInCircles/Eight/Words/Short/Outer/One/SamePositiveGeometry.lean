module

public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameData
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameEvent

/-!
# Eight squares: the full positive-half primary contact domain

The actual contact is decreasing in its target coordinate. Every active
contact is before the unique axial/diagonal event and has target height
at most 1-d. All earlier points on its fixed-target angle segment remain
physical.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Positive
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

def contact (B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x-(arc B-1/2)*Real.sin x
def speed (B x : ℝ) : ℝ :=
  (arc B-1/2)*Real.cos x+(1/2-B)*Real.sin x
def Domain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ outerDiagonal≤contact B x
def cost (r : Row) (B x : ℝ) : ℝ :=
  Real.pi/2+x+c r+source r (contact B x)+target r B
def first (r : Row) (B x : ℝ) : ℝ := 1-sourceD r (contact B x)*speed B x
def second (r : Row) (B x : ℝ) : ℝ :=
  sourceDD r (contact B x)*(speed B x)^2-sourceD r (contact B x)*(contact B x-1/2)

lemma contact_angle_hasDerivAt (B x : ℝ) :
    HasDerivAt (contact B) (-speed B x) x := by
  convert (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).sub
    ((Real.hasDerivAt_sin x).const_mul (arc B-1/2)) using 1
  · funext y; simp only [contact,Pi.sub_apply]
  · simp only [speed]; ring

lemma speed_hasDerivAt (B x : ℝ) : HasDerivAt (speed B) (contact B x-1/2) x := by
  convert ((Real.hasDerivAt_cos x).const_mul (arc B-1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (1/2-B)) using 1
  · funext y; simp only [speed,Pi.add_apply]
  · simp only [contact]; ring

lemma contact_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun B => contact B x) (-Real.cos x+ratio B*Real.sin x) B := by
  convert ((((hasDerivAt_id B).const_sub (1/2)).mul_const (Real.cos x)).const_add (1/2)).sub
    (((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).sub_const (1/2)).mul_const
      (Real.sin x)) using 1
  · funext y; simp only [contact,Pi.sub_apply,id_eq]
  · ring

lemma contact_target_antitone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    AntitoneOn (fun B => contact B x) (Icc 0 outerDiagonal) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (contact_target_hasDerivAt hB x).continuousAt.continuousWithinAt
  · intro B hB
    exact contact_target_hasDerivAt (Ioo_subset_Icc_self hB) x
  · intro B hB
    have ht := positive_trig hx
    have hp := mul_le_mul_of_nonneg_right
      (SecondWord.outer_ratio_bounds (Ioo_subset_Icc_self hB)).2.1 ht.2.2.1
    nlinarith [ht.1,ht.2.2.2.1]

lemma contact_zero (B : ℝ) : contact B 0=1-B := by norm_num [contact]; ring

lemma speed_positive {B x : ℝ} (hB : B∈Icc 0 b0) (hx : x∈Icc 0 (7/10)) :
    0<speed B x := by
  have hA := aligned_target_root hB
  have ht := positive_trig hx
  have hfirst := mul_pos (show 0<arc B-1/2 by linarith)
    (show 0<Real.cos x by linarith [ht.1])
  have hsecond := mul_nonneg (show 0≤1/2-B by linarith [hB.2,b0_bounds.2]) ht.2.2.1
  dsimp [speed]
  linarith

lemma contact_angle_antitone {B : ℝ} (hB : B∈Icc 0 b0) :
    AntitoneOn (contact B) (Icc 0 (7/10)) := antiOn_of_hasDeriv_nonpos
  (fun x _ => (contact_angle_hasDerivAt B x).continuousAt.continuousWithinAt)
  (fun x _ => contact_angle_hasDerivAt B x)
  (fun x hx => neg_nonpos.mpr (speed_positive hB (Ioo_subset_Icc_self hx)).le)

lemma axial_strictAnti : StrictAntiOn (contact 0) (Icc 0 (7/10)) := by
  have hm : StrictMonoOn (fun x => -contact 0 x) (Icc 0 (7/10)) := by
    apply strict_increase_of_reserve
      (fun x _ => (contact_angle_hasDerivAt 0 x).neg.continuousAt.continuousWithinAt)
      (fun x _ => by simpa using (contact_angle_hasDerivAt 0 x).neg)
      (show (0:ℝ)<69/100 by norm_num)
    intro x hx
    have ht := positive_trig (Ioo_subset_Icc_self hx)
    have ha := ShortOuterZero.fine_axial_bounds.1
    have hp := mul_le_mul
      (show (914575671/1000000000:ℝ)≤outerAxial-1/2 by linarith)
      (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (by norm_num)
      (by linarith : 0≤outerAxial-1/2)
    dsimp [speed]
    rw [SameContact.arc_zero]
    nlinarith [ht.2.2.1]
  intro x hx y hy hxy
  have hh := hm hx hy hxy
  linarith

/-- This is the same geometric axial/diagonal event already constructed
from its exact circle equation in the zero-contact chart. -/
theorem exists_axial_event : ∃e,e∈Ioo (134/1250:ℝ) (1073/10000) ∧ contact 0 e=outerDiagonal := by
  obtain ⟨e,he⟩ := ShortOuterZero.Same.Event.exists_event
  refine ⟨e,⟨?_,?_⟩,?_⟩
  · have hh := he.1.1
    norm_num [ShortOuterZero.Same.Event.lo] at hh
    linarith
  · have hh := he.1.2
    norm_num [ShortOuterZero.Same.Event.hi] at hh
    linarith
  · simpa [contact,ShortOuterZero.Same.contact,SecondWord.SameZero.b] using he.2

lemma active_ranges {B x : ℝ} (hd : Domain B x) :
    B∈Icc 0 b0 ∧ contact B x∈Icc outerDiagonal 1 ∧ x<(27/250:ℝ) := by
  have ht := positive_trig hd.2.1
  have hA := (outer_bounds (SameContact.arc_state hd.1)).1
  have hApos : 0≤arc B-1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  have hsin := mul_nonneg hApos ht.2.2.1
  have hBhalf : B<1/2 := by
    by_contra! hbad
    have hcos := mul_nonpos_of_nonpos_of_nonneg (show 1/2-B≤0 by linarith)
      (show 0≤Real.cos x by linarith [ht.1])
    have hc := hd.2.2
    dsimp [contact] at hc
    linarith [outer_endpoint_bounds.2.2.1]
  have hupper : contact B x≤1-B := by
    have hh := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤1/2-B by linarith)
    dsimp [contact]
    linarith
  have hB0 : B≤b0 := by dsimp [b0]; linarith [hd.2.2]
  have hcontact0 := contact_target_antitone hd.2.1
    (show (0:ℝ)∈Icc 0 outerDiagonal from ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩)
    hd.1 hd.1.1
  obtain ⟨e,he,heq⟩ := exists_axial_event
  have heDom : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
  have hxe : x≤e := by
    by_contra! hbad
    have hh := axial_strictAnti heDom hd.2.1 hbad
    rw [heq] at hh
    linarith [hd.2.2]
  exact ⟨⟨hd.1.1,hB0⟩,⟨hd.2.2,by linarith [hd.1.1]⟩,by linarith [he.2]⟩

lemma primary_mem {B x : ℝ} (hd : Domain B x) :
    contact B x∈Icc outerDiagonal outerAxial :=
  ⟨hd.2.2,by linarith [(active_ranges hd).2.1.2,outer_endpoint_bounds.1]⟩

lemma physical_before {B x y : ℝ} (hd : Domain B x) (hy : y∈Icc 0 x) : Domain B y := by
  have hy' : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hd.2.1.2⟩
  have hh := contact_angle_antitone (active_ranges hd).1 hy' hd.2.1 hy.2
  exact ⟨hd.1,hy',hd.2.2.trans hh⟩

lemma cost_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (cost r B) (first r B x) x := by
  convert (((hasDerivAt_id x).const_add (Real.pi/2+c r)).add
    ((source_hasDerivAt r (primary_mem hd)).comp x (contact_angle_hasDerivAt B x))).add_const
      (target r B) using 1
  · funext y; simp only [cost,Pi.add_apply,id_eq,Function.comp_apply]; ring
  · simp only [first]; ring

lemma first_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (first r B) (second r B x) x := by
  convert ((((sourceD_hasDerivAt r (primary_mem hd)).comp x (contact_angle_hasDerivAt B x)).mul
    (speed_hasDerivAt B x)).const_sub 1) using 1
  · funext y; simp only [first,Pi.mul_apply,Function.comp_apply]
  · simp only [second,Function.comp_apply]; ring

lemma near_cos {x : ℝ} (hx : x∈Icc 0 (27/250)) : (497/500:ℝ)<Real.cos x := by
  have hr := HighOrderTaylor.C18_le_cos (show (0:ℝ)≤27/250 by norm_num)
  have hnum : (497/500:ℝ)<HighOrderTaylor.C18 (27/250) := by
    norm_num [HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,
      HighOrderTaylor.C12,cos10,cos8]
  have hh := cos_anti (show x∈Icc 0 (7/10) from ⟨hx.1,by linarith [hx.2]⟩)
    (show (27/250:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  exact hnum.trans_le (hr.trans hh)

lemma source_root {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    (129/100:ℝ)<arc a+1/2 ∧ arc a+1/2<(7/5:ℝ) := by
  have hB : 1-a∈Icc 0 b0 := ⟨by linarith [ha.2],by dsimp [b0]; linarith [ha.1]⟩
  have he : 1-(1-a)=a := by ring
  simpa only [he] using aligned_source_root hB

lemma sourceD_upper (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    sourceD r a<(13/10:ℝ) := by
  have hroot := source_root ha
  have hratio : ratio a<(50/43:ℝ) := by
    change (a+1/2)/(arc a+1/2)<50/43
    apply (div_lt_iff₀ (by linarith [hroot.1])).2
    linarith [ha.2]
  have hq := coefficient_bounds r
  have hp := mul_le_mul_of_nonneg_left hratio.le (show 0≤q r by fin_cases r <;> norm_num [q])
  dsimp [sourceD]
  fin_cases r <;> norm_num [p,q] at * <;> linarith

lemma speed_lower {B x : ℝ} (hd : Domain B x) : (879/1000:ℝ)<speed B x := by
  have hr := active_ranges hd
  have hA := aligned_target_root hr.1
  have hc := near_cos ⟨hd.2.1.1,hr.2.2.le⟩
  have hp := mul_le_mul
    (show (177/200:ℝ)≤arc B-1/2 by linarith)
    hc.le (by norm_num) (by linarith : 0≤arc B-1/2)
  have hs := mul_nonneg (show 0≤1/2-B by linarith [hr.1.2,b0_bounds.2])
    (positive_trig hd.2.1).2.2.1
  dsimp [speed]
  nlinarith

lemma curvature (r : Row) {B x : ℝ} (hd : Domain B x) : (19/100:ℝ)<second r B x := by
  have hr := active_ranges hd
  have hv := source_root hr.2.1
  have hspeed := speed_lower hd
  have hL := sourceD_upper r hr.2.1
  have hL0 := sourceD_lower r (primary_mem hd)
  have hv0 : 0<arc (contact B x)+1/2 := by linarith [hv.1]
  have hv3 := pow_le_pow_left₀ hv0.le hv.2.le 3
  have hratio : Q0/(7/5:ℝ)^3≤ratioD (contact B x) := by
    dsimp [ratioD]
    apply (le_div_iff₀ (pow_pos hv0 3)).2
    norm_num [Q0] at *
    nlinarith
  have hcoef := mul_le_mul (coefficient_bounds r).2.2.1 hratio
    (by norm_num [Q0] : 0≤Q0/(7/5:ℝ)^3)
    (show 0≤q r by fin_cases r <;> norm_num [q])
  have hsquare : (879/1000:ℝ)^2≤(speed B x)^2 := by nlinarith
  have hpositive := mul_le_mul hcoef hsquare (by positivity)
    (mul_nonneg (show 0≤q r by fin_cases r <;> norm_num [q])
      (SameContact.ratioD_pos (primary_domain (primary_mem hd))).le)
  have hnegative := mul_le_mul hL.le
    (show contact B x-1/2≤(1/2:ℝ) by linarith [hr.2.1.2])
    (show 0≤contact B x-1/2 by linarith [hr.2.1.1,outer_endpoint_bounds.2.2.1])
    (by norm_num : (0:ℝ)≤13/10)
  dsimp [second,sourceDD]
  norm_num [Q0] at hpositive
  nlinarith

lemma initial_cost (r : Row) (B : ℝ) : cost r B 0=aligned r B := by
  rw [cost,contact_zero]
  simp [aligned]

lemma initial_first (r : Row) (B : ℝ) : first r B 0=initialAngle r B := by
  rw [first,contact_zero]
  norm_num [speed,initialAngle]

end SquaresInCircles.Eight.ShortOuterOne.Same.Positive
