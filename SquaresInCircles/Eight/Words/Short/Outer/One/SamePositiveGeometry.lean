module

public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeNegativeCurvature
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameEvent

/-!
# Eight squares: the full positive-half primary contact domain

The actual contact is decreasing in its target coordinate. Every active
contact is before the unique axial/diagonal event and has target height
at most 1-d. All earlier points on its fixed-target angle segment remain
physical.
-/

section
/-!
## Literal data for the three paired same-sign quarter owners

The source is parametrized by its primary coordinate and the target
by its transverse coordinate. Both are the original outer-circle states.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

abbrev Row := Fin 3
def c : Row→ℝ := ![-53489/100000,-53062/100000,-20704/100000]
def p : Row→ℝ := ![9133/100000,19335/100000,0]
def q : Row→ℝ := ![88074/100000,76744/100000,94766/100000]
def P : Row→ℝ := ![-33147/100000,-20967/100000,-21826/100000]
def t : Row→ℝ := ![11336/10000,83048/100000,83472/100000]
def b0 : ℝ := 1-outerDiagonal
def eta : ℝ := 1/80
def source (r : Row) (a : ℝ) : ℝ := p r*a-q r*arc a
def sourceD (r : Row) (a : ℝ) : ℝ := p r+q r*ratio a
def sourceDD (r : Row) (a : ℝ) : ℝ := q r*ratioD a
def target (r : Row) (B : ℝ) : ℝ := -P r*arc B+t r*B
def targetD (r : Row) (B : ℝ) : ℝ := P r*ratio B+t r
def aligned (r : Row) (B : ℝ) : ℝ := Real.pi/2+c r+source r (1-B)+target r B
def alignedD (r : Row) (B : ℝ) : ℝ := -sourceD r (1-B)+targetD r B
def alignedDD (r : Row) (B : ℝ) : ℝ := sourceDD r (1-B)+P r*ratioD B
def initialAngle (r : Row) (B : ℝ) : ℝ := 1-sourceD r (1-B)*(arc B-1/2)

lemma coefficient_bounds (r : Row) :
    0≤p r ∧ p r≤19335/100000 ∧ (76744/100000:ℝ)≤q r ∧ q r≤94766/100000 ∧
    P r≤0 ∧ 0<t r+P r ∧ (94766/100000:ℝ)≤p r+q r := by
  fin_cases r <;> norm_num [p,q,P,t]

lemma b0_bounds : (1/10:ℝ)<b0 ∧ b0<(101/1000:ℝ) := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [b0]
  constructor <;> linarith

lemma b0_mem : b0∈Icc 0 outerDiagonal := by
  dsimp [b0]
  constructor <;> linarith [outer_endpoint_bounds.2.2.1,outer_endpoint_bounds.2.2.2]

lemma aligned_domains {B : ℝ} (hB : B∈Icc 0 b0) :
    B∈Icc 0 outerDiagonal ∧ 1-B∈Icc outerDiagonal 1 ∧
      1-B∈Icc outerDiagonal outerAxial := by
  have ha := outer_endpoint_bounds.1
  have h1 : outerDiagonal≤1-B := by dsimp [b0] at hB; linarith [hB.2]
  exact ⟨⟨hB.1,hB.2.trans b0_mem.2⟩,⟨h1,by linarith [hB.1]⟩,
    ⟨h1,by linarith [hB.1]⟩⟩

lemma primary_domain {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    a∈Icc 0 outerAxial := ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.1],ha.2⟩

lemma primary_ratio_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) : 1≤ratio a := by
  have hs := SameContact.primary_state ha
  have hp := SameContact.shifted_positive (primary_domain ha)
  change 1≤(a+1/2)/(arc a+1/2)
  exact (le_div_iff₀ hp).2 (by linarith [hs.2.1])

lemma source_hasDerivAt (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (source r) (sourceD r a) a := by
  convert ((hasDerivAt_id a).const_mul (p r)).sub
    ((SameContact.arc_hasDerivAt (primary_domain ha)).const_mul (q r)) using 1
  · funext y; simp only [source,Pi.sub_apply,id_eq]
  · simp only [sourceD]; ring

lemma sourceD_hasDerivAt (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (sourceD r) (sourceDD r a) a :=
  ((SameContact.ratio_hasDerivAt (primary_domain ha)).const_mul (q r)).const_add (p r)

lemma sourceD_lower (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    (94766/100000:ℝ)≤ sourceD r a := by
  have hh := mul_le_mul_of_nonneg_left (primary_ratio_lower ha)
    (show 0≤q r by fin_cases r <;> norm_num [q])
  dsimp [sourceD]
  linarith [(coefficient_bounds r).2.2.2.2.2.2]

lemma source_monotone (r : Row) : MonotoneOn (source r) (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (source_hasDerivAt r ha).continuousAt.continuousWithinAt)
    (fun a ha => source_hasDerivAt r (Ioo_subset_Icc_self ha))
    (fun a ha => by linarith [sourceD_lower r (Ioo_subset_Icc_self ha)])

lemma target_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (target r) (targetD r B) B := by
  convert ((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).const_mul (-P r)).add
    ((hasDerivAt_id B).const_mul (t r)) using 1
  · funext y; simp only [target,Pi.add_apply,id_eq]
  · simp only [targetD]; ring

lemma targetD_positive (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<targetD r B := by
  have hr := SecondWord.outer_ratio_bounds hB
  have hh := mul_le_mul_of_nonpos_left hr.2.1 (coefficient_bounds r).2.2.2.2.1
  dsimp [targetD]
  linarith [(coefficient_bounds r).2.2.2.2.2.1]

lemma target_monotone (r : Row) : MonotoneOn (target r) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hB => (target_hasDerivAt r hB).continuousAt.continuousWithinAt)
    (fun _ hB => target_hasDerivAt r (Ioo_subset_Icc_self hB))
    (fun _ hB => (targetD_positive r (Ioo_subset_Icc_self hB)).le)

lemma aligned_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 b0) :
    HasDerivAt (aligned r) (alignedD r B) B := by
  have hd := aligned_domains hB
  convert (((source_hasDerivAt r hd.2.2).comp B ((hasDerivAt_id B).const_sub 1)).const_add
    (Real.pi/2+c r)).add (target_hasDerivAt r hd.1) using 1
  · funext y; simp only [aligned,Pi.add_apply,Function.comp_apply]
  · simp only [alignedD]; ring

lemma alignedD_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 b0) :
    HasDerivAt (alignedD r) (alignedDD r B) B := by
  have hd := aligned_domains hB
  convert (((sourceD_hasDerivAt r hd.2.2).comp B ((hasDerivAt_id B).const_sub 1)).neg).add
    (((SameContact.ratio_hasDerivAt (SameContact.outer_domain hd.1)).const_mul (P r)).add_const
      (t r)) using 1
  · funext y; simp only [alignedD,targetD,Pi.add_apply,Pi.neg_apply,Function.comp_apply]
  · simp only [alignedDD]; ring

lemma aligned_target_root {B : ℝ} (hB : B∈Icc 0 b0) : (377/200:ℝ)<arc B+1/2 := by
  have hl := ShortOuterZero.Opposite.low_radical.1
  have hm := SameContact.arc_antitone (SameContact.outer_domain (aligned_domains hB).1)
    (SameContact.outer_domain b0_mem) hB.2
  change (377/200:ℝ)<arc (1-outerDiagonal)+1/2 at hl
  dsimp [b0] at hm
  linarith

lemma aligned_source_root {B : ℝ} (hB : B∈Icc 0 b0) :
    (129/100:ℝ)<arc (1-B)+1/2 ∧ arc (1-B)+1/2<(7/5:ℝ) := by
  have hd := aligned_domains hB
  have hc := SameContact.arc_circle (primary_domain hd.2.2)
  have hp := SameContact.shifted_positive (primary_domain hd.2.2)
  have hs := SameContact.primary_secondary_mem hd.2.2
  norm_num [Q0] at hc
  constructor
  · have hcoord : 0≤1-B+1/2 ∧ 1-B+1/2≤3/2 := by constructor <;> linarith [hB.1,hd.2.1.1,outer_endpoint_bounds.2.2.1]
    have hsq := pow_le_pow_left₀ hcoord.1 hcoord.2 2
    nlinarith
  · linarith [hs.2,outer_endpoint_bounds.2.2.2]

lemma aligned_curvature {B : ℝ} (hB : B∈Icc 0 b0) : (1:ℝ)<alignedDD 0 B := by
  have hu := aligned_source_root hB
  have hU := aligned_target_root hB
  have hp := SameContact.shifted_positive (SameContact.outer_domain (aligned_domains hB).1)
  have hup := SameContact.shifted_positive (primary_domain (aligned_domains hB).2.2)
  have hu3 := pow_le_pow_left₀ hup.le hu.2.le 3
  have hU3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤377/200) hU.le 3
  have hrlo : Q0/(7/5:ℝ)^3≤ratioD (1-B) := by
    dsimp [ratioD]
    apply (le_div_iff₀ (pow_pos hup 3)).2
    norm_num [Q0] at *
    nlinarith
  have hrhi : ratioD B≤Q0/(377/200:ℝ)^3 := by
    dsimp [ratioD]
    apply (div_le_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at *
    nlinarith
  norm_num [alignedDD,sourceDD,q,P,Q0] at *
  linarith

lemma aligned_later_derivative (r : Row) (hr : r=1 ∨ r=2)
    {B : ℝ} (hB : B∈Icc 0 b0) : alignedD r B<0 := by
  have hs := primary_ratio_lower (aligned_domains hB).2.2
  have ht := (SecondWord.outer_ratio_bounds (aligned_domains hB).1).1
  rcases hr with rfl | rfl <;>
    norm_num [alignedD,sourceD,targetD,p,q,P,t] <;> linarith

end SquaresInCircles.Eight.ShortOuterOne.Same
end
end
end

section
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
  (fun _ hx => neg_nonpos.mpr (speed_positive hB (Ioo_subset_Icc_self hx)).le)

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
end
end
end
