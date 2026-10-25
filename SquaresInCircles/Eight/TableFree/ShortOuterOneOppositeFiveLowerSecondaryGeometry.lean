module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveLowerData

/-!
# The actual lower secondary contact and its forced angle interval

Uncompiled transcription of Section 2, equations (8)--(12), of
`HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md`.
The source is moved monotonically to its original weak separator.
Its contact remains strictly below the diagonal. The original target
circle determines the positive radical and the unique rotated point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerSecondary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def cap : ℝ := 571/1000
def feasibility (u : ℝ) : ℝ := (2*outerAxial-1)*Real.cos u-Real.sin u
def source (r : Bool) (b : ℝ) : ℝ := p r*SameContact.arc b-q r*b
def sourceD (r : Bool) (b : ℝ) : ℝ := -p r*SameContact.ratio b-q r
def contact (A B u : ℝ) : ℝ := A*Real.cos u-B*Real.sin u-width u
def Z (v u : ℝ) : ℝ := v+Real.cos u
def T (v u : ℝ) : ℝ := root (Z v u)
def cost (r : Bool) (v u : ℝ) : ℝ := Real.pi/2-u+cShift r+p r*root v-
  (q r+D r u)*v-D r u*Real.cos u-E r u*T v u
def first (r : Bool) (v u : ℝ) : ℝ := p r*rootD v-(q r+D r u)-E r u*rootD (Z v u)
def second (r : Bool) (v u : ℝ) : ℝ := p r*rootDD v-E r u*rootDD (Z v u)
def Domain (v u : ℝ) : Prop := u∈Icc 0 cap ∧ RootDomain v ∧ RootDomain (Z v u)

lemma small_angle {u : ℝ} (hu : u∈Icc 0 cap) : u∈Icc 0 (7/10) :=
  ⟨hu.1,hu.2.trans (by norm_num [cap])⟩

lemma feasible {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10))
    (hm : width u≤-b+A*Real.cos u-B*Real.sin u) : 1≤feasibility u := by
  have hb := outer_bounds hs
  have hB := outer_bounds ht
  have htr := positive_trig hu
  have hA := mul_le_mul_of_nonneg_right hB.2.1 (by linarith [htr.1] : 0≤Real.cos u)
  have hBs := mul_nonneg hB.2.2.1 htr.2.2.1
  dsimp [width] at hm
  dsimp [feasibility]
  nlinarith

lemma feasibility_hasDerivAt (u : ℝ) : HasDerivAt feasibility
    (-(2*outerAxial-1)*Real.sin u-Real.cos u) u := by
  have hh := ((Real.hasDerivAt_cos u).const_mul (2*outerAxial-1)).fun_sub (Real.hasDerivAt_sin u)
  exact hh.congr_deriv (by ring)

lemma feasibility_antitone : AntitoneOn feasibility (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (feasibility_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => feasibility_hasDerivAt u)
    (fun u hu => by
      have ht := positive_trig (Ioo_subset_Icc_self hu)
      have hp := mul_nonneg (show 0≤2*outerAxial-1 by linarith [outer_endpoint_bounds.1]) ht.2.2.1
      linarith [ht.1])

lemma cap_infeasible : feasibility cap<1 := by
  let V := (((ShortWord.MixedQuarter.Reference.axial.mul (Interval.point 2)).sub
    (Interval.point 1)).mul
    (ShortWord.MixedQuarter.Reference.cosine (by norm_num [cap] : (0:ℝ)≤cap))).sub
      (ShortWord.MixedQuarter.Reference.sine (by norm_num [cap] : (0:ℝ)≤cap))
  have hh : V.hi<1 := by dsimp [V,cap]; mixed_fixed
  have hv : feasibility cap≤V.hi := by
    have h2 := V.mem.2
    dsimp [feasibility]
    linarith
  exact hv.trans_lt hh

lemma forced_cap {u : ℝ} (hu : u∈Icc 0 (7/10)) (hf : 1≤feasibility u) : u<cap := by
  by_contra! hcap
  have hh := feasibility_antitone (by norm_num [cap] : cap∈Icc 0 (7/10)) hu hcap
  linarith [cap_infeasible]

lemma forced_half_cap {u : ℝ} (hu : u∈Icc 0 (7/10)) (hf : 1≤feasibility u) :
    half u<halfCap := by
  have hx := half_bounds hu
  have htr := half_trig hu
  have hd : 0<1+(half u)^2 := by positivity
  have he : feasibility u-1=
      (2*outerAxial*(1-(half u)^2)-2-2*half u)/(1+(half u)^2) := by
    dsimp [feasibility]
    rw [htr.1,htr.2]
    field_simp [hd.ne']
    ring
  have hn : 0≤2*outerAxial*(1-(half u)^2)-2-2*half u := by
    have h0 : 0≤(2*outerAxial*(1-(half u)^2)-2-2*half u)/(1+(half u)^2) := by
      rw [←he]
      linarith
    have h1 := mul_nonneg h0 hd.le
    rwa [div_mul_cancel₀ _ hd.ne'] at h1
  by_contra! hcap
  have hx2 : (halfCap)^2≤(half u)^2 := by
    have hp := mul_nonneg (show 0≤half u-halfCap by linarith) (show 0≤half u+halfCap by dsimp [halfCap]; linarith)
    nlinarith only [hp]
  have hfactor : 0≤2*(1-(half u)^2) := by nlinarith [hx.1,hx.2]
  have ha := mul_le_mul_of_nonneg_right ShortOuterZero.fine_axial_bounds.2.le hfactor
  dsimp [halfCap] at *
  nlinarith only [hn,ha,hx2,hcap]

lemma cap_trig : (21/25:ℝ)<Real.cos cap ∧ (27/50:ℝ)<Real.sin cap := by
  have hc : (21/25:ℝ)<(ShortWord.MixedQuarter.Reference.cosine
      (by norm_num [cap] : (0:ℝ)≤cap)).lo := by dsimp [cap]; mixed_fixed
  have hs : (27/50:ℝ)<(ShortWord.MixedQuarter.Reference.sine
      (by norm_num [cap] : (0:ℝ)≤cap)).lo := by dsimp [cap]; mixed_fixed
  exact ⟨hc.trans_le (ShortWord.MixedQuarter.Reference.cosine (by norm_num [cap])).mem.1,
    hs.trans_le (ShortWord.MixedQuarter.Reference.sine (by norm_num [cap])).mem.1⟩

lemma small_trig {u : ℝ} (hu : u∈Icc 0 cap) :
    (21/25:ℝ)<Real.cos u ∧ Real.cos u≤1 ∧ 0≤Real.sin u ∧ Real.sin u<13/20 := by
  have ht := positive_trig (small_angle hu)
  have hk := cos_anti (small_angle hu) (by norm_num [cap] : cap∈Icc 0 (7/10)) hu.2
  exact ⟨cap_trig.1.trans_le hk,ht.2.1,ht.2.2.1,by linarith [ht.2.2.2.1]⟩

lemma E_hasDerivAt (r : Bool) (u : ℝ) : HasDerivAt (E r) (D r u) u := by
  have hh := ((Real.hasDerivAt_sin u).const_mul (P r)).fun_add
    ((Real.hasDerivAt_cos u).const_mul (t r))
  exact hh.congr_deriv (by simp only [D]; ring)
lemma D_hasDerivAt (r : Bool) (u : ℝ) : HasDerivAt (D r) (-E r u) u := by
  have hh := ((Real.hasDerivAt_cos u).const_mul (P r)).fun_sub
    ((Real.hasDerivAt_sin u).const_mul (t r))
  exact hh.congr_deriv (by simp only [E]; ring)

lemma E_lower (r : Bool) {u : ℝ} (hu : u∈Icc 0 cap) : (81/100:ℝ)<E r u := by
  have hc : ConcaveOn ℝ (Icc 0 cap) (E r) := concave_of_deriv2
    (fun x _ => E_hasDerivAt r x) (fun x _ => D_hasDerivAt r x)
    (fun x hx => by linarith [E_positive r (small_angle hx)])
  apply concave_gt_of_endpoints hc hu
  · cases r <;> norm_num [E,P,t,PQ,tQ]
  · have hs := mul_lt_mul_of_pos_left cap_trig.2
      (show 0<P r by linarith [(coefficient_bounds r).2.2.2.2.1])
    have hk := mul_lt_mul_of_pos_left cap_trig.1
      (show 0<t r by linarith [(coefficient_bounds r).2.2.2.2.2.2.1])
    cases r <;> norm_num [E,P,t,PQ,tQ] at hs hk ⊢ <;> linarith

lemma source_hasDerivAt (r : Bool) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (source r) (sourceD r b) b := by
  have hh := ((SameContact.arc_hasDerivAt (SameContact.outer_domain hb)).const_mul (p r)).fun_sub
    ((hasDerivAt_id' b).const_mul (q r))
  exact hh.congr_deriv (by simp only [sourceD]; ring)
lemma sourceD_negative (r : Bool) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : sourceD r b<0 := by
  have hratio := SecondWord.outer_ratio_bounds hb
  have hh := mul_le_mul_of_nonneg_left hratio.2.1
    (show 0≤-p r by linarith [(coefficient_bounds r).2.1])
  have hcoeff := coefficient_bounds r
  dsimp [sourceD]
  linarith
lemma source_antitone (r : Bool) : AntitoneOn (source r) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (source_hasDerivAt r hb).continuousAt.continuousWithinAt)
    (fun b hb => source_hasDerivAt r (Ioo_subset_Icc_self hb))
    (fun b hb => (sourceD_negative r (Ioo_subset_Icc_self hb)).le)

lemma contact_bounds {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    b≤contact A B u ∧ contact A B u∈Icc 0 outerDiagonal := by
  have hb := outer_bounds hs
  have hB := outer_bounds ht
  have htr := positive_trig hu
  have hAs := mul_le_mul_of_nonneg_left htr.2.1 (show 0≤A by linarith [hB.1,outer_endpoint_bounds.2.2.1])
  have hBs := mul_nonneg hB.2.2.1 htr.2.2.1
  have hmax : contact A B u≤outerAxial-1 := by
    dsimp [contact]
    linarith [width_ge_one hu,hB.2.1]
  have hbc : b≤contact A B u := by dsimp [contact]; linarith
  exact ⟨hbc,⟨hb.2.2.1.trans hbc,by linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.1,
    ShortOuterZero.fine_axial_bounds.2]⟩⟩

lemma contact_domain {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    Domain (contact A B u+1/2) u := by
  have hb := (contact_bounds hs ht hu hm).2
  have hB := outer_bounds ht
  have htr := positive_trig hu
  have hv : RootDomain (contact A B u+1/2) := by
    apply root_domain_iff.2
    simpa using SameContact.outer_domain hb
  have he : Z (contact A B u+1/2) u=
      (A+1/2)*Real.cos u-(B+1/2)*Real.sin u := by dsimp [Z,contact,width]; ring
  have hAk := mul_le_mul_of_nonneg_left htr.2.1
    (show 0≤A+1/2 by linarith [hB.1,outer_endpoint_bounds.2.2.1])
  have hBs := mul_nonneg (show 0≤B+1/2 by linarith [hB.2.2.1]) htr.2.2.1
  have hz : RootDomain (Z (contact A B u+1/2) u) := by
    constructor
    · dsimp [Z]
      linarith [hv.1,htr.1]
    · rw [he,X0_eq]
      linarith [hB.2.1]
  exact ⟨⟨hu.1,(forced_cap hu (feasible hs ht hu hm)).le⟩,hv,hz⟩

lemma interval_domain {v u w : ℝ} (hd : Domain v u) (hw : w∈Icc (1/2) v) : Domain w u := by
  refine ⟨hd.1,⟨hw.1,hw.2.trans hd.2.1.2⟩,?_⟩
  have ht := small_trig hd.1
  have hZ : Z v u≤X0 := hd.2.2.2
  constructor
  · dsimp [Z]
    linarith [hw.1,ht.1]
  · dsimp [Z] at hZ ⊢
    linarith [hw.2]

lemma contact_target_radical {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    T (contact A B u+1/2) u=(A+1/2)*Real.sin u+(B+1/2)*Real.cos u := by
  have hd := contact_domain hs ht hu hm
  have hB := outer_bounds ht
  have htr := positive_trig hu
  have he : Z (contact A B u+1/2) u=
      (A+1/2)*Real.cos u-(B+1/2)*Real.sin u := by dsimp [Z,contact,width]; ring
  have hp : 0<(A+1/2)*Real.sin u+(B+1/2)*Real.cos u := by
    have h1 := mul_nonneg (show 0≤A+1/2 by linarith [hB.1,outer_endpoint_bounds.2.2.1]) htr.2.2.1
    have h2 := mul_pos (show 0<B+1/2 by linarith [hB.2.2.1]) (show 0<Real.cos u by linarith [htr.1])
    linarith
  have heq : ((A+1/2)*Real.sin u+(B+1/2)*Real.cos u)^2=
      Q0-(Z (contact A B u+1/2) u)^2 := by
    rw [he]
    linear_combination ht.2.2+((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq u)
  have hroot := root_sq hd.2.2
  have hroot0 := root_positive hd.2.2
  change (root (Z (contact A B u+1/2) u))^2=_ at hroot
  dsimp [T]
  nlinarith

lemma contact_identity {a b A B u : ℝ} (r : Bool) (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    cost r (contact A B u+1/2) u=
      Real.pi/2-u+c+source r (contact A B u)-P r*A-t r*B := by
  have hT := contact_target_radical hs ht hu hm
  have hroot : root (contact A B u+1/2)=SameContact.arc (contact A B u)+1/2 := by
    rw [root_eq_arc]
    congr 2
    ring
  have he : Z (contact A B u+1/2) u=(A+1/2)*Real.cos u-(B+1/2)*Real.sin u := by
    dsimp [Z,contact,width]
    ring
  have hcircle := Real.sin_sq_add_cos_sq u
  dsimp [cost]
  rw [hT,hroot]
  dsimp [cShift,source,D,E]
  dsimp [Z] at he
  linear_combination (-P r*Real.cos u+t r*Real.sin u)*he-
    (P r*(A+1/2)+t r*(B+1/2))*hcircle

lemma original_to_contact {a b A B u : ℝ} (r : Bool) (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    cost r (contact A B u+1/2) u≤Real.pi/2-u+c+p r*a-q r*b-P r*A-t r*B := by
  have hb := contact_bounds hs ht hu hm
  have hsrc := source_antitone r ⟨(outer_bounds hs).2.2.1,(outer_bounds hs).2.2.2.1⟩ hb.2 hb.1
  rw [contact_identity r hs ht hu hm]
  dsimp only [source] at hsrc ⊢
  rw [(SameContact.actual_arc hs).1] at hsrc
  linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerSecondary
