module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeContactStationarity

/-!
# A whole-arc affine bound for the zero-target contact angle

The comparison projection at angle `.571-.72*b` is strictly convex.
Its second derivative is positive by a circle-coordinate chord and the
elementary inequalities `cos C>5/6` and `sin C≤C`.  Both endpoint
projections are below one half, so every original zero-target contact
has smaller angle.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.ZeroAngle

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def endpoint : ℝ := arc 1
def slope : ℝ := 18/25
def line (b : ℝ) : ℝ := 571/1000-slope*b
def projection (b : ℝ) : ℝ :=
  (U b-1)*Real.cos (line b)-W b*Real.sin (line b)
def first (b : ℝ) : ℝ :=
  (slope*W b-ratio b)*Real.cos (line b)+
    (slope*(U b-1)-1)*Real.sin (line b)
def core (b : ℝ) : ℝ := 2*slope-ratioD b-slope^2*(U b-1)
def coreFirst (b : ℝ) : ℝ := -ratioDD b+slope^2*ratio b
def coreSecond (b : ℝ) : ℝ := -ratioDDD b+slope^2*ratioD b
def loss (b : ℝ) : ℝ := 2*slope*ratio b-slope^2*W b
def lossFirst (b : ℝ) : ℝ := 2*slope*ratioD b-slope^2
def second (b : ℝ) : ℝ := core b*Real.cos (line b)-loss b*Real.sin (line b)

lemma endpoint_mem : endpoint∈Icc 0 outerDiagonal :=
  NegativeTwo.source_mem (ShortOuterOne.SameContact.primary_state primary_one_mem)

lemma endpoint_circle : U endpoint=3/2 := by
  have hh := (ShortOuterOne.SameContact.actual_arc
    (ShortOuterOne.SameContact.primary_state primary_one_mem)).1
  dsimp [endpoint,U]
  rw [hh]
  norm_num

lemma endpoint_bounds : (1581/2000:ℝ)<endpoint ∧ endpoint<791/1000 := by
  have hc := UW_circle (outer_domain endpoint_mem)
  rw [endpoint_circle] at hc
  norm_num [Q0] at hc
  have hb := endpoint_mem.1
  dsimp [W] at hc
  constructor <;> nlinarith

lemma source_mem {b : ℝ} (hb : b∈Icc 0 endpoint) : b∈Icc 0 outerDiagonal :=
  ⟨hb.1,hb.2.trans endpoint_mem.2⟩

lemma line_bounds {b : ℝ} (hb : b∈Icc 0 endpoint) :
    0<line b ∧ line b≤571/1000 := by
  dsimp [line,slope]
  constructor <;> linarith [hb.1,hb.2,endpoint_bounds.2]

lemma line_mem {b : ℝ} (hb : b∈Icc 0 endpoint) : line b∈Icc 0 (7/10) :=
  ⟨(line_bounds hb).1.le,by linarith [(line_bounds hb).2]⟩

lemma line_hasDerivAt (b : ℝ) : HasDerivAt line (-slope) b := by
  convert ((hasDerivAt_id b).const_mul slope).const_sub (571/1000) using 1

lemma core_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt core (coreFirst b) b := by
  have hh := ((ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hb)).const_sub
    (2*slope)).sub
      ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const
        (1/2)).sub_const 1).const_mul (slope^2))
  convert hh using 1 <;> dsimp [core,coreFirst,U] <;> ring

lemma coreFirst_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt coreFirst (coreSecond b) b := by
  convert (ratioDD_hasDerivAt (outer_domain hb)).neg.add
    ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul (slope^2))
    using 1

lemma loss_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt loss (lossFirst b) b := by
  have hh := ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).const_mul
    (2*slope)).sub (((hasDerivAt_id b).add_const (1/2)).const_mul (slope^2))
  convert hh using 1

lemma projection_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt projection (first b) b := by
  have hc := (line_hasDerivAt b).cos
  have hs := (line_hasDerivAt b).sin
  have hu := ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const
    (1/2)).sub_const 1
  have hw := (hasDerivAt_id b).add_const (1/2)
  convert (hu.mul hc).sub (hw.mul hs) using 1 <;>
    dsimp [projection,first,U,W] <;> ring

lemma first_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt first (second b) b := by
  have hleft := (((hasDerivAt_id b).add_const (1/2)).const_mul slope).sub
    (ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb))
  have hright := ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).add_const
    (1/2)).sub_const 1).const_mul slope).sub_const 1
  convert (hleft.mul (line_hasDerivAt b).cos).add
    (hright.mul (line_hasDerivAt b).sin) using 1 <;>
    dsimp [first,second,core,loss,U,W] <;> ring

lemma coreSecond_negative {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : coreSecond b<0 := by
  have hu := U_positive (outer_domain hb)
  have hc := UW_circle (outer_domain hb)
  have hU := (UW_bounds hb).2.1
  have hU4 := pow_lt_pow_left₀ hu.le hU (by norm_num : (4:ℕ)≠0)
  have he : coreSecond b*(U b)^7=
      Q0*(slope^2*(U b)^4-3*Q0-12*(W b)^2) := by
    dsimp [coreSecond,ratioDDD,ratioD,U] at *
    field_simp [show arc b+1/2≠0 from hu.ne']
    linear_combination -3*Q0*hc
  have hp := pow_pos hu 7
  norm_num [slope,Q0] at he hU4
  have hn : slope^2*(U b)^4-3*Q0-12*(W b)^2<0 := by
    norm_num [slope,Q0]
    nlinarith [sq_nonneg (W b)]
  have hprod := mul_neg_of_pos_of_neg (show 0<Q0 by norm_num [Q0]) hn
  nlinarith

lemma core_zero : (407/1000:ℝ)<core 0 := by
  have hu := NegativeTwo.TargetContact.Cap.zero_source_fine
  have hp := U_positive (outer_domain outer_zero_mem)
  have hlo : (957/500:ℝ)<U 0 := by linarith [hu.1]
  have hcube := pow_lt_pow_left₀ (by norm_num : (0:ℝ)≤957/500) hlo
    (by norm_num : (3:ℕ)≠0)
  have hD : ratioD 0<(2793/5000:ℝ) := by
    change Q0/(U 0)^3<(2793/5000:ℝ)
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at *
    nlinarith
  dsimp [core,slope]
  linarith [hu.2]

lemma core_endpoint : (103/5000:ℝ)<core endpoint := by
  have he : ratioD endpoint=Q0/(3/2)^3 := by
    change Q0/(U endpoint)^3=_
    rw [endpoint_circle]
  dsimp [core,slope]
  rw [he,endpoint_circle]
  norm_num [Q0]

lemma core_chord {b : ℝ} (hb : b∈Icc 0 endpoint) :
    (1/50:ℝ)+(12/25)*(endpoint-b)<core b := by
  have hconcave : ConcaveOn ℝ (Icc 0 endpoint)
      (fun t => core t-1/50-(12/25)*(endpoint-t)) := by
    apply concave_of_deriv2
      (fun t ht => ((core_hasDerivAt (source_mem ht)).sub_const (1/50)).sub
        (((hasDerivAt_id t).const_sub endpoint).const_mul (12/25)))
      (fun t ht => (coreFirst_hasDerivAt (source_mem ht)).add_const (12/25))
    intro t ht
    exact (coreSecond_negative (source_mem ht)).le
  have hlo : 0<core 0-1/50-(12/25)*(endpoint-0) := by
    linarith [core_zero,endpoint_bounds.2]
  have hhi : 0<core endpoint-1/50-(12/25)*(endpoint-endpoint) := by
    linarith [core_endpoint]
  have hh := concave_gt_of_endpoints hconcave hb hlo hhi
  linarith

lemma ratioD_half {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (1/2:ℝ)<ratioD b := by
  have hu := U_positive (outer_domain hb)
  have hU := (UW_bounds hb).2.1
  have hcube := pow_lt_pow_left₀ hu.le hU (by norm_num : (3:ℕ)≠0)
  change (1/2:ℝ)<Q0/(U b)^3
  apply (lt_div_iff₀ (pow_pos hu 3)).2
  norm_num [Q0] at *
  linarith

lemma loss_monotone : MonotoneOn loss (Icc 0 endpoint) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (loss_hasDerivAt (source_mem hb)).continuousAt.continuousWithinAt)
    (fun b hb => loss_hasDerivAt (source_mem (Ioo_subset_Icc_self hb)))
    (fun b hb => by
      have hh := ratioD_half (source_mem (Ioo_subset_Icc_self hb))
      dsimp [lossFirst,slope]
      linarith)

lemma loss_bounds {b : ℝ} (hb : b∈Icc 0 endpoint) : 0<loss b ∧ loss b<571/1000 := by
  have h0 := loss_monotone (show (0:ℝ)∈Icc 0 endpoint from ⟨le_rfl,endpoint_mem.1⟩) hb hb.1
  have h1 := loss_monotone hb (show endpoint∈Icc 0 endpoint from
    ⟨endpoint_mem.1,le_rfl⟩) hb.2
  have hz : 0<loss 0 := by
    have hr := (outer_ratio_bounds outer_zero_mem).1
    norm_num [loss,slope,W]
    linarith
  have he : loss endpoint<(571/1000:ℝ) := by
    have hr : ratio endpoint=W endpoint/(3/2) := by
      change W endpoint/U endpoint=_
      rw [endpoint_circle]
    dsimp [loss,slope]
    rw [hr]
    dsimp [W]
    linarith [endpoint_bounds.2]
  exact ⟨hz.trans_le h0,h1.trans_lt he⟩

lemma second_positive {b : ℝ} (hb : b∈Icc 0 endpoint) : 0<second b := by
  have hline := line_bounds hb
  have htr := positive_trig (line_mem hb)
  have ht := positive_taylor_reserves (line_mem hb)
  have hcos : (5/6:ℝ)<Real.cos (line b) := by
    have hs : (line b)^2≤(571/1000:ℝ)^2 := by nlinarith [hline.1,hline.2]
    nlinarith [ht.2.2]
  have hy : 0≤endpoint-b ∧ endpoint-b<(791/1000:ℝ) := by
    constructor <;> linarith [hb.1,hb.2,endpoint_bounds.2]
  have hc := core_chord hb
  have hcore : 0<core b := by linarith [hy.1]
  have hl := loss_bounds hb
  have hfirst := mul_lt_mul hc hcos (by norm_num : (0:ℝ)<5/6) hcore.le
  have hlast := mul_le_mul hl.2.le htr.2.2.2.2.1 htr.2.2.1
    (by norm_num : (0:ℝ)≤571/1000)
  have hlin : line b<(23/12500:ℝ)+(18/25)*(endpoint-b) := by
    dsimp [line,slope]
    linarith [endpoint_bounds.1]
  dsimp [second]
  nlinarith

lemma projection_zero : projection 0<(1/2:ℝ) := by
  have hc := cos_le_cos12 (show (0:ℝ)≤571/1000 by norm_num)
  have hs := sin11_le_sin (show (0:ℝ)≤571/1000 by norm_num)
  have hcos0 : 0≤Real.cos (571/1000) := by
    linarith [(positive_trig (show (571/1000:ℝ)∈Icc 0 (7/10) by norm_num)).1]
  have hu := NegativeTwo.TargetContact.Cap.zero_source_fine
  have hp := mul_le_mul
    (show U 0-1≤183/200 by linarith [hu.2]) hc hcos0
    (by norm_num : (0:ℝ)≤183/200)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hp hs
  dsimp [projection,line,slope,W]
  norm_num
  linarith

lemma projection_endpoint : projection endpoint<(1/2:ℝ) := by
  have hm : endpoint∈Icc 0 endpoint := ⟨endpoint_mem.1,le_rfl⟩
  have htr := positive_trig (line_mem hm)
  have ht := positive_taylor_reserves (line_mem hm)
  have hs : 0<Real.sin (line endpoint) := by
    nlinarith [(line_bounds hm).1,ht.1]
  have hw : 0<W endpoint := by dsimp [W]; linarith [endpoint_mem.1]
  have hp := mul_pos hw hs
  dsimp [projection]
  rw [endpoint_circle]
  linarith [htr.2.1]

lemma projection_upper {b : ℝ} (hb : b∈Icc 0 endpoint) : projection b<(1/2:ℝ) := by
  have hc : ConcaveOn ℝ (Icc 0 endpoint) (fun t => 1/2-projection t) :=
    concave_of_deriv2
      (fun t ht => (projection_hasDerivAt (source_mem ht)).const_sub (1/2))
      (fun t ht => (first_hasDerivAt (source_mem ht)).neg)
      (fun t ht => by linarith [second_positive ht])
  have hh := concave_gt_of_endpoints hc hb
    (by linarith [projection_zero]) (by linarith [projection_endpoint])
  linarith

lemma original_source_range {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=0) :
    b∈Icc 0 endpoint := by
  have hm := NegativeTwo.TargetContact.B_angle_monotone hb (by norm_num) hx hx.1
  rw [NegativeTwo.TargetContact.B_zero,hc] at hm
  have hs := UW_circle (outer_domain hb)
  have he := UW_circle (outer_domain endpoint_mem)
  rw [endpoint_circle] at he
  have hu : (3/2:ℝ)≤U b := by dsimp [U]; linarith
  have hb0 := endpoint_mem.1
  dsimp [W] at hs he
  refine ⟨hb.1,?_⟩
  nlinarith

theorem original_angle {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=0) :
    x<571/1000-(18/25)*b := by
  have hrange := original_source_range hb hx hc
  have hp := projection_upper hrange
  have he : NegativeTwo.TargetContact.B b (line b)=1/2-projection b := by
    dsimp [NegativeTwo.TargetContact.B,projection,U,W]
    ring
  by_contra hn
  have hle : line b≤x := by dsimp [line,slope]; linarith
  have hm := NegativeTwo.TargetContact.B_angle_monotone hb (line_mem hrange) hx hle
  rw [he,hc] at hm
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.ZeroAngle
