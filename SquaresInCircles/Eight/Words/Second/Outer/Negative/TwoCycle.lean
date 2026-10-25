module

public import Mathlib.Tactic
public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Second.Outer.LabelBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoCapValues
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeZeroTarget
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoDiagonalReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoPrimaryDiagonal
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoFirstOwners
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle

/-!
# Eight squares: original physical and cyclic negative edge-two inequalities

The literal role-two negative pair and its role-six positive reflection
retain the original weak owner.  The actual-cycle theorem uses the
existing selected separator, physical signs, common circle and quarter
lift; no new owner is chosen.
-/

section
/-!
## The physical source-diagonal boundary for negative edge three

The target label is increasing and strictly concave.  Its physical
contact coordinate is increasing and strictly concave as well.  Their
composition therefore makes the whole contact cost concave, without
an angle subdivision.  Both true endpoint costs exceed `.93`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Diagonal

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.PrimaryDiagonal

def cost (x : ℝ) : ℝ := value outerDiagonal (height x) (Real.pi/2-x)
def first (x : ℝ) : ℝ := -1+KLabel.d1 (height x)*speed x
def second (x : ℝ) : ℝ :=
  KLabel.d2 (height x)*(speed x)^2+KLabel.d1 (height x)*acceleration x

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x := by
  have hd := (((hasDerivAt_id' x).const_sub (Real.pi/2)).sub_const
    (T outerDiagonal)).add
      ((KLabel.outer_hasDerivAt (outer_domain (target_mem hx))).comp x
        (height_hasDerivAt hx.1))
  have hfun : cost=fun y => (Real.pi/2-y-T outerDiagonal)+KLabel.outer (height y) := by
    funext y
    simp only [cost,value,K]
  rw [hfun]
  exact hd

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x := by
  have hd := (((KLabel.d1_hasDerivAt (outer_domain (target_mem hx))).comp x
    (height_hasDerivAt hx.1)).mul (speed_hasDerivAt hx.1)).const_add (-1)
  exact hd.congr_deriv (by simp only [second,Function.comp_apply]; ring)

lemma second_negative {x : ℝ} (hx : Domain x) : second x<0 := by
  have hb := target_mem hx
  have hleft := mul_neg_of_neg_of_pos
    (show KLabel.d2 (height x)<0 by linarith [K_second_upper hb])
    (pow_pos (show 0<speed x by linarith [speed_positive hx.1]) 2)
  have hright := mul_neg_of_pos_of_neg
    (show 0<KLabel.d1 (height x) by linarith [(K_first_bounds hb).1])
    (acceleration_negative hx.1)
  dsimp [second]
  linarith

lemma zero_value : (93/100:ℝ)<cost 0 := by
  have hb : 1-outerDiagonal∈Icc 0 outerDiagonal := by
    constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]
  have hK := K_chord hb
  dsimp [cost,value]
  rw [height_zero]
  linarith [pi_hand_enclosure.1,T_diagonal_upper,K_zero_bounds.1,
    outer_endpoint_bounds.2.2.2]

lemma endpoint_value {e : ℝ} (he : e∈Icc (2/5) (139/250))
    (hc : height e=outerDiagonal) : (93/100:ℝ)<cost e := by
  dsimp [cost,value]
  rw [hc]
  linarith [pi_hand_enclosure.1,he.2,T_diagonal_upper,K_diagonal_lower]

theorem cost_lower {x : ℝ} (hx : Domain x) : (93/100:ℝ)<cost x := by
  obtain ⟨e,he,hc⟩ := end_contact
  have hefull : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
  have hed : Domain e := ⟨hefull,by rw [hc]⟩
  have hxe := bounded_by_end hx he hc
  have hconcave : ConcaveOn ℝ (Icc 0 e) cost := by
    apply concave_of_deriv2
      (fun t ht => cost_hasDerivAt (before hed ht))
      (fun t ht => first_hasDerivAt (before hed ht))
    intro t ht
    exact (second_negative (before hed ht)).le
  exact concave_gt_of_endpoints hconcave ⟨hx.1.1,hxe⟩ zero_value
    (endpoint_value he hc)

theorem original_contact {A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.lowerSource A B x=outerDiagonal) :
    (93/100:ℝ)<value outerDiagonal B (Real.pi/2-x) := by
  have he := original_height ht hx hc
  have hd : Domain x := ⟨hx,by rw [he]; exact (NegativeTwo.source_mem ht).2⟩
  simpa only [cost,he] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.NegativeThree.Diagonal
end
end
end

section
/-!
## The original lower source-primary weak owner for negative edge three

The actual contact moves monotonically in the source primary coordinate.
Its source-label increment strictly pays the angle change, by the
whole-arc speed estimate.  The first feasible contact therefore reduces
to alignment or the actual source-diagonal boundary.  The target square
and its original circle are unchanged in both comparisons.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic

lemma lower_active_monotone {A B l u : ℝ} (ht : OuterState A B)
    (hl : l∈Icc 0 (7/10)) (hu : u∈Icc 0 (7/10)) (_hlu : l≤u)
    (hleft : outerDiagonal≤NegativeTwo.lowerSource A B l)
    (hright : NegativeTwo.lowerSource A B u≤outerAxial) :
    MonotoneOn (fun t => -t+TPrimaryLabel.outer (NegativeTwo.lowerSource A B t))
      (Icc l u) := by
  have hdom (t : ℝ) (htime : t∈Icc l u) :
      t∈Icc 0 (7/10) ∧ NegativeTwo.lowerSource A B t∈Icc outerDiagonal outerAxial := by
    have htf : t∈Icc 0 (7/10) := ⟨hl.1.trans htime.1,htime.2.trans hu.2⟩
    exact ⟨htf,⟨hleft.trans (NegativeTwo.lowerSource_monotone ht hl htf htime.1),
      (NegativeTwo.lowerSource_monotone ht htf hu htime.2).trans hright⟩⟩
  have hd (t : ℝ) (htime : t∈Icc l u) :
      HasDerivAt (fun z => -z+TPrimaryLabel.outer (NegativeTwo.lowerSource A B z))
        (-1+TPrimaryLabel.d1 (NegativeTwo.lowerSource A B t)*
          NegativeTwo.lowerSpeed A B t) t := by
    have hc := (TPrimaryLabel.outer_hasDerivAt
      (primary_domain (hdom t htime).2)).comp t (NegativeTwo.lowerSource_hasDerivAt A B t)
    exact (hasDerivAt_neg' t).add hc
  exact monoOn_of_hasDeriv_nonneg
    (fun t htime => (hd t htime).continuousAt.continuousWithinAt)
    (fun t htime => hd t (Ioo_subset_Icc_self htime))
    (fun t htime => by
      have h := hdom t (Ioo_subset_Icc_self htime)
      linarith [lower_active_speed ht h.1 h.2])

theorem original_lower_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-x)) :
    (93/100:ℝ)<value b B (Real.pi/2-x) := by
  have hcut := NegativeTwo.lower_source_cut hx hm
  have ha := NegativeTwo.primary_mem hs
  have hactual := primary_actual hs
  by_cases hstart : outerDiagonal≤1-B
  · have hzero : outerDiagonal≤NegativeTwo.lowerSource A B 0 := by
      simpa only [NegativeTwo.lowerSource_zero] using hstart
    have hmono := lower_active_monotone ht (by norm_num) hx hx.1 hzero (hcut.trans ha.2)
    have hstep := hmono (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hx.1⟩)
      (show x∈Icc 0 x from ⟨hx.1,le_rfl⟩) hx.1
    have hxdom : NegativeTwo.lowerSource A B x∈Icc outerDiagonal outerAxial :=
      ⟨hzero.trans (NegativeTwo.lowerSource_monotone ht (by norm_num) hx hx.1),hcut.trans ha.2⟩
    have hM := primary_monotone hxdom ha hcut
    rw [hactual] at hM
    dsimp only at hstep
    rw [NegativeTwo.lowerSource_zero] at hstep
    have hbase := aligned_lower
      (show 1-B∈Icc outerDiagonal 1 from ⟨hstart,by linarith [ht.1]⟩)
    have harg : 1-(1-B)=B := by ring
    dsimp only [aligned] at hbase
    rw [harg] at hbase
    dsimp only [value]
    linarith
  · have hcont : Continuous (NegativeTwo.lowerSource A B) :=
      continuous_iff_continuousAt.2 fun t => (NegativeTwo.lowerSource_hasDerivAt A B t).continuousAt
    obtain ⟨y,hy,hycontact⟩ := intermediate_value_Icc
      (show (0:ℝ)≤7/10 by norm_num) hcont.continuousOn
      (show outerDiagonal∈Icc (NegativeTwo.lowerSource A B 0)
          (NegativeTwo.lowerSource A B (7/10)) by
        rw [NegativeTwo.lowerSource_zero]
        exact ⟨by linarith,(NegativeTwo.lowerSource_cap ht).le⟩)
    have hdiag := Diagonal.original_contact ht hy hycontact
    rcases le_total x y with hxy | hyx
    · have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
      have hT := T_monotone (NegativeTwo.source_mem hs) hd (NegativeTwo.source_mem hs).2
      dsimp only [value] at hdiag ⊢
      linarith
    · have hmono := lower_active_monotone ht hy hx hyx (by rw [hycontact]) (hcut.trans ha.2)
      have hstep := hmono (show y∈Icc y x from ⟨le_rfl,hyx⟩)
        (show x∈Icc y x from ⟨hyx,le_rfl⟩) hyx
      dsimp only at hstep
      rw [hycontact] at hstep
      have hxdom : NegativeTwo.lowerSource A B x∈Icc outerDiagonal outerAxial := by
        have hh := NegativeTwo.lowerSource_monotone ht hy hx hyx
        rw [hycontact] at hh
        exact ⟨hh,hcut.trans ha.2⟩
      have hM := primary_monotone hxdom ha hcut
      rw [hactual] at hM
      have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
      have hD : TPrimaryLabel.outer outerDiagonal= -T outerDiagonal := by
        have hh := primary_actual (ShortOuterOne.SameContact.arc_state hd)
        simpa only [ShortOuterOne.SameContact.arc_diagonal] using hh
      rw [hD] at hstep
      dsimp only [value] at hdiag ⊢
      linarith

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end

section
@[expose] public section

namespace SquaresInCircles.Eight.SecondWord.NegativeThree
open Set

theorem stationary_radius_curvature {k p t : ℝ}
    (hk : 0 < k) (hku : k < (116 / 125 : ℝ))
    (hp : p < -(221 / 1000 : ℝ)) (ht : t < -(371 / 500 : ℝ)) :
    -1 + t / k ^ 3 - 3 * p ^ 2 / k ^ 4 < -(2 : ℝ) := by
  have hk3 : 0 < k ^ 3 := pow_pos hk 3
  have hk4 : 0 < k ^ 4 := pow_pos hk 4
  have hk3u : k ^ 3 ≤ (116 / 125 : ℝ) ^ 3 := by
    gcongr
  have hk4u : k ^ 4 ≤ (116 / 125 : ℝ) ^ 4 := by
    gcongr
  have htq : t / k ^ 3 < -(9 / 10 : ℝ) := by
    apply (div_lt_iff₀ hk3).2
    nlinarith
  have hpsq : (221 / 1000 : ℝ) ^ 2 < p ^ 2 := by
    nlinarith [sq_nonneg (p + (221 / 1000 : ℝ))]
  have hpq : (19 / 100 : ℝ) < 3 * p ^ 2 / k ^ 4 := by
    apply (lt_div_iff₀ hk4).2
    nlinarith
  linarith

theorem stationary_projection_lower {u w z v : ℝ}
    (hu : u ∈ Ioo (219 / 125 : ℝ) (353 / 200 : ℝ))
    (hw : w ∈ Icc (1 / 2 : ℝ) (23 / 25 : ℝ))
    (hz : z ∈ Icc (-(1 / 2 : ℝ)) (-(2 / 5 : ℝ)))
    (hv : (1077 / 1000 : ℝ) < v) :
    (687 / 1000 : ℝ) <
      ((9789 / 2500 : ℝ) - u) /
          (u * ((9789 / 2500 : ℝ) + 1 - 2 * u)) +
        (w / u) * z / (((9789 / 2500 : ℝ) + 1 - 2 * u) * v) := by
  let q : ℝ := (9789 / 2500 : ℝ) + 1 - 2 * u
  have hu0 : 0 < u := by linarith [hu.1]
  have hq : q ∈ Ioo (866 / 625 : ℝ) (3529 / 2500 : ℝ) := by
    dsimp [q]
    constructor <;> linarith [hu.1, hu.2]
  have hq0 : 0 < q := by linarith [hq.1]
  have hv0 : 0 < v := by linarith
  have huq : u * q ≤ (353 / 200 : ℝ) * (3529 / 2500 : ℝ) :=
    mul_le_mul hu.2.le hq.2.le hq0.le (by norm_num)
  have hfirst : (863 / 1000 : ℝ) < ((9789 / 2500 : ℝ) - u) / (u * q) := by
    apply (lt_div_iff₀ (mul_pos hu0 hq0)).2
    nlinarith [hu.2]
  have hr0 : 0 ≤ w / u := div_nonneg (by linarith [hw.1]) hu0.le
  have hru : w / u < (115 / 219 : ℝ) := by
    apply (div_lt_iff₀ hu0).2
    nlinarith [hu.1, hw.2]
  have hrz : -(115 / 438 : ℝ) ≤ (w / u) * z := by
    have hmul := mul_le_mul_of_nonneg_left hz.1 hr0
    nlinarith
  have hqv : (866 / 625 : ℝ) * (1077 / 1000 : ℝ) ≤ q * v :=
    mul_le_mul hq.1.le hv.le (by norm_num) hq0.le
  have hsecond : -(22 / 125 : ℝ) < (w / u) * z / (q * v) := by
    apply (lt_div_iff₀ (mul_pos hq0 hv0)).2
    nlinarith
  change (687 / 1000 : ℝ) <
    ((9789 / 2500 : ℝ) - u) / (u * q) + (w / u) * z / (q * v)
  linarith

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end

section
/-!
## The target-coordinate curve forced by angular stationarity

Angular stationarity determines the original source primary coordinate
from the target coordinate and the actual target-label derivative.  Its
second derivative is less than `-2`; endpoint circle references and one
strengthened tangent put that coordinate in `(1.752,1.765)` throughout
the small-target interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.StationaryCurve

open CommonQuarter CorePairGeometry Arithmetic

def height (B : ℝ) : ℝ :=
  (Q0+1-(B-1/2)^2-1/(KLabel.d1 B)^2)/2
def first (B : ℝ) : ℝ := -(B-1/2)+KLabel.d2 B/(KLabel.d1 B)^3
def second (B : ℝ) : ℝ :=
  -1+KLabel.d3 B/(KLabel.d1 B)^3-3*(KLabel.d2 B)^2/(KLabel.d1 B)^4

lemma small_mem {B : ℝ} (hB : B∈Icc 0 (1/10)) : B∈Icc 0 outerDiagonal :=
  ⟨hB.1,by linarith [hB.2,fine_outer_endpoint_bounds.2]⟩

lemma slope_pos {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<KLabel.d1 B := by
  linarith [(K_first_bounds hB).1]

lemma height_identity {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    2*height B*(KLabel.d1 B)^2=
      (Q0+1-(B-1/2)^2)*(KLabel.d1 B)^2-1 := by
  dsimp [height]
  field_simp [(slope_pos hB).ne']

lemma height_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt height (first B) B := by
  have hk := KLabel.d1_hasDerivAt (outer_domain hB)
  have hrad := ((hasDerivAt_id' B).sub_const (1/2)).pow 2
  have hinv := (hasDerivAt_const B (1:ℝ)).div (hk.pow 2)
    (pow_ne_zero 2 (slope_pos hB).ne')
  have hd := ((hrad.const_sub (Q0+1)).sub hinv).div_const 2
  have hk0 := (slope_pos hB).ne'
  exact hd.congr_deriv (by
    simp only [first,Pi.pow_apply]
    norm_num
    field_simp
    ring)

lemma first_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt first (second B) B := by
  have hk := KLabel.d1_hasDerivAt (outer_domain hB)
  have hp := KLabel.d2_hasDerivAt (outer_domain hB)
  have hd := (((hasDerivAt_id' B).sub_const (1/2)).neg).add
    (hp.div (hk.pow 3) (pow_ne_zero 3 (slope_pos hB).ne'))
  have hk0 := (slope_pos hB).ne'
  exact hd.congr_deriv (by
    simp only [second,Pi.pow_apply]
    norm_num
    field_simp
    ring)

lemma second_upper {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : second B< -2 :=
  stationary_radius_curvature (slope_pos hB) (K_first_bounds hB).2
    (by linarith [K_second_upper hB]) (by linarith [K_third_upper hB])

lemma zero_slope_reference :
    (18558209/20000000:ℝ)<KLabel.d1 0 ∧ KLabel.d1 0<46395523/50000000 := by
  exact KLabel.first_chart_reference (outer_domain outer_zero_mem)
    (l := (191457567100389/100000000000000:ℝ))
    (u := (191457567100390/100000000000000:ℝ))
    (dlo := (18558209/20000000:ℝ)) (dhi := (46395523/50000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])

lemma zero_curvature_reference : KLabel.d2 0<(-4427713/20000000:ℝ) := by
  have hh := KLabel.second_chart_reference (outer_domain outer_zero_mem)
    (l := (191457567100389/100000000000000:ℝ))
    (u := (191457567100390/100000000000000:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-4427713/20000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])
  exact hh.2

lemma tenth_slope_reference :
    (90198827/100000000:ℝ)<KLabel.d1 (1/10) ∧
      KLabel.d1 (1/10)<22549707/25000000 := by
  have hm : (1/10:ℝ)∈Icc 0 outerDiagonal := small_mem (by norm_num)
  exact KLabel.first_chart_reference (outer_domain hm)
    (l := (188562986824031/100000000000000:ℝ))
    (u := (188562986824032/100000000000000:ℝ))
    (dlo := (90198827/100000000:ℝ)) (dhi := (22549707/25000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])

lemma tenth_curvature_reference : KLabel.d2 (1/10)<(-29783553/100000000:ℝ) := by
  have hm : (1/10:ℝ)∈Icc 0 outerDiagonal := small_mem (by norm_num)
  have hh := KLabel.second_chart_reference (outer_domain hm)
    (l := (188562986824031/100000000000000:ℝ))
    (u := (188562986824032/100000000000000:ℝ))
    (dlo := (-1:ℝ)) (dhi := (-29783553/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [KLabel,W,Q0]) (by norm_num [KLabel,W,Q0])
  exact hh.2

lemma zero_reference : (219/125:ℝ)<height 0 ∧ height 0<17521/10000 := by
  have hs := zero_slope_reference
  have hsqlo := pow_lt_pow_left₀ hs.1 (by norm_num : (0:ℝ)≤18558209/20000000)
    (by norm_num : (2:ℕ)≠0)
  have hsqhi := pow_lt_pow_left₀ hs.2 (slope_pos outer_zero_mem).le
    (by norm_num : (2:ℕ)≠0)
  have he := height_identity outer_zero_mem
  have hk : 0<(KLabel.d1 0)^2 := pow_pos (slope_pos outer_zero_mem) 2
  norm_num [Q0] at he hsqlo hsqhi
  constructor
  · by_contra h
    have hp := mul_nonneg (show 0≤219/125-height 0 by linarith) hk.le
    nlinarith
  · by_contra h
    have hp := mul_nonneg (show 0≤height 0-17521/10000 by linarith) hk.le
    nlinarith

lemma tenth_reference : (219/125:ℝ)<height (1/10) := by
  have hm : (1/10:ℝ)∈Icc 0 outerDiagonal := small_mem (by norm_num)
  have hs := tenth_slope_reference
  have hsq := pow_lt_pow_left₀ hs.1 (by norm_num : (0:ℝ)≤90198827/100000000)
    (by norm_num : (2:ℕ)≠0)
  have he := height_identity hm
  have hk : 0<(KLabel.d1 (1/10))^2 := pow_pos (slope_pos hm) 2
  norm_num [Q0] at he hsq
  by_contra h
  have hp := mul_nonneg (show 0≤219/125-height (1/10) by linarith) hk.le
  nlinarith

lemma first_zero_upper : first 0<(28/125:ℝ) := by
  have hk := slope_pos outer_zero_mem
  have hk3 := pow_pos hk 3
  have hc := pow_lt_pow_left₀ K_zero_first hk.le (by norm_num : (3:ℕ)≠0)
  have he : (first 0-1/2)*(KLabel.d1 0)^3=KLabel.d2 0 := by
    dsimp [first]
    field_simp [hk.ne']
    ring
  by_contra h
  have hp := mul_nonneg (show 0≤first 0-28/125 by linarith) hk3.le
  norm_num at hc
  nlinarith [zero_curvature_reference]

lemma height_concave : ConcaveOn ℝ (Icc 0 (1/10)) height :=
  concave_of_deriv2
    (fun B hB => height_hasDerivAt (small_mem hB))
    (fun B hB => first_hasDerivAt (small_mem hB))
    (fun B hB => by linarith [second_upper (small_mem hB)])

theorem height_bounds {B : ℝ} (hB : B∈Icc 0 (1/10)) :
    height B∈Ioo (219/125) (353/200) := by
  have hlo := concave_gt_of_endpoints height_concave hB zero_reference.1 tenth_reference
  have ht := curvature_tangent (f := fun t => -height t)
    (d := fun t => -first t) (dd := fun t => -second t) (κ := (2:ℝ))
    hB (show (0:ℝ)∈Icc 0 (1/10) by norm_num)
    (fun t ht => (height_hasDerivAt (small_mem ht)).neg)
    (fun t ht => (first_hasDerivAt (small_mem ht)).neg)
    (fun t ht => by linarith [second_upper (small_mem ht)])
  have hs := mul_le_mul_of_nonneg_right first_zero_upper.le hB.1
  refine ⟨hlo,?_⟩
  nlinarith [zero_reference.2,sq_nonneg (B-14/125)]

end SquaresInCircles.Eight.SecondWord.NegativeThree.StationaryCurve
end
end
end

section
/-!
## No interior contact minimum for the last negative edge-three owner

At an angular stationary point, targets at least `.1` give a negative
angular second derivative.  Smaller targets determine a narrow original
source-circle arc; its exact projection identity gives a strictly
positive source derivative.  Both conclusions concern the original
two-variable contact cost.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Contact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open NegativeTwo

def cost (b x : ℝ) : ℝ := value b (TargetContact.B b x) (Real.pi/2-x)
def sourceFirst (b x : ℝ) : ℝ :=
  -TLabel.d1 b+KLabel.d1 (TargetContact.B b x)*TargetContact.k b x
def angleFirst (b x : ℝ) : ℝ :=
  -1+KLabel.d1 (TargetContact.B b x)*TargetContact.v b x
def angleSecond (b x : ℝ) : ℝ :=
  KLabel.d2 (TargetContact.B b x)*(TargetContact.v b x)^2-
    KLabel.d1 (TargetContact.B b x)*(TargetContact.B b x-1/2)

lemma cost_source_hasDerivAt {b x : ℝ} (hd : TargetContact.Domain b x) :
    HasDerivAt (fun t => cost t x) (sourceFirst b x) b := by
  have hh := ((TLabel.outer_hasDerivAt (outer_domain hd.1)).neg).add
    ((KLabel.outer_hasDerivAt (outer_domain hd.2.2)).comp b
      (TargetContact.B_source_hasDerivAt hd.1 x))
  convert hh.const_add (Real.pi/2-x) using 1 <;>
    dsimp [cost,value,sourceFirst,T,K]
  ring_nf

lemma cost_angle_hasDerivAt {b x : ℝ} (hd : TargetContact.Domain b x) :
    HasDerivAt (cost b) (angleFirst b x) x := by
  have hh := (((hasDerivAt_id' x).const_sub (Real.pi/2)).sub_const (T b)).add
    ((KLabel.outer_hasDerivAt (outer_domain hd.2.2)).comp x
      (TargetContact.B_angle_hasDerivAt b x))
  exact hh.congr_deriv (by simp only [angleFirst])

lemma angleFirst_hasDerivAt {b x : ℝ} (hd : TargetContact.Domain b x) :
    HasDerivAt (angleFirst b) (angleSecond b x) x := by
  have hh := (((KLabel.d1_hasDerivAt (outer_domain hd.2.2)).comp x
    (TargetContact.B_angle_hasDerivAt b x)).mul
      (TargetContact.v_angle_hasDerivAt b x)).const_add (-1)
  exact hh.congr_deriv (by simp only [angleSecond,Function.comp_apply]; ring)

def charge (B : ℝ) : ℝ := KLabel.d2 B-(B-1/2)*(KLabel.d1 B)^3
def chargeFirst (B : ℝ) : ℝ :=
  KLabel.d3 B-(KLabel.d1 B)^3-3*(B-1/2)*(KLabel.d1 B)^2*KLabel.d2 B

lemma charge_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt charge (chargeFirst B) B := by
  have hk := KLabel.d1_hasDerivAt (outer_domain hB)
  have hh := (KLabel.d2_hasDerivAt (outer_domain hB)).sub
    (((hasDerivAt_id' B).sub_const (1/2)).mul (hk.pow 3))
  exact hh.congr_deriv (by simp only [chargeFirst,Pi.pow_apply]; norm_num; ring)

lemma chargeFirst_negative {B : ℝ} (hB : B∈Icc (1/10) (1/2)) :
    chargeFirst B<0 := by
  have hm : B∈Icc 0 outerDiagonal :=
    ⟨by linarith [hB.1],by linarith [hB.2,fine_outer_endpoint_bounds.2]⟩
  have hk : 0<KLabel.d1 B := StationaryCurve.slope_pos hm
  have hp := mul_nonneg_of_nonpos_of_nonpos
    (show B-1/2≤0 by linarith [hB.2])
    (show KLabel.d2 B≤0 by linarith [K_second_upper hm])
  have hprod := mul_nonneg (sq_nonneg (KLabel.d1 B)) hp
  dsimp [chargeFirst]
  nlinarith [K_third_upper hm,pow_pos hk 3]

lemma charge_tenth : charge (1/10)<0 := by
  have hm : (1/10:ℝ)∈Icc 0 outerDiagonal := StationaryCurve.small_mem (by norm_num)
  have hk := StationaryCurve.slope_pos hm
  have hh := pow_lt_pow_left₀ StationaryCurve.tenth_slope_reference.2 hk.le
    (by norm_num : (3:ℕ)≠0)
  dsimp [charge]
  norm_num at hh ⊢
  linarith [StationaryCurve.tenth_curvature_reference]

lemma charge_negative {B : ℝ} (hB : B∈Icc (1/10) outerDiagonal) : charge B<0 := by
  have hm : B∈Icc 0 outerDiagonal := ⟨by linarith [hB.1],hB.2⟩
  rcases le_total B (1/2) with h | h
  · have hanti : AntitoneOn charge (Icc (1/10) (1/2)) :=
      antiOn_of_hasDeriv_nonpos
        (fun t ht => (charge_hasDerivAt
          ⟨by linarith [ht.1],by linarith [ht.2,fine_outer_endpoint_bounds.2]⟩).continuousAt.continuousWithinAt)
        (fun t ht => charge_hasDerivAt
          ⟨by linarith [ht.1],by linarith [ht.2,fine_outer_endpoint_bounds.2]⟩)
        (fun t ht => (chargeFirst_negative (Ioo_subset_Icc_self ht)).le)
    exact (hanti (by norm_num) ⟨hB.1,h⟩ hB.1).trans_lt charge_tenth
  · have hp := mul_nonneg (show 0≤B-1/2 by linarith)
      (pow_nonneg (StationaryCurve.slope_pos hm).le 3)
    dsimp [charge]
    linarith [K_second_upper hm]

lemma angular_stationary_large {b x : ℝ} (hd : TargetContact.Domain b x)
    (hB : (1/10:ℝ)≤TargetContact.B b x) (hs : angleFirst b x=0) :
    angleSecond b x<0 := by
  have hk := StationaryCurve.slope_pos hd.2.2
  have hv := TargetContact.v_positive hd.1 hd.2.1
  have he : KLabel.d1 (TargetContact.B b x)*TargetContact.v b x=1 := by
    dsimp [angleFirst] at hs
    linarith
  have hvformula : TargetContact.v b x=1/KLabel.d1 (TargetContact.B b x) := by
    apply (eq_div_iff hk.ne').2
    simpa only [mul_comm] using he
  have hid : angleSecond b x=(TargetContact.v b x)^2*charge (TargetContact.B b x) := by
    rw [hvformula]
    dsimp [angleSecond,charge]
    rw [hvformula]
    field_simp [hk.ne']
  rw [hid]
  exact mul_neg_of_pos_of_neg (pow_pos hv 2) (charge_negative ⟨hB,hd.2.2.2⟩)

lemma stationary_height {b x : ℝ} (hd : TargetContact.Domain b x)
    (hs : angleFirst b x=0) : U b=StationaryCurve.height (TargetContact.B b x) := by
  have hk := StationaryCurve.slope_pos hd.2.2
  have hv : KLabel.d1 (TargetContact.B b x)*TargetContact.v b x=1 := by
    dsimp [angleFirst] at hs
    linarith
  have hv2 : (KLabel.d1 (TargetContact.B b x))^2*(TargetContact.v b x)^2=1 := by
    nlinarith [sq_nonneg (KLabel.d1 (TargetContact.B b x)*TargetContact.v b x-1)]
  have hn := TargetContact.norm_identity hd.1 x
  have hn' := congrArg (fun t : ℝ => t*(KLabel.d1 (TargetContact.B b x))^2) hn
  have hc := StationaryCurve.height_identity hd.2.2
  dsimp [NegativeTwo.Inverse.q] at hn'
  have he : (U b-StationaryCurve.height (TargetContact.B b x))*
      (KLabel.d1 (TargetContact.B b x))^2=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (pow_ne_zero 2 hk.ne'))

lemma projection_identity {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) :
    TargetContact.k b x/TargetContact.v b x=
      (Q0-U b)/(U b*NegativeTwo.Inverse.q (U b))+
        (W b/U b)*(TargetContact.B b x-1/2)/
          (NegativeTwo.Inverse.q (U b)*TargetContact.v b x) := by
  have hu := U_positive (outer_domain hb)
  have hq : 0<NegativeTwo.Inverse.q (U b) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hb]
  have hv := TargetContact.v_positive hb hx
  have hc := UW_circle (outer_domain hb)
  have hk : TargetContact.k b x=W b/U b*Real.cos x+Real.sin x := rfl
  have hB : TargetContact.B b x-1/2=-(U b-1)*Real.cos x+W b*Real.sin x := by
    simp only [TargetContact.B,U,W]; ring
  have hvv : TargetContact.v b x=(U b-1)*Real.sin x+W b*Real.cos x := by
    simp only [TargetContact.v,U,W]; ring
  have hqq : NegativeTwo.Inverse.q (U b)=Q0+1-2*U b := rfl
  rw [hk,hB]
  field_simp
  rw [hvv,hqq]
  linear_combination (-Real.sin x)*hc

lemma source_slope_reference : TLabel.d1 (197/500)<(17/25:ℝ) := by
  have hm : (197/500:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hh := TLabel.first_chart_reference (outer_domain hm)
    (l := (17653/10000:ℝ)) (u := (8827/5000:ℝ))
    (dlo := (0:ℝ)) (dhi := (17/25:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [TLabel,W,Q0]) (by norm_num [TLabel,W,Q0])
  exact hh.2

lemma source_slope_small {b : ℝ} (hb : b∈Icc (197/500) (21/50)) :
    TLabel.d1 b<(17/25:ℝ) := by
  have hanti : AntitoneOn TLabel.d1 (Icc (197/500) (21/50)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (TLabel.d1_hasDerivAt (outer_domain
        ⟨by linarith [ht.1],by linarith [ht.2,fine_outer_endpoint_bounds.2]⟩)).continuousAt.continuousWithinAt)
      (fun t ht => TLabel.d1_hasDerivAt (outer_domain
        ⟨by linarith [ht.1],by linarith [ht.2,fine_outer_endpoint_bounds.2]⟩))
      (fun t ht => by
        linarith [T_second_early (show t∈Icc 0 (3/5) from
          ⟨by linarith [ht.1],by linarith [ht.2]⟩)])
  exact (hanti (by norm_num) hb hb.1).trans_lt source_slope_reference

lemma angular_stationary_small {b x : ℝ} (hd : TargetContact.Domain b x)
    (hB : TargetContact.B b x≤(1/10:ℝ)) (hs : angleFirst b x=0) :
    0<sourceFirst b x := by
  have hu := StationaryCurve.height_bounds ⟨hd.2.2.1,hB⟩
  rw [←stationary_height hd hs] at hu
  have hc := UW_circle (outer_domain hd.1)
  have hw0 : (1/2:ℝ)≤W b := by dsimp [W]; linarith [hd.1.1]
  have hbsmall : b∈Ioo (197/500) (21/50) := by
    norm_num [Q0] at hc
    have hu2lo : (219/125:ℝ)^2<(U b)^2 := by nlinarith [hu.1]
    have hu2hi : (U b)^2<(353/200:ℝ)^2 := by nlinarith [hu.1,hu.2]
    dsimp [W] at hc hw0
    constructor <;> nlinarith
  have hvpos := TargetContact.v_positive hd.1 hd.2.1
  have hstat : KLabel.d1 (TargetContact.B b x)*TargetContact.v b x=1 := by
    dsimp [angleFirst] at hs
    linarith
  have hK := (K_first_bounds hd.2.2).2
  have hv : (1077/1000:ℝ)<TargetContact.v b x := by
    have hp := mul_lt_mul_of_pos_right hK hvpos
    nlinarith
  have hp := stationary_projection_lower hu
    (show W b∈Icc (1/2) (23/25) from ⟨hw0,by dsimp [W]; linarith [hbsmall.2]⟩)
    (show TargetContact.B b x-1/2∈Icc (-(1/2)) (-(2/5)) from
      ⟨by linarith [hd.2.2.1],by linarith⟩) hv
  have hproj := projection_identity hd.1 hd.2.1
  norm_num [Q0,NegativeTwo.Inverse.q] at hproj hp
  have he : KLabel.d1 (TargetContact.B b x)*TargetContact.k b x=
      TargetContact.k b x/TargetContact.v b x := by
    apply (eq_div_iff hvpos.ne').2
    linear_combination (TargetContact.k b x)*hstat
  dsimp [sourceFirst]
  rw [he]
  linarith [source_slope_small ⟨hbsmall.1.le,hbsmall.2.le⟩]

theorem stationary_alternatives {b x : ℝ} (hd : TargetContact.Domain b x)
    (hs : angleFirst b x=0) :
    angleSecond b x<0 ∨ 0<sourceFirst b x := by
  rcases le_total (1/10:ℝ) (TargetContact.B b x) with h | h
  · exact Or.inl (angular_stationary_large hd h hs)
  · exact Or.inr (angular_stationary_small hd h hs)

end SquaresInCircles.Eight.SecondWord.NegativeThree.Contact
end
end
end

section
/-!
## The full original diagonal-source contact boundary

On this boundary the physical angular speed has square greater than
`1.9556`.  The global target-label curvature already makes the cost
strictly concave on the entire feasible arc.  Its actual diagonal-target
end occurs before `.556`, and both endpoint costs exceed `.93`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.DiagonalSource

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig
open NegativeTwo.DiagonalSource (height speed Domain diagonal_mem domain_data domain_before)

def cost (x : ℝ) : ℝ := Contact.cost outerDiagonal x
def first (x : ℝ) : ℝ := Contact.angleFirst outerDiagonal x
def second (x : ℝ) : ℝ := Contact.angleSecond outerDiagonal x

lemma contact_domain {x : ℝ} (hx : Domain x) : NegativeTwo.TargetContact.Domain outerDiagonal x :=
  ⟨diagonal_mem,hx.1,(domain_data hx).1⟩

lemma cost_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt cost (first x) x :=
  Contact.cost_angle_hasDerivAt (contact_domain hx)

lemma first_hasDerivAt {x : ℝ} (hx : Domain x) : HasDerivAt first (second x) x :=
  Contact.angleFirst_hasDerivAt (contact_domain hx)

lemma second_negative {x : ℝ} (hx : Domain x) : second x<0 := by
  have hd := domain_data hx
  have hk := K_first_bounds hd.1
  have hk0 : 0<KLabel.d1 (height x) := by linarith [hk.1]
  have hneg := mul_lt_mul_of_pos_right (K_second_upper hd.1) (pow_pos hd.2.1 2)
  have habs := mul_lt_mul'' hk.2 hd.2.2.1 hk0.le (abs_nonneg (height x-1/2))
  have hlast : -KLabel.d1 (height x)*(height x-1/2)<(232/625:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (neg_le_abs (height x-1/2)) hk0.le
    nlinarith
  change KLabel.d2 (height x)*(speed x)^2-
    KLabel.d1 (height x)*(height x-1/2)<0
  nlinarith [hd.2.2.2]

lemma end_reference : outerDiagonal<height (139/250) := by
  have hs : Real.sin (139/250:ℝ)∈Icc (sin11 (139/250)) (sin9 (139/250)) :=
    ⟨sin11_le_sin (by norm_num),sin_le_sin9 (by norm_num)⟩
  have hc : Real.cos (139/250:ℝ)∈Icc (cos10 (139/250)) (cos12 (139/250)) :=
    ⟨cos10_le_cos (by norm_num),cos_le_cos12 (by norm_num)⟩
  have hh := NegativeTwo.DiagonalSource.point_cage hs hc
    (by norm_num [sin11,sin9,sin7]) (by norm_num [cos10,cos8])
  norm_num [NegativeTwo.DiagonalSource.dLo,NegativeTwo.DiagonalSource.dHi,
    sin11,sin9,sin7,cos12,cos10,cos8] at hh
  linarith [diagonal_fine.2]

lemma true_endpoint : ∃ e : ℝ, e∈Icc 0 (139/250) ∧ height e=outerDiagonal := by
  have hcont : Continuous (fun t => height t) := by
    dsimp only [height,NegativeTwo.TargetContact.B,ShortOuterOne.SameContact.arc]
    fun_prop
  obtain ⟨e,he,hc⟩ := intermediate_value_Icc (show (0:ℝ)≤139/250 by norm_num)
    hcont.continuousOn
    (show outerDiagonal∈Icc (height 0) (height (139/250)) by
      rw [NegativeTwo.DiagonalSource.height_zero]
      exact ⟨by linarith [fine_outer_endpoint_bounds.2],end_reference.le⟩)
  exact ⟨e,he,hc⟩

lemma speed_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) : 1<speed x := by
  have ht := positive_trig hx
  have hp := mul_nonneg
    (show 0≤outerDiagonal-1/2 by linarith [fine_outer_endpoint_bounds.2]) ht.2.2.1
  have hq := mul_nonneg
    (show 0≤outerDiagonal+1/2-1399/1000 by linarith [fine_outer_endpoint_bounds.2])
    (show 0≤Real.cos x by linarith [ht.1])
  dsimp [speed,NegativeTwo.TargetContact.v]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  nlinarith [ht.1]

lemma bounded_by_end {x e : ℝ} (hx : Domain x) (he : e∈Icc 0 (139/250))
    (hc : height e=outerDiagonal) : x≤e := by
  have hef : e∈Icc 0 (7/10) := ⟨he.1,by linarith [he.2]⟩
  have hmono : MonotoneOn (fun t => height t-t) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t _ => ((NegativeTwo.DiagonalSource.height_hasDerivAt t).sub
        (hasDerivAt_id t)).continuousAt.continuousWithinAt)
      (fun t _ => (NegativeTwo.DiagonalSource.height_hasDerivAt t).sub (hasDerivAt_id t))
      (fun t ht => by linarith [speed_lower (Ioo_subset_Icc_self ht)])
  rcases le_total x e with h | h
  · exact h
  · have hh := hmono hef hx.1 h
    dsimp only at hh
    rw [hc] at hh
    linarith [hx.2]

lemma zero_value : (93/100:ℝ)<cost 0 := by
  have hb : 1-outerDiagonal∈Icc 0 outerDiagonal := by
    constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]
  have hk := K_chord hb
  change (93/100:ℝ)<value outerDiagonal (height 0) (Real.pi/2-0)
  rw [NegativeTwo.DiagonalSource.height_zero]
  dsimp [value]
  linarith [pi_hand_enclosure.1,T_diagonal_upper,K_zero_bounds.1,
    outer_endpoint_bounds.2.2.2]

lemma endpoint_value {e : ℝ} (he : e∈Icc 0 (139/250))
    (hc : height e=outerDiagonal) : (93/100:ℝ)<cost e := by
  change (93/100:ℝ)<value outerDiagonal (height e) (Real.pi/2-e)
  rw [hc]
  dsimp [value]
  linarith [pi_hand_enclosure.1,he.2,T_diagonal_upper,K_diagonal_lower]

theorem cost_lower {x : ℝ} (hx : Domain x) : (93/100:ℝ)<cost x := by
  obtain ⟨e,he,hc⟩ := true_endpoint
  have hed : Domain e := ⟨⟨he.1,by linarith [he.2]⟩,by rw [hc]⟩
  have hxe := bounded_by_end hx he hc
  have hconcave : ConcaveOn ℝ (Icc 0 e) cost :=
    concave_of_deriv2
      (fun t ht => cost_hasDerivAt (domain_before hed ht))
      (fun t ht => first_hasDerivAt (domain_before hed ht))
      (fun t ht => (second_negative (domain_before hed ht)).le)
  exact concave_gt_of_endpoints hconcave ⟨hx.1.1,hxe⟩ zero_value (endpoint_value he hc)

theorem original_contact {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B outerDiagonal x=B) :
    (93/100:ℝ)<value outerDiagonal B (Real.pi/2-x) := by
  have hd : Domain x := ⟨hx,by
    change NegativeTwo.TargetContact.B outerDiagonal x≤outerDiagonal
    rw [hc]
    exact hB.2⟩
  simpa only [cost,Contact.cost,NegativeTwo.DiagonalSource.height,hc] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.NegativeThree.DiagonalSource
end
end
end

section
/-!
## The original diagonal-target contact boundary

At nonnegative shifted target coordinate, the exact inverse-angle
derivative has magnitude greater than `.8`.  Along the actual
diagonal-target arc the source-label derivative is below `.774`.
The fixed-target cost consequently increases with source coordinate,
and its minimum is the already bounded angle-cap endpoint.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.DiagonalTarget

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (ratio)

def shift : ℝ := outerDiagonal-1/2
def cost (b : ℝ) : ℝ :=
  Real.pi/2-NegativeTwo.ContactInverse.angle shift b-T b+K outerDiagonal
def first (b : ℝ) : ℝ := -NegativeTwo.ContactInverse.first shift b-TLabel.d1 b

lemma shift_mem : shift∈Icc (-(1/2)) (2/5) := by
  dsimp [shift]
  constructor <;> linarith [fine_outer_endpoint_bounds.2,outer_endpoint_bounds.2.2.2]

lemma shift_nonneg : 0≤ shift := by
  dsimp [shift]
  linarith [fine_outer_endpoint_bounds.2]

lemma cost_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt cost (first b) b := by
  have hh := (((NegativeTwo.ContactInverse.angle_hasDerivAt hb shift_mem).const_sub
    (Real.pi/2)).sub (TLabel.outer_hasDerivAt (outer_domain hb))).add_const (K outerDiagonal)
  exact hh

lemma first_positive {b : ℝ} (hb : b∈Icc (3/5) outerDiagonal) : 0<first b := by
  have hm : b∈Icc 0 outerDiagonal := ⟨by linarith [hb.1],hb.2⟩
  have hd := NegativeTwo.ContactInverse.data hm shift_mem
  have hq : 0<NegativeTwo.Inverse.q (U b) := by
    linarith [NegativeTwo.Inverse.actual_q_positive hm]
  have hf := NegativeTwo.Inverse.factor_lower hd.1 hq
  have hr : 0≤ratio b := (ShortOuterOne.SameContact.ratio_pos (outer_domain hm)).le
  have hp : 0≤ shift*ratio b/(NegativeTwo.Inverse.q (U b)*
      NegativeTwo.ContactInverse.speed shift b) :=
    div_nonneg (mul_nonneg shift_nonneg hr) (mul_nonneg hq.le hd.2.2.2.2.1.le)
  have ht := NegativeTwo.PrimaryDiagonal.target_first_late hb
  dsimp [first,NegativeTwo.ContactInverse.first]
  linarith

lemma cost_monotone : MonotoneOn cost (Icc (3/5) outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (cost_hasDerivAt ⟨by linarith [hb.1],hb.2⟩).continuousAt.continuousWithinAt)
    (fun b hb => cost_hasDerivAt ⟨by linarith [hb.1],hb.2.le⟩)
    (fun b hb => (first_positive (Ioo_subset_Icc_self hb)).le)

lemma endpoint_late {e : ℝ} (he : e∈Icc (2/5) Cap.endpointUpper)
    (hc : NegativeTwo.CapCurve.height e=outerDiagonal) : (3/5:ℝ)<e := by
  have hed := Cap.endpoint_domain he hc
  by_contra hh
  have hle : e≤(3/5:ℝ) := le_of_not_gt hh
  have hm := NegativeTwo.CapCurve.height_monotone hed.1 NegativeTwo.CapCurve.six_mem hle
  rw [hc] at hm
  linarith [NegativeTwo.CapCurve.six_cage.1.2,fine_outer_endpoint_bounds.2]

lemma source_after_cap {b e x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=outerDiagonal)
    (he : e∈Icc (2/5) Cap.endpointUpper)
    (hec : NegativeTwo.CapCurve.height e=outerDiagonal) : e≤b := by
  have hed := Cap.endpoint_domain he hec
  have hcap := NegativeTwo.TargetContact.B_angle_monotone hb hx (by norm_num) hx.2
  rw [hc] at hcap
  have hmono : MonotoneOn (fun t => NegativeTwo.CapCurve.height t-(4/5)*t)
      (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => ((NegativeTwo.CapCurve.height_hasDerivAt ht).sub
        ((hasDerivAt_id t).const_mul (4/5))).continuousAt.continuousWithinAt)
      (fun t ht => (NegativeTwo.CapCurve.height_hasDerivAt (Ioo_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).const_mul (4/5)))
      (fun t ht => by linarith [(NegativeTwo.CapCurve.k_bounds (Ioo_subset_Icc_self ht)).1])
  rcases le_total e b with h | h
  · exact h
  · have hh := hmono hb hed.1 h
    dsimp only at hh
    rw [hec] at hh
    change outerDiagonal≤NegativeTwo.CapCurve.height b at hcap
    linarith

lemma original_value {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=outerDiagonal) :
    cost b=value b outerDiagonal (Real.pi/2-x) := by
  have hd : NegativeTwo.TargetContact.Domain b x :=
    ⟨hb,hx,by rw [hc]; exact ⟨outer_zero_mem.2,le_rfl⟩⟩
  have hi := NegativeTwo.ContactInverse.original_angle hd
  rw [hc] at hi
  change NegativeTwo.ContactInverse.angle shift b=x at hi
  dsimp [cost,value]
  rw [hi]

theorem original_contact {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : NegativeTwo.TargetContact.B b x=outerDiagonal) :
    (44889/50000:ℝ)<value b outerDiagonal (Real.pi/2-x) := by
  obtain ⟨e,he,hec⟩ := Cap.true_endpoint
  have hed := Cap.endpoint_domain he hec
  have hlate := endpoint_late he hec
  have heb := source_after_cap hb hx hc he hec
  have hm := cost_monotone ⟨hlate.le,hed.1.2⟩ ⟨hlate.le.trans heb,hb.2⟩ heb
  have hcap := Cap.endpoint_value he hec
  have hevalue := original_value hed.1 (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hec
  have hbvalue := original_value hb hx hc
  rw [hevalue,hbvalue] at hm
  dsimp [Cap.cost] at hcap
  rw [hec] at hcap
  linarith

end SquaresInCircles.Eight.SecondWord.NegativeThree.DiagonalTarget
end
end
end

section
/-!
## The six boundary pieces of the last contact domain

Alignment, either source endpoint, either target endpoint and the final angle all have strict
bounds (`boundary_lower`). An original weak target-secondary axis also reaches a nonnegative
contact with no larger cost; its inactive portion ends at the zero-target contact by the
intermediate value theorem (`original_lower_contact`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Contact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open NegativeTwo

def Boundary (b x : ℝ) : Prop :=
  b=0 ∨ b=outerDiagonal ∨ x=0 ∨ x=7/10 ∨
    TargetContact.B b x=0 ∨ TargetContact.B b x=outerDiagonal

lemma aligned_contact_lower {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hc : TargetContact.B b 0=B) :
    (93/100:ℝ)<value b B (Real.pi/2) := by
  rw [TargetContact.B_zero] at hc
  exact original_aligned (ShortOuterOne.SameContact.arc_state hb)
    (ShortOuterOne.SameContact.arc_state hB) (by linarith)

lemma axial_angle_first {x : ℝ} (hd : TargetContact.Domain 0 x) : angleFirst 0 x<0 := by
  have hv := TargetContact.v_positive outer_zero_mem hd.2.1
  have hn := TargetContact.norm_identity outer_zero_mem x
  have hz : U 0=outerAxial+1/2 := by
    dsimp [U]
    rw [ShortOuterOne.SameContact.arc_zero]
  rw [hz] at hn
  have hvhi : TargetContact.v 0 x<(21/20:ℝ) := by
    norm_num [Inverse.q,Q0] at hn
    nlinarith [sq_nonneg (TargetContact.B 0 x-1/2),fine_outer_endpoint_bounds.1]
  have hK := (K_first_bounds hd.2.2).2
  have hp := mul_lt_mul hK hvhi.le hv (by norm_num : (0:ℝ)≤116/125)
  dsimp [angleFirst]
  norm_num at hp
  linarith

lemma axial_contact_lower {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : TargetContact.B 0 x=B) :
    (9/10:ℝ)<value 0 B (Real.pi/2-x) := by
  have hdom (t : ℝ) (ht : t∈Icc x (7/10)) : TargetContact.Domain 0 t := by
    have htf : t∈Icc 0 (7/10) := ⟨hx.1.trans ht.1,ht.2⟩
    have hlo := TargetContact.B_angle_monotone outer_zero_mem hx htf ht.1
    have hhi := TargetContact.B_angle_monotone outer_zero_mem htf (by norm_num) ht.2
    rw [hc] at hlo
    exact ⟨outer_zero_mem,htf,⟨hB.1.trans hlo,
      hhi.trans NegativeTwo.CapCurve.zero_domain.2⟩⟩
  have hanti : AntitoneOn (cost 0) (Icc x (7/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t ht => (cost_angle_hasDerivAt (hdom t ht)).continuousAt.continuousWithinAt)
      (fun t ht => cost_angle_hasDerivAt (hdom t (Ioo_subset_Icc_self ht)))
      (fun t ht => (axial_angle_first (hdom t (Ioo_subset_Icc_self ht))).le)
  have hm := hanti ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
  have hcap := Cap.zero_value
  change (9/10:ℝ)<cost 0 (7/10) at hcap
  have hh := hcap.trans_le hm
  simpa only [cost,hc] using hh

theorem boundary_lower {b x : ℝ} (hd : TargetContact.Domain b x)
    (hb : Boundary b x) : (89777/100000:ℝ)<cost b x := by
  rcases hb with hzero | hdiag | halign | hcap | hBzero | hBdiag
  · have hh := axial_contact_lower (by simpa only [hzero] using hd.2.2) hd.2.1 rfl
    rw [hzero]
    dsimp [cost]
    linarith
  · have hh := DiagonalSource.original_contact
      (by simpa only [hdiag] using hd.2.2) hd.2.1 rfl
    rw [hdiag]
    dsimp [cost]
    linarith
  · have hh := aligned_contact_lower hd.1 (by simpa only [halign] using hd.2.2) rfl
    rw [halign]
    dsimp [cost]
    rw [sub_zero]
    linarith
  · have hh := Cap.original_contact hd.1 (by simpa only [hcap] using hd.2.2) rfl
    rw [hcap]
    dsimp [cost]
    linarith
  · have hh := ZeroTarget.original_contact hd.1 hd.2.1 hBzero
    dsimp [cost]
    rw [hBzero]
    linarith
  · have hh := DiagonalTarget.original_contact hd.1 hd.2.1 hBdiag
    dsimp [cost]
    rw [hBdiag]
    linarith

theorem original_lower_contact {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    ∃ b' B', b'∈Icc 0 outerDiagonal ∧ B'∈Icc 0 outerDiagonal ∧
      TargetContact.B b' x=B' ∧ value b' B' (Real.pi/2-x)≤value b B (Real.pi/2-x) := by
  have hb := NegativeTwo.source_mem hs
  have hB := NegativeTwo.source_mem ht
  have hcut := NegativeTwo.lower_target_cut hs hx hm
  by_cases hpos : 0≤TargetContact.B b x
  · have hd : TargetContact.B b x∈Icc 0 outerDiagonal := ⟨hpos,hcut.trans hB.2⟩
    have hK := K_monotone hd hB hcut
    refine ⟨b,TargetContact.B b x,hb,hd,rfl,?_⟩
    dsimp [value]
    linarith
  · have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
    have hdiag := TargetContact.B_angle_monotone hd (by norm_num) hx hx.1
    rw [TargetContact.B_zero,ShortOuterOne.SameContact.arc_diagonal] at hdiag
    have hcont : Continuous (fun t => TargetContact.B t x) := by
      dsimp [TargetContact.B,arc]
      fun_prop
    obtain ⟨b',hb',he⟩ := intermediate_value_Icc hb.2 hcont.continuousOn
      (show (0:ℝ)∈Icc (TargetContact.B b x) (TargetContact.B outerDiagonal x) by
        constructor <;> linarith [outer_endpoint_bounds.2.2.2])
    have hbnew : b'∈Icc 0 outerDiagonal := ⟨hb.1.trans hb'.1,hb'.2⟩
    have hT := T_monotone hb hbnew hb'.1
    have hK := K_monotone outer_zero_mem hB hB.1
    refine ⟨b',0,hbnew,outer_zero_mem,he,?_⟩
    dsimp [value]
    linarith

end SquaresInCircles.Eight.SecondWord.NegativeThree.Contact
end
end
end

section
/-!
## The compact original contact minimum and the last weak owner

The actual contact region is the closed source-angle rectangle cut by
both original target-coordinate bounds.  Every interior minimizer is
angularly stationary.  A negative angular second derivative contradicts
minimality on an actual feasible angular interval; otherwise the proved
positive source derivative contradicts source stationarity.  The six
remaining boundary pieces are already bounded strictly.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology

namespace SquaresInCircles.Eight.SecondWord.NegativeThree.Contact

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo

lemma target_continuous : Continuous (fun p : ℝ×ℝ => TargetContact.B p.1 p.2) := by
  dsimp [TargetContact.B,ShortOuterOne.SameContact.arc]
  fun_prop

lemma cost_continuous : Continuous (fun p : ℝ×ℝ => cost p.1 p.2) := by
  dsimp [cost,value,T,K,RoleLabel.outer,RoleLabel.eval,TLabel,KLabel,
    TargetContact.B,ShortOuterOne.SameContact.arc]
  fun_prop

lemma angleSecond_continuousAt {b x : ℝ} (hd : TargetContact.Domain b x) :
    ContinuousAt (angleSecond b) x := by
  have hB := (TargetContact.B_angle_hasDerivAt b x).continuousAt
  have hK := (KLabel.d1_hasDerivAt (outer_domain hd.2.2)).continuousAt.comp hB
  have hK2 := (KLabel.d2_hasDerivAt (outer_domain hd.2.2)).continuousAt.comp hB
  have hv := (TargetContact.v_angle_hasDerivAt b x).continuousAt
  exact (hK2.mul (hv.pow 2)).sub (hK.mul (hB.sub continuousAt_const))

theorem interior_not_minimum {b x : ℝ}
    (hb : b∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hB : TargetContact.B b x∈Ioo 0 outerDiagonal)
    (hmin : ∀ u v, TargetContact.Domain u v → cost b x≤cost u v) : False := by
  have hd : TargetContact.Domain b x :=
    ⟨Ioo_subset_Icc_self hb,Ioo_subset_Icc_self hx,Ioo_subset_Icc_self hB⟩
  let O : Set ℝ := {t | t∈Ioo (0:ℝ) (7/10) ∧ TargetContact.B b t∈Ioo 0 outerDiagonal}
  have hcB : Continuous (fun t => TargetContact.B b t) := by
    dsimp only [TargetContact.B,ShortOuterOne.SameContact.arc]
    fun_prop
  have hO : IsOpen O := isOpen_Ioo.inter (isOpen_Ioo.preimage hcB)
  have hxO : x∈O := ⟨hx,hB⟩
  have hdom {t : ℝ} (ht : t∈O) : TargetContact.Domain b t :=
    ⟨hd.1,Ioo_subset_Icc_self ht.1,Ioo_subset_Icc_self ht.2⟩
  have hlocal : IsLocalMin (cost b) x := by
    filter_upwards [hO.mem_nhds hxO] with t ht
    exact hmin b t (hdom ht)
  have hstationary : angleFirst b x=0 :=
    hlocal.hasDerivAt_eq_zero (cost_angle_hasDerivAt hd)
  rcases stationary_alternatives hd hstationary with hnegative | hpositive
  · let κ : ℝ := -angleSecond b x/2
    have hk : 0<κ := by dsimp [κ]; linarith
    have hcurv : ∀ᶠ t in 𝓝 x, angleSecond b t<angleSecond b x/2 :=
      (angleSecond_continuousAt hd).tendsto.eventually
        (gt_mem_nhds (by linarith : angleSecond b x<angleSecond b x/2))
    have hneighborhood : {t | t∈O ∧ angleSecond b t<angleSecond b x/2}∈𝓝 x :=
      inter_mem (hO.mem_nhds hxO) hcurv
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hneighborhood
    apply not_minimum_on_strictly_concave_curve
      (s := {q : ℝ×ℝ | TargetContact.Domain q.1 q.2})
      (cost := fun q : ℝ×ℝ => cost q.1 q.2)
      (p := (b,x)) (fun q hq => hmin q.1 q.2 hq)
      (curve := fun t : ℝ => (b,t)) (value := cost b)
      (dvalue := angleFirst b) (ddvalue := angleSecond b)
      (O := Metric.ball x r) Metric.isOpen_ball
      (show x∈Metric.ball x r by simpa using hr) hk
    · rfl
    · intro t ht
      exact hdom (hsub ht).1
    · intros
      rfl
    · intro t ht
      exact cost_angle_hasDerivAt (hdom (hsub ht).1)
    · intro t ht
      exact angleFirst_hasDerivAt (hdom (hsub ht).1)
    · intro t ht
      have hh := (hsub ht).2
      dsimp [κ]
      linarith
  · let P : Set ℝ := {t | t∈Ioo (0:ℝ) outerDiagonal ∧ TargetContact.B t x∈Ioo 0 outerDiagonal}
    have hc : Continuous (fun t => TargetContact.B t x) := by
      dsimp [TargetContact.B,ShortOuterOne.SameContact.arc]
      fun_prop
    have hP : IsOpen P := isOpen_Ioo.inter (isOpen_Ioo.preimage hc)
    have hbP : b∈P := ⟨hb,hB⟩
    have hsourceLocal : IsLocalMin (fun t => cost t x) b := by
      filter_upwards [hP.mem_nhds hbP] with t ht
      exact hmin t x ⟨Ioo_subset_Icc_self ht.1,hd.2.1,Ioo_subset_Icc_self ht.2⟩
    have he := hsourceLocal.hasDerivAt_eq_zero (cost_source_hasDerivAt hd)
    linarith

theorem contact_lower {b x : ℝ} (hd : TargetContact.Domain b x) :
    (89777/100000:ℝ)<cost b x := by
  let guard : ℝ×ℝ→ℝ := fun p =>
    min (TargetContact.B p.1 p.2) (outerDiagonal-TargetContact.B p.1 p.2)
  have hg : Continuous guard := target_continuous.min (continuous_const.sub target_continuous)
  have hguard : 0≤guard (b,x) := by
    exact le_min hd.2.2.1 (sub_nonneg.mpr hd.2.2.2)
  obtain ⟨p,hp,hbetter,hmin⟩ := contact_region_minimum hg cost_continuous
    (p₀ := (b,x)) ⟨hd.1,hd.2.1,hguard⟩
  have hpguard := le_min_iff.mp hp.2.2
  have hpd : TargetContact.Domain p.1 p.2 :=
    ⟨hp.1,hp.2.1,⟨hpguard.1,by linarith [hpguard.2]⟩⟩
  have hpboundary : Boundary p.1 p.2 := by
    by_contra hn
    simp only [Boundary,not_or] at hn
    rcases hn with ⟨hb0,hbd,hx0,hxc,hB0,hBd⟩
    have hbi : p.1∈Ioo 0 outerDiagonal :=
      ⟨lt_of_le_of_ne hpd.1.1 (Ne.symm hb0),lt_of_le_of_ne hpd.1.2 hbd⟩
    have hxi : p.2∈Ioo 0 (7/10) :=
      ⟨lt_of_le_of_ne hpd.2.1.1 (Ne.symm hx0),lt_of_le_of_ne hpd.2.1.2 hxc⟩
    have hBi : TargetContact.B p.1 p.2∈Ioo 0 outerDiagonal :=
      ⟨lt_of_le_of_ne hpd.2.2.1 (Ne.symm hB0),lt_of_le_of_ne hpd.2.2.2 hBd⟩
    exact interior_not_minimum hbi hxi hBi (fun u v huv =>
      hmin (u,v) huv.1 huv.2.1 (le_min huv.2.2.1 (sub_nonneg.mpr huv.2.2.2)))
  exact (boundary_lower hpd hpboundary).trans_le hbetter

end SquaresInCircles.Eight.SecondWord.NegativeThree.Contact

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  obtain ⟨b',B',hb',hB',hc,hbetter⟩ := Contact.original_lower_contact hs ht hx hm
  have hd : NegativeTwo.TargetContact.Domain b' x :=
    ⟨hb',hx,by rw [hc]; exact hB'⟩
  have hh := Contact.contact_lower hd
  dsimp [Contact.cost] at hh
  rw [hc] at hh
  exact hh.trans_le hbetter

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end

section
/-!
## All original weak axes for the second-word negative edge three

Both closed half-angle intervals and all four original axes are
included.  The final target-secondary owner is proved by an actual
compact contact minimum and six complete boundary bounds.  The source
and target remain on the original common circle, including every weak
owner tie.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic

theorem original_scalar {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hx0 : 0≤x
  · have hupper : x∈Icc 0 (7/10) := ⟨hx0,hx.2⟩
    fin_cases j
    · linarith [original_upper_source_secondary hs ht hupper hm]
    · linarith [original_upper_target_primary hs ht hupper hm]
    · linarith [original_upper_target_secondary hs ht hupper hm]
    · linarith [original_upper_source_primary hs ht hupper hm]
  · have hlower : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [hx.1]⟩
    have he : Real.pi/2+x=Real.pi/2-(-x) := by ring
    rw [he] at hm ⊢
    fin_cases j
    · linarith [original_lower_source_secondary hs ht hlower hm]
    · linarith [original_lower_target_primary hs ht hlower hm]
    · exact original_lower_target_secondary hs ht hlower hm
    · linarith [original_lower_source_primary hs ht hlower hm]

theorem original_scalar_abs {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) :=
  original_scalar hs ht (abs_le.mp hx) j hm

theorem original_at_angle {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (89777/100000:ℝ)<value b B φ := by
  have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
  have hh := original_scalar_abs hs ht hφ j (by simpa only [he] using hm)
  simpa only [he] using hh

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end

section
/-!
## Original physical and cyclic negative edge-three inequalities

The literal role-three negative pair and its role-five positive
reflection retain the original separating axis.  The actual-cycle
theorem uses the existing selected weak separator, physical signs,
common circle and quarter lift, including every tied owner.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (89777/100000:ℝ)<SecondWord.cost 3 .outer .outer false false a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (89777/100000:ℝ)<SecondWord.cost 5 .outer .outer true true a b A B φ := by
  have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) (-1) φ := by
    simpa only [neg_neg] using
      (show 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-(1:ℝ)) (-(1:ℝ)) φ from by
        rw [margin_reflection]
        exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (3:Vertex) .outer .outer false false A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (σ τ : Bool)
    (hrole : (i=3 ∧ σ=false ∧ τ=false) ∨ (i=5 ∧ σ=true ∧ τ=true))
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    threshold i<SecondWord.cost i .outer .outer σ τ a b A B φ := by
  rw [threshold_value]
  rcases hrole with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hmargin : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_cost hs ht hφ j hmargin]
  · have hmargin : 0≤Eight.forwardMargin j a b A B 1 1 φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_reflected hs ht hφ j hmargin]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=3 ∧ positiveOf C i=false ∧ positiveOf C (next i)=false) ∨
      (i=5 ∧ positiveOf C i=true ∧ positiveOf C (next i)=true))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,ite_true] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,ite_true] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh := original_role i (positiveOf C i) (positiveOf C (next i)) hrole
    hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=3 ∧ positiveOf C i=false ∧ positiveOf C (next i)=false) ∨
      (i=5 ∧ positiveOf C i=true ∧ positiveOf C (next i)=true))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole hs ht j howner

end SquaresInCircles.Eight.SecondWord.NegativeThree
end
end
end

section
/-!
## The entire endpoint-angle contact has a strict scalar reserve

The whole-curve fourth derivative controls the initial concavity and
the later increasing curvature.  One tangent parabola at `.72365`
bounds the entire final interval, including its unknown feasible end.
The theorem below retains the actual original contact equation.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve

open CommonQuarter CorePairGeometry Arithmetic

lemma early_second {b : ℝ} (hb : b∈Icc 0 (1/5)) : second b<0 := by
  have hh := concave_gt_of_endpoints (negative_second_concave two_domain) hb
    (show (0:ℝ)< -second 0 by linarith [zero_second])
    (show (0:ℝ)< -second (1/5) by linarith [two_second])
  linarith

lemma early_value {b : ℝ} (hb : b∈Icc 0 (1/5)) : (9/10:ℝ)<cost b := by
  have hc := concave_of_deriv2
    (fun t ht => cost_hasDerivAt (before two_domain ht))
    (fun t ht => first_hasDerivAt (before two_domain ht))
    (fun t ht => (early_second ht).le)
  exact concave_gt_of_endpoints hc hb zero_value two_value

lemma tail_second_monotone {b : ℝ} (hb : Domain b) (hstart : (1/5:ℝ)≤b) :
    MonotoneOn second (Icc (1/5) b) := by
  have hdom (t : ℝ) (ht : t∈Icc (1/5) b) : Domain t :=
    before hb ⟨by linarith [ht.1],ht.2⟩
  have hthird (t : ℝ) (ht : t∈Icc (1/5) b) : 0<third t := by
    have hm := third_monotone hb (show (1/5:ℝ)∈Icc 0 b by exact ⟨by norm_num,hstart⟩)
      (show t∈Icc 0 b from ⟨by linarith [ht.1],ht.2⟩) ht.1
    linarith [two_third]
  exact monoOn_of_hasDeriv_nonneg
    (fun t ht => (second_hasDerivAt (hdom t ht)).continuousAt.continuousWithinAt)
    (fun t ht => second_hasDerivAt (hdom t (Ioo_subset_Icc_self ht)))
    (fun t ht => (hthird t (Ioo_subset_Icc_self ht)).le)

lemma middle_value {b : ℝ} (hb : b∈Icc (1/5) (3/5)) : (9/10:ℝ)<cost b := by
  have hdom (t : ℝ) (ht : t∈Icc (1/5) (3/5)) : Domain t :=
    before six_domain ⟨by linarith [ht.1],ht.2⟩
  have hthird (t : ℝ) (ht : t∈Icc (1/5) (3/5)) : 0≤third t := by
    have hm := third_monotone six_domain
      (show (1/5:ℝ)∈Icc 0 (3/5) by norm_num)
      (show t∈Icc 0 (3/5) from ⟨by linarith [ht.1],ht.2⟩) ht.1
    linarith [two_third]
  have hm := MinimumCalculus.endpoint_minimum hb
    (fun t ht => cost_hasDerivAt (hdom t ht))
    (fun t ht => first_hasDerivAt (hdom t ht))
    (fun t ht => second_hasDerivAt (hdom t ht))
    hthird six_first
  have hends : (9/10:ℝ)< min (cost (1/5)) (cost (3/5)) :=
    lt_min two_value (by linarith [six_value])
  exact hends.trans_le hm

lemma final_value {b : ℝ} (hb : Domain b) (hsix : (3/5:ℝ)≤b) :
    (44889/50000:ℝ)<cost b := by
  let u : ℝ := max b (14473/20000)
  have hu : Domain u := by
    rcases le_total b (14473/20000) with h | h
    · simpa only [u,max_eq_right h] using reference_domain
    · simpa only [u,max_eq_left h] using hb
  have hum : (3/5:ℝ)≤u := hsix.trans (le_max_left _ _)
  have hx : b∈Icc (3/5) u := ⟨hsix,le_max_left _ _⟩
  have ht : (14473/20000:ℝ)∈Icc (3/5) u := ⟨by norm_num,le_max_right _ _⟩
  have hdom (t : ℝ) (ht : t∈Icc (3/5) u) : Domain t :=
    before hu ⟨by linarith [ht.1],ht.2⟩
  have hcurv (t : ℝ) (ht : t∈Icc (3/5) u) : (13/20:ℝ)≤ second t := by
    have hm := tail_second_monotone hu (by linarith : (1/5:ℝ)≤u)
      (show (3/5:ℝ)∈Icc (1/5) u from ⟨by norm_num,hum⟩)
      (show t∈Icc (1/5) u from ⟨by linarith [ht.1],ht.2⟩) ht.1
    exact six_second.le.trans hm
  have htan := curvature_tangent (κ := (13/20:ℝ)) hx ht
    (fun t ht => cost_hasDerivAt (hdom t ht))
    (fun t ht => first_hasDerivAt (hdom t ht)) hcurv
  have hsmall := abs_lt.mp reference_first
  have hsq : (first (14473/20000))^2<(1/1000000000000:ℝ) := by
    nlinarith
  have hcomplete := sq_nonneg ((13/20)*(b-14473/20000)+first (14473/20000))
  nlinarith [reference_value]

theorem cost_lower {b : ℝ} (hb : Domain b) : (44889/50000:ℝ)<cost b := by
  rcases le_total b (1/5) with htwo | htwo
  · have hh := early_value ⟨hb.1.1,htwo⟩
    linarith
  · rcases le_total b (3/5) with hsix | hsix
    · have hh := middle_value ⟨htwo,hsix⟩
      linarith
    · exact final_value hb hsix

theorem original_contact {b B : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hB : B∈Icc 0 outerDiagonal) (hc : TargetContact.B b (7/10)=B) :
    (44889/50000:ℝ)<value b B (Real.pi/2-7/10) := by
  have hd : Domain b := ⟨hb,by simpa only [height,hc] using hB.2⟩
  simpa only [cost,height,hc] using cost_lower hd

end SquaresInCircles.Eight.SecondWord.NegativeTwo.CapCurve
end
end
end

section
/-!
## The entire diagonal-source lower contact

Before angle `2/5`, the increasing second derivative and negative final
slope force an endpoint minimum.  Afterwards its curvature exceeds
`3/10`, so the tangent parabola at angle `1/2` bounds the complete
physical tail.  The original contact endpoints are included.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.DiagonalSource

open CommonQuarter CorePairGeometry Arithmetic

lemma zero_value : (8977827/10000000:ℝ)<cost 0 := by
  have hz := domain_before four_domain (show (0:ℝ)∈Icc 0 (2/5) by norm_num)
  have hh := aligned_contact_lower diagonal_mem (domain_data hz).1
    (show TargetContact.B outerDiagonal 0=height 0 from rfl)
  simpa only [cost,sub_zero] using hh

lemma early_bound {x : ℝ} (hx : x∈Icc 0 (2/5)) :
    (8977827/10000000:ℝ)<cost x := by
  have hh := MinimumCalculus.endpoint_minimum hx
    (fun t ht => cost_hasDerivAt (domain_before four_domain ht))
    (fun t ht => first_hasDerivAt (domain_before four_domain ht))
    (fun t ht => second_hasDerivAt (domain_before four_domain ht))
    (fun t ht => (third_positive (domain_before four_domain ht)).le)
    four_first
  exact (lt_min zero_value (by linarith [four_value])).trans_le hh

lemma tail_bound {x : ℝ} (hx : Domain x) (hfour : 2/5≤x) :
    (2253/2500:ℝ)<cost x := by
  let u : ℝ := max x (1/2)
  have hu : Domain u := by
    by_cases hh : x≤1/2
    · simpa only [u,max_eq_right hh] using five_domain
    · simpa only [u,max_eq_left (le_of_not_ge hh)] using hx
  have hxu : x≤u := le_max_left _ _
  have h5u : (1/2:ℝ)≤u := le_max_right _ _
  have hdom {t : ℝ} (ht : t∈Icc (2/5) u) : Domain t :=
    domain_before hu ⟨by linarith [ht.1],ht.2⟩
  have hcurvature {t : ℝ} (ht : t∈Icc (2/5) u) : (3/10:ℝ)≤ second t := by
    have hm := second_monotone hu
      (show (2/5:ℝ)∈Icc 0 u from ⟨by norm_num,by linarith [h5u]⟩)
      ⟨by linarith [ht.1],ht.2⟩ ht.1
    exact four_second.le.trans hm
  have htan := curvature_tangent (κ := (3/10:ℝ))
    (show x∈Icc (2/5) u from ⟨hfour,hxu⟩)
    (show (1/2:ℝ)∈Icc (2/5) u from ⟨by norm_num,h5u⟩)
    (fun t ht => cost_hasDerivAt (hdom ht))
    (fun t ht => first_hasDerivAt (hdom ht))
    (fun t ht => hcurvature ht)
  have hfirst : (first (1/2))^2<(11/500:ℝ)^2 := by
    nlinarith [(abs_lt.mp five_first).1,(abs_lt.mp five_first).2]
  have hsq := sq_nonneg ((3/10:ℝ)*(x-1/2)+first (1/2))
  nlinarith [five_value]

theorem cost_lower {x : ℝ} (hx : Domain x) :
    (8977827/10000000:ℝ)<cost x := by
  rcases le_total x (2/5) with h|h
  · exact early_bound ⟨hx.1.1,h⟩
  · linarith [tail_bound hx h]

theorem original_contact {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (hc : TargetContact.B outerDiagonal x=B) :
    (8977827/10000000:ℝ)<value outerDiagonal B (Real.pi/2-x) := by
  have hd : Domain x := ⟨hx,by change TargetContact.B outerDiagonal x≤outerDiagonal; rw [hc]; exact hB.2⟩
  have hh := cost_lower hd
  simpa only [cost,height,hc] using hh

end SquaresInCircles.Eight.SecondWord.NegativeTwo.DiagonalSource
end
end
end

section
/-!
## The original lower target-secondary owner

Every original weak separator reaches a contact on the same circle. Source-coordinate concavity
reduces that contact to its four boundary types, each with a strict scalar reserve
(`original_lower_target_secondary`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic

lemma boundary_contact_lower {B : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (w : BoundaryContact B) :
    (89777/100000:ℝ)<value w.b B (Real.pi/2-w.x) := by
  rcases w.boundary with hax | hdiag | halign | hcap
  · have hc : TargetContact.B 0 w.x=B := by simpa only [hax] using w.contact
    have hh := axial_contact_lower hB w.angle hc
    rw [hax]
    linarith
  · have hc : TargetContact.B outerDiagonal w.x=B := by
      simpa only [hdiag] using w.contact
    have hh := DiagonalSource.original_contact hB w.angle hc
    rw [hdiag]
    linarith
  · have hc : TargetContact.B w.b 0=B := by simpa only [halign] using w.contact
    have hh := aligned_contact_lower w.source hB hc
    rw [halign,sub_zero]
    linarith
  · have hc : TargetContact.B w.b (7/10)=B := by simpa only [hcap] using w.contact
    have hh := CapCurve.original_contact w.source hB hc
    rw [hcap]
    linarith

theorem original_lower_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  obtain ⟨B',hB',w,hw⟩ := original_lower_boundary hs ht hx hm
  exact (boundary_contact_lower hB' w).trans_le hw

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end

section
/-!
## Every original weak owner for the second-word negative edge two

Both closed physical half-angle intervals and all four original axes are
included.  The lower target-secondary contact and the lower source-primary
contact have actual, complete boundary reductions.  No favorable owner
or endpoint is assumed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic

theorem original_scalar {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (-(7/10)) (7/10)) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) := by
  by_cases hx0 : 0≤x
  · have hupper : x∈Icc 0 (7/10) := ⟨hx0,hx.2⟩
    fin_cases j
    · linarith [original_upper_source_secondary hs ht hupper hm]
    · linarith [original_upper_target_primary hs ht hupper hm]
    · linarith [original_upper_target_secondary hs ht hupper hm]
    · linarith [original_upper_source_primary hs ht hupper hm]
  · have hlower : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [hx.1]⟩
    have he : Real.pi/2+x=Real.pi/2-(-x) := by ring
    rw [he] at hm ⊢
    fin_cases j
    · linarith [original_lower_source_secondary hs ht hlower hm]
    · linarith [original_lower_target_primary hs ht hlower hm]
    · exact original_lower_target_secondary hs ht hlower hm
    · linarith [original_lower_source_primary hs ht hlower hm]

theorem original_scalar_abs {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) (Real.pi/2+x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2+x) :=
  original_scalar hs ht (abs_le.mp hx) j hm

theorem original_at_angle {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (89777/100000:ℝ)<value b B φ := by
  have he : Real.pi/2+(φ-Real.pi/2)=φ := by ring
  have hh := original_scalar_abs hs ht hφ j (by simpa only [he] using hm)
  simpa only [he] using hh

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem original_cost {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ) :
    (89777/100000:ℝ)<SecondWord.cost 2 .outer .outer false false a b A B φ := by
  rw [cost_identity hs ht]
  exact original_at_angle hs ht hφ j hm

theorem original_reflected {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B 1 1 φ) :
    (89777/100000:ℝ)<SecondWord.cost 6 .outer .outer true true a b A B φ := by
  have hrev : 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-1) (-1) φ := by
    simpa only [neg_neg] using
      (show 0≤Eight.forwardMargin (reflectedOwner j) A B a b (-(1:ℝ)) (-(1:ℝ)) φ from by
        rw [margin_reflection]
        exact hm)
  have hh := original_cost ht hs hφ (reflectedOwner j) hrev
  have he := cost_reflection (2:Vertex) .outer .outer false false A B a b φ
  norm_num [reverseEdge] at he
  rwa [←he] at hh

theorem original_role (i : Vertex) (σ τ : Bool)
    (hrole : (i=2 ∧ σ=false ∧ τ=false) ∨ (i=6 ∧ σ=true ∧ τ=true))
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign τ) φ) :
    threshold i<SecondWord.cost i .outer .outer σ τ a b A B φ := by
  rw [threshold_value]
  rcases hrole with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hmargin : 0≤Eight.forwardMargin j a b A B (-1) (-1) φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_cost hs ht hφ j hmargin]
  · have hmargin : 0≤Eight.forwardMargin j a b A B 1 1 φ := by
      simpa [WordProblems.sign] using hm
    linarith [original_reflected hs ht hφ j hmargin]

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=2 ∧ positiveOf C i=false ∧ positiveOf C (next i)=false) ∨
      (i=6 ∧ positiveOf C i=true ∧ positiveOf C (next i)=true))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hk : F.word hgap pi_lt_22_over_7 i=1 := by
    rw [hw]
    rcases hrole with ⟨rfl,_,_⟩ | ⟨rfl,_,_⟩ <;> norm_num [WordProblems.wrongWord]
  have he : phaseValue F hgap i-Real.pi/2=difference F i := by
    simp [phaseValue,hk]
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F i).le
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa [State,hs] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa [State,ht] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh := original_role i (positiveOf C i) (positiveOf C (next i)) hrole
    hsource htarget hφ j hm
  simpa only [SecondWord.cost,label,wrongMarker,hs,ht] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex)
    (hrole : (i=2 ∧ positiveOf C i=false ∧ positiveOf C (next i)=false) ∨
      (i=6 ∧ positiveOf C i=true ∧ positiveOf C (next i)=true))
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hrole hs ht j howner

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end
