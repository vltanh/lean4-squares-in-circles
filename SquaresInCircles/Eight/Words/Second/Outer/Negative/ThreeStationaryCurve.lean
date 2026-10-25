module

public import SquaresInCircles.Eight.Words.Second.Outer.KBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeStationaryAlgebra

/-!
# Eight squares: the target-coordinate curve forced by angular stationarity

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
