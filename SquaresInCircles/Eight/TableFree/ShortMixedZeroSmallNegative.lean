module

public import SquaresInCircles.Eight.TableFree.ShortMixedZeroOuter
public import SquaresInCircles.Eight.TableFree.FramePairCalculus

/-!
# The original negative-angle cutoff and the first small-slope family

The weak source-secondary inequality forces the whole feasible interval
to end before `.44152`. The first small-slope family's lower envelope
has a concave derivative that starts positive, hence its minimum is at
one of the two geometric endpoints. The endpoint comparisons use exact
Taylor bounds. Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortMixedZero

open CommonQuarter CorePairGeometry Arithmetic

def smallCap : ℝ := 5519/12500
def capMargin (x : ℝ) : ℝ := outerDiagonal-1/2+
  (CoreAngleEndpoint.diagonal-1/2)*Real.cos x-
    (CoreAngleEndpoint.diagonal+1/2)*Real.sin x
def capMarginD (x : ℝ) : ℝ :=
  -(CoreAngleEndpoint.diagonal-1/2)*Real.sin x-
    (CoreAngleEndpoint.diagonal+1/2)*Real.cos x

lemma capMargin_hasDerivAt (x : ℝ) : HasDerivAt capMargin (capMarginD x) x := by
  have hh : HasDerivAt (fun y => outerDiagonal-1/2+
      (CoreAngleEndpoint.diagonal-1/2)*Real.cos y-
        (CoreAngleEndpoint.diagonal+1/2)*Real.sin y)
      ((CoreAngleEndpoint.diagonal-1/2)*(-Real.sin x)-
        (CoreAngleEndpoint.diagonal+1/2)*Real.cos x) x :=
    (((Real.hasDerivAt_cos x).const_mul (CoreAngleEndpoint.diagonal-1/2)).const_add
      (outerDiagonal-1/2)).sub
        ((Real.hasDerivAt_sin x).const_mul (CoreAngleEndpoint.diagonal+1/2))
  exact hh.congr_deriv (by dsimp [capMarginD]; ring)

lemma capMargin_antitone : AntitoneOn capMargin (Icc 0 (7/10)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (capMargin_hasDerivAt x).continuousAt.continuousWithinAt
  · exact fun x _ => capMargin_hasDerivAt x
  · intro x hx
    have ht := positive_trig (Ioo_subset_Icc_self hx)
    have hc := CoreAngleEndpoint.diagonal_bounds
    have hs := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [hc.1]) ht.2.2.1
    have hk := mul_nonneg (show 0≤CoreAngleEndpoint.diagonal+1/2 by linarith [hc.1])
      (show 0≤Real.cos x by linarith [ht.1])
    dsimp [capMarginD]
    linarith

lemma smallCap_point_trig :
    (213657/500000:ℝ)<Real.sin smallCap ∧
      Real.cos smallCap<113013/125000 := by
  have hsc : smallCap=5519/12500 := rfl
  have hs := sin_lower_seven (x := smallCap) (by norm_num [smallCap])
  have hcU := cos_le_cos8 (x := smallCap) (by norm_num [smallCap])
  rw [hsc] at hs hcU ⊢
  norm_num [cos8] at hs hcU
  exact ⟨by linarith,by linarith⟩

lemma capMargin_smallCap_neg : capMargin smallCap<0 := by
  have ht := smallCap_point_trig
  have hc := CoreAngleEndpoint.diagonal_bounds
  have hd := fine_diagonal_bounds
  have hp := mul_le_mul_of_nonneg_left ht.2.le
    (show 0≤CoreAngleEndpoint.diagonal-1/2 by linarith [hc.1])
  have hn := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤CoreAngleEndpoint.diagonal+1/2 by linarith [hc.1])
  dsimp [capMargin]
  nlinarith [hd.2,hc.1,hc.2]

/-- This cutoff is derived from the actual outer/core states and the
original weak source-secondary owner, before a role coefficient is used. -/
theorem negative_angle_cut {a b A B x : ℝ} (hs : OuterState a b)
    (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    x<smallCap := by
  have htr := positive_trig hx
  have hb := (outer_bounds hs).2.2.2.1
  have hA := core_primary_lower ht
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.2.2
  have hprim := mul_le_mul_of_nonneg_right hA htr.2.2.1
  have hsec := mul_le_mul_of_nonneg_right hB (show 0≤Real.cos x by linarith [htr.1])
  have hbound : 0≤capMargin x := by dsimp [capMargin]; linarith
  by_contra! hlarge
  have hcap : smallCap∈Icc 0 (7/10) := by norm_num [smallCap]
  have hh := capMargin_antitone hcap hx hlarge
  linarith [capMargin_smallCap_neg]

def firstNegative (x : ℝ) : ℝ :=
  -x+c 0+g 0*CoreAngleEndpoint.diagonal+q 0/2+
    q 0*(1/2-CoreAngleEndpoint.diagonal)*Real.cos x+
      q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.sin x
def firstNegativeD (x : ℝ) : ℝ :=
  -1+q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.sin x+
    q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos x
def firstNegativeDD (x : ℝ) : ℝ :=
  q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.cos x-
    q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.sin x
def firstNegativeDDD (x : ℝ) : ℝ :=
  -q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.sin x-
    q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos x

lemma firstNegative_hasDerivAt (x : ℝ) :
    HasDerivAt firstNegative (firstNegativeD x) x := by
  have hh : HasDerivAt (fun y => -y+c 0+g 0*CoreAngleEndpoint.diagonal+q 0/2+
      q 0*(1/2-CoreAngleEndpoint.diagonal)*Real.cos y+
        q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.sin y)
      (-1+q 0*(1/2-CoreAngleEndpoint.diagonal)*(-Real.sin x)+
        q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos x) x :=
    (((((hasDerivAt_id' x).neg.add_const (c 0)).add_const
      (g 0*CoreAngleEndpoint.diagonal)).add_const (q 0/2)).add
        ((Real.hasDerivAt_cos x).const_mul (q 0*(1/2-CoreAngleEndpoint.diagonal)))).add
          ((Real.hasDerivAt_sin x).const_mul (q 0*(1/2+CoreAngleEndpoint.diagonal)))
  exact hh.congr_deriv (by dsimp [firstNegativeD]; ring)

lemma firstNegativeD_hasDerivAt (x : ℝ) :
    HasDerivAt firstNegativeD (firstNegativeDD x) x := by
  have hh : HasDerivAt (fun y => -1+q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.sin y+
      q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos y)
      (q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.cos x+
        q 0*(1/2+CoreAngleEndpoint.diagonal)*(-Real.sin x)) x :=
    (((Real.hasDerivAt_sin x).const_mul (q 0*(CoreAngleEndpoint.diagonal-1/2))).const_add (-1)).add
      ((Real.hasDerivAt_cos x).const_mul (q 0*(1/2+CoreAngleEndpoint.diagonal)))
  exact hh.congr_deriv (by dsimp [firstNegativeDD]; ring)

lemma firstNegativeDD_hasDerivAt (x : ℝ) :
    HasDerivAt firstNegativeDD (firstNegativeDDD x) x := by
  have hh : HasDerivAt (fun y => q 0*(CoreAngleEndpoint.diagonal-1/2)*Real.cos y-
      q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.sin y)
      (q 0*(CoreAngleEndpoint.diagonal-1/2)*(-Real.sin x)-
        q 0*(1/2+CoreAngleEndpoint.diagonal)*Real.cos x) x :=
    ((Real.hasDerivAt_cos x).const_mul (q 0*(CoreAngleEndpoint.diagonal-1/2))).sub
      ((Real.hasDerivAt_sin x).const_mul (q 0*(1/2+CoreAngleEndpoint.diagonal)))
  exact hh.congr_deriv (by dsimp [firstNegativeDDD]; ring)

lemma firstNegativeD_concave : ConcaveOn ℝ (Icc 0 smallCap) firstNegativeD := by
  apply concave_of_deriv2 (fun x _ => firstNegativeD_hasDerivAt x)
    (fun x _ => firstNegativeDD_hasDerivAt x)
  intro x hx
  have ht := positive_trig ⟨hx.1,hx.2.trans (by norm_num [smallCap])⟩
  have hq : 0≤q 0 := by norm_num [q]
  have hd : 0≤CoreAngleEndpoint.diagonal-1/2 := by linarith [CoreAngleEndpoint.diagonal_bounds.1]
  have hs := mul_nonneg (mul_nonneg hq hd) ht.2.2.1
  have hc := mul_nonneg (mul_nonneg hq (show 0≤1/2+CoreAngleEndpoint.diagonal by linarith))
    (show 0≤Real.cos x by linarith [ht.1])
  dsimp [firstNegativeDDD]
  linarith

lemma firstNegative_endpoints :
    0≤firstNegativeD 0 ∧ (449/500:ℝ)<firstNegative 0 ∧
      (449/500:ℝ)<firstNegative smallCap := by
  have hd := CoreAngleEndpoint.diagonal_bounds
  have ht := smallCap_point_trig
  have hsin := mul_le_mul_of_nonneg_left ht.1.le
    (show 0≤1/2+CoreAngleEndpoint.diagonal by linarith [hd.1])
  have hcos := mul_le_mul_of_nonpos_left ht.2.le
    (show 1/2-CoreAngleEndpoint.diagonal≤0 by linarith [hd.1])
  have hsc : smallCap=5519/12500 := rfl
  refine ⟨?_,?_,?_⟩
  · norm_num [firstNegativeD,q]
    nlinarith [hd.1]
  · norm_num [firstNegative,c,q,g]
    nlinarith [hd.1,hd.2]
  · norm_num [firstNegative,c,q,g]
    linarith [hd.1,hd.2]

lemma firstNegative_lower {x : ℝ} (hx : x∈Icc 0 smallCap) :
    (449/500:ℝ)<firstNegative x := by
  have hh := FramePairCalculus.endpoint_minimum_of_concave_derivative hx
    (fun z _ => firstNegative_hasDerivAt z) firstNegativeD_concave firstNegative_endpoints.1
  exact (lt_min firstNegative_endpoints.2.1 firstNegative_endpoints.2.2).trans_le hh

/-- The first small-slope family, including its complete negative half,
both core pieces and every original weak contact. -/
theorem opposite_outer_negative_first {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (449/500:ℝ)< -x+c 0-p 0*a+q 0*b+g 0*B := by
  have hcut := negative_angle_cut hs ht hx hm
  have hh := firstNegative_lower ⟨hx.1,hcut.le⟩
  have htr := positive_trig hx
  have hq : 0<q 0 := by norm_num [q]
  have hcoef : g 0-q 0*Real.cos x≤0 := by
    have hm := mul_lt_mul_of_pos_left htr.1 hq
    norm_num [q,g] at hm ⊢
    linarith
  have hcore := core_diagonal_lower (X := q 0*Real.sin x) (Y := g 0-q 0*Real.cos x)
    ht (mul_nonneg hq.le htr.2.2.1) hcoef
  have hsep := mul_nonneg hq.le (sub_nonneg.mpr hm)
  dsimp [firstNegative] at hh
  norm_num [p]
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortMixedZero
