module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoInverse

/-!
# The original secondary contact on an outer circle

Both the source-coordinate and angle derivatives are derived from the
same original circle chart.  The norm identity retains the exact
contact speed and gives the inverse-angle radical without a new radius.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.TargetContact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def B (b x : ℝ) : ℝ :=
  1/2-(arc b-1/2)*Real.cos x+(b+1/2)*Real.sin x
def v (b x : ℝ) : ℝ :=
  (arc b-1/2)*Real.sin x+(b+1/2)*Real.cos x
def k (b x : ℝ) : ℝ := ratio b*Real.cos x+Real.sin x
def Domain (b x : ℝ) : Prop :=
  b∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ B b x∈Icc 0 outerDiagonal

lemma B_zero (b : ℝ) : B b 0=1-arc b := by norm_num [B]; ring

lemma B_source_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => B t x) (k b x) b := by
  have hd := ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).sub_const
    (1/2)).mul_const (Real.cos x)).const_sub (1/2)).fun_add
      (((hasDerivAt_id' b).add_const (1/2)).mul_const (Real.sin x))
  exact hd.congr_deriv (by dsimp [k]; ring)

lemma k_source_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => k t x) (ratioD b*Real.cos x) b :=
  ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hb)).mul_const
    (Real.cos x)).add_const (Real.sin x)

lemma B_angle_hasDerivAt (b x : ℝ) : HasDerivAt (B b) (v b x) x := by
  have hd := (((Real.hasDerivAt_cos x).const_mul (arc b-1/2)).const_sub
    (1/2)).fun_add ((Real.hasDerivAt_sin x).const_mul (b+1/2))
  exact hd.congr_deriv (by dsimp [v]; ring)

lemma v_angle_hasDerivAt (b x : ℝ) :
    HasDerivAt (v b) (1/2-B b x) x := by
  have hd := ((Real.hasDerivAt_sin x).const_mul (arc b-1/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (b+1/2))
  exact hd.congr_deriv (by dsimp [B]; ring)

lemma v_source_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => v t x) (Real.cos x-ratio b*Real.sin x) b := by
  have hd := (((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).sub_const
    (1/2)).mul_const (Real.sin x)).fun_add
      (((hasDerivAt_id' b).add_const (1/2)).mul_const (Real.cos x))
  exact hd.congr_deriv (by ring)

lemma k_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<k b x := by
  have hr := ShortOuterOne.SameContact.ratio_pos (outer_domain hb)
  have ht := positive_trig hx
  have hp := mul_pos hr (show 0<Real.cos x by linarith [ht.1])
  dsimp [k]
  linarith [ht.2.2.1]

lemma v_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<v b x := by
  have hu := UW_bounds hb
  have ht := positive_trig hx
  have hsin := mul_nonneg (show 0≤arc b-1/2 by dsimp [U] at hu; linarith [hu.1])
    ht.2.2.1
  have hcos := mul_pos (show 0<b+1/2 by linarith [hb.1])
    (show 0<Real.cos x by linarith [ht.1])
  dsimp [v]
  linarith

lemma B_source_monotone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun b => B b x) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (B_source_hasDerivAt hb x).continuousAt.continuousWithinAt)
    (fun b hb => B_source_hasDerivAt (Ioo_subset_Icc_self hb) x)
    (fun b hb => (k_positive (Ioo_subset_Icc_self hb) hx).le)

lemma B_angle_monotone {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    MonotoneOn (B b) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (B_angle_hasDerivAt b x).continuousAt.continuousWithinAt)
    (fun x _ => B_angle_hasDerivAt b x)
    (fun x hx => (v_positive hb (Ioo_subset_Icc_self hx)).le)

lemma norm_identity {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    (B b x-1/2)^2+(v b x)^2=Inverse.q (U b) := by
  have hc := UW_circle (outer_domain hb)
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [B,v,Inverse.q,U,W] at *
  linear_combination hc+((arc b-1/2)^2+(b+1/2)^2)*ht

lemma contact_norm_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    1<Inverse.q (U b) := by linarith [Inverse.actual_q_positive hb]

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.TargetContact
