module

public import SquaresInCircles.Eight.Frames.Low.HighExtendedQuarter
public import SquaresInCircles.Eight.Frames.Low.HighGeometry
public import SquaresInCircles.Eight.Frames.Low.HighParallelCalculus

/-!
# Eight squares: the low/high parallel strip

A positive low source and a negative high target separated along the secondary axis of the low
square, at a frame angle `|x| ≤ 1/50`, have the cost of the pair above `8833/10000`
(`low_high_strip`). The target is held fixed, and the source moves along its segment of secondary
contact to the angle `0`, where the cost is that of an aligned contact; along the segment the
source coordinate is given by a formula, and the derivative of its marker has the sign that lowers
the cost (`low_move_to_zero`, `low_phase`). The markers are extended beyond the cuts of the types,
so the segment may cross a cut while the pair and its axis stay the same.
-/

section
/-!
## An enlarged parallel-contact support

The analytic labels are continued slightly past the intrinsic type
cuts.  Their aligned sum still has curvature greater than `1/5` on the
entire enlarged interval.  This permits an explicit source-coordinate
comparison in the narrow parallel strip, without selecting another
physical owner or presuming a continuation inside the type arcs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighExtendedAligned
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned

def domain : Set ℝ := Icc (7/100:ℝ) (7/20)

theorem chart_domain {b : ℝ} (hb : b∈domain) :
    b∈extendedDomain ∧ 1-b∈extendedDomain := by
  dsimp [domain,extendedDomain] at *
  constructor <;> constructor <;> linarith [hb.1,hb.2]

theorem parallel_deriv {b : ℝ} (hb : b∈domain) : HasDerivAt parallel (parallelD b) b := by
  have hd := chart_domain hb
  have hm : HasDerivAt (fun y : ℝ => 1-y) (-1) b := (hasDerivAt_id' b).const_sub 1
  have h := (extended_L_deriv hd.1).fun_add ((extended_H_deriv hd.2).comp b hm)
  refine h.congr_deriv ?_
  simp only [parallelD]
  ring

theorem parallelD_deriv {b : ℝ} (hb : b∈domain) :
    HasDerivAt parallelD (parallelDD b) b := by
  have hd := chart_domain hb
  have hm : HasDerivAt (fun y : ℝ => 1-y) (-1) b := (hasDerivAt_id' b).const_sub 1
  have h := (extended_Ld_deriv hd.1).fun_sub ((extended_Hd_deriv hd.2).comp b hm)
  refine h.congr_deriv ?_
  simp only [parallelDD]
  ring

theorem curvature {b : ℝ} (hb : b∈domain) : (1/5:ℝ)<parallelDD b := by
  have hd := chart_domain hb
  have hc := extended_circle hd.1
  have ht := extended_circle hd.2
  have hp := extended_shift_pos hd.1
  have htp := extended_shift_pos hd.2
  have hbU : b+1/2≤17/20 := by dsimp [domain] at hb; linarith [hb.2]
  have hbsq := pow_le_pow_left₀ (by dsimp [domain] at hb; linarith [hb.1] : 0≤b+1/2) hbU 2
  have hA : (89/50:ℝ)<A b+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hAcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤89/50) hA.le 3
  have hsource : slopeD b<7/10 := by
    dsimp [slopeD]
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    norm_num [Q0] at *
    nlinarith
  have hbL : (23/20:ℝ)≤1-b+1/2 := by dsimp [domain] at hb; linarith [hb.2]
  have htbsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤23/20) hbL 2
  have htA : A (1-b)+1/2<81/50 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤81/50) hbad 2
    norm_num [Q0] at ht
    nlinarith
  have htAcube := pow_le_pow_left₀ htp.le htA.le 3
  have htarget : (91/100:ℝ)<slopeD (1-b) := by
    dsimp [slopeD]
    apply (lt_div_iff₀ (pow_pos htp 3)).2
    norm_num [Q0] at *
    nlinarith
  dsimp [parallelDD,FrameLowArc.u,FrameHighArc.u]
  linarith

theorem lower {b : ℝ} (hb : b∈domain) :
    F0-(5/2)*d0^2≤L b+H (1-b) := by
  have hb0 : b0∈domain := by constructor <;> linarith [b0_bounds.1,b0_bounds.2]
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (1/5:ℝ)) (fun z hz => parallel_deriv hz)
    (fun z hz => parallelD_deriv hz) (fun z hz => (curvature hz).le) hb0 hb
  rw [FrameLowHighAligned.parallel_initial.1,FrameLowHighAligned.parallel_initial.2] at hh
  dsimp [parallel] at hh
  nlinarith [sq_nonneg (b-b0+5*d0)]

theorem reserve : (8833/10000:ℝ)<F0-(5/2)*d0^2 := by
  have hd := mul_pos (sub_pos.mpr d0_bounds.2)
    (show 0<(1/10000:ℝ)+d0 by linarith [d0_bounds.1])
  nlinarith [F0_lower]

theorem strict_lower {b : ℝ} (hb : b∈domain) :
    (8833/10000:ℝ)<L b+H (1-b) := reserve.trans_le (lower hb)

end SquaresInCircles.Eight.FrameLowHighExtendedAligned
end
end
end

section
/-!
## Original-margin bounds for the explicit parallel contact path

Every path domain is derived from the original feasible pair.  The
source height is explicit, so the marker derivative bounds apply to
the entire segment from the original angle to zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighParallelBounds
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FrameLowHighParallelCalculus

def segment (positive : Bool) (x : ℝ) : Set ℝ :=
  if positive then Icc 0 x else Icc x 0
def lowCost (positive : Bool) (B x : ℝ) : ℝ :=
  x-(9/50)*(FrameLowHighParallelCalculus.width positive x-1)+L (height positive B x)+H B
def highCost (positive : Bool) (B x : ℝ) : ℝ :=
  x-(9/50)*(FrameLowHighParallelCalculus.width positive x-1)+H (height positive B x)+L B
def lowD (positive : Bool) (B x : ℝ) : ℝ :=
  1-(9/50)*widthD positive x-Ld (height positive B x)*P positive B x
def highD (positive : Bool) (B x : ℝ) : ℝ :=
  1-(9/50)*widthD positive x-Hd (height positive B x)*P positive B x

theorem segment_angle (positive : Bool) {x t : ℝ}
    (hx : x∈angleDomain positive) (ht : t∈segment positive x) : t∈angleDomain positive := by
  cases positive <;> dsimp [angleDomain,segment] at * <;> constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]

theorem height_between (positive : Bool) {B x t : ℝ} (hB : B∈Icc 0 c0)
    (hx : x∈angleDomain positive) (ht : t∈segment positive x) :
    if positive then height positive B x≤height positive B t ∧ height positive B t≤1-B
    else 1-B≤height positive B t ∧ height positive B t≤height positive B x := by
  have hta := segment_angle positive hx ht
  have hzero : (0:ℝ)∈angleDomain positive := by cases positive <;> constructor <;> norm_num [angleDomain]
  have hm := height_antitone positive hB
  cases positive with
  | false =>
      have hts : t∈Icc x 0 := by simpa [segment] using ht
      have h0 := hm hta hzero hts.2
      have h1 := hm hx hta hts.1
      simpa only [height_zero,Bool.false_eq_true,ite_false] using And.intro h0 h1
  | true =>
      have hts : t∈Icc 0 x := by simpa [segment] using ht
      have h0 := hm hta hx hts.2
      have h1 := hm hzero hta hts.1
      simpa only [height_zero,ite_true] using And.intro h0 h1

theorem height_le_source (positive : Bool) {b B x : ℝ}
    (hx : x∈angleDomain positive) (hm : 0≤ secondary true false b B x) :
    height positive B x≤b := by
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
  dsimp [height]
  rw [width_eq positive hx]
  linarith

theorem high_target_cut (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true false b B x) : (651/1000:ℝ)<B := by
  have ht := trig_small positive hx
  have ha := high_bounds hB
  have hAs := mul_le_mul_of_nonneg_left ht.2.1 (by linarith [ha.2.2.1] : 0≤A B)
  have hBc := mul_le_mul_of_nonneg_left ht.2.2.2.1 (b2_mem.1.trans hB.1)
  have hw := FrameCoreArc.width_one_le x
  dsimp [secondary,FrameLowMidGeometry.secondary,sign] at hm
  nlinarith [hb.2,b1_bounds.2]

theorem low_height_lower (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) : (7/100:ℝ)<height positive B x := by
  have ht := trig_small positive hx
  have ha := high_bounds hB
  have hAs := mul_le_mul_of_nonneg_left ht.2.1 (by linarith [ha.2.2.1] : 0≤A B)
  have hBc := mul_le_mul_of_nonneg_left ht.2.2.2.1 (b2_mem.1.trans hB.1)
  have hw := FrameCoreArc.width_one_le x
  rw [← width_eq positive hx] at hw
  dsimp [height]
  nlinarith

theorem low_height_domain (positive : Bool) {b B x t : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true false b B x) (ht : t∈segment positive x) :
    height positive B t∈Icc (0:ℝ) (7/20) := by
  have hl := low_height_lower positive hB (segment_angle positive hx ht)
  have hh := height_between positive ⟨b2_mem.1.trans hB.1,hB.2⟩ hx ht
  have hc := high_target_cut positive hb hB hx hm
  have hs := height_le_source positive hx hm
  cases positive <;> dsimp at hh <;> constructor <;> linarith [hb.2,b1_bounds.2]

theorem lowCost_deriv (positive : Bool) {B x : ℝ}
    (hz : height positive B x∈Icc (0:ℝ) (7/20)) :
    HasDerivAt (lowCost positive B) (lowD positive B x) x := by
  have hd : height positive B x∈extendedDomain := by constructor <;> linarith [hz.1,hz.2]
  have h := (((hasDerivAt_id' x).fun_sub
    (((width_deriv positive x).sub_const 1).const_mul (9/50))).fun_add
      ((extended_L_deriv hd).comp x (height_deriv positive B x))).add_const (H B)
  refine h.congr_deriv ?_
  simp only [lowD]
  ring

theorem highCost_deriv (positive : Bool) {B x : ℝ}
    (hz : height positive B x∈Icc (16/25:ℝ) (93/100)) :
    HasDerivAt (highCost positive B) (highD positive B x) x := by
  have hd : height positive B x∈extendedDomain := by constructor <;> linarith [hz.1,hz.2]
  have h := (((hasDerivAt_id' x).fun_sub
    (((width_deriv positive x).sub_const 1).const_mul (9/50))).fun_add
      ((extended_H_deriv hd).comp x (height_deriv positive B x))).add_const (L B)
  refine h.congr_deriv ?_
  simp only [highD]
  ring

theorem lowD_sign (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) (hz : height positive B x∈Icc (0:ℝ) (7/20)) :
    if positive then 0<lowD positive B x else lowD positive B x<0 := by
  have hd := low_derivative_bounds hz
  have hp := high_target_P positive hB hx
  have hp0 := P_positive positive ⟨b2_mem.1.trans hB.1,hB.2⟩ hx
  have hw := widthD_bounds positive hx
  cases positive with
  | false =>
      have hm := mul_le_mul hd.1.le hp.le (by norm_num : (0:ℝ)≤69/50)
        (by linarith [hd.1] : 0≤Ld (height false B x))
      simp only [Bool.false_eq_true,↓reduceIte] at hw
      dsimp [lowD]
      linarith
  | true =>
      have hm := mul_le_mul hd.2.le hp.le hp0.le (by norm_num : (0:ℝ)≤109/100)
      simp only [↓reduceIte] at hw
      dsimp [lowD]
      linarith

theorem width_charge (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    FrameLowHighParallelCalculus.width positive x-1=periodicFrameCost x := by
  rw [width_eq positive hx]
  dsimp [pairWidth,periodicFrameCost]
  ring

end SquaresInCircles.Eight.FrameLowHighParallelBounds
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighParallel
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighGeometry FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds

theorem segment_self (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    x∈segment positive x := by
  cases positive <;> simp only [angleDomain,FrameLowHighParallelBounds.segment,Bool.false_eq_true,ite_false,ite_true] at *
  · exact ⟨le_rfl,hx.2⟩
  · exact ⟨hx.1,le_rfl⟩

@[simp] theorem lowCost_zero (positive : Bool) (B : ℝ) :
    lowCost positive B 0=L (1-B)+H B := by
  cases positive <;> simp [lowCost,height,FrameLowHighParallelCalculus.width]

@[simp] theorem highCost_zero (positive : Bool) (B : ℝ) :
    highCost positive B 0=H (1-B)+L B := by
  cases positive <;> simp [highCost,height,FrameLowHighParallelCalculus.width]

theorem low_move_to_zero (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true false b B x) :
    lowCost positive B 0≤lowCost positive B x := by
  have hd t (ht : t∈segment positive x) :=
    lowCost_deriv positive (low_height_domain positive hb hB hx hm ht)
  cases positive with
  | false =>
      have hc : AntitoneOn (lowCost false B) (Icc x 0) := by
        apply antiOn_of_hasDeriv_nonpos
        · intro t ht
          exact (hd t (by simpa [FrameLowHighParallelBounds.segment] using ht)).continuousAt.continuousWithinAt
        · intro t ht
          exact hd t (by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht)
        · intro t ht
          have hts : t∈segment false x := by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht
          exact (lowD_sign false hB (segment_angle false hx hts)
            (low_height_domain false hb hB hx hm hts)).le
      exact hc ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2
  | true =>
      have hc : MonotoneOn (lowCost true B) (Icc 0 x) := by
        apply monoOn_of_hasDeriv_nonneg
        · intro t ht
          exact (hd t (by simpa [FrameLowHighParallelBounds.segment] using ht)).continuousAt.continuousWithinAt
        · intro t ht
          exact hd t (by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht)
        · intro t ht
          have hts : t∈segment true x := by simpa [FrameLowHighParallelBounds.segment] using Ioo_subset_Icc_self ht
          exact (lowD_sign true hB (segment_angle true hx hts)
            (low_height_domain true hb hB hx hm hts)).le
      exact hc ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1

theorem low_phase (positive : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0) (hx : x∈angleDomain positive)
    (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  have hcut := high_target_cut positive hb hB hx hm
  have haligned : 1-B∈FrameLowHighExtendedAligned.domain := by
    constructor <;> linarith [hB.2,c0_bounds.2]
  have hz := FrameLowHighExtendedAligned.strict_lower haligned
  have hcancel : 1-(1-B)=B := by ring
  rw [hcancel] at hz
  have hzero : (8833/10000:ℝ)<lowCost positive B 0 := by
    simpa only [lowCost_zero] using hz
  have hmove := low_move_to_zero positive hb hB hx hm
  have hpath := low_height_domain positive hb hB hx hm (segment_self positive hx)
  have hbwide : b∈Icc (0:ℝ) (7/20) := ⟨hb.1,by linarith [hb.2,b1_bounds.2]⟩
  have hlabel := low_label_monotone hpath hbwide (height_le_source positive hx hm)
  have hcontact : lowCost positive B x≤lowHighCost true false b B x := by
    dsimp [lowCost,lowHighCost,sign]
    rw [width_charge positive hx]
    linarith
  exact hzero.trans_le (hmove.trans hcontact)

theorem low_high_strip {b B x : ℝ} (hb : b∈Icc 0 b1) (hB : B∈Icc b2 c0)
    (hx : x∈Icc (-(1/50:ℝ)) (1/50)) (hm : 0≤ secondary true false b B x) :
    (8833/10000:ℝ)<lowHighCost true false b B x := by
  by_cases hsign : x≤0
  · exact low_phase false hb hB ⟨hx.1,hsign⟩ hm
  · exact low_phase true hb hB ⟨le_of_not_ge hsign,hx.2⟩ hm

end SquaresInCircles.Eight.FrameLowHighParallel
end
end
end
