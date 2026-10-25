module

public import SquaresInCircles.Eight.Frames.Low.HighGeometry
public import SquaresInCircles.Eight.Frames.Low.HighParallelCalculus

/-!
# Eight squares: original-margin bounds for the explicit parallel contact path

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
