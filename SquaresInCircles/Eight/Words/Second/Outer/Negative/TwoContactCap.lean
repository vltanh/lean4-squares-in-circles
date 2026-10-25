module

public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeData

/-!
# Eight squares: exact endpoint references for the original circle contact

The axial radical is bracketed by integer squares.  At the physical
angle cap, adjacent Taylor supports prove a strictly positive target
coordinate.  No sampled angle range is used.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.TargetContact.Cap

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig
open ShortOuterOne.SameContact (arc)

lemma two_mem : (1/5:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma zero_source_fine :
    (191457567100389/100000000000000:ℝ)<U 0 ∧
      U 0<191457567100390/100000000000000 :=
  Asymmetric.shifted_reference outer_zero_mem
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])

lemma zero_source :
    (1914575671/1000000000:ℝ)<U 0 ∧ U 0<239321959/125000000 := by
  constructor <;> linarith [zero_source_fine.1,zero_source_fine.2]

private lemma r17_sin_le_sin13 {x : ℝ} (hx : 0≤x) :
    Real.sin x ≤ sin11 x+x^13/6227020800 := by
  have hh := nonneg_of_deriv_nonneg (fun t => sin11 t+t^13/6227020800-Real.sin t)
    (by dsimp [sin11,sin9,sin7]; fun_prop)
    (by norm_num [sin11,sin9,sin7])
    (fun t ht => by
      simp (disch := fun_prop) [sin11,sin9,sin7]
      have hc := cos_le_cos12 ht
      dsimp [cos12,cos10,cos8] at hc
      linarith) hx
  linarith

private lemma r17_cos14_le_cos {x : ℝ} (hx : 0≤x) :
    cos12 x-x^14/87178291200≤Real.cos x := by
  have hh := nonneg_of_deriv_nonneg (fun t => Real.cos t-(cos12 t-t^14/87178291200))
    (by dsimp [cos12,cos10,cos8]; fun_prop)
    (by norm_num [cos12,cos10,cos8])
    (fun t ht => by
      simp (disch := fun_prop) [cos12,cos10,cos8]
      have hs := r17_sin_le_sin13 ht
      dsimp [sin11,sin9,sin7] at hs
      linarith) hx
  linarith

lemma zero_target :
    (613013931/5000000000:ℝ)<B 0 (7/10) ∧
      B 0 (7/10)<613013935/5000000000 := by
  have hu := zero_source_fine
  have hc := ShortOuterOne.FiveSame.cap_fine
  have hs := sin11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hsu := r17_sin_le_sin13 (show (0:ℝ)≤7/10 by norm_num)
  have hcos := r17_cos14_le_cos (show (0:ℝ)≤7/10 by norm_num)
  have hcosu := cos_le_cos12 (show (0:ℝ)≤7/10 by norm_num)
  have hl := mul_le_mul
    (show U 0-1≤191457567100390/100000000000000-1 by linarith) hcosu
    (by linarith [hc.2.2.1] : 0≤Real.cos (7/10))
    (by norm_num : (0:ℝ)≤191457567100390/100000000000000-1)
  have hh := mul_le_mul
    (show 191457567100389/100000000000000-1≤U 0-1 by linarith) hcos
    (by norm_num [cos12,cos10,cos8] : (0:ℝ)≤cos12 (7/10)-(7/10)^14/87178291200)
    (by linarith [hu.1] : 0≤U 0-1)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hsu hcos hcosu hl hh
  have he : B 0 (7/10)=1/2-(U 0-1)*Real.cos (7/10)+(1/2)*Real.sin (7/10) := by
    simp only [B,U]
    ring
  rw [he]
  constructor <;> linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo.TargetContact.Cap
