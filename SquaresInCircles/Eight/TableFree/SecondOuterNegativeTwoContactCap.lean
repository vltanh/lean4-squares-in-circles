module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoContactInverse
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# Exact endpoint references for the original circle contact

The axial radical is bracketed by integer squares.  At the physical
angle cap, adjacent Taylor supports prove a strictly positive target
coordinate.  No sampled angle range is used.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.TargetContact.Cap

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

lemma zero_target :
    (613013931/5000000000:ℝ)<B 0 (7/10) ∧
      B 0 (7/10)<613013935/5000000000 := by
  have hu := zero_source_fine
  have hc := ShortOuterOne.FiveSame.cap_fine
  have hs := sin11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hsu := sin_le_sin9 (show (0:ℝ)≤7/10 by norm_num)
  have hcos := cos10_le_cos (show (0:ℝ)≤7/10 by norm_num)
  have hcosu := cos_le_cos12 (show (0:ℝ)≤7/10 by norm_num)
  have hl := mul_le_mul hu.2.le hcosu
    (by linarith [hc.2.2.1] : 0≤Real.cos (7/10))
    (by norm_num : (0:ℝ)≤191457567100390/100000000000000)
  have hh := mul_le_mul hu.1.le hcos
    (by norm_num [cos10,cos8] : (0:ℝ)≤cos10 (7/10))
    (by linarith [hu.1] : 0≤U 0)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hsu hcos hcosu hl hh
  change (613013931/5000000000:ℝ)<
      1/2-(U 0-1)*Real.cos (7/10)+(1/2)*Real.sin (7/10) ∧
    1/2-(U 0-1)*Real.cos (7/10)+(1/2)*Real.sin (7/10)<613013935/5000000000
  constructor <;> nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.TargetContact.Cap
