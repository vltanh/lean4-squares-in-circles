module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyCutReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeZeroData

/-!
# Eight squares: the two finite references on the original zero-source arc

The references at `1.3` and `1.4` use only Taylor inequalities and
the original circle square.  They provide the initial scalar reserve,
both label slopes, and the positive target curvature at `1.4`.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

lemma left_curve :
    y parameter (13/10)∈Icc (133176429/10^8:ℝ) (133176479/10^8) ∧
      u parameter (13/10)∈Icc (17664687/10^7:ℝ) (17664702/10^7) ∧
      w parameter (13/10)∈Icc (8917320/10^7:ℝ) (8917336/10^7) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter (13/10)∈Icc (799/1000:ℝ) (4/5) ∧
      fp parameter (13/10)∈Icc (679/1000:ℝ) (17/25) := by
  have hh := SourceReference.curve (domain left_mem) parameter_nonnegative.1
    EarlyCut.right_trig.1 EarlyCut.right_trig.2
    (yl := (133176429/10^8:ℝ)) (yh := (133176479/10^8:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [parameter,Q0]) (by norm_num [parameter,Q0])
    (by norm_num [SourceReference.nLo,parameter,Q0])
  norm_num [SourceReference.uLo,SourceReference.uHi,SourceReference.wLo,
    SourceReference.wHi,SourceReference.fLo,SourceReference.fHi,
    SourceReference.fpLo,SourceReference.fpHi,SourceReference.nLo,
    SourceReference.nHi,parameter,Q0] at hh
  rw [show parameter=(1/2:ℝ) from rfl]
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1.1],by linarith [hh.2.1.2]⟩,
    ⟨by linarith [hh.2.2.1.1],by linarith [hh.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.1.1],by linarith [hh.2.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.2.1],by linarith [hh.2.2.2.2.2]⟩⟩

lemma middle_trig :
    Real.sin (7/5)∈Icc (98544971/10^8:ℝ) (98545074/10^8) ∧
      Real.cos (7/5)∈Icc (16996702/10^8:ℝ) (16996715/10^8) := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/5 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  exact ⟨⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩,
    ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩⟩

lemma middle_curve :
    y parameter (7/5)∈Icc (130730107/10^8:ℝ) (130730225/10^8) ∧
      u parameter (7/5)∈Icc (16860339/10^7:ℝ) (16860371/10^7) ∧
      w parameter (7/5)∈Icc (10358014/10^7:ℝ) (10358048/10^7) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter (7/5)∈Icc (8699/10000:ℝ) (87/100) ∧
      fp parameter (7/5)∈Icc (73/100:ℝ) (147/200) := by
  have hh := SourceReference.curve (domain middle_mem) parameter_nonnegative.1
    middle_trig.1 middle_trig.2
    (yl := (130730107/10^8:ℝ)) (yh := (130730225/10^8:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [parameter,Q0]) (by norm_num [parameter,Q0])
    (by norm_num [SourceReference.nLo,parameter,Q0])
  norm_num [SourceReference.uLo,SourceReference.uHi,SourceReference.wLo,
    SourceReference.wHi,SourceReference.fLo,SourceReference.fHi,
    SourceReference.fpLo,SourceReference.fpHi,SourceReference.nLo,
    SourceReference.nHi,parameter,Q0] at hh
  rw [show parameter=(1/2:ℝ) from rfl]
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1.1],by linarith [hh.2.1.2]⟩,
    ⟨by linarith [hh.2.2.1.1],by linarith [hh.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.1.1],by linarith [hh.2.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.2.1],by linarith [hh.2.2.2.2.2]⟩⟩

lemma left_target : target parameter (13/10)∈Icc 0 outerDiagonal := by
  have hw := left_curve.2.2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma middle_target : target parameter (7/5)∈Icc 0 outerDiagonal := by
  have hw := middle_curve.2.2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma left_labels : LLabel.d1 (target parameter (13/10))<659/1000 ∧
    (451/500:ℝ)<cost (13/10) := by
  have hh := left_curve
  have hb : target parameter (13/10)∈Icc (3917320/10^7:ℝ) (3917336/10^7) := by
    dsimp [target]
    constructor <;> linarith [hh.2.2.1.1,hh.2.2.1.2]
  have hu : U (target parameter (13/10))∈Icc (17664687/10^7:ℝ) (17664702/10^7) := by
    rw [target_U (domain left_mem) left_target]
    exact hh.2.1
  have hL := LReference.target left_target hb hu (by norm_num) (by norm_num)
  have hfirst := hL.2.2.2.1
  have hvalue := hL.2.1
  norm_num [LReference.firstHi,LReference.valueHi] at hfirst hvalue
  constructor
  · linarith
  · dsimp [cost,value]
    linarith [V_zero_bounds.1]

lemma middle_labels : LLabel.d1 (target parameter (7/5))<659/1000 ∧
    (161/1000:ℝ)<LLabel.d2 (target parameter (7/5)) := by
  have hh := middle_curve
  have hb : target parameter (7/5)∈Icc (5358014/10^7:ℝ) (5358048/10^7) := by
    dsimp [target]
    constructor <;> linarith [hh.2.2.1.1,hh.2.2.1.2]
  have hu : U (target parameter (7/5))∈Icc (16860339/10^7:ℝ) (16860371/10^7) := by
    rw [target_U (domain middle_mem) middle_target]
    exact hh.2.1
  have hL := LReference.target middle_target hb hu (by norm_num) (by norm_num)
  have hfirst := hL.2.2.2.1
  have hsecond := hL.2.2.2.2.1
  norm_num [LReference.firstHi,LReference.secondLo,Q0] at hfirst hsecond
  exact ⟨by linarith,by linarith⟩

lemma quarter_curvature : LLabel.d2 zeroTarget<(21/10:ℝ) := by
  have hL := LReference.target zeroTarget_mem
    ⟨zeroTarget_bounds.1.le,zeroTarget_bounds.2.le⟩
    (show U zeroTarget∈Icc (3/2) (3/2) by rw [zeroTarget_U]; exact ⟨le_rfl,le_rfl⟩)
    (by norm_num) (by norm_num)
  have hh := hL.2.2.2.2.2
  norm_num [LReference.secondHi,Q0] at hh
  linarith

lemma left_slope : 0<slope g parameter (13/10) := by
  have hh := left_curve
  have hq := SourceReference.quotient_interval hh.1 hh.2.1 (by norm_num) (by norm_num)
  dsimp only [SourceCurve.slope,quotient,g]
  norm_num at hq
  nlinarith [hq.1,left_labels.1]

lemma middle_speed : bp parameter (7/5)<(1467/1000:ℝ) := by
  have hh := middle_curve
  have hf0 : 0≤SecondWord.PositiveThree.SourceCurve.f parameter (7/5) := by linarith [hh.2.2.2.1.1]
  have hp := mul_le_mul hh.2.1.2 hh.2.2.2.1.2 hf0 (by norm_num : (0:ℝ)≤16860371/10^7)
  dsimp [bp]
  norm_num at hp
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.ZeroContact
