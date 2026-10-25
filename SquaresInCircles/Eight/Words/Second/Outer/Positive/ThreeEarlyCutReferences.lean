module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeEarlyMinorant
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeSourceReference
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeSourceSlope

/-!
# Eight squares: the two actual endpoints of the source `0.35` contact

The first endpoint is the original lower angle `pi/2-0.7`; its
trigonometric references are therefore those of `0.7`.  The other
endpoint is `1.3`.  All coordinate cages below follow by squaring the
same circle radical.  Both original contact derivatives are positive.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut

open CommonQuarter CorePairGeometry Arithmetic SourceCurve

def parameter : ℝ := 3/20
def Domain (φ : ℝ) : Prop := φ∈Icc lowerAngle (13/10)

lemma parameter_mem : parameter∈Icc (-2/5:ℝ) (1/2) := by norm_num [parameter]
lemma parameter_nonnegative : parameter∈Icc (0:ℝ) (1/2) := by norm_num [parameter]
lemma domain {φ : ℝ} (hφ : Domain φ) : SourceCurve.Domain parameter φ :=
  ⟨parameter_mem,Early.early_lower hφ⟩
lemma left_mem : Domain lowerAngle := ⟨le_rfl,Early.end_mem.1⟩
lemma right_mem : Domain (13/10) := Early.end_mem

lemma left_trig :
    Real.sin lowerAngle∈Icc (76484218/10^8:ℝ) (76484219/10^8) ∧
      Real.cos lowerAngle∈Icc (64421768/10^8:ℝ) (64421769/10^8) := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  simp only [lowerAngle,Real.sin_sub,Real.cos_sub,Real.sin_pi_div_two,
    Real.cos_pi_div_two,one_mul,zero_mul,sub_zero,zero_add]
  exact ⟨⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩,
    ⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩⟩

lemma right_trig :
    Real.sin (13/10)∈Icc (96355818/10^8:ℝ) (96355863/10^8) ∧
      Real.cos (13/10)∈Icc (26749878/10^8:ℝ) (26749883/10^8) := by
  have ht := PointProducts.trig (show (0:ℝ)≤13/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  exact ⟨⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩,
    ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩⟩

lemma left_curve :
    y parameter lowerAngle∈Icc (175461213/10^8:ℝ) (175461215/10^8) ∧
      u parameter lowerAngle∈Icc (18300620/10^7:ℝ) (18300622/10^7) ∧
      w parameter lowerAngle∈Icc (7526438/10^7:ℝ) (7526440/10^7) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter lowerAngle∈Icc (6328/10000:ℝ) (6329/10000) ∧
      fp parameter lowerAngle∈Icc (3656/10000:ℝ) (3657/10000) := by
  have hh := SourceReference.curve (domain left_mem) parameter_nonnegative.1
    left_trig.1 left_trig.2
    (yl := (175461213/10^8:ℝ)) (yh := (175461215/10^8:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [parameter,Q0]) (by norm_num [parameter,Q0])
    (by norm_num [SourceReference.nLo,parameter,Q0])
  norm_num [SourceReference.uLo,SourceReference.uHi,SourceReference.wLo,
    SourceReference.wHi,SourceReference.fLo,SourceReference.fHi,
    SourceReference.fpLo,SourceReference.fpHi,SourceReference.nLo,
    SourceReference.nHi,parameter,Q0] at hh
  rw [show parameter=(3/20:ℝ) from rfl]
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1.1],by linarith [hh.2.1.2]⟩,
    ⟨by linarith [hh.2.2.1.1],by linarith [hh.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.1.1],by linarith [hh.2.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.2.1],by linarith [hh.2.2.2.2.2]⟩⟩

lemma right_curve :
    y parameter (13/10)∈Icc (163572221/10^8:ℝ) (163572253/10^8) ∧
      u parameter (13/10)∈Icc (15105317/10^7:ℝ) (15105330/10^7) ∧
      w parameter (13/10)∈Icc (12782378/10^7:ℝ) (12782392/10^7) ∧
      SecondWord.PositiveThree.SourceCurve.f parameter (13/10)∈Icc (8364/10000:ℝ) (8365/10000) ∧
      fp parameter (13/10)∈Icc (5708/10000:ℝ) (5709/10000) := by
  have hh := SourceReference.curve (domain right_mem) parameter_nonnegative.1
    right_trig.1 right_trig.2
    (yl := (163572221/10^8:ℝ)) (yh := (163572253/10^8:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [parameter,Q0]) (by norm_num [parameter,Q0])
    (by norm_num [SourceReference.nLo,parameter,Q0])
  norm_num [SourceReference.uLo,SourceReference.uHi,SourceReference.wLo,
    SourceReference.wHi,SourceReference.fLo,SourceReference.fHi,
    SourceReference.fpLo,SourceReference.fpHi,SourceReference.nLo,
    SourceReference.nHi,parameter,Q0] at hh
  rw [show parameter=(3/20:ℝ) from rfl]
  exact ⟨⟨by linarith [hh.1.1],by linarith [hh.1.2]⟩,
    ⟨by linarith [hh.2.1.1],by linarith [hh.2.1.2]⟩,
    ⟨by linarith [hh.2.2.1.1],by linarith [hh.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.1.1],by linarith [hh.2.2.2.1.2]⟩,
    ⟨by linarith [hh.2.2.2.2.1],by linarith [hh.2.2.2.2.2]⟩⟩

lemma left_target : target parameter lowerAngle∈Icc 0 outerDiagonal := by
  have hw := left_curve.2.2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma right_target : target parameter (13/10)∈Icc 0 outerDiagonal := by
  have hw := right_curve.2.2.1
  dsimp [target]
  constructor <;> linarith [hw.1,hw.2,fine_outer_endpoint_bounds.2]

lemma source_first : (219/250:ℝ)<VLabel.d1 (7/20) ∧ VLabel.d1 (7/20)<877/1000 := by
  apply VLabel.first_chart_reference (outer_domain V_short_mem)
    (l := (17869247326/10^10:ℝ)) (u := (17869247327/10^10:ℝ)) <;>
    norm_num [VLabel,Q0,W]

lemma left_slope : 0<slope (VLabel.d1 (7/20)) parameter lowerAngle := by
  have hh := left_curve
  have hB : target parameter lowerAngle∈Icc (2526438/10^7:ℝ) (2526440/10^7) := by
    dsimp [target]
    constructor <;> linarith [hh.2.2.1.1,hh.2.2.1.2]
  have hU : U (target parameter lowerAngle)∈Icc
      (18300620/10^7:ℝ) (18300622/10^7) := by
    rw [target_U (domain left_mem) left_target]
    exact hh.2.1
  have hL := LReference.target left_target hB hU (by norm_num) (by norm_num)
  have hq := SourceReference.quotient_interval hh.1 hh.2.1 (by norm_num) (by norm_num)
  have hprod := mul_le_mul source_first.1.le hq.1
    (by norm_num : (0:ℝ)≤(175461213/10^8)/(18300622/10^7))
    (by linarith [source_first.1] : 0≤VLabel.d1 (7/20))
  have hLhi := hL.2.2.2.1
  norm_num [LReference.firstHi,Q0] at hLhi hprod
  dsimp only [SourceCurve.slope,quotient]
  linarith

lemma right_slope : 0<slope (VLabel.d1 (7/20)) parameter (13/10) := by
  have hh := right_curve
  have hB : target parameter (13/10)∈Icc (7782378/10^7:ℝ) (7782392/10^7) := by
    dsimp [target]
    constructor <;> linarith [hh.2.2.1.1,hh.2.2.1.2]
  have hU : U (target parameter (13/10))∈Icc
      (15105317/10^7:ℝ) (15105330/10^7) := by
    rw [target_U (domain right_mem) right_target]
    exact hh.2.1
  have hL := LReference.target right_target hB hU (by norm_num) (by norm_num)
  have hq := SourceReference.quotient_interval hh.1 hh.2.1 (by norm_num) (by norm_num)
  have hprod := mul_le_mul source_first.1.le hq.1
    (by norm_num : (0:ℝ)≤(163572221/10^8)/(15105330/10^7))
    (by linarith [source_first.1] : 0≤VLabel.d1 (7/20))
  have hLhi := hL.2.2.2.1
  norm_num [LReference.firstHi,Q0] at hLhi hprod
  dsimp only [SourceCurve.slope,quotient]
  linarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.EarlyCut
