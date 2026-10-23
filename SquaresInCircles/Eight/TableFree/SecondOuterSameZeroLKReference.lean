module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroLKShape
public import SquaresInCircles.Eight.TableFree.SecondOuterGeneralReference

/-!
# The single target-zero reference for the L/K row

Uncompiled source draft.  The displayed rational angle determines its
actual source coordinate and circle radical.  Taylor bounds and exact
circle squares prove the reference value and slope; no independently
chosen contact coordinate is substituted for the original one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.LK
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def reference : ℝ := 15781/100000
def bLo : ℝ := 4250280203/5000000000
def bHi : ℝ := 1700112083/2000000000
def vLo : ℝ := 4908944453/5000000000
def vHi : ℝ := 9817888921/10000000000
def uLo : ℝ := 14467026939/10000000000
def uHi : ℝ := 14467026949/10000000000

lemma reference_trig :
    (314311597/2000000000:ℝ)<Real.sin reference ∧
      Real.sin reference<1571557991/10000000000 ∧
      (395029529/400000000:ℝ)<Real.cos reference ∧
      Real.cos reference<4937869113/5000000000 := by
  have hs := sin_lower_seven (x := reference) (by norm_num [reference])
  have hu := sin_upper_five (x := reference) (by norm_num [reference])
  have hc := cos_lower_six (x := reference) (by norm_num [reference])
  have hk := cos_le_cos8 (x := reference) (by norm_num [reference])
  norm_num [reference,cos8] at hs hu hc hk
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_coordinates : b 0 reference∈Icc bLo bHi ∧ v 0 reference∈Icc vLo vHi := by
  have ht := reference_trig
  have ha := ShortOuterZero.fine_axial_bounds
  have has0 : 0≤outerAxial-1/2 := by linarith [ha.1]
  have hslo := mul_le_mul
    (show (914575671/1000000000:ℝ)≤outerAxial-1/2 by linarith [ha.1]) ht.1.le
    (by norm_num : (0:ℝ)≤314311597/2000000000) has0
  have hshi := mul_le_mul
    (show outerAxial-1/2≤(114321959/125000000:ℝ) by linarith [ha.2]) ht.2.1.le
    (show 0≤Real.sin reference by linarith [ht.1]) (by norm_num : (0:ℝ)≤114321959/125000000)
  have hclo := mul_le_mul
    (show (914575671/1000000000:ℝ)≤outerAxial-1/2 by linarith [ha.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤395029529/400000000) has0
  have hchi := mul_le_mul
    (show outerAxial-1/2≤(114321959/125000000:ℝ) by linarith [ha.2]) ht.2.2.2.le
    (show 0≤Real.cos reference by linarith [ht.2.2.1]) (by norm_num : (0:ℝ)≤114321959/125000000)
  norm_num [b,v,ShortOuterOne.SameContact.arc_zero,bLo,bHi,vLo,vHi]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith

lemma reference_domain : Domain 0 reference ∧ (151/200:ℝ)<b 0 reference := by
  have hb := reference_coordinates.1
  refine ⟨⟨outer_zero_mem,by norm_num [reference],⟨?_,?_⟩⟩,?_⟩
  · norm_num [bLo] at hb
    linarith
  · norm_num [bHi] at hb
    linarith [fine_outer_endpoint_bounds.2]
  · norm_num [bLo] at hb
    linarith

lemma reference_radical : U (b 0 reference)∈Icc uLo uHi := by
  have hb := reference_coordinates.1
  have hc := UW_circle (outer_domain reference_domain.1.2.2)
  have hu := U_positive (outer_domain reference_domain.1.2.2)
  have hb2lo := pow_le_pow_left₀ (by norm_num [bLo] : (0:ℝ)≤bLo+1/2)
    (show bLo+1/2≤b 0 reference+1/2 by linarith) 2
  have hb2hi := pow_le_pow_left₀ (show 0≤b 0 reference+1/2 by
    linarith [reference_domain.1.2.2.1])
    (show b 0 reference+1/2≤bHi+1/2 by linarith) 2
  norm_num [bLo,bHi,uLo,uHi,Q0,W] at hb2lo hb2hi hc ⊢
  constructor <;> nlinarith

theorem reference_value :
    (8977797/10000000:ℝ)<value LLabel KLabel 0 reference ∧
      |angleFirst LLabel 0 reference|<(3/1000000:ℝ) := by
  have hh := GeneralReference.label LLabel reference_domain.1.2.2
    reference_coordinates.1 reference_radical
    (by norm_num [bLo] : (0:ℝ)≤bLo) (by norm_num [uLo] : (1/2:ℝ)<uLo)
  have hp := mul_le_mul hh.2.2.1 reference_coordinates.2.1
    (by norm_num [vLo] : (0:ℝ)≤vLo)
    (show 0≤LLabel.d1 (b 0 reference) by
      linarith [(L_first_bounds reference_domain.1.2.2).1])
  have hq := mul_le_mul hh.2.2.2.1 reference_coordinates.2.2
    (v_positive outer_zero_mem reference_domain.1.2.1).le
    (by norm_num [GeneralReference.firstHi,GeneralReference.hi,GeneralReference.rlo,
      GeneralReference.rhi,LLabel,bLo,bHi,uLo,uHi])
  have hK := K_zero
  have ha := ShortOuterZero.fine_axial_bounds
  dsimp [K] at hK
  norm_num [GeneralReference.valueLo,GeneralReference.valueHi,
    GeneralReference.firstLo,GeneralReference.firstHi,
    GeneralReference.secondLo,GeneralReference.secondHi,GeneralReference.lo,
    GeneralReference.hi,GeneralReference.rlo,GeneralReference.rhi,
    GeneralReference.dlo,GeneralReference.dhi,LLabel,bLo,bHi,uLo,uHi,vLo,vHi,Q0] at hh hp hq
  constructor
  · dsimp [value,reference]
    linarith [hh.1,ha.1]
  · rw [abs_lt]
    dsimp [angleFirst]
    constructor <;> linarith

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.LK
