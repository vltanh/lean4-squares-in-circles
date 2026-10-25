module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeData

/-!
# Named scalar references for the opposite mixed zero rows

Uncompiled source draft.  Every radical enclosure below follows from
two rational square comparisons at one named coordinate.  The values
and slopes are direct substitutions in the literal role polynomials.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.References
open CommonQuarter CorePairGeometry Arithmetic GeneralReference

lemma six_mem : (3/5:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
lemma minimum_mem : (1027/1250:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)

lemma L_six : (47/50:ℝ)<aligned 2 (3/5) ∧ alignedD 2 (3/5)<0 ∧
    (1/2:ℝ)<LLabel.d2 (3/5) := by
  have hr := shifted_chart_reference (outer_domain six_mem)
    (l := (164487081559616/100000000000000:ℝ))
    (u := (164487081559617/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label LLabel six_mem ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,LLabel,Q0] at hh
  norm_num [aligned,alignedD,c,g,F,LLabel]
  exact ⟨by linarith [hh.1],by linarith [hh.2.2.2.1],by linarith [hh.2.2.2.2.1]⟩

lemma L_minimum : (9010079/10000000:ℝ)<aligned 2 (1027/1250) ∧
    |alignedD 2 (1027/1250)|<(1/10000:ℝ) := by
  have hr := shifted_chart_reference (outer_domain minimum_mem)
    (l := (147274350787908/100000000000000:ℝ))
    (u := (147274350787909/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label LLabel minimum_mem ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,LLabel,Q0] at hh
  norm_num [aligned,alignedD,c,g,F,LLabel]
  exact ⟨by linarith [hh.1],abs_lt.mpr ⟨by linarith [hh.2.2.1],by linarith [hh.2.2.2.1]⟩⟩

lemma L_late : g 2<LLabel.d1 (21/25) := by
  have hb : (21/25:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (145602197785610/100000000000000:ℝ))
    (u := (145602197785611/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label LLabel hb ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,LLabel,Q0,g] at hh ⊢
  linarith [hh.2.2.1]

lemma J_small_slope : 1<JLabel.d1 (3/20) := by
  have hb : (3/20:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (186898368104165/100000000000000:ℝ))
    (u := (186898368104166/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label JLabel hb ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,JLabel,Q0] at hh ⊢
  linarith [hh.2.2.1]

lemma P_target : (463/500:ℝ)<aligned 1 (87/200) := by
  have hb : (87/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (174395384113227/100000000000000:ℝ))
    (u := (174395384113228/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label PLabel hb ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,PLabel,Q0] at hh
  norm_num [aligned,c,g,F,PLabel]
  linarith [hh.1]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.References
