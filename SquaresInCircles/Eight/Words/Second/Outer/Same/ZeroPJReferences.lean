module

public import SquaresInCircles.Eight.Words.Second.Outer.GeneralReference
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoLabels
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJData
public import SquaresInCircles.Eight.Words.Second.Outer.SourceReference

/-!
# Eight squares: exact endpoints for the whole P/J critical interval

Only the two physical interval endpoints and
one rational target coordinate occur here.  Their radical brackets are
proved by squares, and the literal labels retain their exact rational
coefficients.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma six_mem : (3/5:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)

lemma six_reference :
    (876298/1000000:ℝ)<p (3/5) ∧ p (3/5)<876299/1000000 ∧
      (253479/1000000:ℝ)<PLabel.d2 (3/5) ∧
      PLabel.d2 (3/5)<6337/25000 ∧ PLabel.d3 (3/5)<91/250 := by
  have hu := shifted_chart_reference (outer_domain six_mem)
    (l := (411217703899/250000000000:ℝ))
    (u := (1644870815597/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  rcases GeneralReference.label PLabel six_mem ⟨le_rfl,le_rfl⟩
    ⟨hu.1.le,hu.2.le⟩ (by norm_num) (by norm_num) with
    ⟨_,_,hpl,hpu,hdl,hdu⟩
  have hthird := SourceReference.source_third_upper six_mem
    (by norm_num : (0:ℝ)<411217703899/250000000000) hu.1.le
    (by norm_num : (0:ℝ)<91/250) (by norm_num [Q0])
  have e1 : (876298/1000000:ℝ)<GeneralReference.firstLo PLabel (3/5) (3/5)
      (411217703899/250000000000) (1644870815597/1000000000000) := by
    norm_num [GeneralReference.firstLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,PLabel]
  have e2 : GeneralReference.firstHi PLabel (3/5) (3/5)
      (411217703899/250000000000) (1644870815597/1000000000000)<(876299/1000000:ℝ) := by
    norm_num [GeneralReference.firstHi,GeneralReference.hi,GeneralReference.rlo,
      GeneralReference.rhi,PLabel]
  have e3 : (253479/1000000:ℝ)<GeneralReference.secondLo PLabel (3/5) (3/5)
      (411217703899/250000000000) (1644870815597/1000000000000) := by
    norm_num [GeneralReference.secondLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,GeneralReference.dlo,GeneralReference.dhi,PLabel,Q0]
  have e4 : GeneralReference.secondHi PLabel (3/5) (3/5)
      (411217703899/250000000000) (1644870815597/1000000000000)<(6337/25000:ℝ) := by
    norm_num [GeneralReference.secondHi,GeneralReference.hi,GeneralReference.rlo,
      GeneralReference.rhi,GeneralReference.dlo,GeneralReference.dhi,PLabel,Q0]
  dsimp only [p]
  exact ⟨by linarith,by linarith,by linarith,by linarith,hthird⟩

lemma diagonal_reference :
    (972646/1000000:ℝ)<p outerDiagonal ∧ p outerDiagonal<972647/1000000 ∧
      (8209/20000:ℝ)<PLabel.d2 outerDiagonal ∧ PLabel.d3 outerDiagonal<779/1000 := by
  have hd : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hb := diagonal_fine
  have hu : U outerDiagonal∈Icc
      (139921406510940/100000000000000:ℝ) (139921406510941/100000000000000) := by
    rw [U,ShortOuterOne.SameContact.arc_diagonal]
    constructor <;> linarith [hb.1,hb.2]
  rcases GeneralReference.label PLabel hd ⟨hb.1.le,hb.2.le⟩ hu
    (by norm_num) (by norm_num) with ⟨_,_,hpl,hpu,hdl,_⟩
  have hthird := SourceReference.source_third_upper hd
    (by norm_num : (0:ℝ)<139921406510940/100000000000000) hu.1
    (by norm_num : (0:ℝ)<779/1000) (by
      norm_num [Q0]
      linarith [hb.1])
  have e1 : (972646/1000000:ℝ)<GeneralReference.firstLo PLabel
      (89921406510940/100000000000000) (89921406510941/100000000000000)
      (139921406510940/100000000000000) (139921406510941/100000000000000) := by
    norm_num [GeneralReference.firstLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,PLabel]
  have e2 : GeneralReference.firstHi PLabel
      (89921406510940/100000000000000) (89921406510941/100000000000000)
      (139921406510940/100000000000000) (139921406510941/100000000000000)<
        (972647/1000000:ℝ) := by
    norm_num [GeneralReference.firstHi,GeneralReference.hi,GeneralReference.rlo,
      GeneralReference.rhi,PLabel]
  have e3 : (8209/20000:ℝ)<GeneralReference.secondLo PLabel
      (89921406510940/100000000000000) (89921406510941/100000000000000)
      (139921406510940/100000000000000) (139921406510941/100000000000000) := by
    norm_num [GeneralReference.secondLo,GeneralReference.lo,GeneralReference.rlo,
      GeneralReference.rhi,GeneralReference.dlo,GeneralReference.dhi,PLabel,Q0]
  dsimp only [p]
  exact ⟨by linarith,by linarith,by linarith,hthird⟩

lemma E_endpoints : (43/1000:ℝ)<E outerDiagonal ∧ E (3/5)<187/1000 := by
  have hp := diagonal_reference
  have hp3 := pow_le_pow_left₀ (p_positive
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)).le hp.2.1.le 3
  have hz : outerDiagonal-1/2<(79843/200000:ℝ) := by linarith [diagonal_fine.2]
  have hprod := mul_le_mul hz.le hp3 (pow_nonneg (p_positive
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨outer_zero_mem.2,le_rfl⟩)).le 3)
    (by norm_num : (0:ℝ)≤79843/200000)
  have hs := six_reference
  have hs3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤876298/1000000) hs.1.le 3
  dsimp [E]
  constructor <;> nlinarith

lemma criticalU_endpoints :
    (1801/1000:ℝ)<criticalU (3/5) ∧ criticalU (3/5)<18017/10000 ∧
      criticalU outerDiagonal<37/20 := by
  have hs := six_reference
  have hps := p_positive six_mem
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤876298/1000000) hs.1.le 2
  have hhi := pow_le_pow_left₀ hps.le hs.2.1.le 2
  have hrlo : (1:ℝ)/(p (3/5))^2<1303/1000 := by
    apply (div_lt_iff₀ (pow_pos hps 2)).2
    linarith
  have hrhi : (6511/5000:ℝ)<1/(p (3/5))^2 := by
    apply (lt_div_iff₀ (pow_pos hps 2)).2
    linarith
  have hp := diagonal_reference
  have hpd := p_positive (show outerDiagonal∈Icc 0 outerDiagonal from
    ⟨outer_zero_mem.2,le_rfl⟩)
  have hdp := pow_le_pow_left₀ hpd.le hp.2.1.le 2
  have hrec : (1057/1000:ℝ)<1/(p outerDiagonal)^2 := by
    apply (lt_div_iff₀ (pow_pos hpd 2)).2
    linarith
  have hz : (399/1000:ℝ)<outerDiagonal-1/2 := by
    linarith [fine_outer_endpoint_bounds.2]
  have hz2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤399/1000) hz.le 2
  have hQ : Q0=9789/2500 := rfl
  dsimp only [criticalU]
  exact ⟨by linarith,by linarith,by linarith⟩

lemma J_eight_twentyfifths_second : -(109/250:ℝ)<JLabel.d2 (8/25) := by
  have hm : (8/25:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hu := shifted_chart_reference (outer_domain hm)
    (l := (18008/10000:ℝ)) (u := (1801/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := JLabel.second_chart_reference (outer_domain hm)
    (l := (18008/10000:ℝ)) (u := (1801/1000:ℝ))
    (dlo := (-(109/250):ℝ)) (dhi := (0:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
    (by norm_num [JLabel,W,Q0]) (by norm_num [JLabel,W,Q0])
  exact hh.1

end SquaresInCircles.Eight.SecondWord.SameZero.PJ
