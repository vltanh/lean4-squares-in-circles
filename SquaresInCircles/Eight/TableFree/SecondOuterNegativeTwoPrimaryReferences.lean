module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeTwoPrimaryDiagonal
public import SquaresInCircles.Eight.TableFree.SecondOuterReferenceTrig

/-!
# Three fixed references on the lower primary diagonal

The rational angles `.3`, `.4`, and `.556` give the transition bounds
for the physical curve.  Their enclosures follow from the exact
diagonal, adjacent Taylor polynomials, and circle square comparisons.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.PrimaryDiagonal

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig

lemma trig_reference {x sl sh cl ch : ℝ} (hx : 0≤x)
    (hsl : sl≤sin11 x) (hsh : sin9 x≤sh)
    (hcl : cl≤cos10 x) (hch : cos12 x≤ch) :
    Real.sin x∈Icc sl sh ∧ Real.cos x∈Icc cl ch :=
  ⟨⟨hsl.trans (sin11_le_sin hx),(sin_le_sin9 hx).trans hsh⟩,
    ⟨hcl.trans (cos10_le_cos hx),(cos_le_cos12 hx).trans hch⟩⟩

lemma three_trig :
    Real.sin (3/10:ℝ)∈Icc (295520206/1000000000) (295520207/1000000000) ∧
      Real.cos (3/10:ℝ)∈Icc (955336489/1000000000) (955336490/1000000000) :=
  trig_reference (by norm_num)
    (by norm_num [sin11,sin9,sin7]) (by norm_num [sin9,sin7])
    (by norm_num [cos10,cos8]) (by norm_num [cos12,cos10,cos8])

lemma four_trig :
    Real.sin (2/5:ℝ)∈Icc (389418342/1000000000) (389418343/1000000000) ∧
      Real.cos (2/5:ℝ)∈Icc (921060994/1000000000) (921060995/1000000000) :=
  trig_reference (by norm_num)
    (by norm_num [sin11,sin9,sin7]) (by norm_num [sin9,sin7])
    (by norm_num [cos10,cos8]) (by norm_num [cos12,cos10,cos8])

lemma end_trig :
    Real.sin (139/250:ℝ)∈Icc (527792937/1000000000) (527792938/1000000000) ∧
      Real.cos (139/250:ℝ)∈Icc (849373072/1000000000) (849373073/1000000000) :=
  trig_reference (by norm_num)
    (by norm_num [sin11,sin9,sin7]) (by norm_num [sin9,sin7])
    (by norm_num [cos10,cos8]) (by norm_num [cos12,cos10,cos8])

lemma three_Z : Z (3/10)∈Icc (556122423/1000000000) (556122426/1000000000) := by
  dsimp [Z,offset]
  exact ⟨by linarith [three_trig.2.1,diagonal_fine.2],
    by linarith [three_trig.2.2,diagonal_fine.1]⟩

lemma four_Z : Z (2/5)∈Icc (521846928/1000000000) (521846930/1000000000) := by
  dsimp [Z,offset]
  exact ⟨by linarith [four_trig.2.1,diagonal_fine.2],
    by linarith [four_trig.2.2,diagonal_fine.1]⟩

lemma end_Z : Z (139/250)∈Icc (450159006/1000000000) (450159008/1000000000) := by
  dsimp [Z,offset]
  exact ⟨by linarith [end_trig.2.1,diagonal_fine.2],
    by linarith [end_trig.2.2,diagonal_fine.1]⟩

lemma three_Y : Y (3/10)∈Icc (1899033397/1000000000) (1899033400/1000000000) := by
  have hh := radical_data (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hc := hh.2.2.2.2
  norm_num [Q0] at hc
  constructor <;> nlinarith [hh.2.2.1,three_Z.1,three_Z.2]

lemma four_Y : Y (2/5)∈Icc (1908736697/1000000000) (1908736700/1000000000) := by
  have hh := radical_data (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num)
  have hc := hh.2.2.2.2
  norm_num [Q0] at hc
  constructor <;> nlinarith [hh.2.2.1,four_Z.1,four_Z.2]

lemma end_Y : Y (139/250)∈Icc (1926903439/1000000000) (1926903443/1000000000) := by
  have hh := radical_data (show (139/250:ℝ)∈Icc 0 (7/10) by norm_num)
  have hc := hh.2.2.2.2
  norm_num [Q0] at hc
  constructor <;> nlinarith [hh.2.2.1,end_Z.1,end_Z.2]

lemma coordinate_cage {x sl sh cl ch zl zh yl yh : ℝ}
    (hx : x∈Icc 0 (7/10)) (hs : Real.sin x∈Icc sl sh)
    (hc : Real.cos x∈Icc cl ch) (hz : Z x∈Icc zl zh) (hy : Y x∈Icc yl yh)
    (hsl : 0≤sl) (hcl : 0≤cl) (hzl : 0≤zl) (hyl : 0<yl) :
    yl*cl-zh*sh≤horizontal x ∧ horizontal x≤yh*ch-zl*sl ∧
      yl*sl+zl*cl≤vertical x ∧ vertical x≤yh*sh+zh*ch ∧
      1-sh/yl≤factor x ∧ factor x≤1-sl/yh := by
  have hh := radical_data hx
  have ht := positive_trig hx
  have hyp : 0<Y x := by linarith [hh.2.2.1]
  have hyhp : 0<yh := hyp.trans_le hy.2
  have hYcL := mul_le_mul hy.1 hc.1 hcl hyp.le
  have hYcH := mul_le_mul hy.2 hc.2 (by linarith [ht.1]) hyhp.le
  have hZsL := mul_le_mul hz.1 hs.1 hsl hh.1.le
  have hZsH := mul_le_mul hz.2 hs.2 ht.2.2.1 (hh.1.le.trans hz.2)
  have hYsL := mul_le_mul hy.1 hs.1 hsl hyp.le
  have hYsH := mul_le_mul hy.2 hs.2 ht.2.2.1 hyhp.le
  have hZcL := mul_le_mul hz.1 hc.1 hcl hh.1.le
  have hZcH := mul_le_mul hz.2 hc.2 (by linarith [ht.1]) (hh.1.le.trans hz.2)
  have hdivL : sl/yh≤Real.sin x/Y x := by
    apply (le_div_iff₀ hyp).2
    have hm := mul_le_mul_of_nonneg_left hy.2 (div_nonneg hsl hyhp.le)
    have he : (sl/yh)*yh=sl := by field_simp [hyhp.ne']
    rw [he] at hm
    linarith [hs.1]
  have hdivH : Real.sin x/Y x≤sh/yl := by
    apply (div_le_iff₀ hyp).2
    have hm := mul_le_mul_of_nonneg_left hy.1
      (div_nonneg (ht.2.2.1.trans hs.2) hyl.le)
    have he : (sh/yl)*yl=sh := by field_simp [hyl.ne']
    rw [he] at hm
    linarith [hs.2]
  dsimp [horizontal,vertical,factor]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma three_reference : height (3/10)<3/5 ∧ (273/250:ℝ)<vertical (3/10) ∧
    speed (3/10)<697/500 := by
  have hh := coordinate_cage (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num)
    three_trig.1 three_trig.2 three_Z three_Y
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hu : horizontal (3/10)<1649871/1000000 := by norm_num at hh; linarith
  have hf : factor (3/10)<105548/125000 := by norm_num at hh; linarith
  have hp := factor_bounds (show (3/10:ℝ)∈Icc 0 (7/10) by norm_num)
  have hprod := mul_lt_mul hu hf (by linarith [hp.1] : 0<factor (3/10))
    (by norm_num : (0:ℝ)≤1649871/1000000)
  norm_num at hh hprod
  dsimp [height,speed]
  exact ⟨by linarith,by linarith,by linarith⟩

lemma four_reference :
    (3/5:ℝ)<height (2/5) ∧ height (2/5)<181/250 ∧
      (777/500:ℝ)<horizontal (2/5) ∧ (159/200:ℝ)<factor (2/5) ∧
      speed (2/5)<619/500 := by
  have hh := coordinate_cage (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num)
    four_trig.1 four_trig.2 four_Z four_Y
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hu : horizontal (2/5)<1554847/1000000 := by norm_num at hh; linarith
  have hf : factor (2/5)<397991/500000 := by norm_num at hh; linarith
  have hp := factor_bounds (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num)
  have hprod := mul_lt_mul hu hf (by linarith [hp.1] : 0<factor (2/5))
    (by norm_num : (0:ℝ)≤1554847/1000000)
  norm_num at hh hprod
  dsimp [height,speed]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma end_reference : outerDiagonal<height (139/250) := by
  have hh := coordinate_cage (show (139/250:ℝ)∈Icc 0 (7/10) by norm_num)
    end_trig.1 end_trig.2 end_Z end_Y
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh
  dsimp [height]
  linarith [diagonal_fine.2]

lemma four_domain : Domain (2/5) :=
  ⟨by norm_num,by linarith [four_reference.2.1,fine_outer_endpoint_bounds.2]⟩

lemma mid_factorD {x : ℝ} (hx : x∈Icc 0 (2/5)) : factorD x< -2/5 := by
  have hxfull : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have hy := radical_data hxfull
  have ht := positive_trig hxfull
  have hc := cos_anti hxfull (show (2/5:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have hcos : (23/25:ℝ)<Real.cos x := by linarith [four_trig.2.1]
  have hnum := factorD_numerator hxfull
  have hk := offset_bounds
  have hcoef : (6889/2500:ℝ)<Q0-1-offset^2 := by norm_num [Q0]; nlinarith
  have hfirst := mul_lt_mul hcoef hcos (by norm_num : (0:ℝ)<23/25)
    (by linarith [hcoef] : 0≤Q0-1-offset^2)
  have hsq := pow_lt_pow_left₀ (by norm_num : (0:ℝ)≤23/25) hcos (by norm_num : (2:ℕ)≠0)
  have hsecond := mul_lt_mul
    (show (399/1000:ℝ)< -offset by linarith [hk.2])
    (show (1+(23/25)^2:ℝ)<1+(Real.cos x)^2 by linarith)
    (by norm_num : (0:ℝ)<1+(23/25)^2) (by linarith [hk.2] : 0≤ -offset)
  have hycube := pow_lt_pow_left₀ (show 0≤Y x by linarith [hy.2.2.1]) hy.2.2.2.1
    (by norm_num : (3:ℕ)≠0)
  have hycube0 := pow_pos (show 0<Y x by linarith [hy.2.2.1]) 3
  norm_num at hfirst hsecond hycube
  nlinarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeTwo.PrimaryDiagonal
