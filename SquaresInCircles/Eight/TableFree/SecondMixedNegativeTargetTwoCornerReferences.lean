module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeTargetTwoCornerCurvature

/-!
# Exact endpoint references for the whole corner

There are two interior-minimum references and one late diagonal
reference. Their trigonometric and core-diagonal cages are fixed
rational inequalities; the polynomial evaluations are exact.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Corner
open CommonQuarter CorePairGeometry Arithmetic

abbrev dc := CoreAngleEndpoint.diagonal

lemma diagonal_label : (28058641/50000000:ℝ)<MixedThree.negativeCore dc dc := by
  have hh := CoreAngleEndpoint.diagonal_bounds
  have hp := pow_le_pow_left₀ (by linarith [hh.1] : 0≤dc) hh.2.le 2
  dsimp [MixedThree.negativeCore]
  nlinarith [hh.1,hh.2]

private lemma diagonal_cage {φ sl su cl cu : ℝ} (hsl : 0≤ sl) (hcl : 0≤cl)
    (hs : sl≤Real.sin φ ∧ Real.sin φ≤ su) (hc : cl≤Real.cos φ ∧ Real.cos φ≤cu) :
    1+(26473139/25000000)*cl-(5892557/100000000)*su≤u dc φ ∧
    u dc φ≤1+(105892557/100000000)*cu-(1473139/25000000)*sl ∧
    (26473139/25000000)*sl+(1473139/25000000)*cl≤ speed dc φ ∧
    speed dc φ≤(105892557/100000000)*su+(5892557/100000000)*cu := by
  have hd := CoreAngleEndpoint.diagonal_bounds
  have hdp : 0≤dc+1/2 := by linarith [hd.1]
  have hdm : 0≤dc-1/2 := by linarith [hd.1]
  have hcpL := mul_le_mul (show (26473139/25000000:ℝ)≤dc+1/2 by linarith [hd.1]) hc.1 hcl hdp
  have hcpU := mul_le_mul (show dc+1/2≤(105892557/100000000:ℝ) by linarith [hd.2]) hc.2
    (hcl.trans hc.1) (by norm_num : (0:ℝ)≤105892557/100000000)
  have hsmL := mul_le_mul (show (1473139/25000000:ℝ)≤dc-1/2 by linarith [hd.1]) hs.1 hsl hdm
  have hsmU := mul_le_mul (show dc-1/2≤(5892557/100000000:ℝ) by linarith [hd.2]) hs.2
    (hsl.trans hs.1) (by norm_num : (0:ℝ)≤5892557/100000000)
  have hspL := mul_le_mul (show (26473139/25000000:ℝ)≤dc+1/2 by linarith [hd.1]) hs.1 hsl hdp
  have hspU := mul_le_mul (show dc+1/2≤(105892557/100000000:ℝ) by linarith [hd.2]) hs.2
    (hsl.trans hs.1) (by norm_num : (0:ℝ)≤105892557/100000000)
  have hcmL := mul_le_mul (show (1473139/25000000:ℝ)≤dc-1/2 by linarith [hd.1]) hc.1 hcl hdm
  have hcmU := mul_le_mul (show dc-1/2≤(5892557/100000000:ℝ) by linarith [hd.2]) hc.2
    (hcl.trans hc.1) (by norm_num : (0:ℝ)≤5892557/100000000)
  simp only [u,speed,MixedCorner.diagonal]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma diagonal_reference_trig :
    (43346261/50000000:ℝ)<Real.sin (1049/1000) ∧ Real.sin (1049/1000)<86692523/100000000 ∧
    (24921911/50000000:ℝ)<Real.cos (1049/1000) ∧ Real.cos (1049/1000)<49843823/100000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (1049/1000:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (1049/1000:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1049/1000:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (1049/1000:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma join_reference_trig :
    (9168031/10000000:ℝ)<Real.sin (29/25) ∧ Real.sin (29/25)<11460039/12500000 ∧
    (4991744/12500000:ℝ)<Real.cos (29/25) ∧ Real.cos (29/25)<19966977/50000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (29/25:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (29/25:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (29/25:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (29/25:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma late_reference_trig :
    (11140092/12500000:ℝ)<Real.sin (11/10) ∧ Real.sin (11/10)<89120737/100000000 ∧
    (11339903/25000000:ℝ)<Real.cos (11/10) ∧ Real.cos (11/10)<45359613/100000000 := by
  have hs := HighOrderTaylor.S15_le_sin (x := (11/10:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (11/10:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (11/10:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (11/10:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S11,HighOrderTaylor.S13,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma diagonal_reference_coordinates :
    (147672490/100000000:ℝ)≤u dc (1049/1000) ∧ u dc (1049/1000)≤147672494/100000000 ∧
    (94738001/100000000:ℝ)≤ speed dc (1049/1000) ∧ speed dc (1049/1000)≤47369003/50000000 := by
  have hh := diagonal_cage (by norm_num) (by norm_num)
    ⟨diagonal_reference_trig.1.le,diagonal_reference_trig.2.1.le⟩
    ⟨diagonal_reference_trig.2.2.1.le,diagonal_reference_trig.2.2.2.le⟩
  norm_num at hh
  exact ⟨by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2.1],by linarith [hh.2.2.2]⟩

lemma join_reference_coordinates :
    (143261781/100000000:ℝ)≤u (1/2) (29/25) ∧ u (1/2) (29/25)≤17907723/12500000 ∧
    (19864067/20000000:ℝ)≤ speed (1/2) (29/25) ∧ speed (1/2) (29/25)≤99320339/100000000 := by
  simp only [u,speed,MixedCorner.join]
  exact ⟨by linarith [join_reference_trig.2.2.1],by linarith [join_reference_trig.2.2.2],
    by linarith [join_reference_trig.1],by linarith [join_reference_trig.2.1]⟩

lemma late_reference_coordinates :
    (2855619/2000000:ℝ)≤u dc (11/10) ∧ u dc (11/10)≤7139049/5000000 ∧
    (1940901/2000000:ℝ)≤ speed dc (11/10) ∧ speed dc (11/10)≤9704509/10000000 := by
  have hh := diagonal_cage (by norm_num) (by norm_num)
    ⟨late_reference_trig.1.le,late_reference_trig.2.1.le⟩
    ⟨late_reference_trig.2.2.1.le,late_reference_trig.2.2.2.le⟩
  norm_num at hh
  exact ⟨by linarith [hh.1],by linarith [hh.2.1],by linarith [hh.2.2.1],by linarith [hh.2.2.2]⟩

private lemma reference_transfer {B φ ul uu vl vu : ℝ}
    (hu : ul≤u B φ ∧ u B φ≤uu) (hv : vl≤ speed B φ ∧ speed B φ≤vu)
    (hl : ul∈PHeightBounds.heights) (hh : uu∈PHeightBounds.heights) (hvl : 0≤vl) :
    PHeightTaylor.poly ul≤PHeightTaylor.poly (u B φ) ∧
    PHeightTaylor.d1 ul*vl≤PHeightTaylor.d1 (u B φ)*speed B φ ∧
    PHeightTaylor.d1 (u B φ)*speed B φ≤PHeightTaylor.d1 uu*vu := by
  have hud : u B φ∈PHeightBounds.heights := ⟨hl.1.trans hu.1,hu.2.trans hh.2⟩
  have hdl := PHeightTaylor.d1_monotone hl hud hu.1
  have hdu := PHeightTaylor.d1_monotone hud hh hu.2
  exact ⟨PHeightTaylor.poly_monotone hl hud hu.1,
    mul_le_mul hdl hv.1 hvl (PHeightTaylor.d1_positive hud).le,
    mul_le_mul hdu hv.2 (hvl.trans hv.1) (PHeightTaylor.d1_positive hh).le⟩

lemma diagonal_reference : (11222/12500:ℝ)<f dc (1049/1000) ∧
    |fAngle dc (1049/1000)|<(1/1000:ℝ) := by
  have hc := diagonal_reference_coordinates
  have hh := reference_transfer ⟨hc.1,hc.2.1⟩ ⟨hc.2.2.1,hc.2.2.2⟩
    (by norm_num [PHeightBounds.heights]) (by norm_num [PHeightBounds.heights]) (by norm_num)
  norm_num [PHeightTaylor.poly,PHeightTaylor.d1,PHeightTaylor.c0,PHeightTaylor.c1,
    PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r] at hh
  constructor
  · dsimp [f,PHeightTaylor.poly,PHeightTaylor.c0,PHeightTaylor.c1,
      PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    rw [MixedCorner.diagonal]
    linarith [diagonal_label]
  · rw [abs_lt]
    dsimp [fAngle,PHeightTaylor.d1,PHeightTaylor.c1,PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    constructor <;> linarith [hh.2.1,hh.2.2]

lemma join_reference : (45011/50000:ℝ)<f (1/2) (29/25) ∧
    |fAngle (1/2) (29/25)|<(1/2500:ℝ) := by
  have hc := join_reference_coordinates
  have hh := reference_transfer ⟨hc.1,hc.2.1⟩ ⟨hc.2.2.1,hc.2.2.2⟩
    (by norm_num [PHeightBounds.heights]) (by norm_num [PHeightBounds.heights]) (by norm_num)
  norm_num [PHeightTaylor.poly,PHeightTaylor.d1,PHeightTaylor.c0,PHeightTaylor.c1,
    PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r] at hh
  constructor
  · simp only [f,MixedCorner.join]
    norm_num [MixedThree.negativeCore]
    dsimp [PHeightTaylor.poly,PHeightTaylor.c0,PHeightTaylor.c1,
      PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    linarith [hh.1]
  · rw [abs_lt]
    dsimp [fAngle,PHeightTaylor.d1,PHeightTaylor.c1,PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    constructor <;> linarith [hh.2.1,hh.2.2]

lemma late_reference : (89849/100000:ℝ)<f dc (11/10) ∧ 0<fAngle dc (11/10) := by
  have hc := late_reference_coordinates
  have hh := reference_transfer ⟨hc.1,hc.2.1⟩ ⟨hc.2.2.1,hc.2.2.2⟩
    (by norm_num [PHeightBounds.heights]) (by norm_num [PHeightBounds.heights]) (by norm_num)
  norm_num [PHeightTaylor.poly,PHeightTaylor.d1,PHeightTaylor.c0,PHeightTaylor.c1,
    PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r] at hh
  constructor
  · dsimp [f,PHeightTaylor.poly,PHeightTaylor.c0,PHeightTaylor.c1,
      PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    rw [MixedCorner.diagonal]
    linarith [diagonal_label]
  · dsimp [fAngle,PHeightTaylor.d1,PHeightTaylor.c1,PHeightTaylor.c2,PHeightTaylor.c3,PHeightTaylor.r]
    linarith [hh.2.2]

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.NegativeTarget.Corner
