module

public import SquaresInCircles.Eight.Words.Second.Outer.FixedReference
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoDiagonalSource
public import SquaresInCircles.Eight.Words.Second.Outer.ReferenceTrig

/-!
# Eight squares: two fixed references on the original diagonal-source contact

All reference enclosures are consequences of rational Taylor polynomials
and the same physical circle equation.  The points `2/5` and `1/2` supply
the slope, curvature and tangent-value reserves for the complete arc.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.DiagonalSource

open CommonQuarter CorePairGeometry Arithmetic ReferenceTrig

def dLo : ℝ := 89921406510940/100000000000000
def dHi : ℝ := 89921406510941/100000000000000

lemma point_cage {x sl sh cl ch : ℝ}
    (hs : Real.sin x∈Icc sl sh) (hc : Real.cos x∈Icc cl ch)
    (hsl : 0≤ sl) (hcl : 0≤cl) :
    1/2-(dHi-1/2)*ch+(dLo+1/2)*sl≤height x ∧
      height x≤1/2-(dLo-1/2)*cl+(dHi+1/2)*sh ∧
      (dLo-1/2)*sl+(dLo+1/2)*cl≤ speed x ∧
      speed x≤(dHi-1/2)*sh+(dHi+1/2)*ch := by
  have hd : dLo≤outerDiagonal ∧ outerDiagonal≤dHi :=
    ⟨diagonal_fine.1.le,diagonal_fine.2.le⟩
  have hslow : 0≤Real.sin x := hsl.trans hs.1
  have hclow : 0≤Real.cos x := hcl.trans hc.1
  have hsm := mul_le_mul (show dLo-1/2≤outerDiagonal-1/2 by linarith) hs.1 hsl
    (by linarith [hd.1,show (1/2:ℝ)<dLo by norm_num [dLo]])
  have hsM := mul_le_mul (show outerDiagonal-1/2≤dHi-1/2 by linarith) hs.2 hslow
    (by norm_num [dHi])
  have hsp := mul_le_mul (show dLo+1/2≤outerDiagonal+1/2 by linarith) hs.1 hsl
    (by linarith [hd.1,show (0:ℝ)<dLo by norm_num [dLo]])
  have hsP := mul_le_mul (show outerDiagonal+1/2≤dHi+1/2 by linarith) hs.2 hslow
    (by norm_num [dHi])
  have hcm := mul_le_mul (show dLo-1/2≤outerDiagonal-1/2 by linarith) hc.1 hcl
    (by linarith [hd.1,show (1/2:ℝ)<dLo by norm_num [dLo]])
  have hcM := mul_le_mul (show outerDiagonal-1/2≤dHi-1/2 by linarith) hc.2 hclow
    (by norm_num [dHi])
  have hcp := mul_le_mul (show dLo+1/2≤outerDiagonal+1/2 by linarith) hc.1 hcl
    (by linarith [hd.1,show (0:ℝ)<dLo by norm_num [dLo]])
  have hcP := mul_le_mul (show outerDiagonal+1/2≤dHi+1/2 by linarith) hc.2 hclow
    (by norm_num [dHi])
  dsimp [height,speed,TargetContact.B,TargetContact.v]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

lemma four_trig :
    Real.sin (2/5:ℝ)∈Icc (97354585577/250000000000) (38941834231/100000000000) ∧
      Real.cos (2/5:ℝ)∈Icc (460530497001/500000000000) (921060994003/1000000000000) := by
  have hs := sin11_le_sin (show (0:ℝ)≤2/5 by norm_num)
  have hS := sin_le_sin9 (show (0:ℝ)≤2/5 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤2/5 by norm_num)
  have hC := cos_le_cos12 (show (0:ℝ)≤2/5 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hS hc hC
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma five_trig :
    Real.sin (1/2:ℝ)∈Icc (119856384651/250000000000) (479425538617/1000000000000) ∧
      Real.cos (1/2:ℝ)∈Icc (877582561889/1000000000000) (877582561891/1000000000000) := by
  have hs := sin11_le_sin (show (0:ℝ)≤1/2 by norm_num)
  have hS := sin_le_sin9 (show (0:ℝ)≤1/2 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤1/2 by norm_num)
  have hC := cos_le_cos12 (show (0:ℝ)≤1/2 by norm_num)
  norm_num [sin11,sin9,sin7,cos12,cos10,cos8] at hs hS hc hC
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma four_cage :
    height (2/5)∈Icc (6771791/10000000) (846474/1250000) ∧
      speed (2/5)∈Icc (14442227/10000000) (14442229/10000000) := by
  have hh := point_cage four_trig.1 four_trig.2 (by norm_num) (by norm_num)
  norm_num [dLo,dHi] at hh
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma five_cage :
    height (1/2)∈Icc (2051189/2500000) (8204757/10000000) ∧
      speed (1/2)∈Icc (1774149/1250000) (7096597/5000000) := by
  have hh := point_cage five_trig.1 five_trig.2 (by norm_num) (by norm_num)
  norm_num [dLo,dHi] at hh
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma four_domain : Domain (2/5) :=
  ⟨by norm_num,by linarith [four_cage.1.2,fine_outer_endpoint_bounds.2]⟩

lemma five_domain : Domain (1/2) :=
  ⟨by norm_num,by linarith [five_cage.1.2,fine_outer_endpoint_bounds.2]⟩

lemma four_radical : U (height (2/5))∈Icc (15905499/10000000) (15905501/10000000) := by
  have hc := UW_circle (outer_domain (domain_data four_domain).1)
  have hp := U_positive (outer_domain (domain_data four_domain).1)
  dsimp [W] at hc
  norm_num [Q0] at hc
  constructor <;> nlinarith [four_cage.1.1,four_cage.1.2]

lemma five_radical : U (height (1/2))∈Icc (3684379/2500000) (7368759/5000000) := by
  have hc := UW_circle (outer_domain (domain_data five_domain).1)
  have hp := U_positive (outer_domain (domain_data five_domain).1)
  dsimp [W] at hc
  norm_num [Q0] at hc
  constructor <;> nlinarith [five_cage.1.1,five_cage.1.2]

lemma four_label :
    (6621/12500:ℝ)<T (height (2/5)) ∧
      (7703/12500:ℝ)<TLabel.d1 (height (2/5)) ∧
      TLabel.d1 (height (2/5))<30813/50000 ∧
      (10689/50000:ℝ)<TLabel.d2 (height (2/5)) := by
  have hh := FixedReference.target (domain_data four_domain).1 four_cage.1 four_radical
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hh
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma five_label : (12443/20000:ℝ)<T (height (1/2)) ∧
    (68923/100000:ℝ)<TLabel.d1 (height (1/2)) ∧
      TLabel.d1 (height (1/2))<17231/25000 := by
  have hh := FixedReference.target (domain_data five_domain).1 five_cage.1 five_radical
    (by norm_num) (by norm_num)
  norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
    FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at hh
  exact ⟨by linarith,by linarith,by linarith⟩

lemma four_value : (1819/2000:ℝ)<cost (2/5) := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,P_diagonal_fine,four_label.1]

lemma four_first : first (2/5)<0 := by
  have hh := mul_le_mul four_label.2.2.1.le four_cage.2.2
    (domain_data four_domain).2.1.le (by norm_num : (0:ℝ)≤30813/50000)
  dsimp [first]
  norm_num at hh
  linarith

lemma four_second : (3/10:ℝ)<second (2/5) := by
  have hspeed : (14442227/10000000:ℝ)^2≤(speed (2/5))^2 :=
    pow_le_pow_left₀ (by norm_num) four_cage.2.1 2
  have hpositive := mul_le_mul four_label.2.2.2.le hspeed
    (by positivity) (by linarith [four_label.2.2.2] : 0≤TLabel.d2 (height (2/5)))
  have hnegative := mul_le_mul four_label.2.2.1.le
    (show height (2/5)-1/2≤846474/1250000-1/2 by linarith [four_cage.1.2])
    (by linarith [four_cage.1.1] : 0≤height (2/5)-1/2)
    (by norm_num : (0:ℝ)≤30813/50000)
  dsimp [second]
  norm_num at hpositive hnegative
  linarith

lemma five_value : (22551/25000:ℝ)<cost (1/2) := by
  dsimp [cost,value]
  linarith [pi_hand_enclosure.1,P_diagonal_fine,five_label.1]

lemma five_first : |first (1/2)|<(11/500:ℝ) := by
  have hlo := mul_le_mul five_label.2.1.le five_cage.2.1
    (by norm_num : (0:ℝ)≤1774149/1250000)
    (by linarith [five_label.2.1] : 0≤TLabel.d1 (height (1/2)))
  have hhi := mul_le_mul five_label.2.2.le five_cage.2.2
    (domain_data five_domain).2.1.le (by norm_num : (0:ℝ)≤17231/25000)
  rw [abs_lt]
  dsimp [first]
  norm_num at hlo hhi
  constructor <;> linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo.DiagonalSource
