module

public import SquaresInCircles.Eight.Words.Second.Outer.Negative.TwoLabels
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.OppositeData

/-!
# Eight squares: the entire physical negative-angle contact domain

The final
angle is the exact double-diagonal contact, not an auxiliary search
endpoint. Its half-angle formula, bound .556, original coordinate cuts,
and the two endpoints of each target interval are proved here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open SecondWord (U W outer_domain outer_zero_mem)

abbrev diagonal_mem : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
def halfRatio : ℝ := (outerDiagonal-1/2)/(outerDiagonal+1/2)
def halfAngle : ℝ := Real.arctan halfRatio
def finalAngle : ℝ := 2*halfAngle

lemma halfRatio_bounds : (0:ℝ)<halfRatio ∧ halfRatio<143/500 := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hden : 0<outerDiagonal+1/2 := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · apply (div_lt_iff₀ hden).2
    linarith

lemma halfAngle_bounds : 0<halfAngle ∧ halfAngle<Real.pi/2 ∧ halfAngle<143/500 := by
  have hp : 0<halfAngle := Real.arctan_pos.mpr halfRatio_bounds.1
  have hu : halfAngle<Real.pi/2 := Real.arctan_lt_pi_div_two _
  have hh := Real.arctan_le_self halfRatio_bounds.1.le
  exact ⟨hp,hu,hh.trans_lt halfRatio_bounds.2⟩

lemma final_mem : finalAngle∈Icc 0 (7/10) := by
  have h := halfAngle_bounds
  dsimp [finalAngle]
  constructor <;> linarith [h.1,h.2.2]

lemma final_trig : Real.sin finalAngle=2*halfRatio/(1+halfRatio^2) ∧
    Real.cos finalAngle=(1-halfRatio^2)/(1+halfRatio^2) := by
  have hc : 0<Real.cos halfAngle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [halfAngle_bounds.1,Real.pi_pos],halfAngle_bounds.2.1⟩
  have ht : Real.sin halfAngle/Real.cos halfAngle=halfRatio := by
    rw [←Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan _
  have hs : Real.sin halfAngle=halfRatio*Real.cos halfAngle := (div_eq_iff hc.ne').1 ht
  have hunit := Real.sin_sq_add_cos_sq halfAngle
  have hden : 0<1+halfRatio^2 := by nlinarith [sq_nonneg halfRatio]
  have hcos2 : (Real.cos halfAngle)^2=1/(1+halfRatio^2) := by
    apply (eq_div_iff hden.ne').2
    rw [hs] at hunit
    nlinarith
  dsimp [finalAngle]
  rw [Real.sin_two_mul,Real.cos_two_mul]
  constructor
  · rw [hs,show 2*(halfRatio*Real.cos halfAngle)*Real.cos halfAngle=
      2*halfRatio*(Real.cos halfAngle)^2 by ring,hcos2]
    ring
  · rw [hcos2]
    field_simp
    ring

lemma double_contact : minus outerDiagonal finalAngle=outerDiagonal := by
  have ht := final_trig
  have hden : outerDiagonal+1/2≠0 := by linarith [outer_endpoint_bounds.2.2.1]
  have hroot : 1+halfRatio^2≠0 := by positivity
  have hr : halfRatio*(outerDiagonal+1/2)=outerDiagonal-1/2 := div_mul_cancel₀ _ hden
  have hinv : (1+halfRatio^2)*(1+halfRatio^2)⁻¹=1 := mul_inv_cancel₀ hroot
  dsimp [minus,SecondWord.OppositeZero.minus]
  rw [ShortOuterOne.SameContact.arc_diagonal,ht.1,ht.2]
  linear_combination (outerDiagonal-1/2)*hinv+2*(1+halfRatio^2)⁻¹*hr

lemma final_exit : outerDiagonal< minus outerDiagonal (139/250) := by
  have hs := HighOrderTaylor.S15_le_sin (show (0:ℝ)≤139/250 by norm_num)
  have hc := HighOrderTaylor.cos_le_C16 (show (0:ℝ)≤139/250 by norm_num)
  have tr := positive_trig (show (139/250:ℝ)∈Icc 0 (7/10) by norm_num)
  have hd := SecondWord.diagonal_fine
  have hp := mul_le_mul
    (show (1399214065109/1000000000000:ℝ)≤outerDiagonal+1/2 by linarith)
    hs (by norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7])
    (by linarith : 0≤outerDiagonal+1/2)
  have hn := mul_le_mul
    (show outerDiagonal-1/2≤(399214065110/1000000000000:ℝ) by linarith)
    hc (by linarith [tr.1] : 0≤Real.cos (139/250)) (by norm_num)
  dsimp [minus,SecondWord.OppositeZero.minus]
  rw [ShortOuterOne.SameContact.arc_diagonal]
  norm_num [HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,sin9,sin7,
    HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8] at hp hn
  linarith

lemma final_bound : 0<finalAngle ∧ finalAngle<(139/250:ℝ) := by
  constructor
  · dsimp [finalAngle]
    linarith [halfAngle_bounds.1]
  · by_contra! hh
    have hm := SecondWord.OppositeZero.minus_angle_monotone diagonal_mem
      (by norm_num : (139/250:ℝ)∈Icc 0 (7/10)) final_mem hh
    rw [show SecondWord.OppositeZero.minus outerDiagonal finalAngle=outerDiagonal
      from double_contact] at hm
    exact (not_lt_of_ge hm) final_exit

lemma diagonal_speed_lower {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (7/10:ℝ)< minusSpeed outerDiagonal x := by
  have tr := positive_trig hx
  have h1 := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [ShortMixedZero.fine_diagonal_bounds.1])
    tr.1.le (by norm_num) (by linarith [outer_endpoint_bounds.2.2.1])
  have h2 := mul_nonneg
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1]) tr.2.2.1
  norm_num [minusSpeed,SecondWord.OppositeZero.minusSpeed,ShortOuterOne.SameContact.arc_diagonal]
  linarith

lemma diagonal_increase {x y : ℝ} (hx : x∈Icc 0 (7/10)) (hy : y∈Icc 0 (7/10))
    (hxy : x≤y) : (7/10)*(y-x)≤ minus outerDiagonal y-minus outerDiagonal x := by
  have hm : MonotoneOn (fun u => minus outerDiagonal u-(7/10)*u) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun u _ => ((SecondWord.OppositeZero.minus_hasDerivAt outerDiagonal u).sub
        ((hasDerivAt_id u).const_mul (7/10))).continuousAt.continuousWithinAt)
      (fun u _ => (SecondWord.OppositeZero.minus_hasDerivAt outerDiagonal u).sub
        ((hasDerivAt_id u).const_mul (7/10)))
      (fun u hu => by linarith [diagonal_speed_lower (Ioo_subset_Icc_self hu)])
  have hh := hm hx hy hxy
  linarith

lemma original_angle {B x : ℝ} (hd : MinusDomain B x) : x≤finalAngle := by
  have ht := SecondWord.OppositeZero.minus_target_antitone hd.2.1 hd.1 diagonal_mem hd.1.2
  have hxbound : minus outerDiagonal x≤outerDiagonal := ht.trans hd.2.2.2
  by_contra! hx
  have hm := diagonal_increase final_mem hd.2.1 hx.le
  rw [double_contact] at hm
  linarith

lemma band_coordinates {B x : ℝ} (hd : MinusDomain B x) :
    B∈Icc low outerDiagonal ∧ minus B x∈Icc low outerDiagonal := by
  have hh := SecondWord.OppositeZero.minus_aligned_le hd.1 hd.2.1
  refine ⟨⟨?_,hd.1.2⟩,⟨?_,hd.2.2.2⟩⟩ <;>
    dsimp [low] <;> linarith [hd.1.2,hd.2.2.2]

lemma target_interval {B x C : ℝ} (hd : MinusDomain B x)
    (hC : C∈Icc B outerDiagonal) : MinusDomain C x := by
  have hCi : C∈Icc 0 outerDiagonal := ⟨hd.1.1.trans hC.1,hC.2⟩
  have hl := SecondWord.OppositeZero.minus_aligned_le hCi hd.2.1
  have hu := SecondWord.OppositeZero.minus_target_antitone hd.2.1 hd.1 hCi hC.1
  exact ⟨hCi,hd.2.1,⟨by linarith [hC.2,outer_endpoint_bounds.2.2.2],hu.trans hd.2.2.2⟩⟩

lemma entry {B x : ℝ} (hd : MinusDomain B x) :
    ∃a, a∈Icc 0 B ∧ minus a x=outerDiagonal ∧
      ∀C∈Icc a outerDiagonal, MinusDomain C x := by
  have hzero : outerDiagonal < minus 0 x := by
    have hh := SecondWord.OppositeZero.minus_aligned_le outer_zero_mem hd.2.1
    linarith [outer_endpoint_bounds.2.2.2]
  have hc : Continuous (fun C => minus C x) := by
    dsimp [minus,SecondWord.OppositeZero.minus,arc]; fun_prop
  obtain ⟨a,ha,he⟩ := intermediate_value_Icc hd.1.1 hc.neg.continuousOn
    (show -outerDiagonal∈Icc (-minus 0 x) (-minus B x) from
      ⟨by linarith,by linarith [hd.2.2.2]⟩)
  have heq : minus a x=outerDiagonal := by
    simp only [Pi.neg_apply] at he
    linarith
  have had : MinusDomain a x :=
    ⟨⟨ha.1,ha.2.trans hd.1.2⟩,hd.2.1,by
      rw [show SecondWord.OppositeZero.minus a x=outerDiagonal from heq]; exact diagonal_mem⟩
  exact ⟨a,ha,heq,fun C hC => target_interval had hC⟩

lemma double_value (r : Row) :
    (131/125:ℝ)< -finalAngle+c r+(p r+q r+v r+t r)*outerDiagonal := by
  have hf := final_bound.2
  have hd := ShortMixedZero.fine_diagonal_bounds
  fin_cases r <;> norm_num [c,p,q,v,t] <;> linarith

end SquaresInCircles.Eight.ShortOuterZero.Opposite.Negative
