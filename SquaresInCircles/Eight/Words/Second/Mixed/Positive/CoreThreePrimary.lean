module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.CoreThreeTransverse
public import SquaresInCircles.Eight.Words.Second.Mixed.Primary.SupportShort
public import SquaresInCircles.Eight.Words.Second.Mixed.TSmallEnvelope

/-!
# Eight squares: the entire late primary support and aligned relaxation

The primary support is strictly concave on the whole short angle arc,
so its two exact endpoint bounds suffice. The aligned relaxed cost is
bounded for every original outer point, including primary coordinates
below one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open MixedPrimarySupport

def p : ℝ := 31/50
def k : ℝ := 1109/10000
def K : ℝ := Real.pi/2-c-k+(g+p)/2-γ

lemma K_bounds : (1296701326/1000000000:ℝ)<K ∧ K<(1296701327/1000000000:ℝ) := by
  dsimp [K,c,k,g,p,γ]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma radius_fine : CommonQuarter.radius<(494697/250000:ℝ) := by
  have hh := radius_sq
  norm_num [Q0] at hh
  nlinarith [radius_bounds.1]

lemma primary_zero : 0< minus g p K 0 := by
  have he := N_sq (g := g) (p := p) (x := (0:ℝ)) (by norm_num [g])
  have hp := N_positive (g := g) (p := p) (x := (0:ℝ)) (by norm_num [g])
  simp only [minus,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero,sub_zero]
  generalize N g p 0 = n at he hp ⊢
  norm_num [g,p] at he ⊢
  have hN : n<(566501/500000:ℝ) := by nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_fine (by norm_num : (0:ℝ)<566501/500000))
  linarith [K_bounds.1]

lemma primary_right : 0< minus g p K (171/1000) := by
  have ht := PointProducts.trig (show (0:ℝ)≤171/1000 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,ReferenceTrig.cos12,cos10,cos8] at ht
  have hs : (170167/1000000:ℝ)<Real.sin (171/1000) := by linarith [ht.1.1]
  have hc : (492707/500000:ℝ)<Real.cos (171/1000) := by linarith [ht.2.1]
  have hcu : Real.cos (171/1000)<(123177/125000:ℝ) := by linarith [ht.2.2]
  have he := N_sq (g := g) (p := p) (x := (171/1000:ℝ)) (by norm_num [g])
  have hp := N_positive (g := g) (p := p) (x := (171/1000:ℝ)) (by norm_num [g])
  have hcos2 : (Real.cos (171/1000))^2<(123177/125000:ℝ)^2 := by nlinarith
  have hKC := mul_le_mul
    (show (1296701326/1000000000:ℝ)-171/1000≤K-171/1000 by linarith [K_bounds.1]) hc.le
    (by norm_num : (0:ℝ)≤492707/500000) (by linarith [K_bounds.1] : 0≤K-171/1000)
  simp only [minus]
  generalize N g p (171/1000) = n at he hp ⊢
  have hN : n<(14101/12500:ℝ) := by
    norm_num [g,p] at he
    nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
    (mul_lt_mul_of_pos_right radius_fine (by norm_num : (0:ℝ)<14101/12500))
  have hsp := mul_le_mul_of_nonneg_left hs.le (show 0≤g*(13/12) by norm_num [g])
  norm_num [g] at hsp ⊢
  linarith

lemma primary_curvature {x : ℝ} (hx : x∈Icc (0:ℝ) (171/1000)) : minusDD g p K x<0 := by
  have ht := positive_trig (show x∈Icc (0:ℝ) (7/10) from ⟨hx.1,by linarith [hx.2]⟩)
  have hs : Real.sin x≤(171/1000:ℝ) := ht.2.2.2.2.1.trans hx.2
  have hs2 := pow_le_pow_left₀ ht.2.2.1 hs 2
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hc : (1-(171/1000:ℝ)^2/2)≤Real.cos x := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hKC := mul_le_mul
    (show (12967/10000:ℝ)-171/1000≤K-x by linarith [K_bounds.1,hx.2]) hc
    (by norm_num : (0:ℝ)≤1-(171/1000:ℝ)^2/2) (by linarith [K_bounds.1,hx.2] : 0≤K-x)
  have hn := negative_curvature_upper (g := g) (p := p) (x := x) (by norm_num [g])
  have hnorm : -NDD g p x≤p^2/g+p^4*(171/1000)^2/g^3 := by
    norm_num [g,p] at hn ⊢
    nlinarith
  have hpaid := (mul_le_mul_of_nonneg_left hnorm (by linarith [radius_bounds.1] : 0≤CommonQuarter.radius)).trans_lt
    (mul_lt_mul_of_pos_right radius_fine (by norm_num [g,p] : 0<p^2/g+p^4*(171/1000)^2/g^3))
  have hsp := mul_le_mul_of_nonneg_left hs (show 0≤2-13*g/12 by norm_num [g])
  dsimp [minusDD,g,p] at *
  nlinarith

theorem primary_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (171/1000)) : 0< minus g p K x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (171/1000)) (minus g p K) :=
    concave_of_deriv2 (fun _ _ => minus_hasDerivAt (by norm_num [g]))
      (fun _ _ => minusD_hasDerivAt (by norm_num [g]))
      (fun _ hx => (primary_curvature hx).le)
  exact concave_gt_of_endpoints hc hx primary_zero primary_right

lemma aligned_initial {b : ℝ} (hb : b∈Icc (0:ℝ) (7/10)) : (9/10:ℝ)<aligned b := by
  have hs := ShortOuterOne.SameContact.arc_state
    (show b∈Icc 0 outerDiagonal from ⟨hb.1,hb.2.trans MixedTSmall.seven_mem.2⟩)
  have hT := MixedTSmall.upper hb
  dsimp [MixedTSmall.k,MixedTEnvelope.k,MixedTSmall.q] at hT
  have hc := outer_circle_lower (X := -g) (Y := -(31/50)) hs
  have he : Real.sqrt ((-g)^2+(-(31/50:ℝ))^2)=MixedTransverseSupport.lowerN g (31/50) (Real.pi/2) := by
    simp [MixedTransverseSupport.lowerN,CircularNorm.norm,CircularNorm.energy]
  rw [he] at hc
  have hh := late_aligned
  simp only [late,MixedTransverseSupport.lower,Real.sin_pi_div_two,mul_one] at hh
  dsimp [aligned]
  linarith

theorem aligned_lower {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : (9/10:ℝ)<aligned b := by
  by_cases he : b≤7/10
  · exact aligned_initial ⟨hb.1,he⟩
  · have hm := aligned_monotone
      (show (7/10:ℝ)∈Icc (7/10:ℝ) outerDiagonal from ⟨le_rfl,MixedTSmall.seven_mem.2⟩)
      (show b∈Icc (7/10:ℝ) outerDiagonal from ⟨by linarith,hb.2⟩) (by linarith)
    exact (aligned_initial (show (7/10:ℝ)∈Icc (0:ℝ) (7/10) by norm_num)).trans_le hm

end SquaresInCircles.Eight.SecondWord.MixedThree.PositiveCore
