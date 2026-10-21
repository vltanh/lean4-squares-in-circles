module

public import SquaresInCircles.Eight.TableFree.SecondMixedPositiveCoreTwoData

/-!
# Two complete lower-half supports for the positive core target

The restricted transverse chord gives a strictly concave circle
support.  The restricted primary chord gives one square completion
on the entire half.  The constants are proved from single radicals
and the actual angle endpoints.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveCore
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower)

def q : ℝ := 1617/2000
def p : ℝ := 8281/10000
def K : ℝ := Real.pi/2-c+(g+p)/2-γ
def transverse (φ : ℝ) : ℝ := MixedTransverseSupport.lower g q (-c) φ

lemma transverse_left : (91/100:ℝ)<transverse lowerAngle := by
  have ht := MixedAffine.left_trig
  have hn := MixedTransverseSupport.lower_sq (g := g) (p := q)
    (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) lowerAngle
  have hp : 0<MixedTransverseSupport.lowerN g q lowerAngle :=
    CircularNorm.norm_pos (MixedTransverseSupport.lower_domain
      (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) lowerAngle)
  have hN : MixedTransverseSupport.lowerN g q lowerAngle<(41/50:ℝ) := by
    norm_num [g,q] at hn
    nlinarith [ht.2.2.1]
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<41/50))
  dsimp [transverse,MixedTransverseSupport.lower,g,q,c,lowerAngle]
  linarith [ht.1,pi_hand_enclosure.1]

lemma transverse_right : (91/100:ℝ)<transverse (Real.pi/2) := by
  have hn := MixedTransverseSupport.lower_sq (g := g) (p := q)
    (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) (Real.pi/2)
  have hp : 0<MixedTransverseSupport.lowerN g q (Real.pi/2) :=
    CircularNorm.norm_pos (MixedTransverseSupport.lower_domain
      (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) (Real.pi/2))
  have hN : MixedTransverseSupport.lowerN g q (Real.pi/2)<(33/25:ℝ) := by
    norm_num [g,q] at hn
    nlinarith
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<33/25))
  norm_num [transverse,MixedTransverseSupport.lower,g,q,c]
  linarith [pi_hand_enclosure.1]

theorem transverse_lower {φ : ℝ} (hφ : Lower φ) : (91/100:ℝ)<transverse φ :=
  concave_gt_of_endpoints (MixedTransverseSupport.lower_concave
    (by norm_num [g]) (by norm_num [q]) (by norm_num [g,q]) (-c))
    hφ transverse_left transverse_right

lemma K_bounds : (799/500:ℝ)<K ∧ K<(1599/1000:ℝ) := by
  dsimp [K,c,g,p,γ]
  constructor <;> linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]

lemma primary_norm_zero :
    (1331/1000:ℝ)<MixedPrimarySupport.N g p 0 ∧
      MixedPrimarySupport.N g p 0<(333/250:ℝ) := by
  have hh := MixedPrimarySupport.N_sq (p := p) (x := 0)
    (show 0<g by norm_num [g])
  have hp := MixedPrimarySupport.N_positive (p := p) (x := 0)
    (show 0<g by norm_num [g])
  norm_num [g,p] at hh
  constructor <;> nlinarith

lemma primary_gain :
    (509/1000:ℝ)<MixedPrimarySupport.gain g p ∧ MixedPrimarySupport.gain g p<(51/100:ℝ) := by
  have hp := MixedPrimarySupport.N_positive (p := p) (x := 0)
    (show 0<g by norm_num [g])
  constructor
  · apply (lt_div_iff₀ (by positivity : 0<2*MixedPrimarySupport.N g p 0)).2
    have hR := radius_bounds.1
    have hN := primary_norm_zero.2
    norm_num [g,p] at *
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0<2*MixedPrimarySupport.N g p 0)).2
    have hR := radius_bounds.2
    have hN := primary_norm_zero.1
    norm_num [g,p] at *
    nlinarith

lemma primary_zero : 0<MixedPrimarySupport.minus g p K 0 := by
  have hRN := (mul_lt_mul_of_pos_left primary_norm_zero.2
    (by linarith [radius_bounds.1] : 0<radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<333/250))
  rw [MixedPrimarySupport.minus_zero]
  norm_num [g]
  linarith [K_bounds.1]

theorem primary_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) :
    0<MixedPrimarySupport.minus g p K x := by
  apply MixedPrimarySupport.minus_positive
    (α := 129/1000) (β := 291/1000) (ε := 111/500)
    (by norm_num [g]) (by linarith [K_bounds.1])
  · linarith [K_bounds.2,primary_gain.1]
  · norm_num [g]
  · norm_num [g]
  · exact primary_zero
  · norm_num [MixedPrimarySupport.linearCoefficient,g]
  · dsimp [MixedPrimarySupport.quadraticCoefficient]
    linarith [K_bounds.2,primary_gain.1]
  · dsimp [MixedPrimarySupport.cubicCoefficient]
    norm_num [g]
    linarith [K_bounds.1,K_bounds.2,primary_gain.2]
  · norm_num
  · norm_num
  · exact hx

end SquaresInCircles.Eight.TableFree.SecondWord.MixedTwo.PositiveCore
