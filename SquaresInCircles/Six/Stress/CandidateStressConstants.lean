module
public import SquaresInCircles.Six.Stress.CandidateRadiusConstants

@[expose] public section

/-!
# Exact candidate self-stress constants

These are the outer multipliers used by every candidate-graph stress. Their
signs and basic identities are consequences of candidate algebra alone.
The constant dependency chain no longer imports packing normalization.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress

def rStar : ℝ := (Six.sStar+1/2)/(Six.sStar+3/2)
def kStar : ℝ := (Six.tStar+1/2)/(3/2-Six.sStar)
def mStar : ℝ := (1+rStar)*kStar

lemma rStar_den_pos : 0 < Six.sStar+3/2 := by linarith [Six.sStar_pos]
lemma kStar_den_pos : 0 < 3/2-Six.sStar := by linarith [Six.sStar_lt_fifth]

lemma rStar_pos : 0 < rStar := by
  exact div_pos (by linarith [Six.sStar_pos]) rStar_den_pos

lemma rStar_gt_third : 1/3 < rStar := by
  rw [rStar, lt_div_iff₀ rStar_den_pos]
  nlinarith [Six.sStar_pos]

lemma rStar_lt_half : rStar < 1/2 := by
  rw [rStar, div_lt_iff₀ rStar_den_pos]
  linarith [Six.sStar_lt_fifth]

lemma kStar_pos : 0 < kStar := by
  exact div_pos (by linarith [Six.tStar_bounds.1]) kStar_den_pos

lemma mStar_pos : 0 < mStar := by
  exact mul_pos (by linarith [rStar_pos]) kStar_pos

lemma one_add_rStar_pos : 0 < 1+rStar := by linarith [rStar_pos]

lemma rStar_mul_den : rStar*(Six.sStar+3/2)=Six.sStar+1/2 := by
  rw [rStar, div_mul_cancel₀]
  exact ne_of_gt rStar_den_pos

lemma kStar_mul_den : kStar*(3/2-Six.sStar)=Six.tStar+1/2 := by
  rw [kStar, div_mul_cancel₀]
  exact ne_of_gt kStar_den_pos

lemma mStar_mul_den : mStar*(3/2-Six.sStar)=(1+rStar)*(Six.tStar+1/2) := by
  dsimp [mStar]
  rw [mul_assoc,kStar_mul_den]

lemma rhoStar_eq_two_h_d : rhoStar=2*Six.hStar*Six.dStar := by
  have hx : (2*Six.hStar*Six.dStar)^2+
      (2*Six.hStar*Six.dStar)+1/2=Six.qStar := by
    have hh := congrArg (fun z : ℝ => 4*Six.dStar^2*z) Six.hStar_sq
    nlinarith [hh,Six.diagonal_radius_identity]
  have hsum : 0 < rhoStar+2*Six.hStar*Six.dStar+1 := by
    have hp := mul_pos (mul_pos (by norm_num : (0:ℝ)<2) Six.hStar_pos) Six.dStar_pos
    linarith [rhoStar_gt_11_10]
  have hfactor : (rhoStar-2*Six.hStar*Six.dStar)*
      (rhoStar+2*Six.hStar*Six.dStar+1)=0 := by
    nlinarith [rhoStar_identity,hx]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hsum))

lemma dStar_gt_hStar : Six.hStar < Six.dStar := by
  dsimp [Six.dStar]
  linarith [Six.tStar_bounds.2]

lemma diagonal_self_factor_pos : 0 < 2*mStar*(Six.dStar-Six.hStar) := by
  exact mul_pos (mul_pos (by norm_num) mStar_pos) (sub_pos.mpr dStar_gt_hStar)

end SquaresInCircles.Six.Stress
