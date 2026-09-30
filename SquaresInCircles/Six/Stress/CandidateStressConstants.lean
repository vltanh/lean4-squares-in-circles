import SquaresInCircles.Six.Stress.CandidateRadius

/-!
# Exact candidate self-stress constants

These are the outer multipliers used by every candidate-graph stress in the
audited hand proof. Their signs and basic ranges are consequences of the
candidate algebra, not numerical assumptions.
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

lemma rStar_mul_den :
    rStar*(Six.sStar+3/2)=Six.sStar+1/2 := by
  rw [rStar, div_mul_cancel₀]
  exact ne_of_gt rStar_den_pos

lemma kStar_mul_den :
    kStar*(3/2-Six.sStar)=Six.tStar+1/2 := by
  rw [kStar, div_mul_cancel₀]
  exact ne_of_gt kStar_den_pos

lemma mStar_mul_den :
    mStar*(3/2-Six.sStar)=(1+rStar)*(Six.tStar+1/2) := by
  dsimp [mStar]
  rw [mul_assoc,kStar_mul_den]

/-- The candidate cap radius equals the diagonal center's primary coordinate:
rho_* = sqrt(2) d_* = 2 h_* d_*. -/
lemma rhoStar_eq_two_h_d : rhoStar=2*Six.hStar*Six.dStar := by
  have hx : (2*Six.hStar*Six.dStar)^2+
      (2*Six.hStar*Six.dStar)+1/2=Six.qStar := by
    nlinarith [Six.hStar_sq,Six.diagonal_radius_identity]
  have hsum : 0 < rhoStar+2*Six.hStar*Six.dStar+1 := by
    positivity
  nlinarith [rhoStar_identity,hx]

lemma dStar_gt_hStar : Six.hStar < Six.dStar := by
  dsimp [Six.dStar]
  linarith [Six.tStar_bounds.2]

lemma diagonal_self_factor_pos :
    0 < 2*mStar*(Six.dStar-Six.hStar) := by
  positivity

end SquaresInCircles.Six.Stress
