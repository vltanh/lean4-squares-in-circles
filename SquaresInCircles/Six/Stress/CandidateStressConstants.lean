import SquaresInCircles.Six.Stress.CandidateRadiusConstants

/-!
# The weights of the stress of the model

The weights `rStar = (sStar + 1/2)/(sStar + 3/2)` and
`mStar = (1 + rStar) kStar`, with `kStar = (tStar + 1/2)/(3/2 - sStar)`, of
the stress of the model, and their positivity. The turned square D of the
model reaches the radial bound: `rhoStar = 2 hStar dStar`, the distance of its
centre from the disk centre.
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

lemma kStar_pos : 0 < kStar := by
  exact div_pos (by linarith [Six.tStar_bounds.1]) kStar_den_pos

lemma mStar_pos : 0 < mStar := by
  exact mul_pos (by linarith [rStar_pos]) kStar_pos

lemma one_add_rStar_pos : 0 < 1+rStar := by linarith [rStar_pos]

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

end SquaresInCircles.Six.Stress
