import SquaresInCircles.Six.Analytic.CandidateWestTail.Support

/-!
# A stronger D-sourced west gap

Use the three actual CW, CD and D-sourced WD inequalities with weights
27/100, 57/25 and 1. The W far-vertex resultant is bounded by one global
square-root tangent at 31/25, not by an unjustified axial support.
Writing q=d+v leaves the full rectangle
  1<=q<=53/50, 3/5<=d<=11/14.
Every coordinate slice of the resulting minorant is a constant plus a
positive sine/cosine combination. Its four corner Taylor lower bounds exceed
1/400. Hence no packing can realize this entire short-gap rectangle.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestGapReserve

/-- The rational minorant after the two vertex supports. -/
def profile (q d : ℝ) : ℝ :=
  -376881562797/155000000000+
  (27/100)*((19359/50000)*Real.cos (q-d)+(30641/50000)*Real.sin (q-d))+
  (57/25)*(19359/50000)*(Real.cos d+Real.sin d)+
  Real.cos q+(392039/620000)*Real.sin q

private def qA (d : ℝ) : ℝ :=
  1+(27/100)*((19359/50000)*Real.cos d-(30641/50000)*Real.sin d)
private def qB (d : ℝ) : ℝ :=
  392039/620000+(27/100)*((19359/50000)*Real.sin d+(30641/50000)*Real.cos d)
private def qK (d : ℝ) : ℝ :=
  -376881562797/155000000000+(57/25)*(19359/50000)*(Real.cos d+Real.sin d)
private def dA (q : ℝ) : ℝ :=
  (57/25)*(19359/50000)+(27/100)*((19359/50000)*Real.cos q+(30641/50000)*Real.sin q)
private def dB (q : ℝ) : ℝ :=
  (57/25)*(19359/50000)+(27/100)*((19359/50000)*Real.sin q-(30641/50000)*Real.cos q)
private def dK (q : ℝ) : ℝ :=
  -376881562797/155000000000+Real.cos q+(392039/620000)*Real.sin q

private lemma q_identity (q d : ℝ) :
    profile q d=qK d+qA d*Real.cos q+qB d*Real.sin q := by
  dsimp [profile,qK,qA,qB]
  rw [Real.cos_sub,Real.sin_sub]
  ring

private lemma d_identity (q d : ℝ) :
    profile q d=dK q+dA q*Real.cos d+dB q*Real.sin d := by
  dsimp [profile,dK,dA,dB]
  rw [Real.cos_sub,Real.sin_sub]
  ring

private lemma q_coefficients (d : ℝ) : 0 ≤ qA d ∧ 0 ≤ qB d := by
  dsimp [qA,qB]
  constructor <;> linarith [Real.neg_one_le_cos d,Real.cos_le_one d,
    Real.neg_one_le_sin d,Real.sin_le_one d]

private lemma d_coefficients (q : ℝ) : 0 ≤ dA q ∧ 0 ≤ dB q := by
  dsimp [dA,dB]
  constructor <;> linarith [Real.neg_one_le_cos q,Real.cos_le_one q,
    Real.neg_one_le_sin q,Real.sin_le_one q]

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def lowerPolynomial (q d : ℝ) : ℝ :=
  -376881562797/155000000000+
  (27/100)*((19359/50000)*cosLower (q-d)+(30641/50000)*sinLower (q-d))+
  (57/25)*(19359/50000)*(cosLower d+sinLower d)+
  cosLower q+(392039/620000)*sinLower q

private lemma polynomial_le {q d : ℝ} (hd : 0 ≤ d) (hqd : d ≤ q) :
    lowerPolynomial q d ≤ profile q d := by
  have cv := Seven.cos_lower_six (x := q-d) (by linarith)
  have sv := Seven.sin_lower_seven (x := q-d) (by linarith)
  have cd := Seven.cos_lower_six hd
  have sd := Seven.sin_lower_seven hd
  have cq := Seven.cos_lower_six (x := q) (by linarith)
  have sq := Seven.sin_lower_seven (x := q) (by linarith)
  dsimp [lowerPolynomial,profile,cosLower,sinLower]
  nlinarith only [cv,sv,cd,sd,cq,sq]

lemma four_corners :
    0 < profile 1 (3/5) ∧ 0 < profile 1 (11/14) ∧
    0 < profile (53/50) (3/5) ∧ 0 < profile (53/50) (11/14) := by
  have h0 := polynomial_le (q := 1) (d := 3/5) (by norm_num) (by norm_num)
  have h1 := polynomial_le (q := 1) (d := 11/14) (by norm_num) (by norm_num)
  have h2 := polynomial_le (q := 53/50) (d := 3/5) (by norm_num) (by norm_num)
  have h3 := polynomial_le (q := 53/50) (d := 11/14) (by norm_num) (by norm_num)
  norm_num [lowerPolynomial,cosLower,sinLower] at h0 h1 h2 h3
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

private lemma extend_diagonal {q d : ℝ} (hd : 3/5 ≤ d ∧ d ≤ 11/14)
    (hl : 0 < profile q (3/5)) (hu : 0 < profile q (11/14)) :
    0 < profile q d := by
  rw [d_identity] at hl hu ⊢
  have h := trig_lower_of_endpoints (d_coefficients q).1 (d_coefficients q).2
    (by norm_num : (0:ℝ) ≤ 3/5) (by linarith [Real.pi_gt_d2] : (11:ℝ)/14 ≤ Real.pi/2)
    hd (C := -dK q) (by linarith) (by linarith)
  linarith

/-- Positivity on the whole two-variable rectangle. -/
theorem positive {q d : ℝ} (hq : 1 ≤ q ∧ q ≤ 53/50)
    (hd : 3/5 ≤ d ∧ d ≤ 11/14) : 0 < profile q d := by
  have hl := extend_diagonal hd four_corners.1 four_corners.2.1
  have hu := extend_diagonal hd four_corners.2.2.1 four_corners.2.2.2
  rw [q_identity] at hl hu ⊢
  have h := trig_lower_of_endpoints (q_coefficients d).1 (q_coefficients d).2
    (by norm_num : (0:ℝ) ≤ 1) (by linarith [Real.pi_gt_d2] : (53:ℝ)/50 ≤ Real.pi/2)
    hq (C := -qK d) (by linarith) (by linarith)
  linarith

end SquaresInCircles.Six.Analytic.WestGapReserve
