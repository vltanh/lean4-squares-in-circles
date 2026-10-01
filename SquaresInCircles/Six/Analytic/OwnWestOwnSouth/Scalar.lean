import SquaresInCircles.Six.Analytic.WestMixed.Reduction
import SquaresInCircles.Six.Analytic.RadicalPolynomialMajorant

/-!
# A continuous-weight analytic stress for two OWN wings

The CW, WD and DS weights are fixed at 41/20,1,211/200. The CS weight is
38/25+3s on the entire interval 0<=s<=12/25. It is not selected from a table.
WestMixed.Reduction leaves three geometric v,d boundary points while retaining
s. Multiplication by the positive fifth power of this weight removes the S
radical using the global polynomial majorant. Each boundary polynomial exceeds
the same explicit coarse polynomial below. Its positivity follows at once
from s<=1/2, with a positive tail coefficient 7437/256.
There is no subdivision of s and no generated stress certificate.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestOwnSouth
open WestMixed

def gamma (s : ℝ) : ℝ := 38/25+3*s
def constantTerm : ℝ := 3959823/5000000

def profile (v s d : ℝ) : ℝ :=
  constantTerm+base v s d+gamma s*(1+wing s)-
    CandidateWestTail.radiusBound*Real.sqrt ((gamma s)^2+nu^2)

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

private def trigLower (v s d : ℝ) : ℝ :=
  constantTerm+WestMixed.beta*(A*cosLower v+B*sinLower v)+
  (1/2)*cosLower (v+d)-B*sinUpper (v+d)+
  nu*cosLower (d-s)-waveCoefficient*cosUpper ((d-s)/2)+waveCoefficient*sinLower ((d-s)/2)+
  gamma s*(1+A*cosLower s+B*sinLower s)

private def lowerPolynomial (v s d : ℝ) : ℝ :=
  (gamma s)^5*trigLower v s d-
    CandidateWestTail.radiusBound*RadicalPolynomialMajorant.numerator (gamma s) nu

private lemma polynomial_le {v s d : ℝ} (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hd : 0 ≤ d) (hr : s ≤ d) :
    lowerPolynomial v s d ≤ (gamma s)^5*profile v s d := by
  have hg : 0 ≤ gamma s := by dsimp [gamma]; linarith
  have cv := Seven.cos_lower_six hv
  have sv := Seven.sin_lower_seven hv
  have cq := Seven.cos_lower_six (add_nonneg hv hd)
  have sq := Seven.sin_upper_five (add_nonneg hv hd)
  have cr := Seven.cos_lower_six (x := d-s) (by linarith)
  have ch := Seven.cos_upper_four (x := (d-s)/2) (by linarith)
  have sh := Seven.sin_lower_seven (x := (d-s)/2) (by linarith)
  have cs := Seven.cos_lower_six hs
  have ss := Seven.sin_lower_seven hs
  have hcs := mul_nonneg (mul_nonneg hg (by norm_num [A] : 0 ≤ A))
    (show 0 ≤ Real.cos s-cosLower s by exact sub_nonneg.mpr cs)
  have hss := mul_nonneg (mul_nonneg hg (by norm_num [B] : 0 ≤ B))
    (show 0 ≤ Real.sin s-sinLower s by exact sub_nonneg.mpr ss)
  have htrig : trigLower v s d ≤ constantTerm+base v s d+gamma s*(1+wing s) := by
    dsimp [trigLower,base,wing,gapWave,diagonalWave,WestMixed.beta,A,B,nu,waveCoefficient,
      rootSlope,CandidateWestTail.radiusBound,cosLower,cosUpper,sinLower,sinUpper] at *
    nlinarith only [cv,sv,cq,sq,cr,ch,sh,hcs,hss]
  have hm := mul_le_mul_of_nonneg_left htrig (show 0 ≤ (gamma s)^5 by positivity)
  have hroot := RadicalPolynomialMajorant.scaled_sqrt_upper (gamma s) nu hg
  have hR := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ CandidateWestTail.radiusBound by norm_num [CandidateWestTail.radiusBound])
  dsimp [lowerPolynomial,profile]
  nlinarith only [hm,hR]

/-- A single readable polynomial common to all three boundary points. -/
def coarse (s : ℝ) : ℝ :=
  1/50+s+3*s^2+16*s^3+68*s^4+144*s^5+34*s^6-
    302*s^7-307*s^8-17*s^9-s^12-s^13

lemma coarse_factor (s : ℝ) :
    coarse s=1/50+s+3*s^2+16*s^3+68*s^4+34*s^6+
      s^5*(144-302*s^2-307*s^3-17*s^4-s^7-s^8) := by
  dsimp [coarse]
  ring

lemma coarse_positive {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25) : 0 < coarse s := by
  have hhalf : s ≤ (1:ℝ)/2 := by linarith [hs.2]
  have h2 : s^2 ≤ ((1:ℝ)/2)^2 := pow_le_pow_left₀ hs.1 hhalf 2
  have h3 : s^3 ≤ ((1:ℝ)/2)^3 := pow_le_pow_left₀ hs.1 hhalf 3
  have h4 : s^4 ≤ ((1:ℝ)/2)^4 := pow_le_pow_left₀ hs.1 hhalf 4
  have h7 : s^7 ≤ ((1:ℝ)/2)^7 := pow_le_pow_left₀ hs.1 hhalf 7
  have h8 : s^8 ≤ ((1:ℝ)/2)^8 := pow_le_pow_left₀ hs.1 hhalf 8
  have htail : 7437/256 ≤ 144-302*s^2-307*s^3-17*s^4-s^7-s^8 := by
    norm_num at h2 h3 h4 h7 h8
    linarith
  have hprod := mul_nonneg (pow_nonneg hs.1 5)
    (show 0 ≤ 144-302*s^2-307*s^3-17*s^4-s^7-s^8 by linarith)
  rw [coarse_factor]
  have p2 := pow_nonneg hs.1 2
  have p3 := pow_nonneg hs.1 3
  have p4 := pow_nonneg hs.1 4
  have p6 := pow_nonneg hs.1 6
  exact add_pos_of_pos_of_nonneg (by linarith [hs.1]) hprod

private def vertexV (i : Fin 3) : ℝ := ![21/50,48/175,31/50] i
private def vertexD (i : Fin 3) : ℝ := ![16/25,11/14,16/25] i

/-- After expansion, each difference has only nonnegative monomial coefficients.
This is a coefficient comparison on one whole interval, not a cell checker. -/
lemma coarse_le_boundary (i : Fin 3) {s : ℝ} (hs : 0 ≤ s) :
    coarse s ≤ lowerPolynomial (vertexV i) s (vertexD i) := by
  apply sub_nonneg.mp
  fin_cases i <;>
    dsimp [coarse,lowerPolynomial,trigLower,RadicalPolynomialMajorant.numerator,
      gamma,constantTerm,WestMixed.beta,A,B,nu,waveCoefficient,rootSlope,
      CandidateWestTail.radiusBound,cosLower,cosUpper,sinLower,sinUpper,vertexV,vertexD] <;>
    ring_nf <;> positivity

lemma boundary_positive (i : Fin 3) {s : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25) :
    0 < profile (vertexV i) s (vertexD i) := by
  have hv : 0 ≤ vertexV i := by fin_cases i <;> norm_num [vertexV]
  have hd : 0 ≤ vertexD i := by fin_cases i <;> norm_num [vertexD]
  have hr : s ≤ vertexD i := by fin_cases i <;> norm_num [vertexD] <;> linarith [hs.2]
  have hp := polynomial_le hv hs.1 hd hr
  have hlo := (coarse_positive hs).trans_le (coarse_le_boundary i hs.1)
  have hg : 0 ≤ (gamma s)^5 := pow_nonneg (by dsimp [gamma]; linarith [hs.1]) 5
  by_contra! h
  have hm := mul_nonpos_of_nonneg_of_nonpos hg h
  linarith

/-- The complete scalar bound with a continuously varying, positive CS weight. -/
theorem positive {v s d : ℝ} (hs : 0 ≤ s ∧ s ≤ 12/25)
    (hd : 16/25 ≤ d ∧ d ≤ 11/14) (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    0 < profile v s d := by
  let K := constantTerm+gamma s*(1+wing s)-
    CandidateWestTail.radiusBound*Real.sqrt ((gamma s)^2+nu^2)
  have h0 := boundary_positive 0 hs
  have h1 := boundary_positive 1 hs
  have h2 := boundary_positive 2 hs
  have h := positive_of_three_points (K := K)
    (show -(2/5) ≤ s ∧ s ≤ 12/25 by constructor <;> linarith [hs.1,hs.2]) hd hv
    (by dsimp [K]; simpa [profile,vertexV,vertexD,add_assoc,add_left_comm,add_comm,sub_eq_add_neg] using h0)
    (by dsimp [K]; simpa [profile,vertexV,vertexD,add_assoc,add_left_comm,add_comm,sub_eq_add_neg] using h1)
    (by dsimp [K]; simpa [profile,vertexV,vertexD,add_assoc,add_left_comm,add_comm,sub_eq_add_neg] using h2)
  simpa [K,profile,add_assoc,add_left_comm,add_comm,sub_eq_add_neg] using h

end SquaresInCircles.Six.Analytic.OwnWestOwnSouth
