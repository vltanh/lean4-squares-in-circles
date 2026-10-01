import SquaresInCircles.Six.Analytic.WestCoreBounds.Profile

/-!
# Two exact three-edge scalar obstructions

The first uses weights 17/3,14/3,1 and excludes v>=31/50 on the whole
rectangle 31/50<=v<=2/3, 3/5<=d<=11/14. Both resultants are axial.
The second uses weights 207/100,56/25,1 and excludes d<=16/25 after the
new v<31/50 and q>53/50 restrictions. Its domain is the quadrilateral
  3/5<=d<=16/25, 53/50-d<=v<=31/50.
Its D support is a universal vertex bound. Each proof evaluates exactly the
four geometric vertices, for either central y face, using Taylor inequalities.
Compilation and kernel acceptance remain unverified.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.WestCoreBounds

def beta (large : Bool) : ℝ := if large then 17/3 else 207/100
def delta (large : Bool) : ℝ := if large then 14/3 else 56/25
def constantTerm (large : Bool) : ℝ :=
  if large then -874871/150000 else -67837759/31250000

def value (large upper : Bool) (v d : ℝ) : ℝ :=
  profile (beta large) (delta large) (face upper) (constantTerm large) v d

lemma coefficients (large upper : Bool) :
    Coefficients (beta large) (delta large) (face upper) := by
  cases large <;> cases upper <;>
    constructor <;> norm_num [beta,delta,face,A,B]

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

private def lowerPolynomial (large upper : Bool) (v d : ℝ) : ℝ :=
  constantTerm large+
  beta large*(A*cosLower v+(1/2+face upper)*sinLower v)+
  delta large*(A*cosLower d+(1/2-face upper)*sinLower d)+
  (1/2)*cosLower (v+d)-B*sinUpper (v+d)

private lemma polynomial_le (large upper : Bool) {v d : ℝ} (hv : 0 ≤ v) (hd : 0 ≤ d) :
    lowerPolynomial large upper v d ≤ value large upper v d := by
  have cv := Seven.cos_lower_six hv
  have sv := Seven.sin_lower_seven hv
  have cd := Seven.cos_lower_six hd
  have sd := Seven.sin_lower_seven hd
  have cq := Seven.cos_lower_six (add_nonneg hv hd)
  have sq := Seven.sin_upper_five (add_nonneg hv hd)
  cases large <;> cases upper <;>
    dsimp [lowerPolynomial,value,profile,beta,delta,face,constantTerm,A,B,
      cosLower,sinLower,sinUpper] <;>
    nlinarith only [cv,sv,cd,sd,cq,sq]

lemma large_vertices (upper : Bool) :
    0 < value true upper (31/50) (3/5) ∧
    0 < value true upper (31/50) (11/14) ∧
    0 < value true upper (2/3) (3/5) ∧
    0 < value true upper (2/3) (11/14) := by
  have h0 := polynomial_le true upper (v := 31/50) (d := 3/5) (by norm_num) (by norm_num)
  have h1 := polynomial_le true upper (v := 31/50) (d := 11/14) (by norm_num) (by norm_num)
  have h2 := polynomial_le true upper (v := 2/3) (d := 3/5) (by norm_num) (by norm_num)
  have h3 := polynomial_le true upper (v := 2/3) (d := 11/14) (by norm_num) (by norm_num)
  cases upper <;> norm_num [lowerPolynomial,beta,delta,face,constantTerm,A,B,
    cosLower,sinLower,sinUpper] at h0 h1 h2 h3 <;>
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma low_vertices (upper : Bool) :
    0 < value false upper (23/50) (3/5) ∧
    0 < value false upper (21/50) (16/25) ∧
    0 < value false upper (31/50) (3/5) ∧
    0 < value false upper (31/50) (16/25) := by
  have h0 := polynomial_le false upper (v := 23/50) (d := 3/5) (by norm_num) (by norm_num)
  have h1 := polynomial_le false upper (v := 21/50) (d := 16/25) (by norm_num) (by norm_num)
  have h2 := polynomial_le false upper (v := 31/50) (d := 3/5) (by norm_num) (by norm_num)
  have h3 := polynomial_le false upper (v := 31/50) (d := 16/25) (by norm_num) (by norm_num)
  cases upper <;> norm_num [lowerPolynomial,beta,delta,face,constantTerm,A,B,
    cosLower,sinLower,sinUpper] at h0 h1 h2 h3 <;>
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem large_positive (upper : Bool) {v d : ℝ}
    (hv : 31/50 ≤ v ∧ v ≤ 2/3) (hd : 3/5 ≤ d ∧ d ≤ 11/14) :
    0 < value true upper v d := by
  have hc := coefficients true upper
  have hl := extend_diagonal hc
    (v := 31/50) (K := constantTerm true) (by constructor <;> linarith [Real.pi_gt_d2])
    (by norm_num) (by linarith [Real.pi_gt_d2]) hd
    (large_vertices upper).1 (large_vertices upper).2.1
  have hu := extend_diagonal hc
    (v := 2/3) (K := constantTerm true) (by constructor <;> linarith [Real.pi_gt_d2])
    (by norm_num) (by linarith [Real.pi_gt_d2]) hd
    (large_vertices upper).2.2.1 (large_vertices upper).2.2.2
  exact extend_west hc
    (by constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
    (by norm_num) (by linarith [Real.pi_gt_d2]) hv hl hu

theorem low_positive (upper : Bool) {v d : ℝ}
    (hd : 3/5 ≤ d ∧ d ≤ 16/25) (hv : 53/50-d ≤ v ∧ v ≤ 31/50) :
    0 < value false upper v d := by
  have hc := coefficients false upper
  have hbalance : beta false*(1/2+face upper)/2 ≤ delta false*(1/2-face upper) := by
    cases upper <;> norm_num [beta,delta,face]
  have hleft : 0 < value false upper (53/50-3/5) (3/5) := by
    convert (low_vertices upper).1 using 1 <;> norm_num
  have hright : 0 < value false upper (53/50-16/25) (16/25) := by
    convert (low_vertices upper).2.1 using 1 <;> norm_num
  have hwall := extend_gap_wall hc hbalance (K := constantTerm false)
    (by norm_num) (by linarith [Real.pi_gt_d2]) hd hleft hright
  have htop := extend_diagonal hc
    (v := 31/50) (K := constantTerm false) (by constructor <;> linarith [Real.pi_gt_d2])
    (by norm_num) (by linarith [Real.pi_gt_d2]) hd
    (low_vertices upper).2.2.1 (low_vertices upper).2.2.2
  exact extend_west hc
    (by constructor <;> linarith [hd.1,hd.2,Real.pi_gt_d2])
    (by linarith [hd.2]) (by linarith [Real.pi_gt_d2]) hv hwall htop

end SquaresInCircles.Six.Analytic.WestCoreBounds
