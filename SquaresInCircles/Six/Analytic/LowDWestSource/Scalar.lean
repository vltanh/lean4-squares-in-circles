module
public import SquaresInCircles.Six.Analytic.OneRadianWestGap
public import SquaresInCircles.Six.Analytic.EndpointReduction

@[expose] public section

/-!
# A four-vertex obstruction for a D-sourced west edge below d = 3/5

Write v=-w. The already proved one-radian gap forces 1-d <= v, so the
remaining low-D domain is the quadrilateral
  1/2 <= d <= 3/5,  1-d <= v <= 2/3.
Use weights (39,43,18)/100 on CW, CD and WD. W is on the genuine axial
support branch; D has a constant vertex resultant. The two possible signs of
the central y-force are bounded separately, not by discarding its negative
W contribution.

After rational weakening, each coordinate slice and the boundary v=1-d is a
positive sine/cosine combination. Concavity therefore leaves precisely four
geometric vertices. The endpoint proof uses explicit Taylor inequalities.
No subdivision, numerical certificate, or generated stress table is used.
Compilation is deferred; these are written proof bodies, not a build log.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.LowDWestSource
open Normalization

def vSin (centralY : Bool) : ℝ := if centralY then 2379/10000 else 39/200
def dSin (centralY : Bool) : ℝ := if centralY then 16641/100000 else 43/200

def minorant (centralY : Bool) (v d : ℝ) : ℝ :=
  -2082409/5000000+(15093/100000)*Real.cos v+vSin centralY*Real.sin v+
    (16641/100000)*Real.cos d+dSin centralY*Real.sin d+
    (9/100)*Real.cos (v+d)-(5517/50000)*Real.sin (v+d)

private lemma coefficient_bounds (b : Bool) :
    3/20 < vSin b ∧ vSin b ≤ 2379/10000 ∧ 3/20 < dSin b := by
  cases b <;> norm_num [vSin,dSin]

/-- A uniform bound on the only coefficient combination which might look
negative after expanding the difference angle. -/
private lemma harmonic_bound (x : ℝ) :
    (9/100)*Real.sin x+(5517/50000)*Real.cos x ≤ 3/20 := by
  have hid : ((9/100)*Real.sin x+(5517/50000)*Real.cos x)^2+
      ((9/100)*Real.cos x-(5517/50000)*Real.sin x)^2 =
      (9/100:ℝ)^2+(5517/50000:ℝ)^2 := by
    linear_combination ((9/100:ℝ)^2+(5517/50000:ℝ)^2)*(Real.sin_sq_add_cos_sq x)
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h)
    (show 0 < (9/100)*Real.sin x+(5517/50000)*Real.cos x+3/20 by linarith)
  nlinarith [sq_nonneg ((9/100)*Real.cos x-(5517/50000)*Real.sin x)]

private lemma trig_nonnegative {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 4/3) :
    0 ≤ Real.cos x ∧ 0 ≤ Real.sin x := by
  exact ⟨Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_gt_d2]⟩,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_gt_d2])⟩

private def cosLower (x : ℝ) := 1-x^2/2+x^4/24-x^6/720
private def sinLower (x : ℝ) := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) := x-x^3/6+x^5/120
private def lowerPolynomial (b : Bool) (v d : ℝ) : ℝ :=
  -2082409/5000000+(15093/100000)*cosLower v+vSin b*sinLower v+
    (16641/100000)*cosLower d+dSin b*sinLower d+
    (9/100)*cosLower (v+d)-(5517/50000)*sinUpper (v+d)

private lemma polynomial_le (b : Bool) {v d : ℝ} (hv : 0 ≤ v) (hd : 0 ≤ d) :
    lowerPolynomial b v d ≤ minorant b v d := by
  have cv := Seven.cos_lower_six hv
  have sv := Seven.sin_lower_seven hv
  have cd := Seven.cos_lower_six hd
  have sd := Seven.sin_lower_seven hd
  have cq := Seven.cos_lower_six (add_nonneg hv hd)
  have sq := Seven.sin_upper_five (add_nonneg hv hd)
  cases b <;> dsimp [lowerPolynomial,minorant,vSin,dSin,cosLower,sinLower,sinUpper] <;>
    nlinarith only [cv,sv,cd,sd,cq,sq]

private lemma endpoints (b : Bool) :
    0 < minorant b (1/2) (1/2) ∧
    0 < minorant b (2/3) (1/2) ∧
    0 < minorant b (2/3) (3/5) ∧
    0 < minorant b (2/5) (3/5) := by
  have h1 := polynomial_le b (v := 1/2) (d := 1/2) (by norm_num) (by norm_num)
  have h2 := polynomial_le b (v := 2/3) (d := 1/2) (by norm_num) (by norm_num)
  have h3 := polynomial_le b (v := 2/3) (d := 3/5) (by norm_num) (by norm_num)
  have h4 := polynomial_le b (v := 2/5) (d := 3/5) (by norm_num) (by norm_num)
  cases b <;>
    norm_num [lowerPolynomial,vSin,dSin,cosLower,sinLower,sinUpper] at h1 h2 h3 h4 <;>
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

private lemma positive_trig_slice {A B K l u x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 ≤ l) (hu : u ≤ Real.pi/2)
    (hx : l ≤ x ∧ x ≤ u)
    (hleft : 0 < K+A*Real.cos l+B*Real.sin l)
    (hright : 0 < K+A*Real.cos u+B*Real.sin u) :
    0 < K+A*Real.cos x+B*Real.sin x := by
  have h := trig_lower_of_endpoints hA hB hl hu hx
    (C := -K) (by linarith) (by linarith)
  linarith

private lemma top_positive (b : Bool) {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 3/5) :
    0 < minorant b (2/3) d := by
  let A : ℝ := 16641/100000+(9/100)*Real.cos (2/3)-(5517/50000)*Real.sin (2/3)
  let B : ℝ := dSin b-(9/100)*Real.sin (2/3)-(5517/50000)*Real.cos (2/3)
  let K : ℝ := -2082409/5000000+(15093/100000)*Real.cos (2/3)+vSin b*Real.sin (2/3)
  have ident (x : ℝ) : minorant b (2/3) x=K+A*Real.cos x+B*Real.sin x := by
    dsimp [minorant,A,B,K]
    rw [Real.cos_add,Real.sin_add]
    ring
  have ht := trig_nonnegative (x := 2/3) ⟨by norm_num,by norm_num⟩
  have hA : 0 ≤ A := by dsimp [A]; linarith [Real.sin_le_one (2/3)]
  have hB : 0 ≤ B := by dsimp [B]; linarith [harmonic_bound (2/3),(coefficient_bounds b).2.2]
  rw [ident]
  apply positive_trig_slice hA hB (by norm_num) (by linarith [Real.pi_gt_d2]) hd
  · rw [← ident]
    exact (endpoints b).2.1
  · rw [← ident]
    exact (endpoints b).2.2.1

private lemma wall_positive (b : Bool) {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 3/5) :
    0 < minorant b (1-d) d := by
  let A : ℝ := 16641/100000+(15093/100000)*Real.cos 1+vSin b*Real.sin 1
  let B : ℝ := dSin b+(15093/100000)*Real.sin 1-vSin b*Real.cos 1
  let K : ℝ := -2082409/5000000+(9/100)*Real.cos 1-(5517/50000)*Real.sin 1
  have ident (x : ℝ) : minorant b (1-x) x=K+A*Real.cos x+B*Real.sin x := by
    dsimp [minorant,A,B,K]
    rw [show 1-x+x=1 by ring,Real.cos_sub,Real.sin_sub]
    ring
  have ht := trig_nonnegative (x := 1) ⟨by norm_num,by norm_num⟩
  have hv0 : 0 ≤ vSin b := by linarith [(coefficient_bounds b).1]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcos : Real.cos 1 ≤ 13/24 := by nlinarith [Seven.cos_upper_four (x := 1) (by norm_num)]
  have hprod := mul_le_mul (coefficient_bounds b).2.1 hcos ht.1 (by norm_num : (0:ℝ) ≤ 2379/10000)
  have hB : 0 ≤ B := by
    have hp := mul_nonneg (by norm_num : (0:ℝ) ≤ 15093/100000) ht.2
    dsimp [B]
    cases b <;> norm_num [dSin] at * <;> nlinarith only [hprod,hp]
  rw [ident]
  apply positive_trig_slice hA hB (by norm_num) (by linarith [Real.pi_gt_d2]) hd
  · rw [← ident]
    norm_num only [show (1:ℝ)-1/2=1/2 by norm_num]
    exact (endpoints b).1
  · rw [← ident]
    norm_num only [show (1:ℝ)-3/5=2/5 by norm_num]
    exact (endpoints b).2.2.2

/-- Positive on the entire physical quadrilateral, not on a sampled cover. -/
theorem positive (b : Bool) {v d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 3/5) (hv : 1-d ≤ v ∧ v ≤ 2/3) :
    0 < minorant b v d := by
  let A : ℝ := 15093/100000+(9/100)*Real.cos d-(5517/50000)*Real.sin d
  let B : ℝ := vSin b-(9/100)*Real.sin d-(5517/50000)*Real.cos d
  let K : ℝ := -2082409/5000000+(16641/100000)*Real.cos d+dSin b*Real.sin d
  have ident (x : ℝ) : minorant b x d=K+A*Real.cos x+B*Real.sin x := by
    dsimp [minorant,A,B,K]
    rw [Real.cos_add,Real.sin_add]
    ring
  have ht := trig_nonnegative ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have hA : 0 ≤ A := by dsimp [A]; linarith [Real.sin_le_one d]
  have hB : 0 ≤ B := by dsimp [B]; linarith [harmonic_bound d,(coefficient_bounds b).1]
  rw [ident]
  apply positive_trig_slice hA hB (by linarith [hd.2]) (by linarith [Real.pi_gt_d2]) hv
  · rw [← ident]
    exact wall_positive b hd
  · rw [← ident]
    exact top_positive b hd

end SquaresInCircles.Six.Analytic.LowDWestSource
