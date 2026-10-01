import SquaresInCircles.Six.Analytic.SouthOuterTail.RootConcavity

/-!
# The south tail profile

The south tail is the case of S separated from C along its own axis, at an
angle `s ∈ [11/25, 2/3]`, with D at an angle `d ∈ [1/2, 11/14]`. The stress with
weights `3/5`, `1`, `2/5` and `3/10` on C–W, C–S, W–D and D–S, after the support
bounds, is the function `profile k upper x s d` of the angles. W is separated
from C along its own axis (`k = 0`) or along the west side of C at an angle of
either sign (`k = 1, 2`), and `upper` selects the end of the range of the first
coordinate of the centre of C. In `s` and in `d` the profile is a first
harmonic with nonnegative coefficients, so its minimum over an interval is at
an end; in `x` this holds for `k = 0`, and for `k = 1, 2` the profile is
concave. So it is positive on the box once it is positive at the ends of the
three intervals.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail

def beta : ℝ := 3/5
def mu : ℝ := 2/5
def nu : ℝ := 3/10
def A : ℝ := 19359/50000
def B : ℝ := 30641/50000
def kappa : ℝ := CandidateWestTail.radiusBound/5
def southRootUpper : ℝ := 1044031/1000000

def face (upper : Bool) : ℝ := if upper then 5641/50000 else 0
def side (k : Fin 3) : ℝ := ![1,1,-1] k
def xMax (k : Fin 3) : ℝ := if k=0 then 11/25 else 2/5

def cosineCoefficient (k : Fin 3) (upper : Bool) : ℝ :=
  if k=0 then beta*(1/2-face upper) else beta
def sineCoefficient (k : Fin 3) : ℝ := ![beta*B,0,beta] k

def constantTerm (k : Fin 3) (upper : Bool) : ℝ :=
  (if k=0 then 23/10 else 2-beta*face upper)-
    CandidateWestTail.radiusBound*(southRootUpper+61/120)

def westRoot (k : Fin 3) (x : ℝ) : ℝ :=
  if k=0 then rootPolynomial 0 else rootPolynomial (side k*Real.sin x)

def profile (k : Fin 3) (upper : Bool) (x s d : ℝ) : ℝ :=
  constantTerm k upper+cosineCoefficient k upper*Real.cos x+sineCoefficient k*Real.sin x-
    CandidateWestTail.radiusBound*westRoot k x+
    A*Real.cos s+(1/2+face upper)*Real.sin s+
    mu*(Real.cos (d+side k*x)+Real.sin (d+side k*x))+nu*Real.cos (d-s)-
    kappa*Real.sin (side k*x+s)

private lemma x_trig {k : Fin 3} {x : ℝ} (hx : 0 ≤ x ∧ x ≤ xMax k) :
    9/10 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ 11/25 := by
  have hm : xMax k ≤ 11/25 := by fin_cases k <;> norm_num [xMax]
  have hu := hx.2.trans hm
  have hsq := mul_nonneg (sub_nonneg.mpr hu)
    (show 0 ≤ 11/25+x by linarith [hx.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  exact ⟨by nlinarith,
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hu,Real.pi_gt_d2]),
    (Real.sin_le hx.1).trans hu⟩

private lemma s_trig {s : ℝ} (hs : 11/25 ≤ s ∧ s ≤ 2/3) :
    7/9 ≤ Real.cos s ∧ 0 ≤ Real.sin s ∧ Real.sin s ≤ 2/3 := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hsq := mul_nonneg (sub_nonneg.mpr hs.2)
    (show 0 ≤ 2/3+s by linarith)
  exact ⟨by nlinarith [Real.one_sub_sq_div_two_le_cos (x := s)],
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [hs.2,Real.pi_gt_d2]),
    (Real.sin_le hs0).trans hs.2⟩

private lemma d_trig {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    69/100 ≤ Real.cos d ∧ 23/48 ≤ Real.sin d ∧ Real.sin d ≤ 71/100 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hd.2)
    (show 0 ≤ 11/14+d by linarith [hd.1])
  have hlow := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ (1:ℝ)/2 by linarith [Real.pi_pos])
    (show d ≤ Real.pi/2 by linarith [hd.2,Real.pi_gt_d2]) hd.1
  have hupp := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ d by linarith [hd.1,Real.pi_pos])
    (show (11:ℝ)/14 ≤ Real.pi/2 by linarith [Real.pi_gt_d2]) hd.2
  have hl := Real.sin_ge_sub_cube (x := (1:ℝ)/2) (by norm_num)
  have hu := Seven.sin_upper_five (x := (11:ℝ)/14) (by norm_num)
  exact ⟨by nlinarith [Real.one_sub_sq_div_two_le_cos (x := d)],
    by nlinarith only [hl,hlow],by nlinarith only [hu,hupp]⟩

def xA (k : Fin 3) (upper : Bool) (s d : ℝ) : ℝ :=
  cosineCoefficient k upper+mu*(Real.cos d+Real.sin d)-kappa*Real.sin s
def xB (k : Fin 3) (s d : ℝ) : ℝ :=
  sineCoefficient k+side k*(mu*(Real.cos d-Real.sin d)-kappa*Real.cos s)
def xK (k : Fin 3) (upper : Bool) (s d : ℝ) : ℝ :=
  constantTerm k upper+A*Real.cos s+(1/2+face upper)*Real.sin s+nu*Real.cos (d-s)

private lemma side_trig (k : Fin 3) (x : ℝ) :
    Real.cos (side k*x)=Real.cos x ∧ Real.sin (side k*x)=side k*Real.sin x := by
  fin_cases k <;> simp [side]

lemma x_identity (k : Fin 3) (upper : Bool) (x s d : ℝ) :
    profile k upper x s d=xK k upper s d+xA k upper s d*Real.cos x+xB k s d*Real.sin x-
      CandidateWestTail.radiusBound*westRoot k x := by
  have hσ := side_trig k x
  dsimp [profile,xK,xA,xB]
  rw [Real.cos_add d (side k*x),Real.sin_add d (side k*x),Real.sin_add (side k*x) s,
    hσ.1,hσ.2]
  ring

lemma x_coefficients (upper : Bool) {s d : ℝ}
    (hs : 11/25 ≤ s ∧ s ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    (0 ≤ xA 0 upper s d ∧ 0 ≤ xB 0 s d) ∧
    (21/25 ≤ xA 1 upper s d ∧ -(7/20) ≤ xB 1 s d) ∧
    (21/25 ≤ xA 2 upper s d ∧ 0 ≤ xB 2 s d) := by
  have ht := s_trig hs
  have hd' := d_trig hd
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩ <;>
    cases upper <;> dsimp [xA,xB,cosineCoefficient,sineCoefficient,side,face,beta,mu,A,B,
      kappa,CandidateWestTail.radiusBound] <;>
    nlinarith [ht.1,ht.2.1,ht.2.2,hd'.1,hd'.2.1,hd'.2.2,Real.cos_le_one s,Real.cos_le_one d]

def sA (k : Fin 3) (x d : ℝ) : ℝ := A+nu*Real.cos d-kappa*side k*Real.sin x
def sB (upper : Bool) (x d : ℝ) : ℝ := 1/2+face upper+nu*Real.sin d-kappa*Real.cos x

def sK (k : Fin 3) (upper : Bool) (x d : ℝ) : ℝ :=
  constantTerm k upper+cosineCoefficient k upper*Real.cos x+sineCoefficient k*Real.sin x-
    CandidateWestTail.radiusBound*westRoot k x+
    mu*(Real.cos (d+side k*x)+Real.sin (d+side k*x))

lemma s_identity (k : Fin 3) (upper : Bool) (x s d : ℝ) :
    profile k upper x s d=sK k upper x d+sA k x d*Real.cos s+sB upper x d*Real.sin s := by
  have hσ := side_trig k x
  dsimp [profile,sK,sA,sB]
  rw [Real.cos_sub d s,Real.sin_add (side k*x) s,hσ.1,hσ.2]
  ring

lemma s_coefficients (k : Fin 3) (upper : Bool) {x d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ xMax k) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ sA k x d ∧ 0 ≤ sB upper x d := by
  have ht := x_trig hx
  have htD := d_trig hd
  fin_cases k <;> cases upper <;> dsimp [sA,sB,A,nu,kappa,side,face,CandidateWestTail.radiusBound] <;>
    constructor <;> nlinarith [ht.1,ht.2.1,ht.2.2,htD.1,htD.2.1,Real.cos_le_one x]

def dA (k : Fin 3) (x s : ℝ) : ℝ :=
  mu*(Real.cos x+side k*Real.sin x)+nu*Real.cos s
def dB (k : Fin 3) (x s : ℝ) : ℝ :=
  mu*(Real.cos x-side k*Real.sin x)+nu*Real.sin s

def dK (k : Fin 3) (upper : Bool) (x s : ℝ) : ℝ :=
  constantTerm k upper+cosineCoefficient k upper*Real.cos x+sineCoefficient k*Real.sin x-
    CandidateWestTail.radiusBound*westRoot k x+
    A*Real.cos s+(1/2+face upper)*Real.sin s-kappa*Real.sin (side k*x+s)

lemma d_identity (k : Fin 3) (upper : Bool) (x s d : ℝ) :
    profile k upper x s d=dK k upper x s+dA k x s*Real.cos d+dB k x s*Real.sin d := by
  have hσ := side_trig k x
  dsimp [profile,dK,dA,dB]
  rw [Real.cos_add d (side k*x),Real.sin_add d (side k*x),Real.cos_sub d s,hσ.1,hσ.2]
  ring

lemma d_coefficients (k : Fin 3) {x s : ℝ}
    (hx : 0 ≤ x ∧ x ≤ xMax k) (hs : 11/25 ≤ s ∧ s ≤ 2/3) :
    0 ≤ dA k x s ∧ 0 ≤ dB k x s := by
  have ht := x_trig hx
  have htS := s_trig hs
  fin_cases k <;> dsimp [dA,dB,side,mu,nu] <;> constructor <;>
    nlinarith [ht.1,ht.2.1,ht.2.2,htS.1,htS.2.1]

lemma extend_south (k : Fin 3) (upper : Bool) {x s d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ xMax k) (hs : 11/25 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hl : 0 < profile k upper x (11/25) d) (hu : 0 < profile k upper x (2/3) d) :
    0 < profile k upper x s d := by
  rw [s_identity] at hl hu ⊢
  have hc := s_coefficients k upper hx hd
  have h := trig_lower_of_endpoints hc.1 hc.2 (by norm_num)
    (by linarith [Real.pi_gt_d2]) hs (C := -sK k upper x d) (by linarith) (by linarith)
  linarith

lemma extend_diagonal (k : Fin 3) (upper : Bool) {x s d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ xMax k) (hs : 11/25 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hl : 0 < profile k upper x s (1/2)) (hu : 0 < profile k upper x s (11/14)) :
    0 < profile k upper x s d := by
  rw [d_identity] at hl hu ⊢
  have hc := d_coefficients k hx hs
  have h := trig_lower_of_endpoints hc.1 hc.2 (by norm_num)
    (by linarith [Real.pi_gt_d2]) hd (C := -dK k upper x s) (by linarith) (by linarith)
  linarith

lemma extend_west (k : Fin 3) (upper : Bool) {x s d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ xMax k) (hs : 11/25 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hl : 0 < profile k upper 0 s d) (hu : 0 < profile k upper (xMax k) s d) :
    0 < profile k upper x s d := by
  have hc := x_coefficients upper hs hd
  rw [x_identity] at hl hu ⊢
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  · have hw (y : ℝ) : westRoot 0 y = rootPolynomial 0 := by simp [westRoot]
    simp only [hw] at hl hu ⊢
    have h := trig_lower_of_endpoints hc.1.1 hc.1.2 (by norm_num)
      (by norm_num [xMax]; linarith [Real.pi_gt_d2]) hx
      (C := CandidateWestTail.radiusBound*rootPolynomial 0-xK 0 upper s d)
      (by linarith) (by linarith)
    linarith
  · have h := positive_on_concave_interval
      (cardinal_slice_concave false (K := xK 1 upper s d) hc.2.1.1 hc.2.1.2)
      (show 0 ≤ x ∧ x ≤ 2/5 by simpa [xMax] using hx)
      (by simpa [cardinalSlice,rootSign,westRoot,side] using hl)
      (by simpa [cardinalSlice,rootSign,westRoot,side,xMax] using hu)
    simpa [cardinalSlice,rootSign,westRoot,side] using h
  · have h := positive_on_concave_interval
      (cardinal_slice_concave true (K := xK 2 upper s d) hc.2.2.1 hc.2.2.2)
      (show 0 ≤ x ∧ x ≤ 2/5 by simpa [xMax] using hx)
      (by simpa [cardinalSlice,rootSign,westRoot,side] using hl)
      (by simpa [cardinalSlice,rootSign,westRoot,side,xMax] using hu)
    simpa [cardinalSlice,rootSign,westRoot,side] using h

end SquaresInCircles.Six.Analytic.SouthOuterTail
