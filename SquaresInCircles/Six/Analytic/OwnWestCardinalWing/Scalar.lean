import SquaresInCircles.Six.Analytic.WestMixed.Reduction

/-!
# W along its own axis, S along a side: positivity

The profile of the stress with weights `41/20`, `38/25`, `1` and `211/200` is
positive on `16/25 ≤ d ≤ 11/14`, `53/50 - d ≤ v ≤ 31/50` and `|s| ≤ 2/5`, where
`v`, `s` and `d` are the angles of W, S and D. For each sign of `s` the profile
is concave in `x = |s|` on `[0, 2/5]`, and the reduction in `(v, d)` leaves the
points `(21/50, 16/25)`, `(48/175, 11/14)` and `(31/50, 16/25)`. At these
points, with `x = 0` or `x = 2/5`, Taylor polynomials of `sin` and `cos` bound
the profile below by `1/1000`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.OwnWestCardinalWing
open WestMixed

def gamma : ℝ := 38/25
def rootIntercept : ℝ := 273901/148000
def rootSin : ℝ := 8018/9250

def constantTerm : ℝ := -51639691/29600000
def side (negative : Bool) : ℝ := if negative then -1 else 1
def sineCoefficient (negative : Bool) : ℝ :=
  if negative then 1302013/23125000 else 33847987/23125000

def southTerm (negative : Bool) (x : ℝ) : ℝ :=
  gamma*Real.cos x+sineCoefficient negative*Real.sin x

def profile (negative : Bool) (v x d : ℝ) : ℝ :=
  constantTerm+base v (side negative*x) d+southTerm negative x

private lemma south_term_concave (negative : Bool) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (southTerm negative) := by
  let f' : ℝ → ℝ := fun x => -gamma*Real.sin x+sineCoefficient negative*Real.cos x
  let f'' : ℝ → ℝ := fun x => -gamma*Real.cos x-sineCoefficient negative*Real.sin x
  have hf (x : ℝ) : HasDerivAt (southTerm negative) (f' x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul gamma).add
      ((Real.hasDerivAt_sin x).const_mul (sineCoefficient negative)) using 1
    · funext y
      simp only [southTerm,Pi.add_apply]
    · simp only [f']
      ring
  have hff (x : ℝ) : HasDerivAt f' (f'' x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul (-gamma)).add
      ((Real.hasDerivAt_cos x).const_mul (sineCoefficient negative)) using 1
    simp only [f'']
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (2/5))
    (f' := f') (f'' := f'') (fun x _ => (hf x).continuousAt.continuousWithinAt)
  · intro x _; exact (hf x).hasDerivWithinAt
  · intro x _; exact (hff x).hasDerivWithinAt
  · intro x hx
    have h := interior_subset hx
    have hc := Real.cos_nonneg_of_mem_Icc
      (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith [h.1,h.2,Real.pi_gt_d2])
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi h.1
      (by linarith [h.2,Real.pi_gt_d2])
    cases negative <;> dsimp [f'',gamma,sineCoefficient] <;> linarith

lemma south_concave (negative : Bool) {v d : ℝ}
    (hd : 16/25 ≤ d ∧ d ≤ 11/14) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (fun x => profile negative v x d) := by
  have hD0 := concave_affine_argument (a := -side negative) (b := d) diagonal_concave
    (l := 0) (u := 2/5) (by
      intro x hx
      cases negative <;> dsimp [side] <;> constructor <;>
        linarith [hd.1,hd.2,hx.1,hx.2])
  have hD : ConcaveOn ℝ (Set.Icc 0 (2/5))
      (fun x => diagonalWave (d-side negative*x)) := by
    convert hD0 using 1
    funext x
    congr 1
    ring
  have h := ((concave_constant
    (constantTerm+WestMixed.beta*wing v+gapWave (v+d)) 0 (2/5)).add hD).add (south_term_concave negative)
  convert h using 1
  funext x
  dsimp [profile,base]
  ring

private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def cosUpper (x : ℝ) : ℝ := 1-x^2/2+x^4/24
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

private def lowerPolynomial (negative : Bool) (v x d : ℝ) : ℝ :=
  constantTerm+WestMixed.beta*(A*cosLower v+B*sinLower v)+
  (1/2)*cosLower (v+d)-B*sinUpper (v+d)+
  nu*cosLower (d-side negative*x)-waveCoefficient*cosUpper ((d-side negative*x)/2)+
  waveCoefficient*sinLower ((d-side negative*x)/2)+
  gamma*cosLower x+sineCoefficient negative*sinLower x

private lemma polynomial_le (negative : Bool) {v x d : ℝ}
    (hv : 0 ≤ v) (hx : 0 ≤ x) (hd : 0 ≤ d) (hr : 0 ≤ d-side negative*x) :
    lowerPolynomial negative v x d ≤ profile negative v x d := by
  have cv := Seven.cos_lower_six hv
  have sv := Seven.sin_lower_seven hv
  have cq := Seven.cos_lower_six (add_nonneg hv hd)
  have sq := Seven.sin_upper_five (add_nonneg hv hd)
  have cr := Seven.cos_lower_six hr
  have ch := Seven.cos_upper_four (x := (d-side negative*x)/2) (by linarith)
  have sh := Seven.sin_lower_seven (x := (d-side negative*x)/2) (by linarith)
  have cx := Seven.cos_lower_six hx
  have sx := Seven.sin_lower_seven hx
  cases negative <;>
    dsimp [lowerPolynomial,profile,base,wing,gapWave,diagonalWave,southTerm,
      WestMixed.beta,A,B,nu,waveCoefficient,rootSlope,CandidateWestTail.radiusBound,
      gamma,sineCoefficient,cosLower,cosUpper,sinLower,sinUpper] <;>
    nlinarith only [cv,sv,cq,sq,cr,ch,sh,cx,sx]

private def vertexV (i : Fin 3) : ℝ := ![21/50,48/175,31/50] i
private def vertexD (i : Fin 3) : ℝ := ![16/25,11/14,16/25] i
private def endpoint (upper : Bool) : ℝ := if upper then 2/5 else 0

private lemma endpoint_margin (negative upper : Bool) (i : Fin 3) :
    (1:ℝ)/1000 < lowerPolynomial negative (vertexV i) (endpoint upper) (vertexD i) := by
  cases negative <;> cases upper <;> fin_cases i <;>
    norm_num [lowerPolynomial,constantTerm,WestMixed.beta,A,B,nu,waveCoefficient,rootSlope,
      CandidateWestTail.radiusBound,gamma,sineCoefficient,side,
      cosLower,cosUpper,sinLower,sinUpper,vertexV,vertexD,endpoint]

lemma boundary_positive (negative : Bool) (i : Fin 3) {x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 2/5) : 0 < profile negative (vertexV i) x (vertexD i) := by
  have endpos (upper : Bool) :
      0 < profile negative (vertexV i) (endpoint upper) (vertexD i) := by
    have hv : 0 ≤ vertexV i := by fin_cases i <;> norm_num [vertexV]
    have hx : 0 ≤ endpoint upper := by cases upper <;> norm_num [endpoint]
    have hd : 0 ≤ vertexD i := by fin_cases i <;> norm_num [vertexD]
    have hr : 0 ≤ vertexD i-side negative*endpoint upper := by
      cases negative <;> cases upper <;> fin_cases i <;> norm_num [vertexD,side,endpoint]
    have hp := polynomial_le negative hv hx hd hr
    have hm := endpoint_margin negative upper i
    linarith
  have hd : 16/25 ≤ vertexD i ∧ vertexD i ≤ 11/14 := by
    fin_cases i <;> norm_num [vertexD]
  have h0 := endpos false
  have h1 := endpos true
  have he0 : endpoint false=0 := by simp [endpoint]
  have he1 : endpoint true=2/5 := by simp [endpoint]
  rw [he0] at h0
  rw [he1] at h1
  exact positive_on_concave_interval (f := fun x => profile negative (vertexV i) x (vertexD i))
    (south_concave negative hd) hx h0 h1

/-- The profile is positive on its whole domain, for either sign of `s`. -/
theorem positive (negative : Bool) {v x d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 2/5) (hd : 16/25 ≤ d ∧ d ≤ 11/14)
    (hv : 53/50-d ≤ v ∧ v ≤ 31/50) : 0 < profile negative v x d := by
  have hs : -(2/5) ≤ side negative*x ∧ side negative*x ≤ 12/25 := by
    cases negative <;> dsimp [side] <;> constructor <;> linarith [hx.1,hx.2]
  have h0 := boundary_positive negative 0 hx
  have h1 := boundary_positive negative 1 hx
  have h2 := boundary_positive negative 2 hx
  have h := positive_of_three_points (K := constantTerm+southTerm negative x) hs hd hv
    (by simpa [profile,vertexV,vertexD,add_assoc,add_left_comm,add_comm] using h0)
    (by simpa [profile,vertexV,vertexD,add_assoc,add_left_comm,add_comm] using h1)
    (by simpa [profile,vertexV,vertexD,add_assoc,add_left_comm,add_comm] using h2)
  simpa [profile,add_assoc,add_left_comm,add_comm] using h

end SquaresInCircles.Six.Analytic.OwnWestCardinalWing
