import SquaresInCircles.Six.Analytic.SouthOuterTail.OwnDiagonal

/-!
# The south tail with W on its own axis

The stress `raw` is positive for `v ∈ [0, 11/25]`, `s ∈ [11/25, 2/3]` and
`d ∈ [1/2, 11/14]`, and every local centre `(a, b)` of D in the disk with
`|b| ≤ 23/100`. By the first harmonics in `v` and `s` it is enough to take the
four corners. At three of them the far-vertex support of D, with the length
`√(μ² + ν² + 2μν z) ≤ 61/120 + z/5` of its force (`μ = 2/5`, `ν = 3/10`,
`z = sin (v + s)`), leaves a first harmonic in `d` with nonnegative
coefficients, positive at `d = 1/2` and `d = 11/14` by Taylor bounds. At the
corner `v = s = 11/25` the support of a nearly radial force leaves a term
decreasing in `d`, positive at `d = 11/14`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.SouthOuterTail.Own
open Normalization

def vertexProfile (upper : Bool) (v s d : ℝ) : ℝ :=
  constant-CandidateWestTail.radiusBound*(61/120)+
    weightW*(1/2-face upper)*Real.cos v+weightW*B*Real.sin v+
    A*Real.cos s+(1/2+face upper)*Real.sin s+
    mu*(Real.cos (d+v)+Real.sin (d+v))+nu*Real.cos (d-s)-kappa*Real.sin (v+s)
def vertexConstant (upper : Bool) (v s : ℝ) : ℝ :=
  constant-CandidateWestTail.radiusBound*(61/120)+
    weightW*(1/2-face upper)*Real.cos v+weightW*B*Real.sin v+
    A*Real.cos s+(1/2+face upper)*Real.sin s-kappa*Real.sin (v+s)

lemma diagonal_root_upper (z : ℝ) (hz : -(1:ℝ) ≤ z ∧ z ≤ 1) :
    Real.sqrt (mu^2+nu^2+2*mu*nu*z) ≤ 61/120+z/5 := by
  have hr : 0 ≤ mu^2+nu^2+2*mu*nu*z := by dsimp [mu,nu]; linarith [hz.1]
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (mu^2+nu^2+2*mu*nu*z)
  have hP : 0 ≤ 61/120+z/5 := by linarith [hz.1]
  have he := sq_nonneg (z/5-11/120)
  dsimp [mu,nu] at hs hn ⊢
  nlinarith only [hs,hn,hP,he]

lemma vertex_le_raw (upper : Bool) {v s d a b : ℝ} (hc : ContainedChart a |b|) :
    vertexProfile upper v s d ≤ raw upper v s d a b := by
  let U := mu*Real.sin (d+v)+nu*Real.cos (d-s)
  let V := mu*Real.cos (d+v)-nu*Real.sin (d-s)
  have h := CandidateWestTail.local_vertex_weak hc U V
  have ht : Real.sin (v+s)=Real.sin (d+v)*Real.cos (d-s)-
      Real.cos (d+v)*Real.sin (d-s) := by
    rw [← Real.sin_sub]
    congr 1
    ring
  have hn : U^2+V^2=mu^2+nu^2+2*mu*nu*Real.sin (v+s) := by
    dsimp [U,V]
    linear_combination mu^2*(Real.sin_sq_add_cos_sq (d+v))+
      nu^2*(Real.sin_sq_add_cos_sq (d-s))-2*mu*nu*ht
  rw [hn] at h
  have hr := diagonal_root_upper (Real.sin (v+s))
    ⟨Real.neg_one_le_sin _,Real.sin_le_one _⟩
  have hp := mul_le_mul CandidateWestTail.ceiling_bounds.1 hr (Real.sqrt_nonneg _)
    (by norm_num [CandidateWestTail.radiusBound])
  dsimp [vertexProfile,raw,U,V,kappa] at *
  nlinarith only [h,hp]

lemma vertex_diagonal_identity (upper : Bool) (v s d : ℝ) :
    vertexProfile upper v s d=vertexConstant upper v s+
      dA 0 v s*Real.cos d+dB 0 v s*Real.sin d := by
  dsimp [vertexProfile,vertexConstant,dA,dB,side]
  rw [Real.cos_add,Real.sin_add,Real.cos_sub]
  ring

private def vCorner (i : Fin 3) : ℝ := ![0,0,11/25] i
private def sCorner (i : Fin 3) : ℝ := ![11/25,2/3,2/3] i
private def dEnd (right : Bool) : ℝ := if right then 11/14 else 1/2
private def cosLower (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
private def sinLower (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040
private def sinUpper (x : ℝ) : ℝ := x-x^3/6+x^5/120

private lemma cos_lower (x : ℝ) : cosLower x ≤ Real.cos x := by
  by_cases hx : 0 ≤ x
  · exact Seven.cos_lower_six hx
  · have h := Seven.cos_lower_six (x := -x) (by linarith)
    have h2 : (-x)^2 = x^2 := by ring
    have h4 : (-x)^4 = x^4 := by ring
    have h6 : (-x)^6 = x^6 := by ring
    rw [h2,h4,h6,Real.cos_neg] at h
    simpa [cosLower] using h

private def polynomialLower (upper : Bool) (v s d : ℝ) : ℝ :=
  constant-CandidateWestTail.radiusBound*(61/120)+
    weightW*(1/2-face upper)*cosLower v+weightW*B*sinLower v+
    A*cosLower s+(1/2+face upper)*sinLower s+
    mu*(cosLower (d+v)+sinLower (d+v))+nu*cosLower (d-s)-kappa*sinUpper (v+s)

private lemma polynomial_le (upper : Bool) (i : Fin 3) {d : ℝ} (hd : 0 ≤ d) :
    polynomialLower upper (vCorner i) (sCorner i) d ≤
      vertexProfile upper (vCorner i) (sCorner i) d := by
  have hv : 0 ≤ vCorner i := by fin_cases i <;> norm_num [vCorner]
  have hs : 0 ≤ sCorner i := by fin_cases i <;> norm_num [sCorner]
  have cv := cos_lower (vCorner i)
  have sv := Seven.sin_lower_seven hv
  have cs := cos_lower (sCorner i)
  have ss := Seven.sin_lower_seven hs
  have cq := cos_lower (d+vCorner i)
  have sq := Seven.sin_lower_seven (add_nonneg hd hv)
  have cr := cos_lower (d-sCorner i)
  have sz := Seven.sin_upper_five (add_nonneg hv hs)
  cases upper <;>
    dsimp [polynomialLower,vertexProfile,cosLower,sinLower,sinUpper,
      weightW,face,A,B,mu,nu,kappa,CandidateWestTail.radiusBound] at * <;>
    nlinarith only [cv,sv,cs,ss,cq,sq,cr,sz]

private lemma endpoint_positive (upper right : Bool) (i : Fin 3) :
    0 < vertexProfile upper (vCorner i) (sCorner i) (dEnd right) := by
  have h := polynomial_le upper i
    (d := dEnd right) (by cases right <;> norm_num [dEnd])
  have hp : 0 < polynomialLower upper (vCorner i) (sCorner i) (dEnd right) := by
    cases upper <;> cases right <;> fin_cases i <;>
      norm_num [polynomialLower,vCorner,sCorner,dEnd,constant,weightW,face,A,B,mu,nu,
        kappa,CandidateWestTail.radiusBound,westRootUpper,southRootUpper,
        cosLower,sinLower,sinUpper]
  exact hp.trans_le h

private lemma raw_vertex_corner_positive (upper : Bool) (i : Fin 3) {d a b : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) (hc : ContainedChart a |b|) :
    0 < raw upper (vCorner i) (sCorner i) d a b := by
  have hv : 0 ≤ vCorner i ∧ vCorner i ≤ xMax 0 := by
    fin_cases i <;> norm_num [vCorner,xMax]
  have hs : 11/25 ≤ sCorner i ∧ sCorner i ≤ 2/3 := by
    fin_cases i <;> norm_num [sCorner]
  have hcoeff := d_coefficients 0 hv hs
  have hl := endpoint_positive upper false i
  have hu := endpoint_positive upper true i
  have hp : 0 < vertexProfile upper (vCorner i) (sCorner i) d := by
    rw [vertex_diagonal_identity] at hl hu ⊢
    have h := trig_lower_of_endpoints hcoeff.1 hcoeff.2 (by norm_num)
      (by linarith [Real.pi_gt_d2]) hd (C := -vertexConstant upper (vCorner i) (sCorner i))
      (by dsimp [dEnd] at hl; linarith)
      (by dsimp [dEnd] at hu; linarith)
    linarith
  exact hp.trans_le (vertex_le_raw upper hc)

def specialValue (upper : Bool) (d : ℝ) : ℝ :=
  constant+(weightW*(1/2-face upper)+A)*Real.cos corner+
    (weightW*B+1/2+face upper)*Real.sin corner-1/160+specialTerm d

lemma special_le_raw (upper : Bool) {d a b : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) (hc : ContainedChart a |b|) :
    specialValue upper d ≤ raw upper corner corner d a b := by
  have h := corner_support hc hd
  dsimp [specialValue,specialTerm,raw,forceU,forceV,B,CandidateWestTail.rhoBound] at *
  nlinarith only [h]

lemma special_endpoint_positive (upper : Bool) : 0 < specialValue upper (11/14) := by
  have ct := Seven.cos_lower_six (x := (11:ℝ)/25) (by norm_num)
  have st := Seven.sin_lower_seven (x := (11:ℝ)/25) (by norm_num)
  have cq := Seven.cos_lower_six (x := (429:ℝ)/350) (by norm_num)
  have sq := Seven.sin_upper_five (x := (429:ℝ)/350) (by norm_num)
  have cr := Seven.cos_upper_four (x := (121:ℝ)/350) (by norm_num)
  have sr := Seven.sin_lower_seven (x := (121:ℝ)/350) (by norm_num)
  cases upper <;>
    norm_num [specialValue,specialTerm,constant,corner,weightW,face,A,B,mu,nu,
      CandidateWestTail.radiusBound,westRootUpper,southRootUpper] <;>
    nlinarith only [ct,st,cq,sq,cr,sr]

lemma raw_special_corner_positive (upper : Bool) {d a b : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) (hc : ContainedChart a |b|) :
    0 < raw upper corner corner d a b := by
  have he := special_endpoint_positive upper
  have hm := special_at_upper_diagonal hd
  have hs : 0 < specialValue upper d := by
    dsimp [specialValue] at *
    linarith
  exact hs.trans_le (special_le_raw upper hd hc)

/-- With W on its own axis, the stress of the south tail is positive. -/
theorem positive_raw (upper : Bool) {v s d a b : ℝ}
    (hv : 0 ≤ v ∧ v ≤ 11/25) (hs : 11/25 ≤ s ∧ s ≤ 2/3)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) (hc : ContainedChart a |b|)
    (hb : |b| ≤ 23/100) : 0 < raw upper v s d a b := by
  have ha : 1/2 ≤ a ∧ a ≤ 1113/1000 :=
    ⟨hc.half_le,hc.a_le_rho0.trans rho0_upper.le⟩
  have hb' := abs_le.mp hb
  apply extend_raw_west upper hv hd ha hb'
  · apply extend_raw_south upper hs hd ha hb'
    · exact raw_vertex_corner_positive upper 0 hd hc
    · exact raw_vertex_corner_positive upper 1 hd hc
  · apply extend_raw_south upper hs hd ha hb'
    · exact raw_special_corner_positive upper hd hc
    · exact raw_vertex_corner_positive upper 2 hd hc

end SquaresInCircles.Six.Analytic.SouthOuterTail.Own
