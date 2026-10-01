import SquaresInCircles.Six.Tails.West
import SquaresInCircles.Six.Wings.Separators

/-!
# Six squares: the south tail

If S is separated from C along its own axis, at the phase `3π/2 + s`, then
`s < 11/25`. Otherwise `s ∈ [11/25, 2/3]`; W–D and D–S are separated along the
secondary axes of W and of S, as in the model; D lies at an angle
`d ∈ [1/2, π/4]`; and W is either on the west side of C at an angle `σ x`,
`σ = ±1`, `0 ≤ x ≤ 2/5`, or on its own axis at the phase `π - v` with
`0 ≤ v ≤ 11/25`, by the west tail. The separating inequalities of C–W, C–S, W–D
and D–S, with the weights `3/5` (W on the west side) or `5/8` (W on its own
axis), `1`, `2/5` and `3/10`, contradict the supports of the squares.

For W on the west side, the length `√(13/25 - (12/25) sin v)` of the force on
W lies below its tangent at `c²`, with `c = 18/25`, or `c = 21/25` for
`v < -3/20`. After the far-vertex supports the stress is then a first harmonic
with nonnegative coefficients in each of `x`, `s` and `d`, so it is positive
once it is positive at the corners of the box, where Taylor polynomials bound it
below. For W on its own axis the stress keeps the centre of D; it is a first
harmonic with nonnegative coefficients in `v` and in `s`. At three corners the
far-vertex support of D leaves a first harmonic in `d`; at the corner
`v = s = 11/25` the force on D is nearly radial, its support exceeds `ρ0` times
its length by at most `1/160`, and what remains decreases in `d`.
-/

noncomputable section
namespace SquaresInCircles.Six.SouthTail
open Normalization Wings

/-! The weights are `beta` on C–W for W on the west side of C, `omega` for W on
its own axis, `1` on C–S, `mu` on W–D and `nu` on D–S. The rationals
`southRootUpper` and `westRootUpper` lie above `√(1 + ν²)` and `√(ω² + μ²)`, the
lengths of the forces on S and on W on its own axis, and `kappa` is the
coefficient of `sin (v + s)` in the support of D. -/

def beta : ℝ := 3/5
def omega : ℝ := 5/8
def mu : ℝ := 2/5
def nu : ℝ := 3/10
def kappa : ℝ := radiusBound/5
def southRootUpper : ℝ := 1044031/1000000
def westRootUpper : ℝ := 371021/500000

/-- An end of the range `[0, c̄]` of the first coordinate of the centre of C. -/
def face (upper : Bool) : ℝ := if upper then coreUpper else 0

/-- The sign `σ` of the angle of W on the west side of C. -/
def sideSign (neg : Bool) : ℝ := if neg then -1 else 1

lemma sideSign_trig (neg : Bool) (x : ℝ) :
    Real.cos (sideSign neg*x)=Real.cos x ∧ Real.sin (sideSign neg*x)=sideSign neg*Real.sin x := by
  cases neg <;> simp [sideSign]

/-! ### Supports

The far-vertex supports of S, of W on its own axis and of D. -/

lemma south_support {a b : ℝ} (hc : ContainedChart a |b|) :
    a+nu*b≤radiusBound*southRootUpper-(1+nu)/2 := by
  have h := local_vertex_support hc 1 nu
  rw [one_pow,one_mul] at h
  have hr : Real.sqrt (1+nu^2)≤southRootUpper :=
    (Real.sqrt_le_left (by norm_num [southRootUpper])).mpr (by norm_num [nu,southRootUpper])
  have hp := mul_le_mul ceiling_bounds.1 hr (Real.sqrt_nonneg _) (by norm_num [radiusBound])
  linarith [le_abs_self nu,abs_one (α := ℝ)]

lemma west_own_support {a b : ℝ} (hc : ContainedChart a |b|) :
    omega*a-mu*b≤radiusBound*westRootUpper-(omega+mu)/2 := by
  have h := local_vertex_support hc omega (-mu)
  have hr : Real.sqrt (omega^2+(-mu)^2)≤westRootUpper :=
    (Real.sqrt_le_left (by norm_num [westRootUpper])).mpr
      (by norm_num [omega,mu,westRootUpper])
  have hp := mul_le_mul ceiling_bounds.1 hr (Real.sqrt_nonneg _) (by norm_num [radiusBound])
  norm_num [omega,mu] at h hp ⊢
  nlinarith only [h,hp]

/-- The force on D, of length at most `61/120 + sin (v + s)/5`. -/
def diagonalU (v s d : ℝ) : ℝ := mu*Real.sin (d+v)+nu*Real.cos (d-s)
def diagonalV (v s d : ℝ) : ℝ := mu*Real.cos (d+v)-nu*Real.sin (d-s)

lemma diagonal_norm (v s d : ℝ) :
    (diagonalU v s d)^2+(diagonalV v s d)^2=mu^2+nu^2+2*mu*nu*Real.sin (v+s) := by
  have ht : Real.sin (v+s)=Real.sin (d+v)*Real.cos (d-s)-Real.cos (d+v)*Real.sin (d-s) := by
    rw [← Real.sin_sub]
    congr 1
    ring
  dsimp [diagonalU,diagonalV]
  linear_combination mu^2*(Real.sin_sq_add_cos_sq (d+v))+
    nu^2*(Real.sin_sq_add_cos_sq (d-s))-2*mu*nu*ht

lemma diagonal_root_upper {z : ℝ} (hz : -(1:ℝ)≤z ∧ z≤1) :
    Real.sqrt (mu^2+nu^2+2*mu*nu*z)≤61/120+z/5 := by
  refine (Real.sqrt_le_left (by linarith [hz.1])).mpr ?_
  have he := sq_nonneg (z/5-11/120)
  dsimp [mu,nu]
  nlinarith only [he]

lemma diagonal_vertex_support {a b : ℝ} (hc : ContainedChart a |b|) (v s d : ℝ) :
    diagonalU v s d*a+diagonalV v s d*b≤
      radiusBound*(61/120+Real.sin (v+s)/5)-(diagonalU v s d+diagonalV v s d)/2 := by
  have h := local_vertex_support hc (diagonalU v s d) (diagonalV v s d)
  rw [diagonal_norm] at h
  have hr := diagonal_root_upper ⟨Real.neg_one_le_sin (v+s),Real.sin_le_one (v+s)⟩
  have hp := mul_le_mul ceiling_bounds.1 hr (Real.sqrt_nonneg _) (by norm_num [radiusBound])
  nlinarith only [h,hp,le_abs_self (diagonalU v s d),le_abs_self (diagonalV v s d)]

private lemma s_trig {s : ℝ} (hs : 11/25≤s ∧ s≤2/3) :
    7/9≤Real.cos s ∧ 0≤Real.sin s ∧ Real.sin s≤2/3 := by
  have h := small_angle_nonneg (r := 2/3) ⟨by linarith [hs.1],hs.2⟩ (by norm_num)
  exact ⟨by linarith [h.1],h.2⟩

private lemma d_trig {d : ℝ} (hd : 1/2≤d ∧ d≤11/14) :
    69/100≤Real.cos d ∧ 23/48≤Real.sin d ∧ Real.sin d≤71/100 := by
  obtain ⟨hs,hs',hc,-⟩ := trig_bracket (by norm_num) (by linarith [Real.pi_gt_d2]) hd
  norm_num at hs hs' hc
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The coefficients of `cos d` and `sin d` in the term of D. -/
def dA (σ x s : ℝ) : ℝ := mu*(Real.cos x+σ*Real.sin x)+nu*Real.cos s
def dB (σ x s : ℝ) : ℝ := mu*(Real.cos x-σ*Real.sin x)+nu*Real.sin s

lemma d_coefficients {σ x s : ℝ} (hσ : σ=1 ∨ σ=-1)
    (hx : 0≤x ∧ x≤11/25) (hs : 11/25≤s ∧ s≤2/3) : 0≤dA σ x s ∧ 0≤dB σ x s := by
  have ht := small_angle_nonneg (r := 11/25) (hr := by norm_num) hx
  have htS := s_trig hs
  rcases hσ with rfl | rfl <;> dsimp [dA,dB,mu,nu] <;> constructor <;>
    nlinarith [ht.1,ht.2.1,ht.2.2,htS.1,htS.2.1]

/-! ### W on the west side of C -/

/-- The force on W on the west side of C at the angle `v` has length
`√(13/25 - (12/25) sin v)`, at most `(13/25 - (12/25) sin v + c²)/(2c)` for
every `c > 0`. -/
lemma west_side_support {a b v c : ℝ} (hc : ContainedChart a |b|) (hc0 : 0<c) :
    beta*Real.cos v*a+(beta*Real.sin v-mu)*b≤
      radiusBound*((13/25-(12/25)*Real.sin v+c^2)/(2*c))-
        (beta*Real.cos v+mu-beta*Real.sin v)/2 := by
  have h := local_vertex_support hc (beta*Real.cos v) (beta*Real.sin v-mu)
  have hn : (beta*Real.cos v)^2+(beta*Real.sin v-mu)^2=13/25-(12/25)*Real.sin v := by
    dsimp [beta,mu]
    linear_combination (9/25)*(Real.sin_sq_add_cos_sq v)
  rw [hn] at h
  have hp := mul_le_mul ceiling_bounds.1
    (sqrt_le_tangent hc0 (show 0≤13/25-(12/25)*Real.sin v by linarith [Real.sin_le_one v]))
    (Real.sqrt_nonneg _) (by norm_num [radiusBound])
  have hw : beta*Real.cos v+mu-beta*Real.sin v≤|beta*Real.cos v|+|beta*Real.sin v-mu| := by
    linarith [le_abs_self (beta*Real.cos v),neg_le_abs (beta*Real.sin v-mu)]
  nlinarith only [h,hp,hw]

/-- The stress of the south tail with W on the west side of C at the angle
`σ x`, after the supports of W, S and D and of the centre of C, where `c`
is the parameter of the majorant of the length of the force on W. -/
def sideProfile (neg upper : Bool) (c x s d : ℝ) : ℝ :=
  2-beta*face upper-radiusBound*(southRootUpper+61/120)+
    beta*Real.cos x+(if neg then beta else 0)*Real.sin x-
    radiusBound*((13/25-(12/25)*(sideSign neg*Real.sin x)+c^2)/(2*c))+
    A*Real.cos s+(1/2+face upper)*Real.sin s+
    mu*(Real.cos (d+sideSign neg*x)+Real.sin (d+sideSign neg*x))+nu*Real.cos (d-s)-
    kappa*Real.sin (sideSign neg*x+s)

/-- The coefficient of `sin x` in `sideProfile`. -/
private def sideXB (neg : Bool) (c s d : ℝ) : ℝ :=
  (if neg then beta else 0)+radiusBound*(12/25)*sideSign neg/(2*c)+
    sideSign neg*(mu*(Real.cos d-Real.sin d)-kappa*Real.cos s)

/-- `sideProfile` is a first harmonic in each of `x`, `s` and `d`. -/
private lemma side_forms (neg upper : Bool) (c x s d : ℝ) :
    sideProfile neg upper c x s d=(sideProfile neg upper c 0 s d-
        (beta+mu*(Real.cos d+Real.sin d)-kappa*Real.sin s))+
      (beta+mu*(Real.cos d+Real.sin d)-kappa*Real.sin s)*Real.cos x+
      sideXB neg c s d*Real.sin x ∧
    sideProfile neg upper c x s d=(sideProfile neg upper c x 0 d-
        (A+nu*Real.cos d-kappa*sideSign neg*Real.sin x))+
      (A+nu*Real.cos d-kappa*sideSign neg*Real.sin x)*Real.cos s+
      (1/2+face upper+nu*Real.sin d-kappa*Real.cos x)*Real.sin s ∧
    sideProfile neg upper c x s d=(sideProfile neg upper c x s 0-dA (sideSign neg) x s)+
      dA (sideSign neg) x s*Real.cos d+dB (sideSign neg) x s*Real.sin d := by
  have hσ := sideSign_trig neg x
  refine ⟨?_,?_,?_⟩ <;>
    simp only [sideProfile,sideXB,dA,dB,Real.cos_add,Real.sin_add,Real.cos_sub,hσ.1,hσ.2,
      Real.cos_zero,Real.sin_zero,Real.cos_neg,mul_zero,zero_add,add_zero,
      sub_zero,zero_sub] <;>
    ring

private def sEnd (right : Bool) : ℝ := if right then 2/3 else 11/25
private def dEnd (right : Bool) : ℝ := if right then 11/14 else 1/2

/-- The stress is positive on `[l, u] × [11/25, 2/3] × [1/2, 11/14]` when the
coefficient of `sin x` is nonnegative and the stress is positive at the
corners. -/
private lemma side_piece_positive (neg upper : Bool) {c l u x s d : ℝ}
    (hl : 0≤l) (hu : u≤2/5) (hx : l≤x ∧ x≤u) (hs : 11/25≤s ∧ s≤2/3)
    (hd : 1/2≤d ∧ d≤11/14)
    (hxb : ∀ s d, 11/25≤s ∧ s≤2/3 → 1/2≤d ∧ d≤11/14 → 0≤sideXB neg c s d)
    (hcorner : ∀ xb sb db : Bool,
      0<sideProfile neg upper c (if xb then u else l) (sEnd sb) (dEnd db)) :
    0<sideProfile neg upper c x s d := by
  have hse (sb : Bool) : 11/25≤sEnd sb ∧ sEnd sb≤2/3 := by cases sb <;> norm_num [sEnd]
  have hxe (xb : Bool) : 0≤(if xb then u else l) ∧ (if xb then u else l)≤2/5 := by
    cases xb <;> simp <;> constructor <;> linarith
  have alongD (xb sb : Bool) : 0<sideProfile neg upper c (if xb then u else l) (sEnd sb) d := by
    have hc := d_coefficients (σ := sideSign neg) (by cases neg <;> simp [sideSign])
      ⟨(hxe xb).1,by linarith [(hxe xb).2]⟩ (hse sb)
    have hl0 := hcorner xb sb false
    have hu0 := hcorner xb sb true
    rw [(side_forms neg upper c _ _ _).2.2] at hl0 hu0 ⊢
    dsimp [dEnd] at hl0 hu0
    exact harmonic_pos_of_endpoints hc.1 hc.2 (by norm_num) (by linarith [Real.pi_gt_d2]) hd
      hl0 hu0
  have alongS (xb : Bool) : 0<sideProfile neg upper c (if xb then u else l) s d := by
    have ht := small_angle_nonneg (r := 2/5) (hr := by norm_num) (hxe xb)
    have htD := d_trig hd
    have hc : 0≤A+nu*Real.cos d-kappa*sideSign neg*Real.sin (if xb then u else l) ∧
        0≤1/2+face upper+nu*Real.sin d-kappa*Real.cos (if xb then u else l) := by
      cases neg <;> cases upper <;>
        dsimp [sideSign,A,nu,kappa,face,coreUpper,radiusBound] <;> constructor <;>
        nlinarith [ht.1,ht.2.1,ht.2.2,htD.1,htD.2.1,Real.cos_le_one (if xb then u else l)]
    have hl0 := alongD xb false
    have hu0 := alongD xb true
    rw [(side_forms neg upper c _ _ _).2.1] at hl0 hu0 ⊢
    dsimp [sEnd] at hl0 hu0
    exact harmonic_pos_of_endpoints hc.1 hc.2 (by norm_num) (by linarith [Real.pi_gt_d2]) hs
      hl0 hu0
  have htS := s_trig hs
  have htD := d_trig hd
  have hxa : 0≤beta+mu*(Real.cos d+Real.sin d)-kappa*Real.sin s := by
    dsimp [beta,mu,kappa,radiusBound]
    nlinarith [htS.2.2,htD.1,htD.2.1]
  have hl0 := alongS false
  have hu0 := alongS true
  rw [(side_forms neg upper c _ _ _).1] at hl0 hu0 ⊢
  simp only [Bool.false_eq_true,ite_false,ite_true] at hl0 hu0
  exact harmonic_pos_of_endpoints hxa (hxb s d hs hd) hl (by linarith [Real.pi_gt_d2]) hx
    hl0 hu0

private def rootArgument (neg : Bool) (x : ℝ) : ℝ := if neg then -sinAbove x else sinBelow x

private def sideLower (neg upper : Bool) (c x s d : ℝ) : ℝ :=
  2-beta*face upper-radiusBound*(southRootUpper+61/120)+
    beta*cosLower x+(if neg then beta else 0)*sinBelow x-
    radiusBound*((13/25-(12/25)*rootArgument neg x+c^2)/(2*c))+
    A*cosLower s+(1/2+face upper)*sinBelow s+
    mu*(cosLower (d+sideSign neg*x)+sinBelow (d+sideSign neg*x))+nu*cosLower (d-s)-
    kappa*sinAbove (sideSign neg*x+s)

private lemma side_lower_le (neg upper : Bool) {c : ℝ} (hc : 0<c) (x s d : ℝ) :
    sideLower neg upper c x s d≤sideProfile neg upper c x s d := by
  have horder : rootArgument neg x≤sideSign neg*Real.sin x := by
    cases neg <;> simp [rootArgument,sideSign] <;> linarith [sinBelow_le x,le_sinAbove x]
  have hroot : radiusBound*((13/25-(12/25)*(sideSign neg*Real.sin x)+c^2)/(2*c))≤
      radiusBound*((13/25-(12/25)*rootArgument neg x+c^2)/(2*c)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num [radiusBound])
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have cx := cosLower_le x
  have sx := sinBelow_le x
  have cs := cosLower_le s
  have ss := sinBelow_le s
  have cq := cosLower_le (d+sideSign neg*x)
  have sq := sinBelow_le (d+sideSign neg*x)
  have cr := cosLower_le (d-s)
  have sz := le_sinAbove (sideSign neg*x+s)
  cases neg <;> cases upper <;>
    simp only [sideLower,sideProfile,Bool.false_eq_true,ite_false,ite_true,face,coreUpper,
      beta,mu,nu,A,kappa,radiusBound] at * <;>
    nlinarith only [hroot,cx,sx,cs,ss,cq,sq,cr,sz]

private lemma side_corner_plus (upper xb sb db : Bool) :
    0<sideProfile false upper (18/25) (if xb then 2/5 else 0) (sEnd sb) (dEnd db) := by
  refine lt_of_lt_of_le ?_ (side_lower_le false upper (by norm_num) _ _ _)
  cases upper <;> cases xb <;> cases sb <;> cases db <;>
    norm_num [sideLower,sEnd,dEnd,sideSign,face,coreUpper,beta,mu,nu,A,kappa,
      radiusBound,southRootUpper,rootArgument,cosLower,sinBelow,sinAbove,sinLower,sinUpper]

private lemma side_corner_near (upper xb sb db : Bool) :
    0<sideProfile true upper (18/25) (if xb then 3/20 else 0) (sEnd sb) (dEnd db) := by
  refine lt_of_lt_of_le ?_ (side_lower_le true upper (by norm_num) _ _ _)
  cases upper <;> cases xb <;> cases sb <;> cases db <;>
    norm_num [sideLower,sEnd,dEnd,sideSign,face,coreUpper,beta,mu,nu,A,kappa,
      radiusBound,southRootUpper,rootArgument,cosLower,sinBelow,sinAbove,sinLower,sinUpper]

private lemma side_corner_far (upper xb sb db : Bool) :
    0<sideProfile true upper (21/25) (if xb then 2/5 else 3/20) (sEnd sb) (dEnd db) := by
  refine lt_of_lt_of_le ?_ (side_lower_le true upper (by norm_num) _ _ _)
  cases upper <;> cases xb <;> cases sb <;> cases db <;>
    norm_num [sideLower,sEnd,dEnd,sideSign,face,coreUpper,beta,mu,nu,A,kappa,
      radiusBound,southRootUpper,rootArgument,cosLower,sinBelow,sinAbove,sinLower,sinUpper]

/-- The parameter of the majorant: `18/25`, or `21/25` for `σ = -1` and
`x > 3/20`. -/
def sideCenter (neg : Bool) (x : ℝ) : ℝ := if neg ∧ 3/20<x then 21/25 else 18/25

lemma sideCenter_pos (neg : Bool) (x : ℝ) : 0<sideCenter neg x := by
  unfold sideCenter
  split_ifs <;> norm_num

/-- With W on the west side of C the stress of the south tail is positive. -/
theorem side_positive (neg upper : Bool) {x s d : ℝ}
    (hx : 0≤x ∧ x≤2/5) (hs : 11/25≤s ∧ s≤2/3) (hd : 1/2≤d ∧ d≤11/14) :
    0<sideProfile neg upper (sideCenter neg x) x s d := by
  have hxb (c : ℝ) (hc : c=18/25 ∨ c=21/25) (s d : ℝ) (hs : 11/25≤s ∧ s≤2/3)
      (hd : 1/2≤d ∧ d≤11/14) : 0≤sideXB neg c s d := by
    have htS := s_trig hs
    have htD := d_trig hd
    rcases hc with rfl | rfl <;> cases neg <;>
      dsimp [sideXB,sideSign,beta,mu,kappa,radiusBound] <;>
      nlinarith [htS.1,htS.2.1,htD.1,htD.2.1,htD.2.2,Real.cos_le_one s,Real.cos_le_one d]
  by_cases hfar : neg=true ∧ 3/20<x
  · have he : sideCenter neg x=21/25 := by simp [sideCenter,hfar.1,hfar.2]
    rw [he]
    exact side_piece_positive neg upper (l := 3/20) (u := 2/5) (by norm_num) le_rfl
      ⟨hfar.2.le,hx.2⟩ hs hd (hxb _ (Or.inr rfl))
      (by rw [hfar.1]; exact side_corner_far upper)
  · cases neg
    · have he : sideCenter false x=18/25 := by simp [sideCenter]
      rw [he]
      exact side_piece_positive false upper (l := 0) (u := 2/5) le_rfl le_rfl hx hs hd
        (hxb _ (Or.inl rfl)) (side_corner_plus upper)
    · have hx' : x≤3/20 := by simpa using hfar
      have he : sideCenter true x=18/25 := by simp [sideCenter,not_lt.mpr hx']
      rw [he]
      exact side_piece_positive true upper (l := 0) (u := 3/20) le_rfl (by norm_num)
        ⟨hx.1,hx'⟩ hs hd (hxb _ (Or.inl rfl))
        (side_corner_near upper)

/-! ### W on its own axis -/

namespace Own

/-- The constant term of the stress with W on its own axis, after the far-vertex
supports of W and S. -/
def constant : ℝ := 93/40-radiusBound*(westRootUpper+southRootUpper)

/-- The stress with W on its own axis, keeping the centre `(a, b)` of D. -/
def raw (upper : Bool) (v s d a b : ℝ) : ℝ :=
  constant+omega*(1/2-face upper)*Real.cos v+omega*B*Real.sin v+
    A*Real.cos s+(1/2+face upper)*Real.sin s+
    mu*((1/2-b)*Real.cos (d+v)+(1/2-a)*Real.sin (d+v))+
    nu*((1/2-a)*Real.cos (d-s)+(1/2+b)*Real.sin (d-s))

private lemma raw_v_form (upper : Bool) (v s d a b : ℝ) :
    raw upper v s d a b=(constant+A*Real.cos s+(1/2+face upper)*Real.sin s+
        nu*((1/2-a)*Real.cos (d-s)+(1/2+b)*Real.sin (d-s)))+
      (omega*(1/2-face upper)+mu*((1/2-b)*Real.cos d+(1/2-a)*Real.sin d))*Real.cos v+
      (omega*B+mu*(-(1/2-b)*Real.sin d+(1/2-a)*Real.cos d))*Real.sin v := by
  dsimp [raw]
  rw [Real.cos_add,Real.sin_add]
  ring

private lemma raw_s_form (upper : Bool) (v s d a b : ℝ) :
    raw upper v s d a b=(constant+omega*(1/2-face upper)*Real.cos v+omega*B*Real.sin v+
        mu*((1/2-b)*Real.cos (d+v)+(1/2-a)*Real.sin (d+v)))+
      (A+nu*((1/2-a)*Real.cos d+(1/2+b)*Real.sin d))*Real.cos s+
      (1/2+face upper+nu*((1/2-a)*Real.sin d-(1/2+b)*Real.cos d))*Real.sin s := by
  dsimp [raw]
  rw [Real.cos_sub,Real.sin_sub]
  ring

private lemma unit_harmonic_upper {x y : ℝ} (hxy : x^2+y^2=1) :
    (73/100)*x+(613/1000)*y≤191/200 := by
  have hid : ((73/100)*x+(613/1000)*y)^2+((73/100)*y-(613/1000)*x)^2=
      (73/100:ℝ)^2+(613/1000:ℝ)^2 := by
    linear_combination ((73/100:ℝ)^2+(613/1000:ℝ)^2)*hxy
  by_contra! h
  have hp := mul_pos (sub_pos.mpr h) (show 0<(73/100)*x+(613/1000)*y+191/200 by linarith)
  nlinarith [sq_nonneg ((73/100)*y-(613/1000)*x)]

/-- For `1/2 ≤ a ≤ 1113/1000` and `|b| ≤ 23/100`, the coefficients of `cos v`,
`sin v`, `cos s` and `sin s` in `raw` are nonnegative. -/
private lemma raw_coefficients (upper : Bool) {d a b : ℝ}
    (hd : 1/2≤d ∧ d≤11/14)
    (ha : 1/2≤a ∧ a≤1113/1000) (hb : -(23/100)≤b ∧ b≤23/100) :
    (0≤omega*(1/2-face upper)+mu*((1/2-b)*Real.cos d+(1/2-a)*Real.sin d) ∧
      0≤omega*B+mu*(-(1/2-b)*Real.sin d+(1/2-a)*Real.cos d)) ∧
    (0≤A+nu*((1/2-a)*Real.cos d+(1/2+b)*Real.sin d) ∧
      0≤1/2+face upper+nu*((1/2-a)*Real.sin d-(1/2+b)*Real.cos d)) := by
  have ht := d_trig hd
  have hc : 0≤Real.cos d := by linarith [ht.1]
  have hs : 0≤Real.sin d := by linarith [ht.2.1]
  have hamin : 0≤a-1/2 := by linarith [ha.1]
  have has : (a-1/2)*Real.sin d≤613/1000 := by
    nlinarith only [mul_le_mul_of_nonneg_left (Real.sin_le_one d) hamin,ha.2]
  have hac : (a-1/2)*Real.cos d≤613/1000 := by
    nlinarith only [mul_le_mul_of_nonneg_left (Real.cos_le_one d) hamin,ha.2]
  have hbc := mul_nonneg (show 0≤(1/2-b)-27/100 by linarith [hb.2]) hc
  have hbs := mul_nonneg (show 0≤1/2+b by linarith [hb.1]) hs
  have v1 := mul_nonneg (show 0≤73/100-(1/2-b) by linarith [hb.1]) hs
  have v2 := mul_nonneg (show 0≤613/1000-(a-1/2) by linarith [ha.2]) hc
  have vu := unit_harmonic_upper (Real.sin_sq_add_cos_sq d)
  have s1 := mul_nonneg (show 0≤73/100-(1/2+b) by linarith [hb.2]) hc
  have s2 := mul_nonneg (show 0≤613/1000-(a-1/2) by linarith [ha.2]) hs
  have su := unit_harmonic_upper (x := Real.cos d) (y := Real.sin d)
    (by nlinarith only [Real.sin_sq_add_cos_sq d])
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · cases upper <;> dsimp [omega,face,coreUpper,mu] <;> nlinarith only [has,hbc,ht.1]
  · dsimp [omega,B,mu]
    nlinarith only [v1,v2,vu]
  · dsimp [A,nu]
    nlinarith only [hac,hbs]
  · cases upper <;> dsimp [face,coreUpper,nu] <;> nlinarith only [s1,s2,su]

/-- The stress with the far-vertex support of D in place of its centre. -/
def vertexProfile (upper : Bool) (v s d : ℝ) : ℝ :=
  constant-radiusBound*(61/120)+
    omega*(1/2-face upper)*Real.cos v+omega*B*Real.sin v+
    A*Real.cos s+(1/2+face upper)*Real.sin s+
    mu*(Real.cos (d+v)+Real.sin (d+v))+nu*Real.cos (d-s)-kappa*Real.sin (v+s)

lemma vertex_le_raw (upper : Bool) {v s d a b : ℝ} (hc : ContainedChart a |b|) :
    vertexProfile upper v s d≤raw upper v s d a b := by
  have h := diagonal_vertex_support hc v s d
  dsimp [vertexProfile,raw,diagonalU,diagonalV,kappa] at *
  nlinarith only [h]

private lemma vertex_d_form (upper : Bool) (v s d : ℝ) :
    vertexProfile upper v s d=(constant-radiusBound*(61/120)+
        omega*(1/2-face upper)*Real.cos v+omega*B*Real.sin v+
        A*Real.cos s+(1/2+face upper)*Real.sin s-kappa*Real.sin (v+s))+
      dA 1 v s*Real.cos d+dB 1 v s*Real.sin d := by
  dsimp [vertexProfile,dA,dB]
  rw [Real.cos_add,Real.sin_add,Real.cos_sub]
  ring

private def vCorner (i : Fin 3) : ℝ := ![0,0,11/25] i
private def sCorner (i : Fin 3) : ℝ := ![11/25,2/3,2/3] i

private def vertexLower (upper : Bool) (v s d : ℝ) : ℝ :=
  constant-radiusBound*(61/120)+
    omega*(1/2-face upper)*cosLower v+omega*B*sinBelow v+
    A*cosLower s+(1/2+face upper)*sinBelow s+
    mu*(cosLower (d+v)+sinBelow (d+v))+nu*cosLower (d-s)-kappa*sinAbove (v+s)

private lemma vertex_corner (upper right : Bool) (i : Fin 3) :
    0<vertexProfile upper (vCorner i) (sCorner i) (dEnd right) := by
  have hle : vertexLower upper (vCorner i) (sCorner i) (dEnd right)≤
      vertexProfile upper (vCorner i) (sCorner i) (dEnd right) := by
    have cv := cosLower_le (vCorner i)
    have sv := sinBelow_le (vCorner i)
    have cs := cosLower_le (sCorner i)
    have ss := sinBelow_le (sCorner i)
    have cq := cosLower_le (dEnd right+vCorner i)
    have sq := sinBelow_le (dEnd right+vCorner i)
    have cr := cosLower_le (dEnd right-sCorner i)
    have sz := le_sinAbove (vCorner i+sCorner i)
    cases upper <;>
      dsimp [vertexLower,vertexProfile,omega,face,coreUpper,A,B,mu,nu,kappa,radiusBound] at * <;>
      nlinarith only [cv,sv,cs,ss,cq,sq,cr,sz]
  refine lt_of_lt_of_le ?_ hle
  cases upper <;> cases right <;> fin_cases i <;>
    norm_num [vertexLower,vCorner,sCorner,dEnd,constant,omega,face,coreUpper,A,B,mu,nu,kappa,
      radiusBound,westRootUpper,southRootUpper,cosLower,sinBelow,sinAbove,sinLower,sinUpper]

private lemma raw_vertex_corner (upper : Bool) (i : Fin 3) {d a b : ℝ}
    (hd : 1/2≤d ∧ d≤11/14) (hc : ContainedChart a |b|) :
    0<raw upper (vCorner i) (sCorner i) d a b := by
  have hcoeff := d_coefficients (σ := 1) (Or.inl rfl)
    (show 0≤vCorner i ∧ vCorner i≤11/25 by fin_cases i <;> norm_num [vCorner])
    (show 11/25≤sCorner i ∧ sCorner i≤2/3 by fin_cases i <;> norm_num [sCorner])
  have hl := vertex_corner upper false i
  have hu := vertex_corner upper true i
  rw [vertex_d_form] at hl hu
  dsimp [dEnd] at hl hu
  have hp : 0<vertexProfile upper (vCorner i) (sCorner i) d := by
    rw [vertex_d_form]
    exact harmonic_pos_of_endpoints hcoeff.1 hcoeff.2 (by norm_num)
      (by linarith [Real.pi_gt_d2]) hd hl hu
  exact hp.trans_le (vertex_le_raw upper hc)

/-! At the corner `v = s = 11/25` the force `(forceU d, forceV d)` on D is the
vector `(rotationA, rotationB)` turned by `-d`; for `1/2 ≤ d ≤ 11/14` it lies in
the narrow cone `|V| ≤ (2/5) U`, so it is nearly radial. -/

def corner : ℝ := 11/25
def forceU (d : ℝ) : ℝ := mu*Real.sin (d+corner)+nu*Real.cos (d-corner)
def forceV (d : ℝ) : ℝ := mu*Real.cos (d+corner)-nu*Real.sin (d-corner)
def rotationA : ℝ := mu*Real.sin corner+nu*Real.cos corner
def rotationB : ℝ := mu*Real.cos corner+nu*Real.sin corner

lemma force_rotation (d : ℝ) :
    forceU d=rotationA*Real.cos d+rotationB*Real.sin d ∧
    forceV d=rotationB*Real.cos d-rotationA*Real.sin d := by
  constructor <;> dsimp [forceU,forceV,rotationA,rotationB] <;>
    simp only [Real.sin_add,Real.cos_add,Real.sin_sub,Real.cos_sub] <;> ring

lemma rotation_bounds :
    11/25≤rotationA ∧ rotationA≤443/1000 ∧ 489/1000≤rotationB ∧ rotationB≤49/100 := by
  have h := trig_bracket (l := 11/25) (u := 11/25) (x := 11/25) (by norm_num)
    (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
  norm_num at h
  dsimp [rotationA,rotationB,corner,mu,nu]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

lemma diagonal_trig_bounds {d : ℝ} (hd : 1/2≤d ∧ d≤11/14) :
    (69/100≤Real.cos d ∧ Real.cos d≤879/1000) ∧ 4/3<Real.cos d+Real.sin d := by
  have ht := d_trig hd
  obtain ⟨-,-,-,hcu⟩ := trig_bracket (by norm_num) (by linarith [Real.pi_gt_d2]) hd
  have hl := cosLower_le (1/2)
  have hl' := sinBelow_le (1/2)
  have hu := cosLower_le (11/14)
  have hu' := sinBelow_le (11/14)
  norm_num [cosLower,sinBelow,sinLower,sinUpper] at hl hl' hu hu'
  have h := harmonic_pos_of_endpoints (K := -4/3) (A := 1) (B := 1) (l := 1/2) (u := 11/14)
    (by norm_num) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_d2]) hd
    (by linarith) (by linarith)
  exact ⟨⟨ht.1,by norm_num at hcu; linarith⟩,by linarith⟩

lemma force_cone {d : ℝ} (hd : 1/2≤d ∧ d≤11/14) :
    (3/5≤forceU d ∧ forceU d≤7/10) ∧ |forceV d|≤(2/5)*forceU d := by
  have ht := d_trig hd
  have ht' := diagonal_trig_bounds hd
  have hc : 0≤Real.cos d := by linarith [ht.1]
  have hs : 0≤Real.sin d := by linarith [ht.2.1]
  have hr := rotation_bounds
  have hi := force_rotation d
  have u1 := mul_nonneg (show 0≤rotationA-11/25 by linarith [hr.1]) hc
  have u2 := mul_nonneg (show 0≤rotationB-489/1000 by linarith [hr.2.2.1]) hs
  have ulo : 3/5≤forceU d := by nlinarith only [u1,u2,hi.1,ht.2.1,ht'.2]
  have uhi : forceU d≤7/10 := by
    dsimp [forceU,mu,nu]
    linarith [Real.sin_le_one (d+corner),Real.cos_le_one (d-corner)]
  have v1 := mul_nonneg (show 0≤rotationB-489/1000 by linarith [hr.2.2.1]) hc
  have v2 := mul_nonneg (show 0≤443/1000-rotationA by linarith [hr.2.1]) hs
  have vlo : 0≤forceV d := by nlinarith only [v1,v2,hi.2,ht'.1.1,ht.2.2]
  have w1 := mul_nonneg
    (show 0≤(2/5)*rotationA-rotationB+157/500 by linarith [hr.1,hr.2.2.2]) hc
  have w2 := mul_nonneg
    (show 0≤(2/5)*rotationB+rotationA-1589/2500 by linarith [hr.1,hr.2.2.1]) hs
  have vhi : forceV d≤(2/5)*forceU d := by
    nlinarith only [w1,w2,hi.1,hi.2,ht'.1.2,ht.2.1]
  exact ⟨⟨ulo,uhi⟩,by rwa [abs_of_nonneg vlo]⟩

/-- The terms in `d` of the stress at the corner, after the narrow-cone support
of D, and their derivative. -/
def specialTerm (d : ℝ) : ℝ :=
  (mu/2)*Real.cos (d+corner)-mu*B*Real.sin (d+corner)-
    nu*B*Real.cos (d-corner)+(nu/2)*Real.sin (d-corner)
def specialFirst (d : ℝ) : ℝ :=
  -mu*(B*Real.cos (d+corner)+(1/2)*Real.sin (d+corner))+
    nu*((1/2)*Real.cos (d-corner)+B*Real.sin (d-corner))

lemma special_hasDeriv (d : ℝ) : HasDerivAt specialTerm (specialFirst d) d := by
  convert ((((((hasDerivAt_id d).add_const corner).cos).const_mul (mu/2)).sub
    ((((hasDerivAt_id d).add_const corner).sin).const_mul (mu*B))).sub
    ((((hasDerivAt_id d).sub_const corner).cos).const_mul (nu*B))).add
    ((((hasDerivAt_id d).sub_const corner).sin).const_mul (nu/2)) using 1
  · funext y
    simp only [specialTerm,Pi.add_apply,Pi.sub_apply,id]
  · dsimp [specialFirst]
    ring

lemma special_derivative_nonpositive {d : ℝ} (hd : 1/2≤d ∧ d≤11/14) :
    specialFirst d≤0 := by
  have hq : 47/50≤d+corner ∧ d+corner≤429/350 := by
    dsimp [corner]
    constructor <;> linarith [hd.1,hd.2]
  have hl := cosLower_le (47/50)
  have hl' := sinBelow_le (47/50)
  have hu := cosLower_le (429/350)
  have hu' := sinBelow_le (429/350)
  norm_num [cosLower,sinBelow,sinLower,sinUpper] at hl hl' hu hu'
  have hf := harmonic_pos_of_endpoints (K := -2/3) (A := B) (B := 1/2) (by norm_num [B])
    (by norm_num) (by norm_num) (by linarith [Real.pi_gt_d2]) hq
    (by dsimp [B]; linarith) (by dsimp [B]; linarith)
  have hs : Real.sin (d-corner)≤121/350 := by
    have h := Real.sin_le (show 0≤d-corner by dsimp [corner]; linarith [hd.1])
    dsimp [corner] at h ⊢
    linarith [hd.2]
  have hc := Real.cos_le_one (d-corner)
  dsimp [specialFirst,mu,nu,B] at *
  nlinarith only [hf,hs,hc]

/-- A lower bound for the stress at the corner, decreasing in `d`. -/
def specialValue (upper : Bool) (d : ℝ) : ℝ :=
  constant+(omega*(1/2-face upper)+A)*Real.cos corner+
    (omega*B+1/2+face upper)*Real.sin corner-1/160+specialTerm d

private lemma raw_special_corner (upper : Bool) {d a b : ℝ}
    (hd : 1/2≤d ∧ d≤11/14) (hc : ContainedChart a |b|) :
    0<raw upper corner corner d a b := by
  have hcone := force_cone hd
  have h := narrow_support hc hcone.1 hcone.2
  have hp := mul_nonneg (sub_nonneg.mpr ceiling_bounds.2.1) (show 0≤forceU d by linarith [hcone.1.1])
  have hle : specialValue upper d≤raw upper corner corner d a b := by
    dsimp [specialValue,specialTerm,raw,forceU,forceV,B,rhoBound] at *
    nlinarith only [h,hp]
  have hm : MonotoneOn (fun x => -specialTerm x) (Set.Icc (1/2) (11/14)) :=
    monoOn_of_hasDeriv_nonneg (d := fun x => -specialFirst x)
      (fun x _ => (special_hasDeriv x).continuousAt.neg.continuousWithinAt)
      (fun x _ => (special_hasDeriv x).neg)
      (fun x hx => neg_nonneg.mpr (special_derivative_nonpositive ⟨hx.1.le,hx.2.le⟩))
  have hmono := hm hd (by norm_num : (11:ℝ)/14∈Set.Icc (1/2) (11/14)) hd.2
  have hend : 0<specialValue upper (11/14) := by
    obtain ⟨st,-,ct,-⟩ := trig_bracket (l := 11/25) (u := 11/25) (x := 11/25)
      (by norm_num) (by linarith [Real.pi_gt_three]) ⟨le_rfl,le_rfl⟩
    have cq := cosLower_le (429/350)
    have sq := le_sinAbove (429/350)
    have cr := cos_upper_four (x := (121:ℝ)/350) (by norm_num)
    have sr := sinBelow_le (121/350)
    norm_num [cosLower,sinBelow,sinAbove,sinLower,sinUpper] at st ct cq sq cr sr
    cases upper <;>
      norm_num [specialValue,specialTerm,constant,corner,omega,face,coreUpper,A,B,mu,nu,
        radiusBound,westRootUpper,southRootUpper] <;>
      nlinarith only [st,ct,cq,sq,cr,sr]
  have hs : 0<specialValue upper d := by
    dsimp [specialValue] at *
    linarith
  exact hs.trans_le hle

/-- With W on its own axis, the stress of the south tail is positive. -/
theorem positive_raw (upper : Bool) {v s d a b : ℝ}
    (hv : 0≤v ∧ v≤11/25) (hs : 11/25≤s ∧ s≤2/3)
    (hd : 1/2≤d ∧ d≤11/14) (hc : ContainedChart a |b|)
    (hb : |b|≤23/100) : 0<raw upper v s d a b := by
  have hcf := raw_coefficients upper hd ⟨hc.half_le,by linarith [hc.a_le_rho0,rho0_bounds.2]⟩
    (abs_le.mp hb)
  have alongS {v : ℝ} (h0 : 0<raw upper v (11/25) d a b) (h1 : 0<raw upper v (2/3) d a b) :
      0<raw upper v s d a b := by
    rw [raw_s_form] at h0 h1 ⊢
    exact harmonic_pos_of_endpoints hcf.2.1 hcf.2.2 (by norm_num)
      (by linarith [Real.pi_gt_d2]) hs h0 h1
  have h0 : 0<raw upper 0 s d a b :=
    alongS (raw_vertex_corner upper 0 hd hc) (raw_vertex_corner upper 1 hd hc)
  have h1 : 0<raw upper (11/25) s d a b :=
    alongS (raw_special_corner upper hd hc) (raw_vertex_corner upper 2 hd hc)
  rw [raw_v_form] at h0 h1 ⊢
  exact harmonic_pos_of_endpoints hcf.1.1 hcf.1.2 (by norm_num)
    (by linarith [Real.pi_gt_d2]) hv h0 h1

end Own

/-! ### The tail -/

lemma south_cos_lower {s : ℝ} (hs : 11/25≤s ∧ s≤2/3) : 7/9≤Real.cos s :=
  (s_trig hs).1

/-- With W on its own axis the four separating inequalities are
inconsistent. -/
theorem own_impossible {v s d aw bw asouth bsouth ad bd cx cy : ℝ}
    (hv : 0≤v ∧ v≤11/25) (hs : 11/25≤s ∧ s≤2/3) (hd : 1/2≤d ∧ d≤11/14)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart asouth |bsouth|)
    (hD : ContainedChart ad |bd|) (hb : |bd|≤23/100)
    (hx : 0≤cx ∧ cx≤coreUpper) (hy : cy≤coreUpper)
    (hCW : 1/2+angularWidth v≤aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth s≤asouth-cx*Real.sin s+cy*Real.cos s)
    (hWD : 1/2+angularWidth (d+v)≤ad*Real.sin (d+v)+bd*Real.cos (d+v)-bw)
    (hDS : 1/2+angularWidth (d-s)≤bsouth+ad*Real.cos (d-s)-bd*Real.sin (d-s)) : False := by
  have hvSin := (Real.sin_le hv.1).trans hv.2
  have hfy : 0≤Real.cos s-omega*Real.sin v := by
    dsimp [omega]
    linarith [south_cos_lower hs]
  obtain ⟨y,hy,hcenter⟩ := center_face
    (X := Real.cos s-omega*Real.sin v) (Y := omega*Real.cos v-Real.sin s) hfy hy hx
  obtain ⟨upper,rfl⟩ : ∃ upper, y=face upper := by
    rcases hy with rfl | rfl
    exacts [⟨false,rfl⟩,⟨true,rfl⟩]
  have hsum : omega*(1/2+angularWidth v)+(1/2+angularWidth s)+
      mu*(1/2+angularWidth (d+v))+nu*(1/2+angularWidth (d-s))≤
      (omega*aw-mu*bw)+(asouth+nu*bsouth)+diagonalU v s d*ad+diagonalV v s d*bd+
      (omega*Real.cos v-Real.sin s)*cx+(Real.cos s-omega*Real.sin v)*cy := by
    dsimp [omega,mu,nu,diagonalU,diagonalV]
    linear_combination (5/8)*hCW+hCS+(2/5)*hWD+(3/10)*hDS
  have hw := west_own_support hW
  have hsu := south_support hS
  have wv := angularWidth_lower v
  have ws := angularWidth_lower s
  have wq := angularWidth_lower (d+v)
  have wr := angularWidth_lower (d-s)
  have hn : Own.raw upper v s d ad bd≤0 := by
    cases upper <;>
      dsimp [Own.raw,Own.constant,omega,diagonalU,diagonalV,mu,nu,A,B,coreUpper,face]
        at hsum hw hsu hcenter ⊢ <;>
      nlinarith only [hsum,hw,hsu,hcenter,wv,ws,wq,wr]
  exact (not_lt_of_ge hn) (Own.positive_raw upper hv hs hd hD hb)

/-- With W on the west side of C, at an angle of either sign, the four
separating inequalities are inconsistent. -/
theorem side_impossible (neg : Bool) {x s d aw bw asouth bsouth ad bd cx cy : ℝ}
    (hxangle : 0≤x ∧ x≤2/5) (hs : 11/25≤s ∧ s≤2/3) (hd : 1/2≤d ∧ d≤11/14)
    (hW : ContainedChart aw |bw|) (hS : ContainedChart asouth |bsouth|)
    (hD : ContainedChart ad |bd|)
    (hx : 0≤cx ∧ cx≤coreUpper) (hy : cy≤coreUpper)
    (hCW : 1/2+angularWidth (sideSign neg*x)≤
      aw*Real.cos (sideSign neg*x)+bw*Real.sin (sideSign neg*x)+cx)
    (hCS : 1/2+angularWidth s≤asouth-cx*Real.sin s+cy*Real.cos s)
    (hWD : 1/2+angularWidth (d+sideSign neg*x)≤
      ad*Real.sin (d+sideSign neg*x)+bd*Real.cos (d+sideSign neg*x)-bw)
    (hDS : 1/2+angularWidth (d-s)≤bsouth+ad*Real.cos (d-s)-bd*Real.sin (d-s)) : False := by
  let v := sideSign neg*x
  let c := sideCenter neg x
  have ht := small_angle_nonneg (r := 2/5) (hr := by norm_num) hxangle
  have wv : angularWidth v=(Real.cos x+Real.sin x)/2 := by
    have hc : 0≤Real.cos x := by linarith [ht.1]
    cases neg <;> simp [v,sideSign,angularWidth,abs_of_nonneg hc,abs_of_nonneg ht.2.1]
  obtain ⟨y,hy,hcenter⟩ := center_face (X := Real.cos s) (Y := beta-Real.sin s)
    (by linarith [south_cos_lower hs]) hy hx
  obtain ⟨upper,rfl⟩ : ∃ upper, y=face upper := by
    rcases hy with rfl | rfl
    exacts [⟨false,rfl⟩,⟨true,rfl⟩]
  have hsum : beta*(1/2+angularWidth v)+(1/2+angularWidth s)+
      mu*(1/2+angularWidth (d+v))+nu*(1/2+angularWidth (d-s))≤
      (beta*Real.cos v*aw+(beta*Real.sin v-mu)*bw)+(asouth+nu*bsouth)+
      diagonalU v s d*ad+diagonalV v s d*bd+(beta-Real.sin s)*cx+Real.cos s*cy := by
    dsimp [beta,mu,nu,diagonalU,diagonalV,v]
    linear_combination (3/5)*hCW+hCS+(2/5)*hWD+(3/10)*hDS
  rw [wv] at hsum
  have hw := west_side_support (v := v) hW (sideCenter_pos neg x)
  have hsu := south_support hS
  have hdu := diagonal_vertex_support hD v s d
  have ws := angularWidth_lower s
  have wq := angularWidth_lower (d+v)
  have wr := angularWidth_lower (d-s)
  have hn : sideProfile neg upper c x s d≤0 := by
    cases neg <;> cases upper <;>
      simp [v,sideSign,sideProfile,beta,mu,nu,A,kappa,coreUpper,face,diagonalU,diagonalV]
        at hsum hw hsu hdu hcenter ws wq wr ⊢ <;>
      nlinarith only [hsum,hw,hsu,hdu,hcenter,ws,wq,wr]
  exact (not_lt_of_ge hn) (side_positive neg upper hxangle hs hd)

/-- If S is separated from C along its own axis, its angle is below `11/25`. -/
theorem own_south_bound {R : ℝ} (P : NormalizedPacking R)
    (hS : P.ownAxis 4=true) : P.deviation 4<11/25 := by
  by_contra! htail
  let X := chart P
  have hedges := wing_separators P
  have hs : 11/25≤X.s ∧ X.s≤2/3 := ⟨htail,south_upper.le⟩
  have hd : 1/2≤X.d ∧ X.d≤11/14 := by
    have h : 1/2<X.d ∧ X.d≤Real.pi/4 := diagonal_range
    constructor <;> linarith [Real.pi_lt_d4]
  have hx : 0≤X.cx ∧ X.cx≤coreUpper := ⟨X.box.1.1,X.box.1.2.trans ceiling_bounds.2.2.2⟩
  have hy : X.cy≤coreUpper := X.box.2.2.trans ceiling_bounds.2.2.2
  have hCS : X.SouthOwn := south_own hS
  have hWD : X.WestWing := west_wing hedges.1
  have hDS : X.SouthWing := south_wing hedges.2
  rw [Chart.WestWing] at hWD
  cases hW : P.ownAxis 2
  · have hw := abs_lt.mp (west_side_angle hW)
    have hCW : X.WestSide := west_side hW
    rw [Chart.WestSide] at hCW
    by_cases hv0 : 0≤X.v
    · exact side_impossible false (x := X.v) ⟨hv0,hw.2.le⟩ hs hd X.west X.south X.diagonal hx hy
        (by simpa [sideSign] using hCW) hCS (by simpa [sideSign] using hWD) hDS
    · exact side_impossible true (x := -X.v) ⟨by linarith,by linarith [hw.1]⟩ hs hd
        X.west X.south X.diagonal hx hy
        (by simpa [sideSign] using hCW) hCS (by simpa [sideSign] using hWD) hDS
  · have hwest := WestTail.own_west_bound P hedges hW
    have hCW : X.WestOwn := west_own hW
    exact own_impossible ⟨(west_own_angle hW).le,by dsimp [X,chart]; linarith⟩ hs hd
      X.west X.south X.diagonal ((normalized_diagonal_transverse_small P).le.trans (by norm_num))
      hx hy hCW hCS hWD hDS

end SquaresInCircles.Six.SouthTail
