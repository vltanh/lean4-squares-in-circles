module

public import SquaresInCircles.Six.Wings.Chart

/-!
# Six squares: the west tail

If W–D and D–S are separated along the secondary axes of W and of S, as in the
model, and W is separated from C along its own axis, then `w > -11/25`.
Otherwise `v = -w` lies in `[11/25, 2/3]`, and the separating inequalities of
C–W, C–S, W–D and D–S, with the weights `8/15`, `1/5`, `1/6` and `1/10`,
contradict the supports of the squares. W and S take the far-vertex support;
the centre of D lies within `ρ0` of the origin, and the length of its force, the
square root of an affine function of `sin (v + s)`, is at most the tangent at
`(6/25)²`, as is the length of the force on S on the south side of C, at
`(2/9)²`; the box of the centre of C bounds its work. What remains is a
minorant that is, in each of `v`, `|s|` and `d`, a constant plus a first
harmonic with nonnegative coefficients on the box
`[11/25, 2/3] × [0, 3/5] × [1/2, 11/14]`, so it is positive once it is positive
at the eight corners, where Taylor polynomials bound it below. The corner
`v = 2/3`, `s = 0`, `d = 11/14` is tight: weights of sum `1` leave at most
`5·10⁻⁴` there, and these, after the tangents and the Taylor polynomials,
`3·10⁻⁴`. The index `k` records the separator of S from C: its own axis
(`k = 0`, with `0 < s < 3/5` since `s - w < 24/25`), or the south side of C
with `s ≥ 0` (`k = 1`) or `s ≤ 0` (`k = 2`), with `|s| < 2/5`.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.Six.WestTail
open Normalization Wings

/-! ### The weights and the lengths of the forces

The weights `beta`, `gamma`, `mu` and `nu` on C–W, C–S, W–D and D–S. The force
on W has length at most `westNormUpper`; with `z` the sine of the angle between
the two forces on D, or on S on the south side of C, their lengths are at most
`diagonalIntercept + diagonalSlope z` and `southNormUpper + southSlope z`, the
tangents of the square roots at `(6/25)²` and `(2/9)²`. -/

def beta : ℝ := 8/15
def gamma : ℝ := 1/5
def mu : ℝ := 1/6
def nu : ℝ := 1/10
/-- A ceiling for `√(beta² + mu²) = √281/30`. -/
def westNormUpper : ℝ := 0.5588
def southNormUpper : ℝ := (gamma^2+nu^2+(2/9)^2)/(2*(2/9))
def southSlope : ℝ := -(gamma*nu/(2/9))
def diagonalIntercept : ℝ := (mu^2+nu^2+(6/25)^2)/(2*(6/25))
def diagonalSlope : ℝ := mu*nu/(6/25)

/-! ### The minorant -/

/-- The sign of `s = side k * x` in the three cases for S: separated from C
along its own axis (`k = 0`), or along the south side of C with `s ≥ 0`
(`k = 1`) or `s ≤ 0` (`k = 2`). -/
def side (k : Fin 3) : ℝ := ![1,1,-1] k

/-! In case `k` the angle `x = |s|` lies in `[0, xMax k]`, and the minorant has
the coefficients `gCoeff k` and `hCoeff k` of `cos x` and `sin x`, from the
threshold of C–S, the support of S and the box of C, and the constant
`constantTerm + offset k`. -/

def xMax (k : Fin 3) : ℝ := ![3/5,3/5,2/5] k
def gCoeff (k : Fin 3) : ℝ := ![gamma/2,gamma,gamma] k
def hCoeff (k : Fin 3) : ℝ :=
  ![gamma*(1/2+coreLower),-radiusBound*southSlope,gamma+radiusBound*southSlope] k
def offset (k : Fin 3) : ℝ := ![0,-gamma/2,-gamma/2] k

/-- The halves `beta + gamma + mu + nu` of the thresholds and of the far-vertex
supports of W and S, less the bounds of the works on W, S and D. -/
def constantTerm : ℝ :=
  beta+gamma+mu+nu-radiusBound*(westNormUpper+southNormUpper)-rhoBound*diagonalIntercept

/-- A lower bound for the defect of the stress (`minorant_le_defect`). -/
def minorant (k : Fin 3) (v x d : ℝ) : ℝ :=
  constantTerm+offset k+beta*A*Real.cos v+(beta/2)*Real.sin v+
    gCoeff k*Real.cos x+hCoeff k*Real.sin x+
    (mu/2)*(Real.cos (v+d)+Real.sin (v+d))+
    (nu/2)*(Real.cos (d-side k*x)+Real.sin (d-side k*x))-
    rhoBound*diagonalSlope*Real.sin (v+side k*x)

private lemma trig_x {k : Fin 3} {x : ℝ} (hx : 0 ≤ x ∧ x ≤ xMax k) :
    41/50 ≤ Real.cos x ∧ 0 ≤ Real.sin x ∧ Real.sin x ≤ 3/5 := by
  have h := small_angle_nonneg (r := 3/5)
    ⟨hx.1,hx.2.trans (by fin_cases k <;> norm_num [xMax])⟩ (by norm_num)
  exact ⟨by linarith [h.1],h.2⟩

private lemma trig_d {d : ℝ} (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ Real.cos d ∧ 23/48 ≤ Real.sin d := by
  obtain ⟨hs,-,hc,-⟩ := trig_bracket (by norm_num) (by linarith [Real.pi_gt_d2]) hd
  norm_num at hs hc
  exact ⟨by linarith,by linarith⟩

private def vA (k : Fin 3) (x d : ℝ) : ℝ :=
  beta*A+(mu/2)*(Real.cos d+Real.sin d)-rhoBound*diagonalSlope*side k*Real.sin x
private def vB (x d : ℝ) : ℝ :=
  beta/2+(mu/2)*(Real.cos d-Real.sin d)-rhoBound*diagonalSlope*Real.cos x
private def vK (k : Fin 3) (x d : ℝ) : ℝ :=
  constantTerm+offset k+gCoeff k*Real.cos x+hCoeff k*Real.sin x+
    (nu/2)*(Real.cos (d-side k*x)+Real.sin (d-side k*x))

private def xA (k : Fin 3) (v d : ℝ) : ℝ :=
  gCoeff k+(nu/2)*(Real.cos d+Real.sin d)-rhoBound*diagonalSlope*Real.sin v
private def xB (k : Fin 3) (v d : ℝ) : ℝ :=
  hCoeff k+side k*((nu/2)*(Real.sin d-Real.cos d)-rhoBound*diagonalSlope*Real.cos v)
private def xK (k : Fin 3) (v d : ℝ) : ℝ :=
  constantTerm+offset k+beta*A*Real.cos v+(beta/2)*Real.sin v+
    (mu/2)*(Real.cos (v+d)+Real.sin (v+d))

private def dA (k : Fin 3) (v x : ℝ) : ℝ :=
  (mu/2)*(Real.cos v+Real.sin v)+(nu/2)*(Real.cos x-side k*Real.sin x)
private def dB (k : Fin 3) (v x : ℝ) : ℝ :=
  (mu/2)*(Real.cos v-Real.sin v)+(nu/2)*(Real.cos x+side k*Real.sin x)
private def dK (k : Fin 3) (v x : ℝ) : ℝ :=
  constantTerm+offset k+beta*A*Real.cos v+(beta/2)*Real.sin v+
    gCoeff k*Real.cos x+hCoeff k*Real.sin x-rhoBound*diagonalSlope*Real.sin (v+side k*x)

private lemma v_identity (k : Fin 3) (v x d : ℝ) :
    minorant k v x d=vK k x d+vA k x d*Real.cos v+vB x d*Real.sin v := by
  fin_cases k <;>
    simp [minorant,vK,vA,vB,side,Real.cos_add,Real.sin_add,Real.sin_neg,Real.cos_neg] <;> ring

private lemma x_identity (k : Fin 3) (v x d : ℝ) :
    minorant k v x d=xK k v d+xA k v d*Real.cos x+xB k v d*Real.sin x := by
  fin_cases k <;>
    simp [minorant,xK,xA,xB,side,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
      Real.sin_neg,Real.cos_neg] <;> ring

private lemma d_identity (k : Fin 3) (v x d : ℝ) :
    minorant k v x d=dK k v x+dA k v x*Real.cos d+dB k v x*Real.sin d := by
  fin_cases k <;>
    simp [minorant,dK,dA,dB,side,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
      Real.sin_neg,Real.cos_neg] <;> ring

private lemma v_coefficients (k : Fin 3) {x d : ℝ}
    (hx : 0 ≤ x ∧ x ≤ xMax k) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ vA k x d ∧ 0 ≤ vB x d := by
  have tx := trig_x hx
  have td := trig_d hd
  fin_cases k <;> dsimp [vA,vB,side,beta,A,coreUpper,mu,nu,rhoBound,diagonalSlope] <;>
    constructor <;> nlinarith [Real.sin_le_one x,Real.cos_le_one x,Real.sin_le_one d]

private lemma x_coefficients (k : Fin 3) {v d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hd : 1/2 ≤ d ∧ d ≤ 11/14) :
    0 ≤ xA k v d ∧ 0 ≤ xB k v d := by
  have tv := small_angle_nonneg ⟨by linarith [hv.1],hv.2⟩ (show (2:ℝ)/3 ≤ 3 by norm_num)
  have td := trig_d hd
  fin_cases k <;>
    dsimp [xA,xB,gCoeff,hCoeff,side,gamma,coreLower,radiusBound,southSlope,mu,nu,rhoBound,
      diagonalSlope] <;>
    constructor <;> nlinarith [Real.cos_le_one v,Real.cos_le_one d,Real.sin_le_one d]

private lemma d_coefficients (k : Fin 3) {v x : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k) :
    0 ≤ dA k v x ∧ 0 ≤ dB k v x := by
  have tv := small_angle_nonneg ⟨by linarith [hv.1],hv.2⟩ (show (2:ℝ)/3 ≤ 3 by norm_num)
  have tx := trig_x hx
  fin_cases k <;> dsimp [dA,dB,side,mu,nu] <;> constructor <;> nlinarith

private lemma extend_v (k : Fin 3) {v x d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hleft : 0 < minorant k (11/25) x d) (hright : 0 < minorant k (2/3) x d) :
    0 < minorant k v x d := by
  rw [v_identity] at hleft hright ⊢
  have h := v_coefficients k hx hd
  exact harmonic_pos_of_endpoints h.1 h.2 (by norm_num) (by linarith [Real.pi_gt_d2]) hv hleft hright

private lemma extend_x (k : Fin 3) {v x d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hleft : 0 < minorant k v 0 d) (hright : 0 < minorant k v (xMax k) d) :
    0 < minorant k v x d := by
  rw [x_identity] at hleft hright ⊢
  have h := x_coefficients k hv hd
  have hup : xMax k ≤ Real.pi/2 := by fin_cases k <;> norm_num [xMax] <;> linarith [Real.pi_gt_d2]
  exact harmonic_pos_of_endpoints h.1 h.2 (by norm_num) hup hx hleft hright

private lemma extend_d (k : Fin 3) {v x d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hleft : 0 < minorant k v x (1/2)) (hright : 0 < minorant k v x (11/14)) :
    0 < minorant k v x d := by
  rw [d_identity] at hleft hright ⊢
  have h := d_coefficients k hv hx
  exact harmonic_pos_of_endpoints h.1 h.2 (by norm_num) (by linarith [Real.pi_gt_d2]) hd hleft hright

private def polynomialLower (k : Fin 3) (v x d : ℝ) : ℝ :=
  constantTerm+offset k+beta*A*cosLower v+(beta/2)*sinBelow v+
    gCoeff k*cosLower x+hCoeff k*sinBelow x+
    (mu/2)*(cosLower (v+d)+sinBelow (v+d))+
    (nu/2)*(cosLower (d-side k*x)+sinBelow (d-side k*x))-
    rhoBound*diagonalSlope*sinAbove (v+side k*x)

private lemma polynomial_le (k : Fin 3) (v x d : ℝ) :
    polynomialLower k v x d ≤ minorant k v x d := by
  have cv := cosLower_le v
  have sv := sinBelow_le v
  have cx := cosLower_le x
  have sx := sinBelow_le x
  have cq := cosLower_le (v+d)
  have sq := sinBelow_le (v+d)
  have cr := cosLower_le (d-side k*x)
  have sr := sinBelow_le (d-side k*x)
  have sz := le_sinAbove (v+side k*x)
  have hg : 0 ≤ gCoeff k := by fin_cases k <;> norm_num [gCoeff,gamma]
  have hh : 0 ≤ hCoeff k := by
    fin_cases k <;> norm_num [hCoeff,gamma,nu,coreLower,radiusBound,southSlope]
  have gx := mul_le_mul_of_nonneg_left cx hg
  have hx := mul_le_mul_of_nonneg_left sx hh
  dsimp [polynomialLower,minorant,beta,A,coreUpper,mu,nu,rhoBound,diagonalSlope]
  linarith only [cv,sv,gx,hx,cq,sq,cr,sr,sz]

private def vEnd (i : Fin 2) : ℝ := ![11/25,2/3] i
private def xEnd (k : Fin 3) (i : Fin 2) : ℝ := ![0,xMax k] i
private def dEnd (i : Fin 2) : ℝ := ![1/2,11/14] i

/-- The minorant is positive at the corners of the box. -/
private lemma corners (k : Fin 3) (i j l : Fin 2) :
    0 < minorant k (vEnd i) (xEnd k j) (dEnd l) := by
  have h := polynomial_le k (vEnd i) (xEnd k j) (dEnd l)
  fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals norm_num [polynomialLower,constantTerm,beta,gamma,mu,nu,A,coreUpper,coreLower,
    radiusBound,rhoBound,westNormUpper,southNormUpper,southSlope,diagonalIntercept,
    diagonalSlope,cosLower,sinBelow,sinAbove,gCoeff,hCoeff,offset,side,vEnd,xEnd,xMax,dEnd,
    sinLower,sinUpper] at h ⊢
  all_goals linarith

/-- The minorant is positive on the box: it is concave in each variable and
positive at the corners. -/
theorem positive (k : Fin 3) {v x d : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14) : 0 < minorant k v x d := by
  have hvEnd (i : Fin 2) : 11/25 ≤ vEnd i ∧ vEnd i ≤ 2/3 := by
    fin_cases i <;> norm_num [vEnd]
  have hxEnd (j : Fin 2) : 0 ≤ xEnd k j ∧ xEnd k j ≤ xMax k := by
    fin_cases k <;> fin_cases j <;> norm_num [xEnd,xMax]
  have alongD (i j : Fin 2) : 0 < minorant k (vEnd i) (xEnd k j) d :=
    extend_d k (hvEnd i) (hxEnd j) hd (corners k i j 0) (corners k i j 1)
  have alongX (i : Fin 2) : 0 < minorant k (vEnd i) x d :=
    extend_x k (hvEnd i) hx hd (alongD i 0) (alongD i 1)
  exact extend_v k hv hx hd (alongX 0) (alongX 1)

/-! ### The stress -/

private lemma west_root : Real.sqrt (beta^2+mu^2) ≤ westNormUpper :=
  (Real.sqrt_le_left (by norm_num [westNormUpper])).mpr (by norm_num [beta,mu,westNormUpper])

/-- An affine majorant for the length of the force on D: the tangent of the
square root at `(6/25)²`. -/
lemma diagonal_root {z : ℝ} (hz : -1 ≤ z ∧ z ≤ 1) :
    Real.sqrt (mu^2+nu^2+2*mu*nu*z) ≤ diagonalIntercept+diagonalSlope*z := by
  have h := sqrt_le_tangent (c := 6/25) (by norm_num)
    (show 0 ≤ mu^2+nu^2+2*mu*nu*z by dsimp [mu,nu]; linarith [hz.1])
  convert h using 1
  dsimp [diagonalIntercept,diagonalSlope]
  ring

/-- The same for the force on S on the south side of C, at `(2/9)²`. -/
lemma south_root {z : ℝ} (hz : -1 ≤ z ∧ z ≤ 1) :
    Real.sqrt (gamma^2+nu^2-2*gamma*nu*z) ≤ southNormUpper+southSlope*z := by
  have h := sqrt_le_tangent (c := 2/9) (by norm_num)
    (show 0 ≤ gamma^2+nu^2-2*gamma*nu*z by dsimp [gamma,nu]; linarith [hz.2])
  convert h using 1
  dsimp [southNormUpper,southSlope]
  ring

/-! The works `southWork` and `centerWork` of the forces on S and on C, the
force `(diagonalU, diagonalV)` on D, and the bounds `westUpper`, `southUpper`,
`diagonalUpper` and `centerUpper` for the works on W, S, D and C. -/

def westUpper : ℝ := radiusBound*westNormUpper-(beta+mu)/2

def southWork (k : Fin 3) (s a b : ℝ) : ℝ :=
  if k=0 then gamma*a+nu*b else gamma*Real.cos s*a+(nu-gamma*Real.sin s)*b

def southUpper (k : Fin 3) (s : ℝ) : ℝ :=
  if k=0 then radiusBound*southNormUpper-(gamma+nu)/2
  else radiusBound*(southNormUpper+southSlope*Real.sin s)-
    (gamma*Real.cos s+nu-gamma*Real.sin s)/2

def diagonalU (v s d : ℝ) : ℝ := mu*Real.sin (v+d)+nu*Real.cos (d-s)
def diagonalV (v s d : ℝ) : ℝ := mu*Real.cos (v+d)-nu*Real.sin (d-s)
def diagonalUpper (v s : ℝ) : ℝ := rhoBound*(diagonalIntercept+diagonalSlope*Real.sin (v+s))

def centerWork (k : Fin 3) (v s cx cy : ℝ) : ℝ :=
  beta*(cx*Real.cos v-cy*Real.sin v)+
    (if k=0 then gamma*(-cx*Real.sin s+cy*Real.cos s) else gamma*cy)

def centerUpper (k : Fin 3) (v s : ℝ) : ℝ :=
  beta*coreUpper*Real.cos v-(if k=0 then gamma*coreLower*Real.sin s else 0)

lemma west_support {a b : ℝ} (hc : ContainedChart a |b|) : beta*a-mu*b ≤ westUpper := by
  have h := local_vertex_support hc beta (-mu)
  have hp := mul_le_mul ceiling_bounds.1 west_root (Real.sqrt_nonneg _)
    (by norm_num [radiusBound])
  rw [neg_sq,abs_neg,abs_of_pos (show (0:ℝ) < beta by norm_num [beta]),
    abs_of_pos (show (0:ℝ) < mu by norm_num [mu])] at h
  dsimp [westUpper]
  linarith only [h,hp]

lemma south_support (k : Fin 3) {a b s : ℝ} (hc : ContainedChart a |b|) :
    southWork k s a b ≤ southUpper k s := by
  by_cases hk : k=0
  · have h := local_vertex_support hc gamma nu
    have hr := south_root (z := 0) ⟨by norm_num,by norm_num⟩
    simp only [mul_zero,sub_zero,add_zero] at hr
    have hp := mul_le_mul ceiling_bounds.1 hr (Real.sqrt_nonneg _)
      (by norm_num [radiusBound])
    simp only [southWork,southUpper,ite_eq_left hk]
    nlinarith only [h,hp,le_abs_self gamma,le_abs_self nu]
  · have h := local_vertex_support hc (gamma*Real.cos s) (nu-gamma*Real.sin s)
    have hi : (gamma*Real.cos s)^2+(nu-gamma*Real.sin s)^2=
        gamma^2+nu^2-2*gamma*nu*Real.sin s := by
      linear_combination gamma^2*(Real.sin_sq_add_cos_sq s)
    rw [hi] at h
    have hr := south_root ⟨Real.neg_one_le_sin s,Real.sin_le_one s⟩
    have hp := mul_le_mul ceiling_bounds.1 hr (Real.sqrt_nonneg _)
      (by norm_num [radiusBound])
    simp only [southWork,southUpper,ite_eq_right hk]
    nlinarith only [h,hp,le_abs_self (gamma*Real.cos s),le_abs_self (nu-gamma*Real.sin s)]

lemma diagonal_support {a b v s d : ℝ} (hc : ContainedChart a |b|) :
    diagonalU v s d*a+diagonalV v s d*b ≤ diagonalUpper v s := by
  have h := dot_le_radius (v := (diagonalU v s d,diagonalV v s d))
    (p := (a,b)) (show 0 ≤ rho0 by linarith [rho0_bounds.1]) hc.center_sq_le
  have hi : (diagonalU v s d)^2+(diagonalV v s d)^2=
      mu^2+nu^2+2*mu*nu*Real.sin (v+s) := by
    have ht : Real.sin (v+s)=Real.sin (v+d)*Real.cos (d-s)-
        Real.cos (v+d)*Real.sin (d-s) := by
      rw [← Real.sin_sub]
      congr 1
      ring
    dsimp [diagonalU,diagonalV]
    rw [ht]
    linear_combination mu^2*(Real.sin_sq_add_cos_sq (v+d))+
      nu^2*(Real.sin_sq_add_cos_sq (d-s))
  simp only [dot,vectorLength,normSq] at h
  rw [hi] at h
  have hr := diagonal_root ⟨Real.neg_one_le_sin (v+s),Real.sin_le_one (v+s)⟩
  have hp := mul_le_mul ceiling_bounds.2.1 hr (Real.sqrt_nonneg _)
    (by norm_num [rhoBound])
  exact h.trans hp

lemma center_support (k : Fin 3) {v x cx cy : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hcx : cx ≤ c0) (hcy : 0 ≤ cy) :
    centerWork k v (side k*x) cx cy ≤ centerUpper k v (side k*x) := by
  have hmax : xMax k ≤ 3/5 := by fin_cases k <;> norm_num [xMax]
  have hx1 : x ≤ 3/5 := hx.2.trans hmax
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hv2 : v^2 ≤ 4/9 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.2)
      (show 0 ≤ (2:ℝ)/3+v by linarith)]
  have hv3 := mul_le_mul_of_nonneg_right hv2 hv0
  have hcv : 7/9 ≤ Real.cos v := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have hsv : 2/5 ≤ Real.sin v := by nlinarith [Real.sin_ge_sub_cube hv0]
  have hsx : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx1,Real.pi_gt_d2])
  have hsu : Real.sin x ≤ 3/5 := (Real.sin_le hx.1).trans hx1
  have hpv := mul_nonneg (show 0 ≤ coreUpper-c0 by linarith [ceiling_bounds.2.2.2])
    (show 0 ≤ beta*Real.cos v by dsimp [beta]; nlinarith)
  by_cases hk : k=0
  · subst k
    have gx : 0 ≤ beta*Real.cos v-gamma*Real.sin x := by dsimp [beta,gamma]; nlinarith
    have gy : gamma*Real.cos x-beta*Real.sin v ≤ 0 := by
      dsimp [beta,gamma]
      nlinarith [Real.cos_le_one x]
    have hX := mul_nonneg (sub_nonneg.mpr hcx) gx
    have hY := mul_nonpos_of_nonneg_of_nonpos hcy gy
    have hps := mul_nonneg
      (show 0 ≤ c0-coreLower by linarith [ceiling_bounds.2.2.1])
      (show 0 ≤ gamma*Real.sin x by dsimp [gamma]; positivity)
    simp only [centerWork,centerUpper,side,Matrix.cons_val_zero,one_mul,↓reduceIte]
    nlinarith only [hX,hY,hpv,hps]
  · have gx : 0 ≤ beta*Real.cos v := by dsimp [beta]; nlinarith
    have gy : gamma-beta*Real.sin v ≤ 0 := by dsimp [beta,gamma]; nlinarith
    have hX := mul_nonneg (sub_nonneg.mpr hcx) gx
    have hY := mul_nonpos_of_nonneg_of_nonpos hcy gy
    simp only [centerWork,centerUpper,ite_eq_right hk]
    nlinarith only [hX,hY,hpv]

/-- The weighted sum of the thresholds of C–W, C–S, W–D and D–S. -/
def totalThreshold (v s d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+gamma*(1/2+angularWidth s)+
    mu*(1/2+angularWidth (v+d))+nu*(1/2+angularWidth (d-s))

/-- The threshold sum less the bounds for the works: nonpositive for a packing,
positive by the minorant. -/
def defect (k : Fin 3) (v s d : ℝ) : ℝ :=
  totalThreshold v s d-centerUpper k v s-westUpper-diagonalUpper v s-southUpper k s

/-- The minorant is at most the defect, as
`angularWidth x ≥ (cos x + sin x)/2`. -/
lemma minorant_le_defect (k : Fin 3) (v x d : ℝ) :
    minorant k v x d ≤ defect k v (side k*x) d := by
  have hv := angularWidth_lower v
  have hx := angularWidth_lower x
  have hq := angularWidth_lower (v+d)
  have hu := angularWidth_lower (d-side k*x)
  have hs : angularWidth (side k*x)=angularWidth x := by
    fin_cases k <;> simp [side,angularWidth,Real.cos_neg,Real.sin_neg,abs_neg]
  fin_cases k
  all_goals simp only [defect,totalThreshold,hs]
  all_goals norm_num [minorant,constantTerm,centerUpper,westUpper,diagonalUpper,southUpper,
    beta,gamma,mu,nu,A,radiusBound,rhoBound,coreUpper,coreLower,
    westNormUpper,southNormUpper,southSlope,diagonalIntercept,diagonalSlope,
    offset,gCoeff,hCoeff,side,Real.cos_neg,Real.sin_neg] at hu ⊢
  all_goals nlinarith only [hv,hx,hq,hu]

/-! ### The west tail -/

/-- For `11/25 ≤ v ≤ 2/3`, the four separating inequalities, in the coordinates
of the squares, are inconsistent. -/
theorem scalar_impossible (k : Fin 3) {v x d aw bw ad bd asouth bsouth cx cy : ℝ}
    (hv : 11/25 ≤ v ∧ v ≤ 2/3) (hx : 0 ≤ x ∧ x ≤ xMax k)
    (hd : 1/2 ≤ d ∧ d ≤ 11/14)
    (hW : ContainedChart aw |bw|) (hD : ContainedChart ad |bd|)
    (hS : ContainedChart asouth |bsouth|) (hcx : cx ≤ c0) (hcy : 0 ≤ cy)
    (hCW : 1/2+angularWidth v ≤ aw+cx*Real.cos v-cy*Real.sin v)
    (hCS : 1/2+angularWidth (side k*x) ≤
      if k=0 then asouth-cx*Real.sin (side k*x)+cy*Real.cos (side k*x)
      else asouth*Real.cos (side k*x)-bsouth*Real.sin (side k*x)+cy)
    (hWD : 1/2+angularWidth (v+d) ≤
      ad*Real.sin (v+d)+bd*Real.cos (v+d)-bw)
    (hDS : 1/2+angularWidth (d-side k*x) ≤
      bsouth+ad*Real.cos (d-side k*x)-bd*Real.sin (d-side k*x)) : False := by
  have hsum : totalThreshold v (side k*x) d ≤
      (beta*aw-mu*bw)+
      (diagonalU v (side k*x) d*ad+diagonalV v (side k*x) d*bd)+
      southWork k (side k*x) asouth bsouth+centerWork k v (side k*x) cx cy := by
    by_cases hk : k=0
    · simp only [ite_eq_left hk] at hCS
      simp only [totalThreshold,diagonalU,diagonalV,southWork,centerWork,ite_eq_left hk]
      dsimp [beta,gamma,mu,nu]
      linear_combination (8/15)*hCW+(1/5)*hCS+(1/6)*hWD+(1/10)*hDS
    · simp only [ite_eq_right hk] at hCS
      simp only [totalThreshold,diagonalU,diagonalV,southWork,centerWork,ite_eq_right hk]
      dsimp [beta,gamma,mu,nu]
      linear_combination (8/15)*hCW+(1/5)*hCS+(1/6)*hWD+(1/10)*hDS
  have hw := west_support hW
  have hs := south_support k (s := side k*x) hS
  have hd' := diagonal_support (v := v) (s := side k*x) (d := d) hD
  have hc := center_support k hv hx hcx hcy
  have hnonpos : defect k v (side k*x) d ≤ 0 := by
    dsimp [defect]
    linarith only [hsum,hw,hs,hd',hc]
  have hpositive := (positive k hv hx hd).trans_le (minorant_le_defect k v x d)
  linarith

/-- If W–D and D–S are separated as in the model and W is separated from C
along its own axis, then `w > -11/25`. -/
theorem own_west_bound {R : ℝ} (P : NormalizedPacking R)
    (hedges : WingSeparators P) (hW : P.ownAxis 2=true) :
    -11/25 < P.deviation 2 := by
  by_contra! htail
  let X := chart P
  have hv : 11/25 ≤ X.v ∧ X.v ≤ 2/3 := ⟨by dsimp [X,chart]; linarith,west_upper.le⟩
  have hd : 1/2 ≤ X.d ∧ X.d ≤ 11/14 := by
    have h : 1/2 < X.d ∧ X.d ≤ Real.pi/4 := diagonal_range
    constructor <;> linarith [Real.pi_lt_d4]
  have hCW : X.WestOwn := west_own hW
  have hWD : X.WestWing := west_wing hedges.1
  have hDS : X.SouthWing := south_wing hedges.2
  rw [Chart.WestWing,add_comm X.d X.v] at hWD
  rw [Chart.SouthWing] at hDS
  have finish (k : Fin 3) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ xMax k) (hxid : X.s=side k*x)
      (hCS : 1/2+angularWidth X.s ≤
        if k=0 then X.aS-X.cx*Real.sin X.s+X.cy*Real.cos X.s
        else X.aS*Real.cos X.s-X.bS*Real.sin X.s+X.cy) : False := by
    apply scalar_impossible k hv hx hd X.west X.diagonal X.south X.box.1.2 X.box.2.1 hCW
    · simpa only [← hxid] using hCS
    · exact hWD
    · simpa only [← hxid] using hDS
  cases hS : P.ownAxis 4
  · have hs := abs_lt.mp (south_side_angle hS)
    have hCS : X.SouthSide := south_side hS
    rw [Chart.SouthSide] at hCS
    by_cases hs0 : 0 ≤ X.s
    · apply finish 1 X.s
      · norm_num [xMax]
        exact ⟨hs0,by linarith [hs.2]⟩
      · norm_num [side]
      · simpa using hCS
    · apply finish 2 (-X.s)
      · norm_num [xMax]
        constructor <;> linarith [hs.1]
      · norm_num [side]
      · simpa using hCS
  · have hs0 : 0 < X.s := south_own_angle hS
    have hsum := own_angle_sum hW hS
    have hCS : X.SouthOwn := south_own hS
    rw [Chart.SouthOwn] at hCS
    apply finish 0 X.s
    · simpa [xMax] using And.intro hs0.le (show X.s ≤ 3/5 by linarith)
    · norm_num [side]
    · simpa using hCS

end SquaresInCircles.Six.WestTail
