import SquaresInCircles.Six.Analytic.CandidateWestTail.Scalar
import SquaresInCircles.Six.Stress.Support

/-!
# Support estimates for the candidate west-tail stress

Two explicit affine radical majorants are proved by completing a square. They
are global in the sine argument. The W/S supports are universal far-vertex
bounds; D uses the independent center-radius bound. No cap branch is selected
or assumed in this argument. The signed central force is retained until its
negative y component and positive x component have been proved.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.CandidateWestTail
open Normalization

def beta : ℝ := 109/200
def gamma : ℝ := 47/250
def mu : ℝ := 169/1000
def nu : ℝ := 49/500
def radiusBound : ℝ := 8443/5000
def rhoBound : ℝ := 55641/50000
def coreUpper : ℝ := 5641/50000
def coreLower : ℝ := 141/1250
def westNormUpper : ℝ := 285301/500000
def southNormUpper : ℝ := 21201/100000
def southSlope : ℝ := -869/10000
def diagonalIntercept : ℝ := 199877/1000000
def diagonalSlope : ℝ := 171/2500

lemma ceiling_bounds : R0 ≤ radiusBound ∧ rho0 ≤ rhoBound ∧
    coreLower ≤ c0 ∧ c0 ≤ coreUpper := by
  have hr : R0 ≤ radiusBound := by
    have hs := R0_sq
    have hn := R0_nonneg
    dsimp [radiusBound]
    norm_num [Q0] at hs
    nlinarith
  have hu : rho0 ≤ rhoBound := by
    have hs := rho0_sq
    dsimp [rhoBound]
    norm_num [Q0] at hs
    nlinarith [rho0_lower]
  have hl : 1391/1250 ≤ rho0 := by
    have hs := rho0_sq
    norm_num [Q0] at hs
    by_contra! h
    have hp := mul_pos (sub_pos.mpr h)
      (show 0 < 1391/1250+rho0+1 by linarith [rho0_lower])
    nlinarith
  exact ⟨hr,hu,by dsimp [coreLower,c0]; linarith,
    by dsimp [coreUpper,c0,rhoBound] at *; linarith⟩

/-- The usual far-vertex support, proved directly in signed side coordinates. -/
lemma local_vertex_support {a b : ℝ} (hc : ContainedChart a |b|) (U V : ℝ) :
    U*a+V*b ≤ R0*Real.sqrt (U^2+V^2)-(|U|+|V|)/2 := by
  have hC := Stress.dot_le_radius (v := (|U|,|V|)) (p := (a+1/2,|b|+1/2))
    R0_nonneg (by simpa only [R0_sq] using hc.containment)
  simp only [Stress.vectorLength,normSq,dot,sq_abs] at hC
  have hA := mul_le_mul_of_nonneg_right (le_abs_self U)
    (show 0 ≤ a by linarith [hc.half_le])
  have hB : V*b ≤ |V|*|b| := by simpa only [abs_mul] using le_abs_self (V*b)
  nlinarith only [hC,hA,hB]

lemma local_vertex_weak {a b : ℝ} (hc : ContainedChart a |b|) (U V : ℝ) :
    U*a+V*b ≤ R0*Real.sqrt (U^2+V^2)-(U+V)/2 := by
  have h := local_vertex_support hc U V
  linarith [le_abs_self U,le_abs_self V]

private lemma west_root : Real.sqrt (beta^2+mu^2) ≤ westNormUpper := by
  have hs := Real.sq_sqrt (show 0 ≤ beta^2+mu^2 by positivity)
  have hn := Real.sqrt_nonneg (beta^2+mu^2)
  dsimp [beta,mu,westNormUpper]
  norm_num [beta,mu] at hs
  nlinarith

/-- The radical majorant is one completed square on the whole sine range. -/
lemma diagonal_root {z : ℝ} (hz : -1 ≤ z ∧ z ≤ 1) :
    Real.sqrt (mu^2+nu^2+2*mu*nu*z) ≤ diagonalIntercept+diagonalSlope*z := by
  have hr : 0 ≤ mu^2+nu^2+2*mu*nu*z := by dsimp [mu,nu]; linarith [hz.1]
  have ha : 0 ≤ diagonalIntercept+diagonalSlope*z := by
    dsimp [diagonalIntercept,diagonalSlope]; linarith [hz.1]
  have hp : mu^2+nu^2+2*mu*nu*z ≤ (diagonalIntercept+diagonalSlope*z)^2 := by
    have hs := sq_nonneg (diagonalSlope*z+diagonalIntercept-(2*mu*nu)/(2*diagonalSlope))
    norm_num [diagonalSlope,diagonalIntercept,mu,nu] at hs ⊢
    nlinarith only [hs]
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (mu^2+nu^2+2*mu*nu*z)
  nlinarith

lemma south_root {z : ℝ} (hz : -1 ≤ z ∧ z ≤ 1) :
    Real.sqrt (gamma^2+nu^2-2*gamma*nu*z) ≤ southNormUpper+southSlope*z := by
  have hr : 0 ≤ gamma^2+nu^2-2*gamma*nu*z := by dsimp [gamma,nu]; linarith [hz.2]
  have ha : 0 ≤ southNormUpper+southSlope*z := by
    dsimp [southNormUpper,southSlope]; linarith [hz.2]
  have hp : gamma^2+nu^2-2*gamma*nu*z ≤ (southNormUpper+southSlope*z)^2 := by
    have hs := sq_nonneg (southSlope*z+southNormUpper-(-2*gamma*nu)/(2*southSlope))
    norm_num [southSlope,southNormUpper,gamma,nu] at hs ⊢
    nlinarith only [hs]
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (gamma^2+nu^2-2*gamma*nu*z)
  nlinarith

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
  norm_num [beta,mu] at h
  dsimp [westUpper,beta,mu] at *
  nlinarith only [h,hp]

lemma south_support (k : Fin 3) {a b s : ℝ} (hc : ContainedChart a |b|) :
    southWork k s a b ≤ southUpper k s := by
  by_cases hk : k=0
  · have h := local_vertex_weak hc gamma nu
    have hr := south_root (z := 0) ⟨by norm_num,by norm_num⟩
    simp only [mul_zero,sub_zero,add_zero] at hr
    have hp := mul_le_mul ceiling_bounds.1 hr (Real.sqrt_nonneg _)
      (by norm_num [radiusBound])
    simp only [southWork,southUpper,if_pos hk]
    nlinarith only [h,hp]
  · have h := local_vertex_weak hc (gamma*Real.cos s) (nu-gamma*Real.sin s)
    have hi : (gamma*Real.cos s)^2+(nu-gamma*Real.sin s)^2=
        gamma^2+nu^2-2*gamma*nu*Real.sin s := by
      linear_combination gamma^2*(Real.sin_sq_add_cos_sq s)
    rw [hi] at h
    have hr := south_root ⟨Real.neg_one_le_sin s,Real.sin_le_one s⟩
    have hp := mul_le_mul ceiling_bounds.1 hr (Real.sqrt_nonneg _)
      (by norm_num [radiusBound])
    simp only [southWork,southUpper,if_neg hk]
    nlinarith only [h,hp]

lemma diagonal_support {a b v s d : ℝ} (hc : ContainedChart a |b|) :
    diagonalU v s d*a+diagonalV v s d*b ≤ diagonalUpper v s := by
  have h := Stress.dot_le_radius (v := (diagonalU v s d,diagonalV v s d))
    (p := (a,b)) (show 0 ≤ rho0 by linarith [rho0_lower]) (chart_center_radius_sq hc)
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
  simp only [dot,Stress.vectorLength,normSq] at h
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
    simp only [centerWork,centerUpper,side,Matrix.cons_val_zero,one_mul,if_pos rfl]
    nlinarith only [hX,hY,hpv,hps]
  · have gx : 0 ≤ beta*Real.cos v := by dsimp [beta]; nlinarith
    have gy : gamma-beta*Real.sin v ≤ 0 := by dsimp [beta,gamma]; nlinarith
    have hX := mul_nonneg (sub_nonneg.mpr hcx) gx
    have hY := mul_nonpos_of_nonneg_of_nonpos hcy gy
    simp only [centerWork,centerUpper,if_neg hk]
    nlinarith only [hX,hY,hpv]

def totalThreshold (v s d : ℝ) : ℝ :=
  beta*(1/2+angularWidth v)+gamma*(1/2+angularWidth s)+
    mu*(1/2+angularWidth (v+d))+nu*(1/2+angularWidth (d-s))

def defect (k : Fin 3) (v s d : ℝ) : ℝ :=
  totalThreshold v s d-centerUpper k v s-westUpper-diagonalUpper v s-southUpper k s

private lemma width_lower (x : ℝ) : (Real.cos x+Real.sin x)/2 ≤ angularWidth x := by
  dsimp [angularWidth]
  linarith [le_abs_self (Real.cos x),le_abs_self (Real.sin x)]

/-- Replacing |sin(d-s)| by sin(d-s) weakens the bound without assuming s<=d. -/
lemma minorant_le_defect (k : Fin 3) (v x d : ℝ) :
    minorant k v x d ≤ defect k v (side k*x) d := by
  have hv := width_lower v
  have hx := width_lower x
  have hq := width_lower (v+d)
  have hu := width_lower (d-side k*x)
  have hs : angularWidth (side k*x)=angularWidth x := by
    fin_cases k <;> simp [side,angularWidth,Real.cos_neg,Real.sin_neg,abs_neg]
  fin_cases k
  all_goals simp only [defect,totalThreshold,hs]
  all_goals norm_num [minorant,centerUpper,westUpper,diagonalUpper,southUpper,
    beta,gamma,mu,nu,radiusBound,rhoBound,coreUpper,coreLower,
    westNormUpper,southNormUpper,southSlope,diagonalIntercept,diagonalSlope,
    offset,gCoeff,hCoeff,side,Real.cos_neg,Real.sin_neg]
  all_goals nlinarith only [hv,hx,hq,hu]

end SquaresInCircles.Six.Analytic.CandidateWestTail
