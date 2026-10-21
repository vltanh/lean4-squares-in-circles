module

public import SquaresInCircles.Eight.TableFree.SecondMixedNegativeSourceThreeData
public import SquaresInCircles.Eight.TableFree.CentralSegment
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeThreeReferenceAlgebra
public import SquaresInCircles.Eight.Arithmetic.Arctangent

/-!
# Exact angle minimization for the negative-core side contact

Completing the source quadratic leaves a positive sinusoid. Its phase
is proved to remain in the first quadrant at every feasible original
contact, and a zero-curvature tangent gives its exact angle minimum.
The two rational slopes used later share the same physical target arc.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)
open PositiveThree (Lower lowerAngle lower_trig)

def targets : Set ℝ := Icc 0 (27/50)
def slopes : Set ℝ := Icc (39/40) g
def P (B : ℝ) : ℝ := U B-1
def V (B : ℝ) : ℝ := B+1/2
def T (B : ℝ) : ℝ := Q0+1-2*U B
def S (h B : ℝ) : ℝ := Real.sqrt (h^2*T B-1)
def beta (B : ℝ) : ℝ := Real.arctan (V B/P B)
def epsilon (h : ℝ) : ℝ := (g-h)^2/(4*z)
def E (h B : ℝ) : ℝ := beta B+Real.arctan (S h B)-S h B-e-epsilon h+h/2-L B

def baseE (u : ℝ) : ℝ := 2*u^2-4*Q0*u+Q0*(Q0+1)
def baseEd (u : ℝ) : ℝ := 4*u-4*Q0
def A0 (u : ℝ) : ℝ := baseE u*u^2*(Q0+1-2*u)-
  (Q0-u^2)*(baseEd u*u*(Q0+1-2*u)-baseE u*(3*(Q0+1-2*u)-4*u))
def D0 (u : ℝ) : ℝ := u^5*(Q0+1-2*u)^3-A0 u
def Ch (h u : ℝ) : ℝ :=
  let t := Q0+1-2*u
  let w := Q0-u^2
  let s := h^2*t-1
  3*h^2*Q0*u*t^2*s-h^4*w*u^2*t^2-4*h^2*w*u^2*t*s+
    3*Q0*t^2*s^2-6*Q0*u*t*s^2+8*w*u^2*s^2

def betaD (B : ℝ) : ℝ := (Q0-U B)/(U B*T B)
def betaDD (B : ℝ) : ℝ := baseE (U B)*V B/((U B)^3*(T B)^2)
def betaDDD (B : ℝ) : ℝ := A0 (U B)/((U B)^5*(T B)^3)
def R (h B : ℝ) : ℝ := ratio B*S h B/T B
def RD (h B : ℝ) : ℝ := ratioD B*S h B/T B+
  h^2*(ratio B)^2/(S h B*T B)-2*(ratio B)^2*S h B/(T B)^2
def RDD (h B : ℝ) : ℝ := ratioDD B*S h B/T B+
  3*h^2*ratio B*ratioD B/(S h B*T B)-h^4*(ratio B)^3/((S h B)^3*T B)-
  6*ratio B*ratioD B*S h B/(T B)^2-
  4*h^2*(ratio B)^3/(S h B*(T B)^2)+8*(ratio B)^3*S h B/(T B)^3
def E1 (h B : ℝ) : ℝ := betaD B-R h B-LLabel.d1 B
def E2 (h B : ℝ) : ℝ := betaDD B-RD h B-LLabel.d2 B
def E3 (h B : ℝ) : ℝ := betaDDD B-RDD h B-LLabel.d3 B

lemma target_domain {B : ℝ} (hB : B∈targets) : B∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem ⟨hB.1,by dsimp [targets] at hB; linarith [hB.2]⟩

lemma U_bounds {B : ℝ} (hB : B∈targets) : (42/25:ℝ)<U B ∧ U B<(383/200:ℝ) := by
  have hd := target_domain hB
  have ht := ShortOuterOne.SameContact.arc_state hd
  have hu := U_positive (outer_domain hd)
  have hq := UW_circle (outer_domain hd)
  have hv2 := pow_le_pow_left₀ (show 0≤B+1/2 by linarith [hB.1])
    (show B+1/2≤26/25 by dsimp [targets] at hB; linarith [hB.2]) 2
  have ha := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  dsimp [W] at hq
  norm_num [Q0] at hq
  constructor
  · by_contra hn
    have hup : U B≤42/25 := le_of_not_gt hn
    have hu2 := pow_le_pow_left₀ hu.le hup 2
    nlinarith
  · dsimp [U]
    linarith

lemma P_positive {B : ℝ} (hB : B∈targets) : 0<P B := by
  dsimp [P]
  linarith [(U_bounds hB).1]

lemma T_bounds {B : ℝ} (hB : B∈targets) : (1357/1250:ℝ)<T B ∧ T B<(3889/2500:ℝ) := by
  have hu := U_bounds hB
  dsimp [T,Q0]
  constructor <;> linarith

lemma S_positive {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) : 0<S h B := by
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤39/40) hh.1 2
  have hp := mul_le_mul (show (1521/1600:ℝ)≤h^2 by norm_num at hsq ⊢; exact hsq)
    (T_bounds hB).1.le (by norm_num) (sq_nonneg h)
  apply Real.sqrt_pos.mpr
  nlinarith

lemma S_sq {h B : ℝ} (hh : h∈slopes) (hB : B∈targets) :
    (S h B)^2=h^2*T B-1 := by
  have hp := S_positive hh hB
  exact Real.sq_sqrt ((Real.sqrt_pos.mp hp).le)

lemma circle_phase {B : ℝ} (hB : B∈targets) : (P B)^2+(V B)^2=T B := by
  have hq := UW_circle (outer_domain (target_domain hB))
  dsimp [P,V,T,W] at *
  nlinarith

lemma angle_lower {h B φ : ℝ} (hh : h∈slopes) (hB : B∈targets)
    (hφ : Lower φ) (hb : 0≤contact B φ) : E h B≤C B φ := by
  let ρ : ℝ := Real.sqrt (T B)
  let α : ℝ := Real.arctan (S h B)
  let θ : ℝ := φ-beta B
  have hρ : 0<ρ := Real.sqrt_pos.mpr (by linarith [(T_bounds hB).1])
  have hρ2 : ρ^2=T B := Real.sq_sqrt (by linarith [(T_bounds hB).1])
  have hS := S_positive hh hB
  have hs2 := S_sq hh hB
  have hh0 : 0<h := by linarith [hh.1]
  have hV : 0<V B := by dsimp [V]; linarith [hB.1]
  have hframe := CentralForbidden.atan_frame (P_positive hB) hV.le
  rw [circle_phase hB] at hframe
  change ρ*Real.cos (beta B)=P B ∧ ρ*Real.sin (beta B)=V B at hframe
  have hβ : beta B∈Icc (0:ℝ) (Real.pi/2) :=
    ⟨Real.arctan_nonneg.mpr (div_nonneg hV.le (P_positive hB).le),
      (Real.arctan_lt_pi_div_two _).le⟩
  have hφ0 : 0≤φ := by dsimp [Lower,lowerAngle] at hφ; linarith [hφ.1,pi_hand_enclosure.1]
  let q : ℝ→ℝ := fun x => P B*Real.sin x-V B*Real.cos x
  have hq (x : ℝ) : HasDerivAt q (P B*Real.cos x+V B*Real.sin x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul (P B)).sub
      ((Real.hasDerivAt_cos x).const_mul (V B)) using 1 <;> dsimp [q] <;> ring
  have hmono : MonotoneOn q (Icc (0:ℝ) (Real.pi/2)) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x _ => (hq x).continuousAt.continuousWithinAt) (fun x _ => hq x)
    intro x hx
    exact add_nonneg
      (mul_nonneg (P_positive hB).le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2.le⟩))
      (mul_nonneg hV.le (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2,Real.pi_pos])))
  have hqβ : q (beta B)=0 := by
    have he : ρ*q (beta B)=0 := by
      dsimp [q]
      linear_combination P B*hframe.2-V B*hframe.1
    nlinarith
  have hqφ : 0<q φ := by dsimp [q,P,V,U,contact] at *; linarith
  have hθ0 : 0≤θ := by
    by_contra hn
    have hle : φ≤beta B := by dsimp [θ] at hn; linarith
    have he := hmono ⟨hφ0,hφ.2⟩ hβ hle
    rw [hqβ] at he
    linarith
  have hθhi : θ≤Real.pi/2 := by dsimp [θ]; linarith [hφ.2,hβ.1]
  have hα : α∈Icc (0:ℝ) (Real.pi/2) :=
    ⟨Real.arctan_nonneg.mpr hS.le,(Real.arctan_lt_pi_div_two _).le⟩
  have hroot : Real.sqrt (1+(S h B)^2)=h*ρ := by
    have hr := Real.sqrt_nonneg (1+(S h B)^2)
    have hr2 := Real.sq_sqrt (show 0≤1+(S h B)^2 by positivity)
    have hp := mul_pos hh0 hρ
    nlinarith [congrArg (fun x : ℝ => h^2*x) hρ2]
  have hαframe := CentralForbidden.atan_frame (show (0:ℝ)<1 by norm_num) hS.le
  norm_num only [one_pow,div_one] at hαframe
  rw [hroot] at hαframe
  change h*ρ*Real.cos α=1 ∧ h*ρ*Real.sin α=S h B at hαframe
  have hf (x : ℝ) : HasDerivAt (fun y => y-h*ρ*Real.sin y) (1-h*ρ*Real.cos x) x := by
    convert (hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).const_mul (h*ρ)) using 1 <;> ring
  have hd (x : ℝ) : HasDerivAt (fun y => 1-h*ρ*Real.cos y) (h*ρ*Real.sin x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul (h*ρ)).const_sub 1 using 1 <;> ring
  have ht := curvature_tangent (κ := (0:ℝ)) (f := fun y => y-h*ρ*Real.sin y)
    (d := fun y => 1-h*ρ*Real.cos y) (dd := fun y => h*ρ*Real.sin y)
    (show θ∈Icc (0:ℝ) (Real.pi/2) from ⟨hθ0,hθhi⟩) hα
    (fun x _ => hf x) (fun x _ => hd x)
    (fun x hx => mul_nonneg (mul_nonneg hh0.le hρ.le)
      (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])))
  have hrotation : ρ*Real.sin θ=q φ := by
    dsimp [θ,q]
    rw [Real.sin_sub]
    linear_combination Real.sin φ*hframe.1-Real.cos φ*hframe.2
  have hmin : beta B+Real.arctan (S h B)-S h B≤φ-h*q φ := by
    rw [hαframe.1,hαframe.2] at ht
    dsimp [α,θ] at ht
    nlinarith [congrArg (fun x : ℝ => h*x) hrotation]
  have hsq := mul_nonneg (by norm_num [z,EdgeThreeAligned.zn] : 0≤z)
    (sq_nonneg (contact B φ-(g-h)/(2*z)))
  have hquad : -h*contact B φ-epsilon h≤-g*contact B φ+z*(contact B φ)^2 := by
    dsimp [epsilon,z,EdgeThreeAligned.zn] at *
    nlinarith
  have hqcontact : q φ=contact B φ+1/2 := by dsimp [q,P,V,U,contact]; ring
  rw [hqcontact] at hmin
  dsimp [E,C,sideValue,EdgeThreeAligned.negativeSideCost,EdgeThreeAligned.sideH]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedThree.NegativeSource.Minimum
