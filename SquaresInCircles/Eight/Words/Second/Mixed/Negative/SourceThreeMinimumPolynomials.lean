module

public import SquaresInCircles.Eight.Arithmetic.PolynomialCertificates
public import SquaresInCircles.Eight.Words.Second.Mixed.Edge.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeUpperEasy

/-!
# Eight squares: whole-height polynomial signs for the negative-core minimum

The degree-eight denominator difference and the two stationary numerators, of degree six, have
positive Bernstein coefficients on [1.68,1.915] (the second numerator on [1.68,1.74]). Each input
is the displayed symbolic polynomial. No target subdivision, sampled
values, or supplied coefficient table is used.
-/

section
/-!
## The original negative-core transverse contact

On the lower angle half every feasible transverse source lies strictly
on the straight core side. Increasing its coordinate to contact stays
on that same side and only decreases the cost. These facts retain the
original target and both weak endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open PositiveThree (Lower lowerAngle lower_trig)

abbrev g := EdgeThreeAligned.gn
abbrev z := EdgeThreeAligned.zn
abbrev e := EdgeThreeAligned.en
abbrev γ := EdgeThreeAligned.threshold
abbrev value := EdgeThreeAligned.negativeCost
abbrev sideValue := EdgeThreeAligned.negativeSideCost

def contact (B φ : ℝ) : ℝ :=
  (arc B-1/2)*Real.sin φ-(B+1/2)*Real.cos φ-1/2
def contactD (B φ : ℝ) : ℝ :=
  (arc B-1/2)*Real.cos φ+(B+1/2)*Real.sin φ
def C (B φ : ℝ) : ℝ := sideValue (contact B φ) B φ
def CD (B φ : ℝ) : ℝ := 1-(g-2*z*contact B φ)*contactD B φ
def CDD (B φ : ℝ) : ℝ :=
  2*z*(contactD B φ)^2+(g-2*z*contact B φ)*(contact B φ+1/2)

lemma contact_hasDerivAt (B φ : ℝ) :
    HasDerivAt (contact B) (contactD B φ) φ := by
  have h := (((Real.hasDerivAt_sin φ).const_mul (arc B-1/2)).sub
    ((Real.hasDerivAt_cos φ).const_mul (B+1/2))).sub_const (1/2)
  exact h.congr_deriv (by simp only [contactD]; ring)

lemma contactD_hasDerivAt (B φ : ℝ) :
    HasDerivAt (contactD B) (-(contact B φ+1/2)) φ := by
  have h := ((Real.hasDerivAt_cos φ).const_mul (arc B-1/2)).add
    ((Real.hasDerivAt_sin φ).const_mul (B+1/2))
  exact h.congr_deriv (by simp only [contact]; ring)

lemma C_hasDerivAt (B φ : ℝ) : HasDerivAt (C B) (CD B φ) φ := by
  have h := ((hasDerivAt_id φ).sub
    ((((contact_hasDerivAt B φ).const_mul g).const_add e).sub
      (((contact_hasDerivAt B φ).pow 2).const_mul z))).sub_const (L B)
  exact h.congr_deriv (by simp only [CD]; push_cast; ring)

lemma CD_hasDerivAt (B φ : ℝ) : HasDerivAt (CD B) (CDD B φ) φ := by
  have h := ((((contact_hasDerivAt B φ).const_mul (2*z)).const_sub g).mul
    (contactD_hasDerivAt B φ)).const_sub 1
  exact h.congr_deriv (by simp only [CDD]; ring)

lemma contact_upper {A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ) :
    contact B φ≤A-1 := by
  have htr := lower_trig hφ
  have ha : (89/100:ℝ)<A := outer_endpoint_bounds.2.2.1.trans_le (outer_bounds ht).1
  have hp := mul_nonneg (show 0≤A-1/2 by linarith) (sub_nonneg.mpr htr.2.1)
  have hq := mul_nonneg (show 0≤B+1/2 by linarith [ht.1]) htr.2.2.1
  dsimp [contact]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  nlinarith

lemma contactD_positive {A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ) :
    0<contactD B φ := by
  have htr := lower_trig hφ
  have ha : (89/100:ℝ)<A := outer_endpoint_bounds.2.2.1.trans_le (outer_bounds ht).1
  have hp := mul_nonneg (show 0≤A-1/2 by linarith) htr.2.2.1
  have hq := mul_pos (show 0<B+1/2 by linarith [ht.1]) (show 0<Real.sin φ by linarith [htr.1])
  dsimp [contactD]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma contact_monotone {A B : ℝ} (ht : OuterState A B) :
    MonotoneOn (contact B) (Icc lowerAngle (Real.pi/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun φ _ => (contact_hasDerivAt B φ).continuousAt.continuousWithinAt)
    (fun φ _ => contact_hasDerivAt B φ)
    (fun _ hφ => (contactD_positive ht (Ioo_subset_Icc_self hφ)).le)

lemma original_contact {a b A B φ : ℝ} (hs : CoreState a b)
    (ht : OuterState A B) (hφ : Lower φ)
    (hsep : (1+Real.sin φ+Real.cos φ)/2≤-b+A*Real.sin φ-B*Real.cos φ) :
    a=7/12 ∧ 0≤contact B φ ∧ contact B φ<(83/200:ℝ) ∧
      1≤A ∧ C B φ≤value a b B φ := by
  have hb := (CoreAngleEndpoint.state_bounds hs).2.2.1
  have hA := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hbc : b≤contact B φ := by
    dsimp [contact]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hupper := contact_upper ht hφ
  have hside : b<1/2 := by linarith
  have ha := (CommonQuarter.core_small_side hs hside).1
  have hmono := EdgeThreeAligned.sideH_mono hb (by linarith : contact B φ≤1/2) hbc
  refine ⟨ha,by linarith,by linarith,by linarith,?_⟩
  dsimp [C,sideValue,value,EdgeThreeAligned.negativeSideCost,EdgeThreeAligned.negativeCost]
  rw [ha,EdgeThreeAligned.sideH_eq]
  linarith

lemma contact_aligned {A B : ℝ} (ht : OuterState A B) :
    contact B (Real.pi/2)=A-1 := by
  norm_num [contact,(ShortOuterOne.SameContact.actual_arc ht).1]
  ring

lemma aligned_lower {A B : ℝ} (ht : OuterState A B) (hA : 1≤A) :
    γ<C B (Real.pi/2) := by
  have hh := EdgeThreeAligned.negative_side_aligned (b := A-1) ht (by linarith) (by linarith)
  rw [C,contact_aligned ht]
  dsimp [γ,EdgeThreeAligned.threshold]
  linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource
end
end
end

section
/-!
## The complete large-target negative-core transverse family

The physical source contact increases continuously to alignment. Its
cost has increasing angle derivative, and that derivative is already
negative at alignment when B≥.54. There is therefore no intermediate
exit.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.High
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (Lower lowerAngle lower_trig)

lemma aligned_slope {A B : ℝ} (ht : OuterState A B) (hB : (27/50:ℝ)≤B) :
    CD B (Real.pi/2)<0 := by
  have hA : A<(148/125:ℝ) := by
    by_contra hn
    have ha : 148/125≤A := le_of_not_gt hn
    have ha2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤421/250)
      (show (421/250:ℝ)≤A+1/2 by linarith) 2
    have hb2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤26/25)
      (show (26/25:ℝ)≤B+1/2 by linarith) 2
    have hq := ht.2.2
    norm_num [Q0] at hq
    nlinarith
  have hc : (241/250:ℝ)<g-2*z*(A-1) := by
    dsimp [g,z,EdgeThreeAligned.gn,EdgeThreeAligned.zn]
    linarith
  have hp := mul_le_mul (show (241/250:ℝ)≤g-2*z*(A-1) by linarith)
    (show (26/25:ℝ)≤B+1/2 by linarith) (by norm_num)
    (show 0≤g-2*z*(A-1) by linarith)
  norm_num [CD,contactD,contact_aligned ht] at *
  nlinarith

theorem lower {A B φ : ℝ} (ht : OuterState A B) (hB : (27/50:ℝ)≤B)
    (hφ : Lower φ) (hb : 0≤contact B φ) : γ<C B φ := by
  have hA : 1≤A := by linarith [contact_upper ht hφ]
  have hAhi := (outer_bounds ht).2.1.trans_lt outer_endpoint_bounds.2.1
  have hdom {θ : ℝ} (hθ : θ∈Icc φ (Real.pi/2)) : Lower θ := ⟨hφ.1.trans hθ.1,hθ.2⟩
  have hbθ (θ : ℝ) (hθ : θ∈Icc φ (Real.pi/2)) :
      0≤contact B θ ∧ contact B θ<83/200 := by
    have hm := contact_monotone ht hφ (hdom hθ) hθ.1
    exact ⟨by linarith,by linarith [contact_upper ht (hdom hθ)]⟩
  have hcurv (θ : ℝ) (hθ : θ∈Icc φ (Real.pi/2)) : 0<CDD B θ := by
    have hh := hbθ θ hθ
    have hc : 0<g-2*z*contact B θ := by
      dsimp [g,z,EdgeThreeAligned.gn,EdgeThreeAligned.zn]
      linarith [hh.2]
    have hp := mul_pos hc (show 0<contact B θ+1/2 by linarith [hh.1])
    have hq := mul_nonneg (by norm_num [z,EdgeThreeAligned.zn] : 0≤2*z)
      (sq_nonneg (contactD B θ))
    dsimp [CDD]
    linarith
  have hdmono : MonotoneOn (CD B) (Icc φ (Real.pi/2)) :=
    monoOn_of_hasDeriv_nonneg
      (fun θ _ => (CD_hasDerivAt B θ).continuousAt.continuousWithinAt)
      (fun θ _ => CD_hasDerivAt B θ)
      (fun θ hθ => (hcurv θ (Ioo_subset_Icc_self hθ)).le)
  have hnegative (θ : ℝ) (hθ : θ∈Icc φ (Real.pi/2)) : CD B θ<0 :=
    (hdmono hθ ⟨hφ.2,le_rfl⟩ hθ.2).trans_lt (aligned_slope ht hB)
  have hm : AntitoneOn (C B) (Icc φ (Real.pi/2)) :=
    antiOn_of_hasDeriv_nonpos
      (fun θ _ => (C_hasDerivAt B θ).continuousAt.continuousWithinAt)
      (fun θ _ => C_hasDerivAt B θ)
      (fun θ hθ => (hnegative θ (Ioo_subset_Icc_self hθ)).le)
  exact (aligned_lower ht hA).trans_le
    (hm ⟨le_rfl,hφ.2⟩ ⟨hφ.2,le_rfl⟩ hφ.2)

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.High
end
end
end

section
/-!
## Exact angle minimization for the negative-core side contact

Completing the source quadratic leaves a positive sinusoid. Its phase
is proved to remain in the first quadrant at every feasible original
contact, and a zero-curvature tangent gives its exact angle minimum.
The two rational slopes used later share the same physical target arc.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
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
    exact (((Real.hasDerivAt_sin x).const_mul (P B)).sub
      ((Real.hasDerivAt_cos x).const_mul (V B))).congr_deriv (by ring)
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
    exact (mul_eq_zero.mp he).resolve_left hρ.ne'
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
    have hp := mul_pos hh0 hρ
    rw [show 1+(S h B)^2=(h*ρ)^2 by rw [mul_pow,hρ2]; linarith [hs2]]
    exact Real.sqrt_sq hp.le
  have hαframe := CentralForbidden.atan_frame (show (0:ℝ)<1 by norm_num) hS.le
  norm_num only [one_pow,div_one] at hαframe
  rw [hroot] at hαframe
  change h*ρ*Real.cos α=1 ∧ h*ρ*Real.sin α=S h B at hαframe
  have hf (x : ℝ) : HasDerivAt (fun y => y-h*ρ*Real.sin y) (1-h*ρ*Real.cos x) x := by
    exact ((hasDerivAt_id' x).sub ((Real.hasDerivAt_sin x).const_mul (h*ρ))).congr_deriv
      (by ring)
  have hd (x : ℝ) : HasDerivAt (fun y => 1-h*ρ*Real.cos y) (h*ρ*Real.sin x) x := by
    exact (((Real.hasDerivAt_cos x).const_mul (h*ρ)).const_sub 1).congr_deriv (by ring)
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
    linarith [congrArg (fun x : ℝ => h*x) hrotation]
  have hsq := mul_nonneg (by norm_num [z,EdgeThreeAligned.zn] : 0≤z)
    (sq_nonneg (contact B φ-(g-h)/(2*z)))
  have hquad : -h*contact B φ-epsilon h≤-g*contact B φ+z*(contact B φ)^2 := by
    have hkey : -g*contact B φ+z*(contact B φ)^2-(-h*contact B φ-epsilon h)=
        z*(contact B φ-(g-h)/(2*z))^2 := by
      dsimp only [epsilon,z,EdgeThreeAligned.zn]
      field_simp
      ring
    linarith
  have hqcontact : q φ=contact B φ+1/2 := by dsimp [q,P,V,U,contact]; ring
  rw [hqcontact] at hmin
  dsimp [E,C,sideValue,EdgeThreeAligned.negativeSideCost,EdgeThreeAligned.sideH]
  linarith

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum.Polynomials
open Polynomial WholeIntervalPolynomial WholeIntervalPolynomial.Certificate

def q : ℚ := 9789/2500
def t : ℚ[X] := Polynomial.C (q+1)-Polynomial.C 2*X
def w : ℚ[X] := Polynomial.C q-X^2
def b : ℚ[X] := Polynomial.C 2*X^2-Polynomial.C (4*q)*X+Polynomial.C (q*(q+1))
def bd : ℚ[X] := Polynomial.C 4*X-Polynomial.C (4*q)
def a : ℚ[X] := b*X^2*t-w*(bd*X*t-b*(Polynomial.C 3*t-Polynomial.C 4*X))
def d : ℚ[X] := X^5*t^3-a
def c (h : ℚ) : ℚ[X] :=
  let s := Polynomial.C (h^2)*t-1
  Polynomial.C (3*h^2*q)*X*t^2*s-Polynomial.C (h^4)*w*X^2*t^2-Polynomial.C (4*h^2)*w*X^2*t*s+
    Polynomial.C (3*q)*t^2*s^2-Polynomial.C (6*q)*X*t*s^2+Polynomial.C 8*w*X^2*s^2
def cg : ℚ[X] := c (98439/100000)
lemma d_evaluation (u : ℝ) : aeval u d=D0 u := by
  simp [d,a,b,bd,t,w,q,D0,A0,baseE,baseEd,Q0]

lemma c_evaluation (h : ℚ) (u : ℝ) : aeval u (c h)=Ch (h:ℝ) u := by
  simp [c,t,w,q,Ch,Q0]

/-- `d` has positive Bernstein coefficients of degree `8` on `[42/25, 383/200]`. -/
theorem D0_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (383/200)) : 0<D0 u := by
  have h0 : 0≤u-42/25 := sub_nonneg.2 hu.1
  have h1 : 0≤383/200-u := sub_nonneg.2 hu.2
  have hb (i j : ℕ) : 0≤(u-42/25)^i*(383/200-u)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  rw [← d_evaluation]
  simp only [d,a,b,bd,t,w,q,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 8 0,hb 7 1,hb 6 2,hb 5 3,hb 4 4,hb 3 5,hb 2 6,hb 1 7,hb 0 8]

/-- `cg` has positive Bernstein coefficients of degree `6` on `[42/25, 383/200]`. -/
theorem Ch_first_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (383/200)) : 0<Ch g u := by
  have h0 : 0≤u-42/25 := sub_nonneg.2 hu.1
  have h1 : 0≤383/200-u := sub_nonneg.2 hu.2
  have hb (i j : ℕ) : 0≤(u-42/25)^i*(383/200-u)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  have hc : aeval u cg=Ch g u := by
    simpa [cg,g,EdgeThreeAligned.gn] using c_evaluation (98439/100000) u
  rw [← hc]
  simp only [cg,c,t,w,q,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 6 0,hb 5 1,hb 4 2,hb 3 3,hb 2 4,hb 1 5,hb 0 6]

/-- `c (39/40)` has positive Bernstein coefficients of degree `6` on `[42/25, 87/50]`. -/
theorem Ch_second_positive {u : ℝ} (hu : u∈Set.Icc (42/25:ℝ) (87/50)) : 0<Ch (39/40) u := by
  have h0 : 0≤u-42/25 := sub_nonneg.2 hu.1
  have h1 : 0≤87/50-u := sub_nonneg.2 hu.2
  have hb (i j : ℕ) : 0≤(u-42/25)^i*(87/50-u)^j := mul_nonneg (pow_nonneg h0 i) (pow_nonneg h1 j)
  have hc := c_evaluation (39/40) u
  norm_num at hc
  rw [← hc]
  simp only [c,t,w,q,map_add,map_sub,map_mul,map_pow,map_one,aeval_C,aeval_X,eq_ratCast]
  push_cast
  linarith [hb 6 0,hb 5 1,hb 4 2,hb 3 3,hb 2 4,hb 1 5,hb 0 6]

end SquaresInCircles.Eight.SecondWord.MixedThree.NegativeSource.Minimum.Polynomials
end
end
end
