module

public import SquaresInCircles.Eight.Corners.Nominal
public import SquaresInCircles.Eight.Owners.Negative.CaptureStress

/-!
# Eight squares: whole-arc flux reserves of the nominal family

The cosine support inequality and two
explicit polynomial identities preserve the linear gains of both
canonical errors.  These estimates use one continuous weight family
over the entire actual tilt interval.
-/

section
/-!
## Completing the circles on the canonical negative branch

The only angular errors of this branch are `t` and `e`; the other mixed angle is
`u = α - t - e`. Collecting the five weak contacts with the weights of `Parameters`
(`demand_le_work`) and completing the circle of each anchor (`exact_identity`,
`original_circle_inequality`) gives an exact formula in the two errors (`defect_difference`,
`defect_radius`), with no auxiliary point for G or T.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.CanonicalNegativeStress

structure Parameters where
  a : ℝ
  beta : ℝ
  delta : ℝ
  epsilon : ℝ
  omega : ℝ
  mu : Fin 5 → ℝ

def Parameters.Positive (w : Parameters) : Prop :=
  0≤w.a ∧ 0≤w.beta ∧ 0≤w.delta ∧ 0≤w.epsilon ∧ 0≤w.omega ∧ ∀i,0<w.mu i

abbrev W := NegativeCaptureStress.W
def massSum (w : Parameters) : ℝ := ∑i : Fin 5,w.mu i

/-- The forces on the anchors, in the order A, B, D, E, H, each in its own frame with positive
coordinates; the entry of E uses the magnitude of its tangent. -/
def forces (w : Parameters) (α t u e : ℝ) : Fin 5 → Point := ![
  (w.omega*Real.cos u,w.a-w.omega*Real.sin u),
  (w.beta*Real.cos t,w.a-w.beta*Real.sin t),
  (w.delta,w.beta/Real.cos e),
  (w.epsilon*Real.sin α,w.delta-w.epsilon*Real.cos α),
  (w.epsilon,w.omega)]

def demand (w : Parameters) (α t u e : ℝ) : ℝ :=
  w.omega*(1+W u)+w.a+
    w.beta*(W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e)+
    w.delta+w.epsilon*W α

def circleSupport (q m : ℝ) (F : Point) : ℝ :=
  q*m+normSq F/(4*m)-(F.1+F.2)/2

def defect (q : ℝ) (w : Parameters) (α t u e : ℝ) : ℝ :=
  demand w α t u e-∑i : Fin 5,circleSupport q (w.mu i) (forces w α t u e i)

def work (F : Point) (P : SignedPoint) : ℝ := F.1*P.a+F.2*P.y

def centerSquare (m : ℝ) (F : Point) (P : SignedPoint) : ℝ :=
  m*((P.a+1/2-F.1/(2*m))^2+(P.y+1/2-F.2/(2*m))^2)

def centerLoss (w : Parameters) (α t u e : ℝ) (p : Fin 5 → SignedPoint) : ℝ :=
  ∑i : Fin 5,centerSquare (w.mu i) (forces w α t u e i) (p i)

def circleLoss (q : ℝ) (w : Parameters) (p : Fin 5 → SignedPoint) : ℝ :=
  ∑i : Fin 5,w.mu i*(q-(p i).circle)

theorem center_identity {m : ℝ} (hm : m≠0) (F : Point) {P : SignedPoint}
    (hy : 0≤P.y) (q : ℝ) :
    centerSquare m F P+m*(q-P.circle)=circleSupport q m F-work F P := by
  rw [SignedPoint.circle,abs_of_nonneg hy]
  dsimp [centerSquare,circleSupport,normSq,work]
  field_simp [hm]
  ring

/-- The exact identity: the defect, the center loss and the circle loss add up to the demand minus
the work of the forces. It keeps the radial slack of each anchor. -/
theorem exact_identity {w : Parameters} (hm : ∀i,w.mu i≠0)
    {p : Fin 5 → SignedPoint} (hy : ∀i,0≤(p i).y) (q α t u e : ℝ) :
    defect q w α t u e+centerLoss w α t u e p+circleLoss q w p=
      demand w α t u e-∑i : Fin 5,work (forces w α t u e i) (p i) := by
  have hh := Finset.sum_congr rfl
    (fun i (_ : i∈(Finset.univ : Finset (Fin 5))) =>
      center_identity (hm i) (forces w α t u e i) (hy i) q)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hh
  dsimp [defect,centerLoss,circleLoss]
  linarith

/-- The weighted sum of the five weak contacts HA, AB, BD, DE, EH bounds the demand by the work of
the forces. -/
theorem demand_le_work {w : Parameters} (hw : w.Positive)
    {H A B D E : SignedPoint} {α t u e : ℝ}
    (hHA : 1+W u≤H.y+A.a*Real.cos u-A.y*Real.sin u)
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    demand w α t u e≤∑i : Fin 5,
      work (forces w α t u e i) (![A,B,D,E,H] i) := by
  obtain ⟨ha,hb,hd,he,ho,hm⟩ := hw
  have h1 := mul_le_mul_of_nonneg_left hHA ho
  have h2 := mul_le_mul_of_nonneg_left hAB ha
  have h3 := mul_le_mul_of_nonneg_left hBD hb
  have h4 := mul_le_mul_of_nonneg_left hDE hd
  have h5 := mul_le_mul_of_nonneg_left hEH he
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,forces,work,demand,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero]
  have hdiv : w.beta*(D.y/Real.cos e)=w.beta/Real.cos e*D.y := by ring
  linarith

theorem original_circle_inequality {w : Parameters} (hw : w.Positive)
    {H A B D E : SignedPoint} {q α t u e : ℝ}
    (hyH : 0≤H.y) (hyA : 0≤A.y) (hyB : 0≤B.y) (hyD : 0≤D.y) (hyE : 0≤E.y)
    (hHA : 1+W u≤H.y+A.a*Real.cos u-A.y*Real.sin u)
    (hAB : 1≤A.y+B.y)
    (hBD : W t+1/2+1/(2*Real.cos e)+(13/12)*Real.tan e≤
      D.y/Real.cos e+B.a*Real.cos t-B.y*Real.sin t)
    (hDE : 1≤D.a+E.y)
    (hEH : W α≤H.a+E.a*Real.sin α-E.y*Real.cos α) :
    defect q w α t u e+centerLoss w α t u e ![A,B,D,E,H]+
      circleLoss q w ![A,B,D,E,H]≤0 := by
  have hm : ∀i,w.mu i≠0 := fun i => (hw.2.2.2.2.2 i).ne'
  have hy : ∀i : Fin 5,0≤(![A,B,D,E,H] i).y := by
    intro i
    fin_cases i <;>
      simp only [] <;>
      assumption
  rw [exact_identity hm hy]
  exact sub_nonpos.mpr (demand_le_work hw hHA hAB hBD hDE hEH)

theorem centerLoss_nonneg {w : Parameters} (hw : w.Positive)
    (p : Fin 5 → SignedPoint) (α t u e : ℝ) : 0≤centerLoss w α t u e p := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hw.2.2.2.2.2 i).le (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem circleLoss_nonneg {w : Parameters} (hw : w.Positive)
    {p : Fin 5 → SignedPoint} {q : ℝ} (hc : ∀i,(p i).Contained q) :
    0≤circleLoss q w p := by
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hw.2.2.2.2.2 i).le (sub_nonneg.mpr (hc i)))

def KA (w : Parameters) : ℝ := w.a*w.omega/(2*w.mu 0)
def KB (w : Parameters) : ℝ := w.a*w.beta/(2*w.mu 1)
def flux (w : Parameters) (α : ℝ) : ℝ := KA w*Real.cos α-w.omega*Real.sin α

def fixedPart (q : ℝ) (w : Parameters) (α : ℝ) : ℝ :=
  2*w.omega+2*w.a+w.beta+2*w.delta+w.epsilon+w.epsilon*Real.sin α-q*massSum w-
    (w.omega^2+w.a^2)/(4*w.mu 0)-(w.beta^2+w.a^2)/(4*w.mu 1)-
    w.delta^2/(4*w.mu 2)-
    ((w.epsilon*Real.sin α)^2+(w.delta-w.epsilon*Real.cos α)^2)/(4*w.mu 3)-
    (w.epsilon^2+w.omega^2)/(4*w.mu 4)

theorem ordinary_norm (omega a z : ℝ) :
    (omega*Real.cos z)^2+(a-omega*Real.sin z)^2=
      omega^2+a^2-2*omega*a*Real.sin z := by
  nlinarith [congrArg (fun x : ℝ => omega^2*x) (Real.sin_sq_add_cos_sq z)]

theorem defect_formula {w : Parameters} (_hm : ∀i,w.mu i≠0)
    (q α t u e : ℝ) :
    defect q w α t u e=fixedPart q w α+w.omega*Real.cos u+KA w*Real.sin u+
      w.beta*Real.cos t+KB w*Real.sin t+w.beta/Real.cos e+
      w.beta*(13/12)*Real.tan e-w.beta^2/(4*w.mu 2)*(1/Real.cos e)^2 := by
  simp only [defect,forces,demand,circleSupport,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,normSq]
  rw [ordinary_norm,ordinary_norm]
  dsimp [fixedPart,massSum,KA,KB,W,NegativeCaptureStress.W,NegativeLargeDEStress.W]
  simp only [Fin.sum_univ_five]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def correction (w : Parameters) (α t e : ℝ) : ℝ :=
  w.omega*(Real.cos (α-t-e)-Real.cos α)+KA w*(Real.sin (α-t-e)-Real.sin α)+
    w.beta*(Real.cos t-1)+KB w*Real.sin t+
    w.beta*(1/Real.cos e-1)+w.beta*(13/12)*Real.tan e-
    w.beta^2/(4*w.mu 2)*((1/Real.cos e)^2-1)

/-- The defect at the errors `t`, `e` is the defect at zero errors plus `correction w α t e`. -/
theorem defect_difference {w : Parameters} (hm : ∀i,w.mu i≠0)
    (q α t e : ℝ) :
    defect q w α t (α-t-e) e=defect q w α 0 α 0+correction w α t e := by
  rw [defect_formula hm,defect_formula hm]
  simp only [Real.cos_zero,Real.sin_zero,Real.tan_zero,mul_one,mul_zero,
    div_one,one_pow]
  dsimp [correction]
  ring

theorem defect_radius (w : Parameters) (q q₀ α t u e : ℝ) :
    defect q w α t u e=defect q₀ w α t u e-(q-q₀)*massSum w := by
  simp [defect,circleSupport,massSum,Fin.sum_univ_succ]
  ring

end SquaresInCircles.Eight.CanonicalNegativeStress
end
end
end

section
/-!
## A direct quantitative correction for the two canonical negative errors

The exact five-circle scalar has only two
errors after canonicalization.  Sine/cosine addition and elementary
Taylor bounds preserve their first-order flux reserves.  The estimates
below therefore need neither an owner table nor a five-variable Hessian.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CanonicalNegativeCorrection
open CanonicalNegativeStress

theorem mixed_turn_lower {omega k α r L : ℝ}
    (hr : 0≤r) (hflux : 0≤k*Real.cos α-omega*Real.sin α)
    (hamp : 0≤omega*Real.cos α+k*Real.sin α)
    (hL : omega*Real.cos α+k*Real.sin α≤L) :
    -(k*Real.cos α-omega*Real.sin α)*r-L*r^2/2≤
      omega*(Real.cos (α-r)-Real.cos α)+k*(Real.sin (α-r)-Real.sin α) := by
  have hid : omega*(Real.cos (α-r)-Real.cos α)+k*(Real.sin (α-r)-Real.sin α)=
      (omega*Real.cos α+k*Real.sin α)*(Real.cos r-1)-
        (k*Real.cos α-omega*Real.sin α)*Real.sin r := by
    rw [Real.cos_sub,Real.sin_sub]
    ring
  rw [hid]
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le hr) hflux
  have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := r)) hamp
  have hquad := mul_le_mul_of_nonneg_right hL (sq_nonneg r)
  linarith

theorem ordinary_turn_lower {beta k t B K : ℝ}
    (ht : 0≤t) (hbeta : beta∈Icc 0 B) (hk : k∈Icc 0 K) :
    k*t-B*t^2/2-K*t^3/6≤beta*(Real.cos t-1)+k*Real.sin t := by
  have hc := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := t)) hbeta.1
  have hs := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube ht) hk.1
  have hB := mul_le_mul_of_nonneg_right hbeta.2 (sq_nonneg t)
  have hK := mul_le_mul_of_nonneg_right hk.2 (pow_nonneg ht 3)
  linarith

theorem short_secant_bounds {e : ℝ} (he : e∈Icc 0 (3/200:ℝ)) :
    0<Real.cos e ∧ 1≤1/Real.cos e ∧ 1/Real.cos e≤501/500 ∧
      0≤1/Real.cos e-1 ∧ 1/Real.cos e-1≤(501/1000)*e^2 ∧
      0≤(1/Real.cos e)^2-1 ∧ (1/Real.cos e)^2-1≤(101/100)*e^2 ∧
      e-e^3/6≤Real.tan e := by
  have he2 := pow_le_pow_left₀ he.1 he.2 2
  have hcl := Real.one_sub_sq_div_two_le_cos (x := e)
  have hcos : (999/1000:ℝ)<Real.cos e := by
    nlinarith
  have hc : 0<Real.cos e := by linarith
  have hc1 := Real.cos_le_one e
  have hv : 1≤1/Real.cos e := by apply (le_div_iff₀ hc).2; simpa
  have hvu : 1/Real.cos e≤501/500 := by apply (div_le_iff₀ hc).2; linarith
  have hd : 0≤1/Real.cos e-1 := by linarith
  have hdiff : 1/Real.cos e-1=(1-Real.cos e)/Real.cos e := by
    field_simp [hc.ne']
  have hdu : 1/Real.cos e-1≤(501/1000)*e^2 := by
    rw [hdiff]
    apply (div_le_iff₀ hc).2
    have hp := mul_le_mul_of_nonneg_right hcos.le (sq_nonneg e)
    nlinarith [sq_nonneg e]
  have hv2 : 0≤(1/Real.cos e)^2-1 := by nlinarith
  have hv2u : (1/Real.cos e)^2-1≤(101/100)*e^2 := by
    have hp := mul_le_mul hdu (show 1/Real.cos e+1≤1001/500 by linarith)
      (show 0≤1/Real.cos e+1 by linarith) (by positivity : 0≤(501/1000)*e^2)
    nlinarith [sq_nonneg e]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi he.1
    (by linarith [he.2,Real.pi_gt_three])
  have htangent : Real.sin e≤Real.tan e := by
    rw [Real.tan_eq_sin_div_cos]
    apply (le_div_iff₀ hc).2
    simpa using mul_le_mul_of_nonneg_left hc1 hs0
  exact ⟨hc,hv,hvu,hd,hdu,hv2,hv2u,(Real.sin_ge_sub_cube he.1).trans htangent⟩

theorem secant_turn_lower {beta gamma e : ℝ}
    (hbeta : beta∈Icc 0 (39/50:ℝ)) (hgamma : gamma∈Icc 0 (6/5:ℝ))
    (he : e∈Icc 0 (3/200:ℝ)) :
    beta*(13/12)*e-(61/100)*e^2≤
      beta*(1/Real.cos e-1)+beta*(13/12)*Real.tan e-
        (gamma/2)*((1/Real.cos e)^2-1) := by
  obtain ⟨hc,hv,hvu,hd,hdu,hv2,hv2u,htan⟩ := short_secant_bounds he
  have hsec := mul_nonneg hbeta.1 hd
  have htan' := mul_le_mul_of_nonneg_left htan
    (mul_nonneg hbeta.1 (by norm_num : (0:ℝ)≤13/12))
  have hlast := mul_le_mul hgamma.2 hv2u hv2 (by norm_num : (0:ℝ)≤6/5)
  have hbeta3 := mul_le_mul_of_nonneg_right hbeta.2 (pow_nonneg he.1 3)
  have he3 : e^3≤(3/200)*e^2 := by
    have hp := mul_le_mul_of_nonneg_right he.2 (sq_nonneg e)
    nlinarith
  nlinarith [sq_nonneg e]

theorem ordinary_short_lower {beta k t : ℝ}
    (hbeta : beta∈Icc 0 (39/50:ℝ)) (hk : k∈Icc 0 (431/500:ℝ))
    (ht : t∈Icc 0 (3/200:ℝ)) :
    k*t-(79/200)*t^2≤beta*(Real.cos t-1)+k*Real.sin t := by
  have hh := ordinary_turn_lower ht.1 hbeta hk
  have ht3 : t^3≤(3/200)*t^2 := by
    have hp := mul_le_mul_of_nonneg_right ht.2 (sq_nonneg t)
    nlinarith
  nlinarith [sq_nonneg t]

/-- The stationary primitive bounds are the only inputs to this
quantitative scalar lemma.  Its conclusion is proved from the exact
two-error formula, not assumed as a terminal contract. -/
theorem correction_lower {w : CanonicalNegativeStress.Parameters} {α t e : ℝ}
    (hα : α∈Icc (1/10:ℝ) (4/25))
    (ht : 0≤t) (he : 0≤e) (hr : t+e≤3/200) (hu : t+e≤α)
    (homega : w.omega∈Icc 0 (4/5:ℝ))
    (hKA : KA w∈Icc 0 (471/500:ℝ))
    (hbeta : w.beta∈Icc 0 (39/50:ℝ))
    (hKB : KB w∈Icc 0 (431/500:ℝ))
    (hgamma : w.beta^2/(2*w.mu 2)∈Icc 0 (6/5:ℝ))
    (hflux : 0≤flux w α)
    (hsmall : 3367/250000≤KB w-flux w α)
    (hsecant : 23/1000≤w.beta*(13/12)-flux w α) :
    (t+e)/5000≤correction w α t e := by
  have hα0 : 0≤α := by linarith [hα.1]
  have hc0 : 0≤Real.cos α := by
    have ha2 := pow_le_pow_left₀ hα0 hα.2 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hα0
    (by linarith [hα.2,Real.pi_gt_three])
  have hamp0 : 0≤w.omega*Real.cos α+KA w*Real.sin α :=
    add_nonneg (mul_nonneg homega.1 hc0) (mul_nonneg hKA.1 hs0)
  have hamp : w.omega*Real.cos α+KA w*Real.sin α≤951/1000 := by
    have h1 := mul_le_mul_of_nonneg_left (Real.cos_le_one α) homega.1
    have h2 := mul_le_mul hKA.2 ((Real.sin_le hα0).trans hα.2) hs0
      (by norm_num : (0:ℝ)≤471/500)
    linarith [homega.2]
  have hA := mixed_turn_lower (show 0≤t+e by linarith) hflux hamp0 hamp
  have ht' : t∈Icc 0 (3/200:ℝ) := ⟨ht,by linarith⟩
  have he' : e∈Icc 0 (3/200:ℝ) := ⟨he,by linarith⟩
  have hB := ordinary_short_lower hbeta hKB ht'
  have hD := secant_turn_lower hbeta hgamma he'
  have hDcoef : (w.beta^2/(2*w.mu 2))/2=w.beta^2/(4*w.mu 2) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hDcoef] at hD
  have hsmall' := mul_le_mul_of_nonneg_right hsmall ht
  have hsecant' := mul_le_mul_of_nonneg_right hsecant he
  have htt : t^2≤(t+e)*t := by nlinarith [mul_nonneg ht he]
  have hee : e^2≤(t+e)*e := by nlinarith [mul_nonneg ht he]
  have hrt := mul_le_mul_of_nonneg_right hr ht
  have hre := mul_le_mul_of_nonneg_right hr he
  rw [show α-(t+e)=α-t-e by ring] at hA
  dsimp [correction,flux] at *
  linarith

end SquaresInCircles.Eight.CanonicalNegativeCorrection
end
end
end

section
/-!
## The continuous nominal family in the two-error identity

The single nominal stress is expressed in
the original five-anchor completion used for the canonical negative
branch.  Its baseline is exactly the previously proved nominal gap.
All coefficient bounds below hold on the whole sine interval [0,3/10].
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CanonicalNominal
open Eight.FiveCorner CanonicalNegativeStress

def parameters (s : ℝ) : CanonicalNegativeStress.Parameters where
  a := Nominal.alpha s
  beta := Nominal.beta s
  delta := Nominal.delta s
  epsilon := Nominal.epsilon s
  omega := 1
  mu := Nominal.mass s

def atTilt (α : ℝ) : CanonicalNegativeStress.Parameters := parameters (Real.sin α)

theorem positive {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) (hp : 0<s) :
    (parameters s).Positive := by
  obtain ⟨ha,hb,hd,he⟩ := Nominal.weights_pos hs
  exact ⟨ha.le,hb.le,hd.le,he.le,(zero_le_one : (0:ℝ)≤1),Nominal.mass_pos hs hp⟩

theorem KA_formula {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KA (parameters s)=Nominal.alpha s*(41/24)*(1+13*s/60) := by
  have hd := Nominal.denominator_bounds hs
  dsimp [KA,parameters,Nominal.mass,Nominal.mA]
  field_simp [hd.1.ne']
  ring

theorem KB_formula {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KB (parameters s)=Nominal.alpha s*Nominal.beta s*(41/24)*(1-9*s/50) := by
  have hd := Nominal.denominator_bounds hs
  dsimp [KB,parameters,Nominal.mass,Nominal.mB]
  field_simp [hd.2.1.ne']
  ring

theorem gamma_formula {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    (parameters s).beta^2/(2*(parameters s).mu 2)=
      Nominal.beta s^2*(31/24)*(1+9*s/25) := by
  have hd := Nominal.denominator_bounds hs
  dsimp [parameters,Nominal.mass,Nominal.mD]
  field_simp [hd.2.2.1.ne']
  ring

theorem KA_polynomial {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KA (parameters s)=1+(843/800)*s+(13817/144000)*s^2-(533/28800)*s^3 := by
  rw [KA_formula hs]
  dsimp [Nominal.alpha]
  ring

theorem KB_polynomial {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KB (parameters s)=1+(1457/2400)*s-(34849/80000)*s^2-
      (592807/7200000)*s^3+(11111/288000)*s^4-(41/16000)*s^5 := by
  rw [KB_formula hs]
  dsimp [Nominal.alpha,Nominal.beta]
  ring

theorem beta_bounds {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    Nominal.beta s∈Icc (97/100:ℝ) 1 := by
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  dsimp [Nominal.beta]
  constructor <;> nlinarith [hs.1,hs.2,sq_nonneg s]

theorem KA_bounds {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KA (parameters s)∈Icc (1:ℝ) (4/3) := by
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hs3 := pow_nonneg hs.1 3
  have hb : 0≤843/800+(13817/144000)*s-(533/28800)*s^2 := by
    nlinarith [hs.1]
  have hp := mul_nonneg hs.1 hb
  rw [KA_polynomial hs]
  constructor <;> nlinarith [hs.2]

theorem KB_bounds {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    KB (parameters s)∈Icc (0:ℝ) (6/5) := by
  obtain ⟨ha,hb,_,_⟩ := Nominal.weights_pos hs
  have hd : 0<1-9*s/50 := (Nominal.denominator_bounds hs).2.1
  have hlow : 0≤KB (parameters s) := by
    rw [KB_formula hs]
    positivity
  have hs4 := pow_le_pow_left₀ hs.1 hs.2 4
  have hs3 := pow_nonneg hs.1 3
  have hs5 := pow_nonneg hs.1 5
  refine ⟨hlow,?_⟩
  rw [KB_polynomial hs]
  nlinarith [hs.2,sq_nonneg s]

theorem gamma_bounds {s : ℝ} (hs : s∈Icc 0 (3/10:ℝ)) :
    (parameters s).beta^2/(2*(parameters s).mu 2)∈Icc (0:ℝ) (3/2) := by
  have hs0 := hs.1
  have hb := beta_bounds hs
  have hb0 : 0≤Nominal.beta s := by linarith [hb.1]
  have hb2 : Nominal.beta s^2≤1 := by nlinarith [hb.1,hb.2]
  have hd : 0≤(31/24:ℝ)*(1+9*s/25) := by positivity
  have hm := mul_le_mul_of_nonneg_right hb2 hd
  rw [gamma_formula hs]
  constructor
  · positivity
  · nlinarith [hs.2]

theorem nominal_force_norm (α : ℝ) (i : Fin 5) :
    normSq (forces (atTilt α) α 0 α 0 i)=normSq (Nominal.forces α i) := by
  rw [Nominal.force_norm]
  fin_cases i <;> simp [forces,atTilt,parameters,normSq]
  · linear_combination Real.sin_sq_add_cos_sq α
  · linear_combination (Nominal.epsilon (Real.sin α))^2*Real.sin_sq_add_cos_sq α

theorem nominal_corner_demand (α : ℝ) :
    demand (atTilt α) α 0 α 0+
      ∑i : Fin 5,((forces (atTilt α) α 0 α 0 i).1+
        (forces (atTilt α) α 0 α 0 i).2)/2=Nominal.demand α := by
  simp only [demand,forces,atTilt,parameters,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ,
    Real.cos_zero,Real.sin_zero,Real.tan_zero]
  dsimp [Nominal.demand,spanDemand,W,NegativeCaptureStress.W,NegativeLargeDEStress.W]
  simp only [Real.cos_zero,Real.sin_zero]
  ring

/-- The baseline agrees with the existing nominal gap even at zero
sine, where the E force and mass both vanish. -/
theorem baseline_gap (q α : ℝ) :
    CanonicalNegativeStress.defect q (atTilt α) α 0 α 0=Nominal.gap q α := by
  have henergy : (∑i : Fin 5,normSq (forces (atTilt α) α 0 α 0 i)/
      (4*(atTilt α).mu i))=Nominal.energy α := by
    apply Finset.sum_congr rfl
    intro i _
    rw [nominal_force_norm]
    rfl
  have hmass : massSum (atTilt α)=Nominal.massSum (Real.sin α) := rfl
  have hdemand := nominal_corner_demand α
  dsimp only [CanonicalNegativeStress.defect,circleSupport]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  change demand (atTilt α) α 0 α 0-
    (q*massSum (atTilt α)+
      (∑i : Fin 5,normSq (forces (atTilt α) α 0 α 0 i)/(4*(atTilt α).mu i))-
      (∑i : Fin 5,((forces (atTilt α) α 0 α 0 i).1+
        (forces (atTilt α) α 0 α 0 i).2)/2))=Nominal.gap q α
  rw [henergy,hmass]
  dsimp only [Nominal.gap]
  linarith

end SquaresInCircles.Eight.CanonicalNominal
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CanonicalNominal
open Eight.FiveCorner CanonicalNegativeStress

theorem short_trig {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    Real.sin α∈Icc 0 (3/10:ℝ) ∧ (19/20:ℝ)≤Real.cos α ∧
      Real.cos α≤1-(Real.sin α)^2/2 := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hα.1
    (by linarith [hα.2,Real.pi_gt_three])
  have hsu := (Real.sin_le hα.1).trans hα.2
  have ha2 := pow_le_pow_left₀ hα.1 hα.2 2
  have hcl : (19/20:ℝ)≤Real.cos α := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := α)]
  have hcu : Real.cos α≤1-(Real.sin α)^2/2 := by
    nlinarith [Real.sin_sq_add_cos_sq α,sq_nonneg (1-Real.cos α)]
  exact ⟨⟨hs0,by linarith⟩,hcl,hcu⟩

theorem flux_bounds {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    0≤flux (atTilt α) α ∧ flux (atTilt α) α≤101/100 := by
  obtain ⟨hs,hcl,hcu⟩ := short_trig hα
  have hA := KA_bounds hs
  have hA0 : 0≤KA (parameters (Real.sin α)) := by linarith [hA.1]
  have hc0 : 0≤Real.cos α := by linarith
  have hlow := mul_le_mul_of_nonneg_right hA.1 hc0
  have hup := mul_le_mul_of_nonneg_left hcu hA0
  have hs3 := pow_le_pow_left₀ hs.1 hs.2 3
  have hbracket : 0≤583/144000+(15707/28800)*Real.sin α+
      (13817/288000)*(Real.sin α)^2-(533/57600)*(Real.sin α)^3 := by
    nlinarith [hs.1,sq_nonneg (Real.sin α)]
  have hprod := mul_nonneg (sq_nonneg (Real.sin α)) hbracket
  have hid : 1+(43/800)*Real.sin α-(2/5)*(Real.sin α)^2-
      (KA (parameters (Real.sin α))*(1-(Real.sin α)^2/2)-Real.sin α)=
      (Real.sin α)^2*(583/144000+(15707/28800)*Real.sin α+
        (13817/288000)*(Real.sin α)^2-(533/57600)*(Real.sin α)^3) := by
    rw [KA_polynomial hs]
    ring
  have hquad : 1+(43/800)*Real.sin α-(2/5)*(Real.sin α)^2≤101/100 := by
    nlinarith [sq_nonneg (Real.sin α-43/640)]
  change 0≤KA (parameters (Real.sin α))*Real.cos α-1*Real.sin α ∧
    KA (parameters (Real.sin α))*Real.cos α-1*Real.sin α≤101/100
  simp only [one_mul]
  constructor <;> nlinarith [hs.2]

theorem small_error_reserve {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    Real.sin α/2≤KB (atTilt α)-flux (atTilt α) α := by
  obtain ⟨hs,hcl,hcu⟩ := short_trig hα
  have hA0 : 0≤KA (parameters (Real.sin α)) := by linarith [(KA_bounds hs).1]
  have hcos := mul_le_mul_of_nonneg_left hcu hA0
  have hs4 := pow_le_pow_left₀ hs.1 hs.2 4
  have hbracket : 0≤4/75-(11363/360000)*Real.sin α-
      (3403/288000)*(Real.sin α)^4 := by
    nlinarith [hs.2]
  have hprod := mul_nonneg hs.1 hbracket
  have hid : KB (parameters (Real.sin α))-
      KA (parameters (Real.sin α))*(1-(Real.sin α)^2/2)+Real.sin α-Real.sin α/2=
      Real.sin α*(4/75-(11363/360000)*Real.sin α-(3403/288000)*(Real.sin α)^4)+
        (3333943/7200000)*(Real.sin α)^3+(779/9000)*(Real.sin α)^4 := by
    rw [KA_polynomial hs,KB_polynomial hs]
    ring
  have h3 := pow_nonneg hs.1 3
  have h4 := pow_nonneg hs.1 4
  change Real.sin α/2≤KB (parameters (Real.sin α))-
    (KA (parameters (Real.sin α))*Real.cos α-1*Real.sin α)
  simp only [one_mul]
  nlinarith

theorem secant_error_reserve {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    1/25≤(atTilt α).beta*(13/12)-flux (atTilt α) α := by
  have hb := beta_bounds (short_trig hα).1
  have hf := (flux_bounds hα).2
  change 1/25≤Nominal.beta (Real.sin α)*(13/12)-flux (atTilt α) α
  linarith [hb.1]

theorem amplitude_bounds {α : ℝ} (hα : α∈Icc 0 (27/100:ℝ)) :
    0≤Real.cos α+KA (atTilt α)*Real.sin α ∧
      Real.cos α+KA (atTilt α)*Real.sin α≤7/5 := by
  obtain ⟨hs,hc,_⟩ := short_trig hα
  have hA : KA (atTilt α)∈Icc (1:ℝ) (4/3) := KA_bounds hs
  have hp0 := mul_nonneg (show 0≤KA (atTilt α) by exact le_trans (by norm_num) hA.1) hs.1
  have hpu := mul_le_mul hA.2 hs.2 hs.1 (by norm_num : (0:ℝ)≤4/3)
  constructor <;> linarith [Real.cos_le_one α]

end SquaresInCircles.Eight.CanonicalNominal
end
end
end
