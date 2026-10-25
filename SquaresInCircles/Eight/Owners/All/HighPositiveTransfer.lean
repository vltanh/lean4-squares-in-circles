module

public import SquaresInCircles.Common.DiskSupport
public import SquaresInCircles.Eight.Owners.All.HighSecondary
public import SquaresInCircles.Eight.Owners.DirectedPowerBounds

/-!
# Eight squares: the positive high-primary projection

The multiplier `positiveLambda z`, built with a fixed rational radius, turns the primary
projection of owner `3` into the scalar `positivePrimaryScalar`, bounded on the whole interval
(`positive_primary_transfer`). The target keeps its signed transverse coordinate and may lie on
either piece of the core or on any outer chart. The quarter charge is then at least `kappa`, and
exceeds it at positive angle (`positive_primary_charge`).
-/

section
/-!
## The complete positive-primary scalar for the all-high potential

One degree-eleven polynomial bounds the scalar on the complete angle
interval.  Dividing its known zero constant term gives one degree-ten
polynomial whose derivative is negative by a single centered coefficient
norm.  The scalar transfer is algebraic in the original diagonal
constant.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

def positiveRadius : ℝ := 1979/1000
def etaLower : ℝ := 39921/100000
def etaError : ℝ := 1/100000
def sineCoefficient : ℝ := positiveRadius-(3/4+etaLower^2)/(2*positiveRadius)

def positivePrimaryScalar (z e : ℝ) : ℝ := z+kappa*(e+
  Real.cos z*(Real.sin z-e)-positiveRadius*Real.sin z+
  Real.sin z*(Real.sin z-e)^2/(2*positiveRadius))

namespace PositivePolynomial
open Polynomial PowerTailBounds

def S9 : ℚ[X] := X-C (1/6)*X^3+C (1/120)*X^5-C (1/5040)*X^7+C (1/362880)*X^9
def S11 : ℚ[X] := S9-C (1/39916800)*X^11
def C8 : ℚ[X] := 1-C (1/2)*X^2+C (1/24)*X^4-C (1/720)*X^6+C (1/40320)*X^8
def C10 : ℚ[X] := C8-C (1/3628800)*X^10
def B : ℚ := (1979/1000)-((3/4)+(39921/100000)^2)/(2*(1979/1000))

def H : ℚ[X] := C (1-(103/100)*(1/100000))*X+C (103/100)*
  (C (39921/100000)*(1-C8)+C (1/2)*(S11.comp (C 2*X))-C B*S9-
    C (1/(8*(1979/1000)))*(S9.comp (C 3*X))-
    C ((39921/100000)/(2*(1979/1000)))*(1-C10.comp (C 2*X)))
def P : ℚ[X] := H.divX
def negDerivative : ℚ[X] := DirectedPowerBounds.shift (7/20) (-P.derivative)

@[simp] theorem S9_eval (z : ℝ) : aeval z S9=Arithmetic.sin9 z := by
  simp [S9,Arithmetic.sin9,Arithmetic.sin7]
  ring
@[simp] theorem S11_eval (z : ℝ) : aeval z S11=HighOrderTaylor.S11 z := by
  simp [S11,HighOrderTaylor.S11]
  ring
@[simp] theorem C8_eval (z : ℝ) : aeval z C8=Arithmetic.cos8 z := by
  simp [C8,Arithmetic.cos8]
  ring
@[simp] theorem C10_eval (z : ℝ) : aeval z C10=Arithmetic.cos10 z := by
  simp [C10,Arithmetic.cos10]
  ring

theorem H_eval (z : ℝ) : aeval z H=(1-kappa*etaError)*z+kappa*
    (etaLower*(1-Arithmetic.cos8 z)+(1/2)*HighOrderTaylor.S11 (2*z)-
      sineCoefficient*Arithmetic.sin9 z-Arithmetic.sin9 (3*z)/(8*positiveRadius)-
      etaLower/(2*positiveRadius)*(1-Arithmetic.cos10 (2*z))) := by
  simp [H,aeval_comp,B,kappa,etaError,etaLower,sineCoefficient,positiveRadius]
  ring

/-- `P` in closed form: the coefficients of `H/X`. -/
private def r59_P : ℚ[X] := C (130980455423/3958000000000)+
    C (-86349123/39580000000)*X+
    C (-2223241222823/23748000000000)*X^2+
    C (8252509041/158320000000)*X^3+
    C (-4475878777177/474960000000000)*X^4+
    C (-13715804347/1583200000000)*X^5+
    C (309372358777177/19948320000000000)*X^6+
    C (8225096621/12665600000000)*X^7+
    C (-4031858278777177/1436279040000000000)*X^8+
    C (-195803/6679125000)*X^9+
    C (-103/3898125)*X^10

/-- `negDerivative` in closed form. -/
private def r59_N : ℚ[X] := C (18179501021475297728077903/361121587200000000000000000)+
    C (1665131271580472521376603/18056079360000000000000000)*X+
    C (-37129888110956042190271/300934656000000000000000)*X^2+
    C (-68932579828309747453/9028039680000000000000)*X^3+
    C (-42307927320328579879/451401984000000000000)*X^4+
    C (-11505424702701754579/263317824000000000000)*X^5+
    C (295279021179782129/5642524800000000000)*X^6+
    C (48110634043956947/1974883680000000000)*X^7+
    C (26845199/24490125000)*X^8+
    C (206/779625)*X^9

private theorem r59_H_eq : H=X*r59_P := by
  apply Polynomial.funext
  intro x
  simp only [H,S11,S9,C10,C8,B,r59_P,eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_pow,
    eval_comp,eval_one]
  ring

private theorem r59_P_eq : P=r59_P := by
  have h := X_mul_divX_add H
  have h0 : H.coeff 0=0 := by rw [r59_H_eq,coeff_X_mul_zero]
  rw [h0,map_zero,add_zero] at h
  exact mul_left_cancel₀ X_ne_zero (h.trans r59_H_eq)

private theorem r59_N_eq : negDerivative=r59_N := by
  rw [negDerivative,r59_P_eq]
  apply Polynomial.funext
  intro x
  simp only [DirectedPowerBounds.shift,r59_P,r59_N,eval_comp,eval_neg,derivative_add,
    derivative_C_mul_X_pow,derivative_C_mul_X,derivative_C,eval_add,eval_mul,eval_C,
    eval_X,eval_pow,zero_add]
  norm_num
  ring

theorem factor_identity : H=X*P := by
  rw [r59_P_eq]
  exact r59_H_eq

theorem derivative_identity : negDerivative=C (negDerivative.coeff 0)+tail negDerivative 1 9 := by
  rw [r59_N_eq]
  apply Polynomial.funext
  intro x
  simp only [r59_N,PowerTailBounds.tail,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,eval_add,eval_mul,eval_C,eval_X,eval_pow,
    Fin.val_zero,Fin.val_succ]
  norm_num
  ring

theorem derivative_reserve :
    (1/1250:ℚ)<negDerivative.coeff 0-PowerTailBounds.norm negDerivative 1 9 (7/20) := by
  rw [r59_N_eq]
  simp only [r59_N,PowerTailBounds.norm,Fin.sum_univ_succ,Fin.sum_univ_zero,coeff_add,
    coeff_C_mul,coeff_X_pow,coeff_C,coeff_X,Fin.val_zero,Fin.val_succ]
  norm_num

theorem endpoint_reserve : (3/2000:ℚ)<P.eval (7/10) := by
  rw [r59_P_eq]
  simp only [r59_P,eval_add,eval_mul,eval_C,eval_X,eval_pow]
  norm_num

theorem P_derivative_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    aeval z P.derivative<0 := by
  have hw : |z-7/20|≤((7/20:ℚ):ℝ) := by
    apply abs_le.mpr
    dsimp [frameCap] at hz
    push_cast
    constructor <;> linarith [hz.1,hz.2]
  have hh := DirectedPowerBounds.constant_lower derivative_identity hw
  have hr := Rat.cast_lt (K := ℝ) |>.mpr derivative_reserve
  push_cast at hr
  have he : aeval (z-7/20) negDerivative= -aeval z P.derivative := by
    have hz' : ((7/20:ℚ):ℝ)+(z-7/20)=z := by push_cast; ring
    rw [negDerivative,DirectedPowerBounds.shift_eval,hz',map_neg]
  rw [he] at hh
  linarith

theorem P_antitone : AntitoneOn (fun z : ℝ => aeval z P) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro z _
    exact (CenteredMonomialBounds.aeval_hasDerivAt P z).continuousAt.continuousWithinAt
  · exact fun z _ => CenteredMonomialBounds.aeval_hasDerivAt P z
  · exact fun z hz => (P_derivative_negative (Ioo_subset_Icc_self hz)).le

theorem P_lower {z : ℝ} (hz : z∈Icc 0 frameCap) : (3/2000:ℝ)<aeval z P := by
  have hh := P_antitone hz (by norm_num [frameCap]) hz.2
  have he : (3/2000:ℝ)<aeval (7/10:ℝ) P := by
    have h1 : ((3/2000:ℚ):ℝ)<((P.eval (7/10):ℚ):ℝ) := Rat.cast_lt.mpr endpoint_reserve
    have h2 := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℝ) (7/10:ℚ) P
    simp only [eq_ratCast] at h2
    have h3 : ((7/10:ℚ):ℝ)=7/10 := by norm_num
    have h4 : ((3/2000:ℚ):ℝ)=3/2000 := by norm_num
    rw [h3] at h2
    rw [h2,← h4]
    exact h1
  simpa only [frameCap] using he.trans_le hh

theorem H_lower {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (3/2000)*z≤aeval z H ∧ (0<z → (3/2000)*z<aeval z H) := by
  have hid := congrArg (fun p : ℚ[X] => aeval z p) factor_identity
  simp only [map_mul,aeval_X] at hid
  have hP := P_lower hz
  rw [hid]
  refine ⟨by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hP.le)],?_⟩
  intro hzpos
  nlinarith [mul_pos hzpos (sub_pos.mpr hP)]

end PositivePolynomial

theorem positive_harmonic_identity (z : ℝ) :
    positivePrimaryScalar z etaLower-kappa*etaError*z=
      (1-kappa*etaError)*z+kappa*
        (etaLower*(1-Real.cos z)+(1/2)*Real.sin (2*z)-sineCoefficient*Real.sin z-
          Real.sin (3*z)/(8*positiveRadius)-
          etaLower/(2*positiveRadius)*(1-Real.cos (2*z))) := by
  dsimp [positivePrimaryScalar,sineCoefficient,kappa,etaLower,etaError,positiveRadius]
  rw [Real.sin_two_mul,Real.sin_three_mul,Real.cos_two_mul]
  linear_combination (-(103/100)*(39921/100000)/(1979/1000):ℝ)*Real.sin_sq_add_cos_sq z

theorem positive_polynomial_transfer {z : ℝ} (hz : 0≤z) :
    Polynomial.aeval z PositivePolynomial.H≤
      positivePrimaryScalar z etaLower-kappa*etaError*z := by
  rw [PositivePolynomial.H_eval,positive_harmonic_identity]
  have hc := Arithmetic.cos_le_cos8 hz
  have hs2 := HighOrderTaylor.S11_le_sin (show 0≤2*z by linarith)
  have hs := Arithmetic.sin_le_sin9 hz
  have hs3 := Arithmetic.sin_le_sin9 (show 0≤3*z by linarith)
  have hc2 := Arithmetic.cos10_le_cos (show 0≤2*z by linarith)
  dsimp [kappa,etaLower,etaError,sineCoefficient,positiveRadius]
  norm_num
  linarith only [hc,hs2,hs,hs3,hc2]

theorem positive_eta_transfer {z e : ℝ} (hz : z∈Icc 0 frameCap)
    (he : e∈Icc etaLower (etaLower+etaError)) :
    positivePrimaryScalar z etaLower-kappa*etaError*z≤positivePrimaryScalar z e := by
  obtain ⟨δ,hδdef⟩ : ∃ δ,δ=e-etaLower := ⟨_,rfl⟩
  have hδ : 0≤δ := by rw [hδdef]; linarith [he.1]
  have hδu : δ≤etaError := by rw [hδdef]; linarith [he.2]
  have tr := transport_trig hz
  have hsin := Real.sin_le hz.1
  have hc := Real.cos_le_one z
  have hs1 := Real.sin_le_one z
  have hsquare : (Real.sin z)^2≤z := by
    nlinarith [mul_nonneg tr.2.2.1 (sub_nonneg.mpr hs1)]
  have hfirst := mul_nonneg hδ (sub_nonneg.mpr hc)
  have hsecond := mul_nonneg (mul_nonneg hδ tr.2.2.1)
    (show 0≤e+etaLower by dsimp [etaLower] at he ⊢; linarith [he.1])
  have hthird := mul_le_mul_of_nonneg_left hsquare hδ
  have hfourth := mul_le_mul_of_nonneg_right hδu hz.1
  have hid : positivePrimaryScalar z e-positivePrimaryScalar z etaLower=
      kappa*δ*((1-Real.cos z)+Real.sin z*(e+etaLower-2*Real.sin z)/(2*positiveRadius)) := by
    dsimp [positivePrimaryScalar]
    rw [hδdef]
    ring
  dsimp [kappa,positiveRadius,etaError] at *
  norm_num at hid
  linarith only [hid,hfirst,hsecond,hthird,hfourth,hz.1]

/-- The scalar is strictly positive away from zero on the complete
frame interval, for the actual original diagonal constant. -/
theorem positive_primary_scalar {z : ℝ} (hz : z∈Icc 0 frameCap) :
    (3/2000)*z≤positivePrimaryScalar z (FramePair.c0-1/2) ∧
      (0<z → (3/2000)*z<positivePrimaryScalar z (FramePair.c0-1/2)) := by
  have he : FramePair.c0-1/2∈Icc etaLower (etaLower+etaError) := by
    dsimp [etaLower,etaError]
    exact ⟨by linarith [diagonal_bounds.1],by linarith [diagonal_bounds.2]⟩
  have hpoly := PositivePolynomial.H_lower hz
  have htr := (positive_polynomial_transfer hz.1).trans (positive_eta_transfer hz he)
  exact ⟨hpoly.1.trans htr,fun hpos => (hpoly.2 hpos).trans_le htr⟩

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair FrameCircleArc GlobalZeroSign GlobalOuterAnchor

def positiveLambda (z : ℝ) : ℝ := kappa*(Real.cos z+
  (Real.sin z-(c0-1/2))*Real.sin z/positiveRadius)
def positiveNormBound (z : ℝ) : ℝ := kappa*Real.sin z*
  (1+(Real.sin z-(c0-1/2))^2/(2*positiveRadius^2))

/-- The signed corner `(t.a + 1/2, transverse t + 1/2)` of a state lies in the circle of squared
radius `Q0`, also when the transverse coordinate is negative or zero. -/
theorem signed_target_circle (t : State) :
    (t.a+1/2)^2+(transverse t+1/2)^2≤Q0 := by
  have hc := state_circle t
  cases hsign : t.positive <;>
    simp [transverse,FramePair.sign,hsign] <;> nlinarith [t.b_nonneg]

theorem signed_target_support (t : State) {f g M : ℝ}
    (hM : 0≤M) (hnorm : f^2+g^2≤M^2) :
    f*t.a+g*transverse t≤positiveRadius*M-(f+g)/2 := by
  have hR : 0≤positiveRadius := by norm_num [positiveRadius]
  have hc : normSq (t.a+1/2,transverse t+1/2)≤positiveRadius^2 := by
    have hh := signed_target_circle t
    dsimp [normSq,positiveRadius,Q0] at *
    linarith
  have hs := dot_le_radius (v:=(f,g)) hR hc
  have hN : Real.sqrt (f^2+g^2)≤M := by
    have hsq := Real.sq_sqrt (show 0≤f^2+g^2 by positivity)
    nlinarith [Real.sqrt_nonneg (f^2+g^2)]
  have hmul := mul_le_mul_of_nonneg_left hN hR
  dsimp [dot,vectorLength,normSq] at hs
  linarith

/-- On `[0, frameCap]` the multiplier is positive and at most `kappa`, so its source coefficient
is nonnegative. -/
theorem positiveLambda_bounds {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<positiveLambda z ∧ positiveLambda z≤kappa := by
  have tr := transport_trig hz
  have heL : (399/1000:ℝ)<c0-1/2 := by linarith [diagonal_bounds.1]
  have heU : c0-1/2<(2/5:ℝ) := by linarith [diagonal_bounds.2]
  have hsU : Real.sin z<(13/20:ℝ) := by linarith [tr.2.2.2.1]
  have hprod := mul_nonneg tr.2.2.1 (show 0≤(2/5:ℝ)-(c0-1/2) by linarith)
  have heSin : (3/5)*Real.sin z≤c0-1/2 := by linarith
  have hsmall := mul_nonneg tr.2.2.1 (sub_nonneg.mpr heSin)
  have hcos : Real.cos z+(Real.sin z)^2/2≤1 := by
    nlinarith [sq_nonneg (1-Real.cos z),Real.sin_sq_add_cos_sq z]
  constructor
  · dsimp [positiveLambda,kappa,positiveRadius]
    nlinarith [sq_nonneg (Real.sin z),tr.1]
  · dsimp [positiveLambda,kappa,positiveRadius]
    nlinarith [sq_nonneg (Real.sin z)]

theorem positiveNormBound_nonnegative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤positiveNormBound z := by
  have hs := (transport_trig hz).2.2.1
  dsimp [positiveNormBound,kappa,positiveRadius]
  positivity

theorem positiveNormBound_support (z : ℝ) :
    (positiveLambda z*Real.sin z)^2+
      (kappa-positiveLambda z*Real.cos z)^2≤(positiveNormBound z)^2 := by
  have hu := Real.sin_sq_add_cos_sq z
  have hi : (positiveLambda z*Real.sin z)^2+
      (kappa-positiveLambda z*Real.cos z)^2=
      kappa^2*(Real.sin z)^2+(positiveLambda z-kappa*Real.cos z)^2 := by
    nlinarith [congrArg (fun r : ℝ => (positiveLambda z)^2*r) hu,
      congrArg (fun r : ℝ => kappa^2*r) hu]
  have hr : (positiveNormBound z)^2-
      (kappa^2*(Real.sin z)^2+(positiveLambda z-kappa*Real.cos z)^2)=
      (kappa*Real.sin z*(Real.sin z-(c0-1/2))^2/(2*positiveRadius^2))^2 := by
    dsimp [positiveNormBound,positiveLambda,kappa,positiveRadius]
    ring
  rw [hi]
  nlinarith only [hr,sq_nonneg
    (kappa*Real.sin z*(Real.sin z-(c0-1/2))^2/(2*positiveRadius^2))]

theorem positive_primary_dual_identity (z : ℝ) :
    z+kappa*(c0-1/2)+positiveLambda z*(Real.sin z-(c0-1/2))-
      positiveRadius*positiveNormBound z=positivePrimaryScalar z (c0-1/2) := by
  dsimp [positiveLambda,positiveNormBound,positivePrimaryScalar,positiveRadius]
  ring

/-- The weak primary projection bounds `quarterCharge s (transverse t) z - kappa` below by
`positivePrimaryScalar z (c0 - 1/2)`, for every target, before any sign or radial classification
of it. -/
theorem positive_primary_transfer (s t : State) (hs : s.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a+t.a*Real.sin z-transverse t*Real.cos z) :
    positivePrimaryScalar z (c0-1/2)≤quarterCharge s (transverse t) z-kappa := by
  have hlam := positiveLambda_bounds hz
  have hproj := mul_le_mul_of_nonneg_left hm hlam.1.le
  have hchart := state_outer_chart s hs
  have ha : c0≤ s.a := by simpa only [← hchart.1] using (A_bounds hchart.2).1
  have hsource := mul_nonneg (sub_nonneg.mpr hlam.2) (sub_nonneg.mpr ha)
  have htarget := signed_target_support t (positiveNormBound_nonnegative hz)
    (positiveNormBound_support z)
  have hJ := mul_nonneg (show 0≤rho by norm_num [rho]) (J_nonnegative s hs)
  have hsin := (transport_trig hz).2.2.1
  dsimp [GlobalOuterAnchor.width] at hproj
  rw [abs_of_nonneg hsin] at hproj
  rw [← positive_primary_dual_identity z]
  dsimp [quarterCharge,potential]
  nlinarith only [hproj,hsource,htarget,hJ]

theorem positive_primary_charge (s t : State) (hs : s.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap)
    (hm : GlobalOuterAnchor.width z≤ s.a+t.a*Real.sin z-transverse t*Real.cos z) :
    kappa≤quarterCharge s (transverse t) z ∧
      (0<z → kappa<quarterCharge s (transverse t) z) := by
  have htransfer := positive_primary_transfer s t hs hz hm
  have hscalar := positive_primary_scalar hz
  exact ⟨by linarith [hz.1,hscalar.1],fun hpos => by linarith [hscalar.2 hpos]⟩

end SquaresInCircles.Eight.GlobalAllHigh
end
end
end
