module

public import SquaresInCircles.Eight.TableFree.MiddlePhysicalStress
public import SquaresInCircles.Eight.TableFree.EndpointBudgetScalars

/-!
# The fixed signed middle stress before intermediate order

Uncompiled source draft.  The weight `1 / sqrt (qCap - 1)` makes the
square-root tangent coefficient exactly one.  The resulting scalar bound
retains both signed G/T tangents and the actual A/B circles.  Its two
continuous sign sectors are proved on their full intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.MiddleOrderScalar
open PositiveAngularEnvelope PairNormCalculus MiddleAngularPenalty
open EndpointRotationPenalty EndpointBudgetScalars CorrelatedSameBlock

def r1 : ℝ := Real.sqrt (qCap-1)
def weight : ℝ := 1/r1
def N (t : ℝ) : ℝ := pairNorm 1 weight t
def rateTerm (l t : ℝ) : ℝ := (1-l)*Real.sin t+l*(1-Real.cos t)

theorem r1_pos : 0<r1 := Real.sqrt_pos.mpr (by norm_num [qCap])

theorem r1_sq : r1^2=qCap-1 := Real.sq_sqrt (by norm_num [qCap])

theorem weight_bounds : (7/12 : ℝ)<weight ∧ weight<3/5 := by
  have hh := r1_sq
  have hp := r1_pos
  have hlo : (5/3 : ℝ)<r1 := by dsimp [qCap] at hh; nlinarith
  have hhi : r1<(12/7 : ℝ) := by dsimp [qCap] at hh; nlinarith
  dsimp [weight]
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith
  · apply (div_lt_iff₀ hp).2
    linarith

theorem weight_pos : 0<weight := by linarith [weight_bounds.1]

theorem r1_weight : r1*weight=1 := by
  dsimp [weight]
  field_simp [r1_pos.ne']

theorem norm_zero_identities : R*weight=N 0 ∧ R*N 0=r1+weight := by
  have hN0 : 0≤N 0 := Real.sqrt_nonneg _
  have hN2 : (N 0)^2=1+weight^2 := by
    simpa [N,pairEnergy,pairProduct] using
      pairNorm_sq (show (0:ℝ)<1 by norm_num) weight_pos
        (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hR2 := congrArg (fun z : ℝ => z*weight^2) R_sq
  have hr2 := congrArg (fun z : ℝ => z*weight^2) r1_sq
  have hprod := congrArg (fun z : ℝ => z^2) r1_weight
  have hRlam0 := mul_nonneg R_nonneg weight_pos.le
  have hcoef : R*weight=N 0 := by nlinarith
  refine ⟨hcoef,?_⟩
  have hR := congrArg (fun z : ℝ => z*weight) R_sq
  have hr := congrArg (fun z : ℝ => z*weight) r1_sq
  have hp := congrArg (fun z : ℝ => r1*z) r1_weight
  rw [← hcoef]
  nlinarith

theorem baseline_identity : 2*R*N 0-2*weight-3=S0 := by
  have h := norm_zero_identities.2
  simp only [r1] at h
  simp only [S0]
  linear_combination 2*h

/-- The signed square-root tangent is valid on both sides of zero. -/
theorem norm_tangent {t : ℝ} (ht : |t|≤frameCap) :
    R*(N t-N 0)≤Real.sin t := by
  have hN0 : 0<N 0 := pairNorm_pos (show (0:ℝ)<1 by norm_num) weight_pos
    (by norm_num [frameCap])
  have hN2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) weight_pos ht
  have hZ2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) weight_pos
    (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  change (N t)^2=pairEnergy 1 weight+2*pairProduct 1 weight*Real.sin t at hN2
  change (N 0)^2=pairEnergy 1 weight+2*pairProduct 1 weight*Real.sin 0 at hZ2
  simp only [pairEnergy,pairProduct,one_pow,one_mul,Real.sin_zero,mul_zero,add_zero] at hN2 hZ2
  have htan : N 0*(N t-N 0)≤weight*Real.sin t := by
    nlinarith [sq_nonneg (N t-N 0)]
  have hm := mul_le_mul_of_nonneg_left htan R_nonneg
  have hc := congrArg (fun z : ℝ => z*Real.sin t) norm_zero_identities.1
  refine le_of_mul_le_mul_left ?_ hN0
  linarith

theorem cosine_loss_linear {t : ℝ} (ht : t∈Icc 0 frameCap) :
    1-Real.cos t≤(7/20)*t := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have htprod := mul_nonneg ht.1 (show 0≤7/10-t by dsimp [frameCap] at ht; linarith [ht.2])
  nlinarith

theorem short_half_charge {t : ℝ} (ht : t∈Icc 0 frameCap) :
    19*(1-Real.cos t)≤7*Real.sin t := by
  have h2 : t≤7/10 := ht.2
  have hh : t/2∈Icc 0 (frameCap/2) :=
    ⟨by linarith [ht.1],by show t/2≤7/10/2; linarith⟩
  obtain ⟨hc,hs0,hs⟩ := half_trig hh
  have hp := mul_nonneg (show 0≤2*Real.sin (t/2) by linarith)
    (show 0≤7*Real.cos (t/2)-19*Real.sin (t/2) by linarith)
  have hcos : Real.cos t-1= -2*(Real.sin (t/2))^2 := by
    simpa only [show 2*(t/2)=t by ring] using cosine_double_shift (t/2)
  have hsin : Real.sin t=2*Real.sin (t/2)*Real.cos (t/2) := by
    have h := Real.sin_two_mul (t/2)
    rwa [show 2*(t/2)=t by ring] at h
  nlinarith

theorem rate_derivative {l t : ℝ} :
    HasDerivAt (rateTerm l) ((1-l)*Real.cos t+l*Real.sin t) t := by
  have h : HasDerivAt (fun y => (1-l)*Real.sin y+l*(1-Real.cos y))
      ((1-l)*Real.cos t+l*(0- -Real.sin t)) t :=
    ((Real.hasDerivAt_sin t).const_mul (1-l)).add
      (((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)).const_mul l)
  have e : (1-l)*Real.cos t+l*(0- -Real.sin t)=(1-l)*Real.cos t+l*Real.sin t := by ring
  rw [e] at h
  exact h

theorem rate_upper {l t : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5)) :
    (1-l)*Real.cos t+l*Real.sin t≤3/4 := by
  have hp : 0≤1-l := by linarith [hl.2]
  have hpu : 1-l≤5/12 := by linarith [hl.1]
  have hl0 : 0≤l := by linarith [hl.1]
  have hp2 := pow_le_pow_left₀ hp hpu 2
  have hl2 := pow_le_pow_left₀ hl0 hl.2 2
  have hid : ((1-l)*Real.cos t+l*Real.sin t)^2+
      ((1-l)*Real.sin t-l*Real.cos t)^2=(1-l)^2+l^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t,
      congrArg (fun z : ℝ => (1-l)^2*z) (Real.sin_sq_add_cos_sq t),
      congrArg (fun z : ℝ => l^2*z) (Real.sin_sq_add_cos_sq t)]
  nlinarith [sq_nonneg ((1-l)*Real.sin t-l*Real.cos t)]

theorem rate_growth {l a b : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5))
    (ha : a∈Icc 0 frameCap) (hb : b∈Icc 0 frameCap) (hab : a≤b) :
    rateTerm l b-rateTerm l a≤(3/4)*(b-a) := by
  have hh := derivative_reserve
    (f := fun t => -rateTerm l t)
    (df := fun t => -((1-l)*Real.cos t+l*Real.sin t))
    (k := -(3/4 : ℝ))
    (fun t ht => (rate_derivative (l := l) (t := t)).neg.continuousAt.continuousWithinAt)
    (fun t ht => (rate_derivative (l := l) (t := t)).neg)
    (fun t ht => by linarith [rate_upper (t := t) hl]) ha hb hab
  linarith

theorem cosine_loss_growth {a b : ℝ}
    (ha : a∈Icc 0 frameCap) (hb : b∈Icc 0 frameCap) (hab : a≤b) :
    Real.cos a-Real.cos b≤(13/20)*(b-a) := by
  have hh := derivative_reserve (f := Real.cos) (df := fun t => -Real.sin t)
    (k := -(13/20 : ℝ)) Real.continuous_cos.continuousOn
    (fun t ht => Real.hasDerivAt_cos t)
    (fun t ht => by
      have hs := (transport_trig (Ioo_subset_Icc_self ht)).2.2.2.1
      linarith) ha hb hab
  linarith

/-- A is at or below T.  The signed A--G error may be negative. -/
theorem positive_sector {l x s : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5))
    (hx : |x|≤frameCap) (hs : s∈Icc 0 frameCap) (hr : 0≤x+s) :
    Real.sin x-psi x+Real.sin s-l*(PositiveAngularEnvelope.phi s-1)≤(3/4)*(x+s) := by
  have hl0 : 0≤l := by linarith [hl.1]
  have hl1 : 0≤1-l := by linarith [hl.2]
  by_cases hx0 : 0≤x
  · have hx' : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans hx⟩
    have hcx := cosine_loss_linear hx'
    have hcs := mul_le_mul_of_nonneg_left (cosine_loss_linear hs) hl0
    have hss := mul_le_mul_of_nonneg_left (Real.sin_le hs.1) hl1
    have hlam := mul_nonneg (show 0≤l-7/12 by linarith [hl.1]) hs.1
    rw [psi_positive hx']
    dsimp [PositiveAngularEnvelope.phi]
    nlinarith
  · have hv : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hratio := short_half_charge hv
    have hsin0 := (transport_trig hv).2.2.1
    have hC0 : 0≤1-Real.cos (-x) := by linarith [Real.cos_le_one (-x)]
    have hbase : (1+l)*(1-Real.cos (-x))-l*Real.sin (-x)≤0 := by
      have hratio' := mul_le_mul_of_nonneg_left hratio (show 0≤1+l by linarith [hl.1])
      have hmore := mul_nonneg (show 0≤12*l-7 by linarith [hl.1]) hsin0
      nlinarith
    have hgrowth := rate_growth hl hv hs (by linarith)
    have hpsi : psi x=Real.cos (-x)-1 := by
      simpa only [neg_neg] using psi_negative hv
    rw [hpsi]
    dsimp [rateTerm,PositiveAngularEnvelope.phi] at hgrowth ⊢
    simp only [Real.sin_neg,Real.cos_neg] at hbase hgrowth ⊢
    linarith

/-- A lies above T.  The remaining difference is exactly a cosine loss. -/
theorem negative_sector {x s : ℝ}
    (hx : |x|≤frameCap) (hs : -s∈Icc 0 frameCap) (hr : 0≤x+s) :
    Real.sin x-psi x+Real.sin s-(1-PositiveAngularEnvelope.phi (-s))≤(3/4)*(x+s) := by
  have hx0 : 0≤x := by linarith [hs.1]
  have hx' : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans hx⟩
  have hgrowth := cosine_loss_growth hs hx' (by linarith)
  rw [psi_positive hx']
  dsimp [PositiveAngularEnvelope.phi]
  simp only [Real.sin_neg,Real.cos_neg] at hgrowth ⊢
  linarith

theorem raw_zero {G A B T : SignedPoint} {x d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap)
    (hyA : 0≤A.y) (hyB : B.y≤0)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hs : |d+v|≤frameCap)
    (hGA : quarterFeasible G A x 0) (hAB : zeroFeasible A B d 0)
    (hBT : quarterFeasible B T v 2) :
    -G.y+T.y≤S0+(Real.sin x-psi x)+Real.sin (d+v)-weight*psi d-psi v := by
  have hcA : A.Contained (R^2) := by
    show A.circle≤R^2
    rw [R_sq]; exact hA
  have hcB : B.Contained (R^2) := by
    show B.circle≤R^2
    rw [R_sq]; exact hB
  have hraw := MiddlePhysicalStress.signed_three_zero R_nonneg hcA hcB hyA hyB
    (by norm_num : (0:ℝ)≤1) weight_pos.le (by norm_num : (0:ℝ)≤1)
    hx hd hv hGA hAB hBT
  have hnx := norm_tangent hx
  have hns := norm_tangent hs
  change -1*G.y+1*T.y≤R*(N x+N (d+v))-
    (1+1)/2-weight-1*(1+psi x)-weight*(1+psi d)-1*(1+psi v) at hraw
  linarith [baseline_identity]

end SquaresInCircles.Eight.TableFree.MiddleOrderScalar
