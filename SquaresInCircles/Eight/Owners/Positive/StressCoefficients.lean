module

public import SquaresInCircles.Eight.Owners.SecondaryEStress

/-!
# Eight squares: whole-interval coefficient bounds for the positive-primary stresses

Every terminating decimal is an exact rational.
The correlated coefficient bounds are polynomial inequalities on the full
interval, and the tilted coefficient bounds use analytic Taylor bounds.
There is no angular partition or list of sampled values.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.PositiveStressCoefficients
open SecondaryEStress

def k : ℝ := 863/1000
def lP (d : ℝ) : ℝ := 1263/2500+49/100*d-27/250*d^2
def etaP (d : ℝ) : ℝ := 1/4+329/2000*d
def lN (d : ℝ) : ℝ := 2527/5000+11/20*d-1/5*d^2
def cN (d : ℝ) : ℝ := 863/1000+7/20*d-3/20*d^2
def lambdaN (d : ℝ) : ℝ := 1111/1250+1/5*d
def ratio (d : ℝ) : ℝ := 117/200+51/200*d

theorem coefficient_bounds {d : ℝ} (hd : d∈Icc 0 frameCap) :
    1/2<lP d ∧ lP d<k ∧ 1/2<lN d ∧ lN d<k ∧
    k≤cN d ∧ cN d≤2069/2000 ∧
    1/4≤etaP d ∧ etaP d≤7303/20000 ∧
    117/200≤ratio d ∧ ratio d≤1527/2000 := by
  have hd' : 0≤d ∧ d≤7/10 := hd
  have hd2 : d^2≤(7/10 : ℝ)*d := by nlinarith [hd'.1,hd'.2]
  have hLP : lP d≤lP (7/10) := by
    have h := mul_nonneg (show 0≤(7/10 : ℝ)-d by linarith)
      (show 0≤49/100-(27/250 : ℝ)*(d+7/10) by linarith)
    dsimp [lP]
    nlinarith
  have hLN : lN d≤lN (7/10) := by
    have h := mul_nonneg (show 0≤(7/10 : ℝ)-d by linarith)
      (show 0≤11/20-(1/5 : ℝ)*(d+7/10) by linarith)
    dsimp [lN]
    nlinarith
  have hCN : cN d≤cN (7/10) := by
    have h := mul_nonneg (show 0≤(7/10 : ℝ)-d by linarith)
      (show 0≤7/20-(3/20 : ℝ)*(d+7/10) by linarith)
    dsimp [cN]
    nlinarith
  dsimp [lP,lN,cN,etaP,ratio,k] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- These are the two correlated comparisons (18) in the angular note.
The small reserves are strict already at the endpoint d=0. -/
theorem correlated_ratios {d : ℝ} (hd : d∈Icc 0 frameCap) :
    43/125000<lP d-ratio d*k*(1+d/4) ∧
      68/125000<lN d-ratio d*cN d := by
  have hd' : 0≤d ∧ d≤7/10 := hd
  have hd2 : d^2≤(7/10 : ℝ)*d := by nlinarith [hd'.1,hd'.2]
  constructor
  · dsimp [lP,ratio,k]
    nlinarith
  · have hfactor : 0≤
        d*((125185/1000000 : ℝ)-(403/2000 : ℝ)*d+(153/4000 : ℝ)*d^2) := by
      apply mul_nonneg hd'.1
      have h := mul_nonneg (show 0≤(7/10 : ℝ)-d by linarith)
        (show 0≤(403/2000 : ℝ)-(153/4000 : ℝ)*(d+7/10) by linarith)
      nlinarith
    dsimp [lN,ratio,cN]
    nlinarith

private def lowerFactor (x : ℝ) : ℝ :=
  1/4-671/2000*x-x^2/24+57/4000*x^3+x^4/480-
    13/720000*x^5-x^6/20160-329/10080000*x^7

private def lowerFactorDeriv (x : ℝ) : ℝ :=
  -671/2000-x/12+171/4000*x^2+x^3/120-
    13/144000*x^4-x^5/3360-329/1440000*x^6

private theorem lowerFactor_hasDerivAt (x : ℝ) :
    HasDerivAt lowerFactor (lowerFactorDeriv x) x := by
  have h := (((((((hasDerivAt_const x (1/4 : ℝ)).fun_sub
    ((hasDerivAt_id' (x := x)).const_mul (671/2000 : ℝ))).fun_sub
      ((hasDerivAt_pow 2 x).div_const 24)).fun_add
      ((hasDerivAt_pow 3 x).const_mul (57/4000 : ℝ))).fun_add
      ((hasDerivAt_pow 4 x).div_const 480)).fun_sub
      ((hasDerivAt_pow 5 x).const_mul (13/720000 : ℝ))).fun_sub
      ((hasDerivAt_pow 6 x).div_const 20160)).fun_sub
      ((hasDerivAt_pow 7 x).const_mul (329/10080000 : ℝ))
  refine h.congr_deriv ?_
  norm_num [lowerFactorDeriv]
  ring

private theorem lowerFactor_pos {x : ℝ} (hx : x∈Icc 0 frameCap) :
    0<lowerFactor x := by
  have hm : AntitoneOn lowerFactor (Icc 0 frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact (by unfold lowerFactor; fun_prop : Continuous lowerFactor).continuousOn
    · intro t _
      exact lowerFactor_hasDerivAt t
    · intro t ht
      have ht0 : 0≤t := ht.1.le
      have ht7 : t≤7/10 := ht.2.le
      have h2 := pow_le_pow_left₀ ht0 ht7 2
      have h3 := pow_le_pow_left₀ ht0 ht7 3
      have h4 := pow_nonneg ht0 4
      have h5 := pow_nonneg ht0 5
      have h6 := pow_nonneg ht0 6
      dsimp [lowerFactorDeriv]
      nlinarith
  have h := hm hx ⟨by norm_num [frameCap],le_rfl⟩ hx.2
  have he : 0<lowerFactor frameCap := by norm_num [lowerFactor,frameCap]
  exact he.trans_le h

/-- The small positive endpoint reserve in the tilted weight is proved
analytically, including the correlated case x=d=7/10. -/
theorem tiltedFactor_lower {d x : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) :
    1≤Real.cos x+etaP d*Real.sin x := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hd.2⟩
  have hp := lowerFactor_pos hx'
  have hs := sin_lower_seven hx.1
  have hc := cos_lower_six hx.1
  have heta : 0≤etaP x := by dsimp [etaP]; linarith [hx.1]
  have hsin : 0≤Real.sin x := (transport_trig hx').2.2.1
  have hmul := mul_le_mul_of_nonneg_left hs heta
  have hpoly :
      (1-x^2/2+x^4/24-x^6/720)+
        etaP x*(x-x^3/6+x^5/120-x^7/5040)-1=x*lowerFactor x := by
    dsimp [etaP,lowerFactor]
    ring
  have hpos := mul_nonneg hx.1 hp.le
  have hbase : 1≤Real.cos x+etaP x*Real.sin x := by nlinarith
  have hetaxd : etaP x≤etaP d := by dsimp [etaP]; linarith [hx.2]
  linarith [mul_le_mul_of_nonneg_right hetaxd hsin]

theorem tiltedFactor_upper {d x : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) :
    Real.cos x+etaP d*Real.sin x≤1+d/4 := by
  have hx' : x∈Icc 0 frameCap := ⟨hx.1,hx.2.trans hd.2⟩
  have hx7 : x≤7/10 := hx'.2
  have hx2 : x^2≤(7/10 : ℝ)^2 := pow_le_pow_left₀ hx.1 hx7 2
  have hx4 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
  have hc := cos_upper_four hx.1
  have hcu : Real.cos x≤1-(479/1000 : ℝ)*x^2 := by nlinarith
  have hs : Real.sin x≤x := Real.sin_le hx.1
  have heta : 0≤etaP d := by dsimp [etaP]; linarith [hd.1]
  have hmul := mul_le_mul_of_nonneg_left hs heta
  have hprod := mul_nonneg (sub_nonneg.mpr hx.2)
    (show 0≤(1/4 : ℝ)-(329/2000 : ℝ)*x by linarith)
  dsimp [etaP] at *
  nlinarith [sq_nonneg x]

theorem tiltedWeight_bounds {d x : ℝ} (hd : d∈Icc 0 frameCap)
    (hx : x∈Icc 0 d) :
    k≤tiltedWeight k (etaP d) x ∧
      tiltedWeight k (etaP d) x≤k*(1+d/4) := by
  have hk : 0≤k := by norm_num [k]
  constructor
  · simpa [tiltedWeight] using mul_le_mul_of_nonneg_left (tiltedFactor_lower hd hx) hk
  · exact mul_le_mul_of_nonneg_left (tiltedFactor_upper hd hx) hk

/-- The actual varying B coefficient has the ratio used by the full-angle
comparison; no independent coefficient box discards its correlation with d. -/
theorem varying_B_ratio {d z : ℝ} (hd : d∈Icc 0 frameCap)
    (hz : z∈Icc 0 d) :
    ratio d*tiltedWeight k (etaP d) z<lP d ∧ ratio d*cN d<lN d := by
  have h := correlated_ratios hd
  have hr : 0≤ratio d := by dsimp [ratio]; linarith [hd.1]
  have hw := mul_le_mul_of_nonneg_left (tiltedWeight_bounds hd hz).2 hr
  constructor <;> nlinarith

end SquaresInCircles.Eight.PositiveStressCoefficients
