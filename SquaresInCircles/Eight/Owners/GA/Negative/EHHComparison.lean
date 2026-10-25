module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2PositiveSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHGain

/-!
# Eight squares: the original H block with the far EH multiplier

The multiplier is varied only inside a proved scalar comparison. The
original HG argument and its original H witness are kept throughout.
The mixed radial/angular derivative is bounded on the complete rectangle;
its two integrations give precisely the `.005 t` allowance.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEH.HComparison
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus
open OrdinaryAngleConcavity NegativeAPositiveTD.PositiveSlope

abbrev A : ℝ := p*(129/200)
def baseRoot (k : ℝ) : ℝ := Real.sqrt (1+k^2)
def ratio (k : ℝ) : ℝ := k^2*(k+A)/(baseRoot k)^3
def mixed (k r t : ℝ) : ℝ :=
  R*k^2*Real.cos t*(k+r*Real.sin t)/(pairNorm k r t)^3

theorem radial_norm_derivative {k r t : ℝ} (hk : 0<k) (hr : 0<r)
    (ht : |t|≤frameCap) :
    HasDerivAt (fun r => pairNorm k r t)
      ((r+k*Real.sin t)/pairNorm k r t) r := by
  have hpos := pair_radicand_pos hk hr ht
  have hs : 0<Real.sqrt (k^2+r^2+2*k*r*Real.sin t) := Real.sqrt_pos.mpr hpos
  have h2 : HasDerivAt (fun r : ℝ => r^2) (2*r) r := by simpa using hasDerivAt_pow 2 r
  have h3 : HasDerivAt (fun r : ℝ => 2*k*r*Real.sin t) (2*k*Real.sin t) r := by
    simpa using ((hasDerivAt_id r).const_mul (2*k)).mul_const (Real.sin t)
  have h1 : HasDerivAt (fun r => k^2+r^2+2*k*r*Real.sin t) (2*r+2*k*Real.sin t) r :=
    (h2.const_add (k^2)).fun_add h3
  have hh : HasDerivAt (fun r => pairNorm k r t)
      ((2*r+2*k*Real.sin t)/(2*Real.sqrt (k^2+r^2+2*k*r*Real.sin t))) r :=
    h1.sqrt hpos.ne'
  refine hh.congr_deriv ?_
  unfold pairNorm
  field_simp

theorem mixed_derivative {k r t : ℝ} (hk : 0<k) (hr : 0<r)
    (ht : |t|≤frameCap) :
    HasDerivAt (fun r => Ud k r t) (-mixed k r t) r := by
  have hn := pairNorm_pos hk hr ht
  have hn2 := pairNorm_sq hk hr ht
  have hh := (hasDerivAt_const r (k*(Real.cos t-Real.sin t))).sub
    ((((hasDerivAt_id r).const_mul (R*k*Real.cos t)).div
      (radial_norm_derivative hk hr ht) hn.ne'))
  convert hh using 1
  · funext x
    dsimp [Ud,mixedPDerivative,normD1,pairProduct]
    simp only [sub_zero]
    ring
  · dsimp [mixed,pairEnergy,pairProduct] at hn2 ⊢
    field_simp [hn.ne']
    nlinarith [congrArg (fun z : ℝ => R*k*Real.cos t*z) hn2]

theorem baseRoot_data (k : ℝ) :
    0<baseRoot k ∧ (baseRoot k)^2=1+k^2 := by
  have hh : 0<1+k^2 := by positivity
  exact ⟨Real.sqrt_pos.mpr hh,Real.sq_sqrt hh.le⟩

theorem baseRoot_derivative (k : ℝ) :
    HasDerivAt baseRoot (k/baseRoot k) k := by
  have hh := ((hasDerivAt_const k (1:ℝ)).add ((hasDerivAt_id k).pow 2)).sqrt
    (by positivity : 1+k^2≠0)
  convert hh using 1
  · rfl
  · dsimp [baseRoot]
    ring

theorem ratio_derivative (k : ℝ) :
    HasDerivAt ratio (k*(3*k+2*A-A*k^2)/(baseRoot k)^5) k := by
  have hn := baseRoot_data k
  have hB : baseRoot k≠0 := hn.1.ne'
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*k) k := by simpa using hasDerivAt_pow 2 k
  have h1 : HasDerivAt (fun x : ℝ => x^2*(x+A)) (2*k*(k+A)+k^2*1) k :=
    h2.fun_mul ((hasDerivAt_id' k).add_const A)
  have h3 : HasDerivAt (fun x => baseRoot x^3) (3*baseRoot k*k) k := by
    refine ((baseRoot_derivative k).fun_pow 3).congr_deriv ?_
    norm_num
    field_simp
  have hh : HasDerivAt ratio (((2*k*(k+A)+k^2*1)*baseRoot k^3-k^2*(k+A)*(3*baseRoot k*k))/
      (baseRoot k^3)^2) k :=
    h1.fun_div h3 (pow_ne_zero 3 hB)
  refine hh.congr_deriv ?_
  rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hB)) (pow_ne_zero _ hB)]
  linear_combination (baseRoot k)^6*(3*k^2+2*A*k)*hn.2

theorem ratio_monotone : MonotoneOn ratio (Icc (3/5:ℝ) (4/5)) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun k _ => (ratio_derivative k).continuousAt.continuousWithinAt)
    (fun k _ => ratio_derivative k)
  intro k hk
  have hk0 : 0≤k := by linarith [hk.1]
  have hk2 : k^2≤(4/5:ℝ)^2 := by nlinarith [hk.2]
  have hnum : 0≤3*k+2*A-A*k^2 := by dsimp [A,p]; nlinarith
  exact div_nonneg (mul_nonneg hk0 hnum) (pow_nonneg (baseRoot_data k).1.le 5)

theorem ratio_endpoint : R*ratio (4/5)<1 := by
  have hn := baseRoot_data (4/5)
  have hR : 0<R := by linarith [radius_bounds.1]
  have hp : ((baseRoot (4/5))^3)^2=(1+(4/5:ℝ)^2)^3 := by
    rw [← pow_mul,show (3:ℕ)*2=2*3 by norm_num,pow_mul,hn.2]
  have hnum : (R*(4/5:ℝ)^2*((4/5:ℝ)+A))^2<((baseRoot (4/5))^3)^2 := by
    rw [mul_pow,mul_pow,radius_sq,hp]
    norm_num [A,p,qCap]
  have hh : R*(4/5:ℝ)^2*((4/5:ℝ)+A)<(baseRoot (4/5))^3 := by
    have hright := pow_pos hn.1 3
    nlinarith
  unfold ratio
  rw [← mul_div_assoc]
  exact (div_lt_one (pow_pos hn.1 3)).2 (by nlinarith only [hh])

theorem mixed_bound {k r t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (hr : r∈Icc 1 p) (ht : t∈Icc 0 frameCap) : mixed k r t<1 := by
  have hk0 : 0<k := by linarith [hk.1]
  have hr0 : 0<r := by linarith [hr.1]
  have htf : |t|≤frameCap := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hn := pairNorm_pos hk0 hr0 htf
  have hn2 := pairNorm_sq hk0 hr0 htf
  have hb := baseRoot_data k
  have htrig := transport_trig ht
  have hroot : baseRoot k≤pairNorm k r t := by
    have hprod : 0≤2*k*r*Real.sin t := by
      have := mul_nonneg (mul_nonneg hk0.le hr0.le) htrig.2.2.1
      linarith
    dsimp [pairEnergy,pairProduct] at hn2
    nlinarith [hr.1]
  have hs : r*Real.sin t≤A := by
    have hh := mul_le_mul hr.2
      (show Real.sin t≤(129/200:ℝ) by linarith [htrig.2.2.2.1])
      htrig.2.2.1 (by norm_num [p] : (0:ℝ)≤p)
    exact hh
  have hR : 0≤R := Real.sqrt_nonneg _
  have hnum : R*k^2*Real.cos t*(k+r*Real.sin t)≤R*k^2*(k+A) := by
    have hfactor : 0≤k+r*Real.sin t := by
      have := mul_nonneg hr0.le htrig.2.2.1
      linarith
    have hcos := mul_le_mul_of_nonneg_right htrig.2.1 hfactor
    have hh := mul_le_mul_of_nonneg_left hcos (show 0≤R*k^2 by positivity)
    have hh' := mul_le_mul_of_nonneg_left hs (show 0≤R*k^2 by positivity)
    nlinarith only [hh,hh']
  have hquot := div_le_div₀
    (mul_nonneg (mul_nonneg hR (sq_nonneg k)) (by dsimp [A,p]; linarith : 0≤k+A))
    hnum (pow_pos hb.1 3) (pow_le_pow_left₀ hb.1.le hroot 3)
  have hm := mul_le_mul_of_nonneg_left
    (ratio_monotone hk (by norm_num) hk.2) hR
  have hh : mixed k r t≤R*ratio k := by
    have he : R*ratio k=R*k^2*(k+A)/(baseRoot k)^3 := by unfold ratio; ring
    rw [he]
    exact hquot
  exact (hh.trans hm).trans_lt ratio_endpoint

/-- Integration in the EH multiplier, at a fixed original HG angle. -/
theorem positive_slope_comparison {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) : Ud k 1 t-epsilon≤Ud k p t := by
  have hk0 : 0<k := by linarith [hk.1]
  have htf : |t|≤frameCap := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hd (r : ℝ) (hr : r∈Icc 1 p) :=
    mixed_derivative hk0 (show 0<r by linarith [hr.1]) htf
  have hh := derivative_reserve
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => hd r (Ioo_subset_Icc_self hr))
    (fun r hr => by linarith [mixed_bound hk (Ioo_subset_Icc_self hr) ht])
    (show (1:ℝ)∈Icc 1 p by norm_num [p])
    (show p∈Icc 1 p by norm_num [p]) (show (1:ℝ)≤p by norm_num [p])
    (k:=(-1:ℝ))
  dsimp [p,epsilon] at hh ⊢
  linarith

/-- Integration in the original HG angle: the exact allowance is `.005 t`. -/
theorem positive {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) :
    U R k 1 t-epsilon*t≤U R k p t := by
  have hk0 : 0<k := by linarith [hk.1]
  have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :
      HasDerivAt (fun x => U R k p x-U R k 1 x+epsilon*x)
        (Ud k p x-Ud k 1 x+epsilon) x := by
    have h1 := U_hasDerivAt (q:=p) hk0 (by norm_num [p]) hx
    have h2 := U_hasDerivAt (q:=1) hk0 (by norm_num) hx
    have h3 : HasDerivAt (fun x : ℝ => epsilon*x) epsilon x := by
      simpa using (hasDerivAt_id x).const_mul epsilon
    exact (h1.fun_sub h2).fun_add h3
  have hm : MonotoneOn (fun x => U R k p x-U R k 1 x+epsilon*x)
      (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
    intro x hx
    linarith [positive_slope_comparison hk (Ioo_subset_Icc_self hx)]
  have hh := hm (by norm_num [frameCap]) ht ht.1
  simp only [U_zero,mul_zero,sub_self,zero_add] at hh
  linarith

theorem negative_norm_derivative_nonneg {k r t : ℝ}
    (hk : k∈Icc (3/5:ℝ) (4/5)) (hr : r∈Icc 1 p)
    (ht : t∈Icc 0 frameCap) :
    0≤r/pairNorm k r 0-(r-k*Real.sin t)/pairNorm k r (-t) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hr0 : 0<r := by linarith [hr.1]
  have ht0 : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have htn : |-t|≤frameCap := by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2
  have hn0 := pairNorm_pos hk0 hr0 ht0
  have hnn := pairNorm_pos hk0 hr0 htn
  have hn02 := pairNorm_sq hk0 hr0 ht0
  have hnn2 := pairNorm_sq hk0 hr0 htn
  simp only [Real.sin_zero,Real.sin_neg,mul_zero,add_zero] at hn02 hnn2
  dsimp [pairEnergy,pairProduct] at hn02 hnn2
  have htrig := transport_trig ht
  have hS : Real.sin t≤(129/200:ℝ) := by linarith [htrig.2.2.2.1]
  have hk2 : k^2≤(4/5:ℝ)^2 := by nlinarith [hk.2]
  have hr2 : r^2≤p^2 := by nlinarith [hr.2]
  have hkr : (3/5:ℝ)≤k*r := by nlinarith [hr.1,hk.1]
  norm_num only [p] at hr2
  have hm := mul_le_mul (show k^2+r^2≤(4/5:ℝ)^2+(201/200)^2 by linarith)
    hS htrig.2.2.1 (by norm_num : (0:ℝ)≤(4/5)^2+(201/200)^2)
  have hf : 0≤2*k*r-(k^2+r^2)*Real.sin t := by
    nlinarith
  have hdiff : 0≤(r*pairNorm k r (-t))^2-
      ((r-k*Real.sin t)*pairNorm k r 0)^2 := by
    have hh := mul_nonneg (mul_nonneg (sq_nonneg k) htrig.2.2.1) hf
    rw [mul_pow,mul_pow,hnn2,hn02]
    nlinarith only [hh]
  have hright : 0≤r*pairNorm k r (-t) := by positivity
  have hcross : (r-k*Real.sin t)*pairNorm k r 0≤r*pairNorm k r (-t) := by
    nlinarith
  have hh := (div_le_div_iff₀ hnn hn0).2 hcross
  linarith

theorem negative_norm_gain {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) :
    pairNorm k 1 0-pairNorm k 1 (-t)≤pairNorm k p 0-pairNorm k p (-t) := by
  have hk0 : 0<k := by linarith [hk.1]
  have ht0 : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have htn : |-t|≤frameCap := by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2
  have hd (r : ℝ) (hr : r∈Icc 1 p) :
      HasDerivAt (fun r => pairNorm k r 0-pairNorm k r (-t))
        (r/pairNorm k r 0-(r-k*Real.sin t)/pairNorm k r (-t)) r := by
    have hr0 : 0<r := by linarith [hr.1]
    simpa only [Real.sin_zero,Real.sin_neg,mul_zero,add_zero,mul_neg,← sub_eq_add_neg]
      using (radial_norm_derivative hk0 hr0 ht0).fun_sub
        (radial_norm_derivative hk0 hr0 htn)
  have hm : MonotoneOn (fun r => pairNorm k r 0-pairNorm k r (-t)) (Icc 1 p) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr => hd r (Ioo_subset_Icc_self hr))
    intro r hr
    exact negative_norm_derivative_nonneg hk (Ioo_subset_Icc_self hr) ht
  exact hm (by norm_num [p]) (by norm_num [p]) (by norm_num [p])

/-- The negative HG force has its actual coefficient `k` in the cosine term. -/
theorem negative {k t : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5))
    (ht : t∈Icc 0 frameCap) :
    V R k 1 t≤k*(Real.cos t-1)-R*(pairNorm k p (-t)-pairNorm k p 0) := by
  have hg := mul_le_mul_of_nonneg_left (negative_norm_gain hk ht) (Real.sqrt_nonneg qCap)
  have hc := mul_le_mul_of_nonpos_right (show k≤(1:ℝ) by linarith [hk.2])
    (sub_nonpos.mpr (Real.cos_le_one t))
  dsimp [V]
  nlinarith only [hg,hc]

end SquaresInCircles.Eight.GlobalGA.NegativeEH.HComparison
