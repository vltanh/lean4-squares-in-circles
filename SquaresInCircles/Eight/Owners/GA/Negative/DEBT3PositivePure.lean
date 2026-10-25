module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Owners.ChargedOrdinaryConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Data
public import SquaresInCircles.Eight.Owners.GA.Negative.EHSlopes
public import SquaresInCircles.Eight.Owners.GA.Secant.DCorrectionGrowth
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts

/-!
# Eight squares: all pure-positive DE3 / BT3 allocations have the same intrinsic endpoint

The total angle and the original A/BT split stay fixed. The
secant-D correction is used across its actual sorted-support switch.
Ordinary positive mass is paid by the whole-interval U lower bound;
the original TD0 singleton uses the proved secant penalty comparison.
The closed zero-surplus endpoint is included for every block index.
-/

section
/-!
## The total-dependent high tilt on the complete interval

Multiplying
the half-angle inequality by its positive sine gives the equivalent
harmonic inequality cos(theta)+eta(theta) sin(theta)>=1. Its exact second
derivative is negative, so its two intrinsic endpoint values suffice.
The fixed-total split then uses ordinary harmonic concavity. No sampled
angle interval or coefficient hypothesis is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Explicit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity Arithmetic
open SecondWord.ReferenceTrig

def highFactor (θ : ℝ) : ℝ := Real.cos θ+eta .high θ*Real.sin θ
def highFactorD (θ : ℝ) : ℝ :=
  -(8649/10000)*Real.sin θ+eta .high θ*Real.cos θ
def highFactorDD (θ : ℝ) : ℝ :=
  -(3649/5000)*Real.cos θ-eta .high θ*Real.sin θ

theorem high_eta {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    (293/1000:ℝ)≤eta .high θ ∧ eta .high θ<(183/500:ℝ) := by
  dsimp [eta,L]
  exact ⟨by linarith [hθ.1],by linarith [hθ.2]⟩

theorem high_eta_derivative (θ : ℝ) : HasDerivAt (eta .high) (1351/10000) θ := by
  have h : HasDerivAt (fun x : ℝ => 293/1000+(1351/10000)*(x-L)) ((1351/10000)*1) θ :=
    ((hasDerivAt_id' θ).sub_const L).const_mul (1351/10000) |>.const_add (293/1000)
  have he : eta .high=fun x : ℝ => 293/1000+(1351/10000)*(x-L) := by
    funext x
    rfl
  rw [he]
  simpa using h

theorem highFactor_hasDerivAt (θ : ℝ) : HasDerivAt highFactor (highFactorD θ) θ := by
  have h := (Real.hasDerivAt_cos θ).add ((high_eta_derivative θ).mul (Real.hasDerivAt_sin θ))
  unfold highFactor
  exact h.congr_deriv (by dsimp [highFactorD]; ring)

theorem highFactorD_hasDerivAt (θ : ℝ) : HasDerivAt highFactorD (highFactorDD θ) θ := by
  have h := ((Real.hasDerivAt_sin θ).const_mul (-(8649/10000:ℝ))).add
    ((high_eta_derivative θ).mul (Real.hasDerivAt_cos θ))
  unfold highFactorD
  exact h.congr_deriv (by dsimp [highFactorDD]; ring)

theorem highFactor_concave : ConcaveOn ℝ (Icc (1/6:ℝ) (7/10)) highFactor := by
  apply concave_of_deriv2 (fun θ _ => highFactor_hasDerivAt θ)
    (fun θ _ => highFactorD_hasDerivAt θ)
  intro θ hθ
  have ht := transport_trig (show θ∈Icc 0 frameCap from
    ⟨by linarith [hθ.1],by simpa [frameCap] using hθ.2⟩)
  have hp := mul_nonneg (show 0≤eta .high θ by linarith [(high_eta hθ).1]) ht.2.2.1
  dsimp [highFactorDD]
  linarith [ht.1]

theorem highFactor_left : 1≤highFactor (1/6) := by
  have hh := PositiveTD.Explicit.low_factor (show (1/6:ℝ)∈Icc 0 (1/6) by norm_num)
  simpa [highFactor,eta,L,PositiveTD.eta] using hh.1

theorem highFactor_right : 1<highFactor (7/10) := by
  have hs := sin11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos10_le_cos (show (0:ℝ)≤7/10 by norm_num)
  norm_num [sin11,sin9,sin7,cos10,cos8] at hs hc
  dsimp [highFactor,eta,L]
  linarith

theorem highFactor_lower {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) : 1≤highFactor θ := by
  have hh := highFactor_concave.min_le_of_mem_Icc
    (show (1/6:ℝ)∈Icc (1/6) (7/10) by norm_num)
    (show (7/10:ℝ)∈Icc (1/6) (7/10) by norm_num) hθ
  exact (le_min highFactor_left highFactor_right.le).trans hh

theorem fixed_factor_concave {θ e : ℝ} (hθ : θ∈Icc 0 frameCap) (he : 0≤e) :
    ConcaveOn ℝ (Icc 0 θ) (fun z => Real.cos z+e*Real.sin z) := by
  apply concave_of_deriv2
    (fun z _ => by
      convert (Real.hasDerivAt_cos z).add ((Real.hasDerivAt_sin z).const_mul e) using 1)
    (fun z _ => by
      convert (Real.hasDerivAt_sin z).neg.add ((Real.hasDerivAt_cos z).const_mul e) using 1)
  intro z hz
  have ht := transport_trig (show z∈Icc 0 frameCap from ⟨hz.1,hz.2.trans hθ.2⟩)
  have hp := mul_nonneg he ht.2.2.1
  linarith [ht.1]

theorem high_factor_lower {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) : 1≤Real.cos z+eta .high θ*Real.sin z := by
  have htf := frame_domain .high hθ
  have hc := fixed_factor_concave htf (show 0≤eta .high θ by linarith [(high_eta hθ).1])
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,htf.1⟩ ⟨htf.1,le_rfl⟩ hz
  have he := highFactor_lower hθ
  norm_num only [Real.sin_zero,Real.cos_zero,mul_zero,add_zero] at hh
  dsimp [highFactor] at he
  simpa only [min_eq_left he] using hh

theorem high_factor_upper {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Real.cos z+eta .high θ*Real.sin z<(213/200:ℝ) := by
  have he := high_eta hθ
  have he2 := pow_le_pow_left₀ (show 0≤eta .high θ by linarith [he.1]) he.2.le 2
  have hid : (Real.cos z+eta .high θ*Real.sin z)^2+
      (Real.sin z-eta .high θ*Real.cos z)^2=1+(eta .high θ)^2 := by
    linear_combination (1+(eta .high θ)^2)*(Real.sin_sq_add_cos_sq z)
  nlinarith [sq_nonneg (Real.sin z-eta .high θ*Real.cos z)]

theorem sigma_upper {e : ℝ} (he : e∈Icc (293/1000:ℝ) (183/500)) :
    fullSupport 1 e<(57/40:ℝ) := by
  have hR := Real.sqrt_nonneg qCap
  have hN := Real.sqrt_nonneg (1+e^2)
  have hN2 := Real.sq_sqrt (show 0≤1+e^2 by positivity)
  have hprod := mul_nonneg (sub_nonneg.mpr he.1) (sub_nonneg.mpr he.2)
  have htarget : 0<57/40+(1+e)/2 := by linarith [he.1]
  have hsq : (R*Real.sqrt (1+e^2))^2<(57/40+(1+e)/2)^2 := by
    rw [mul_pow,radius_sq,hN2]
    norm_num [qCap]
    nlinarith
  have hh : R*Real.sqrt (1+e^2)<57/40+(1+e)/2 := by
    nlinarith [mul_nonneg hR hN]
  simpa [fullSupport] using (show R*Real.sqrt (1+e^2)-(1+e)/2<57/40 by linarith)

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Explicit
end
end
end

section
/-!
## Whole-domain coefficient bounds for the two original BT3 stresses

The high polynomial family
is the previously proved DE family with its base coefficient renamed m.
Only the total-dependent tilt is new. Every larger ordinary coefficient
is kept separate, so the spread bounds also cover l below one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Explicit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

structure HighBounds (θ : ℝ) : Prop where
  k_lower : (670158/1000000:ℝ)≤k .high θ
  k_upper : k .high θ≤800408/1000000
  l_lower : (863/1000:ℝ)<l .high θ
  l_upper : l .high θ≤1005069/1000000
  m_lower : (862/1000:ℝ)< m .high θ
  m_upper : m .high θ≤1021248/1000000
  l_ratio : l .high θ<(3/2)*k .high θ
  m_l_lower : (9/10)*l .high θ< m .high θ
  m_l_upper : m .high θ<(1017/1000)*l .high θ

theorem high_bounds {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) : HighBounds θ := by
  have hh := NegativeDEPositiveTD.Explicit.high_ranges hθ
  have hr := NegativeDEPositiveTD.Explicit.high_ratios hθ
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,
    hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.1,hr.1,hr.2⟩

theorem low_bounds {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    k .low θ∈Icc (2933/5000:ℝ) (1673/2500) ∧
      m .low θ∈Icc (10163/10000:ℝ) (5821/5000) := by
  dsimp [k,m,PositiveBT3.lowK,PositiveBT3.lowM,PositiveBT3.Cmax]
  exact ⟨⟨by linarith [hθ.1],by linarith [hθ.2]⟩,
    ⟨by linarith [hθ.2],by linarith [hθ.1]⟩⟩

theorem low_c {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) :
    m .low θ≤c .low θ z ∧ c .low θ z≤5821/5000 := by
  have hm := (low_bounds hθ).2
  have hz' : z∈Icc (0:ℝ) (1/6) := ⟨hz.1,hz.2.trans hθ.2⟩
  have hf := PositiveTD.Explicit.low_factor hz'
  have hm0 : 0 ≤ m .low θ := by linarith [hm.1]
  have hlo := mul_le_mul_of_nonneg_left hf.1 hm0
  have hfactor : Real.cos z+eta .low θ*Real.sin z≤1+(293/1000)*θ := by
    dsimp [eta]
    linarith [Real.cos_le_one z,Real.sin_le hz.1,hz.2]
  have hhi := mul_le_mul_of_nonneg_left hfactor hm0
  have hmdef : m .low θ = 5821/5000-(4437/5000)*θ := by
    simp [m,PositiveBT3.lowM,PositiveBT3.Cmax]
  constructor
  · simpa [c,eta,PositiveTD.eta] using hlo
  · change m .low θ*(Real.cos z+eta .low θ*Real.sin z)≤5821/5000
    rw [hmdef] at hhi ⊢
    nlinarith [hhi,hθ.1,sq_nonneg θ]

theorem high_c {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (hz : z∈Icc 0 θ) :
    m .high θ≤c .high θ z ∧ c .high θ z<(213/200)*m .high θ := by
  have hm := (high_bounds hθ).m_lower
  have hp : 0< m .high θ := by linarith
  have hlo := mul_le_mul_of_nonneg_left (high_factor_lower hθ hz) hp.le
  have hhi := mul_lt_mul_of_pos_left (high_factor_upper (z:=z) hθ) hp
  exact ⟨by simpa [c] using hlo,by simpa [c,mul_comm] using hhi⟩

theorem high_pairs {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    0<p .high θ i ∧ p .high θ i≤q .high θ i ∧ (2/3)*q .high θ i<p .high θ i := by
  have hb := high_bounds hθ
  fin_cases i
  · change 0<k .high θ ∧ k .high θ≤1 ∧ (2/3)*1<k .high θ
    exact ⟨by linarith [hb.k_lower],by linarith [hb.k_upper],by linarith [hb.k_lower]⟩
  · change 0<k .high θ ∧ k .high θ≤l .high θ ∧ (2/3)*l .high θ<k .high θ
    exact ⟨by linarith [hb.k_lower],by linarith [hb.k_upper,hb.l_lower],by linarith [hb.l_ratio]⟩
  · change 0 < min (l .high θ) (m .high θ) ∧
      min (l .high θ) (m .high θ) ≤ max (l .high θ) (m .high θ) ∧
      (2/3)*max (l .high θ) (m .high θ) < min (l .high θ) (m .high θ)
    rcases le_total (l .high θ) (m .high θ) with h|h
    · rw [min_eq_left h,max_eq_right h]
      exact ⟨by linarith [hb.l_lower],h,by linarith [hb.m_l_upper,hb.l_lower]⟩
    · rw [min_eq_right h,max_eq_left h]
      exact ⟨by linarith [hb.m_lower],h,by linarith [hb.m_l_lower,hb.l_lower]⟩

theorem high_q_bounds {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i : Fin 3) :
    (431/500:ℝ)<q .high θ i ∧ q .high θ i<(533/500:ℝ) := by
  have hb := high_bounds hθ
  fin_cases i
  · change (431/500:ℝ)<1 ∧ (1:ℝ)<533/500
    norm_num
  · change (431/500:ℝ)<l .high θ ∧ l .high θ<(533/500:ℝ)
    exact ⟨by linarith [hb.l_lower],by linarith [hb.l_upper]⟩
  · change (431/500:ℝ) < max (l .high θ) (m .high θ) ∧ max (l .high θ) (m .high θ) < (533/500:ℝ)
    exact ⟨by linarith [hb.l_lower,le_max_left (l .high θ) (m .high θ)],
      max_lt (by linarith [hb.l_upper]) (by linarith [hb.m_upper])⟩

theorem high_spread {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) (i j : Fin 3) :
    q .high θ i<(29/25)*q .high θ j := by
  have hb := high_bounds hθ
  have hl : 0<l .high θ := by linarith [hb.l_lower]
  have hscaled : q .high θ i<(29/25)*l .high θ := by
    fin_cases i
    · norm_num [q]
      linarith [hb.l_lower]
    · change l .high θ<(29/25)*l .high θ
      linarith
    · change max (l .high θ) (m .high θ)<(29/25)*l .high θ
      exact max_lt (by linarith) (by linarith [hb.m_l_upper])
  fin_cases j
  · change q .high θ i<(29/25)*1
    linarith [(high_q_bounds hθ i).2]
  · exact hscaled
  · exact hscaled.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))

theorem high_c_ratio {θ z : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (j : Fin 3) : c .high θ z<(109/100)*q .high θ j := by
  have hb := high_bounds hθ
  have hc := (high_c hθ hz).2
  fin_cases j
  · change c .high θ z<(109/100)*1
    linarith [hb.m_upper]
  · change c .high θ z<(109/100)*l .high θ
    linarith [hb.m_l_upper,hb.l_lower]
  · change c .high θ z<(109/100)*max (l .high θ) (m .high θ)
    have hh := le_max_right (l .high θ) (m .high θ)
    linarith [hb.m_lower]

theorem family_pairs (f : Family) {θ : ℝ} (hθ : θ∈Icc (left f) (right f)) (i : Fin 3) :
    0<p f θ i ∧ p f θ i≤q f θ i ∧ q f θ i≤2*p f θ i := by
  cases f
  · have hb := low_bounds hθ
    have hk1 := hb.1.1
    have hk2 := hb.1.2
    have hm1 := hb.2.1
    have hm2 := hb.2.2
    fin_cases i
    · change 0<k .low θ ∧ k .low θ≤1 ∧ 1≤2*k .low θ
      exact ⟨by linarith,by linarith,by linarith⟩
    · change 0<k .low θ ∧ k .low θ≤1 ∧ 1≤2*k .low θ
      exact ⟨by linarith,by linarith,by linarith⟩
    · change 0 < min 1 (m .low θ) ∧ min 1 (m .low θ) ≤ max 1 (m .low θ) ∧
        max 1 (m .low θ) ≤ 2*min 1 (m .low θ)
      rw [min_eq_left (show 1 ≤ m .low θ by linarith [hb.2.1]),
        max_eq_right (show 1 ≤ m .low θ by linarith [hb.2.1])]
      exact ⟨by norm_num,by linarith [hb.2.1],by linarith [hb.2.2]⟩
  · have hh := high_pairs hθ i
    exact ⟨hh.1,hh.2.1,by linarith [hh.1,hh.2.2]⟩

theorem source_coefficients (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left f) (right f)) (hz : z∈Icc 0 θ) :
    k f θ∈Icc (1/2:ℝ) (17/20) ∧ k f θ≤l f θ ∧
      0<l f θ ∧ 0< m f θ ∧
      c f θ z∈Icc SecantD.PositiveEndpoint.d SecantD.cUpper ∧ k f θ≤c f θ z := by
  cases f
  · have hb := low_bounds hθ
    have hc := low_c hθ hz
    refine ⟨⟨by linarith [hb.1.1],by linarith [hb.1.2]⟩,
      by dsimp [l]; linarith [hb.1.2],by norm_num [l],by linarith [hb.2.1],?_,?_⟩
    · norm_num [SecantD.PositiveEndpoint.d,SecantD.cUpper]
      exact ⟨by linarith [hb.2.1,hc.1],by linarith [hc.2]⟩
    · linarith [hb.1.2,hb.2.1,hc.1]
  · have hb := high_bounds hθ
    have hc := high_c hθ hz
    refine ⟨⟨by linarith [hb.k_lower],by linarith [hb.k_upper]⟩,
      by linarith [hb.k_upper,hb.l_lower],by linarith [hb.l_lower],
      by linarith [hb.m_lower],?_,?_⟩
    · norm_num [SecantD.PositiveEndpoint.d,SecantD.cUpper]
      exact ⟨by linarith [hb.m_lower,hc.1],by linarith [hb.m_upper,hc.2]⟩
    · linarith [hb.k_upper,hb.m_lower,hc.1]

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Explicit
end
end
end

section
/-!
## The four-block negative-DE / positive-BT3 scalar model

The fourth block is the TD0 singleton. Its positive slope is the secant-dependent `gamma`, not an
ordinary circle coefficient. All coefficients are fixed while the two signed totals are
concentrated (`concentrate`), and both mass budgets are kept through the intrinsic endpoint
reduction.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Blocks
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def p (f : Family) (θ : ℝ) : Fin 4→ℝ :=
  ![Explicit.k f θ,Explicit.k f θ,min (Explicit.l f θ) (Explicit.m f θ),Explicit.k f θ]
def q (f : Family) (θ : ℝ) : Fin 4→ℝ :=
  ![1,Explicit.l f θ,max (Explicit.l f θ) (Explicit.m f θ),1]
def positive (f : Family) (θ z s t : ℝ) (i : Fin 4) : ℝ :=
  ChargedHybridConcentration.positive R (Explicit.gamma f θ z s) 0 (p f θ) (q f θ) 3 i t
def negative (f : Family) (θ t : ℝ) (i : Fin 4) : ℝ := V R (p f θ i) (q f θ i) t
def block (f : Family) (θ z s P N : ℝ) (i : Fin 4) : ℝ :=
  ChargedHybridConcentration.block R (Explicit.gamma f θ z s) 0 (p f θ) (q f θ) 3 i P N
def pure (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedHybridConcentration.pure R (Explicit.gamma f θ z s) 0 (p f θ) (q f θ) 3 i j s θ
def saturated (f : Family) (θ z s : ℝ) (i j : Fin 4) : ℝ :=
  ChargedHybridConcentration.saturated R (Explicit.gamma f θ z s) 0 (p f θ) (q f θ) 3 i j s θ

def ordinaryIndex (i : Fin 4) : Fin 3 := if h : i.val<3 then ⟨i.val,h⟩ else 0

@[simp] theorem positive_ordinary (f : Family) (θ z s t : ℝ) (i : Fin 3) :
    positive f θ z s t i.castSucc=Explicit.U f θ i t := by
  have hi : i.castSucc≠(3:Fin 4) := by fin_cases i <;> decide
  simp only [positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,
    ite_eq_right hi,zero_mul,sub_zero,Explicit.U]
  fin_cases i <;> rfl

@[simp] theorem negative_ordinary (f : Family) (θ t : ℝ) (i : Fin 3) :
    negative f θ t i.castSucc=Explicit.V f θ i t := by fin_cases i <;> rfl

@[simp] theorem block_ordinary (f : Family) (θ z s P N : ℝ) (i : Fin 3) :
    block f θ z s P N i.castSucc=mixedBlock R (Explicit.p f θ i) (Explicit.q f θ i) P N := by
  have hi : i.castSucc≠(3:Fin 4) := by fin_cases i <;> decide
  simp only [block,ChargedHybridConcentration.block,PositiveTD.Hybrid.block,
    ite_eq_right hi,zero_mul,sub_zero]
  fin_cases i <;> rfl

@[simp] theorem positive_D (f : Family) (θ z s t : ℝ) :
    positive f θ z s t 3= -Explicit.gamma f θ z s*t := by
  simp [positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive]

@[simp] theorem negative_D (f : Family) (θ t : ℝ) :
    negative f θ t 3=Explicit.V f θ 0 t := rfl

@[simp] theorem block_D (f : Family) (θ z s P N : ℝ) :
    block f θ z s P N 3=positive f θ z s P 3+negative f θ N 3 := by
  simp [block,positive,negative,ChargedHybridConcentration.block,
    ChargedHybridConcentration.positive,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive]

@[simp] theorem positive_zero (f : Family) (θ z s : ℝ) (i : Fin 4) :
    positive f θ z s 0 i=0 := by
  by_cases hi : i=3 <;>
    simp [positive,ChargedHybridConcentration.positive,PositiveTD.Hybrid.positive,hi,U_zero]

@[simp] theorem negative_zero (f : Family) (θ : ℝ) (i : Fin 4) : negative f θ 0 i=0 := by
  simp [negative,V_zero]

theorem negative_to_ordinary (f : Family) (θ t : ℝ) (i : Fin 4) :
    negative f θ t i=Explicit.V f θ (ordinaryIndex i) t := by fin_cases i <;> rfl

theorem family_pairs (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 4) :
    0<p f θ i ∧ p f θ i≤q f θ i ∧ q f θ i≤2*p f θ i := by
  have hh := Explicit.family_pairs f hθ (ordinaryIndex i)
  fin_cases i <;> exact hh

theorem concentrate (f : Family) {θ z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (hs : s∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure f θ z s i j) (saturated f θ z s i j)≤∑k,block f θ z s (P k) (N k) k := by
  have hp := family_pairs f hθ
  exact ChargedHybridConcentration.concentrate R (Explicit.gamma f θ z s) 0
    (p f θ) (q f θ) P N 3 (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hp i).1) (fun i => (hp i).2.1) (fun i => (hp i).2.2)
    hP hN hs (Explicit.frame_domain f hθ) hPb hNb hbalance

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.Blocks
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.PositivePure
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma q_upper (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 3) :
    Explicit.q f θ i≤(5821/5000:ℝ) := by
  cases f
  · have hm := (Explicit.low_bounds hθ).2
    fin_cases i
    · norm_num [Explicit.q]
    · norm_num [Explicit.q,Explicit.l]
    · change max 1 (Explicit.m .low θ)≤(5821/5000:ℝ)
      exact max_le (by norm_num) hm.2
  · exact (Explicit.high_q_bounds hθ i).2.le.trans (by norm_num)

lemma ordinary_lower (f : Family) {θ t : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f))
    (ht : t∈Icc 0 frameCap) (i : Fin 3) :
    -(109/200)*(5821/5000)*t≤Explicit.U f θ i t := by
  have hp := Explicit.family_pairs f hθ i
  have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
    hp.1 hp.2.1 hp.2.2 ht
  have hq := mul_le_mul_of_nonneg_right (q_upper f hθ i) ht.1
  change -(109/200)*Explicit.q f θ i*t≤Explicit.U f θ i t at hu
  nlinarith only [hu,hq]

/-- The coefficients are evaluated at a+z, not at the varying DE magnitude. -/
theorem ordinary_intrinsic_lower (f : Family) {a z s : ℝ}
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) frameCap) (i : Fin 3) :
    Explicit.baseline f a z (a+z)≤
      Explicit.baseline f a z s+Explicit.U f (a+z) i (s-(a+z)) := by
  have ht := Explicit.frame_domain f hθ
  obtain ⟨_,_,_,_,hc,_⟩ := Explicit.source_coefficients f hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
  have hsf : s∈Icc 0 frameCap := ⟨ht.1.trans hs.1,hs.2⟩
  have hd : s-(a+z)∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hs.1,by linarith [hs.2,ht.1]⟩
  have hg := SecantD.PositiveEndpoint.correction_growth hc ht hsf hs.1
  have hu := ordinary_lower f hθ hd i
  rw [Explicit.baseline_correction f a z (a+z),
    Explicit.baseline_correction f a z s]
  nlinarith only [hg,hu,hd.1]

/-- The actual D coefficient is max(sec s,c), including its weak support tie. -/
theorem D_intrinsic_lower (f : Family) {a z s : ℝ}
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) frameCap) :
    Explicit.baseline f a z (a+z)≤Explicit.baseline f a z s+
      Blocks.positive f (a+z) z s (s-(a+z)) 3 := by
  have ht := Explicit.frame_domain f hθ
  obtain ⟨_,_,_,_,hc,_⟩ := Explicit.source_coefficients f hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
  have hh := SecantD.PositiveEndpoint.intrinsic_lower hc ht hs
  rw [Blocks.positive_D,Explicit.baseline_correction f a z (a+z),
    Explicit.baseline_correction f a z s]
  dsimp [Explicit.gamma]
  linarith only [hh]

theorem block_intrinsic_lower (f : Family) {a z s : ℝ}
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) frameCap) (i : Fin 4) :
    Explicit.baseline f a z (a+z)≤Explicit.baseline f a z s+
      Blocks.positive f (a+z) z s (s-(a+z)) i := by
  by_cases hi : i=3
  · subst i
    exact D_intrinsic_lower f hθ ha hz hs
  · have hlt : i.val<3 := by
      have h4 := i.isLt
      have h3 : i.val≠3 := fun h => hi (Fin.ext h)
      omega
    obtain ⟨j,hj⟩ : ∃j : Fin 3,j.castSucc=i := ⟨⟨i.val,hlt⟩,Fin.ext rfl⟩
    subst i
    rw [Blocks.positive_ordinary]
    exact ordinary_intrinsic_lower f hθ ha hz hs j

/-- Every positive-surplus concentration alternative, including s=theta. -/
theorem pure_intrinsic_lower (f : Family) {a z s : ℝ}
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) frameCap) (i j : Fin 4) :
    Explicit.baseline f a z (a+z)≤Explicit.baseline f a z s+
      Blocks.pure f (a+z) z s i j := by
  by_cases he : s≤a+z
  · have hsEq : s=a+z := le_antisymm he hs.1
    subst s
    simp [Blocks.pure,ChargedHybridConcentration.pure,V_zero]
  · have hh := block_intrinsic_lower f hθ ha hz hs i
    simpa only [Blocks.pure,ChargedHybridConcentration.pure,ite_eq_right he,
      Blocks.positive] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.PositivePure
end
end
end
