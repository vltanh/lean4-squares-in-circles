module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2CommonVarying

/-!
# Secant curvature and continuous allocation of both negative angles

Uncompiled transcription of (32)--(33) and the charged inequalities
in (5). The coefficient bound is proved by its two positive parameter
derivatives and the prescribed positive-square corner comparison.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary OrdinaryCurvatureBounds OrdinaryAngleConcavity
open VaryingBFunctions VaryingBComparison SecantNormCurvature

def coefficientNorm (k q : ℝ) : ℝ := Real.sqrt (k^2+q^2)
def secantCoefficient (k q : ℝ) : ℝ :=
  R*k^3*q*(2*q^2-1)/(coefficientNorm k q)^3
def chargedFirst (k d r : ℝ) : ℝ := VaryingBFunctions.D R (k/secant r) d*first r
def chargedSecond (k d r : ℝ) : ℝ :=
  Dr R (k/secant r) d*(-k/(secant r)^2)*(first r)^2+
    VaryingBFunctions.D R (k/secant r) d*second r

theorem coefficientNorm_positive {k q : ℝ} (hk : 0<k) : 0<coefficientNorm k q :=
  Real.sqrt_pos.mpr (by nlinarith [sq_nonneg q])
theorem coefficientNorm_square (k q : ℝ) : (coefficientNorm k q)^2=k^2+q^2 :=
  Real.sq_sqrt (by positivity)
theorem coefficientNorm_reduce (k q : ℝ) (n : ℕ) :
    (coefficientNorm k q)^(n+2)=(coefficientNorm k q)^n*(k^2+q^2) := by
  rw [pow_add,coefficientNorm_square]

theorem coefficientNorm_k_derivative {k q : ℝ} (hq : 0<q) :
    HasDerivAt (fun k => coefficientNorm k q) (k/coefficientNorm k q) k := by
  simpa [coefficientNorm,NegativeAPositiveTD.SecantCoordinate.radical,add_comm] using
    NegativeAPositiveTD.SecantCoordinate.radical_hasDerivAt (A:=q^2) (x:=k) (sq_pos_of_pos hq)
theorem coefficientNorm_q_derivative {k q : ℝ} (hk : 0<k) :
    HasDerivAt (coefficientNorm k) (q/coefficientNorm k q) q := by
  simpa [coefficientNorm,NegativeAPositiveTD.SecantCoordinate.radical] using
    NegativeAPositiveTD.SecantCoordinate.radical_hasDerivAt (A:=k^2) (x:=q) (sq_pos_of_pos hk)

theorem coefficient_k_derivative {k q : ℝ} (hk : 0<k) (hq : 0<q) :
    HasDerivAt (fun k => secantCoefficient k q)
      (3*R*k^2*q^3*(2*q^2-1)/(coefficientNorm k q)^5) k := by
  have hn := (coefficientNorm_positive (q:=q) hk).ne'
  have hp := coefficientNorm_reduce k q
  have hd := (((hasDerivAt_id k).pow 3).const_mul (R*q*(2*q^2-1))).div
    ((coefficientNorm_k_derivative hq).pow 3) (pow_ne_zero _ hn)
  convert hd using 1
  · dsimp [secantCoefficient]
    congr 1
    ring
  · field_simp [hn]
    ring_nf
    simp only [hp 0,hp 1,hp 2,hp 3,hp 4,hp 5,hp 6,hp 7,hp 8,pow_zero,pow_one]
    ring

theorem coefficient_q_derivative {k q : ℝ} (hk : 0<k) :
    HasDerivAt (secantCoefficient k)
      (R*k^3*(2*q^2+(6*q^2-1)*k^2)/(coefficientNorm k q)^5) q := by
  have hn := (coefficientNorm_positive (q:=q) hk).ne'
  have hp := coefficientNorm_reduce k q
  have hd := (((hasDerivAt_id q).mul
    ((((hasDerivAt_id q).pow 2).const_mul 2).sub_const 1)).const_mul (R*k^3)).div
      ((coefficientNorm_q_derivative hk).pow 3) (pow_ne_zero _ hn)
  convert hd using 1
  · dsimp [secantCoefficient]
    congr 1
    ring
  · field_simp [hn]
    ring_nf
    simp only [hp 0,hp 1,hp 2,hp 3,hp 4,hp 5,hp 6,hp 7,hp 8,pow_zero,pow_one]
    ring

theorem coefficient_corner : secantCoefficient (751/1000) (327/250)<(39/50:ℝ) := by
  have hn := coefficientNorm_positive (q:=(327/250:ℝ)) (show (0:ℝ)<751/1000 by norm_num)
  dsimp [secantCoefficient]
  apply quotient_lt_of_square (pow_pos hn 3) (by norm_num)
  have hN6 : ((coefficientNorm (751/1000) (327/250))^3)^2=
      ((751/1000:ℝ)^2+(327/250)^2)^3 := by
    rw [show ((coefficientNorm (751/1000) (327/250))^3)^2=
      ((coefficientNorm (751/1000) (327/250))^2)^3 by ring,coefficientNorm_square]
  rw [hN6]
  norm_num [mul_pow,radius_sq,qCap]

theorem coefficient_upper {k q : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hq : q∈Icc (1:ℝ) (327/250)) :
    secantCoefficient k q<(39/50:ℝ) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hq0 : 0<q := by linarith [hq.1]
  have hmK : MonotoneOn (fun k => secantCoefficient k q) (Icc (13/20:ℝ) (751/1000)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (coefficient_k_derivative (by linarith [hx.1]) hq0).continuousAt.continuousWithinAt
    · intro x hx
      exact coefficient_k_derivative (by linarith [hx.1]) hq0
    · intro x hx
      have hq2 : 0≤2*q^2-1 := by nlinarith [hq.1]
      positivity
  have hmQ : MonotoneOn (secantCoefficient (751/1000)) (Icc (1:ℝ) (327/250)) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro x hx
      exact (coefficient_q_derivative (q:=x) (by norm_num : (0:ℝ)<751/1000)).continuousAt.continuousWithinAt
    · intro x hx
      exact coefficient_q_derivative (by norm_num : (0:ℝ)<751/1000)
    · intro x hx
      have hx2 : 0≤6*x^2-1 := by nlinarith [hx.1]
      positivity
  exact ((hmK hk ⟨by norm_num,le_rfl⟩ hk.2).trans
    (hmQ hq ⟨by norm_num,le_rfl⟩ hq.2)).trans_lt coefficient_corner

theorem full_secant_domain {r : ℝ} (hr : r∈Icc 0 frameCap) :
    secant r∈Icc (1:ℝ) (327/250) := by
  have hc : 0<Real.cos r := by linarith [(transport_trig hr).1]
  refine ⟨secant_ge_one hc,?_⟩
  dsimp [secant]
  apply (div_le_iff₀ hc).2
  nlinarith [(transport_trig hr).1]

theorem secant_ratio_domain {k r : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hr : r∈Icc 0 frameCap) :
    k/secant r∈Icc (49/100:ℝ) (751/1000) := by
  have hq := full_secant_domain hr
  have hq0 : 0<secant r := by linarith [hq.1]
  exact ⟨(le_div_iff₀ hq0).2 (by linarith [hq.2,hk.1]),
    (div_le_iff₀ hq0).2 (by nlinarith [hq.1,hk.2])⟩

theorem second_identity {r : ℝ} (hr : r∈Icc 0 frameCap) :
    second r=secant r*(2*(secant r)^2-1) := by
  have hc : Real.cos r≠0 := (show 0<Real.cos r by linarith [(transport_trig hr).1]).ne'
  dsimp [second,secant]
  field_simp [hc]
  nlinarith only [Real.sin_sq_add_cos_sq r]

theorem normalized_coefficient {k q : ℝ} (hq : 0<q) :
    R*(k/q)^3/(shape (k/q))^3*(q*(2*q^2-1))=secantCoefficient k q := by
  have hnorm : coefficientNorm k q=q*shape (k/q) := by
    simpa [coefficientNorm,PositiveAngularEnvelope.pairNorm,
      PairNormCalculus.pairEnergy,PairNormCalculus.pairProduct] using
      negativeNorm_normalized (l:=k) (t:=0) hq
  dsimp [secantCoefficient]
  rw [hnorm]
  field_simp [hq.ne',(shape_pos (k/q)).ne']
  ring

theorem charged_derivative {k d r : ℝ} (hk : 0<k)
    (hd : d∈Icc 0 frameCap) (hr : r∈Icc 0 frameCap) :
    HasDerivAt (fun r => V R k (secant r) d) (chargedFirst k d r) r := by
  have hc : Real.cos r≠0 := (show 0<Real.cos r by linarith [(transport_trig hr).1]).ne'
  have hq : 0<secant r := by linarith [(full_secant_domain hr).1]
  exact (V_hasDerivAt_q (R:=R) hk hq hd).comp r (secant_hasDerivAt hc)

theorem chargedFirst_derivative {k d r : ℝ} (hk : 0<k)
    (hd : d∈Icc 0 frameCap) (hr : r∈Icc 0 frameCap) :
    HasDerivAt (chargedFirst k d) (chargedSecond k d r) r := by
  have hc : Real.cos r≠0 := (show 0<Real.cos r by linarith [(transport_trig hr).1]).ne'
  have hq : 0<secant r := by linarith [(full_secant_domain hr).1]
  have hh := ((OrdinaryNegativeEnvelope.D_quotient_hasDerivAt (R:=R) (p:=k) hq hd).comp r
    (secant_hasDerivAt hc)).mul (first_hasDerivAt hc)
  convert hh using 1
  · rfl
  · dsimp [chargedSecond]
    ring

theorem charged_curvature {k d r : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hd : d∈Icc 0 frameCap) (hr : r∈Icc 0 frameCap) :
    chargedSecond k d r≤(39/50)*d := by
  have hk0 : 0<k := by linarith [hk.1]
  have hq := full_secant_domain hr
  have hq0 : 0<secant r := by linarith [hq.1]
  have hρ := secant_ratio_domain hk hr
  have hDr := varying_Dr_nonnegative hρ hd
  have hD := varying_D_upper hρ hd
  have hq2 : 0≤second r := by rw [second_identity hr]; nlinarith [hq.1]
  have hfirst : Dr R (k/secant r) d*(-k/(secant r)^2)*(first r)^2≤0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hDr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk0.le) (sq_nonneg _))) (sq_nonneg _)
  have hsecond := mul_le_mul_of_nonneg_right hD hq2
  have he : R*(k/secant r)^3/(shape (k/secant r))^3*d*second r=
      secantCoefficient k (secant r)*d := by
    rw [second_identity hr,←normalized_coefficient hq0]
    ring
  rw [he] at hsecond
  have hcoeff := mul_le_mul_of_nonneg_right (coefficient_upper hk hq).le hd.1
  dsimp [chargedSecond]
  linarith

theorem charged_allocation_concave {k S d : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (hS : 0≤S) (hd : 0≤d)
    (hbudget : S+d≤frameCap) :
    ConcaveOn ℝ (Icc 0 S) (fun r => F k r+F k (S-r)+V R k (secant r) d) := by
  have hk0 : 0<k := by linarith [hk.1]
  have hd' : d∈Icc 0 frameCap := ⟨hd,by linarith⟩
  have domains (r : ℝ) (hr : r∈Icc 0 S) : r∈Icc 0 frameCap ∧ S-r∈Icc 0 frameCap :=
    ⟨⟨hr.1,by linarith [hr.2]⟩,⟨by linarith [hr.2],by linarith [hr.1]⟩⟩
  have hf (r : ℝ) (hr : r∈Icc 0 S) :
      HasDerivAt (fun r => F k r+F k (S-r)+V R k (secant r) d)
        (F1 k r-F1 k (S-r)+chargedFirst k d r) r := by
    have hleft := F_derivative (k:=k) (domains r hr).1
    have hright := (F_derivative (k:=k) (domains r hr).2).comp r ((hasDerivAt_id r).const_sub S)
    convert (hleft.add hright).add (charged_derivative hk0 hd' (domains r hr).1) using 1 <;> ring
  have hf' (r : ℝ) (hr : r∈Icc 0 S) :
      HasDerivAt (fun r => F1 k r-F1 k (S-r)+chargedFirst k d r)
        (F2 k r+F2 k (S-r)+chargedSecond k d r) r := by
    have hleft := F1_derivative (k:=k) (domains r hr).1
    have hright := (F1_derivative (k:=k) (domains r hr).2).comp r ((hasDerivAt_id r).const_sub S)
    convert (hleft.sub hright).add (chargedFirst_derivative hk0 hd' (domains r hr).1) using 1 <;> ring
  apply concave_of_deriv2 hf hf'
  intro r hr
  have hs := second_sum hk hr.1 (show 0≤S-r by linarith [hr.2])
    (show r+(S-r)≤frameCap by linarith)
  have hv := charged_curvature hk hd' (domains r hr).1
  linarith

theorem merge_charged {k r s d : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤s) (hd : 0≤d) (ht : r+s+d≤frameCap) :
    F k (r+s)+min (V R k 1 d) (V R k (secant (r+s)) d)≤
      F k r+F k s+V R k (secant r) d := by
  have hc := charged_allocation_concave hk (add_nonneg hr hs) hd ht
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,add_nonneg hr hs⟩
    ⟨add_nonneg hr hs,le_rfl⟩ (show r∈Icc 0 (r+s) from ⟨hr,by linarith⟩)
  simp only [F_zero,zero_add,sub_zero,sub_self,add_zero,add_sub_cancel_left,
    secant,Real.cos_zero,div_one] at hh
  have hm := le_min
    (add_le_add_left (min_le_left (V R k 1 d) (V R k (secant (r+s)) d)) (F k (r+s)))
    (add_le_add_left (min_le_right (V R k 1 d) (V R k (secant (r+s)) d)) (F k (r+s)))
  exact hm.trans hh

theorem merge_charged_right {k r s d : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤s) (hd : 0≤d) (ht : r+s+d≤frameCap) :
    F k (r+s)+min (V R k 1 d) (V R k (secant (r+s)) d)≤
      F k r+F k s+V R k (secant s) d := by
  have hh := merge_charged hk hs hr hd (show s+r+d≤frameCap by linarith)
  simpa only [add_comm s r,add_comm (F k s) (F k r)] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
