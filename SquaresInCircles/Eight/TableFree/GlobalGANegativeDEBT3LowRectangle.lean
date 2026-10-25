module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowRectangleEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowPositiveCoefficients

/-!
# The complete low-total positive-B / negative-H rectangle

Uncompiled Section 4.2. Curvature concavity and the six intrinsic
reference inequalities control the entire signed rectangle. First the
fixed worst coefficient corner is integrated. Concavity in the upper
positive angle and monotonicity in the larger coefficient then transfer
the result to every original low-family coefficient and both original
signed masses. No interior angle or coefficient sample is introduced.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowRectangle
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open OrdinaryNegativeSlope NegativeAPositiveTD.PositiveSlope NegativeAPositiveTD.Curvature

lemma phi_quadratic_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    PositiveAngularEnvelope.phi t≤1+t-t^2/2 := by
  have hc := cos_upper_four ht.1
  have hs := sin_upper_five ht.1
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have hpoly : t/24-1/6+t^2/120≤0 := by
    dsimp [frameCap] at ht ht2
    nlinarith [ht.2]
  have hp := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.1 3) hpoly
  dsimp [PositiveAngularEnvelope.phi]
  nlinarith only [hc,hs,hp]

lemma B_curvature_line {t : ℝ} (ht : t∈Icc 0 frameCap) :
    741/1000+(63/200)*t<curvature R 1 M t := by
  have hc : ConcaveOn ℝ (Icc 0 frameCap)
      (fun t => curvature R 1 M t-(741/1000+(63/200)*t)) := by
    apply concave_of_deriv2
      (f':=fun t => curvatureD R 1 M t-63/200)
      (f'':=fun t => -R*normD4 1 M t)
    · intro t ht
      have h1 := curvature_hasDerivAt (R:=R) (by norm_num : (0:ℝ)<1)
        (by norm_num [M] : (0:ℝ)<M) (show |t|≤frameCap by rw [abs_of_nonneg ht.1]; exact ht.2)
      have h2 : HasDerivAt (fun t : ℝ => 741/1000+(63/200)*t) ((63/200)*1) t :=
        ((hasDerivAt_id' t).const_mul (63/200)).const_add (741/1000)
      exact (h1.fun_sub h2).congr_deriv (by ring)
    · intro t ht
      exact (curvatureD_hasDerivAt (R:=R) (by norm_num : (0:ℝ)<1)
        (by norm_num [M] : (0:ℝ)<M)
        (show |t|≤frameCap by rw [abs_of_nonneg ht.1]; exact ht.2)).sub_const (63/200)
    · intro t ht
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap))
        (normD4_nonneg (by norm_num : (0:ℝ)<1) (by norm_num [M] : (1:ℝ)≤M)
          (by norm_num [M] : M≤2*(1:ℝ)) ht)
  have h0 : 0<curvature R 1 M 0-(741/1000+(63/200)*0) := by
    rw [curvature_zero]
    linarith [B_zero_curvature]
  have h1 : 0<curvature R 1 M frameCap-(741/1000+(63/200)*frameCap) := by
    have hb := B_cap_curvature
    rw [show (741/1000:ℝ)+(63/200)*frameCap=1923/2000 by norm_num [frameCap]]
    linarith
  have hh := concave_gt_of_endpoints hc ht h0 h1
  linarith

lemma B_second_lower {t : ℝ} (ht : t∈Icc 0 frameCap) :
    -(1/2:ℝ)<curvature R 1 M t-PositiveAngularEnvelope.phi t := by
  have hc := B_curvature_line ht
  have hp := phi_quadratic_upper ht
  nlinarith [sq_nonneg (t-137/200)]

lemma H_second_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    curvature R k0 1 (-t)-Real.cos t< -(563/1000:ℝ) := by
  have hc := curvature_signed_tangent
    (by norm_num [k0] : (0:ℝ)<k0) (by norm_num [k0] : k0≤(1:ℝ))
    (by norm_num [k0] : (1:ℝ)≤2*k0)
    (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)
  have hC1 := mul_le_mul_of_nonneg_right H_zero_curvature_slope.le ht.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=t)
  have hquad := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hz := H_zero_curvature
  simp only [frameCap] at hquad
  nlinarith

def excess (N : ℝ) : ℝ := U R 1 M frameCap-U R 1 M (frameCap-N)+V R k0 1 N
def excessD (N : ℝ) : ℝ := Ud 1 M (frameCap-N)+Vd R k0 1 N

theorem excess_derivative {N : ℝ} (hN : N∈Icc 0 frameCap) :
    HasDerivAt excess (excessD N) N := by
  have h1 : HasDerivAt (fun x : ℝ => frameCap-x) (-1) N := (hasDerivAt_id' N).const_sub frameCap
  have hd : HasDerivAt (fun x => U R 1 M (frameCap-x)) (Ud 1 M (frameCap-N)*-1) N :=
    (NegativeAPositiveTD.PositiveSlope.U_hasDerivAt (t:=frameCap-N) (by norm_num : (0:ℝ)<1)
      (by norm_num [M] : (0:ℝ)<M) ⟨by linarith [hN.2],by linarith [hN.1]⟩).comp N h1
  have hv := OrdinaryNegativeSlope.V_hasDerivAt (R:=R) (by norm_num [k0] : (0:ℝ)<k0)
    (by norm_num : (0:ℝ)<1) hN
  exact ((hd.const_sub (U R 1 M frameCap)).fun_add hv).congr_deriv (by simp only [excessD]; ring)

theorem excessD_derivative {N : ℝ} (hN : N∈Icc 0 frameCap) :
    HasDerivAt excessD
      (-(curvature R 1 M (frameCap-N)-PositiveAngularEnvelope.phi (frameCap-N))+
        (curvature R k0 1 (-N)-Real.cos N)) N := by
  have h1 : HasDerivAt (fun x : ℝ => frameCap-x) (-1) N := (hasDerivAt_id' N).const_sub frameCap
  have hd : HasDerivAt (fun x => Ud 1 M (frameCap-x))
      ((curvature R 1 M (frameCap-N)-1*PositiveAngularEnvelope.phi (frameCap-N))*-1) N :=
    (NegativeAPositiveTD.PositiveSlope.Ud_hasDerivAt (t:=frameCap-N) (by norm_num : (0:ℝ)<1)
      (by norm_num [M] : (0:ℝ)<M) ⟨by linarith [hN.2],by linarith [hN.1]⟩).comp N h1
  have hv := OrdinaryNegativeSlope.Vd_hasDerivAt (R:=R) (by norm_num [k0] : (0:ℝ)<k0)
    (by norm_num : (0:ℝ)<1) hN
  exact (hd.fun_add hv).congr_deriv (by ring)

theorem excessD_antitone : AntitoneOn excessD (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun N hN => (excessD_derivative hN).continuousAt.continuousWithinAt)
    (fun N hN => excessD_derivative (Ioo_subset_Icc_self hN))
  intro N hN
  have hb := B_second_lower
    (show frameCap-N∈Icc 0 frameCap from ⟨by linarith [hN.2],by linarith [hN.1]⟩)
  have hh := H_second_upper (Ioo_subset_Icc_self hN)
  linarith

theorem excessD_positive {N : ℝ} (hN : N∈Icc 0 frameCap) : 0<excessD N := by
  have hh := excessD_antitone hN
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hN.2
  have he : 0<excessD frameCap := by
    simp only [excessD,sub_self]
    linarith [B_positive_initial_slope,H_negative_cap_slope]
  exact he.trans_le hh

theorem corner_rectangle {N : ℝ} (hN : N∈Icc 0 frameCap) :
    U R 1 M (frameCap-N)≤U R 1 M frameCap+V R k0 1 N := by
  have hm : MonotoneOn excess (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun N hN => (excess_derivative hN).continuousAt.continuousWithinAt)
      (fun N hN => excess_derivative (Ioo_subset_Icc_self hN))
    intro N hN
    exact (excessD_positive (Ioo_subset_Icc_self hN)).le
  have hh := hm (by norm_num [frameCap]) hN hN.1
  simp only [excess,sub_zero,sub_self,V_zero,zero_add] at hh
  linarith

/-- Concavity moves only the scalar positive interval, not the source point. -/
lemma positive_increment_lower {m P N : ℝ} (hm : m∈Icc (1:ℝ) M)
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    U R 1 M frameCap-U R 1 M (frameCap-N)≤U R 1 m P-U R 1 m (P-N) := by
  have hm0 : 0 < m := by linarith [hm.1]
  have hd (t : ℝ) (ht : t∈Icc 0 P) : HasDerivAt
      (fun t => (U R 1 m P-U R 1 m (P-t))-(U R 1 M frameCap-U R 1 M (frameCap-t)))
      (Ud 1 m (P-t)-Ud 1 M (frameCap-t)) t := by
    have h1 : HasDerivAt (fun x : ℝ => P-x) (-1) t := (hasDerivAt_id' t).const_sub P
    have h2 : HasDerivAt (fun x : ℝ => frameCap-x) (-1) t :=
      (hasDerivAt_id' t).const_sub frameCap
    have hsmall : HasDerivAt (fun x => U R 1 m (P-x)) (Ud 1 m (P-t)*-1) t :=
      (NegativeAPositiveTD.PositiveSlope.U_hasDerivAt (t:=P-t) (by norm_num : (0:ℝ)<1) hm0
        ⟨by linarith [ht.2],by linarith [ht.1]⟩).comp t h1
    have hlarge : HasDerivAt (fun x => U R 1 M (frameCap-x)) (Ud 1 M (frameCap-t)*-1) t :=
      (NegativeAPositiveTD.PositiveSlope.U_hasDerivAt (t:=frameCap-t) (by norm_num : (0:ℝ)<1)
        (by norm_num [M] : (0:ℝ)<M) ⟨by linarith [ht.2],by linarith [ht.1]⟩).comp t h2
    exact ((hsmall.const_sub (U R 1 m P)).fun_sub
      (hlarge.const_sub (U R 1 M frameCap))).congr_deriv (by ring)
  have hmono : MonotoneOn
      (fun t => (U R 1 m P-U R 1 m (P-t))-(U R 1 M frameCap-U R 1 M (frameCap-t)))
      (Icc 0 P) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
    intro t ht
    have hx : P-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hy : frameCap-t∈Icc 0 frameCap := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have ha := Ud_antitone (p:=(1:ℝ)) (q:=M) (by norm_num) (by norm_num [M])
      (by norm_num [M]) hx hy (by linarith)
    have hc := NegativeDEPositiveTD.LowPositive.larger_comparison
      (by norm_num : (0:ℝ)<1) hm0 hm.2 hx
    exact sub_nonneg.mpr (ha.trans hc)
  have hh := hmono (show (0:ℝ)∈Icc 0 P from ⟨le_rfl,hN.trans hNP⟩) ⟨hN,hNP⟩ hN
  simp only [sub_zero,sub_self] at hh
  linarith

/-- Full coefficient and signed-mass rectangle used by the low family. -/
theorem original_rectangle {k m P N : ℝ}
    (hk : k∈Icc k0 1) (hm : m∈Icc (1:ℝ) M)
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    U R 1 m (P-N)≤U R 1 m P+V R k 1 N := by
  have hn : N∈Icc 0 frameCap := ⟨hN,hNP.trans hP⟩
  have hc := corner_rectangle hn
  have hp := positive_increment_lower hm hN hNP hP
  have hv := PositiveTD.V_first_coefficient (q:=(1:ℝ)) (by norm_num)
    (by norm_num [k0] : (1:ℝ)/2≤k0) hk.1 (by linarith [hk.2]) hn
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowRectangle
