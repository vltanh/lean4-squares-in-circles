module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDEBT3LowRectangleEndpoints

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
    phi t≤1+t-t^2/2 := by
  have hc := cos_upper_four ht.1
  have hs := sin_upper_five ht.1
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  have hpoly : t/24-1/6+t^2/120≤0 := by
    dsimp [frameCap] at ht ht2
    nlinarith [ht.2]
  have hp := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.1 3) hpoly
  dsimp [phi]
  nlinarith only [hc,hs,hp]

lemma B_curvature_line {t : ℝ} (ht : t∈Icc 0 frameCap) :
    741/1000+(63/200)*t<curvature R 1 M t := by
  have hc : ConcaveOn ℝ (Icc 0 frameCap)
      (fun t => curvature R 1 M t-(741/1000+(63/200)*t)) := by
    apply concave_of_deriv2
      (f':=fun t => curvatureD R 1 M t-63/200)
      (f'':=fun t => -R*normD4 1 M t)
    · intro t ht
      convert (curvature_hasDerivAt (R:=R) (by norm_num : (0:ℝ)<1)
        (by norm_num [M] : 0<M) (by rw [abs_of_nonneg ht.1]; exact ht.2)).sub
          ((((hasDerivAt_id t).const_mul (63/200)).const_add (741/1000))) using 1 <;> ring
    · intro t ht
      exact (curvatureD_hasDerivAt (R:=R) (by norm_num : (0:ℝ)<1)
        (by norm_num [M] : 0<M) (by rw [abs_of_nonneg ht.1]; exact ht.2)).sub_const (63/200)
    · intro t ht
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap))
        (normD4_nonneg (by norm_num : (0:ℝ)<1) (by norm_num [M] : (1:ℝ)≤M)
          (by norm_num [M] : M≤2*(1:ℝ)) ht)
  have h0 : 0<curvature R 1 M 0-(741/1000+(63/200)*0) := by
    simpa only [curvature_zero,mul_zero,add_zero,sub_pos] using B_zero_curvature
  have h1 : 0<curvature R 1 M frameCap-(741/1000+(63/200)*frameCap) := by
    norm_num [frameCap] at ⊢
    linarith [B_cap_curvature]
  have hh := concave_gt_of_endpoints hc ht h0 h1
  linarith

lemma B_second_lower {t : ℝ} (ht : t∈Icc 0 frameCap) :
    -(1/2:ℝ)<curvature R 1 M t-phi t := by
  have hc := B_curvature_line ht
  have hp := phi_quadratic_upper ht
  nlinarith [sq_nonneg (t-137/200)]

lemma H_second_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    curvature R k0 1 (-t)-Real.cos t<-(563/1000:ℝ) := by
  have hc := curvature_signed_tangent
    (by norm_num [k0] : 0<k0) (by norm_num [k0] : k0≤(1:ℝ))
    (by norm_num [k0] : (1:ℝ)≤2*k0)
    (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)
  have hC1 := mul_le_mul_of_nonneg_right H_zero_curvature_slope.le ht.1
  have hcos := cos_lower_two ht.1
  have hquad := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  dsimp [frameCap] at ht hquad
  nlinarith [H_zero_curvature]

def excess (N : ℝ) : ℝ := U R 1 M frameCap-U R 1 M (frameCap-N)+V R k0 1 N
def excessD (N : ℝ) : ℝ := Ud 1 M (frameCap-N)+Vd R k0 1 N

theorem excess_derivative {N : ℝ} (hN : N∈Icc 0 frameCap) :
    HasDerivAt excess (excessD N) N := by
  have hd := (U_hasDerivAt (by norm_num : (0:ℝ)<1) (by norm_num [M] : 0<M)
    (show frameCap-N∈Icc 0 frameCap from ⟨by linarith [hN.2],by linarith [hN.1]⟩)).
      comp N ((hasDerivAt_id N).const_sub frameCap)
  have hv := V_hasDerivAt (R:=R) (by norm_num [k0] : 0<k0) (by norm_num : (0:ℝ)<1) hN
  convert (hd.const_sub (U R 1 M frameCap)).add hv using 1 <;>
    dsimp [excess,excessD] <;> ring

theorem excessD_derivative {N : ℝ} (hN : N∈Icc 0 frameCap) :
    HasDerivAt excessD
      (-(curvature R 1 M (frameCap-N)-phi (frameCap-N))+
        (curvature R k0 1 (-N)-Real.cos N)) N := by
  have hd := (Ud_hasDerivAt (by norm_num : (0:ℝ)<1) (by norm_num [M] : 0<M)
    (show frameCap-N∈Icc 0 frameCap from ⟨by linarith [hN.2],by linarith [hN.1]⟩)).
      comp N ((hasDerivAt_id N).const_sub frameCap)
  have hv := Vd_hasDerivAt (R:=R) (by norm_num [k0] : 0<k0)
    (by norm_num : (0:ℝ)<1) hN
  convert hd.add hv using 1 <;> dsimp [excessD] <;> ring

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
  have hm0 : 0<m := by linarith [hm.1]
  let f : ℝ→ℝ := fun t =>
    (U R 1 m P-U R 1 m (P-t))-(U R 1 M frameCap-U R 1 M (frameCap-t))
  have hd (t : ℝ) (ht : t∈Icc 0 P) : HasDerivAt f
      (Ud 1 m (P-t)-Ud 1 M (frameCap-t)) t := by
    have hsmall := (U_hasDerivAt (by norm_num : (0:ℝ)<1) hm0
      (show P-t∈Icc 0 frameCap from ⟨by linarith [ht.2],by linarith [ht.1]⟩)).
        comp t ((hasDerivAt_id t).const_sub P)
    have hlarge := (U_hasDerivAt (by norm_num : (0:ℝ)<1) (by norm_num [M] : 0<M)
      (show frameCap-t∈Icc 0 frameCap from ⟨by linarith [ht.2],by linarith [ht.1]⟩)).
        comp t ((hasDerivAt_id t).const_sub frameCap)
    convert (hsmall.const_sub (U R 1 m P)).sub
      (hlarge.const_sub (U R 1 M frameCap)) using 1 <;> dsimp [f] <;> ring
  have hmono : MonotoneOn f (Icc 0 P) := by
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
  dsimp [f] at hh
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
    (by norm_num [k0] : 0<k0) hk.1 hk.2 hn
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveBT.LowRectangle
