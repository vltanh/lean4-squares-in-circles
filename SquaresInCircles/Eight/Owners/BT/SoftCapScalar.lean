module

public import SquaresInCircles.Eight.Owners.BT.ErrorComparisons
public import SquaresInCircles.Eight.Owners.BT.TailTransfer

/-!
# Eight squares: the full positive-AB2 scalar for the additional prefix charge

The small-error range uses the sorted diagonal support.  The large
range uses one full-circle radical whose second derivative is
positive; its charge is concave and has positive rational endpoint
reserves.  Both arguments apply to the actual original A disk.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.SoftCap

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def N (v : ℝ) : ℝ := Real.sqrt (4+kappa^2-4*kappa*Real.cos v)
def Nd (v : ℝ) : ℝ := 2*kappa*Real.sin v/N v
def Ndd (v : ℝ) : ℝ :=
  2*kappa*(2-kappa*Real.cos v)*(2*Real.cos v-kappa)/(N v)^3
def largeCharge (v : ℝ) : ℝ :=
  v+2*(Real.sin v+Real.cos v)-1-kappa/2+(2-kappa)*c0-R*N v
def largeD (v : ℝ) : ℝ := 1+2*(Real.cos v-Real.sin v)-R*Nd v
def largeDD (v : ℝ) : ℝ := -2*(Real.sin v+Real.cos v)-R*Ndd v

theorem energy_positive (v : ℝ) : 0<4+kappa^2-4*kappa*Real.cos v := by
  dsimp [kappa]
  nlinarith [Real.cos_le_one v]

theorem N_pos (v : ℝ) : 0<N v := Real.sqrt_pos.mpr (energy_positive v)
theorem N_sq (v : ℝ) : (N v)^2=4+kappa^2-4*kappa*Real.cos v :=
  Real.sq_sqrt (energy_positive v).le

theorem N_deriv (v : ℝ) : HasDerivAt N (Nd v) v := by
  have hh := (((Real.hasDerivAt_cos v).const_mul (4*kappa)).const_sub (4+kappa^2)).sqrt
    (energy_positive v).ne'
  convert hh using 1
  · rfl
  · dsimp [Nd,N]
    ring

theorem Nd_deriv (v : ℝ) : HasDerivAt Nd (Ndd v) v := by
  have hn := (N_pos v).ne'
  have hh := ((Real.hasDerivAt_sin v).const_mul (2*kappa)).div (N_deriv v) hn
  have hinside : Real.cos v*(N v)^2-2*kappa*(Real.sin v)^2=
      (2-kappa*Real.cos v)*(2*Real.cos v-kappa) := by
    rw [N_sq]
    dsimp [kappa]
    nlinarith only [Real.sin_sq_add_cos_sq v]
  convert hh using 1
  · rfl
  · dsimp [Nd,Ndd]
    have hid : ((2*kappa*Real.cos v)*N v-(2*kappa*Real.sin v)*(2*kappa*Real.sin v/N v))/(N v)^2=
        2*kappa*(Real.cos v*(N v)^2-2*kappa*(Real.sin v)^2)/(N v)^3 := by
      field_simp
    rw [hid,hinside]
    ring

theorem Ndd_positive {v : ℝ} (hv : v∈Icc 0 frameCap) : 0<Ndd v := by
  have tr := transport_trig hv
  have hfirst : 0<2-kappa*Real.cos v := by
    dsimp [kappa]
    linarith [Real.cos_le_one v]
  have hsecond : 0<2*Real.cos v-kappa := by dsimp [kappa]; linarith [tr.1]
  exact div_pos
    (mul_pos (mul_pos (by norm_num [kappa]) hfirst) hsecond)
    (pow_pos (N_pos v) 3)

theorem large_deriv (v : ℝ) : HasDerivAt largeCharge (largeD v) v := by
  have h1 : HasDerivAt (fun y => y+2*(Real.sin y+Real.cos y))
      (1+2*(Real.cos v+-Real.sin v)) v :=
    (hasDerivAt_id' v).fun_add
      (((Real.hasDerivAt_sin v).fun_add (Real.hasDerivAt_cos v)).const_mul 2)
  have h2 : HasDerivAt (fun y => R*N y) (R*Nd v) v := (N_deriv v).const_mul R
  have h := (((h1.sub_const 1).sub_const (kappa/2)).add_const ((2-kappa)*c0)).fun_sub h2
  unfold largeCharge largeD
  exact h.congr_deriv (by ring)

theorem largeD_deriv (v : ℝ) : HasDerivAt largeD (largeDD v) v := by
  have h1 : HasDerivAt (fun y => 2*(Real.cos y-Real.sin y))
      (2*(-Real.sin v-Real.cos v)) v :=
    ((Real.hasDerivAt_cos v).fun_sub (Real.hasDerivAt_sin v)).const_mul 2
  have h2 : HasDerivAt (fun y => R*Nd y) (R*Ndd v) v := (Nd_deriv v).const_mul R
  have h := ((hasDerivAt_const v (1:ℝ)).fun_add h1).fun_sub h2
  unfold largeD largeDD
  exact h.congr_deriv (by ring)

theorem large_concave : ConcaveOn ℝ (Icc (2/5) frameCap) largeCharge := by
  apply concave_of_deriv2 (fun v _ => large_deriv v) (fun v _ => largeD_deriv v)
  intro v hv
  have hv' : v∈Icc 0 frameCap := ⟨by linarith [hv.1],hv.2⟩
  have hprod := mul_pos R_pos (Ndd_positive hv')
  have tr := transport_trig hv'
  dsimp [largeDD]
  linarith [tr.1,tr.2.2.1]

theorem N_two_fifths : N (2/5)<11621/10000 := by
  have hc := cos_lower_six (show (0:ℝ)≤2/5 by norm_num)
  have hs := N_sq (2/5)
  have hn := N_pos (2/5)
  norm_num [kappa] at hc hs
  nlinarith

theorem N_cap : N frameCap<14009/10000 := by
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hs := N_sq frameCap
  have hn := N_pos frameCap
  norm_num [kappa,frameCap] at hs
  norm_num at hc
  change N (7/10)<14009/10000
  change 0<N (7/10) at hn
  nlinarith

theorem large_two_fifths : (7/50:ℝ)<largeCharge (2/5) := by
  have hs := sin_lower_seven (show (0:ℝ)≤2/5 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤2/5 by norm_num)
  have hprod := mul_le_mul radius_upper.le N_two_fifths.le (N_pos (2/5)).le
    (by norm_num : (0:ℝ)≤1979/1000)
  have hc0 := c0_bounds.1
  norm_num at hs hc
  dsimp [largeCharge,kappa]
  nlinarith only [hs,hc,hprod,hc0]

theorem large_cap : (7/50:ℝ)<largeCharge frameCap := by
  have hs := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hprod := mul_le_mul radius_upper.le N_cap.le (N_pos frameCap).le
    (by norm_num : (0:ℝ)≤1979/1000)
  have hc0 := c0_bounds.1
  norm_num at hs hc
  dsimp [largeCharge,kappa,frameCap] at *
  nlinarith only [hs,hc,hprod,hc0]

theorem large_positive {v : ℝ} (hv : v∈Icc (2/5) frameCap) : 0<largeCharge v := by
  have hh := concave_gt_of_endpoints large_concave hv large_two_fifths large_cap
  linarith

theorem sorted_support (a : State) {f g : ℝ} (hf : 0≤f) (hfg : f≤g) :
    f*a.a+g*a.b≤(f+g)*c0 := by
  have hsum := state_sum_sharp a
  have hgap := mul_nonneg (sub_nonneg.mpr hfg) (sub_nonneg.mpr a.canonical)
  have hp := mul_le_mul_of_nonneg_left hsum (show 0≤f+g by linarith)
  nlinarith only [hgap,hp]

theorem small_charge (a : State) {v : ℝ} (hv : v∈Icc 0 (2/5:ℝ)) :
    0≤v+2*(GlobalOuterAnchor.width v-1)+(2-kappa)*c0-
      (2*Real.sin v*a.a+(2*Real.cos v-kappa)*a.b) := by
  have hv' : v∈Icc 0 frameCap := ⟨hv.1,by dsimp [frameCap]; linarith [hv.2]⟩
  have hs := Real.sin_le hv.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := v)
  have hsq := pow_le_pow_left₀ hv.1 hv.2 2
  have hfg : 2*Real.sin v≤2*Real.cos v-kappa := by
    dsimp [kappa]
    nlinarith only [hs,hc,hsq,hv.2]
  have hsupport := sorted_support a
    (show 0≤2*Real.sin v by linarith [(transport_trig hv').2.2.1]) hfg
  have hsum : Real.sin v+Real.cos v-1≤v := by linarith [Real.cos_le_one v]
  have hm := mul_le_mul_of_nonneg_left hsum (show 0≤2*c0-1 by linarith [c0_bounds.1])
  have hp := mul_nonneg (show 0≤2-2*c0 by linarith [c0_bounds.2]) hv.1
  rw [width_positive hv']
  nlinarith only [hsupport,hm,hp]

theorem norm_identity (v : ℝ) :
    Real.sqrt ((2*Real.sin v)^2+(2*Real.cos v-kappa)^2)=N v := by
  dsimp [N]
  congr 1
  linear_combination 4*(Real.sin_sq_add_cos_sq v)

theorem charge (a : State) {v : ℝ} (hv : v∈Icc 0 frameCap) :
    0≤v+2*(GlobalOuterAnchor.width v-1)+(2-kappa)*c0-
      (2*Real.sin v*a.a+(2*Real.cos v-kappa)*a.b) := by
  by_cases hsmall : v≤2/5
  · exact small_charge a ⟨hv.1,hsmall⟩
  · have hlarge := large_positive (show v∈Icc (2/5:ℝ) frameCap from ⟨by linarith,hv.2⟩)
    have hsupport := state_support a (2*Real.sin v) (2*Real.cos v-kappa)
    rw [norm_identity] at hsupport
    change 2*Real.sin v*a.a+(2*Real.cos v-kappa)*a.b≤
      R*N v-(2*Real.sin v+(2*Real.cos v-kappa))/2 at hsupport
    rw [width_positive hv]
    dsimp [largeCharge] at hlarge
    linarith only [hlarge,hsupport]

end SquaresInCircles.Eight.GlobalBT.SoftCap
