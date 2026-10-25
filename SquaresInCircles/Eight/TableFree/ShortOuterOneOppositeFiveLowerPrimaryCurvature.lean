module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveLowerPrimaryCalculus

/-!
# Whole-domain curvature and the increasing axial derivative

Uncompiled transcription of Section 3, equations (21)--(24). The
original numerical comparison gives C_yy > 1.20, hence the common 1.14
used in the completed square. The axial angular derivative increases
throughout every feasible prefix of the original angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerPrimary
open CommonQuarter CorePairGeometry Arithmetic

def numeratorFloor : ℝ := (487/500)*(7/4:ℝ)^3-(9/40)*(Q0-13/4)
def bracketFloor : ℝ := 20967/100000+(83048/100000)*numeratorFloor/(1291/1000:ℝ)^3
theorem fixed_curvature :
    0<numeratorFloor ∧ 0<bracketFloor ∧ (6/5:ℝ)<Q0/(383/200:ℝ)^3*bracketFloor := by
  norm_num [numeratorFloor,bracketFloor,Q0]

theorem numerator_lower {y u : ℝ} (hd : Domain y u) :
    numeratorFloor<Real.cos u*(T y u)^3+Real.sin u*(3*(z y u)^2+3*z y u+1-Q0) := by
  have hb := contact_bounds hd
  have tr := small_trig hd.1
  have hT := T_positive hd.2.1 hd.1
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/4) hb.2.2.1.le 3
  have hk := mul_lt_mul_of_pos_right tr.1 (pow_pos hT 3)
  have hcub := mul_le_mul_of_nonneg_left hcube (by norm_num : (0:ℝ)≤487/500)
  have hz : (13/4:ℝ)≤3*(z y u)^2+3*z y u+1 := by nlinarith [hb.1]
  have hdrop := mul_le_mul_of_nonneg_left
    (show (13/4:ℝ)-Q0≤3*(z y u)^2+3*z y u+1-Q0 by linarith) tr.2.1
  have hsmall := mul_le_mul_of_nonpos_right tr.2.2.le (by norm_num [Q0] : (13/4:ℝ)-Q0≤0)
  dsimp [numeratorFloor]
  nlinarith only [hk,hcub,hdrop,hsmall]

theorem targetSecond_lower (r : Bool) {y u : ℝ} (hd : Domain y u) :
    (6/5:ℝ)<targetSecond r y u := by
  obtain ⟨N, hNdef⟩ : ∃ N, N=Real.cos u*(T y u)^3+Real.sin u*(3*(z y u)^2+3*z y u+1-Q0) :=
    ⟨_, rfl⟩
  have hN : numeratorFloor<N := hNdef ▸ numerator_lower hd
  have hc := coefficient_bounds r
  have hq : 0<q r := by linarith [hc.2.2.1]
  have hV := V_positive hd
  have hX := X_positive hd.2.1
  have hb := contact_bounds hd
  have hVc := pow_le_pow_left₀ hV.le hb.2.2.2.1.le 3
  have hXc := pow_le_pow_left₀ hX.le hb.2.2.2.2.le 3
  have hqN := mul_lt_mul_of_pos_left hN hq
  have hqfloor := mul_le_mul_of_nonneg_right hc.2.2.1 fixed_curvature.1.le
  have hterm : (83048/100000)*numeratorFloor/(1291/1000:ℝ)^3<q r*N/(V y u)^3 := by
    apply (lt_div_iff₀ (pow_pos hV 3)).mpr
    have hh := mul_le_mul_of_nonneg_left hVc
      (show 0≤(83048/100000)*numeratorFloor/(1291/1000:ℝ)^3 from
        div_nonneg (mul_nonneg (by norm_num) fixed_curvature.1.le) (by norm_num))
    norm_num at hh ⊢
    linarith only [hh,hqN,hqfloor]
  have hp := mul_nonpos_of_nonpos_of_nonneg (show p r≤0 by linarith [hc.2.1]) (small_trig hd.1).2.1
  have hbracket : bracketFloor<P r-p r*Real.sin u+q r*N/(V y u)^3 := by
    dsimp [bracketFloor]
    linarith [hc.2.2.2.2.1]
  have hQ : 0<Q0 := by norm_num [Q0]
  have hmul := mul_lt_mul_of_pos_left hbracket hQ
  have hX3 := pow_pos hX 3
  have hA : 0<Q0*bracketFloor := mul_pos hQ fixed_curvature.2.1
  have h1 : Q0/(383/200:ℝ)^3*bracketFloor≤Q0*bracketFloor/(X y)^3 := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left hA.le hX3 hXc
  have h2 : Q0*bracketFloor/(X y)^3<Q0/(X y)^3*(P r-p r*Real.sin u+q r*N/(V y u)^3) := by
    rw [div_mul_eq_mul_div]
    exact div_lt_div_of_pos_right hmul hX3
  rw [targetSecond_identity r hd,← hNdef]
  exact fixed_curvature.2.2.trans (h1.trans_lt h2)

theorem axial_numerator_positive {u : ℝ} (hd : Domain (1/2) u) :
    0<Q0*(T (1/2) u)^2-K (1/2) u*(K (1/2) u-1)*(V (1/2) u)^2 := by
  have hb := contact_bounds hd
  have hc := circle (u:=u) hd.2.1
  have hv := V_sq hd
  have hk : (3/2:ℝ)≤K (1/2) u ∧ K (1/2) u<383/200 := by
    dsimp [K]
    exact ⟨by linarith [hb.1],by linarith [hb.2.1]⟩
  have hT : Q0-(183/200:ℝ)^2<(T (1/2) u)^2 := by nlinarith [hb.1,hb.2.1]
  have hV : (V (1/2) u)^2≤Q0-9/4 := by nlinarith [hk.1]
  have hKz : K (1/2) u*(K (1/2) u-1)≤(383/200:ℝ)*(183/200) := by
    have hh := mul_le_mul hk.2.le
      (show K (1/2) u-1≤183/200 by linarith [hk.2])
      (by linarith [hk.1]) (by norm_num : (0:ℝ)≤383/200)
    exact hh
  have hprod := mul_le_mul hKz hV (sq_nonneg (V (1/2) u)) (by norm_num : (0:ℝ)≤(383/200)*(183/200))
  have hQT := mul_lt_mul_of_pos_left hT (by norm_num [Q0] : 0<Q0)
  norm_num [Q0] at hprod hQT ⊢
  linarith
theorem JD_positive (r : Bool) {u : ℝ} (hd : Domain (1/2) u) : 0<JD r u := by
  have hc := coefficient_bounds r
  have hq : 0<q r/(V (1/2) u)^3 :=
    div_pos (by linarith [hc.2.2.1]) (pow_pos (V_positive hd) 3)
  have hh := mul_pos hq (axial_numerator_positive hd)
  have hp := mul_nonpos_of_nonpos_of_nonneg (show p r≤0 by linarith [hc.2.1])
    (show 0≤K (1/2) u-1 by dsimp [K]; linarith [(contact_bounds hd).1])
  dsimp [JD]
  linarith
theorem J_monotone (r : Bool) {u : ℝ} (hd : Domain (1/2) u) :
    MonotoneOn (J r) (Icc 0 u) :=
  monoOn_of_hasDeriv_nonneg
    (fun v hv => (J_hasDerivAt r (angle_interval hd hv)).continuousAt.continuousWithinAt)
    (fun v hv => J_hasDerivAt r (angle_interval hd (Ioo_subset_Icc_self hv)))
    (fun v hv => (JD_positive r (angle_interval hd (Ioo_subset_Icc_self hv))).le)

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerPrimary
