module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighQuadratic

/-!
# The complete original high-secondary augmented charge

Every target sign and radial kind is permitted.  The original source
is outer and its unchanged marker correction is retained.  Negative
errors use either the whole-arc quadratic reserve or one concave
derivative on the complete angle interval.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh

open FramePair FrameCircleArc FrameLowArc FrameMidArc GlobalOuterAnchor

def quarterCharge (s : State) (Y d : ℝ) : ℝ := d+potential s-kappa*Y
def secondaryNegative (s : State) (z : ℝ) : ℝ :=
  -z+kappa*((s.b+1/2)*Real.sin z+(s.a-1/2)*(1-Real.cos z))+rho*J s
def secondaryNegativeD (s : State) (z : ℝ) : ℝ :=
  -1+kappa*((s.b+1/2)*Real.cos z+(s.a-1/2)*Real.sin z)
def secondaryNegativeDD (s : State) (z : ℝ) : ℝ :=
  kappa*(-(s.b+1/2)*Real.sin z+(s.a-1/2)*Real.cos z)
def secondaryNegativeDDD (s : State) (z : ℝ) : ℝ :=
  -kappa*((s.b+1/2)*Real.cos z+(s.a-1/2)*Real.sin z)

theorem secondaryNegative_derivative (s : State) (z : ℝ) :
    HasDerivAt (secondaryNegative s) (secondaryNegativeD s z) z := by
  have h := ((hasDerivAt_id z).neg.add
    ((((Real.hasDerivAt_sin z).const_mul (s.b+1/2)).add
      (((Real.hasDerivAt_cos z).const_sub 1).const_mul (s.a-1/2))).const_mul kappa)).add_const
    (rho*J s)
  convert h using 1
  · funext x
    simp only [secondaryNegative,Pi.add_apply,Pi.neg_apply,id]
  · simp only [secondaryNegativeD]
    ring

theorem secondaryNegative_second_derivative (s : State) (z : ℝ) :
    HasDerivAt (secondaryNegativeD s) (secondaryNegativeDD s z) z := by
  have h := ((((Real.hasDerivAt_cos z).const_mul (s.b+1/2)).add
    ((Real.hasDerivAt_sin z).const_mul (s.a-1/2))).const_mul kappa).const_add (-1)
  convert h using 1
  · funext x
    simp only [secondaryNegativeD,Pi.add_apply]
  · simp only [secondaryNegativeDD]
    ring

theorem secondaryNegative_third_derivative (s : State) (z : ℝ) :
    HasDerivAt (secondaryNegativeDD s) (secondaryNegativeDDD s z) z := by
  have h := (((Real.hasDerivAt_sin z).const_mul (-(s.b+1/2))).add
    ((Real.hasDerivAt_cos z).const_mul (s.a-1/2))).const_mul kappa
  convert h using 1
  · funext x
    simp only [secondaryNegativeDD,Pi.add_apply]
  · simp only [secondaryNegativeDDD]
    ring

theorem secondaryNegativeD_concave (s : State) (hs : s.branch.type≠0) :
    ConcaveOn ℝ (Icc 0 frameCap) (secondaryNegativeD s) := by
  apply concave_of_deriv2 (fun z _ => secondaryNegative_second_derivative s z)
    (fun z _ => secondaryNegative_third_derivative s z)
  intro z hz
  have ha := (A_bounds (state_outer_chart s hs).2).1
  rw [← (state_outer_chart s hs).1] at ha
  have tr := transport_trig hz
  have hp := mul_nonneg (show 0≤ s.b+1/2 by linarith [s.b_nonneg])
    (show 0≤Real.cos z by linarith [tr.1])
  have hq := mul_nonneg (show 0≤ s.a-1/2 by linarith [c0_bounds.1]) tr.2.2.1
  dsimp [secondaryNegativeDDD,kappa]
  linarith

theorem secondaryNegativeD_right (s : State) (hs : s.branch.type≠0)
    (hb : primaryThreshold≤ s.b) : (1/50:ℝ)<secondaryNegativeD s frameCap := by
  have ha := (A_bounds (state_outer_chart s hs).2).1
  rw [← (state_outer_chart s hs).1] at ha
  have ht : 1≤kappa*(s.b+1/2) := by
    dsimp [primaryThreshold,kappa] at hb ⊢
    linarith
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hsine := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  norm_num at hc hsine
  have hc0 : 0≤Real.cos frameCap := by dsimp [frameCap]; linarith
  have hsin0 : 0≤Real.sin frameCap := by dsimp [frameCap]; linarith
  have hp := mul_le_mul_of_nonneg_right ht hc0
  have hq := mul_le_mul_of_nonneg_right
    (show (399/1000:ℝ)≤ s.a-1/2 by linarith [diagonal_bounds.1]) hsin0
  dsimp [secondaryNegativeD,kappa,frameCap] at *
  nlinarith only [hp,hq,hc,hsine]

theorem secondaryNegativeD_nonnegative (s : State) (hs : s.branch.type≠0)
    (hb : primaryThreshold≤ s.b) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0≤ secondaryNegativeD s z := by
  have h0 : 0≤ secondaryNegativeD s 0 := by
    norm_num [secondaryNegativeD] at ⊢
    dsimp [primaryThreshold,kappa] at hb ⊢
    linarith
  have h1 : 0≤ secondaryNegativeD s frameCap := by
    linarith [secondaryNegativeD_right s hs hb]
  exact (le_min h0 h1).trans
    ((secondaryNegativeD_concave s hs).min_le_of_mem_Icc
      ⟨le_rfl,hz.1.trans hz.2⟩ ⟨hz.1.trans hz.2,le_rfl⟩ hz)

theorem secondaryNegativeD_high (s : State) (hs : s.branch=.high)
    {z : ℝ} (hz : z∈Icc 0 frameCap) : (1/50:ℝ)≤ secondaryNegativeD s z := by
  have hsOuter : s.branch.type≠0 := by simp [hs,Branch.type]
  have hb := (FrameHighArc.state_high_chart s hs).2.1
  have hthreshold : primaryThreshold≤ s.b := by linarith [threshold_domain.2]
  have h0 : (1/50:ℝ)≤ secondaryNegativeD s 0 := by
    norm_num [secondaryNegativeD,kappa] at ⊢
    linarith [b2_bounds.1]
  have h1 := (secondaryNegativeD_right s hsOuter hthreshold).le
  exact (le_min h0 h1).trans
    ((secondaryNegativeD_concave s hsOuter).min_le_of_mem_Icc
      ⟨le_rfl,hz.1.trans hz.2⟩ ⟨hz.1.trans hz.2,le_rfl⟩ hz)

theorem secondaryNegative_large (s : State) (hs : s.branch.type≠0)
    (hb : primaryThreshold≤ s.b) {z : ℝ} (hz : z∈Ioc 0 frameCap) :
    0<secondaryNegative s z := by
  have hmono : MonotoneOn (secondaryNegative s) (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t _ => (secondaryNegative_derivative s t).continuousAt.continuousWithinAt
    · exact fun t _ => secondaryNegative_derivative s t
    · exact fun t ht => secondaryNegativeD_nonnegative s hs hb (Ioo_subset_Icc_self ht)
  have hbase := hmono (by norm_num [frameCap]) (Ioc_subset_Icc_self hz) hz.1.le
  have hzero : secondaryNegative s 0=rho*J s := by simp [secondaryNegative]
  rw [hzero] at hbase
  by_cases hJ : 0<J s
  · exact (mul_pos (by norm_num [rho] : 0<rho) hJ).trans_le hbase
  · have hJzero : J s=0 := le_antisymm (le_of_not_gt hJ) (J_nonnegative s hs)
    have hhigh := (J_eq_zero_iff s hs).1 hJzero
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => secondaryNegative s t-t/50)
        (secondaryNegativeD s t-1/50) t :=
      (secondaryNegative_derivative s t).sub ((hasDerivAt_id t).div_const 50)
    have hm : MonotoneOn (fun t : ℝ => secondaryNegative s t-t/50) (Icc 0 frameCap) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun t _ => (hd t).continuousAt.continuousWithinAt
      · exact fun t _ => hd t
      · intro t ht
        linarith [secondaryNegativeD_high s hhigh (Ioo_subset_Icc_self ht)]
    have hh := hm (by norm_num [frameCap]) (Ioc_subset_Icc_self hz) hz.1.le
    simp only at hh
    rw [hzero,hJzero] at hh
    norm_num at hh
    linarith [hz.1]

theorem secondaryNegative_quadratic_lower (s : State) (hs : s.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    rho*J s+(kappa*(s.b+1/2)-1)*z+kappa*quadraticD s*z^2≤ secondaryNegative s z := by
  have hA := (A_bounds (state_outer_chart s hs).2).1
  rw [← (state_outer_chart s hs).1] at hA
  have ha : 0≤ s.a-1/2 := by linarith [c0_bounds.1]
  have hb : 0≤ s.b+1/2 := by linarith [s.b_nonneg]
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_ge_sub_cube hz.1) hb
  have hcos := mul_le_mul_of_nonneg_left (cos_upper_four hz.1) ha
  have h3 : z^3≤(7/10)*z^2 := by
    have hh := mul_le_mul_of_nonneg_right hz.2 (sq_nonneg z)
    dsimp [frameCap] at hh
    nlinarith only [hh]
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h4 : z^4≤(49/100)*z^2 := by
    have hh := mul_le_mul_of_nonneg_right h2 (sq_nonneg z)
    dsimp [frameCap] at hh
    nlinarith only [hh]
  have h3b := mul_le_mul_of_nonneg_left h3 hb
  have h4a := mul_le_mul_of_nonneg_left h4 ha
  dsimp [secondaryNegative,quadraticD,quadraticR,quadraticS,kappa]
  nlinarith only [hsin,hcos,h3b,h4a]

theorem positive_quadratic {A B C z : ℝ} (hA : 0<A) (hdisc : B^2<4*A*C) :
    0<A*z^2+B*z+C := by
  have hid : 4*A*(A*z^2+B*z+C)=(2*A*z+B)^2+(4*A*C-B^2) := by ring
  have hp : 0<4*A*(A*z^2+B*z+C) := by linarith [sq_nonneg (2*A*z+B)]
  exact (mul_pos_iff_of_pos_left (by linarith : 0<4*A)).1 hp

theorem secondaryNegative_small (s : State) (hs : s.branch.type≠0)
    (hb : s.b<primaryThreshold) {z : ℝ} (hz : z∈Icc 0 frameCap) :
    0<secondaryNegative s z := by
  have hreserve := correction_quadratic s hs hb
  have hA : 0<kappa*quadraticD s := mul_pos (by norm_num [kappa]) hreserve.1
  have hdisc : (kappa*(s.b+1/2)-1)^2<4*(kappa*quadraticD s)*(rho*J s) := by
    nlinarith only [hreserve.2]
  have hp := positive_quadratic (z:=z) hA hdisc
  have hl := secondaryNegative_quadratic_lower s hs hz
  linarith

/-- The original owner-2 projection has the common augmented charge,
with strict gain at every nonzero original error. -/
theorem secondary_charge (s : State) (hs : s.branch.type≠0) {Y d : ℝ}
    (hd : |d|≤frameCap)
    (hm : GlobalOuterAnchor.width d≤ s.a*Real.cos d+s.b*Real.sin d-Y) :
    kappa≤quarterCharge s Y d ∧ (d≠0 → kappa<quarterCharge s Y d) := by
  have hJ := J_nonnegative s hs
  have houter := state_outer_chart s hs
  have hab := A_bounds houter.2
  rw [← houter.1] at hab
  by_cases hd0 : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hd0,(le_abs_self d).trans hd⟩
    have tr := transport_trig hd'
    have hsin := Real.sin_le hd0
    have hfirst := mul_nonneg (show 0≤ s.a-1/2 by linarith [c0_bounds.1])
      (sub_nonneg.mpr (Real.cos_le_one d))
    have hsecond := mul_nonneg (show 0≤(9/10:ℝ)-s.b by linarith [houter.2.2,c0_bounds.2])
      tr.2.2.1
    dsimp [GlobalOuterAnchor.width] at hm
    rw [abs_of_nonneg tr.2.2.1] at hm
    have hgain : (147/250)*d≤quarterCharge s Y d-kappa := by
      dsimp [quarterCharge,potential,kappa,rho]
      nlinarith only [hm,hJ,hfirst,hsecond,hsin]
    refine ⟨by linarith,?_⟩
    intro hdne
    have hdpos : 0<d := lt_of_le_of_ne hd0 (Ne.symm hdne)
    linarith
  · have hz : -d∈Ioc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hscalar : 0<secondaryNegative s (-d) := by
      rcases lt_or_ge s.b primaryThreshold with hb | hb
      · exact secondaryNegative_small s hs hb (Ioc_subset_Icc_self hz)
      · exact secondaryNegative_large s hs hb hz
    have hsine := (transport_trig (Ioc_subset_Icc_self hz)).2.2.1
    have hsinneg : Real.sin d= -Real.sin (-d) := by simp
    have hcosneg : Real.cos d=Real.cos (-d) := by simp
    dsimp [GlobalOuterAnchor.width] at hm
    rw [hsinneg,hcosneg,abs_neg,abs_of_nonneg hsine] at hm
    have hgain : secondaryNegative s (-d)≤quarterCharge s Y d-kappa := by
      dsimp [secondaryNegative,quarterCharge,potential,kappa,rho]
      nlinarith only [hm]
    exact ⟨by linarith,fun _ => by linarith⟩

end SquaresInCircles.Eight.TableFree.GlobalAllHigh
