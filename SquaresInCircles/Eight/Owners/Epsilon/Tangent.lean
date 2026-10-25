module

public import SquaresInCircles.Eight.Owners.E.ZeroHessian
public import SquaresInCircles.Eight.Owners.Epsilon.ActiveRates

/-!
# Eight squares: the original E transverse parameter and the active cap comparison

The scalar g is computed from the same original E
circle at every tangent b.  Its decrease is bounded between zero and one.
If D's diagonal cap is inactive, the actual total angle is below .11 and
the primary K reserve dominates the angular K gain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EpsilonTangent
open EpsilonCapCalculus

def g (a b : ℝ) : ℝ := (1+Real.cos a+Real.sin a)/2-EpsilonCapCalculus.f b*Real.sin a-b*Real.cos a
def decrease (a b : ℝ) : ℝ := Real.cos a-ratio b*Real.sin a

theorem E_root_bounds {b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    (9/5 : ℝ)<R b ∧ R b<383/200 ∧ (R b)^2=qCap-(b+1/2)^2 := by
  have hlo : 0≤b+1/2 := by linarith [hb.1]
  have hhi : b+1/2≤131/200 := by linarith [hb.2]
  have hs := pow_le_pow_left₀ hlo hhi 2
  have hr : 0≤qCap-(b+1/2)^2 := by dsimp [qCap]; nlinarith
  have hsq := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (qCap-(b+1/2)^2)
  have hlow := pow_le_pow_left₀ (show (0:ℝ)≤1/2 by norm_num)
    (show 1/2≤b+1/2 by linarith [hb.1]) 2
  dsimp [R,qCap]
  dsimp [qCap] at hsq
  exact ⟨by nlinarith,by nlinarith,hsq⟩

theorem E_ratio_bounds {b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    0<ratio b ∧ ratio b<1 := by
  have hr := E_root_bounds hb
  have hp : 0<R b := by linarith [hr.1]
  dsimp [ratio]
  exact ⟨div_pos (by linarith [hb.1]) hp,
    (div_lt_one hp).2 (by linarith [hb.2,hr.1])⟩

theorem E_f_hasDerivAt {b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    HasDerivAt EpsilonCapCalculus.f (-ratio b) b := by
  have hr := E_root_bounds hb
  have hp : 0<R b := by linarith [hr.1]
  have hne : qCap-(b+1/2)^2≠0 := by nlinarith [hr.2.2]
  have hh := (((((hasDerivAt_id b).add_const (1/2)).pow 2).const_sub qCap).sqrt hne).sub_const
    (1/2)
  convert hh using 1
  · rfl
  · dsimp [ratio,R]
    field_simp

theorem decrease_bounds {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) : 0<decrease a b ∧ decrease a b≤1 := by
  have ht : a∈Icc 0 (7/10 : ℝ) := ⟨ha.1,by linarith [ha.2]⟩
  have hh := transport_trig ht
  have hr := E_ratio_bounds hb
  have hmul := mul_le_mul_of_nonneg_right hr.2.le hh.2.2.1
  have hmul0 := mul_nonneg hr.1.le hh.2.2.1
  dsimp [decrease]
  exact ⟨by linarith [hh.2.2.2.2],by linarith [hh.2.1]⟩

theorem g_hasDerivAt {a b : ℝ} (hb : b∈Icc (0:ℝ) (31/200)) :
    HasDerivAt (g a) (-decrease a b) b := by
  have hf := E_f_hasDerivAt hb
  have hh := ((hf.const_mul (Real.sin a)).const_sub ((1+Real.cos a+Real.sin a)/2)).fun_sub
    ((hasDerivAt_id' b).mul_const (Real.cos a))
  convert hh using 1
  · funext x
    simp only [g]
    ring
  · dsimp [decrease]
    ring

theorem g_antitone {a : ℝ} (ha : a∈Icc 0 (11/50 : ℝ)) :
    AntitoneOn (g a) (Icc (0:ℝ) (31/200)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (g_hasDerivAt hb).continuousAt.continuousWithinAt
  · exact fun b hb => g_hasDerivAt (Ioo_subset_Icc_self hb)
  · exact fun b hb => (neg_nonpos.mpr (decrease_bounds ha (Ioo_subset_Icc_self hb)).1.le)

theorem g_bounds {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) : (1/2 : ℝ)<g a b ∧ g a b≤1-b := by
  have ht : a∈Icc 0 (7/10 : ℝ) := ⟨ha.1,by linarith [ha.2]⟩
  have hh := transport_trig ht
  have hr := E_root_bounds hb
  have hf : (1/2 : ℝ)<EpsilonCapCalculus.f b ∧ EpsilonCapCalculus.f b<283/200 := by
    dsimp [EpsilonCapCalculus.f]
    exact ⟨by linarith [hr.1],by linarith [hr.2.1]⟩
  have hs : Real.sin a≤11/50 := (Real.sin_le ha.1).trans ha.2
  have hfs := mul_le_mul hf.2.le hs hh.2.2.1 (by norm_num)
  have hbc := mul_le_mul_of_nonneg_left hh.2.1 hb.1
  have hw : 1≤(1+Real.cos a+Real.sin a)/2 := by
    rw [← edgeWidth_positive_formula ht]
    exact edgeWidth_ge_one _
  have hterm1 := mul_nonpos_of_nonpos_of_nonneg (show b-1/2≤0 by linarith [hb.2])
    (show 0≤1-Real.cos a by linarith [hh.2.1])
  have hterm2 := mul_nonneg (show 0≤EpsilonCapCalculus.f b-1/2 by linarith [hf.1]) hh.2.2.1
  have heq : g a b=1-b+(b-1/2)*(1-Real.cos a)-(EpsilonCapCalculus.f b-1/2)*Real.sin a := by
    dsimp [g]
    ring
  constructor
  · dsimp [g]
    linarith [hb.2]
  · rw [heq]
    linarith

theorem g_zero (a : ℝ) : g a 0=EZeroFunctions.u a-1/2 := by
  dsimp [g,EZeroFunctions.u,EpsilonCapCalculus.f,R,EZeroFunctions.v]
  simp only [zero_add,zero_mul,sub_zero]
  norm_num
  ring

theorem g_zero_endpoint : g (11/100) 0<diagonalCoordinate qCap := by
  have hb := trig_bracket (l := (11/100 : ℝ)) (u := (11/100 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) (by constructor <;> rfl)
  have hv := EZeroFunctions.v_bounds
  have hs : (1097/10000 : ℝ)<Real.sin (11/100) := by norm_num at hb; linarith [hb.1]
  have hc : Real.cos (11/100)<(497/500 : ℝ) := by norm_num at hb; linarith [hb.2.2.2]
  have hvs : (457/500 : ℝ)*(1097/10000)<EZeroFunctions.v*Real.sin (11/100) := by
    have h1 := mul_lt_mul_of_pos_right (show (457/500 : ℝ)<EZeroFunctions.v by linarith)
      (show 0<Real.sin (11/100) by linarith)
    have h2 := mul_lt_mul_of_pos_left hs (show (0:ℝ)<457/500 by norm_num)
    linarith
  rw [g_zero]
  dsimp [EZeroFunctions.u]
  linarith [EpsilonActiveRates.diagonal_bounds.1]

theorem active_angle {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) (hactive : diagonalCoordinate qCap≤g a b) :
    a∈Icc 0 (11/100 : ℝ) := by
  have hmono := g_antitone ha (show (0:ℝ)∈Icc 0 (31/200) by norm_num) hb hb.1
  refine ⟨ha.1,?_⟩
  by_contra! hbad
  have hu := EZeroFunctions.u_antitone (show (11/100 : ℝ)∈Icc 0 (7/10) by norm_num)
    (show a∈Icc 0 (7/10 : ℝ) from ⟨ha.1,by linarith [ha.2]⟩) hbad.le
  rw [g_zero] at hmono
  have he := g_zero_endpoint
  rw [g_zero] at he
  linarith

theorem initial_deficit {a : ℝ} (ha : a∈Icc 0 (11/100 : ℝ)) :
    (891/1000 : ℝ)*a≤1-g a 0 := by
  have hder (t : ℝ) : HasDerivAt (fun z => -EZeroFunctions.u z) (EZeroFunctions.j t) t := by
    have h := (EZeroFunctions.u_hasDerivAt t).const_sub 0
    simp only [zero_sub,neg_neg] at h
    exact h
  have hrate (t : ℝ) (ht : t∈Ioo 0 (11/100 : ℝ)) : (891/1000 : ℝ)≤EZeroFunctions.j t := by
    have htrig := EZeroHessian.trig (show t∈Icc 0 (11/100 : ℝ) from Ioo_subset_Icc_self ht)
      (show (0:ℝ)∈Icc 0 (11/100) by norm_num)
    have hv := EZeroFunctions.v_bounds
    have hc : (99/100 : ℝ)<Real.cos t := by
      have hsq := pow_le_pow_left₀ ht.1.le ht.2.le 2
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := t)]
    have hs : 0≤Real.sin t := by simpa using htrig.2.2.1
    have hm := mul_lt_mul_of_pos_right (show (457/500 : ℝ)<EZeroFunctions.v by linarith)
      (show 0<Real.cos t by linarith)
    dsimp [EZeroFunctions.j]
    nlinarith
  have hh := derivative_reserve
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t _ => hder t) hrate
    (show (0:ℝ)∈Icc 0 (11/100) by norm_num) ha ha.1
  rw [g_zero]
  norm_num [EZeroFunctions.u] at hh ⊢
  linarith

theorem active_K {a b : ℝ} (ha : a∈Icc 0 (11/50 : ℝ))
    (hb : b∈Icc (0:ℝ) (31/200)) (hactive : diagonalCoordinate qCap≤g a b) :
    K a (g a b)≤K 0 1 ∧ K 0 (g a b)≤K a 1 := by
  have has := active_angle ha hb hactive
  have hg := g_bounds ha hb
  have hx : g a b∈Icc (diagonalCoordinate qCap) 1 := ⟨hactive,by linarith [hg.2,hb.1]⟩
  have h1 : (1:ℝ)∈Icc (diagonalCoordinate qCap) 1 :=
    ⟨by linarith [EpsilonActiveRates.diagonal_bounds.2],le_rfl⟩
  have hp := EpsilonActiveRates.primary_growth has hx h1 hx.2
  have hangle := EpsilonActiveRates.angular_growth has h1
  have hgb := g_antitone ha (show (0:ℝ)∈Icc 0 (31/200) by norm_num) hb hb.1
  have hdef := initial_deficit has
  have hm := K_monotone (show (0:ℝ)∈Icc 0 (11/50) by norm_num)
    (EpsilonActiveRates.primary_mem hx) (by norm_num) hx.2
  exact ⟨by linarith,hm.trans hangle.1⟩

end SquaresInCircles.Eight.EpsilonTangent
