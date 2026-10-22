module

public import SquaresInCircles.Eight.TableFree.GlobalGATargetZeroErrors
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# The one-variable outer target support

Uncompiled transcription of Section 5 of
`HAND_G3_HIGH_GA_TARGET_HAS_SMALL_TANGENT.md`.
The radical is used only on its actual feasible interval. In particular,
no differentiability assertion is made at the infeasible angle zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Target.Outer
open FramePair FrameCircleArc Arithmetic

def S : ℝ := Real.sqrt (Q0-1)
def P : ℝ := S-1
def K (u : ℝ) : ℝ := 1+Real.cos u-P*Real.sin u
def Y (u : ℝ) : ℝ := Real.sqrt (Q0-K u^2)
def C (u : ℝ) : ℝ := Real.cos u+Real.sin u/S
def Cd (u : ℝ) : ℝ := -Real.sin u+Real.cos u/S
def U (u : ℝ) : ℝ := Real.sin u+P*Real.cos u
def B (u : ℝ) : ℝ := K u^2*(1+C u^2)-Q0
def N (d : ℝ) : ℝ := Q0*(1+P^2)-Q0*(2*d^2+d)+d*(d+1)^3
def weight (u : ℝ) : ℝ := m*K u/Y u
def J (u : ℝ) : ℝ := u+m*(2-Y u)+(9/100)*(Real.sin u+Real.cos u-1)
def Jd (u : ℝ) : ℝ := 1-m*K u*U u/Y u+(9/100)*(Real.cos u-Real.sin u)
def Jdd (u : ℝ) : ℝ := m*N (K u-1)/Y u^3-(9/100)*(Real.sin u+Real.cos u)

def Domain (u : ℝ) : Prop := u∈Icc 0 frameCap ∧ K u≤a0+1/2

theorem S_bounds : (2134391/1250000:ℝ)<S ∧ S<17075129/10000000 := by
  have hs := Real.sq_sqrt (by norm_num [Q0] : 0≤Q0-1)
  have hp := Real.sqrt_nonneg (Q0-1)
  dsimp [S,Q0] at *
  constructor <;> nlinarith

theorem S_pos : 0<S := by linarith [S_bounds.1]
theorem S_sq : S^2=Q0-1 := Real.sq_sqrt (by norm_num [Q0])
theorem P_bounds : (7/10:ℝ)<P ∧ P<7075129/10000000 := by
  dsimp [P]
  constructor <;> linarith [S_bounds.1,S_bounds.2]

theorem inv_S_bounds : (0:ℝ)<1/S ∧ 1/S<10/17 := by
  exact ⟨div_pos (by norm_num) S_pos,
    (div_lt_iff₀ S_pos).2 (by linarith [S_bounds.1])⟩

theorem K_hasDerivAt (u : ℝ) : HasDerivAt K (-U u) u := by
  convert ((Real.hasDerivAt_cos u).const_add 1).sub
    ((Real.hasDerivAt_sin u).const_mul P) using 1 <;> dsimp [K,U] <;> ring

theorem U_hasDerivAt (u : ℝ) :
    HasDerivAt U (Real.cos u-P*Real.sin u) u := by
  convert (Real.hasDerivAt_sin u).add ((Real.hasDerivAt_cos u).const_mul P)
    using 1 <;> dsimp [U] <;> ring

theorem C_hasDerivAt (u : ℝ) : HasDerivAt C (Cd u) u :=
  (Real.hasDerivAt_cos u).add ((Real.hasDerivAt_sin u).div_const S)

theorem Cd_hasDerivAt (u : ℝ) : HasDerivAt Cd (-C u) u := by
  convert (Real.hasDerivAt_sin u).neg.add ((Real.hasDerivAt_cos u).div_const S)
    using 1 <;> dsimp [C,Cd] <;> ring

theorem K_bounds {u : ℝ} (hu : u∈Icc 0 frameCap) : (13/10:ℝ)<K u ∧ K u≤2 := by
  have ht := transport_trig hu
  have hprod := mul_lt_mul P_bounds.2 ht.2.2.2.1 ht.2.2.1
    (by norm_num : (0:ℝ)<7075129/10000000)
  have hnonneg := mul_nonneg (by linarith [P_bounds.1] : 0≤P) ht.2.2.1
  dsimp [K]
  exact ⟨by linarith [ht.1],by linarith [ht.2.1]⟩

theorem U_increasing_derivative {u : ℝ} (hu : u∈Icc 0 frameCap) :
    0<Real.cos u-P*Real.sin u := by
  have ht := transport_trig hu
  have hprod := mul_lt_mul P_bounds.2 ht.2.2.2.1 ht.2.2.1
    (by norm_num : (0:ℝ)<7075129/10000000)
  linarith [ht.1]

theorem U_monotone : MonotoneOn U (Icc 0 frameCap) :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (U_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => U_hasDerivAt u)
    (fun u hu => (U_increasing_derivative (Ioo_subset_Icc_self hu)).le)

theorem U_lower {u : ℝ} (hu : u∈Icc 0 frameCap) : (7/10:ℝ)<U u := by
  have hh := U_monotone (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hu hu.1
  simp only [U,Real.sin_zero,Real.cos_zero,mul_one,zero_add] at hh
  exact P_bounds.1.trans_le hh

theorem K_antitone : AntitoneOn K (Icc 0 frameCap) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (K_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => K_hasDerivAt u)
    (fun u hu => by linarith [U_lower (Ioo_subset_Icc_self hu)])

theorem C_pos {u : ℝ} (hu : u∈Icc 0 frameCap) : 0<C u := by
  have ht := transport_trig hu
  dsimp [C]
  exact add_pos_of_pos_of_nonneg (by linarith [ht.1]) (div_nonneg ht.2.2.1 S_pos.le)

theorem C_cap : 1<C frameCap := by
  have ht := CommonQuarter.cap_trig
  have hquot : (3221/5000:ℝ)/(17075129/10000000)<Real.sin frameCap/S := by
    apply (div_lt_div_iff₀ (by norm_num) S_pos).2
    have hp := mul_lt_mul S_bounds.2 ht.1 (by norm_num : (0:ℝ)≤3221/5000)
      (by norm_num : (0:ℝ)<17075129/10000000)
    simpa [frameCap,mul_comm] using hp
  dsimp [C,frameCap]
  norm_num at hquot
  linarith [ht.2.2.1]

theorem C_bounds {u : ℝ} (hu : u∈Icc 0 frameCap) : 1≤C u ∧ C u<7/6 := by
  have hc : ConcaveOn ℝ (Icc 0 frameCap) C :=
    concave_of_deriv2 (fun u _ => C_hasDerivAt u) (fun u _ => Cd_hasDerivAt u)
      (fun u hu => by linarith [C_pos hu])
  have hlo := hc.min_le_of_mem_Icc
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
    (by norm_num [frameCap] : frameCap∈Icc 0 frameCap) hu
  have hmin : 1≤min (C 0) (C frameCap) := le_min (by norm_num [C]) C_cap.le
  have hn : (1/S)^2+1<(7/6:ℝ)^2 := by
    have hp := pow_lt_pow_left₀ inv_S_bounds.1.le inv_S_bounds.2 (by decide : 0<2)
    norm_num at hp ⊢
    linarith
  have hproj := FrameCoreArc.projection_lt (a:=1/S) (b:=(1:ℝ)) (by norm_num : (0:ℝ)<7/6)
    (by simpa using hn) u
  refine ⟨hmin.trans hlo,?_⟩
  dsimp [C]
  convert hproj using 1 <;> ring

theorem domain_radicand {u : ℝ} (hu : Domain u) : (1/4:ℝ)≤Q0-K u^2 := by
  have ha : (a0+1/2)^2=Q0-1/4 := by
    simpa [a0] using Real.sq_sqrt (by norm_num [Q0] : 0≤Q0-1/4)
  have hk := pow_le_pow_left₀ (by linarith [(K_bounds hu.1).1] : 0≤K u) hu.2 2
  nlinarith

theorem Y_pos {u : ℝ} (hu : Domain u) : 0<Y u :=
  Real.sqrt_pos.mpr (by linarith [domain_radicand hu])

theorem Y_sq {u : ℝ} (hu : Domain u) : Y u^2=Q0-K u^2 :=
  Real.sq_sqrt (by linarith [domain_radicand hu])

theorem Y_bounds {u : ℝ} (hu : Domain u) : (1/2:ℝ)≤Y u ∧ Y u<3/2 := by
  have hy := Y_sq hu
  have hp := Y_pos hu
  have hk := (K_bounds hu.1).1
  have hr := domain_radicand hu
  dsimp [Q0] at hy hr
  constructor <;> nlinarith

theorem domain_interval {l u z : ℝ} (hl : Domain l) (hu : u∈Icc 0 frameCap)
    (hz : z∈Icc l u) : Domain z := by
  have hz' : z∈Icc 0 frameCap := ⟨hl.1.1.trans hz.1,hz.2.trans hu.2⟩
  exact ⟨hz',(K_antitone hl.1 hz' hz.1).trans hl.2⟩

theorem weight_pos {u : ℝ} (hu : Domain u) : 0<weight u := by
  dsimp [weight]
  exact div_pos (mul_pos (by norm_num [m]) (by linarith [(K_bounds hu.1).1])) (Y_pos hu)

theorem Y_hasDerivAt {u : ℝ} (hu : Domain u) : HasDerivAt Y (K u*U u/Y u) u := by
  have hh := ((hasDerivAt_const u Q0).sub ((K_hasDerivAt u).pow 2)).sqrt
    (show Q0-K u^2≠0 by linarith [domain_radicand hu])
  convert hh using 1 <;> dsimp [Y] <;> ring

theorem J_hasDerivAt {u : ℝ} (hu : Domain u) : HasDerivAt J (Jd u) u := by
  have hh := (hasDerivAt_id u).add (((Y_hasDerivAt hu).const_sub 2).const_mul m)
  convert hh.add ((((Real.hasDerivAt_sin u).add (Real.hasDerivAt_cos u)).sub_const 1).
    const_mul (9/100:ℝ)) using 1 <;> dsimp [J,Jd] <;> ring

theorem circle_identity (u : ℝ) : (K u-1)^2+U u^2=1+P^2 := by
  have ht := Real.sin_sq_add_cos_sq u
  calc
    _=(1+P^2)*(Real.sin u^2+Real.cos u^2) := by dsimp [K,U]; ring
    _=1+P^2 := by rw [ht]; ring

theorem N_identity {u : ℝ} (hu : Domain u) :
    N (K u-1)=Q0*U u^2-K u*(K u-1)*Y u^2 := by
  have hU : U u^2=1+P^2-(K u-1)^2 := by linarith [circle_identity u]
  rw [Y_sq hu,hU]
  dsimp [N]
  ring

theorem Jd_hasDerivAt {u : ℝ} (hu : Domain u) : HasDerivAt Jd (Jdd u) u := by
  have hy := (Y_pos hu).ne'
  have hysq := Y_sq hu
  have hh := ((((K_hasDerivAt u).mul (U_hasDerivAt u)).const_mul m).
    div (Y_hasDerivAt hu) hy).const_sub 1
  convert hh.add (((Real.hasDerivAt_cos u).sub (Real.hasDerivAt_sin u)).
    const_mul (9/100:ℝ)) using 1
  · rfl
  · dsimp [Jdd]
    rw [N_identity hu,show Real.cos u-P*Real.sin u=K u-1 by dsimp [K]; ring]
    rw [show Q0=Y u^2+K u^2 by linarith [hysq]]
    field_simp [hy]
    ring

end SquaresInCircles.Eight.TableFree.GlobalGA.Target.Outer
