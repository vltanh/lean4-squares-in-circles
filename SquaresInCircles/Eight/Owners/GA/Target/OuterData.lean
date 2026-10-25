module

public import SquaresInCircles.Eight.Owners.GA.Target.Markers

/-!
# Eight squares: the one-variable outer target support

The radical is used only on its actual feasible interval. In particular,
no differentiability assertion is made at the infeasible angle zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target.Outer
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
theorem P_bounds : (7/10:ℝ)<P ∧ P<7075129/10000000 := by
  dsimp [P]
  constructor <;> linarith [S_bounds.1,S_bounds.2]

theorem inv_S_bounds : (0:ℝ)<1/S ∧ 1/S<10/17 := by
  exact ⟨div_pos (by norm_num) S_pos,
    (div_lt_iff₀ S_pos).2 (by linarith [S_bounds.1])⟩

theorem K_hasDerivAt (u : ℝ) : HasDerivAt K (-U u) u := by
  have h1 : HasDerivAt (fun x => 1+Real.cos x) (-Real.sin u) u :=
    (Real.hasDerivAt_cos u).const_add 1
  have h2 : HasDerivAt (fun x => P*Real.sin x) (P*Real.cos u) u :=
    (Real.hasDerivAt_sin u).const_mul P
  have h : HasDerivAt (fun x => 1+Real.cos x-P*Real.sin x) (-Real.sin u-P*Real.cos u) u :=
    h1.fun_sub h2
  exact h.congr_deriv (by dsimp [U]; ring)

theorem U_hasDerivAt (u : ℝ) :
    HasDerivAt U (Real.cos u-P*Real.sin u) u := by
  have h2 : HasDerivAt (fun x => P*Real.cos x) (P*(-Real.sin u)) u :=
    (Real.hasDerivAt_cos u).const_mul P
  have h : HasDerivAt (fun x => Real.sin x+P*Real.cos x) (Real.cos u+P*(-Real.sin u)) u :=
    (Real.hasDerivAt_sin u).fun_add h2
  exact h.congr_deriv (by ring)

theorem C_hasDerivAt (u : ℝ) : HasDerivAt C (Cd u) u :=
  (Real.hasDerivAt_cos u).add ((Real.hasDerivAt_sin u).div_const S)

theorem Cd_hasDerivAt (u : ℝ) : HasDerivAt Cd (-C u) u := by
  have h1 : HasDerivAt (fun x => -Real.sin x) (-Real.cos u) u := (Real.hasDerivAt_sin u).neg
  have h2 : HasDerivAt (fun x => Real.cos x/S) (-Real.sin u/S) u :=
    (Real.hasDerivAt_cos u).div_const S
  have h : HasDerivAt (fun x => -Real.sin x+Real.cos x/S) (-Real.cos u+-Real.sin u/S) u :=
    h1.fun_add h2
  exact h.congr_deriv (by dsimp [C]; ring)

theorem K_bounds {u : ℝ} (hu : u∈Icc 0 frameCap) : (13/10:ℝ)<K u ∧ K u≤2 := by
  have ht := transport_trig hu
  have hprod := mul_le_mul P_bounds.2.le ht.2.2.2.1.le ht.2.2.1
    (by norm_num : (0:ℝ)≤7075129/10000000)
  have hnonneg := mul_nonneg (by linarith [P_bounds.1] : 0≤P) ht.2.2.1
  dsimp [K]
  exact ⟨by linarith [ht.1],by linarith [ht.2.1]⟩

theorem U_increasing_derivative {u : ℝ} (hu : u∈Icc 0 frameCap) :
    0<Real.cos u-P*Real.sin u := by
  have ht := transport_trig hu
  have hprod := mul_le_mul P_bounds.2.le ht.2.2.2.1.le ht.2.2.1
    (by norm_num : (0:ℝ)≤7075129/10000000)
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
    have hp := mul_lt_mul'' ht.1 S_bounds.2 (by norm_num) S_pos.le
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
  have hmin : 1 ≤ min (C 0) (C frameCap) := le_min (by norm_num [C]) C_cap.le
  have hn : (1/S)^2+1<(7/6:ℝ)^2 := by
    have hp := pow_lt_pow_left₀ inv_S_bounds.2 inv_S_bounds.1.le (by norm_num : (2:ℕ)≠0)
    norm_num at hp ⊢
    linarith
  have hproj := FrameCoreArc.projection_lt (a:=1/S) (b:=(1:ℝ)) (by norm_num : (0:ℝ)<7/6)
    (by simpa using hn) u
  refine ⟨hmin.trans hlo,?_⟩
  dsimp [C]
  convert hproj using 1; ring

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
  have hK := K_hasDerivAt u
  have h1 : HasDerivAt (fun x => K x^2) ((2:ℕ)*K u^(2-1)*(-U u)) u := hK.fun_pow 2
  have h2 : HasDerivAt (fun x => Q0-K x^2) (-((2:ℕ)*K u^(2-1)*(-U u))) u := h1.const_sub Q0
  have h3 : HasDerivAt (fun x => Real.sqrt (Q0-K x^2))
      (-((2:ℕ)*K u^(2-1)*(-U u))/(2*Real.sqrt (Q0-K u^2))) u :=
    h2.sqrt (show Q0-K u^2≠0 by linarith [domain_radicand hu])
  exact h3.congr_deriv (by dsimp only [Y]; push_cast; ring)

theorem J_hasDerivAt {u : ℝ} (hu : Domain u) : HasDerivAt J (Jd u) u := by
  have hY := Y_hasDerivAt hu
  have h1 : HasDerivAt (fun x => m*(2-Y x)) (m*(-(K u*U u/Y u))) u := (hY.const_sub 2).const_mul m
  have h2 : HasDerivAt (fun x => x+m*(2-Y x)) (1+m*(-(K u*U u/Y u))) u :=
    (hasDerivAt_id' u).fun_add h1
  have h3 : HasDerivAt (fun x => Real.sin x+Real.cos x) (Real.cos u+-Real.sin u) u :=
    (Real.hasDerivAt_sin u).fun_add (Real.hasDerivAt_cos u)
  have h4 : HasDerivAt (fun x => (9/100:ℝ)*(Real.sin x+Real.cos x-1))
      ((9/100)*(Real.cos u+-Real.sin u)) u := (h3.sub_const 1).const_mul (9/100:ℝ)
  have h : HasDerivAt (fun x => x+m*(2-Y x)+(9/100)*(Real.sin x+Real.cos x-1))
      (1+m*(-(K u*U u/Y u))+(9/100)*(Real.cos u+-Real.sin u)) u := h2.fun_add h4
  exact h.congr_deriv (by dsimp [Jd]; ring)

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
  have hK := K_hasDerivAt u
  have hU := U_hasDerivAt u
  have hY := Y_hasDerivAt hu
  have h1 : HasDerivAt (fun x => m*K x) (m*(-U u)) u := hK.const_mul m
  have h2 : HasDerivAt (fun x => m*K x*U x)
      (m*(-U u)*U u+m*K u*(Real.cos u-P*Real.sin u)) u := h1.fun_mul hU
  have h3 : HasDerivAt (fun x => m*K x*U x/Y x)
      (((m*(-U u)*U u+m*K u*(Real.cos u-P*Real.sin u))*Y u-m*K u*U u*(K u*U u/Y u))/
        Y u^2) u := h2.fun_div hY hy
  have h4 : HasDerivAt (fun x => (9/100:ℝ)*(Real.cos x-Real.sin x))
      ((9/100)*(-Real.sin u-Real.cos u)) u :=
    ((Real.hasDerivAt_cos u).fun_sub (Real.hasDerivAt_sin u)).const_mul (9/100:ℝ)
  have h : HasDerivAt (fun x => 1-m*K x*U x/Y x+(9/100)*(Real.cos x-Real.sin x))
      (-(((m*(-U u)*U u+m*K u*(Real.cos u-P*Real.sin u))*Y u-m*K u*U u*(K u*U u/Y u))/
        Y u^2)+(9/100)*(-Real.sin u-Real.cos u)) u := (h3.const_sub 1).fun_add h4
  refine h.congr_deriv ?_
  dsimp only [Jdd]
  rw [N_identity hu,show Real.cos u-P*Real.sin u=K u-1 by dsimp [K]; ring]
  rw [show Q0=Y u^2+K u^2 by linarith [hysq]]
  field_simp
  ring

end SquaresInCircles.Eight.GlobalGA.Target.Outer
