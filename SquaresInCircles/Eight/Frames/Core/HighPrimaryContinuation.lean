module

public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Frames.Core.HighCorePrimary
public import SquaresInCircles.Eight.Frames.Core.HighPrimaryCurvature

/-!
# Eight squares: the actual core/high primary continuation through the quarter turn

The first-quadrant support decreases to the exact quarter value.  The
second-quadrant support is concave on its whole interval.  The norm and
its radial projection are controlled directly by their squared identities.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreHighPrimaryContinuation
open FramePair FrameCircleArc FrameHighArc FrameCoreArc FramePairCalculus
open FrameMidArc (g)
open FrameCoreHighPrimaryCurvature (gamma primaryFirst)

def X (x : ℝ) : ℝ := g/Real.sin x-u
def N (x : ℝ) : ℝ := Real.sqrt ((X x)^2+v^2)
def Z (x : ℝ) : ℝ := R*X x/N x
def Xd (x : ℝ) : ℝ := -g*Real.cos x/(Real.sin x)^2
def Nd (x : ℝ) : ℝ := X x*Xd x/N x
def Zd (x : ℝ) : ℝ := -R*v^2*g*Real.cos x/((Real.sin x)^2*(N x)^3)
def firstD (x : ℝ) : ℝ :=
  1+(9/100)*(Real.sin x-Real.cos x)+
    g/(Real.sin x)^2*(Real.cos x*(Z x-1)-13/12)
def primarySecond (x : ℝ) : ℝ :=
  x-(9/100)*(Real.sin x-Real.cos x-1)-k+(-u+v+g)/2+
    g/Real.sin x+(g/12)*Real.cos x/Real.sin x-R*N x
def secondD (x : ℝ) : ℝ :=
  1-(9/100)*(Real.sin x+Real.cos x)+
    g/(Real.sin x)^2*(Real.cos x*(Z x-1)-1/12)
def secondDD (x : ℝ) : ℝ :=
  (9/100)*(Real.sin x-Real.cos x)+
    g/(Real.sin x)^3*((1+(Real.cos x)^2)*(1-Z x)+Real.cos x/6)-
      R*v^2*g^2*(Real.cos x)^2/((Real.sin x)^4*(N x)^3)
def quarterValue : ℝ :=
  Real.pi/4+3*g/2-(u-v)*(c0+1/2)-R*FrameCoreHighNorm.n 1

theorem interval_sine {x : ℝ} (hx : x∈Icc (3/4:ℝ) (5/2)) :
    (299/500:ℝ)<Real.sin x := by
  apply sin_endpoint_lower (by norm_num : (0:ℝ)≤3/4)
    (by linarith [FrameLowPair.pi_lower] : (5/2:ℝ)≤Real.pi) hx
  · have hh := Real.sin_ge_sub_cube (show (0:ℝ)≤3/4 by norm_num)
    norm_num at hh
    linarith
  · exact FrameCoreHighCorePrimary.trig_endpoints.2.2.2.1

theorem X_lower {x : ℝ} (hx : x∈Icc (3/4:ℝ) (5/2)) : g-u≤X x := by
  have hs : 0<Real.sin x := by linarith [interval_sine hx]
  have hg : g≤g/Real.sin x := (le_div_iff₀ hs).2
    (mul_le_of_le_one_right (by norm_num [g] : 0≤g) (Real.sin_le_one x))
  dsimp [X]
  linarith

theorem N_pos (x : ℝ) : 0<N x := by
  apply Real.sqrt_pos.mpr
  have hv : (0:ℝ)<v^2 := by norm_num [v]
  nlinarith [sq_nonneg (X x)]

theorem N_sq (x : ℝ) : (N x)^2=(X x)^2+v^2 := Real.sq_sqrt (by positivity)

theorem Z_bounds {x : ℝ} (hx : x∈Icc (3/4:ℝ) (5/2)) :
    (39/25:ℝ)<Z x ∧ Z x<(1979/1000:ℝ) := by
  have hxL := X_lower hx
  have hx0 : 0<X x := by norm_num [g,u] at hxL; linarith
  have hn := N_pos x
  have hns := N_sq x
  have hr := R_sq
  have hNgt : X x<N x := by norm_num [v] at hns; nlinarith
  have hu : Z x<R := by
    dsimp [Z]
    apply (div_lt_iff₀ hn).2
    exact mul_lt_mul_of_pos_left hNgt R_pos
  have hXsq := pow_le_pow_left₀
    (show (0:ℝ)≤g-u by norm_num [g,u]) hxL 2
  have hl : (39/25:ℝ)*N x<R*X x := by
    have hp := mul_pos R_pos hx0
    have hprod : ((39/25:ℝ)*N x)^2<(R*X x)^2 := by
      rw [mul_pow,mul_pow,hr,hns]
      norm_num [Q0,g,u,v] at *
      nlinarith
    nlinarith
  exact ⟨(lt_div_iff₀ hn).2 hl,hu.trans (by
    have hh := radius_bound
    norm_num [radiusUpper] at hh
    linarith)⟩

theorem X_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt X (Xd x) x := by
  have h := ((hasDerivAt_const x g).div (Real.hasDerivAt_sin x) hs).sub_const u
  convert h using 1
  · rfl
  · simp only [Xd]; ring

theorem N_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt N (Nd x) x := by
  have hp : 0<(X x)^2+v^2 := by
    have hv : (0:ℝ)<v^2 := by norm_num [v]
    nlinarith [sq_nonneg (X x)]
  have h := (((X_deriv hs).pow 2).add_const (v^2)).sqrt hp.ne'
  convert h using 1
  · rfl
  · simp only [Nd,N]; norm_num; ring

theorem Z_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt Z (Zd x) x := by
  have hn := (N_pos x).ne'
  have hd := ((X_deriv hs).const_mul R).div (N_deriv hs) hn
  convert hd using 1
  · rfl
  · simp only [Zd,Nd,Xd]
    field_simp
    linear_combination (R*g*Real.cos x)*N_sq x

theorem first_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt primaryFirst (firstD x) x := by
  have hbase := ((((hasDerivAt_id' x).fun_sub ((((Real.hasDerivAt_sin x).fun_add
    (Real.hasDerivAt_cos x)).sub_const 1).const_mul (9/100))).sub_const k).add_const
      ((-u+v+g)/2)).fun_add ((hasDerivAt_const x g).div (Real.hasDerivAt_sin x) hs)
  have hd := (hbase.fun_add (((Real.hasDerivAt_cos x).const_mul (13*g/12)).div
    (Real.hasDerivAt_sin x) hs)).fun_sub ((N_deriv hs).const_mul R)
  convert hd using 1
  · rfl
  · have hn := (N_pos x).ne'
    simp only [firstD,Nd,Xd,Z]
    field_simp
    linear_combination (1300*N x*g)*Real.sin_sq_add_cos_sq x

theorem second_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt primarySecond (secondD x) x := by
  have hbase := ((((hasDerivAt_id' x).fun_sub ((((Real.hasDerivAt_sin x).fun_sub
    (Real.hasDerivAt_cos x)).sub_const 1).const_mul (9/100))).sub_const k).add_const
      ((-u+v+g)/2)).fun_add ((hasDerivAt_const x g).div (Real.hasDerivAt_sin x) hs)
  have hd := (hbase.fun_add (((Real.hasDerivAt_cos x).const_mul (g/12)).div
    (Real.hasDerivAt_sin x) hs)).fun_sub ((N_deriv hs).const_mul R)
  convert hd using 1
  · rfl
  · have hn := (N_pos x).ne'
    simp only [secondD,Nd,Xd,Z]
    field_simp
    linear_combination (100*N x*g)*Real.sin_sq_add_cos_sq x

theorem secondD_deriv {x : ℝ} (hs : Real.sin x≠0) : HasDerivAt secondD (secondDD x) x := by
  have hbase := (((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul
    (9/100)).const_sub 1
  have hquot := (hasDerivAt_const x g).fun_div ((Real.hasDerivAt_sin x).fun_pow 2)
    (pow_ne_zero 2 hs)
  have hterm := (((Real.hasDerivAt_cos x).fun_mul ((Z_deriv hs).sub_const 1)).sub_const (1/12))
  convert hbase.fun_add (hquot.fun_mul hterm) using 1
  · rfl
  · have hn := (N_pos x).ne'
    simp only [secondDD,Zd,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one]
    field_simp
    linear_combination (7200*N x^3*g*Real.sin x*(Z x-1))*Real.sin_sq_add_cos_sq x

theorem quarter_lower : (11042/12500:ℝ)<quarterValue := by
  have hN := FrameCoreHighNorm.n_one_bounds.2
  have hN0 : 0≤FrameCoreHighNorm.n 1 := Real.sqrt_nonneg _
  have hRN : R*FrameCoreHighNorm.n 1<radiusUpper*(320451/500000) :=
    mul_lt_mul'' radius_bound hN R_pos.le hN0
  have hd := FrameHighArc.diagonal_bounds.2
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [quarterValue,u,v,g,radiusUpper] at hRN ⊢
  linarith

theorem first_quarter : primaryFirst (Real.pi/2)=quarterValue := by
  simp [primaryFirst,quarterValue,FrameCoreHighNorm.n,FrameCoreHighNorm.energy,k]
  ring

theorem second_quarter : primarySecond (Real.pi/2)=quarterValue := by
  simp [primarySecond,quarterValue,N,X,FrameCoreHighNorm.n,FrameCoreHighNorm.energy,k]
  ring

theorem firstD_negative {x : ℝ} (hx : x∈Icc (3/2:ℝ) (Real.pi/2)) : firstD x<0 := by
  have hdom : x∈Icc (3/4:ℝ) (5/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.2]⟩
  have hs := interval_sine hdom
  have ht := FrameLowPair.quadrant ⟨by linarith [hx.1],hx.2⟩
  have hz := Z_bounds hdom
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤3/2)
    (by linarith [hx.2,Real.pi_pos]) hx.1
  have hc0 := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤3/2 by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hc0
  have hcU : Real.cos x<(71/1000:ℝ) := by linarith
  have hZc := mul_le_mul_of_nonneg_right (show Z x-1≤979/1000 by linarith [hz.2]) ht.2.2.1
  have hn : Real.cos x*(Z x-1)-13/12≤(71/1000:ℝ)*(979/1000)-13/12 := by linarith
  have hn0 : Real.cos x*(Z x-1)-13/12≤0 := by linarith
  have hs2 := pow_le_pow_left₀ ht.1 ht.2.1 2
  have hnum0 := mul_nonpos_of_nonneg_of_nonpos (show 0≤g by norm_num [g]) hn0
  have hmul := mul_le_mul_of_nonpos_left hs2 hnum0
  have hdiv : g/(Real.sin x)^2*(Real.cos x*(Z x-1)-13/12)≤
      g*(Real.cos x*(Z x-1)-13/12) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (pow_pos (by linarith [hs] : 0<Real.sin x) 2)).2 (by linarith)
  have hg : g*(Real.cos x*(Z x-1)-13/12)≤g*((71/1000:ℝ)*(979/1000)-13/12) :=
    mul_le_mul_of_nonneg_left hn (by norm_num [g])
  have hgv : g=269343/250000 := rfl
  dsimp only [firstD]
  linarith [ht.2.1]

theorem first_tail_lower {x : ℝ} (hx : x∈Icc (3/2:ℝ) (Real.pi/2)) : gamma<primaryFirst x := by
  have hsin {z : ℝ} (hz : z∈Icc (3/2:ℝ) (Real.pi/2)) : Real.sin z≠0 := by
    have hdom : z∈Icc (3/4:ℝ) (5/2) :=
      ⟨by linarith [hz.1],by linarith [hz.2,Arithmetic.pi_hand_enclosure.2]⟩
    exact (lt_trans (by norm_num) (interval_sine hdom)).ne'
  have hm : AntitoneOn primaryFirst (Icc (3/2:ℝ) (Real.pi/2)) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun z hz => (first_deriv (hsin hz)).continuousAt.continuousWithinAt
    · exact fun z hz => first_deriv (hsin (Ioo_subset_Icc_self hz))
    · exact fun z hz => (firstD_negative (Ioo_subset_Icc_self hz)).le
  have hh := hm hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2
  rw [first_quarter] at hh
  dsimp [gamma]
  linarith [quarter_lower]

theorem secondDD_negative {x : ℝ} (hx : x∈Icc (Real.pi/2) (5/2:ℝ)) : secondDD x<0 := by
  have hdom : x∈Icc (3/4:ℝ) (5/2) := ⟨by linarith [hx.1,FrameLowPair.pi_lower],hx.2⟩
  have hs := interval_sine hdom
  have ht := second_signs ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hz := Z_bounds hdom
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (Real.cos x))
    (show 1-Z x≤0 by linarith [hz.1])
  have hn : (1+(Real.cos x)^2)*(1-Z x)+Real.cos x/6≤-(14/25:ℝ) := by
    linarith [ht.2,hz.1]
  have hs3 := pow_le_pow_left₀ ht.1 (Real.sin_le_one x) 3
  have hmul := mul_le_mul_of_nonpos_left hs3 (show g*(-14/25)≤0 by norm_num [g])
  have hdiv : g/(Real.sin x)^3*((1+(Real.cos x)^2)*(1-Z x)+Real.cos x/6)≤g*(-14/25) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos (by linarith [hs] : 0<Real.sin x) 3)).2
    have hh := mul_le_mul_of_nonneg_left hn (show 0≤g by norm_num [g])
    linarith
  have hlast : 0≤R*v^2*g^2*(Real.cos x)^2/((Real.sin x)^4*(N x)^3) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg R_pos.le (sq_nonneg v)) (sq_nonneg g))
        (sq_nonneg _)
    · exact mul_nonneg (pow_nonneg ht.1 4) (pow_nonneg (N_pos x).le 3)
  have hch := CorePairGeometry.charge_upper x
  rw [(second_width ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩).2] at hch
  have hgv : g=269343/250000 := rfl
  dsimp only [secondDD]
  linarith

theorem second_end : (27/25:ℝ)<primarySecond (5/2) := by
  have hsL := FrameCoreHighCorePrimary.trig_endpoints.2.2.2.1
  have hcL := FrameCoreHighCorePrimary.trig_endpoints.2.2.2.2
  have hsU0 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤5/2 by norm_num)
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7] at hsU0
  have hsU : Real.sin (5/2:ℝ)<599/1000 := by linarith
  have hs : 0<Real.sin (5/2:ℝ) := by linarith
  have hgL : g/(599/1000)≤g/Real.sin (5/2:ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num [g]) hs (by linarith)
  have hneg := negative_div_lower hcL.le (by norm_num : -(401/500:ℝ)≤0)
    (by norm_num : (0:ℝ)<299/500) hsL.le
  have hcos : (g/12)*(-(401/500)/(299/500))≤(g/12)*Real.cos (5/2)/Real.sin (5/2) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hneg (by norm_num [g])
  have hXu : X (5/2)<g/(299/500)-u := by
    dsimp [X]
    exact sub_lt_sub_right (div_lt_div_of_pos_left (by norm_num [g]) (by norm_num) hsL) u
  have hXl := X_lower (show (5/2:ℝ)∈Icc (3/4:ℝ) (5/2) by constructor <;> norm_num)
  have hX0 : 0≤X (5/2) := le_trans (by norm_num [g,u]) hXl
  have hn : N (5/2)<(647/500:ℝ) := by
    have hsq := N_sq (5/2)
    have hX2 := pow_lt_pow_left₀ hXu hX0 (by norm_num : (2:ℕ)≠0)
    refine lt_of_pow_lt_pow_left₀ 2 (by norm_num) ?_
    rw [hsq]
    norm_num [g,u,v] at hX2 ⊢
    linarith
  have hRN : R*N (5/2)<radiusUpper*(647/500) :=
    mul_lt_mul'' radius_bound hn R_pos.le (N_pos _).le
  have hch := CorePairGeometry.charge_upper (5/2)
  rw [(second_width (show (5/2:ℝ)∈Icc (Real.pi/2) Real.pi by
    constructor <;> linarith [Arithmetic.pi_hand_enclosure.2,FrameLowPair.pi_lower])).2] at hch
  have hk := k_bounds.2.2
  dsimp only [primarySecond]
  dsimp only [kUpper,radiusUpper,u,v,g] at hk hRN hgL hcos ⊢
  linarith

theorem second_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (5/2:ℝ)) : gamma<primarySecond x := by
  have hsin {z : ℝ} (hz : z∈Icc (Real.pi/2) (5/2:ℝ)) : Real.sin z≠0 := by
    linarith [interval_sine (show z∈Icc (3/4:ℝ) (5/2) from
      ⟨by linarith [hz.1,FrameLowPair.pi_lower],hz.2⟩)]
  have hc : ConcaveOn ℝ (Icc (Real.pi/2) (5/2:ℝ)) primarySecond := concave_of_deriv2
    (fun z hz => second_deriv (hsin hz)) (fun z hz => secondD_deriv (hsin hz))
    (fun z hz => (secondDD_negative hz).le)
  apply concave_gt_of_endpoints hc hx
  · rw [second_quarter]
    dsimp [gamma]
    linarith [quarter_lower]
  · dsimp [gamma]
    linarith [second_end]

end SquaresInCircles.Eight.FrameCoreHighPrimaryContinuation
