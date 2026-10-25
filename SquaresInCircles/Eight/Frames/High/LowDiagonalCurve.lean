module

public import SquaresInCircles.Eight.Frames.Low.HighArc

/-!
# Eight squares: the explicit high-diagonal / low-target contact curve

Intersection of the shifted circle with the original secondary line
gives the displayed square-root formula.  Both derivatives are exact.
The curve is analytic on the entire closed interval `[0,.11]`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowDiagonalCurve
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus

def domain : Set ℝ := Icc (0:ℝ) (11/100)
def w (x : ℝ) : ℝ := 1/2-c0+Real.sin x+Real.cos x
def wd (x : ℝ) : ℝ := Real.cos x-Real.sin x
def wdd (x : ℝ) : ℝ := -Real.sin x-Real.cos x
def rho (x : ℝ) : ℝ := Real.sqrt (Q0-(w x)^2)
def rhod (x : ℝ) : ℝ := -w x*wd x/rho x
def rhodd (x : ℝ) : ℝ :=
  -((wd x)^2+w x*wdd x)/rho x-(w x)^2*(wd x)^2/(rho x)^3
def z (x : ℝ) : ℝ := w x*Real.cos x-rho x*Real.sin x-1/2
def u (x : ℝ) : ℝ := w x*Real.sin x+rho x*Real.cos x-1/2
def zd (x : ℝ) : ℝ :=
  (wd x-rho x)*Real.cos x-(w x+rhod x)*Real.sin x
def zdd (x : ℝ) : ℝ :=
  (wdd x-2*rhod x-w x)*Real.cos x+(rho x-2*wd x-rhodd x)*Real.sin x

theorem quadrant {x : ℝ} (hx : x∈domain) : x∈Icc 0 (Real.pi/2) :=
  ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    0≤Real.sin x ∧ Real.sin x≤11/100 ∧
      (19879/20000:ℝ)≤Real.cos x ∧ Real.cos x≤1 ∧
        1≤Real.sin x+Real.cos x := by
  have hq := FrameLowPair.quadrant (quadrant hx)
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width (quadrant hx)).1] at hw
  exact ⟨hq.1,by linarith [hx.2],by linarith,hq.2.2.2,by linarith⟩

theorem w_bounds {x : ℝ} (hx : x∈domain) :
    (3/5:ℝ)<w x ∧ w x<89/125 ∧
      (8839/10000:ℝ)<wd x ∧ wd x≤1 ∧ wdd x≤-1 := by
  have ht := trig_bounds hx
  dsimp only [w,wd,wdd]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith [c0_bounds.1,c0_bounds.2]

theorem radicand_positive {x : ℝ} (hx : x∈domain) : 0<Q0-(w x)^2 := by
  have hw := w_bounds hx
  have hsq := pow_le_pow_left₀ (by linarith [hw.1] : (0:ℝ)≤w x) hw.2.1.le 2
  norm_num [Q0]
  linarith

theorem rho_positive {x : ℝ} (hx : x∈domain) : 0<rho x :=
  Real.sqrt_pos.mpr (radicand_positive hx)
theorem rho_square {x : ℝ} (hx : x∈domain) : (rho x)^2=Q0-(w x)^2 :=
  Real.sq_sqrt (radicand_positive hx).le

theorem rho_bounds {x : ℝ} (hx : x∈domain) : (46/25:ℝ)<rho x ∧ rho x<1979/1000 := by
  have hw := w_bounds hx
  have hs := rho_square hx
  have hp := rho_positive hx
  have hsq := pow_le_pow_left₀ (by linarith [hw.1] : (0:ℝ)≤w x) hw.2.1.le 2
  constructor
  · by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hs
    linarith
  · have hR := R_sq
    have hlt : rho x<R := by
      apply lt_of_pow_lt_pow_left₀ 2 R_pos.le
      rw [hs,hR]
      nlinarith [hw.1]
    linarith [radius_precise.2]

theorem w_deriv (x : ℝ) : HasDerivAt w (wd x) x := by
  have h := ((Real.hasDerivAt_sin x).const_add (1/2-c0)).fun_add (Real.hasDerivAt_cos x)
  exact h.congr_deriv (by simp only [wd]; ring)
theorem wd_deriv (x : ℝ) : HasDerivAt wd (wdd x) x :=
  (Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)

theorem rho_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt rho (rhod x) x := by
  have h := (((w_deriv x).fun_pow 2).const_sub Q0).sqrt (radicand_positive hx).ne'
  have hp : 0<Real.sqrt (Q0-(w x)^2) := rho_positive hx
  exact h.congr_deriv (by simp only [rhod,rho]; field_simp; ring)

theorem rhod_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt rhod (rhodd x) x := by
  have hh := (((w_deriv x).fun_neg).fun_mul (wd_deriv x)).fun_div (rho_deriv hx)
    (rho_positive hx).ne'
  have hp := (rho_positive hx).ne'
  exact hh.congr_deriv (by simp only [rhod,rhodd]; field_simp; ring)

theorem z_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt z (zd x) x := by
  have h := (((w_deriv x).fun_mul (Real.hasDerivAt_cos x)).fun_sub
    ((rho_deriv hx).fun_mul (Real.hasDerivAt_sin x))).sub_const (1/2)
  exact h.congr_deriv (by simp only [zd]; ring)

theorem zd_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt zd (zdd x) x := by
  have h := (((wd_deriv x).fun_sub (rho_deriv hx)).fun_mul (Real.hasDerivAt_cos x)).fun_sub
    (((w_deriv x).fun_add (rhod_deriv hx)).fun_mul (Real.hasDerivAt_sin x))
  exact h.congr_deriv (by simp only [zdd]; ring)

theorem z_derivative_negative {x : ℝ} (hx : x∈domain) : zd x<0 := by
  have hw := w_bounds hx
  have hr := rho_bounds hx
  have ht := trig_bounds hx
  have hratio : wd x/rho x≤1 := by
    apply (div_le_iff₀ (rho_positive hx)).2
    linarith [hw.2.2.2.1]
  have hwpositive : 0≤w x := by linarith [hw.1]
  have hcoef : 0≤w x+rhod x := by
    have hh := mul_le_mul_of_nonneg_left hratio hwpositive
    have he : rhod x=-(w x*(wd x/rho x)) := by simp only [rhod]; ring
    rw [he]
    linarith
  have hfirst := mul_neg_of_neg_of_pos
    (show wd x-rho x<0 by linarith [hw.2.2.2.1])
    (show 0<Real.cos x by linarith [ht.2.2.1])
  have hsecond := mul_nonneg hcoef ht.1
  dsimp only [zd]
  linarith

theorem z_antitone : AntitoneOn z domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (z_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => z_deriv (Ioo_subset_Icc_self hx)
  · exact fun x hx => (z_derivative_negative (Ioo_subset_Icc_self hx)).le

@[simp] theorem z_zero : z 0=1-c0 := by simp [z,w]; ring

theorem final_trig : (10977830/100000000:ℝ)<Real.sin (11/100) ∧
    Real.sin (11/100)<10977831/100000000 ∧
      (99395609/100000000:ℝ)<Real.cos (11/100) ∧
        Real.cos (11/100)<99395610/100000000 := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤11/100 by norm_num)
  have hsu := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤11/100 by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤11/100 by norm_num)
  have hcu := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤11/100 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C12,HighOrderTaylor.C14,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hsu hc hcu
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem final_radicals : (70452032/100000000:ℝ)<w (11/100) ∧
    w (11/100)<70452035/100000000 ∧
      (23114/12500:ℝ)<rho (11/100) ∧ rho (11/100)<184913/100000 := by
  have ht := final_trig
  have hw : (70452032/100000000:ℝ)<w (11/100) ∧ w (11/100)<70452035/100000000 := by
    dsimp [w]
    constructor <;> linarith [diagonal_precise.1,diagonal_precise.2]
  have hr := rho_square (show (11/100:ℝ)∈domain by constructor <;> norm_num)
  have hp := rho_positive (show (11/100:ℝ)∈domain by constructor <;> norm_num)
  have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤70452032/100000000) hw.1.le 2
  have hu := pow_le_pow_left₀ (by linarith [hw.1] : 0≤w (11/100)) hw.2.le 2
  norm_num [Q0] at hr
  refine ⟨hw.1,hw.2,?_,?_⟩
  · by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    nlinarith
  · by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤184913/100000) hbad 2
    nlinarith

theorem final_bounds : -(2733/1000000:ℝ)<z (11/100) ∧ z (11/100)< -(273/100000:ℝ) := by
  have ht := final_trig
  have hr := final_radicals
  have hscL := mul_le_mul hr.1.le ht.2.2.1.le
    (by norm_num : (0:ℝ)≤99395609/100000000) (by linarith [hr.1] : 0≤w (11/100))
  have hscU := mul_le_mul hr.2.1.le ht.2.2.2.le
    (by linarith [ht.2.2.1] : 0≤Real.cos (11/100)) (by norm_num : (0:ℝ)≤70452035/100000000)
  have hrsL := mul_le_mul hr.2.2.1.le ht.1.le
    (by norm_num : (0:ℝ)≤10977830/100000000) (by linarith [hr.2.2.1] : 0≤rho (11/100))
  have hrsU := mul_le_mul hr.2.2.2.le ht.2.1.le
    (by linarith [ht.1] : 0≤Real.sin (11/100)) (by norm_num : (0:ℝ)≤184913/100000)
  dsimp [z]
  constructor <;> linarith

theorem z_bounds {x : ℝ} (hx : x∈domain) :
    -(3/1000:ℝ)<z x ∧ z x<101/1000 := by
  have hl := z_antitone hx (show (11/100:ℝ)∈domain by constructor <;> norm_num) hx.2
  have hu := z_antitone (show (0:ℝ)∈domain by constructor <;> norm_num) hx hx.1
  rw [z_zero] at hu
  exact ⟨by linarith [final_bounds.1],by linarith [c0_bounds.1]⟩

theorem circle_identity {x : ℝ} (hx : x∈domain) : (u x+1/2)^2+(z x+1/2)^2=Q0 := by
  have hr := rho_square hx
  dsimp [u,z]
  linear_combination ((w x)^2+(rho x)^2)*(Real.sin_sq_add_cos_sq x)+hr

theorem u_shift_positive {x : ℝ} (hx : x∈domain) : 0<u x+1/2 := by
  have hw := (w_bounds hx).1
  have hr := rho_positive hx
  have ht := trig_bounds hx
  have hs := mul_nonneg (by linarith : (0:ℝ)≤w x) ht.1
  have hc := mul_pos hr (show 0<Real.cos x by linarith [ht.2.2.1])
  dsimp only [u]
  linarith

theorem u_eq_A {x : ℝ} (hx : x∈domain) : u x=A (z x) := by
  have hc := circle_identity hx
  have hp := u_shift_positive hx
  have he : Q0-(z x+1/2)^2=(u x+1/2)^2 := by linarith
  dsimp [A]
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hp.le]
  ring

theorem contact {x : ℝ} (hx : x∈domain) :
    A (z x)*Real.sin x+z x*Real.cos x=pairWidth x-c0 := by
  rw [← u_eq_A hx,(first_width (quadrant hx)).1]
  dsimp [u,z,w]
  linear_combination (1/2-c0+Real.sin x+Real.cos x)*(Real.sin_sq_add_cos_sq x)

end SquaresInCircles.Eight.FrameHighLowDiagonalCurve
