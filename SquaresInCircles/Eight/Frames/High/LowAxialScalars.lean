module

public import SquaresInCircles.Eight.Frames.Low.HighParallelCalculus
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds

/-!
# Eight squares: both complete low-axial boundary inequalities

The ordinary high marker uses its quantitative second derivative and
one interior tangent.  The upper marker decreases throughout its
interval because its derivative increases to a negative endpoint.
Both conclusions are strict on the entire closed interval.
-/

section
/-!
## The explicit high-diagonal / low-target contact curve

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
end
end
end

section
/-!
## Exact geometry of the low-axial contact boundary

The same explicit contact height supports both the ordinary high
marker and its quarter-rotated continuation.  Every derivative and
domain estimate below follows from the circle chart and the actual
closed angular interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowAxialGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus

def domain : Set ℝ := Icc (0:ℝ) (23/50)
def normalDomain : Set ℝ := Icc (11/100:ℝ) (23/50)
def upperDomain : Set ℝ := Icc (0:ℝ) (11/100)
def Z (x : ℝ) : ℝ := 1/2+(1/2)*Real.cos x+(1/2-a0)*Real.sin x
def P (x : ℝ) : ℝ := (a0-1/2)*Real.cos x+(1/2)*Real.sin x
def Pd (x : ℝ) : ℝ := -(a0-1/2)*Real.sin x+(1/2)*Real.cos x

theorem quadrant {x : ℝ} (hx : x∈domain) : x∈Icc 0 (Real.pi/2) :=
  ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩

theorem Z_deriv (x : ℝ) : HasDerivAt Z (-P x) x := by
  have h := (((Real.hasDerivAt_cos x).const_mul (1/2)).const_add (1/2)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (1/2-a0))
  have he : -P x=1/2*-Real.sin x+(1/2-a0)*Real.cos x := by simp only [P]; ring
  rw [he]
  exact h

theorem P_deriv (x : ℝ) : HasDerivAt P (Pd x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (a0-1/2)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (1/2))
  have he : Pd x=(a0-1/2)*-Real.sin x+1/2*Real.cos x := by simp only [Pd]; ring
  rw [he]
  exact h

theorem Pd_eq (x : ℝ) : Pd x=Z x-1/2 := by dsimp [Pd,Z]; ring
@[simp] theorem Z_zero : Z 0=1 := by norm_num [Z]
@[simp] theorem P_zero : P 0=a0-1/2 := by simp [P]

theorem P_positive {x : ℝ} (hx : x∈domain) : 0<P x := by
  have ht := FrameLowPair.quadrant (quadrant hx)
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hcos : 0<Real.cos x := by nlinarith
  have hp := mul_pos (show 0<a0-1/2 by linarith [a0_precise.1]) hcos
  dsimp [P]
  linarith

theorem Z_antitone : AntitoneOn Z domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (Z_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => Z_deriv x
  · exact fun x hx => neg_nonpos.mpr (P_positive (Ioo_subset_Icc_self hx)).le

theorem final_trig : (44394/100000:ℝ)<Real.sin (23/50) ∧
    Real.sin (23/50)<8879/20000 ∧ (17921/20000:ℝ)<Real.cos (23/50) ∧
      Real.cos (23/50)<44803/50000 := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤23/50 by norm_num)
  have hsu := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤23/50 by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤23/50 by norm_num)
  have hcu := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤23/50 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C12,HighOrderTaylor.C14,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hsu hc hcu
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem endpoint_heights : (1793/2000:ℝ)<Z (11/100) ∧ Z (11/100)<897/1000 ∧
    (541/1000:ℝ)<Z (23/50) ∧ Z (23/50)<543/1000 := by
  have ht0 := FrameHighLowDiagonalCurve.final_trig
  have ht1 := final_trig
  have hs0L := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht0.1.le
    (by norm_num : (0:ℝ)≤10977830/100000000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  have hs0U := mul_le_mul
    (show a0-1/2≤914575672/1000000000 by linarith [a0_precise.2]) ht0.2.1.le
    (by linarith [ht0.1] : 0≤Real.sin (11/100)) (by norm_num : (0:ℝ)≤914575672/1000000000)
  have hs1L := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht1.1.le
    (by norm_num : (0:ℝ)≤44394/100000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  have hs1U := mul_le_mul
    (show a0-1/2≤914575672/1000000000 by linarith [a0_precise.2]) ht1.2.1.le
    (by linarith [ht1.1] : 0≤Real.sin (23/50)) (by norm_num : (0:ℝ)≤914575672/1000000000)
  dsimp only [Z]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [ht0.2.2.1,ht0.2.2.2,ht1.2.2.1,ht1.2.2.2]

theorem Z_bounds {x : ℝ} (hx : x∈domain) : (541/1000:ℝ)<Z x ∧ Z x≤1 := by
  have hl := Z_antitone hx (show (23/50:ℝ)∈domain by constructor <;> norm_num) hx.2
  have hu := Z_antitone (show (0:ℝ)∈domain by constructor <;> norm_num) hx hx.1
  rw [Z_zero] at hu
  exact ⟨endpoint_heights.2.2.1.trans_le hl,hu⟩

theorem Z_extended {x : ℝ} (hx : x∈domain) : Z x∈extendedDomain := by
  have hh := Z_bounds hx
  constructor <;> linarith [hh.1,hh.2]

theorem normal_chart {x : ℝ} (hx : x∈normalDomain) : Z x∈Icc b2 c0 := by
  have hdom : x∈domain := ⟨by linarith [hx.1],hx.2⟩
  have hlo := (Z_bounds hdom).1
  have hu := Z_antitone (show (11/100:ℝ)∈domain by constructor <;> norm_num) hdom hx.1
  constructor <;> linarith [b2_bounds.2,endpoint_heights.2.1,c0_bounds.1]

theorem normal_Pd {x : ℝ} (hx : x∈normalDomain) : 0<Pd x ∧ Pd x<199/500 := by
  have hdom : x∈domain := ⟨by linarith [hx.1],hx.2⟩
  have hz := Z_bounds hdom
  have hu := Z_antitone (show (11/100:ℝ)∈domain by constructor <;> norm_num) hdom hx.1
  rw [Pd_eq]
  constructor <;> linarith [endpoint_heights.2.1]

theorem P_monotone : MonotoneOn P domain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (P_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => P_deriv x
  · intro x hx
    rw [Pd_eq]
    linarith [(Z_bounds (Ioo_subset_Icc_self hx)).1]

theorem P_lower {x : ℝ} (hx : x∈domain) : (1829/2000:ℝ)<P x := by
  have hh := P_monotone (show (0:ℝ)∈domain by constructor <;> norm_num) hx hx.1
  rw [P_zero] at hh
  linarith [a0_precise.1]

theorem normal_P_lower {x : ℝ} (hx : x∈normalDomain) : (24/25:ℝ)<P x := by
  have hh := P_monotone (show (11/100:ℝ)∈domain by constructor <;> norm_num)
    ⟨by linarith [hx.1],hx.2⟩ hx.1
  have ht := FrameHighLowDiagonalCurve.final_trig
  have hm := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤99395609/100000000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  dsimp only [P] at hh ⊢
  linarith [ht.1]

theorem upper_chart {x : ℝ} (hx : x∈upperDomain) :
    (896/1000:ℝ)<Z x ∧ Z x≤1 ∧ (79/100:ℝ)<A (Z x) ∧ A (Z x)<903/1000 := by
  have hdom : x∈domain := ⟨hx.1,by linarith [hx.2]⟩
  have hlo := Z_antitone hdom (show (11/100:ℝ)∈domain by constructor <;> norm_num) hx.2
  have hu := (Z_bounds hdom).2
  have hz : (896/1000:ℝ)<Z x := by linarith [endpoint_heights.1]
  have hc := extended_circle (Z_extended hdom)
  have hp := extended_shift_pos (Z_extended hdom)
  have hlowSq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤349/250)
    (show (349/250:ℝ)≤Z x+1/2 by linarith) 2
  have huppSq := pow_le_pow_left₀ (show 0≤Z x+1/2 by linarith)
    (show Z x+1/2≤3/2 by linarith) 2
  norm_num [Q0] at hc
  refine ⟨hz,hu,?_,?_⟩
  · by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le (show A (Z x)+1/2≤129/100 by linarith) 2
    nlinarith
  · by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1403/1000)
      (show (1403/1000:ℝ)≤A (Z x)+1/2 by linarith) 2
    nlinarith

theorem upper_marker_bounds {x : ℝ} (hx : x∈upperDomain) :
    0<Gd (Z x) ∧ Gd (Z x)<41/40 ∧ (11/20:ℝ)<Gdd (Z x) := by
  have hz := upper_chart hx
  have hp : 0<A (Z x)+1/2 := by linarith [hz.2.2.1]
  have hr0 : 0 ≤ slope (Z x) := div_nonneg (by linarith [hz.1]) hp.le
  have hr : slope (Z x)<50/43 := by
    apply (div_lt_iff₀ hp).2
    linarith [hz.2.1,hz.2.2.1]
  have hcube := pow_le_pow_left₀ hp.le
    (show A (Z x)+1/2≤1403/1000 by linarith [hz.2.2.2]) 3
  have hcurv : (11/20:ℝ)<FrameHighArc.v*Q0/(A (Z x)+1/2)^3 := by
    apply (lt_div_iff₀ (pow_pos hp 3)).2
    norm_num [FrameHighArc.v,Q0] at *
    nlinarith
  rw [mul_div_assoc] at hcurv
  dsimp only [Gd,Gdd,slopeD]
  refine ⟨?_,?_,hcurv⟩ <;> norm_num [FrameHighArc.u,FrameHighArc.v] <;> linarith

end SquaresInCircles.Eight.FrameHighLowAxialGeometry
end
end
end

section
/-!
## Curvature of the two exact low-axial contact costs

The ordinary high cost has second derivative greater than `.12` on
`[.11,.46]`.  The continued quarter marker has positive second
derivative on `[0,.11]`.  The same explicit contact curve supplies both
statements.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowAxialCalculus
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowAxialGeometry

def normalF (x : ℝ) : ℝ := x-(9/100)*(Real.sin x+Real.cos x-1)+H (Z x)
def normalD (x : ℝ) : ℝ := 1-(9/100)*(Real.cos x-Real.sin x)-Hd (Z x)*P x
def normalDD (x : ℝ) : ℝ := (9/100)*(Real.sin x+Real.cos x)+
  FrameHighArc.u*slopeD (Z x)*(P x)^2-Hd (Z x)*Pd x
def upperF (x : ℝ) : ℝ := x-(9/100)*(Real.sin x+Real.cos x-1)+G (Z x)
def upperD (x : ℝ) : ℝ := 1-(9/100)*(Real.cos x-Real.sin x)-Gd (Z x)*P x
def upperDD (x : ℝ) : ℝ := (9/100)*(Real.sin x+Real.cos x)+Gdd (Z x)*(P x)^2-Gd (Z x)*Pd x

theorem normal_deriv {x : ℝ} (hx : x∈normalDomain) : HasDerivAt normalF (normalD x) x := by
  have he := Z_extended (show x∈domain from ⟨by linarith [hx.1],hx.2⟩)
  have h := ((hasDerivAt_id' x).fun_sub
    ((((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).sub_const 1).const_mul
      (9/100))).fun_add ((extended_H_deriv he).comp x (Z_deriv x))
  have hv : normalD x=1-9/100*(Real.cos x+-Real.sin x)+FrameHighArc.Hd (Z x)*-P x := by
    simp only [normalD]; ring
  rw [hv]
  exact h

theorem normalD_deriv {x : ℝ} (hx : x∈normalDomain) : HasDerivAt normalD (normalDD x) x := by
  have he := Z_extended (show x∈domain from ⟨by linarith [hx.1],hx.2⟩)
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (9/100:ℝ)).const_sub 1).fun_sub
      (((extended_Hd_deriv he).comp x (Z_deriv x)).fun_mul (P_deriv x))
  have hv : normalDD x=-(9/100*(-Real.sin x-Real.cos x))-
      (FrameHighArc.u*slopeD (Z x)*-P x*P x+FrameHighArc.Hd (Z x)*Pd x) := by
    simp only [normalDD]; ring
  rw [hv]
  exact h

theorem upper_deriv {x : ℝ} (hx : x∈upperDomain) : HasDerivAt upperF (upperD x) x := by
  have he := Z_extended (show x∈domain from ⟨hx.1,by linarith [hx.2]⟩)
  have h := ((hasDerivAt_id' x).fun_sub
    ((((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).sub_const 1).const_mul
      (9/100))).fun_add ((G_deriv he).comp x (Z_deriv x))
  have hv : upperD x=1-9/100*(Real.cos x+-Real.sin x)+Gd (Z x)*-P x := by
    simp only [upperD]; ring
  rw [hv]
  exact h

theorem upperD_deriv {x : ℝ} (hx : x∈upperDomain) : HasDerivAt upperD (upperDD x) x := by
  have he := Z_extended (show x∈domain from ⟨hx.1,by linarith [hx.2]⟩)
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul
    (9/100:ℝ)).const_sub 1).fun_sub
      (((Gd_deriv he).comp x (Z_deriv x)).fun_mul (P_deriv x))
  have hv : upperDD x=-(9/100*(-Real.sin x-Real.cos x))-
      (Gdd (Z x)*-P x*P x+Gd (Z x)*Pd x) := by
    simp only [upperDD]; ring
  rw [hv]
  exact h

theorem normal_curvature {x : ℝ} (hx : x∈normalDomain) : (3/25:ℝ)<normalDD x := by
  have hq := quadrant (show x∈domain from ⟨by linarith [hx.1],hx.2⟩)
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hq).1] at hw
  have hz := normal_chart hx
  have hPd := normal_Pd hx
  have hP := normal_P_lower hx
  have hP2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤24/25) hP.le 2
  have hcurv := high_Hdd_lower hz
  have hm := mul_le_mul hcurv.le hP2
    (by norm_num : (0:ℝ)≤(24/25)^2) (by linarith : 0≤FrameHighArc.u*slopeD (Z x))
  have hHd : Hd (Z x)≤480179/500000 := by
    have hr := (slope_high_bounds hz).2
    dsimp [Hd,FrameHighArc.u,FrameHighArc.v]
    linarith
  have hlast := mul_le_mul hHd hPd.2.le hPd.1.le (by norm_num : (0:ℝ)≤480179/500000)
  dsimp [normalDD]
  nlinarith

theorem upper_curvature {x : ℝ} (hx : x∈upperDomain) : 0<upperDD x := by
  have hdom : x∈domain := ⟨hx.1,by linarith [hx.2]⟩
  have hq := quadrant hdom
  have hw := FrameCoreArc.width_one_le x
  rw [(first_width hq).1] at hw
  have hmarker := upper_marker_bounds hx
  have hP := P_lower hdom
  have hP2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1829/2000) hP.le 2
  have hm := mul_le_mul hmarker.2.2.le hP2
    (by norm_num : (0:ℝ)≤(1829/2000)^2) (by linarith [hmarker.2.2] : 0≤Gdd (Z x))
  have hPd : 0≤Pd x ∧ Pd x≤1/2 := by
    rw [Pd_eq]
    constructor <;> linarith [(Z_bounds hdom).1,(Z_bounds hdom).2]
  have hlast := mul_le_mul hmarker.2.1.le hPd.2 hPd.1 (by norm_num : (0:ℝ)≤41/40)
  dsimp [upperDD]
  nlinarith

end SquaresInCircles.Eight.FrameHighLowAxialCalculus
end
end
end

section
/-!
## Rational reference bounds for both exact axial costs

All auxiliary constants are displayed rational Taylor expressions.
The primary-coordinate ceilings are derived by squaring them against
the circle equation; no numerical root or endpoint value is assumed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowAxialReferences
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameHighLowAxialGeometry FrameHighLowAxialCalculus

def ref (normal : Bool) : ℝ := if normal then 23/200 else 11/100
def sl (normal : Bool) : ℝ := HighOrderTaylor.S11 (ref normal)
def su (normal : Bool) : ℝ := Arithmetic.sin9 (ref normal)
def cl (normal : Bool) : ℝ := Arithmetic.cos10 (ref normal)
def cu (normal : Bool) : ℝ := Arithmetic.cos8 (ref normal)
def zl (normal : Bool) : ℝ :=
  1/2+cl normal/2-(1414575672/1000000000-1/2)*su normal
def zu (normal : Bool) : ℝ :=
  1/2+cu normal/2-(1414575670/1000000000-1/2)*sl normal
def floor (normal : Bool) : ℝ := if normal then 22087/25000 else 4417/5000
def base (normal : Bool) : ℝ :=
  ref normal-(9/100)*(su normal+cu normal-1)+(314159/100000)/4+
    if normal then (FrameHighArc.u-FrameHighArc.v)*(179842813/200000000)+FrameHighArc.v*zl normal
    else -(FrameHighArc.u-FrameHighArc.v)*(449607033/500000000)+FrameHighArc.u*zl normal
def cap (normal : Bool) : ℝ :=
  (base normal-floor normal)/(if normal then FrameHighArc.u else FrameHighArc.v)

theorem ref_domain (normal : Bool) : ref normal∈domain := by
  cases normal <;> constructor <;> norm_num [ref,domain]

theorem taylor_bounds (normal : Bool) :
    sl normal≤Real.sin (ref normal) ∧ Real.sin (ref normal)≤ su normal ∧
      cl normal≤Real.cos (ref normal) ∧ Real.cos (ref normal)≤cu normal := by
  have hx : 0≤ref normal := (ref_domain normal).1
  exact ⟨HighOrderTaylor.S11_le_sin hx,Arithmetic.sin_le_sin9 hx,
    Arithmetic.cos10_le_cos hx,Arithmetic.cos_le_cos8 hx⟩

theorem positive_constants (normal : Bool) :
    0<sl normal ∧ 0<su normal ∧ 0<cl normal ∧ 0<cu normal ∧
      0<zl normal ∧ 0<cap normal+1/2 := by
  cases normal <;> norm_num [sl,su,cl,cu,zl,cap,base,floor,ref,
    FrameHighArc.u,FrameHighArc.v,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem height_bounds (normal : Bool) : zl normal≤Z (ref normal) ∧ Z (ref normal)≤zu normal := by
  have ht := taylor_bounds normal
  have hc := positive_constants normal
  have hs0 : 0≤Real.sin (ref normal) := hc.1.le.trans ht.1
  have hprodU := mul_le_mul
    (show a0-1/2≤1414575672/1000000000-1/2 by linarith [a0_precise.2]) ht.2.1
    hs0 (by norm_num : (0:ℝ)≤1414575672/1000000000-1/2)
  have hprodL := mul_le_mul
    (show (1414575670/1000000000-1/2:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht.1
    hc.1.le (by linarith [a0_precise.1] : 0≤a0-1/2)
  dsimp [zl,zu,Z]
  constructor <;> nlinarith

theorem cap_circle_reserve (normal : Bool) :
    Q0<(cap normal+1/2)^2+(zl normal+1/2)^2 := by
  cases normal <;> norm_num [cap,base,floor,zl,sl,su,cl,cu,ref,Q0,
    FrameHighArc.u,FrameHighArc.v,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]

theorem primary_upper (normal : Bool) : A (Z (ref normal))<cap normal := by
  have hz := height_bounds normal
  have hc := extended_circle (Z_extended (ref_domain normal))
  have hp := positive_constants normal
  have hzsq := pow_le_pow_left₀ (by linarith [hp.2.2.2.2.1] : 0≤zl normal+1/2)
    (show zl normal+1/2≤Z (ref normal)+1/2 by linarith [hz.1]) 2
  by_contra! hbad
  have hAsq := pow_le_pow_left₀ hp.2.2.2.2.2.le
    (show cap normal+1/2≤A (Z (ref normal))+1/2 by linarith) 2
  nlinarith [cap_circle_reserve normal]

theorem normal_value : (22087/25000:ℝ)<normalF (23/200) := by
  have ht := taylor_bounds true
  have hz := height_bounds true
  have hA := primary_upper true
  have he : FrameHighArc.u*cap true=base true-floor true := by
    dsimp [cap]
    field_simp
    norm_num [FrameHighArc.u]
  dsimp [normalF,H,k,FrameHighArc.u,FrameHighArc.v]
  dsimp [base,floor,ref] at he ht hz hA
  norm_num [FrameHighArc.u,FrameHighArc.v] at he
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.1]

theorem upper_value : (4417/5000:ℝ)<upperF (11/100) := by
  have ht := taylor_bounds false
  have hz := height_bounds false
  have hA := primary_upper false
  have he : FrameHighArc.v*cap false=base false-floor false := by
    dsimp [cap]
    field_simp
    norm_num [FrameHighArc.v]
  dsimp [upperF,G,FrameHighArc.u,FrameHighArc.v]
  dsimp [base,floor,ref] at he ht hz hA
  norm_num [FrameHighArc.u,FrameHighArc.v] at he
  nlinarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.2]

theorem normal_trig : (5737/50000:ℝ)<Real.sin (23/200) ∧
    Real.sin (23/200)<459/4000 ∧ (99339/100000:ℝ)<Real.cos (23/200) ∧
      Real.cos (23/200)<4967/5000 := by
  have ht := taylor_bounds true
  norm_num [sl,su,cl,cu,ref,HighOrderTaylor.S11,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at ht
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]

theorem normal_height : (8917/10000:ℝ)<Z (23/200) ∧ Z (23/200)<4459/5000 := by
  have hz := height_bounds true
  have hl : (8917/10000:ℝ)<zl true := by
    norm_num [zl,sl,su,cl,cu,ref,HighOrderTaylor.S11,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]
  have hu : zu true<(4459/5000:ℝ) := by
    norm_num [zu,sl,su,cl,cu,ref,HighOrderTaylor.S11,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8]
  exact ⟨by simpa [ref] using hl.trans_le hz.1,by simpa [ref] using hz.2.trans_lt hu⟩

theorem normal_primary_shift : (281/200:ℝ)<A (Z (23/200))+1/2 ∧
    A (Z (23/200))+1/2<176/125 := by
  have hx : (23/200:ℝ)∈domain := by constructor <;> norm_num [domain]
  have hc := extended_circle (Z_extended hx)
  have hp := extended_shift_pos (Z_extended hx)
  have hz := normal_height
  have hzl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤13917/10000)
    (show (13917/10000:ℝ)≤Z (23/200)+1/2 by linarith) 2
  have hzu := pow_le_pow_left₀ (show 0≤Z (23/200)+1/2 by linarith)
    (show Z (23/200)+1/2≤6959/5000 by linarith) 2
  norm_num [Q0] at hc
  constructor
  · by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    nlinarith
  · by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤176/125) hbad 2
    nlinarith

theorem normal_marker : (1907/2000:ℝ)<Hd (Z (23/200)) ∧ Hd (Z (23/200))<9553/10000 := by
  have hz := normal_height
  have ha := normal_primary_shift
  have hp : 0<A (Z (23/200))+1/2 := by linarith [ha.1]
  have hrL : (247/250:ℝ)<slope (Z (23/200)) := by
    apply (lt_div_iff₀ hp).2
    linarith [hz.1,ha.2]
  have hrU : slope (Z (23/200))<991/1000 := by
    apply (div_lt_iff₀ hp).2
    linarith [hz.2,ha.1]
  dsimp [Hd,FrameHighArc.u,FrameHighArc.v]
  constructor <;> linarith

theorem normal_P : (193/200:ℝ)<P (23/200) ∧ P (23/200)<967/1000 := by
  have ht := normal_trig
  have hlo := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤99339/100000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  have hhi := mul_le_mul
    (show a0-1/2≤914575672/1000000000 by linarith [a0_precise.2]) ht.2.2.2.le
    (by linarith [ht.2.2.1] : 0≤Real.cos (23/200)) (by norm_num : (0:ℝ)≤914575672/1000000000)
  dsimp [P]
  constructor <;> nlinarith

theorem normal_derivative : |normalD (23/200)|<3/1000 := by
  have ht := normal_trig
  have hd := normal_marker
  have hp := normal_P
  have hlo := mul_le_mul hd.1.le hp.1.le (by norm_num : (0:ℝ)≤193/200)
    (by linarith [hd.1] : 0≤Hd (Z (23/200)))
  have hhi := mul_le_mul hd.2.le hp.2.le (by linarith [hp.1] : 0≤P (23/200))
    (by norm_num : (0:ℝ)≤9553/10000)
  rw [abs_lt]
  dsimp [normalD]
  constructor <;> nlinarith

theorem upper_derivative : upperD (11/100)<0 := by
  have hx : (11/100:ℝ)∈upperDomain := by constructor <;> norm_num [upperDomain]
  have hz := upper_chart hx
  have hp : 0<A (Z (11/100))+1/2 := by linarith [hz.2.2.1]
  have hr : (199/200:ℝ)<slope (Z (11/100)) := by
    apply (lt_div_iff₀ hp).2
    linarith [endpoint_heights.1,hz.2.2.2]
  have hG : (479/500:ℝ)<Gd (Z (11/100)) := by
    dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
    linarith
  have ht := FrameHighLowDiagonalCurve.final_trig
  have hAc := mul_le_mul
    (show (914575670/1000000000:ℝ)≤a0-1/2 by linarith [a0_precise.1]) ht.2.2.1.le
    (by norm_num : (0:ℝ)≤99395609/100000000) (by linarith [a0_precise.1] : 0≤a0-1/2)
  have hP : (963/1000:ℝ)<P (11/100) := by dsimp [P]; nlinarith [ht.1]
  have hprod := mul_le_mul hG.le hP.le (by norm_num : (0:ℝ)≤963/1000)
    (by linarith : 0≤Gd (Z (11/100)))
  dsimp [upperD]
  nlinarith [ht.2.1,ht.2.2.1]

end SquaresInCircles.Eight.FrameHighLowAxialReferences
end
end
end

section
/-!
## Uniform curvature of the explicit high-diagonal contact

The correlation `w*w'` has one quadratic upper bound.  It controls the
first root derivative, while the root equation controls the second.
The resulting contact curvature is less than `-.8` on the complete
interval.  This proof does not use an implicit-function premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowDiagonalCurvature
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowDiagonalCurve

theorem sine_linear_lower {x : ℝ} (hx : x∈domain) : (99/100)*x≤Real.sin x := by
  have hs := Real.sin_ge_sub_cube hx.1
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hmul := mul_nonneg hx.1 (show 0≤(11/100:ℝ)^2-x^2 by linarith)
  linarith [hx.1]

theorem correlated_slope_upper {x : ℝ} (hx : x∈domain) : w x*wd x≤5/8 := by
  have ht := trig_bounds hx
  have hs := sine_linear_lower hx
  have hs2 := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤99/100) hx.1) hs 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx.1 hx.2 2
  have hdc := mul_le_mul
    (show (399/1000:ℝ)≤c0-1/2 by linarith [c0_bounds.1]) hcos
    (by linarith : 0≤1-x^2/2) (by linarith [c0_bounds.1] : 0≤c0-1/2)
  have hds := mul_le_mul
    (show c0-1/2≤2/5 by linarith [c0_bounds.2]) (Real.sin_le hx.1)
    ht.1 (by norm_num : (0:ℝ)≤2/5)
  have hid : w x*wd x=1-2*(Real.sin x)^2-(c0-1/2)*Real.cos x+(c0-1/2)*Real.sin x := by
    dsimp [w,wd]
    linear_combination Real.sin_sq_add_cos_sq x
  rw [hid]
  linarith [sq_nonneg ((17607/5000:ℝ)*x-2/5)]

theorem rho_first_lower {x : ℝ} (hx : x∈domain) : -(17/50:ℝ)≤rhod x := by
  have hnum := correlated_slope_upper hx
  have hr := (rho_bounds hx).1
  have hquot : w x*wd x/rho x≤17/50 := by
    apply (div_le_iff₀ (rho_positive hx)).2
    linarith
  have he : rhod x=-(w x*wd x/rho x) := by simp only [rhod]; ring
  rw [he]
  linarith

theorem rho_second_lower {x : ℝ} (hx : x∈domain) : -(63/100:ℝ)≤rhodd x := by
  have hw := w_bounds hx
  have hr := rho_bounds hx
  have hp := rho_positive hx
  have hw0 : 0≤w x := by linarith [hw.1]
  have hd0 : 0≤wd x := by linarith [hw.2.2.1]
  have hd2 := pow_le_pow_left₀ hd0 hw.2.2.2.1 2
  have hw2 := pow_le_pow_left₀ hw0 hw.2.1.le 2
  have hwdd := mul_nonpos_of_nonneg_of_nonpos hw0
    (by linarith [hw.2.2.2.2] : wdd x≤0)
  have hfirst : ((wd x)^2+w x*wdd x)/rho x≤25/46 := by
    apply (div_le_iff₀ hp).2
    linarith
  have hprod := mul_le_mul_of_nonneg_left hd2 (sq_nonneg (w x))
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤46/25) hr.1.le 3
  have hsecond : (w x)^2*(wd x)^2/(rho x)^3≤17/200 := by
    apply (div_le_iff₀ (pow_pos hp 3)).2
    linarith
  have he : rhodd x=-(((wd x)^2+w x*wdd x)/rho x)-(w x)^2*(wd x)^2/(rho x)^3 := by
    simp only [rhodd]; ring
  rw [he]
  linarith

theorem contact_second_upper {x : ℝ} (hx : x∈domain) : zdd x< -(4/5:ℝ) := by
  have ht := trig_bounds hx
  have hw := w_bounds hx
  have hr := rho_bounds hx
  have hrd := rho_first_lower hx
  have hrdd := rho_second_lower hx
  have hfirst : wdd x-2*rhod x-w x≤-(23/25:ℝ) := by
    have hsum := ht.2.2.2.2
    dsimp [w,wdd] at *
    linarith [c0_bounds.2]
  have hsecond : rho x-2*wd x-rhodd x≤2103/2500 := by
    linarith [hw.2.2.1]
  have hfirstMul := mul_le_mul_of_nonneg_right hfirst
    (show 0≤Real.cos x by linarith [ht.2.2.1])
  have hcosMul := mul_le_mul_of_nonpos_left ht.2.2.1 (by norm_num : (-(23/25:ℝ))≤0)
  have hsecondMul := mul_le_mul_of_nonneg_right hsecond ht.1
  have hsinMul := mul_le_mul_of_nonneg_left ht.2.1 (by norm_num : (0:ℝ)≤2103/2500)
  dsimp [zdd]
  linarith

theorem source_chart {x : ℝ} (hx : x∈domain) : z x∈extendedDomain := by
  have hh := z_bounds hx
  constructor <;> linarith [hh.1,hh.2]

theorem marker_derivative_lower {x : ℝ} (hx : x∈domain) : (19/20:ℝ)<Ld (z x) := by
  have hz := z_bounds hx
  have he := source_chart hx
  have hc := extended_circle he
  have hp := extended_shift_pos he
  have hsq := pow_le_pow_left₀ (show 0≤z x+1/2 by linarith [hz.1])
    (show z x+1/2≤601/1000 by linarith [hz.2]) 2
  have hA : (47/25:ℝ)<A (z x)+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hratio : slope (z x)<8/25 := by
    apply (div_lt_iff₀ hp).2
    linarith [hz.2]
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  linarith

end SquaresInCircles.Eight.FrameHighLowDiagonalCurvature
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighLowAxialScalars
open FramePairCalculus FrameHighLowAxialGeometry FrameHighLowAxialCalculus
open FrameHighLowAxialReferences

theorem normal_lower {x : ℝ} (hx : x∈normalDomain) :
    (8833/10000:ℝ)<normalF x := by
  have href : (23/200:ℝ)∈normalDomain := by constructor <;> norm_num [normalDomain]
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (3/25:ℝ)) (fun z hz => normal_deriv hz)
    (fun z hz => normalD_deriv hz) (fun z hz => (normal_curvature hz).le) href hx
  have hd := abs_lt.mp normal_derivative
  have hs := mul_pos (sub_pos.mpr hd.2)
    (show 0<normalD (23/200)+3/1000 by linarith [hd.1])
  nlinarith [normal_value,sq_nonneg (x-23/200+(25/3)*normalD (23/200))]

theorem upper_derivative_monotone : MonotoneOn upperD upperDomain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x hx => (upperD_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => upperD_deriv (Ioo_subset_Icc_self hx)
  · exact fun x hx => (upper_curvature (Ioo_subset_Icc_self hx)).le

theorem upper_antitone : AntitoneOn upperF upperDomain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (upper_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => upper_deriv (Ioo_subset_Icc_self hx)
  · intro x hx
    have hh := upper_derivative_monotone (Ioo_subset_Icc_self hx)
      (show (11/100:ℝ)∈upperDomain by constructor <;> norm_num [upperDomain]) hx.2.le
    exact hh.trans upper_derivative.le

theorem upper_lower {x : ℝ} (hx : x∈upperDomain) :
    (8833/10000:ℝ)<upperF x := by
  have hh := upper_antitone hx
    (show (11/100:ℝ)∈upperDomain by constructor <;> norm_num [upperDomain]) hx.2
  linarith [upper_value]

end SquaresInCircles.Eight.FrameHighLowAxialScalars
end
end
end
