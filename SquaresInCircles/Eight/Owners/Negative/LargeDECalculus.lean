module

public import SquaresInCircles.Eight.Frames.Ordinary.CurvatureBounds
public import SquaresInCircles.Eight.Owners.GA.Secant.Gain

/-!
# Eight squares: whole-domain curvature for the negative large-tangent DE boundary

The ordinary negative-angle force uses the existing
monotonicity of its exact norm curvature.  Its zero-angle coefficient is
bounded by positive squaring on the complete coefficient interval.  The
secant force is differentiated explicitly and bounded on the complete
short-angle interval.  These are the two quantitative reserves needed
to concentrate one common stress on its three angular simplex vertices.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.NegativeLargeDECalculus
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds

def R : ℝ := Real.sqrt qTrial
def g (p z : ℝ) : ℝ := Real.cos z-R*pairNorm p 1 (-z)
def gd (p z : ℝ) : ℝ := -Real.sin z+R*normD1 p 1 (-z)
def gdd (p z : ℝ) : ℝ := -Real.cos z+curvature R p 1 (-z)

theorem radius_sq : R^2=qTrial := Real.sq_sqrt (by norm_num [qTrial])

theorem radius_bounds : (989/500 : ℝ)<R ∧ R^2≤qCap := by
  have hs := Real.sq_sqrt (show 0≤qTrial by norm_num [qTrial])
  have hn := Real.sqrt_nonneg qTrial
  dsimp [R,qTrial,qCap] at *
  constructor <;> nlinarith

theorem short_trig {z : ℝ} (hz : z∈Icc 0 (27/100 : ℝ)) :
    24/25<Real.cos z ∧ Real.cos z≤1 ∧ 0≤Real.sin z ∧ Real.sin z≤27/100 := by
  have hsq := pow_le_pow_left₀ hz.1 hz.2 2
  have hc : 24/25<Real.cos z := by linarith [Real.one_sub_sq_div_two_le_cos (x := z)]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [hz.2,Real.pi_gt_three])
  exact ⟨hc,Real.cos_le_one z,hs,(Real.sin_le hz.1).trans hz.2⟩

theorem zero_curvature_upper {p : ℝ} (hp : p∈Ioo (0:ℝ) (18/25)) :
    curvatureZero R p 1<(14/25 : ℝ) := by
  have hQ := radius_bounds.2
  have hp2 := pow_le_pow_left₀ hp.1.le hp.2.le 2
  have hp4 := mul_le_mul_of_nonneg_right hp2 (sq_nonneg p)
  have hpol : (14/25 : ℝ)^2*(1+p^2)^3-qCap*p^4=
      196/625+(588/625)*p^2-(7437/2500)*p^4+(196/625)*p^6 := by
    dsimp [qCap]
    ring
  have hpos : 0<(14/25 : ℝ)^2*(1+p^2)^3-qCap*p^4 := by
    rw [hpol]
    nlinarith [pow_nonneg hp.1.le 6]
  have hRprod := mul_le_mul_of_nonneg_right hQ (pow_nonneg hp.1.le 4)
  have hden : ((shape p)^3)^2=(1+p^2)^3 := by
    calc
      ((shape p)^3)^2=((shape p)^2)^3 := by ring
      _=(1+p^2)^3 := by rw [shape_sq]
  have hh := quotient_lt_of_square (x := R*p^2) (y := (shape p)^3)
    (pow_pos (shape_pos p) 3) (show (0:ℝ)<14/25 by norm_num)
    (by
      rw [hden]
      have hsq : (R*p^2)^2=R^2*p^4 := by ring
      rw [hsq]
      dsimp only [qCap] at hRprod hpos
      linarith)
  simpa [curvatureZero,pairProduct,pairNorm,shape,add_comm] using hh

theorem g_hasDerivAt {p z : ℝ} (hp : 0<p)
    (hz : z∈Icc 0 (27/100 : ℝ)) : HasDerivAt (g p) (gd p z) z := by
  have hn := (pairNorm_hasDerivAt hp (show (0:ℝ)<1 by norm_num)
    (show |-z|≤frameCap by rw [abs_neg,abs_of_nonneg hz.1]; dsimp [frameCap]; linarith [hz.2])).comp z
      (hasDerivAt_id z).neg
  convert (Real.hasDerivAt_cos z).sub (hn.const_mul R) using 1
  · rfl
  · dsimp [gd]
    ring

theorem gd_hasDerivAt {p z : ℝ} (hp : 0<p)
    (hz : z∈Icc 0 (27/100 : ℝ)) : HasDerivAt (gd p) (gdd p z) z := by
  have hn := (normD1_hasDerivAt hp (show (0:ℝ)<1 by norm_num)
    (show |-z|≤frameCap by rw [abs_neg,abs_of_nonneg hz.1]; dsimp [frameCap]; linarith [hz.2])).comp z
      (hasDerivAt_id z).neg
  convert (Real.hasDerivAt_sin z).neg.add (hn.const_mul R) using 1
  · rfl
  · dsimp [gdd,curvature]
    ring

theorem gdd_upper {p z : ℝ} (hp : p∈Ioo (0:ℝ) (18/25))
    (hz : z∈Icc 0 (27/100 : ℝ)) : gdd p z< -(2/5 : ℝ) := by
  have hR : 0≤R := by linarith [radius_bounds.1]
  have hc := curvature_negative_upper hR hp.1 (show (0:ℝ)<1 by norm_num)
    (show -z∈Icc (-frameCap) 0 by dsimp [frameCap]; constructor <;> linarith [hz.1,hz.2])
  have hzero := zero_curvature_upper hp
  have hcos := (short_trig hz).1
  dsimp [gdd]
  linarith

def N (ε z : ℝ) : ℝ := Real.sqrt (GlobalGA.gainRadicand ε z)
def Nd (ε z : ℝ) : ℝ := -ε^2*Real.cos z*Real.sin z/N ε z
def f (ε z : ℝ) : ℝ := GlobalGA.secantGain qTrial ε z+1-R*Real.sqrt (1+ε^2)
def fd (ε z : ℝ) : ℝ := GlobalGA.secantGainDeriv qTrial ε z
def fdd (ε z : ℝ) : ℝ :=
  (1-R/N ε z)*(1+(Real.sin z)^2)/(Real.cos z)^3+
    (13/6)*Real.sin z/(Real.cos z)^3-
    R*ε^2*(Real.sin z)^2/(Real.cos z*(N ε z)^3)

theorem N_pos (ε z : ℝ) : 0<N ε z := Real.sqrt_pos.mpr (GlobalGA.gainRadicand_pos ε z)
theorem N_sq (ε z : ℝ) : (N ε z)^2=1+ε^2*(Real.cos z)^2 :=
  Real.sq_sqrt (GlobalGA.gainRadicand_pos ε z).le

theorem N_hasDerivAt (ε z : ℝ) : HasDerivAt (N ε) (Nd ε z) z := by
  have hh := (GlobalGA.gainRadicand_hasDerivAt ε z).sqrt
    (GlobalGA.gainRadicand_pos ε z).ne'
  convert hh using 1
  · rfl
  · dsimp [Nd,N]
    ring

theorem f_formula {ε z : ℝ} (hc : 0<Real.cos z) :
    f ε z=1/Real.cos z+(13/12)*Real.tan z-R*Real.sqrt (ε^2+(1/Real.cos z)^2) := by
  dsimp [f]
  rw [GlobalGA.secantGain_eq_secant_expression qTrial ε hc]
  dsimp [R]
  rw [add_comm ((1/Real.cos z)^2) (ε^2)]
  ring

theorem f_hasDerivAt {ε z : ℝ} (hz : z∈Icc 0 (27/100 : ℝ)) :
    HasDerivAt (f ε) (fd ε z) z := by
  have hc : Real.cos z≠0 := (show 0<Real.cos z by linarith [(short_trig hz).1]).ne'
  exact ((GlobalGA.secantGain_hasDerivAt qTrial ε hc).add_const 1).sub_const
    (R*Real.sqrt (1+ε^2))

theorem fd_hasDerivAt {ε z : ℝ} (hz : z∈Icc 0 (27/100 : ℝ)) :
    HasDerivAt (fd ε) (fdd ε z) z := by
  have hc : Real.cos z≠0 := (show 0<Real.cos z by linarith [(short_trig hz).1]).ne'
  have hn := (N_pos ε z).ne'
  have hnum := (((Real.hasDerivAt_sin z).const_add (13/12)).sub
    (((Real.hasDerivAt_sin z).const_mul R).div (N_hasDerivAt ε z) hn))
  have hh := hnum.div ((Real.hasDerivAt_cos z).pow 2) (pow_ne_zero 2 hc)
  have hu := Real.sin_sq_add_cos_sq z
  convert hh using 1
  · rfl
  · simp only [Pi.pow_apply,Pi.sub_apply,Pi.div_apply]
    dsimp only [fdd,Nd]
    field_simp
    linear_combination 72*Real.cos z*(N ε z)^2*(R-N ε z)*hu

theorem fdd_upper {ε z : ℝ} (hε : |ε|≤117/100)
    (hz : z∈Icc 0 (27/100 : ℝ)) : fdd ε z<(39/100 : ℝ) := by
  obtain ⟨hc,hc1,hs0,hs⟩ := short_trig hz
  have hc0 : 0<Real.cos z := by linarith
  have hn0 := N_pos ε z
  have hR0 : 0≤R := by linarith [radius_bounds.1]
  have hε2 : ε^2≤(117/100 : ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg ε) hε 2
  have hc2 : (Real.cos z)^2≤1 := by simpa using pow_le_pow_left₀ hc0.le hc1 2
  have hprod := mul_le_mul_of_nonneg_left hc2 (sq_nonneg ε)
  have hN : N ε z<77/50 := by nlinarith [N_sq ε z]
  have hratio : (989/770 : ℝ)<R/N ε z := by
    apply (lt_div_iff₀ hn0).2
    nlinarith [radius_bounds.1]
  have hsec : 1/Real.cos z≤25/24 := by
    apply (div_le_iff₀ hc0).2
    linarith
  have htan : Real.sin z/Real.cos z≤2/7 := by
    apply (div_le_iff₀ hc0).2
    linarith
  have htan0 : 0≤Real.sin z/Real.cos z := div_nonneg hs0 hc0.le
  have hsec0 : 0≤1/Real.cos z := div_nonneg (by norm_num) hc0.le
  have hsec2 := pow_le_pow_left₀ hsec0 hsec 2
  have htrig := mul_le_mul hsec2 htan htan0 (by norm_num : (0:ℝ)≤(25/24)^2)
  have hid : (1/Real.cos z)^2*(Real.sin z/Real.cos z)=
      Real.sin z/(Real.cos z)^3 := by field_simp [hc0.ne']
  rw [hid] at htrig
  have hc3 : (Real.cos z)^3≤1 := by simpa using pow_le_pow_left₀ hc0.le hc1 3
  have hsecdd : 1≤(1+(Real.sin z)^2)/(Real.cos z)^3 := by
    apply (le_div_iff₀ (pow_pos hc0 3)).2
    nlinarith [sq_nonneg (Real.sin z)]
  have hfirst := mul_le_mul_of_nonneg_right
    (show 1-R/N ε z≤ -(219/770 : ℝ) by linarith)
    (show 0≤(1+(Real.sin z)^2)/(Real.cos z)^3 by positivity)
  have hfirst' := mul_le_mul_of_nonpos_left hsecdd
    (show -(219/770 : ℝ)≤0 by norm_num)
  have hlast : 0≤R*ε^2*(Real.sin z)^2/(Real.cos z*(N ε z)^3) := by positivity
  have htrig' := mul_le_mul_of_nonneg_left htrig (show (0:ℝ)≤13/6 by norm_num)
  have hbound : fdd ε z≤ -(219/770 : ℝ)+(13/6)*(25/24)^2*(2/7) := by
    dsimp [fdd]
    have hid' : (1-R/N ε z)*(1+(Real.sin z)^2)/(Real.cos z)^3=
        (1-R/N ε z)*((1+(Real.sin z)^2)/(Real.cos z)^3) := by ring
    have hid'' : (13/6)*Real.sin z/(Real.cos z)^3=(13/6)*(Real.sin z/(Real.cos z)^3) := by ring
    rw [hid',hid'']
    linarith
  exact hbound.trans_lt (by norm_num)

end SquaresInCircles.Eight.NegativeLargeDECalculus
