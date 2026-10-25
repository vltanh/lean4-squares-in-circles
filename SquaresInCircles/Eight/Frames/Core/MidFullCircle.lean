module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Frames.Low.Pair
public import SquaresInCircles.Eight.Frames.Mid.Arc

/-!
# Eight squares: the core/middle whole-quadrant full-circle support

The actual radical support decreases on the entire first quadrant.
Its derivative sign follows from one degree-six polynomial in the
half-angle coordinate, with a coefficientwise positive remainder and
one elementary positive factor.  A single Taylor enclosure at `1.53`
then supplies the strict reserve.  No interval row or mesh is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameCoreMidFullCircle
open FramePair FrameCircleArc FrameMidArc

def N (x : ℝ) : ℝ :=
  Real.sqrt (p^2+q^2+g^2+2*g*(p*Real.sin x-q*Real.cos x))
def F (x : ℝ) : ℝ :=
  x+9/100-cM+(p+q+g)/2+(g-9/100)*Real.sin x-(9/100)*Real.cos x-R*N x
def Nd (x : ℝ) : ℝ := g*(p*Real.cos x+q*Real.sin x)/N x
def Fd (x : ℝ) : ℝ :=
  1+(g-9/100)*Real.cos x+(9/100)*Real.sin x-R*Nd x

theorem energy_pos {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    0<p^2+q^2+g^2+2*g*(p*Real.sin x-q*Real.cos x) := by
  have hq := FrameLowPair.quadrant hx
  have hp : 0<p+g*Real.sin x := by dsimp [p,g]; linarith [hq.1]
  have he : p^2+q^2+g^2+2*g*(p*Real.sin x-q*Real.cos x)=
      (p+g*Real.sin x)^2+(g*Real.cos x-q)^2 := by
    linear_combination -g^2*(Real.sin_sq_add_cos_sq x)
  rw [he]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hp) (sq_nonneg _)

theorem N_pos {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : 0<N x :=
  Real.sqrt_pos.mpr (energy_pos hx)

theorem N_sq {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    (N x)^2=p^2+q^2+g^2+2*g*(p*Real.sin x-q*Real.cos x) :=
  Real.sq_sqrt (energy_pos hx).le

theorem N_deriv {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : HasDerivAt N (Nd x) x := by
  have hd := (((((Real.hasDerivAt_sin x).const_mul p).fun_sub
    ((Real.hasDerivAt_cos x).const_mul q)).const_mul (2*g)).const_add
      (p^2+q^2+g^2)).sqrt (energy_pos hx).ne'
  show HasDerivAt (fun y => Real.sqrt (p^2+q^2+g^2+2*g*(p*Real.sin y-q*Real.cos y))) _ x
  convert hd using 1
  have hn : Real.sqrt (p^2+q^2+g^2+2*g*(p*Real.sin x-q*Real.cos x))≠0 := (N_pos hx).ne'
  dsimp [Nd,N]
  field_simp
  ring

theorem F_deriv {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : HasDerivAt F (Fd x) x := by
  have hh := (((((((hasDerivAt_id' x).add_const (9/100)).sub_const cM).add_const
    ((p+q+g)/2)).fun_add ((Real.hasDerivAt_sin x).const_mul (g-9/100))).fun_sub
      ((Real.hasDerivAt_cos x).const_mul (9/100))).fun_sub ((N_deriv hx).const_mul R))
  show HasDerivAt
    (fun y => y+9/100-cM+(p+q+g)/2+(g-9/100)*Real.sin y-(9/100)*Real.cos y-R*N y) _ x
  convert hh using 1
  dsimp [Fd]
  ring

def D (z : ℝ) : ℝ := 1+z^2
def S (z : ℝ) : ℝ := 2*z
def C (z : ℝ) : ℝ := 1-z^2
def E (z : ℝ) : ℝ := (p^2+q^2+g^2)*D z+2*g*(p*S z-q*C z)
def J (z : ℝ) : ℝ := D z+(g-9/100)*C z+(9/100)*S z
def P (z : ℝ) : ℝ :=
  Q0*g^2*(p*C z+q*S z)^2*D z-(J z)^2*E z
def lowerP (z : ℝ) : ℝ :=
  8/25+15*z-(25/4)*z^2-(29/4)*z^3+34*z^4-43*z^5+10*z^6

theorem polynomial_remainder {z : ℝ} (hz : 0≤z) : lowerP z<P z := by
  have hh : 0<P z-lowerP z := by
    simp only [P,J,E,D,S,C,lowerP,p,q,g,Q0]
    ring_nf
    positivity
  linarith

theorem polynomial_positive {z : ℝ} (hz : z∈Icc 0 1) : (8/25:ℝ)<P z := by
  have h2 : z^2≤z := by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
  have h3 : z^3≤z := by
    have hh := mul_le_mul_of_nonneg_right h2 hz.1
    nlinarith
  have htail : 1≤34-43*z+10*z^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hz.2) (show 0≤33-10*z by linarith [hz.2])
    nlinarith
  have hmul := mul_nonneg (pow_nonneg hz.1 4)
    (show 0≤34-43*z+10*z^2 by linarith)
  have hlo : (8/25:ℝ)≤lowerP z := by
    dsimp [lowerP]
    nlinarith
  exact hlo.trans_lt (polynomial_remainder hz.1)

theorem half_angle {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    ∃z∈Icc (0:ℝ) 1, D z*Real.sin x=S z ∧ D z*Real.cos x=C z := by
  have hq := FrameLowPair.quadrant hx
  have hd : 0<1+Real.cos x := by linarith [hq.2.2.1]
  let z : ℝ := Real.sin x/(1+Real.cos x)
  have hz0 : 0≤z := div_nonneg hq.1 hd.le
  have hz1 : z≤1 := (div_le_one hd).2 (by linarith [hq.2.1,hq.2.2.1])
  have hid : z*(1+Real.cos x)=Real.sin x := div_mul_cancel₀ _ hd.ne'
  have hsq : z^2*(1+Real.cos x)=1-Real.cos x := by
    apply (mul_right_cancel₀ hd.ne')
    calc
      (z^2*(1+Real.cos x))*(1+Real.cos x)=(Real.sin x)^2 := by rw [← hid]; ring
      _=(1-Real.cos x)*(1+Real.cos x) := by nlinarith [Real.sin_sq_add_cos_sq x]
  refine ⟨z,⟨hz0,hz1⟩,?_,?_⟩
  · dsimp [D,S]
    rw [← hid]
    nlinarith only [hsq,congrArg (fun a : ℝ => z*a) hsq]
  · dsimp [D,C]
    nlinarith only [hsq]

theorem Fd_negative {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : Fd x<0 := by
  obtain ⟨z,hz,hs,hc⟩ := half_angle hx
  have hD : 0<D z := by dsimp [D]; positivity
  have hn := N_pos hx
  have hN2 := N_sq hx
  have hq := FrameLowPair.quadrant hx
  have hforce : 0<p*Real.cos x+q*Real.sin x := by
    by_contra! hn
    have hcs : Real.cos x=0 := by dsimp [p,q] at hn; linarith only [hn,hq.1,hq.2.2.1]
    have hss : Real.sin x=0 := by dsimp [p,q] at hn; linarith only [hn,hq.1,hq.2.2.1]
    have hh := Real.sin_sq_add_cos_sq x
    rw [hcs,hss] at hh
    norm_num at hh
  let a : ℝ := 1+(g-9/100)*Real.cos x+(9/100)*Real.sin x
  have ha : 0<a := by dsimp [a,g]; linarith only [hq.1,hq.2.2.1]
  have hE : E z=D z*(N x)^2 := by
    dsimp [E]
    rw [← hs,← hc,hN2]
    ring
  have hJ : J z=D z*a := by dsimp [J,a]; rw [← hs,← hc]; ring
  have hP : P z=(D z)^3*
      (Q0*g^2*(p*Real.cos x+q*Real.sin x)^2-a^2*(N x)^2) := by
    dsimp [P]
    rw [hE,hJ,← hs,← hc]
    ring
  have hp := polynomial_positive hz
  have hdelta : 0<Q0*g^2*(p*Real.cos x+q*Real.sin x)^2-a^2*(N x)^2 := by
    have hh : 0<(D z)^3*
        (Q0*g^2*(p*Real.cos x+q*Real.sin x)^2-a^2*(N x)^2) := by
      rw [← hP]
      linarith
    by_contra! hbad
    have hn := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hD.le 3) hbad
    linarith
  have hprod : 0<R*g*(p*Real.cos x+q*Real.sin x) := by
    exact mul_pos (mul_pos R_pos (by norm_num [g])) hforce
  have hsq : (R*g*(p*Real.cos x+q*Real.sin x))^2=
      Q0*g^2*(p*Real.cos x+q*Real.sin x)^2 := by rw [mul_pow,mul_pow,R_sq]
  have hlt : a*N x<R*g*(p*Real.cos x+q*Real.sin x) := by
    apply lt_of_pow_lt_pow_left₀ 2 hprod.le
    rw [hsq]
    linarith
  have hdiv := (lt_div_iff₀ hn).2 hlt
  have hfin : Fd x=a-R*g*(p*Real.cos x+q*Real.sin x)/N x := by
    dsimp [Fd,Nd,a]
    ring
  rw [hfin]
  linarith

theorem F_antitone : AntitoneOn F (Icc 0 (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (F_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => F_deriv (Ioo_subset_Icc_self hx)
  · exact fun x hx => (Fd_negative (Ioo_subset_Icc_self hx)).le

theorem endpoint_trig :
    (24979/25000:ℝ)<Real.sin (153/100:ℝ) ∧
      Real.sin (153/100:ℝ)<99917/100000 ∧
      (2039/50000:ℝ)<Real.cos (153/100:ℝ) ∧
      Real.cos (153/100:ℝ)<4079/100000 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤153/100 by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤153/100 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤153/100 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤153/100 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem endpoint_lower : (9013/10000:ℝ)<F (153/100:ℝ) := by
  have hx : (153/100:ℝ)∈Icc 0 (Real.pi/2) :=
    ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩
  have ht := endpoint_trig
  have hN2 := N_sq hx
  have hR2 := R_sq
  have hprod : 0≤R*N (153/100:ℝ) := mul_nonneg R_pos.le (N_pos hx).le
  have hs := mul_le_mul_of_nonneg_left ht.2.1.le (show 0≤2*g*p by norm_num [g,p])
  have hc := mul_le_mul_of_nonneg_left ht.2.2.1.le (show 0≤2*g*q by norm_num [g,q])
  have hnum : Q0*(p^2+q^2+g^2+2*g*(p*(99917/100000)-q*(2039/50000)))<
      (29591/5000:ℝ)^2 := by norm_num [Q0,p,q,g]
  have hNhi : R*N (153/100:ℝ)<29591/5000 := by
    have he : (R*N (153/100:ℝ))^2=Q0*(N (153/100:ℝ))^2 := by rw [mul_pow,R_sq]
    have hmul := mul_le_mul_of_nonneg_left
      (show (N (153/100:ℝ))^2≤
          p^2+q^2+g^2+2*g*(p*(99917/100000)-q*(2039/50000)) by nlinarith)
      (show 0≤Q0 by norm_num [Q0])
    nlinarith
  have hnon : (13639/2000:ℝ)<
      (153/100:ℝ)+9/100-cM+(p+q+g)/2+
        (g-9/100)*Real.sin (153/100:ℝ)-(9/100)*Real.cos (153/100:ℝ) := by
    have hsin := mul_le_mul_of_nonneg_left ht.1.le (show 0≤g-9/100 by norm_num [g])
    dsimp [p,q,g,cM] at *
    linarith [ht.2.2.2]
  dsimp [F]
  linarith

/-- The original radical support, on the entire interval required by
the core-source positive-target transverse case. -/
theorem lower {x : ℝ} (hx : x∈Icc 0 (153/100:ℝ)) : (9013/10000:ℝ)<F x := by
  have hu : (153/100:ℝ)≤Real.pi/2 := by linarith [FrameLowPair.pi_lower]
  exact endpoint_lower.trans_le
    (F_antitone ⟨hx.1,hx.2.trans hu⟩ ⟨by norm_num,hu⟩ hx.2)

end SquaresInCircles.Eight.FrameCoreMidFullCircle
