module

public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity

/-!
# Eight squares: the universal positive ordinary-angle envelope

The bound `U(t) ≥ -(109/200) q t` is proved
uniformly on the complete coefficient and angle intervals. Its endpoint
radical comparison reduces to one explicit quartic, whose positivity is
proved by a shifted square and a nonnegative tail. No coefficient table,
angle partition, or presumed optimizer value is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OrdinaryPositiveEnvelope
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity

def endpointLine (r : ℝ) : ℝ := (409/1000)*r+763/2000

def endpointQuartic (r : ℝ) : ℝ :=
  4*qCap*(endpointLine r)^2*(1+r^2)-
    (2*qCap*(6443/10000)*r-(endpointLine r)^2)^2

/-- Exact whole-interval positivity. The pivot is an algebraic square
completion, not a sample at which positivity is assumed. -/
theorem endpointQuartic_pos {r : ℝ} (hr : r∈Icc (1/2) 1) :
    0<endpointQuartic r := by
  let x : ℝ := r-97/100
  have hxlo : -(47/100 : ℝ)≤x := by dsimp [x]; linarith [hr.1]
  have hxhi : x≤3/100 := by dsimp [x]; linarith [hr.2]
  have htail : 0≤x^2*
      ((79544927392683861/5000000000000000 : ℝ)-8+
        (413212596976581/25000000000000 : ℝ)*x+
        (2592039001439/1000000000000 : ℝ)*x^2) := by
    apply mul_nonneg (sq_nonneg x)
    nlinarith [sq_nonneg x]
  have hid : endpointQuartic r=
      8*x^2-(15812871342025923/250000000000000000 : ℝ)*x+
        1864574190538604271/100000000000000000000+
      x^2*((79544927392683861/5000000000000000 : ℝ)-8+
        (413212596976581/25000000000000 : ℝ)*x+
        (2592039001439/1000000000000 : ℝ)*x^2) := by
    dsimp [endpointQuartic,endpointLine,qCap,x]
    ring
  rw [hid]
  nlinarith [sq_nonneg (x-1/250)]

/-- The two positive square comparisons are made explicit. -/
theorem positive_norm_increment_le {r : ℝ} (hr : r∈Icc (1/2) 1) :
    Real.sqrt qCap*(pairNorm r 1 frameCap-shape r)≤endpointLine r := by
  have hrp : 0<r := by linarith [hr.1]
  have hN := pairNorm_pos hrp (show (0:ℝ)<1 by norm_num)
    (show |frameCap|≤frameCap by norm_num [frameCap])
  have hN2 := pairNorm_sq hrp (show (0:ℝ)<1 by norm_num)
    (show |frameCap|≤frameCap by norm_num [frameCap])
  have hQ := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hQpos : 0<Real.sqrt qCap := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hS := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).2.2.2.1
  have hline : 0<endpointLine r := by dsimp [endpointLine]; linarith [hr.1]
  have hY2 : (Real.sqrt qCap*shape r)^2=qCap*(1+r^2) := by
    rw [mul_pow,hQ,shape_sq]
  have hX2 : (Real.sqrt qCap*pairNorm r 1 frameCap)^2=
      qCap*(1+r^2+2*r*Real.sin frameCap) := by
    rw [mul_pow,hQ,hN2]
    dsimp [pairEnergy,pairProduct]
    ring
  have hpoly := endpointQuartic_pos hr
  have hcross : 2*qCap*(6443/10000)*r-(endpointLine r)^2<
      2*(Real.sqrt qCap*shape r)*endpointLine r := by
    by_contra! hbad
    have hsq := pow_le_pow_left₀
      (mul_pos (mul_pos two_pos (mul_pos hQpos (shape_pos r))) hline).le hbad 2
    dsimp [endpointQuartic] at hpoly
    have he : (2*(Real.sqrt qCap*shape r)*endpointLine r)^2=
        4*qCap*(1+r^2)*(endpointLine r)^2 := by
      calc
        (2*(Real.sqrt qCap*shape r)*endpointLine r)^2=
          4*(Real.sqrt qCap*shape r)^2*(endpointLine r)^2 := by ring
        _=4*qCap*(1+r^2)*(endpointLine r)^2 := by rw [hY2]; ring
    rw [he] at hsq
    nlinarith
  have hsin := mul_le_mul_of_nonneg_left hS.le
    (show 0≤2*qCap*r by positivity)
  have hsum : Real.sqrt qCap*pairNorm r 1 frameCap≤
      Real.sqrt qCap*shape r+endpointLine r := by
    by_contra! hbad
    have hsq := pow_le_pow_left₀
      (add_pos (mul_pos hQpos (shape_pos r)) hline).le hbad.le 2
    rw [hX2] at hsq
    generalize qCap=Q at *
    linarith
  linarith only [hsum]

theorem normalized_endpoint_lower {R r : ℝ} (_hR : 0≤R) (hQ : R^2≤qCap)
    (hr : r∈Icc (1/2) 1) :
    -(763/2000 : ℝ)≤r*(PositiveAngularEnvelope.phi frameCap-1)-
      R*(pairNorm r 1 frameCap-shape r) := by
  have hrp : 0<r := by linarith [hr.1]
  have hN2 := pairNorm_sq hrp (show (0:ℝ)<1 by norm_num)
    (show |frameCap|≤frameCap by norm_num [frameCap])
  have hN := pairNorm_pos hrp (show (0:ℝ)<1 by norm_num)
    (show |frameCap|≤frameCap by norm_num [frameCap])
  have hS := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).2.2.1
  have hinc : 0≤pairNorm r 1 frameCap-shape r := by
    have hsq := shape_sq r
    dsimp [pairEnergy,pairProduct] at hN2
    nlinarith [mul_nonneg hrp.le hS,shape_pos r]
  have hRle : R≤Real.sqrt qCap := by
    nlinarith [Real.sq_sqrt (show 0≤qCap by norm_num [qCap]),Real.sqrt_nonneg qCap]
  have hmul := mul_le_mul_of_nonneg_right hRle hinc
  have hnorm := positive_norm_increment_le hr
  have hphi := mul_le_mul_of_nonneg_left phi_cap_lower.le hrp.le
  dsimp [endpointLine] at hnorm
  nlinarith

theorem U_endpoint_lower {R p q : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    -(763/2000)*q≤U R p q frameCap := by
  have hq : 0<q := hp.trans_le hpq
  let r : ℝ := p/q
  have hr : r∈Icc (1/2) 1 := by
    dsimp [r]
    exact ⟨(le_div_iff₀ hq).2 (by linarith),(div_le_one hq).2 hpq⟩
  have hpqr : p=q*r := by dsimp [r]; field_simp
  have hN (t : ℝ) : pairNorm p q t=q*pairNorm r 1 t := by
    unfold pairNorm
    rw [hpqr]
    have he : (q*r)^2+q^2+2*(q*r)*q*Real.sin t=
        q^2*(r^2+1^2+2*r*1*Real.sin t) := by ring
    rw [he,Real.sqrt_mul (sq_nonneg q),Real.sqrt_sq hq.le]
  have hzero : pairNorm r 1 0=shape r := by simp [pairNorm,shape,add_comm]
  have he : U R p q frameCap=q*(r*(PositiveAngularEnvelope.phi frameCap-1)-
      R*(pairNorm r 1 frameCap-shape r)) := by
    unfold U
    rw [hN frameCap,hN 0,hzero,hpqr]
    ring
  rw [he]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (normalized_endpoint_lower hR hQ hr) hq.le

/-- The endpoint bound propagates along the whole interval by the already
proved concavity of the actual ordinary force increment. -/
theorem U_lower {R p q t : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (ht : t∈Icc 0 frameCap) :
    -(109/200)*q*t≤U R p q t := by
  have hh : 0<frameCap := by norm_num [frameCap]
  have hα : 0≤t/frameCap ∧ t/frameCap≤1 :=
    ⟨div_nonneg ht.1 hh.le,(div_le_one hh).2 ht.2⟩
  have h := (U_concave hR hQ hp hpq hqp).2
    (show (0:ℝ)∈Icc 0 frameCap from ⟨le_rfl,hh.le⟩)
    (show frameCap∈Icc 0 frameCap from ⟨hh.le,le_rfl⟩)
    (sub_nonneg.mpr hα.2) hα.1 (by ring)
  simp only [smul_eq_mul,U_zero,mul_zero,zero_add] at h
  rw [div_mul_cancel₀ t hh.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left (U_endpoint_lower hR hQ hp hpq hqp) hα.1
  have hid : (t/frameCap)*(-(763/2000)*q)=-(109/200)*q*t := by
    dsimp [frameCap]
    ring
  rw [hid] at hmul
  exact hmul.trans h

end SquaresInCircles.Eight.OrdinaryPositiveEnvelope
