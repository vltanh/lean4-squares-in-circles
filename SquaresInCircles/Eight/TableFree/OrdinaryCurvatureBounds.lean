module

public import SquaresInCircles.Eight.TableFree.PairNormCalculus

/-!
# Uniform ordinary-force curvature constants

Uncompiled source draft of the four estimates (25)--(26) in
HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md. The coefficient ratio
varies on its entire interval. Two extrema follow from polynomial
identities and two from monotonicity with explicit derivatives. The only
substitutions are the proved intrinsic coefficient endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.OrdinaryCurvatureBounds
open PositiveAngularEnvelope PairNormCalculus

def shape (r : ℝ) : ℝ := Real.sqrt (1+r^2)
def shapeC0p (R r : ℝ) : ℝ := R*r/(shape r)^3
def shapeC1p (R r : ℝ) : ℝ := R*(1-r^2+r^4)/(shape r)^5
def shapeC0q (R r : ℝ) : ℝ := R*r^2/(shape r)^3
def shapeCSq (R r : ℝ) : ℝ :=
  R*(r^2+r^4+frameCap*(r-r^3+r^5))/(shape r)^5

theorem shape_pos (r : ℝ) : 0<shape r := Real.sqrt_pos.mpr (by positivity)
theorem shape_sq (r : ℝ) : (shape r)^2=1+r^2 := Real.sq_sqrt (by positivity)

theorem shape_power_reduce (r : ℝ) (n : ℕ) :
    (shape r)^(n+2)=(shape r)^n*(1+r^2) := by
  rw [pow_add,shape_sq]

theorem shape_hasDerivAt (r : ℝ) : HasDerivAt shape (r/shape r) r := by
  have h := ((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).pow 2)).sqrt
    (show 1+r^2≠0 by positivity)
  convert h using 1
  · rfl
  · dsimp [shape]
    ring

theorem shapeC1p_hasDerivAt (R r : ℝ) :
    HasDerivAt (shapeC1p R)
      (R*r*(-7+7*r^2-r^4)/(shape r)^7) r := by
  have hn := shape_hasDerivAt r
  have hnum := (((hasDerivAt_const r (1:ℝ)).sub
    ((hasDerivAt_id r).pow 2)).add ((hasDerivAt_id r).pow 4)).const_mul R
  have hraw := hnum.div (hn.pow 5) (pow_ne_zero 5 (shape_pos r).ne')
  have hpow := shape_power_reduce r
  convert hraw using 1
  · rfl
  · field_simp [(shape_pos r).ne']
    ring_nf
    simp only [hpow 0,hpow 1,hpow 2,hpow 3,hpow 4,hpow 5,hpow 6,
      hpow 7,hpow 8,hpow 9,hpow 10,hpow 11,hpow 12,pow_zero,pow_one]
    ring

theorem shapeCSq_hasDerivAt (R r : ℝ) :
    HasDerivAt (shapeCSq R)
      (R*(2*r+r^3-r^5+frameCap*(1-7*r^2+7*r^4))/(shape r)^7) r := by
  have hn := shape_hasDerivAt r
  have hbase := ((hasDerivAt_id r).pow 2).add ((hasDerivAt_id r).pow 4)
  have hodd := ((hasDerivAt_id r).sub ((hasDerivAt_id r).pow 3)).add
    ((hasDerivAt_id r).pow 5)
  have hraw := ((hbase.add (hodd.const_mul frameCap)).const_mul R).div
    (hn.pow 5) (pow_ne_zero 5 (shape_pos r).ne')
  have hpow := shape_power_reduce r
  convert hraw using 1
  · rfl
  · field_simp [(shape_pos r).ne']
    ring_nf
    simp only [hpow 0,hpow 1,hpow 2,hpow 3,hpow 4,hpow 5,hpow 6,
      hpow 7,hpow 8,hpow 9,hpow 10,hpow 11,hpow 12,pow_zero,pow_one]
    ring

theorem shapeC1p_antitone {R : ℝ} (hR : 0≤R) :
    AntitoneOn (shapeC1p R) (Icc (1/2) 1) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun r _ => (shapeC1p_hasDerivAt R r).continuousAt.continuousWithinAt
  · exact fun r _ => shapeC1p_hasDerivAt R r
  · intro r hr
    have hr0 : 0≤r := by linarith [hr.1]
    have hr2 : r^2≤1 := by
      simpa using pow_le_pow_left₀ hr0 hr.2.le 2
    have hp : -7+7*r^2-r^4≤0 := by nlinarith [sq_nonneg (r^2)]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hR hr0) hp)
      (pow_nonneg (shape_pos r).le 7)

theorem shapeCSq_monotone {R : ℝ} (hR : 0≤R) :
    MonotoneOn (shapeCSq R) (Icc (1/2) 1) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun r _ => (shapeCSq_hasDerivAt R r).continuousAt.continuousWithinAt
  · exact fun r _ => shapeCSq_hasDerivAt R r
  · intro r hr
    have hr0 : 0≤r := by linarith [hr.1]
    have hr2 : r^2≤1 := by
      simpa using pow_le_pow_left₀ hr0 hr.2.le 2
    have hodd : 0≤r^3*(1-r^2) :=
      mul_nonneg (pow_nonneg hr0 3) (sub_nonneg.mpr hr2)
    have hp : 0≤2*r+r^3-r^5+frameCap*(1-7*r^2+7*r^4) := by
      dsimp [frameCap]
      nlinarith [sq_nonneg (r^2-1/2),hr.1]
    exact div_nonneg (mul_nonneg hR hp) (pow_nonneg (shape_pos r).le 7)

theorem quotient_lt_of_square {x y c : ℝ} (hy : 0<y) (hc : 0<c)
    (hsq : x^2<c^2*y^2) : x/y<c := by
  by_contra! h
  have hh : c*y≤x := (le_div_iff₀ hy).1 h
  have hsq' := pow_le_pow_left₀ (mul_nonneg hc.le hy.le) hh 2
  nlinarith

/-- The maximum of `r/(1+r²)^(3/2)` follows from one sum of squares. -/
theorem shapeC0p_lt {R r : ℝ} (hQ : R^2≤qCap) :
    shapeC0p R r<381/500 := by
  have hn := shape_pos r
  have hid : 4*(shape r)^6-27*r^2=(2*r^2-1)^2*(r^2+4) := by
    calc
      4*(shape r)^6-27*r^2=4*((shape r)^2)^3-27*r^2 := by ring
      _=(2*r^2-1)^2*(r^2+4) := by rw [shape_sq]; ring
  have hsos : 27*r^2≤4*(shape r)^6 := by
    have hpos : 0≤(2*r^2-1)^2*(r^2+4) := by positivity
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hsos
    (show 0≤qCap/27 by norm_num [qCap])
  have hRscaled := mul_le_mul_of_nonneg_right hQ (sq_nonneg r)
  have hreserve := mul_pos
    (show (0:ℝ)<(381/500 : ℝ)^2-4*qCap/27 by norm_num [qCap]) (pow_pos hn 6)
  unfold shapeC0p
  apply quotient_lt_of_square (pow_pos hn 3) (by norm_num)
  nlinarith

theorem shapeC0q_lt {R r : ℝ} (hQ : R^2≤qCap) (hr : r∈Icc (1/2) 1) :
    shapeC0q R r<7/10 := by
  have hr0 : 0≤r := by linarith [hr.1]
  have hr2 : r^2≤1 := by simpa using pow_le_pow_left₀ hr0 hr.2 2
  have hr4 : r^4≤1 := by simpa using pow_le_pow_left₀ hr0 hr.2 4
  have hpos : 0≤(1-r^2)*(1+4*r^2-r^4) :=
    mul_nonneg (by linarith) (by nlinarith [sq_nonneg r])
  have hid : (shape r)^6-8*r^4=(1-r^2)*(1+4*r^2-r^4) := by
    calc
      (shape r)^6-8*r^4=((shape r)^2)^3-8*r^4 := by ring
      _=(1-r^2)*(1+4*r^2-r^4) := by rw [shape_sq]; ring
  have hsos : 8*r^4≤(shape r)^6 := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hsos
    (show 0≤qCap/8 by norm_num [qCap])
  have hRscaled := mul_le_mul_of_nonneg_right hQ (pow_nonneg hr0 4)
  have hreserve := mul_pos
    (show (0:ℝ)<(7/10 : ℝ)^2-qCap/8 by norm_num [qCap]) (pow_pos (shape_pos r) 6)
  unfold shapeC0q
  apply quotient_lt_of_square (pow_pos (shape_pos r) 3) (by norm_num)
  nlinarith

theorem shapeC1p_left_lt {R : ℝ} (hQ : R^2≤qCap) :
    shapeC1p R (1/2)<921/1000 := by
  have hden : ((shape (1/2))^5)^2=(5/4 : ℝ)^5 := by
    calc
      ((shape (1/2))^5)^2=((shape (1/2))^2)^5 := by ring
      _=(5/4 : ℝ)^5 := by rw [shape_sq]; norm_num
  have hs : (R*(13/16 : ℝ))^2<(921/1000 : ℝ)^2*((shape (1/2))^5)^2 := by
    rw [hden]
    norm_num [qCap] at hQ ⊢
    nlinarith
  have h := quotient_lt_of_square (pow_pos (shape_pos (1/2)) 5)
    (show (0:ℝ)<921/1000 by norm_num) hs
  convert h using 1 <;> norm_num [shapeC1p] <;> ring

theorem shapeCSq_right_lt {R : ℝ} (hQ : R^2≤qCap) :
    shapeCSq R 1<189/200 := by
  have hden : ((shape 1)^5)^2=32 := by
    calc
      ((shape 1)^5)^2=((shape 1)^2)^5 := by ring
      _=32 := by rw [shape_sq]; norm_num
  have hs : (R*(27/10 : ℝ))^2<(189/200 : ℝ)^2*((shape 1)^5)^2 := by
    rw [hden]
    norm_num [qCap] at hQ ⊢
    nlinarith
  have h := quotient_lt_of_square (pow_pos (shape_pos 1) 5)
    (show (0:ℝ)<189/200 by norm_num) hs
  convert h using 1 <;> norm_num [shapeCSq,frameCap] <;> ring

theorem shapeC1p_lt {R r : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hr : r∈Icc (1/2) 1) : shapeC1p R r<921/1000 :=
  (shapeC1p_antitone hR (by constructor <;> norm_num) hr hr.1).trans_lt
    (shapeC1p_left_lt hQ)

theorem shapeCSq_lt {R r : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hr : r∈Icc (1/2) 1) : shapeCSq R r<189/200 :=
  (shapeCSq_monotone hR hr (by constructor <;> norm_num) hr.2).trans_lt
    (shapeCSq_right_lt hQ)

/-- Exact homogeneity, before any coefficient bound is applied. -/
theorem curvature_constants_normalize {R p q : ℝ} (hp : 0<p) (hq : 0<q) :
    curvatureZero R p q=p*shapeC0p R (p/q) ∧
    curvatureSlope R p q=p*shapeC1p R (p/q) ∧
    curvatureZero R p q=q*shapeC0q R (p/q) ∧
    curvatureZero R p q+frameCap*curvatureSlope R p q=q*shapeCSq R (p/q) := by
  let r : ℝ := p/q
  change curvatureZero R p q=p*shapeC0p R r ∧
    curvatureSlope R p q=p*shapeC1p R r ∧
    curvatureZero R p q=q*shapeC0q R r ∧
    curvatureZero R p q+frameCap*curvatureSlope R p q=q*shapeCSq R r
  have hpq : p=q*r := by dsimp [r]; field_simp [hq.ne']; ring
  have hN : pairNorm p q 0=q*shape r := by
    rw [pairNorm_zero,hpq]
    have hid : (q*r)^2+q^2=q^2*(1+r^2) := by ring
    rw [hid,Real.sqrt_mul (sq_nonneg q),Real.sqrt_sq hq.le]
    rfl
  have hne := (shape_pos r).ne'
  have hpow := shape_power_reduce r
  constructor
  · dsimp [curvatureZero,shapeC0p,pairProduct]
    rw [hN,hpq]
    field_simp [hq.ne',hne]
    ring
  constructor
  · dsimp [curvatureSlope,shapeC1p,pairProduct,pairEnergy]
    rw [hN,hpq]
    field_simp [hq.ne',hne]
    ring
  constructor
  · dsimp [curvatureZero,shapeC0q,pairProduct]
    rw [hN,hpq]
    field_simp [hq.ne',hne]
    ring
  · dsimp [curvatureZero,curvatureSlope,shapeCSq,pairProduct,pairEnergy]
    rw [hN,hpq]
    field_simp [hq.ne',hne]
    ring_nf
    simp only [hpow 0,hpow 1,hpow 2,hpow 3,hpow 4,hpow 5,hpow 6,
      hpow 7,hpow 8,hpow 9,hpow 10,hpow 11,hpow 12,pow_zero,pow_one]
    ring

/-- The four strict caps hold uniformly in the coefficient ratio and radius. -/
theorem curvature_constant_bounds {R p q : ℝ} (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    curvatureZero R p q<(381/500)*p ∧
    curvatureSlope R p q<(921/1000)*p ∧
    curvatureZero R p q<(7/10)*q ∧
    curvatureZero R p q+frameCap*curvatureSlope R p q<(189/200)*q := by
  have hq : 0<q := hp.trans_le hpq
  have hr : p/q∈Icc (1/2) 1 := by
    constructor
    · exact (le_div_iff₀ hq).2 (by linarith)
    · exact (div_le_one hq).2 hpq
  obtain ⟨h₀p,h₁p,h₀q,hΣq⟩ := curvature_constants_normalize (R := R) hp hq
  refine ⟨?_,?_,?_,?_⟩
  · rw [h₀p]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (shapeC0p_lt hQ) hp
  · rw [h₁p]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (shapeC1p_lt hR hQ hr) hp
  · rw [h₀q]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (shapeC0q_lt hQ hr) hq
  · rw [hΣq]
    simpa [mul_comm] using mul_lt_mul_of_pos_left (shapeCSq_lt hR hQ hr) hq

theorem curvatureSlope_nonneg {R p q : ℝ} (hR : 0≤R) (hp : 0<p) (hq : 0<q) :
    0≤curvatureSlope R p q := by
  have hB : 0≤pairProduct p q := (mul_pos hp hq).le
  have hA := pairEnergy_ge_twice p q
  have hA0 : 0≤pairEnergy p q := by dsimp [pairEnergy]; positivity
  have hpoly : 0≤(pairEnergy p q)^2-3*(pairProduct p q)^2 := by nlinarith
  unfold curvatureSlope
  exact div_nonneg (mul_nonneg (mul_nonneg hR hB) hpoly)
    (pow_nonneg (Real.sqrt_nonneg _) 5)

end SquaresInCircles.Eight.TableFree.OrdinaryCurvatureBounds
