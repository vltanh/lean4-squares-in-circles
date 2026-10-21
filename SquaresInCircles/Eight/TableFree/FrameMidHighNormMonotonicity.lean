module

public import SquaresInCircles.Eight.TableFree.FrameMidMidScalars

/-!
# One derivative inequality for the entire middle/high multiplier range

The middle/middle half-angle polynomial extends from `L = .87` to every
`L ∈ [.8,.87]` by one expansion in `.87-L`.  The four coefficients are
bounded on the complete half-angle interval, without choosing an angle
cell or replaying a coefficient certificate.  The final theorem concerns
the derivative of the actual circular norm, with its positive sign kept
when the comparison is squared.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighNormMonotonicity
open FramePair FrameCircleArc FrameMidArc FramePairCalculus

abbrev D := FrameCoreMidFullCircle.D
abbrev S := FrameCoreMidFullCircle.S
abbrev C := FrameCoreMidFullCircle.C

def NF (L x : ℝ) : ℝ :=
  CircularNorm.norm (p^2+q^2+L^2) (-2*L*q) (2*L*p) x
def NFd (L x : ℝ) : ℝ := L*(p*Real.cos x+q*Real.sin x)/NF L x
def F (L x : ℝ) : ℝ :=
  x+(L-9/100)*Real.sin x-(9/100)*Real.cos x-R*NF L x
def Fd (L x : ℝ) : ℝ :=
  1+(L-9/100)*Real.cos x+(9/100)*Real.sin x-R*NFd L x

def E (L z : ℝ) : ℝ :=
  (p^2+q^2+L^2)*D z+2*L*(p*S z-q*C z)
def J (L z : ℝ) : ℝ := D z+(L-9/100)*C z+(9/100)*S z
def P (L z : ℝ) : ℝ :=
  (J L z)^2*E L z-Q0*L^2*(p*C z+q*S z)^2*D z

def E1 (z : ℝ) : ℝ := -(174/100)*D z-2*(p*S z-q*C z)
def C1 (z : ℝ) : ℝ :=
  (J (87/100) z)^2*E1 z-2*J (87/100) z*C z*E (87/100) z+
    2*Q0*(87/100)*(p*C z+q*S z)^2*D z
def C2 (z : ℝ) : ℝ :=
  (J (87/100) z)^2*D z-2*J (87/100) z*C z*E1 z+
    (C z)^2*E (87/100) z-Q0*(p*C z+q*S z)^2*D z
def C3 (z : ℝ) : ℝ := -2*J (87/100) z*C z*D z+(C z)^2*E1 z
def C4 (z : ℝ) : ℝ := (C z)^2*D z

theorem multiplier_expansion (h z : ℝ) :
    P (87/100-h) z=P (87/100) z+h*C1 z+h^2*C2 z+h^3*C3 z+h^4*C4 z := by
  dsimp [P,J,E,E1,C1,C2,C3,C4]
  ring

theorem coefficient_one {z : ℝ} (hz : 0≤z) :
    9+26*z+12*z^2+6*z^3+77*z^4-60*z^5+18*z^6<C1 z := by
  apply sub_pos.mp
  dsimp [C1,J,E,E1,D,S,C,FrameCoreMidFullCircle.D,
    FrameCoreMidFullCircle.S,FrameCoreMidFullCircle.C,p,q,Q0]
  ring_nf
  positivity

theorem coefficient_two {z : ℝ} (hz : 0≤z) :
    -8-11*z-26*z^3-61*z^4-3*z^6<C2 z := by
  apply sub_pos.mp
  dsimp [C2,J,E,E1,D,S,C,FrameCoreMidFullCircle.D,
    FrameCoreMidFullCircle.S,FrameCoreMidFullCircle.C,p,q,Q0]
  ring_nf
  positivity

theorem coefficient_three {z : ℝ} (hz : 0≤z) :
    -3-7*z-9*z^2-6*z^5-5*z^6<C3 z := by
  apply sub_pos.mp
  dsimp [C3,J,E1,D,S,C,FrameCoreMidFullCircle.D,
    FrameCoreMidFullCircle.S,FrameCoreMidFullCircle.C,p,q]
  ring_nf
  positivity

theorem coefficient_four_nonneg (z : ℝ) : 0≤C4 z := by
  dsimp [C4,D,FrameCoreMidFullCircle.D]
  positivity

theorem coefficient_bounds {z : ℝ} (hz : z∈Icc (1/8:ℝ) (5/8)) :
    9<C1 z ∧ -32<C2 z ∧ -12<C3 z ∧ 0≤C4 z := by
  have hz0 : 0≤z := by linarith [hz.1]
  have hz2 := pow_le_pow_left₀ hz0 hz.2 2
  have hz3 := pow_le_pow_left₀ hz0 hz.2 3
  have hz4 := pow_le_pow_left₀ hz0 hz.2 4
  have hz5 := pow_le_pow_left₀ hz0 hz.2 5
  have hz6 := pow_le_pow_left₀ hz0 hz.2 6
  have hg : 0≤z^4*(77-60*z) :=
    mul_nonneg (pow_nonneg hz0 _) (by linarith [hz.2])
  refine ⟨?_,?_,?_,coefficient_four_nonneg z⟩
  · nlinarith [coefficient_one hz0,pow_nonneg hz0 3,pow_nonneg hz0 6]
  · nlinarith [coefficient_two hz0]
  · nlinarith [coefficient_three hz0]

theorem base_polynomial_positive {z : ℝ} (hz : z∈Icc (1/8:ℝ) (5/8)) :
    0<P (87/100) z := by
  simpa only [P,J,E,FrameMidMidScalars.P,FrameMidMidScalars.J,
    FrameMidMidScalars.E,FrameMidMidGeometry.lambda] using
    FrameMidMidScalars.polynomial_positive hz

theorem polynomial_positive {L z : ℝ}
    (hL : L∈Icc (4/5:ℝ) (87/100)) (hz : z∈Icc (1/8:ℝ) (5/8)) :
    0<P L z := by
  let h : ℝ := 87/100-L
  have hh : h∈Icc (0:ℝ) (7/100) := ⟨by dsimp [h]; linarith [hL.2],
    by dsimp [h]; linarith [hL.1]⟩
  have hc := coefficient_bounds hz
  have h1 := mul_le_mul_of_nonneg_left hc.1.le hh.1
  have h2 := mul_le_mul_of_nonneg_left hc.2.1.le (sq_nonneg h)
  have h3 := mul_le_mul_of_nonneg_left hc.2.2.1.le (pow_nonneg hh.1 3)
  have h4 := mul_nonneg (pow_nonneg hh.1 4) hc.2.2.2
  have hsq := pow_le_pow_left₀ hh.1 hh.2 2
  have hbr : 0<9-32*h-12*h^2 := by nlinarith
  have hrem := mul_nonneg hh.1 hbr.le
  have hex := multiplier_expansion h z
  have he : 87/100-h=L := by dsimp [h]; ring
  rw [he] at hex
  nlinarith [base_polynomial_positive hz]

theorem NF_energy_pos {L x : ℝ} (hL : 0≤L) (hx : x∈Icc 0 (Real.pi/2)) :
    0<CircularNorm.energy (p^2+q^2+L^2) (-2*L*q) (2*L*p) x := by
  have ht := FrameLowPair.quadrant hx
  have hp : 0<p+L*Real.sin x := by
    have hh := mul_nonneg hL ht.1
    dsimp [p]
    linarith
  have he : CircularNorm.energy (p^2+q^2+L^2) (-2*L*q) (2*L*p) x=
      (p+L*Real.sin x)^2+(q-L*Real.cos x)^2 := by
    dsimp [CircularNorm.energy]
    linear_combination -L^2*(Real.sin_sq_add_cos_sq x)
  rw [he]
  nlinarith [sq_pos_of_pos hp,sq_nonneg (q-L*Real.cos x)]

theorem NF_pos {L x : ℝ} (hL : 0≤L) (hx : x∈Icc 0 (Real.pi/2)) : 0<NF L x :=
  CircularNorm.norm_pos (NF_energy_pos hL hx)

theorem NF_sq {L x : ℝ} (hL : 0≤L) (hx : x∈Icc 0 (Real.pi/2)) :
    (NF L x)^2=p^2+q^2+L^2+2*L*(p*Real.sin x-q*Real.cos x) := by
  have hh := CircularNorm.norm_sq (NF_energy_pos hL hx).le
  convert hh using 1 <;> dsimp [NF,CircularNorm.energy] <;> ring

theorem NF_deriv {L x : ℝ} (hL : 0≤L) (hx : x∈Icc 0 (Real.pi/2)) :
    HasDerivAt (NF L) (NFd L x) x := by
  convert CircularNorm.norm_hasDerivAt (NF_energy_pos hL hx) using 1
  · rfl
  · dsimp [NFd,NF,CircularNorm.d1,CircularNorm.slope]
    ring

theorem F_deriv {L x : ℝ} (hL : 0≤L) (hx : x∈Icc 0 (Real.pi/2)) :
    HasDerivAt (F L) (Fd L x) x := by
  convert (((hasDerivAt_id x).add
    ((Real.hasDerivAt_sin x).const_mul (L-9/100))).sub
    ((Real.hasDerivAt_cos x).const_mul (9/100))).sub ((NF_deriv hL hx).const_mul R)
    using 1 <;> dsimp [F,Fd] <;> ring

theorem half_angle_domain {x : ℝ} (hx : x∈Icc (21/50:ℝ) (93/100)) :
    ∃z∈Icc (1/8:ℝ) (5/8), D z*Real.sin x=S z ∧ D z*Real.cos x=C z := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  obtain ⟨z,hz,hs,hc⟩ := FrameCoreMidFullCircle.half_angle hxq
  have hD : D z≠0 := by dsimp [D,FrameCoreMidFullCircle.D]; positivity
  have hid : z*(1+Real.cos x)=Real.sin x := by
    apply (mul_left_cancel₀ hD)
    dsimp [D,S,C,FrameCoreMidFullCircle.D,FrameCoreMidFullCircle.S,
      FrameCoreMidFullCircle.C] at hs hc ⊢
    nlinarith
  have hsl := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(21/50:ℝ)) hxq.2 hx.1
  have hsu := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos] : -(Real.pi/2)≤x)
    (by linarith [FrameLowPair.pi_lower] : (93/100:ℝ)≤Real.pi/2) hx.2
  have hcl := Real.cos_le_cos_of_nonneg_of_le_pi hxq.1
    (by linarith [FrameLowPair.pi_lower] : (93/100:ℝ)≤Real.pi) hx.2
  have hsL := Real.sin_ge_sub_cube (show (0:ℝ)≤21/50 by norm_num)
  have hsU := sin_upper_five (show (0:ℝ)≤93/100 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤93/100 by norm_num)
  norm_num at hsL hsU hcL
  have hsinL : (2/5:ℝ)<Real.sin x := by linarith
  have hsinU : Real.sin x<(81/100:ℝ) := by linarith
  have hcosL : (59/100:ℝ)<Real.cos x := by linarith
  refine ⟨z,⟨?_,?_⟩,hs,hc⟩
  · have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hz.1
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hcosL.le hz.1
    nlinarith

theorem Fd_positive {L x : ℝ} (hL : L∈Icc (4/5:ℝ) (87/100))
    (hx : x∈Icc (21/50:ℝ) (93/100)) : 0<Fd L x := by
  have hL0 : 0≤L := by linarith [hL.1]
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  obtain ⟨z,hz,hs,hc⟩ := half_angle_domain hx
  have hD : 0<D z := by dsimp [D,FrameCoreMidFullCircle.D]; positivity
  have hn := NF_pos hL0 hxq
  have hN2 := NF_sq hL0 hxq
  have ht := FrameLowPair.quadrant hxq
  let a : ℝ := 1+(L-9/100)*Real.cos x+(9/100)*Real.sin x
  have ha : 0<a := by
    have hp := mul_nonneg (show 0≤L-9/100 by linarith [hL.1]) ht.2.2.1
    dsimp [a]
    nlinarith [ht.1]
  have hE : E L z=D z*(NF L x)^2 := by
    dsimp [E]
    rw [← hs,← hc,hN2]
    ring
  have hJ : J L z=D z*a := by dsimp [J,a]; rw [← hs,← hc]; ring
  have hP : P L z=(D z)^3*
      (a^2*(NF L x)^2-Q0*L^2*(p*Real.cos x+q*Real.sin x)^2) := by
    dsimp [P]
    rw [hE,hJ,← hs,← hc]
    ring
  have hdelta : 0<a^2*(NF L x)^2-Q0*L^2*(p*Real.cos x+q*Real.sin x)^2 := by
    have hh := polynomial_positive hL hz
    rw [hP] at hh
    exact (mul_pos_iff_of_pos_left (pow_pos hD 3)).mp hh
  have hforce : 0≤R*L*(p*Real.cos x+q*Real.sin x) := by
    apply mul_nonneg (mul_nonneg R_pos.le hL0)
    exact add_nonneg (mul_nonneg (by norm_num [p]) ht.2.2.1)
      (mul_nonneg (by norm_num [q]) ht.1)
  have hsq : (R*L*(p*Real.cos x+q*Real.sin x))^2=
      Q0*L^2*(p*Real.cos x+q*Real.sin x)^2 := by rw [mul_pow,mul_pow,R_sq]
  have hlt : R*L*(p*Real.cos x+q*Real.sin x)<a*NF L x := by
    nlinarith [mul_pos ha hn]
  have hdiv := (div_lt_iff₀ hn).2 hlt
  dsimp [Fd,NFd,a]
  have he : R*(L*(p*Real.cos x+q*Real.sin x)/NF L x)=
      R*L*(p*Real.cos x+q*Real.sin x)/NF L x := by ring
  rw [he]
  linarith

theorem F_monotone {L : ℝ} (hL : L∈Icc (4/5:ℝ) (87/100)) :
    MonotoneOn (F L) (Icc (21/50:ℝ) (93/100)) := by
  have hL0 : 0≤L := by linarith [hL.1]
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact (F_deriv hL0 ⟨by linarith [hx.1],
      by linarith [hx.2,FrameLowPair.pi_lower]⟩).continuousAt.continuousWithinAt
  · intro x hx
    exact F_deriv hL0 ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  · intro x hx
    exact (Fd_positive hL (Ioo_subset_Icc_self hx)).le

theorem add_constant_monotone {L : ℝ} (hL : L∈Icc (4/5:ℝ) (87/100)) (K : ℝ) :
    MonotoneOn (fun x => F L x+K) (Icc (21/50:ℝ) (93/100)) := by
  intro x hx y hy hxy
  exact add_le_add_right (F_monotone hL hx hy hxy) K

end SquaresInCircles.Eight.TableFree.FrameMidHighNormMonotonicity
