module

public import SquaresInCircles.Eight.Frames.Diagonal.Tails
public import SquaresInCircles.Eight.Frames.Mid.HighVaryingCalculus
public import SquaresInCircles.Eight.Frames.Mid.MidScalars
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts

/-!
# Eight squares: the scalar forms of the middle/high supports

The norm of a circle support in the coordinates of the squares equals its norm in the diagonal
coordinates, by an orthogonal change of coordinates, and its positive square root carries the
common radius `R` (`middle_target_norm`, `varying_source_norm`, `high_target_norm`). So the
scalar forms below are the signed support of the central witness of a middle/high pair: for a
positive source with the multiplier `43/100` (`positive_constant`), for a negative source
(`negative_constant`), with the multiplier `FrameMidHighVaryingCalculus.lam i x` that varies with
the angle (`varying_form`), and for a high target bounded by its circle, before and after the
quarter turn (`high_target_first`, `high_target_second`).
-/

section
/-!
## One derivative inequality for the entire middle/high multiplier range

The middle/middle half-angle polynomial extends from `L = .87` to every
`L ∈ [.8,.87]` by one expansion in `.87-L`.  The four coefficients are
bounded on the complete half-angle interval, without choosing an angle
cell or replaying a coefficient certificate.  The final theorem concerns
the derivative of the actual circular norm, with its positive sign kept
when the comparison is squared.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighNormMonotonicity
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
  convert hh using 1 <;> dsimp [NF,CircularNorm.energy]
  ring

theorem NF_deriv {L x : ℝ} (hL : 0≤L) (hx : x∈Icc 0 (Real.pi/2)) :
    HasDerivAt (NF L) (NFd L x) x := by
  convert CircularNorm.norm_hasDerivAt (NF_energy_pos hL hx) using 1
  · rfl
  · dsimp [NFd,NF,CircularNorm.d1,CircularNorm.slope]
    ring

theorem F_deriv {L x : ℝ} (hL : 0≤L) (hx : x∈Icc 0 (Real.pi/2)) :
    HasDerivAt (F L) (Fd L x) x := by
  have h := (((hasDerivAt_id x).fun_add
    ((Real.hasDerivAt_sin x).const_mul (L-9/100))).fun_sub
    ((Real.hasDerivAt_cos x).const_mul (9/100:ℝ))).fun_sub ((NF_deriv hL hx).const_mul R)
  rw [show F L=fun y => id y+(L-9/100)*Real.sin y-(9/100)*Real.cos y-R*NF L y from rfl]
  exact h.congr_deriv (by simp only [Fd]; ring)

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
    linear_combination z*hc-hs
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
    linarith
  · have hm := mul_le_mul_of_nonneg_left hcosL.le hz.1
    linarith

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
    apply lt_of_pow_lt_pow_left₀ 2 (mul_pos ha hn).le
    rw [hsq,mul_pow]
    linarith
  have hdiv := (div_lt_iff₀ hn).2 hlt
  dsimp [Fd,NFd,a]
  have he : R*(L*(p*Real.cos x+q*Real.sin x)/NF L x)=
      R*L*(p*Real.cos x+q*Real.sin x)/NF L x := by ring
  rw [he]
  have ha' : a=1+(L-9/100)*Real.cos x+(9/100)*Real.sin x := rfl
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

end SquaresInCircles.Eight.FrameMidHighNormMonotonicity
end
end
end

section
/-!
## The three constant middle/high supports

The common derivative theorem applies to all three doubled multipliers.
Each remaining comparison is at its first geometric endpoint, using
Taylor bounds and positive square comparisons for the actual norm.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighConstantScalars
open FramePair FrameDiagonalArc FrameDiagonalLabels

def P (x : ℝ) : ℝ :=
  9/100+43/100+cM-(43/100)*FrameDiagonalArc.a0+k+FrameMidHighNormMonotonicity.F (43/50) x
def sourceNorm (l : ℝ) : ℝ := Real.sqrt ((l+u)^2+(l-v)^2)
def negativeK (l : ℝ) : ℝ :=
  9/100+2*l+u*R+cM+k-R*sourceNorm l
def N (l x : ℝ) : ℝ := negativeK l+FrameMidHighNormMonotonicity.F (2*l) x

theorem trigonometric_reference {x : ℝ} (hx : 0≤x) :
    HighOrderTaylor.S11 x≤Real.sin x ∧ Real.sin x≤Arithmetic.sin9 x ∧
      Arithmetic.cos10 x≤Real.cos x ∧ Real.cos x≤SecondWord.ReferenceTrig.cos12 x :=
  ⟨HighOrderTaylor.S11_le_sin hx,Arithmetic.sin_le_sin9 hx,
    Arithmetic.cos10_le_cos hx,SecondWord.ReferenceTrig.cos_le_cos12 hx⟩

/-- The two radii are related by their exact squares. This comparison
retains the positive actual norm before eliminating the radical. -/
theorem target_force_upper {L x z : ℝ} (hL : 0≤L)
    (hx : x∈Icc 0 (Real.pi/2)) (hz : 0<z)
    (he : FrameMidArc.p^2+FrameMidArc.q^2+L^2+
      2*L*(FrameMidArc.p*Real.sin x-FrameMidArc.q*Real.cos x)<2*z^2) :
    FrameCircleArc.R*FrameMidHighNormMonotonicity.NF L x<
      (139921407/50000000:ℝ)*z := by
  have hn := FrameMidHighNormMonotonicity.NF_pos hL hx
  have hN2 := FrameMidHighNormMonotonicity.NF_sq hL hx
  have hN : (FrameMidHighNormMonotonicity.NF L x)^2<2*z^2 := by rwa [hN2]
  have hp := mul_lt_mul_of_pos_left hN (show 0<Q0 by norm_num [Q0])
  have hleft : (FrameCircleArc.R*FrameMidHighNormMonotonicity.NF L x)^2=
      Q0*(FrameMidHighNormMonotonicity.NF L x)^2 := by
    rw [mul_pow,FrameCircleArc.R_sq]
  have hright : (R*z)^2=2*Q0*z^2 := by rw [mul_pow,R_sq]
  have hlt : FrameCircleArc.R*FrameMidHighNormMonotonicity.NF L x<R*z := by
    nlinarith [mul_pos FrameCircleArc.R_pos hn,mul_pos R_pos hz]
  exact hlt.trans (mul_lt_mul_of_pos_right R_precise.2 hz)

theorem positive_reference : (8951/10000:ℝ)<P (21/50) := by
  have ht := trigonometric_reference (show (0:ℝ)≤21/50 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  have he : FrameMidArc.p^2+FrameMidArc.q^2+(43/50:ℝ)^2+
      2*(43/50)*(FrameMidArc.p*Real.sin (21/50)-FrameMidArc.q*Real.cos (21/50))<
        2*(28349773/20000000:ℝ)^2 := by
    dsimp [FrameMidArc.p,FrameMidArc.q]
    nlinarith
  have hforce := target_force_upper (by norm_num : (0:ℝ)≤43/50)
    (show (21/50:ℝ)∈Icc 0 (Real.pi/2) from
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩)
    (by norm_num : (0:ℝ)<28349773/20000000) he
  dsimp [P,FrameMidHighNormMonotonicity.F,cM,k]
  linarith [Arithmetic.pi_hand_enclosure.1,a0_precise.2]

theorem source_norm_positive {l : ℝ} (hl : 0≤l) : 0<sourceNorm l := by
  apply Real.sqrt_pos.mpr
  have hp : 0<l+u := by dsimp [u]; linarith
  nlinarith [sq_pos_of_pos hp,sq_nonneg (l-v)]

theorem source_norm_sq (l : ℝ) : (sourceNorm l)^2=(l+u)^2+(l-v)^2 :=
  Real.sq_sqrt (by positivity)

theorem source_force_upper {l z : ℝ} (hl : 0≤l) (hz : 0<z)
    (he : (l+u)^2+(l-v)^2<z^2) :
    R*sourceNorm l<(139921407/50000000:ℝ)*z := by
  have hn := source_norm_positive hl
  have hs := source_norm_sq l
  have hnorm : sourceNorm l<z := by nlinarith
  exact (mul_lt_mul_of_pos_left hnorm R_pos).trans
    (mul_lt_mul_of_pos_right R_precise.2 hz)

theorem negative_middle_reference : (2233/2500:ℝ)<N (21/50) (3/5) := by
  have ht := trigonometric_reference (show (0:ℝ)≤3/5 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  have he : FrameMidArc.p^2+FrameMidArc.q^2+(21/25:ℝ)^2+
      2*(21/25)*(FrameMidArc.p*Real.sin (3/5)-FrameMidArc.q*Real.cos (3/5))<
        2*(152373423/100000000:ℝ)^2 := by
    dsimp [FrameMidArc.p,FrameMidArc.q]
    nlinarith
  have htarget := target_force_upper (by norm_num : (0:ℝ)≤21/25)
    (show (3/5:ℝ)∈Icc 0 (Real.pi/2) from
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩)
    (by norm_num : (0:ℝ)<152373423/100000000) he
  have hsource := source_force_upper (l := (21/50:ℝ)) (z := (51283613/100000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [u,v])
  dsimp [N,negativeK,FrameMidHighNormMonotonicity.F,cM,k,u]
  norm_num only at htarget ⊢
  linarith [Arithmetic.pi_hand_enclosure.1,R_precise.1]

theorem negative_last_reference : (1123/1250:ℝ)<N (2/5) (7/10) := by
  have ht := trigonometric_reference (show (0:ℝ)≤7/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  have he : FrameMidArc.p^2+FrameMidArc.q^2+(4/5:ℝ)^2+
      2*(4/5)*(FrameMidArc.p*Real.sin (7/10)-FrameMidArc.q*Real.cos (7/10))<
        2*(15744183/10000000:ℝ)^2 := by
    dsimp [FrameMidArc.p,FrameMidArc.q]
    nlinarith
  have htarget := target_force_upper (by norm_num : (0:ℝ)≤4/5)
    (show (7/10:ℝ)∈Icc 0 (Real.pi/2) from
      ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩)
    (by norm_num : (0:ℝ)<15744183/10000000) he
  have hsource := source_force_upper (l := (2/5:ℝ)) (z := (9916377/20000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [u,v])
  dsimp [N,negativeK,FrameMidHighNormMonotonicity.F,cM,k,u]
  norm_num only at htarget ⊢
  linarith [Arithmetic.pi_hand_enclosure.1,R_precise.1]

theorem positive_lower {x : ℝ} (hx : x∈Icc (21/50:ℝ) (61/100)) :
    (4463/5000:ℝ)<P x := by
  have hh := FrameMidHighNormMonotonicity.F_monotone
    (L := (43/50:ℝ)) (by constructor <;> norm_num)
    (show (21/50:ℝ)∈Icc (21/50:ℝ) (93/100) by constructor <;> norm_num)
    (show x∈Icc (21/50:ℝ) (93/100) from ⟨hx.1,by linarith [hx.2]⟩) hx.1
  have hP : P (21/50)≤P x := by dsimp [P]; linarith
  linarith [positive_reference]

theorem negative_middle_lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (7/10)) :
    (4463/5000:ℝ)<N (21/50) x := by
  have hh := FrameMidHighNormMonotonicity.F_monotone
    (L := (21/25:ℝ)) (by constructor <;> norm_num)
    (show (3/5:ℝ)∈Icc (21/50:ℝ) (93/100) by constructor <;> norm_num)
    (show x∈Icc (21/50:ℝ) (93/100) from ⟨by linarith [hx.1],by linarith [hx.2]⟩) hx.1
  have hN : N (21/50) (3/5)≤N (21/50) x := by dsimp [N]; norm_num only; linarith
  linarith [negative_middle_reference]

theorem negative_last_lower {x : ℝ} (hx : x∈Icc (7/10:ℝ) (93/100)) :
    (4463/5000:ℝ)<N (2/5) x := by
  have hh := FrameMidHighNormMonotonicity.F_monotone
    (L := (4/5:ℝ)) (by constructor <;> norm_num)
    (show (7/10:ℝ)∈Icc (21/50:ℝ) (93/100) by constructor <;> norm_num)
    (show x∈Icc (21/50:ℝ) (93/100) from ⟨by linarith [hx.1],hx.2⟩) hx.1
  have hN : N (2/5) (7/10)≤N (2/5) x := by dsimp [N]; norm_num only; linarith
  linarith [negative_last_reference]

end SquaresInCircles.Eight.FrameMidHighConstantScalars
end
end
end

section
/-!
## Whole-interval curvature of the target-high circular support

The exact norm has a positive energy and a squared discriminant.  Its
universal lower curvature bound proves concavity before the quarter turn;
after the quarter turn its actual derivative is bounded directly.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighTargetCalculus
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels

def Allowed (l : ℝ) : Prop := l=7/20 ∨ l=2/5
def energyA (l : ℝ) : ℝ := u^2+v^2+2*l^2
def energyB (j : Bool) (l : ℝ) : ℝ := -2*l*(sign j*u+v)
def energyC (j : Bool) (l : ℝ) : ℝ := 2*l*(sign j*u-v)
def N (j : Bool) (l x : ℝ) : ℝ := CircularNorm.norm (energyA l) (energyB j l) (energyC j l) x
def N1 (j : Bool) (l x : ℝ) : ℝ := CircularNorm.d1 (energyA l) (energyB j l) (energyC j l) x
def N2 (j : Bool) (l x : ℝ) : ℝ := CircularNorm.d2 (energyA l) (energyB j l) (energyC j l) x
def K (i j : Bool) (l : ℝ) : ℝ :=
  9/100+l+sign i*cM+sign j*u*R+(-sign i*k-l)*a1+sign i*(q-l)*b1
def F (i j : Bool) (l x : ℝ) : ℝ :=
  K i j l+x+(2*l-9/100)*Real.sin x-(9/100)*Real.cos x-R*N j l x
def Fd (j : Bool) (l x : ℝ) : ℝ :=
  1+(2*l-9/100)*Real.cos x+(9/100)*Real.sin x-R*N1 j l x
def Fdd (j : Bool) (l x : ℝ) : ℝ :=
  -(2*l-9/100)*Real.sin x+(9/100)*Real.cos x-R*N2 j l x
def after (i j : Bool) (l x : ℝ) : ℝ :=
  K i j l+x+(2*l-9/100)*(Real.sin x-Real.cos x)-R*N j l x
def afterD (j : Bool) (l x : ℝ) : ℝ :=
  1+(2*l-9/100)*(Real.cos x+Real.sin x)-R*N1 j l x

theorem allowed_bounds {l : ℝ} (hl : Allowed l) : 0<l ∧ 9/100<2*l := by
  rcases hl with rfl | rfl <;> norm_num

theorem determinant (j : Bool) (l : ℝ) :
    (energyA l)^2-(energyB j l)^2-(energyC j l)^2=(u^2+v^2-2*l^2)^2 := by
  cases j <;> dsimp [energyA,energyB,energyC,sign] <;> ring

theorem coefficient_strict {j : Bool} {l : ℝ} (hl : Allowed l) :
    (energyB j l)^2+(energyC j l)^2<(energyA l)^2 := by
  have hh := determinant j l
  have hp : 0<(u^2+v^2-2*l^2)^2 := by
    rcases hl with rfl | rfl <;> norm_num [u,v]
  linarith

theorem energy_pos {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    0<CircularNorm.energy (energyA l) (energyB j l) (energyC j l) x := by
  have hA : 0<energyA l := by dsimp [energyA,u,v]; positivity
  have hid : (energyB j l*Real.cos x+energyC j l*Real.sin x)^2+
      (energyB j l*Real.sin x-energyC j l*Real.cos x)^2=
        (energyB j l)^2+(energyC j l)^2 := by
    linear_combination ((energyB j l)^2+(energyC j l)^2)*(Real.sin_sq_add_cos_sq x)
  have hc := coefficient_strict (j := j) hl
  dsimp [CircularNorm.energy]
  nlinarith [sq_nonneg (energyB j l*Real.sin x-energyC j l*Real.cos x)]

theorem N_pos {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) : 0<N j l x :=
  CircularNorm.norm_pos (energy_pos hl x)

theorem N_sq {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    (N j l x)^2=energyA l+energyB j l*Real.cos x+energyC j l*Real.sin x :=
  CircularNorm.norm_sq (energy_pos hl x).le

theorem N_circle {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    (N j l x)^2=(sign j*u+l*(Real.sin x-Real.cos x))^2+
      (l*(Real.sin x+Real.cos x)-v)^2 := by
  rw [N_sq hl]
  cases j <;> dsimp [energyA,energyB,energyC,sign] <;>
    linear_combination -2*l^2*(Real.sin_sq_add_cos_sq x)

theorem N_literal {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    N j l x=Real.sqrt ((sign j*u+l*(Real.sin x-Real.cos x))^2+
      (l*(Real.sin x+Real.cos x)-v)^2) := by
  rw [← N_circle hl x,Real.sqrt_sq (N_pos hl x).le]

theorem N_deriv {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (N j l) (N1 j l x) x := CircularNorm.norm_hasDerivAt (energy_pos hl x)

theorem N1_deriv {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (N1 j l) (N2 j l x) x := CircularNorm.d1_hasDerivAt (energy_pos hl x)

theorem norm_curvature {j : Bool} {l : ℝ} (hl : Allowed l) (x : ℝ) :
    -N j l x/4≤N2 j l x :=
  CircularNorm.curvature_lower (energy_pos hl x) (coefficient_strict hl).le

theorem N1_formula (j : Bool) (l x : ℝ) :
    N1 j l x=l*((sign j*u+v)*Real.sin x-(v-sign j*u)*Real.cos x)/N j l x := by
  dsimp [N1,N,CircularNorm.d1,CircularNorm.slope,energyB,energyC]
  ring

theorem F_deriv (i j : Bool) {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (F i j l) (Fd j l x) x := by
  have h : HasDerivAt (fun y => K i j l+y+(2*l-9/100)*Real.sin y-(9/100)*Real.cos y-R*N j l y)
      (1+(2*l-9/100)*Real.cos x-(9/100)*(-Real.sin x)-R*N1 j l x) x :=
    ((((hasDerivAt_id' x).const_add (K i j l)).add
      ((Real.hasDerivAt_sin x).const_mul (2*l-9/100))).sub
      ((Real.hasDerivAt_cos x).const_mul (9/100))).sub ((N_deriv hl x).const_mul R)
  exact h.congr_deriv (by simp only [Fd]; ring)

theorem Fd_deriv (j : Bool) {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (Fd j l) (Fdd j l x) x := by
  have h : HasDerivAt (fun y => 1+(2*l-9/100)*Real.cos y+(9/100)*Real.sin y-R*N1 j l y)
      ((2*l-9/100)*(-Real.sin x)+(9/100)*Real.cos x-R*N2 j l x) x :=
    ((((Real.hasDerivAt_cos x).const_mul (2*l-9/100)).const_add 1).add
      ((Real.hasDerivAt_sin x).const_mul (9/100))).sub ((N1_deriv hl x).const_mul R)
  exact h.congr_deriv (by simp only [Fdd]; ring)

theorem after_deriv (i j : Bool) {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (after i j l) (afterD j l x) x := by
  have h : HasDerivAt (fun y => K i j l+y+(2*l-9/100)*(Real.sin y-Real.cos y)-R*N j l y)
      (1+(2*l-9/100)*(Real.cos x-(-Real.sin x))-R*N1 j l x) x :=
    (((hasDerivAt_id' x).const_add (K i j l)).add
      (((Real.hasDerivAt_sin x).sub (Real.hasDerivAt_cos x)).const_mul (2*l-9/100))).sub
      ((N_deriv hl x).const_mul R)
  exact h.congr_deriv (by simp only [afterD]; ring)

theorem signed_coefficients (j : Bool) : 0<sign j*u+v ∧ 0<v-sign j*u := by
  cases j <;> norm_num [sign,u,v]

theorem norm_monotone_first {j : Bool} {l a b : ℝ} (hl : Allowed l)
    (ha : 0≤a) (hb : b≤Real.pi/2)
    (hleft : 0≤(sign j*u+v)*Real.sin a-(v-sign j*u)*Real.cos a) :
    MonotoneOn (N j l) (Icc a b) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv hl x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv hl x
  · intro x hx
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤a) (hx.2.le.trans hb) hx.1.le
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha
      (by linarith [hx.2,hb,Real.pi_pos] : x≤Real.pi) hx.1.le
    have hsp := mul_le_mul_of_nonneg_left hs (signed_coefficients j).1.le
    have hcp := mul_le_mul_of_nonneg_left hc (signed_coefficients j).2.le
    rw [N1_formula]
    exact div_nonneg (mul_nonneg (allowed_bounds hl).1.le (by linarith)) (N_pos hl x).le

theorem norm_monotone_second {j : Bool} {l : ℝ} (hl : Allowed l) :
    MonotoneOn (N j l) (Icc (Real.pi/2) Real.pi) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv hl x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv hl x
  · intro x hx
    have ht := second_signs (Ioo_subset_Icc_self hx)
    rw [N1_formula]
    apply div_nonneg _ (N_pos hl x).le
    apply mul_nonneg (allowed_bounds hl).1.le
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos
      (signed_coefficients j).2.le ht.2).trans
      (mul_nonneg (signed_coefficients j).1.le ht.1))

theorem curvature_from_norm {j : Bool} {l a b n x : ℝ} (hl : Allowed l)
    (ha : 0≤a) (hb : b≤Real.pi/2) (hx : x∈Icc a b)
    (hn : N j l x≤n)
    (hreserve : (9/100)*Real.cos a+(139921407/50000000:ℝ)*n/4<
      (2*l-9/100)*Real.sin a) (_hn0 : 0≤n) : Fdd j l x<0 := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤a) (hx.2.trans hb) hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha
    (by linarith [hx.2,hb,Real.pi_pos] : x≤Real.pi) hx.1
  have hsp := mul_le_mul_of_nonneg_left hs (by linarith [(allowed_bounds hl).2] : 0≤2*l-9/100)
  have hnp := mul_le_mul_of_nonneg_left (norm_curvature (j := j) hl x) R_pos.le
  have hR := mul_le_mul R_precise.2.le hn (N_pos hl x).le
    (by norm_num : (0:ℝ)≤139921407/50000000)
  dsimp only [Fdd]
  linarith

theorem positive_norm_bounds {x : ℝ} (hx : x∈Icc (7/10:ℝ) (93/100)) :
    N true (7/20) x<(17/100:ℝ) := by
  have htrigL := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤7/10 by norm_num)
  have htrigU := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤93/100 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at htrigL htrigU
  have hm := norm_monotone_first (j := true) (l := (7/20:ℝ)) (Or.inl rfl)
    (a := (7/10:ℝ)) (b := (93/100:ℝ)) (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) (by norm_num [sign,u,v]; nlinarith)
  have hh := hm hx ⟨by norm_num,le_rfl⟩ hx.2
  have hn := N_pos (j := true) (Or.inl (rfl : (7/20:ℝ)=7/20)) (93/100)
  have hs := N_sq (j := true) (Or.inl (rfl : (7/20:ℝ)=7/20)) (93/100)
  norm_num [energyA,energyB,energyC,sign,u,v] at hs
  have he : N true (7/20) (93/100)<(17/100:ℝ) := by nlinarith
  exact hh.trans_lt he

theorem negative_norm_bounds {x : ℝ} (hx : x∈Icc (6/5:ℝ) (71/50)) :
    N false (2/5) x<(3/10:ℝ) := by
  have htrigL := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤6/5 by norm_num)
  have htrigU := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤71/50 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at htrigL htrigU
  have hm := norm_monotone_first (j := false) (l := (2/5:ℝ)) (Or.inr rfl)
    (a := (6/5:ℝ)) (b := (71/50:ℝ)) (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) (by norm_num [sign,u,v]; nlinarith)
  have hh := hm hx ⟨by norm_num,le_rfl⟩ hx.2
  have hn := N_pos (j := false) (Or.inr (rfl : (2/5:ℝ)=2/5)) (71/50)
  have hs := N_sq (j := false) (Or.inr (rfl : (2/5:ℝ)=2/5)) (71/50)
  norm_num [energyA,energyB,energyC,sign,u,v] at hs
  have he : N false (2/5) (71/50)<(3/10:ℝ) := by nlinarith
  exact hh.trans_lt he

theorem opposite_norm_bounds {x : ℝ} (hx : x∈Icc (13/10:ℝ) (Real.pi/2)) :
    N true (2/5) x<(497/1000:ℝ) := by
  have ht := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤13/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  have hm := norm_monotone_first (j := true) (l := (2/5:ℝ)) (Or.inr rfl)
    (a := (13/10:ℝ)) (b := Real.pi/2) (by norm_num) le_rfl
    (by norm_num [sign,u,v]; nlinarith)
  have hh := hm hx ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ hx.2
  have hn := N_pos (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) (Real.pi/2)
  have hs := N_sq (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) (Real.pi/2)
  norm_num [energyA,energyB,energyC,sign,u,v] at hs
  have he : N true (2/5) (Real.pi/2)<(497/1000:ℝ) := by nlinarith
  exact hh.trans_lt he

theorem positive_concave :
    ConcaveOn ℝ (Icc (7/10:ℝ) (93/100)) (F true true (7/20)) := by
  apply concave_of_deriv2 (fun x _ => F_deriv true true (Or.inl rfl) x)
    (fun x _ => Fd_deriv true (Or.inl rfl) x)
  intro x hx
  have ht := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤7/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  exact (curvature_from_norm (Or.inl rfl) (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) hx (positive_norm_bounds hx).le
    (by nlinarith) (by norm_num)).le

theorem negative_concave :
    ConcaveOn ℝ (Icc (6/5:ℝ) (71/50)) (F false false (2/5)) := by
  apply concave_of_deriv2 (fun x _ => F_deriv false false (Or.inr rfl) x)
    (fun x _ => Fd_deriv false (Or.inr rfl) x)
  intro x hx
  have ht := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤6/5 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  exact (curvature_from_norm (Or.inr rfl) (by norm_num)
    (by linarith [FrameLowPair.pi_lower]) hx (negative_norm_bounds hx).le
    (by nlinarith) (by norm_num)).le

theorem opposite_concave :
    ConcaveOn ℝ (Icc (13/10:ℝ) (Real.pi/2-1/50)) (F false true (2/5)) := by
  apply concave_of_deriv2 (fun x _ => F_deriv false true (Or.inr rfl) x)
    (fun x _ => Fd_deriv true (Or.inr rfl) x)
  intro x hx
  have ht := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤13/10 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at ht
  exact (curvature_from_norm (Or.inr rfl) (by norm_num) (by linarith) hx
    (opposite_norm_bounds ⟨hx.1,by linarith [hx.2]⟩).le
    (by nlinarith) (by norm_num)).le

theorem after_norm_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    (2479/5000:ℝ)<N true (2/5) x := by
  have hn := N_pos (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) (Real.pi/2)
  have hs := N_sq (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) (Real.pi/2)
  norm_num [energyA,energyB,energyC,sign,u,v] at hs
  have he : (2479/5000:ℝ)<N true (2/5) (Real.pi/2) := by nlinarith
  exact he.trans_le (norm_monotone_second (Or.inr rfl)
    ⟨le_rfl,by linarith [Real.pi_pos]⟩
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩ hx.1)

theorem after_cos_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) :
    -(7/50:ℝ)<Real.cos x := by
  let e : ℝ := x-Real.pi/2
  have he : e∈Icc (0:ℝ) (7/50) :=
    ⟨by dsimp [e]; linarith [hx.1],by dsimp [e]; linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩
  have hu : e<(7/50:ℝ) := by dsimp [e]; linarith [hx.2,Arithmetic.pi_hand_enclosure.1]
  have hs := Real.sin_le he.1
  have hxid : x=Real.pi/2+e := by dsimp [e]; ring
  rw [hxid,Real.cos_add]
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,zero_mul,one_mul,zero_sub]
  linarith

theorem after_derivative_positive {x : ℝ}
    (hx : x∈Icc (Real.pi/2) (171/100:ℝ)) : 0<afterD true (2/5) x := by
  have ht := second_signs (show x∈Icc (Real.pi/2) Real.pi from
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩)
  have hsum := FrameDiagonalGeometry.late_sum_lower hx
  have hc := after_cos_lower hx
  have hn := after_norm_lower hx
  let cap : ℝ := (2/5)*((v-u)*(7/50)+u+v)
  have hcap : 0≤cap := by norm_num [cap,u,v]
  have hnum : 0≤(2/5:ℝ)*((u+v)*Real.sin x-(v-u)*Real.cos x) := by
    have h1 := mul_nonneg (show 0≤u+v by norm_num [u,v]) ht.1
    have h2 := mul_nonpos_of_nonneg_of_nonpos (show 0≤v-u by norm_num [u,v]) ht.2
    nlinarith
  have hnumU : (2/5:ℝ)*((u+v)*Real.sin x-(v-u)*Real.cos x)≤cap := by
    dsimp [cap,u,v]
    nlinarith [Real.sin_le_one x]
  have hNpos := N_pos (j := true) (Or.inr (rfl : (2/5:ℝ)=2/5)) x
  have hderiv : N1 true (2/5) x≤cap/(2479/5000:ℝ) := by
    rw [N1_formula]
    simp only [sign,ite_true,one_mul]
    calc
      _ ≤ cap/N true (2/5) x := div_le_div_of_nonneg_right hnumU hNpos.le
      _ ≤ cap/(2479/5000:ℝ) := div_le_div_of_nonneg_left hcap (by norm_num) hn.le
  have hderiv0 : 0≤N1 true (2/5) x := by
    rw [N1_formula]
    simp only [sign,ite_true,one_mul]
    exact div_nonneg hnum hNpos.le
  have hprod := mul_le_mul R_precise.2.le hderiv hderiv0
    (by norm_num : (0:ℝ)≤139921407/50000000)
  have hreserve : (139921407/50000000:ℝ)*(cap/(2479/5000))<1+(71/100)*(17/20) := by
    norm_num [cap,u,v]
  dsimp [afterD]
  nlinarith

theorem after_monotone :
    MonotoneOn (after false true (2/5)) (Icc (Real.pi/2+1/50) (171/100:ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (after_deriv false true (Or.inr rfl) x).continuousAt.continuousWithinAt
  · exact fun x _ => after_deriv false true (Or.inr rfl) x
  · exact fun x hx => (after_derivative_positive
      ⟨by linarith [hx.1],hx.2.le⟩).le

end SquaresInCircles.Eight.FrameMidHighTargetCalculus
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidHighSupportForms
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels
open FrameDiagonalSupport

theorem middle_target_norm {l x : ℝ} (hl : 0≤l) (hx : x∈Icc 0 (Real.pi/2)) :
    R*Real.sqrt ((targetU true false l x)^2+(targetV true false l x)^2)=
      FrameCircleArc.R*FrameMidHighNormMonotonicity.NF (2*l) x := by
  have hN := FrameMidHighNormMonotonicity.NF_sq (by linarith : 0≤2*l) hx
  have hNpos := FrameMidHighNormMonotonicity.NF_pos (by linarith : 0≤2*l) hx
  have he : (FrameMidHighNormMonotonicity.NF (2*l) x)^2=
      2*((targetU true false l x)^2+(targetV true false l x)^2) := by
    rw [hN]
    dsimp [targetU,targetV,primary,transverse,sign,k,q,FrameMidArc.p,FrameMidArc.q]
    linear_combination -4*l^2*(Real.sin_sq_add_cos_sq x)
  have hsq : (R*Real.sqrt ((targetU true false l x)^2+(targetV true false l x)^2))^2=
      (FrameCircleArc.R*FrameMidHighNormMonotonicity.NF (2*l) x)^2 := by
    rw [mul_pow,mul_pow,R_sq,FrameCircleArc.R_sq,Real.sq_sqrt (by positivity),he]
    ring
  have hleft := mul_nonneg R_pos.le
    (Real.sqrt_nonneg ((targetU true false l x)^2+(targetV true false l x)^2))
  have hright := mul_nonneg FrameCircleArc.R_pos.le hNpos.le
  nlinarith

theorem positive_constant {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    base false true true false (43/100) x+source false true (43/100) 0+
      targetCircle true false (43/100) x=FrameMidHighConstantScalars.P x := by
  have hn := middle_target_norm (l := (43/100:ℝ)) (by norm_num) hx
  rw [base_first false true true false (43/100) hx,targetCircle,hn]
  dsimp [source,linear,sourceU,sourceV,targetU,primary,transverse,constant,
    sign,FrameMidHighConstantScalars.P,FrameMidHighNormMonotonicity.F]
  rw [A_zero]
  norm_num only
  ring

theorem negative_constant {l x : ℝ} (hl : 0≤l) (hx : x∈Icc 0 (Real.pi/2)) :
    base false true false false l x+sourceCircle false false l+
      targetCircle true false l x=FrameMidHighConstantScalars.N l x := by
  have hn := middle_target_norm hl hx
  have hs : Real.sqrt ((sourceU false false l)^2+(sourceV false false l)^2)=
      FrameMidHighConstantScalars.sourceNorm l := by
    dsimp [sourceU,sourceV,primary,transverse,sign,FrameMidHighConstantScalars.sourceNorm]
    congr 1
    ring
  rw [base_first false true false false l hx,targetCircle,hn,sourceCircle,hs]
  dsimp [sourceU,targetU,primary,transverse,constant,sign,FrameDiagonalArc.a0,
    FrameMidHighConstantScalars.N,FrameMidHighConstantScalars.negativeK,
    FrameMidHighNormMonotonicity.F]
  ring

theorem varying_source_norm (i : Bool) (x : ℝ) :
    Real.sqrt ((sourceU false i (FrameMidHighVaryingCalculus.lam i x))^2+
      (sourceV false i (FrameMidHighVaryingCalculus.lam i x))^2)=
        FrameMidHighVaryingCalculus.N i x := by
  dsimp [FrameMidHighVaryingCalculus.N]
  congr 1
  cases i <;> dsimp [sourceU,sourceV,primary,transverse,sign] <;> ring

theorem varying_form (i : Bool) {x : ℝ}
    (hx : x∈FrameMidHighVaryingCalculus.domain i) :
    base false true i false (FrameMidHighVaryingCalculus.lam i x) x+
      sourceCircle false i (FrameMidHighVaryingCalculus.lam i x)+
      target true false (FrameMidHighVaryingCalculus.lam i x) x b2=
        FrameMidHighVaryingCalculus.F i x := by
  rw [fixed_target_first false true i false (FrameMidHighVaryingCalculus.lam i x)
    b2 (sourceCircle false i (FrameMidHighVaryingCalculus.lam i x))
    (FrameMidHighVaryingCalculus.domain_quadrant hx)]
  rw [sourceCircle,varying_source_norm,A_b2]
  dsimp [FrameMidHighVaryingCalculus.F,FrameMidHighVaryingCalculus.X,
    FrameMidHighVaryingCalculus.Y,M2,constant,marker,sourceU,primary,sign,FrameDiagonalArc.a0]
  cases i <;> dsimp [sign] <;> ring

theorem high_target_norm (j : Bool) {l : ℝ}
    (hl : FrameMidHighTargetCalculus.Allowed l) (x : ℝ) :
    Real.sqrt ((targetU false j l x)^2+(targetV false j l x)^2)=
      FrameMidHighTargetCalculus.N j l x := by
  rw [FrameMidHighTargetCalculus.N_literal hl x]
  congr 1
  cases j <;> dsimp [targetU,targetV,primary,transverse,sign] <;> ring

theorem high_target_first (i j : Bool) {l x : ℝ}
    (hl : FrameMidHighTargetCalculus.Allowed l) (hx : x∈Icc 0 (Real.pi/2)) :
    base true false i j l x+source true i l b1+targetCircle false j l x=
      FrameMidHighTargetCalculus.F i j l x := by
  rw [base_first true false i j l hx,targetCircle,high_target_norm j hl x]
  dsimp [source,linear]
  rw [A_b1]
  dsimp [sourceU,sourceV,targetU,primary,transverse,constant,FrameDiagonalArc.a0,
    FrameMidHighTargetCalculus.F,FrameMidHighTargetCalculus.K]
  ring

theorem high_target_second (i j : Bool) {l x : ℝ}
    (hl : FrameMidHighTargetCalculus.Allowed l) (hx : x∈Icc (Real.pi/2) Real.pi) :
    base true false i j l x+source true i l b1+targetCircle false j l x=
      FrameMidHighTargetCalculus.after i j l x := by
  rw [base_second true false i j l hx,targetCircle,high_target_norm j hl x]
  dsimp [source,linear]
  rw [A_b1]
  dsimp [sourceU,sourceV,targetU,primary,transverse,constant,FrameDiagonalArc.a0,
    FrameMidHighTargetCalculus.after,FrameMidHighTargetCalculus.K]
  ring

end SquaresInCircles.Eight.FrameMidHighSupportForms
end
end
end
