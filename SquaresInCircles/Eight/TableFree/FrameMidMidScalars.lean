module

public import SquaresInCircles.Eight.TableFree.FrameMidMidGeometry
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# Whole-interval middle/middle scalar supports

The transverse derivative is reduced to one degree-six polynomial and
proved by a centered positive remainder.  The primary support uses the
exact circular-norm curvature identity on its complete physical second
quadrant.  Neither estimate uses a coefficient lookup or an interval mesh.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidMidScalars
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameMidMidGeometry

def NF (x : ℝ) : ℝ :=
  CircularNorm.norm (p^2+q^2+lambda^2) (-2*lambda*q) (2*lambda*p) x
def NFd (x : ℝ) : ℝ := lambda*(p*Real.cos x+q*Real.sin x)/NF x
def F (x : ℝ) : ℝ :=
  x+KF+(lambda-9/100)*Real.sin x-(9/100)*Real.cos x-R*NF x
def Fd (x : ℝ) : ℝ :=
  1+(lambda-9/100)*Real.cos x+(9/100)*Real.sin x-R*NFd x

theorem NF_energy_pos {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    0<CircularNorm.energy (p^2+q^2+lambda^2) (-2*lambda*q) (2*lambda*p) x := by
  have ht := FrameLowPair.quadrant hx
  have hp : 0<p+lambda*Real.sin x := by dsimp [p,lambda]; nlinarith [ht.1]
  have he : CircularNorm.energy (p^2+q^2+lambda^2) (-2*lambda*q) (2*lambda*p) x=
      (p+lambda*Real.sin x)^2+(q-lambda*Real.cos x)^2 := by
    dsimp [CircularNorm.energy]
    linear_combination -lambda^2*(Real.sin_sq_add_cos_sq x)
  rw [he]
  nlinarith [sq_pos_of_pos hp,sq_nonneg (q-lambda*Real.cos x)]

theorem NF_pos {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : 0<NF x :=
  CircularNorm.norm_pos (NF_energy_pos hx)

theorem NF_sq {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    (NF x)^2=p^2+q^2+lambda^2+2*lambda*(p*Real.sin x-q*Real.cos x) := by
  have hh := CircularNorm.norm_sq (NF_energy_pos hx).le
  convert hh using 1 <;> dsimp [NF,CircularNorm.energy] <;> ring

theorem NF_deriv {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : HasDerivAt NF (NFd x) x := by
  convert CircularNorm.norm_hasDerivAt (NF_energy_pos hx) using 1
  · rfl
  · dsimp [NFd,NF,CircularNorm.d1,CircularNorm.slope]
    ring

theorem F_deriv {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : HasDerivAt F (Fd x) x := by
  convert ((((hasDerivAt_id x).add_const KF).add
    ((Real.hasDerivAt_sin x).const_mul (lambda-9/100))).sub
    ((Real.hasDerivAt_cos x).const_mul (9/100))).sub ((NF_deriv hx).const_mul R)
    using 1 <;> dsimp [F,Fd] <;> ring

abbrev D := FrameCoreMidFullCircle.D
abbrev S := FrameCoreMidFullCircle.S
abbrev C := FrameCoreMidFullCircle.C
def E (z : ℝ) : ℝ :=
  (p^2+q^2+lambda^2)*D z+2*lambda*(p*S z-q*C z)
def J (z : ℝ) : ℝ := D z+(lambda-9/100)*C z+(9/100)*S z
def P (z : ℝ) : ℝ :=
  (J z)^2*E z-Q0*lambda^2*(p*C z+q*S z)^2*D z
def lowerP (t : ℝ) : ℝ :=
  3/1000-(17/500)*t+(39/2)*t^2-(201/10)*t^3-15*t^5-(31/5)*t^6

/-- Expanding one fixed polynomial gives a positive remainder for both
signs of the displacement from its single center. -/
theorem polynomial_remainder (i : Bool) {t : ℝ} (ht : 0≤t) :
    lowerP t<P (3/8+sign i*t) := by
  apply sub_pos.mp
  cases i <;>
    dsimp [P,J,E,D,S,C,FrameCoreMidFullCircle.D,FrameCoreMidFullCircle.S,
      FrameCoreMidFullCircle.C,lowerP,p,q,lambda,Q0,sign] <;>
    ring_nf <;> positivity

theorem lowerP_positive {t : ℝ} (ht : t∈Icc (0:ℝ) (1/4)) : 0<lowerP t := by
  have ht3 := pow_le_pow_left₀ ht.1 ht.2 3
  have ht4 := pow_le_pow_left₀ ht.1 ht.2 4
  have hbracket : (14:ℝ)<39/2-(201/10)*t-15*t^3-(31/5)*t^4 := by
    nlinarith [ht.2]
  have hmul := mul_le_mul_of_nonneg_left hbracket.le (sq_nonneg t)
  have hsquare := sq_nonneg (28*t-17/500)
  dsimp [lowerP]
  nlinarith

theorem polynomial_positive {z : ℝ} (hz : z∈Icc (1/8:ℝ) (5/8)) : 0<P z := by
  by_cases hsign : 3/8≤z
  · have ht : z-3/8∈Icc (0:ℝ) (1/4) := ⟨by linarith,by linarith [hz.2]⟩
    have hh := polynomial_remainder true ht.1
    simp only [sign,ite_true,one_mul] at hh
    convert (lowerP_positive ht).trans hh using 1 <;> congr 1 <;> ring
  · have ht : 3/8-z∈Icc (0:ℝ) (1/4) := ⟨by linarith,by linarith [hz.1]⟩
    have hh := polynomial_remainder false ht.1
    simp only [sign,ite_false,neg_one_mul] at hh
    convert (lowerP_positive ht).trans hh using 1 <;> congr 1 <;> ring

theorem half_angle_domain {x : ℝ} (hx : x∈Icc (3/5:ℝ) (109/100)) :
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
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(3/5:ℝ)) hxq.2 hx.1
  have hsu := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos] : -(Real.pi/2)≤x)
    (by linarith [FrameLowPair.pi_lower] : (109/100:ℝ)≤Real.pi/2) hx.2
  have hcl := Real.cos_le_cos_of_nonneg_of_le_pi hxq.1
    (by linarith [FrameLowPair.pi_lower] : (109/100:ℝ)≤Real.pi) hx.2
  have hsL := Real.sin_ge_sub_cube (show (0:ℝ)≤3/5 by norm_num)
  have hsU := sin_upper_five (show (0:ℝ)≤109/100 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤109/100 by norm_num)
  norm_num at hsL hsU hcL
  have hsinL : (14/25:ℝ)<Real.sin x := by linarith
  have hsinU : Real.sin x<(89/100:ℝ) := by linarith
  have hcosL : (23/50:ℝ)<Real.cos x := by linarith
  refine ⟨z,⟨?_,?_⟩,hs,hc⟩
  · have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hz.1
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hcosL.le hz.1
    nlinarith

theorem Fd_positive {x : ℝ} (hx : x∈Icc (3/5:ℝ) (109/100)) : 0<Fd x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  obtain ⟨z,hz,hs,hc⟩ := half_angle_domain hx
  have hD : 0<D z := by dsimp [D,FrameCoreMidFullCircle.D]; positivity
  have hn := NF_pos hxq
  have hN2 := NF_sq hxq
  have ht := FrameLowPair.quadrant hxq
  let a : ℝ := 1+(lambda-9/100)*Real.cos x+(9/100)*Real.sin x
  have ha : 0<a := by dsimp [a,lambda]; nlinarith [ht.1,ht.2.2.1]
  have hE : E z=D z*(NF x)^2 := by
    dsimp [E]
    rw [← hs,← hc,hN2]
    ring
  have hJ : J z=D z*a := by dsimp [J,a]; rw [← hs,← hc]; ring
  have hP : P z=(D z)^3*
      (a^2*(NF x)^2-Q0*lambda^2*(p*Real.cos x+q*Real.sin x)^2) := by
    dsimp [P]
    rw [hE,hJ,← hs,← hc]
    ring
  have hdelta : 0<a^2*(NF x)^2-Q0*lambda^2*(p*Real.cos x+q*Real.sin x)^2 := by
    have hh := polynomial_positive hz
    rw [hP] at hh
    exact (mul_pos_iff_of_pos_left (pow_pos hD 3)).mp hh
  have hforce : 0≤R*lambda*(p*Real.cos x+q*Real.sin x) := by
    apply mul_nonneg (mul_nonneg R_pos.le (by norm_num [lambda]))
    exact add_nonneg (mul_nonneg (by norm_num [p]) ht.2.2.1)
      (mul_nonneg (by norm_num [q]) ht.1)
  have hsq : (R*lambda*(p*Real.cos x+q*Real.sin x))^2=
      Q0*lambda^2*(p*Real.cos x+q*Real.sin x)^2 := by rw [mul_pow,mul_pow,R_sq]
  have hlt : R*lambda*(p*Real.cos x+q*Real.sin x)<a*NF x := by
    nlinarith [mul_pos ha hn]
  have hdiv := (div_lt_iff₀ hn).2 hlt
  dsimp [Fd,NFd,a]
  have he : R*(lambda*(p*Real.cos x+q*Real.sin x)/NF x)=
      R*lambda*(p*Real.cos x+q*Real.sin x)/NF x := by ring
  rw [he]
  linarith

theorem F_monotone : MonotoneOn F (Icc (3/5:ℝ) (109/100)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact (F_deriv ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩).
      continuousAt.continuousWithinAt
  · intro x hx
    exact F_deriv ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  · intro x hx
    exact (Fd_positive (Ioo_subset_Icc_self hx)).le

theorem transverse_endpoint_trig :
    (2823/5000:ℝ)<Real.sin (3/5:ℝ) ∧ Real.sin (3/5:ℝ)<5647/10000 ∧
      (8253/10000:ℝ)<Real.cos (3/5:ℝ) ∧ Real.cos (3/5:ℝ)<4127/5000 := by
  have hsL := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
  have hsU := sin_upper_five (show (0:ℝ)≤3/5 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
  have hcU := Arithmetic.cos_le_cos8 (show (0:ℝ)≤3/5 by norm_num)
  norm_num [Arithmetic.cos8] at *
  repeat' constructor <;> linarith

theorem F_endpoint : (4507/5000:ℝ)<F (3/5:ℝ) := by
  have ht := transverse_endpoint_trig
  have hdom : (3/5:ℝ)∈Icc 0 (Real.pi/2) :=
    ⟨by norm_num,by linarith [FrameLowPair.pi_lower]⟩
  have hn := NF_pos hdom
  have hn2 := NF_sq hdom
  have hsq : (R*NF (3/5:ℝ))^2=Q0*(NF (3/5:ℝ))^2 := by rw [mul_pow,R_sq]
  have hrad : R*NF (3/5:ℝ)<1069/250 := by
    have hprod := mul_pos R_pos hn
    dsimp [p,q,lambda,Q0] at hn2 hsq
    nlinarith
  have hbase : (25887/5000:ℝ)<
      (3/5:ℝ)+KF+(lambda-9/100)*Real.sin (3/5:ℝ)-(9/100)*Real.cos (3/5:ℝ) := by
    dsimp [KF,mF,cM,p,q,lambda]
    linarith
  dsimp [F]
  linarith

theorem transverse_lower {x : ℝ} (hx : x∈Icc (3/5:ℝ) (109/100)) :
    (557/625:ℝ)<F x := by
  have hh := F_monotone ⟨le_rfl,by norm_num⟩ hx hx.1
  linarith [F_endpoint]

/-! ## The actual primary norm and its whole second-quadrant curvature -/

def NP (x : ℝ) : ℝ := CircularNorm.norm (p^2+q^2+1) (-2*p) (-2*q) x
def primaryF (x : ℝ) : ℝ :=
  x+KP-(9/100)*Real.sin x-(91/100)*Real.cos x-R*NP x
def primaryD (x : ℝ) : ℝ :=
  1-(9/100)*Real.cos x+(91/100)*Real.sin x-
    R*CircularNorm.d1 (p^2+q^2+1) (-2*p) (-2*q) x
def primaryDD (x : ℝ) : ℝ :=
  (9/100)*Real.sin x+(91/100)*Real.cos x-
    R*CircularNorm.d2 (p^2+q^2+1) (-2*p) (-2*q) x

theorem NP_energy_pos (x : ℝ) :
    0<CircularNorm.energy (p^2+q^2+1) (-2*p) (-2*q) x := by
  have hp : 0<p-Real.cos x := by dsimp [p]; linarith [Real.cos_le_one x]
  have he : CircularNorm.energy (p^2+q^2+1) (-2*p) (-2*q) x=
      (p-Real.cos x)^2+(q-Real.sin x)^2 := by
    dsimp [CircularNorm.energy]
    linear_combination -(Real.sin_sq_add_cos_sq x)
  rw [he]
  nlinarith [sq_pos_of_pos hp,sq_nonneg (q-Real.sin x)]

theorem NP_pos (x : ℝ) : 0<NP x := CircularNorm.norm_pos (NP_energy_pos x)
theorem NP_sq (x : ℝ) :
    (NP x)^2=p^2+q^2+1-2*(p*Real.cos x+q*Real.sin x) := by
  have hh := CircularNorm.norm_sq (NP_energy_pos x).le
  convert hh using 1 <;> dsimp [NP,CircularNorm.energy] <;> ring

theorem primaryF_deriv (x : ℝ) : HasDerivAt primaryF (primaryD x) x := by
  convert ((((hasDerivAt_id x).add_const KP).sub
    ((Real.hasDerivAt_sin x).const_mul (9/100))).sub
    ((Real.hasDerivAt_cos x).const_mul (91/100))).sub
    ((CircularNorm.norm_hasDerivAt (NP_energy_pos x)).const_mul R) using 1 <;>
    dsimp [primaryF,primaryD,NP] <;> ring

theorem primaryD_deriv (x : ℝ) : HasDerivAt primaryD (primaryDD x) x := by
  convert ((((Real.hasDerivAt_cos x).const_mul (-(9/100:ℝ))).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (91/100))).sub
    ((CircularNorm.d1_hasDerivAt (NP_energy_pos x)).const_mul R) using 1 <;>
    dsimp [primaryD,primaryDD] <;> ring

theorem radius_bounds : (197/100:ℝ)<R ∧ R<(99/50:ℝ) := by
  have hs := R_sq
  have hp := R_pos
  norm_num [Q0] at hs
  constructor <;> nlinarith

theorem primary_endpoint_trig : (24/25:ℝ)<Real.sin (37/20:ℝ) ∧
    -(69/250:ℝ)<Real.cos (37/20:ℝ) ∧ Real.cos (37/20:ℝ)<-(11/40:ℝ) := by
  have hs := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤37/20 by norm_num)
  have hcL := Arithmetic.cos10_le_cos (show (0:ℝ)≤37/20 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤37/20 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
    Arithmetic.cos8,HighOrderTaylor.C12] at *
  repeat' constructor <;> linarith

theorem primary_trig {x : ℝ} (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) :
    (24/25:ℝ)<Real.sin x ∧ -(69/250:ℝ)<Real.cos x ∧ Real.cos x≤0 := by
  have hxq : x∈Icc (Real.pi/2) Real.pi :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hs := sin_endpoint_lower (by positivity : (0:ℝ)≤Real.pi/2)
    (by linarith [FrameLowPair.pi_lower] : (37/20:ℝ)≤Real.pi) hx
    (by norm_num : (24/25:ℝ)<Real.sin (Real.pi/2)) primary_endpoint_trig.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos] : 0≤x)
    (by linarith [FrameLowPair.pi_lower]) hx.2
  exact ⟨hs,primary_endpoint_trig.2.1.trans_le hc,(second_signs hxq).2⟩

theorem NP_upper {x : ℝ} (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) : NP x<(15/8:ℝ) := by
  have ht := primary_trig hx
  have hn := NP_pos x
  have hh := NP_sq x
  dsimp [p,q] at hh
  nlinarith

theorem primaryDD_negative {x : ℝ} (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) :
    primaryDD x<0 := by
  have hn := NP_pos x
  have hnu := NP_upper hx
  have ht := primary_trig hx
  have hR := radius_bounds
  have hK : (69/5:ℝ)<(p^2+q^2-1)^2 := by norm_num [p,q]
  have hden : 0<4*(NP x)^3 := by positivity
  have hdenU : 4*(NP x)^3≤4*(15/8:ℝ)^3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hnu.le 3) (by norm_num)
  have hnum : (197/100:ℝ)*(69/5)<R*(p^2+q^2-1)^2 := by
    exact (mul_lt_mul_of_pos_left hK (by norm_num : (0:ℝ)<197/100)).trans
      (mul_lt_mul_of_pos_right hR.1 (by linarith [hK] : 0<(p^2+q^2-1)^2))
  have hratio : (197/100:ℝ)*(69/5)/(4*(15/8:ℝ)^3)<
      R*(p^2+q^2-1)^2/(4*(NP x)^3) := by
    apply (lt_div_iff₀ hden).2
    have hm := mul_le_mul_of_nonneg_left hdenU
      (show (0:ℝ)≤(197/100)*(69/5)/(4*(15/8)^3) by norm_num)
    norm_num at hm
    linarith
  have hRN : R*NP x<(99/50:ℝ)*(15/8) := by
    exact (mul_lt_mul_of_pos_left hnu R_pos).trans
      (mul_lt_mul_of_pos_right hR.2 (by norm_num : (0:ℝ)<15/8))
  have hid := CircularNorm.curvature_identity (NP_energy_pos x)
  have hcoef : (p^2+q^2+1)^2-(-2*p)^2-(-2*q)^2=(p^2+q^2-1)^2 := by ring
  rw [hcoef] at hid
  change CircularNorm.d2 (p^2+q^2+1) (-2*p) (-2*q) x+NP x/4=
    (p^2+q^2-1)^2/(4*(NP x)^3) at hid
  have hmul := congrArg (fun z : ℝ => R*z) hid
  have he : R*((p^2+q^2-1)^2/(4*(NP x)^3))=
      R*(p^2+q^2-1)^2/(4*(NP x)^3) := by ring
  rw [he] at hmul
  dsimp [primaryDD]
  nlinarith [Real.sin_le_one x,ht.2.2]

theorem primary_concave : ConcaveOn ℝ (Icc (Real.pi/2) (37/20:ℝ)) primaryF :=
  concave_of_deriv2 (fun x _ => primaryF_deriv x)
    (fun x _ => primaryD_deriv x) (fun x hx => (primaryDD_negative hx).le)

theorem primary_quarter_lower : (557/625:ℝ)<primaryF (Real.pi/2) := by
  have hn := NP_pos (Real.pi/2)
  have hh := NP_sq (Real.pi/2)
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,add_zero] at hh
  have hnu : NP (Real.pi/2)<8/5 := by dsimp [p,q] at hh; nlinarith
  have hRN : R*NP (Real.pi/2)<(99/50:ℝ)*(8/5) := by
    exact (mul_lt_mul_of_pos_left hnu R_pos).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<8/5))
  dsimp [primaryF,KP,mP,cM,p,q]
  simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,sub_zero]
  linarith [FrameLowPair.pi_lower]

theorem primary_last_lower : (557/625:ℝ)<primaryF (37/20:ℝ) := by
  have hx : (37/20:ℝ)∈Icc (Real.pi/2) (37/20:ℝ) :=
    ⟨by linarith [Arithmetic.pi_hand_enclosure.2],le_rfl⟩
  have hnu := NP_upper hx
  have hRN : R*NP (37/20:ℝ)<(99/50:ℝ)*(15/8) := by
    exact (mul_lt_mul_of_pos_left hnu R_pos).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<15/8))
  dsimp [primaryF,KP,mP,cM,p,q]
  linarith [Real.sin_le_one (37/20:ℝ),primary_endpoint_trig.2.2]

theorem primary_lower {x : ℝ} (hx : x∈Icc (Real.pi/2) (37/20:ℝ)) :
    (557/625:ℝ)<primaryF x :=
  concave_gt_of_endpoints primary_concave hx primary_quarter_lower primary_last_lower

end SquaresInCircles.Eight.TableFree.FrameMidMidScalars
