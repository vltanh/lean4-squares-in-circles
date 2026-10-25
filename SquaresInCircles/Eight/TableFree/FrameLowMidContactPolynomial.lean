module

public import SquaresInCircles.Eight.TableFree.FrameLowMidArc
public import SquaresInCircles.Eight.TableFree.FrameCoreMidFullCircle

/-!
# The single polynomial for the low-target transverse contact

The determinant is kept in factored rational form.  The apparent
degree-twelve numerator cancels by `sin² + cos² = 1`, leaving one
degree-ten polynomial.  Positivity on the complete half-angle interval
follows from a coefficientwise positive remainder and a power bound.
There is no angular subdivision or sampled-value premise.
Uncompiled source draft of HAND_FOUR_TYPE_SCALAR_REPLACEMENTS §5.3.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidContactPolynomial
open FramePair FrameCircleArc FrameLowArc

def delta : ℝ := 3491721/250000000
def D (z : ℝ) : ℝ := 1+z^2
def S (z : ℝ) : ℝ := 2*z
def C (z : ℝ) : ℝ := 1-z^2
def an (z : ℝ) : ℝ := S z-delta*D z
def hn (z : ℝ) : ℝ := u*S z-v*C z
def jn (z : ℝ) : ℝ := u*C z+v*S z
def en (z : ℝ) : ℝ := Q0*(D z)^2-(an z)^2
def tn (z : ℝ) : ℝ := D z+(9/100)*(S z-C z)
def wn (z : ℝ) : ℝ := (Q0-1-delta^2)*D z+2*delta*S z
def P (z : ℝ) : ℝ :=
  wn z*(Q0*(hn z)^2-(u^2+v^2)*(an z)^2)*(D z)^2-
    en z*(tn z)^2*D z+2*en z*tn z*(C z*hn z+an z*jn z)
def lowerP (y : ℝ) : ℝ :=
  1/20+(7/2)*y-23*y^3-225*y^5-135*y^7-2*y^9-y^10

theorem polynomial_remainder {y : ℝ} (hy : 0≤y) :
    lowerP y<P (21/50-y) := by
  have h2 := pow_nonneg hy 2
  have h3 := pow_nonneg hy 3
  have h4 := pow_nonneg hy 4
  have h5 := pow_nonneg hy 5
  have h6 := pow_nonneg hy 6
  have h7 := pow_nonneg hy 7
  have h8 := pow_nonneg hy 8
  have h9 := pow_nonneg hy 9
  have h10 := pow_nonneg hy 10
  simp only [P,wn,en,tn,hn,jn,an,D,S,C,delta,u,v,Q0,lowerP]
  linarith

theorem lowerP_positive {y : ℝ} (hy : y∈Icc (0:ℝ) (11/50)) :
    (1/20:ℝ)≤lowerP y := by
  have h2 := pow_le_pow_left₀ hy.1 hy.2 2
  have h4 := pow_le_pow_left₀ hy.1 hy.2 4
  have h6 := pow_le_pow_left₀ hy.1 hy.2 6
  have h8 := pow_le_pow_left₀ hy.1 hy.2 8
  have h9 := pow_le_pow_left₀ hy.1 hy.2 9
  have hnum : 23*(11/50:ℝ)^2+225*(11/50:ℝ)^4+
      135*(11/50:ℝ)^6+2*(11/50:ℝ)^8+(11/50:ℝ)^9<5/3 := by norm_num
  have hb : 0≤7/2-23*y^2-225*y^4-135*y^6-2*y^8-y^9 := by linarith
  have hm := mul_nonneg hy.1 hb
  dsimp [lowerP]
  nlinarith only [hm]

theorem polynomial_positive {z : ℝ} (hz : z∈Icc (1/5:ℝ) (21/50)) :
    (1/20:ℝ)<P z := by
  have hy : 21/50-z∈Icc (0:ℝ) (11/50) := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  have hh := (lowerP_positive hy).trans_lt (polynomial_remainder hy.1)
  simpa only [sub_sub_cancel] using hh

theorem half_angle_domain {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    ∃z∈Icc (1/5:ℝ) (21/50), D z*Real.sin x=S z ∧ D z*Real.cos x=C z := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  obtain ⟨z,hz,hs,hc⟩ := FrameCoreMidFullCircle.half_angle hxq
  change D z*Real.sin x=S z at hs
  change D z*Real.cos x=C z at hc
  have hid : z*(1+Real.cos x)=Real.sin x := by
    have hD : D z≠0 := by dsimp [D]; positivity
    apply mul_left_cancel₀ hD
    dsimp [D,S,C] at hs hc ⊢
    linear_combination z*hc-hs
  have hsl := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(2/5:ℝ)) hxq.2 hx.1
  have hsu := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos] : -(Real.pi/2)≤x)
    (by linarith [FrameLowPair.pi_lower] : (79/100:ℝ)≤Real.pi/2) hx.2
  have hcl := Real.cos_le_cos_of_nonneg_of_le_pi hxq.1
    (by linarith [FrameLowPair.pi_lower] : (79/100:ℝ)≤Real.pi) hx.2
  have hcu := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤2/5) (by linarith [hxq.2,Real.pi_pos]) hx.1
  have hsL := Real.sin_ge_sub_cube (show (0:ℝ)≤2/5 by norm_num)
  have hsU := sin_upper_five (show (0:ℝ)≤79/100 by norm_num)
  have hcL := cos_lower_six (show (0:ℝ)≤79/100 by norm_num)
  have hcU := cos_upper_four (show (0:ℝ)≤2/5 by norm_num)
  norm_num at hsL hsU hcL hcU
  have hs0 : (389/1000:ℝ)<Real.sin x := by linarith
  have hs1 : Real.sin x<(711/1000:ℝ) := by linarith
  have hc0 : (703/1000:ℝ)<Real.cos x := by linarith
  have hc1 : Real.cos x<(923/1000:ℝ) := by linarith
  have hzl := mul_le_mul_of_nonneg_left hc1.le hz.1
  have hzu := mul_le_mul_of_nonneg_left hc0.le hz.1
  exact ⟨z,⟨by nlinarith,by nlinarith⟩,hs,hc⟩

/-- Exact cancellation before the half-angle denominators are cleared. -/
theorem determinant_identity (s c : ℝ) (hsc : s^2+c^2=1) :
    let a := s-delta
    let h := u*s-v*c
    let j := u*c+v*s
    let e := Q0-a^2
    let t := 1+(9/100)*(s-c)
    (e*h+a*c*j)^2-e*(t-c*h-a*j)^2=
      (Q0-1-delta^2+2*delta*s)*(Q0*h^2-(u^2+v^2)*a^2)-
        e*t^2+2*e*t*(c*h+a*j) := by
  have hh : (u*s-v*c)^2+(u*c+v*s)^2=u^2+v^2 := by
    linear_combination (u^2+v^2)*hsc
  have he : Q0-(s-delta)^2-c^2=Q0-1-delta^2+2*delta*s := by
    nlinarith only [hsc]
  dsimp
  calc
    _=(Q0-(s-delta)^2-c^2)*
        (Q0*(u*s-v*c)^2-(s-delta)^2*((u*s-v*c)^2+(u*c+v*s)^2))-
        (Q0-(s-delta)^2)*(1+(9/100)*(s-c))^2+
        2*(Q0-(s-delta)^2)*(1+(9/100)*(s-c))*
          (c*(u*s-v*c)+(s-delta)*(u*c+v*s)) := by ring
    _=_ := by rw [hh,he]; ring

theorem denominator_identity {x z : ℝ}
    (hs : D z*Real.sin x=S z) (hc : D z*Real.cos x=C z) :
    let a := Real.sin x-delta
    let h := u*Real.sin x-v*Real.cos x
    let j := u*Real.cos x+v*Real.sin x
    let e := Q0-a^2
    let t := 1+(9/100)*(Real.sin x-Real.cos x)
    P z=(D z)^5*((e*h+a*Real.cos x*j)^2-e*(t-Real.cos x*h-a*j)^2) := by
  dsimp
  rw [determinant_identity (Real.sin x) (Real.cos x) (Real.sin_sq_add_cos_sq x)]
  have hD : 0<D z := by dsimp [D]; positivity
  have hS : S z=D z*Real.sin x := hs.symm
  have hC : C z=D z*Real.cos x := hc.symm
  dsimp [P,wn,en,tn,hn,jn,an]
  rw [hS,hC]
  ring

end SquaresInCircles.Eight.TableFree.FrameLowMidContactPolynomial
