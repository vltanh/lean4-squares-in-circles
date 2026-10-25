module

public import SquaresInCircles.Eight.Frames.Core.MidFullCircle
public import SquaresInCircles.Eight.Frames.Low.HighParallel
public import SquaresInCircles.Eight.Frames.Low.HighParallelCalculus

/-!
# Eight squares: both endpoint continuations for middle-to-low transverse pairs

After the exact positive contact, the target support is decreasing on
the entire low arc and therefore reaches its minimum at the intrinsic
upper endpoint.  For the two negative tangents it is increasing on that
arc and reaches its minimum at the axial endpoint.  Harmonic derivative
bounds control the complete remaining angle intervals.
-/

section
/-!
## Explicit quarter-contact calculus with the original high target fixed

The continued source coordinate lies in `[-.25,.13]` throughout the
strip.  Its marker has derivative between `.95` and `1.09` there.
The positive-angle contact cost increases.  At negative angles it
decreases whenever the target primary coordinate is at most `1.03`;
the remaining target arc has a separate strict marker reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighQuarterCalculus
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds

def sourceDomain : Set ℝ := Icc (-(1/4:ℝ)) (13/100)
def cost (positive : Bool) (B x : ℝ) : ℝ :=
  x-(9/50)*(FrameLowHighParallelCalculus.width positive x-1)+L (height positive (A B) x)+G (A B)
def costD (positive : Bool) (B x : ℝ) : ℝ :=
  1-(9/50)*widthD positive x-Ld (height positive (A B) x)*P positive (A B) x

theorem height_eq (positive : Bool) {B : ℝ} (hB : B∈Icc b2 c0) (x : ℝ) :
    height positive (A B) x=FrameLowHighParallelCalculus.width positive x-B*Real.sin x-A B*Real.cos x := by
  rw [height,extended_involution (high_extended hB)]

theorem width_bounds (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    1≤FrameLowHighParallelCalculus.width positive x ∧ FrameLowHighParallelCalculus.width positive x≤101/100 := by
  have hlo : 1≤FrameLowHighParallelCalculus.width positive x := by rw [width_eq positive hx]; exact FrameCoreArc.width_one_le x
  have ht := trig_small positive hx
  refine ⟨hlo,?_⟩
  cases positive <;> dsimp [FrameLowHighParallelCalculus.width] <;> linarith [ht.1,ht.2.1,ht.2.2.2.1]

theorem height_domain (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) : height positive (A B) x∈sourceDomain := by
  have ht := trig_small positive hx
  have hw := width_bounds positive hx
  have ha := high_bounds hB
  have hBn : 0≤B := b2_mem.1.trans hB.1
  have hAn : 0≤A B := by linarith [ha.2.2.1]
  have hBsU := mul_le_mul_of_nonneg_left ht.2.1 hBn
  have hBsL := mul_le_mul_of_nonneg_left ht.1 hBn
  have hAcU := mul_le_mul_of_nonneg_left ht.2.2.2.1 hAn
  have hAcL := mul_le_mul
    (show (899/1000:ℝ)≤A B by linarith [ha.2.2.1]) ht.2.2.1
    (by norm_num : (0:ℝ)≤4999/5000) hAn
  rw [height_eq positive hB]
  constructor <;> nlinarith [ha.2.1,ha.2.2.2]

theorem source_derivative_bounds {z : ℝ} (hz : z∈sourceDomain) :
    (19/20:ℝ)<Ld z ∧ Ld z<109/100 := by
  have he : z∈extendedDomain := ⟨hz.1,by linarith [hz.2]⟩
  have hc := extended_circle he
  have hp := extended_shift_pos he
  have hsq := pow_le_pow_left₀ (show 0≤z+1/2 by linarith [hz.1])
    (show z+1/2≤63/100 by linarith [hz.2]) 2
  have hA : (15/8:ℝ)<A z+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hr0 : 0≤ slope z := div_nonneg (by linarith [hz.1]) hp.le
  have hrU : slope z<42/125 := by
    apply (div_lt_iff₀ hp).2
    linarith [hz.2]
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  constructor <;> linarith

theorem source_label_monotone : MonotoneOn L (Icc (-(1/4:ℝ)) b1) := by
  have he z (hz : z∈Icc (-(1/4:ℝ)) b1) : z∈extendedDomain :=
    ⟨hz.1,by linarith [hz.2,b1_bounds.2]⟩
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z hz => (extended_L_deriv (he z hz)).continuousAt.continuousWithinAt
  · exact fun z hz => extended_L_deriv (he z (Ioo_subset_Icc_self hz))
  · intro z hz
    have hr := extended_slope_monotone (he z (Ioo_subset_Icc_self hz))
      (low_extended (show b1∈Icc 0 b1 from ⟨b1_mem.1,le_rfl⟩)) hz.2.le
    have hbound := slope_bounds (show b1∈Icc 0 b1 from ⟨b1_mem.1,le_rfl⟩)
    dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
    linarith

theorem cost_deriv (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) : HasDerivAt (cost positive B) (costD positive B x) x := by
  have hz := height_domain positive hB hx
  have he : height positive (A B) x∈extendedDomain := ⟨hz.1,by linarith [hz.2]⟩
  have h := (((hasDerivAt_id' x).fun_sub
    (((width_deriv positive x).sub_const 1).const_mul (9/50))).fun_add
      ((extended_L_deriv he).comp x (height_deriv positive (A B) x))).add_const (G (A B))
  refine h.congr_deriv ?_
  simp only [costD]
  ring

theorem positive_derivative {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain true) : 0<costD true B x := by
  have ht := trig_small true hx
  have hw := widthD_bounds true hx
  have hd := source_derivative_bounds (height_domain true hB hx)
  have hBc := mul_le_mul_of_nonneg_left ht.2.2.2.1 (b2_mem.1.trans hB.1)
  have hAs := mul_nonneg (by linarith [(A_high_bounds hB).1,c0_bounds.1] : 0≤A B) ht.2.2.2.2
  have hp : P true (A B) x≤4101/10000 := by
    rw [P,extended_involution (high_extended hB)]
    linarith [hB.2,c0_bounds.2,hw.1]
  have hm0 := mul_le_mul_of_nonneg_left hp (by linarith [hd.1] : 0≤Ld (height true (A B) x))
  have hm1 := mul_le_mul_of_nonneg_right hd.2.le (by norm_num : (0:ℝ)≤4101/10000)
  dsimp [costD]
  nlinarith [hw.2]

theorem high_transverse_lower {B : ℝ} (hB : B∈Icc b2 c0)
    (hcap : A B≤103/100) : (3/4:ℝ)<B := by
  have hc := extended_circle (high_extended hB)
  have hA := extended_shift_pos (high_extended hB)
  have hAsq := pow_le_pow_left₀ hA.le (show A B+1/2≤153/100 by linarith) 2
  by_contra! hbad
  have hBsq := pow_le_pow_left₀ (by linarith [hB.1,b2_bounds.1] : 0≤B+1/2)
    (show B+1/2≤5/4 by linarith) 2
  norm_num [Q0] at hc
  nlinarith

theorem negative_derivative {B x : ℝ} (hB : B∈Icc b2 c0)
    (hcap : A B≤103/100) (hx : x∈angleDomain false) : costD false B x<0 := by
  have ht := trig_small false hx
  have hw := widthD_bounds false hx
  have hd := source_derivative_bounds (height_domain false hB hx)
  have hBlarge := high_transverse_lower hB hcap
  have hBc := mul_le_mul hBlarge.le ht.2.2.1 (by norm_num : (0:ℝ)≤4999/5000)
    (by linarith : 0≤B)
  have hAs := mul_nonpos_of_nonneg_of_nonpos
    (by linarith [(A_high_bounds hB).1,c0_bounds.1] : 0≤A B) ht.2.2.2.2
  have hp : (4959/4000:ℝ)≤P false (A B) x := by
    rw [P,extended_involution (high_extended hB)]
    linarith [hw.2]
  have hm := mul_le_mul hd.1.le hp (by norm_num : (0:ℝ)≤4959/4000)
    (by linarith [hd.1] : 0≤Ld (height false (A B) x))
  dsimp [costD]
  nlinarith [hw.1]

theorem G_monotone : MonotoneOn G extendedDomain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z hz => (G_deriv hz).continuousAt.continuousWithinAt
  · exact fun z hz => G_deriv (Ioo_subset_Icc_self hz)
  · intro z hz
    have hr : 0≤ FrameLowArc.slope z := div_nonneg
      (by linarith [hz.1])
      (extended_shift_pos (Ioo_subset_Icc_self hz)).le
    dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
    linarith

theorem G_reference : (229/250:ℝ)<G (103/100) := by
  have he : (103/100:ℝ)∈extendedDomain := by constructor <;> norm_num [extendedDomain]
  have hc := extended_circle he
  have hp := extended_shift_pos he
  have hA : A (103/100)<151/200 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤251/200)
      (show (251/200:ℝ)≤A (103/100)+1/2 by linarith) 2
    norm_num [Q0] at hc
    nlinarith
  dsimp [G,FrameHighArc.u,FrameHighArc.v]
  linarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.2]

theorem target_chart {B : ℝ} (hB : B∈Icc b2 c0) : A B∈extendedDomain := by
  have hh := A_high_bounds hB
  constructor <;> linarith [hh.1,hh.2,c0_bounds.1,a2_bounds.2]

end SquaresInCircles.Eight.FrameLowHighQuarterCalculus
end
end
end

section
/-!
## The single polynomial for the low-target transverse contact

The determinant is kept in factored rational form.  The apparent
degree-twelve numerator cancels by `sin² + cos² = 1`, leaving one
degree-ten polynomial.  Positivity on the complete half-angle interval
follows from a coefficientwise positive remainder and a power bound.
There is no angular subdivision or sampled-value premise.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidContactPolynomial
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

end SquaresInCircles.Eight.FrameLowMidContactPolynomial
end
end
end

section
/-!
## The actual low-target transverse contact on its whole interval

The multiplier is chosen from the exact circle contact.  Its validity is
derived from a concave elementary lower bound; the contact itself is
strictly decreasing by the single polynomial proved in the preceding
module.  The final theorem applies to every original weak transverse
separator, including ties and both intrinsic arc endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidContact
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidContactPolynomial (delta)

def a (x : ℝ) : ℝ := Real.sin x-delta
def h (x : ℝ) : ℝ := FrameLowArc.u*Real.sin x-FrameLowArc.v*Real.cos x
def j (x : ℝ) : ℝ := FrameLowArc.u*Real.cos x+FrameLowArc.v*Real.sin x
def rho (x : ℝ) : ℝ := Real.sqrt (Q0-(a x)^2)
def aa (x : ℝ) : ℝ :=
  1+(9/100)*(Real.sin x-Real.cos x)-Real.cos x*h x-a x*j x
def bb (x : ℝ) : ℝ :=
  (Q0-(a x)^2)*h x+a x*Real.cos x*j x
def contactConstant : ℝ :=
  9/100+911/2000+FrameLowArc.u*(1414575670/1000000000)+
    (FrameLowArc.u+FrameLowArc.v)/2
def F (x : ℝ) : ℝ :=
  x+contactConstant-(9/100)*(Real.sin x+Real.cos x)-a x*h x-j x*rho x
def Fd (x : ℝ) : ℝ := aa x+bb x/rho x
def multiplier (x : ℝ) : ℝ := a x*j x/rho x-h x
def f0 (x : ℝ) : ℝ := -h x+a x*j x/(1979/1000)
def f0d (x : ℝ) : ℝ :=
  -j x+(Real.cos x*j x-a x*h x)/(1979/1000)
def f0dd (x : ℝ) : ℝ :=
  h x*(1-2*Real.cos x/(1979/1000))+(delta-2*Real.sin x)*j x/(1979/1000)

theorem trig_bounds {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    (19/50:ℝ)<Real.sin x ∧ Real.sin x<18/25 ∧
      (69/100:ℝ)<Real.cos x ∧ Real.cos x<93/100 := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
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
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem domain_bounds {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    0<a x ∧ a x<71/100 ∧ h x< -(23/50:ℝ) ∧
      0<j x ∧ j x<6/5 ∧ (17/5:ℝ)<Q0-(a x)^2 := by
  have ht := trig_bounds hx
  have ha : 0<a x ∧ a x<71/100 := by
    dsimp [a,delta,FrameLowMidContactPolynomial.delta]
    constructor <;> linarith
  have hsq := pow_le_pow_left₀ ha.1.le ha.2.le 2
  refine ⟨ha.1,ha.2,?_,?_,?_,?_⟩
  · dsimp [h,FrameLowArc.u,FrameLowArc.v]; linarith
  · dsimp [j,FrameLowArc.u,FrameLowArc.v]; linarith
  · dsimp [j,FrameLowArc.u,FrameLowArc.v]; linarith
  · norm_num [Q0] at *; linarith

theorem rho_pos {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) : 0<rho x :=
  Real.sqrt_pos.mpr (by linarith [(domain_bounds hx).2.2.2.2.2])

theorem rho_sq {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    (rho x)^2=Q0-(a x)^2 :=
  Real.sq_sqrt (by linarith [(domain_bounds hx).2.2.2.2.2])

theorem rho_upper {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    rho x<R ∧ rho x<1979/1000 := by
  have hp := rho_pos hx
  have hs := rho_sq hx
  have ha := (domain_bounds hx).1
  have hR := R_sq
  have hlt : rho x<R := by nlinarith [sq_pos_of_pos ha,R_pos]
  exact ⟨hlt,by linarith [radius_precise.2]⟩

theorem a_deriv (x : ℝ) : HasDerivAt a (Real.cos x) x :=
  (Real.hasDerivAt_sin x).sub_const delta
theorem h_deriv (x : ℝ) : HasDerivAt h (j x) x := by
  refine (((Real.hasDerivAt_sin x).const_mul FrameLowArc.u).sub
    ((Real.hasDerivAt_cos x).const_mul FrameLowArc.v)).congr_deriv ?_
  rw [j]
  ring
theorem j_deriv (x : ℝ) : HasDerivAt j (-h x) x := by
  refine (((Real.hasDerivAt_cos x).const_mul FrameLowArc.u).add
    ((Real.hasDerivAt_sin x).const_mul FrameLowArc.v)).congr_deriv ?_
  rw [h]
  ring
theorem rho_deriv {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    HasDerivAt rho (-a x*Real.cos x/rho x) x := by
  have hp : 0<Q0-(a x)^2 := by linarith [(domain_bounds hx).2.2.2.2.2]
  convert (((a_deriv x).pow 2).const_sub Q0).sqrt hp.ne' using 1
  · rfl
  · dsimp [rho]; ring

theorem f0_deriv (x : ℝ) : HasDerivAt f0 (f0d x) x := by
  refine ((h_deriv x).neg.add (((a_deriv x).mul (j_deriv x)).div_const (1979/1000))).congr_deriv ?_
  rw [f0d]
  ring

theorem f0d_deriv (x : ℝ) : HasDerivAt f0d (f0dd x) x := by
  convert (j_deriv x).neg.add ((((Real.hasDerivAt_cos x).mul (j_deriv x)).sub
    ((a_deriv x).mul (h_deriv x))).div_const (1979/1000)) using 1
  · rfl
  · dsimp [f0dd,a]; ring

theorem f0_concave : ConcaveOn ℝ (Icc (2/5:ℝ) (79/100)) f0 := by
  apply concave_of_deriv2 (fun x _ => f0_deriv x) (fun x _ => f0d_deriv x)
  intro x hx
  have ht := trig_bounds hx
  have hb := domain_bounds hx
  have hp : 0≤1-2*Real.cos x/(1979/1000) := by linarith [ht.2.2.2]
  have hn : delta-2*Real.sin x≤0 := by
    dsimp [delta,FrameLowMidContactPolynomial.delta]; linarith [ht.1]
  have h1 := mul_nonpos_of_nonpos_of_nonneg (by linarith [hb.2.2.1] : h x≤0) hp
  have h2 := mul_nonpos_of_nonpos_of_nonneg hn hb.2.2.2.1.le
  dsimp [f0dd]
  linarith

theorem endpoint_trig_coarse (i : Bool) :
    let x : ℝ := if i then 79/100 else 2/5
    let sl : ℝ := if i then 7103/10000 else 3894/10000
    let su : ℝ := if i then 7104/10000 else 3895/10000
    let cl : ℝ := if i then 7038/10000 else 9210/10000
    let cu : ℝ := if i then 7039/10000 else 9211/10000
    sl<Real.sin x ∧ Real.sin x<su ∧ cl<Real.cos x ∧ Real.cos x<cu := by
  let x : ℝ := if i then 79/100 else 2/5
  have hx : 0≤x := by cases i <;> norm_num [x]
  have hsL := HighOrderTaylor.S11_le_sin hx
  have hsU := HighOrderTaylor.sin_le_S13 hx
  have hcL := Arithmetic.cos10_le_cos hx
  have hcU := HighOrderTaylor.cos_le_C12 hx
  cases i <;>
    norm_num [x,HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  all_goals refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem f0_endpoints : (99/100:ℝ)<f0 (2/5:ℝ) ∧ (17/20:ℝ)<f0 (79/100:ℝ) := by
  constructor
  · have ht : (3894/10000:ℝ)<Real.sin (2/5) ∧ Real.sin (2/5)<3895/10000 ∧
        (9210/10000:ℝ)<Real.cos (2/5) ∧ Real.cos (2/5)<9211/10000 :=
      endpoint_trig_coarse false
    have hs2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3894/10000) ht.1.le 2
    have hsc := mul_le_mul ht.1.le ht.2.2.1.le (by norm_num : (0:ℝ)≤9210/10000)
      (by linarith [ht.1] : 0≤Real.sin (2/5:ℝ))
    dsimp [f0,a,h,j,delta,FrameLowMidContactPolynomial.delta,FrameLowArc.u,FrameLowArc.v]
    nlinarith
  · have ht : (7103/10000:ℝ)<Real.sin (79/100) ∧ Real.sin (79/100)<7104/10000 ∧
        (7038/10000:ℝ)<Real.cos (79/100) ∧ Real.cos (79/100)<7039/10000 :=
      endpoint_trig_coarse true
    have hs2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7103/10000) ht.1.le 2
    have hsc := mul_le_mul ht.1.le ht.2.2.1.le (by norm_num : (0:ℝ)≤7038/10000)
      (by linarith [ht.1] : 0≤Real.sin (79/100:ℝ))
    dsimp [f0,a,h,j,delta,FrameLowMidContactPolynomial.delta,FrameLowArc.u,FrameLowArc.v]
    nlinarith

theorem multiplier_lower {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    (17/20:ℝ)< multiplier x := by
  have hf : (17/20:ℝ)<f0 x := concave_gt_of_endpoints f0_concave hx
    (by linarith [f0_endpoints.1]) f0_endpoints.2
  have hb := domain_bounds hx
  have hp : 0<a x*j x := mul_pos hb.1 hb.2.2.2.1
  have hdiv : a x*j x/(1979/1000)<a x*j x/rho x := by
    apply (div_lt_div_iff₀ (by norm_num : (0:ℝ)<1979/1000) (rho_pos hx)).2
    exact mul_lt_mul_of_pos_left (rho_upper hx).2 hp
  dsimp [f0,multiplier] at *
  linarith

theorem derivative_signs {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    0<aa x ∧ bb x<0 := by
  have ht := trig_bounds hx
  have hb := domain_bounds hx
  have hcos : 0≤Real.cos x := by linarith [ht.2.2.1]
  have haj := mul_le_mul hb.2.1.le hb.2.2.2.2.1.le hb.2.2.2.1.le (by norm_num)
  have hch := mul_nonpos_of_nonneg_of_nonpos hcos (by linarith [hb.2.2.1] : h x≤0)
  have heh : (Q0-(a x)^2)*h x≤(17/5)*(-(23/50:ℝ)) := by
    have h1 := mul_le_mul_of_nonpos_right hb.2.2.2.2.2.le
      (by linarith [hb.2.2.1] : h x≤0)
    have h2 := mul_le_mul_of_nonneg_left hb.2.2.1.le (by norm_num : (0:ℝ)≤17/5)
    linarith
  have hac := mul_le_mul hb.2.1.le ht.2.2.2.le hcos (by norm_num)
  have hacj := mul_le_mul hac hb.2.2.2.2.1.le hb.2.2.2.1.le (by norm_num)
  constructor
  · dsimp [aa]; linarith
  · dsimp [bb]; linarith

theorem F_deriv {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    HasDerivAt F (Fd x) x := by
  have hd := ((((hasDerivAt_id x).add_const contactConstant).sub
    (((Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)).const_mul (9/100))).sub
      ((a_deriv x).mul (h_deriv x))).sub ((j_deriv x).mul (rho_deriv hx))
  refine hd.congr_deriv ?_
  have hr := (rho_pos hx).ne'
  rw [Fd,aa,bb,← rho_sq hx]
  field_simp
  ring

theorem Fd_negative {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) : Fd x<0 := by
  obtain ⟨z,hz,hs,hc⟩ := FrameLowMidContactPolynomial.half_angle_domain hx
  have hid := FrameLowMidContactPolynomial.denominator_identity hs hc
  change FrameLowMidContactPolynomial.P z=
    (FrameLowMidContactPolynomial.D z)^5*((bb x)^2-(Q0-(a x)^2)*(aa x)^2) at hid
  have hD : 0<FrameLowMidContactPolynomial.D z := by
    dsimp [FrameLowMidContactPolynomial.D]; positivity
  have hpoly := FrameLowMidContactPolynomial.polynomial_positive hz
  have hdet : 0<(bb x)^2-(Q0-(a x)^2)*(aa x)^2 := by
    have hh : 0<(FrameLowMidContactPolynomial.D z)^5*
        ((bb x)^2-(Q0-(a x)^2)*(aa x)^2) := by rw [← hid]; linarith
    exact (mul_pos_iff_of_pos_left (pow_pos hD 5)).mp hh
  have hs := derivative_signs hx
  have hr := rho_pos hx
  have hr2 := rho_sq hx
  have hprod := mul_pos hr hs.1
  have hsq : (rho x*aa x)^2<(bb x)^2 := by
    rw [mul_pow,hr2]
    linarith
  have hlt : bb x< -(rho x*aa x) := by nlinarith
  have hdiv : bb x/rho x< -(aa x) := (div_lt_iff₀ hr).2 (by nlinarith)
  dsimp [Fd]
  linarith

theorem F_antitone : AntitoneOn F (Icc (2/5:ℝ) (79/100)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x hx => (F_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => F_deriv (Ioo_subset_Icc_self hx)
  · exact fun x hx => (Fd_negative (Ioo_subset_Icc_self hx)).le

theorem endpoint_trig :
    (1775883181/2500000000:ℝ)<Real.sin (79/100:ℝ) ∧
      Real.sin (79/100:ℝ)<284141309/400000000 ∧
      (1759613289/2500000000:ℝ)<Real.cos (79/100:ℝ) ∧
      Real.cos (79/100:ℝ)<7038453157/10000000000 := by
  have hx : (0:ℝ)≤79/100 := by norm_num
  have hsL := HighOrderTaylor.S11_le_sin hx
  have hsU := HighOrderTaylor.sin_le_S13 hx
  have hcL := HighOrderTaylor.C14_le_cos hx
  have hcU := HighOrderTaylor.cos_le_C12 hx
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem endpoint_lower : (90059/100000:ℝ)<F (79/100:ℝ) := by
  have hx : (79/100:ℝ)∈Icc (2/5:ℝ) (79/100) := ⟨by norm_num,le_rfl⟩
  have ht := endpoint_trig
  have hb := domain_bounds hx
  have hr := rho_pos hx
  have hr2 := rho_sq hx
  have haL : (1775883181/2500000000:ℝ)-delta≤a (79/100:ℝ) := by
    dsimp [a]; linarith [ht.1]
  have haL0 : 0≤(1775883181/2500000000:ℝ)-delta := by
    norm_num [delta,FrameLowMidContactPolynomial.delta]
  have ha2 := pow_le_pow_left₀ haL0 haL 2
  have hrU : rho (79/100:ℝ)<1852200313/1000000000 := by
    norm_num [Q0,delta,FrameLowMidContactPolynomial.delta] at *
    nlinarith
  have hhL : FrameLowArc.v*(1759613289/2500000000)-
      FrameLowArc.u*(284141309/400000000)≤-h (79/100:ℝ) := by
    dsimp [h,FrameLowArc.u,FrameLowArc.v]
    linarith [ht.2.1,ht.2.2.1]
  have hhL0 : 0≤FrameLowArc.v*(1759613289/2500000000)-
      FrameLowArc.u*(284141309/400000000) := by norm_num [FrameLowArc.u,FrameLowArc.v]
  have hprodL := mul_le_mul haL hhL hhL0 hb.1.le
  have hjU : j (79/100:ℝ)≤FrameLowArc.u*(7038453157/10000000000)+
      FrameLowArc.v*(284141309/400000000) := by
    dsimp [j,FrameLowArc.u,FrameLowArc.v]
    linarith [ht.2.1,ht.2.2.2]
  have hjU0 : 0≤FrameLowArc.u*(7038453157/10000000000)+
      FrameLowArc.v*(284141309/400000000) := by norm_num [FrameLowArc.u,FrameLowArc.v]
  have hprodU := mul_le_mul hjU hrU.le hr.le hjU0
  dsimp [F,contactConstant]
  norm_num [FrameLowArc.u,FrameLowArc.v,delta,FrameLowMidContactPolynomial.delta] at *
  nlinarith

theorem lower {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) : (1801/2000:ℝ)<F x := by
  have hh := F_antitone hx ⟨by norm_num,le_rfl⟩ hx.2
  linarith [endpoint_lower]

def contactNorm (x : ℝ) : ℝ :=
  Real.sqrt ((FrameLowArc.u+multiplier x*Real.sin x)^2+
    (FrameLowArc.v-multiplier x*Real.cos x)^2)

theorem contact_identity {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    a x*multiplier x-R*contactNorm x=-a x*h x-j x*rho x := by
  have hr := rho_pos hx
  have hr2 := rho_sq hx
  have hj := (domain_bounds hx).2.2.2.1
  have hN0 : 0≤contactNorm x := Real.sqrt_nonneg _
  have hN2 : (contactNorm x)^2=
      (FrameLowArc.u+multiplier x*Real.sin x)^2+
        (FrameLowArc.v-multiplier x*Real.cos x)^2 := Real.sq_sqrt (by positivity)
  have hrot : (FrameLowArc.u+multiplier x*Real.sin x)^2+
      (FrameLowArc.v-multiplier x*Real.cos x)^2=(multiplier x+h x)^2+(j x)^2 := by
    dsimp [h,j]
    linear_combination ((multiplier x)^2-FrameLowArc.u^2-FrameLowArc.v^2)*
      (Real.sin_sq_add_cos_sq x)
  rw [hrot] at hN2
  have hm : multiplier x*rho x=a x*j x-h x*rho x := by
    dsimp [multiplier]
    rw [sub_mul,div_mul_cancel₀ _ hr.ne']
  have hnorm : (contactNorm x*rho x)^2=(R*j x)^2 := by
    calc
      _=(a x*j x)^2+(j x*rho x)^2 := by
        rw [mul_pow,hN2]
        linear_combination (multiplier x*rho x+h x*rho x+a x*j x)*hm
      _=(R*j x)^2 := by
        rw [mul_pow,mul_pow,mul_pow,R_sq,hr2]
        ring
  have he : contactNorm x*rho x=R*j x := by
    have h1 : 0≤contactNorm x*rho x := mul_nonneg hN0 hr.le
    have h2 : 0≤R*j x := (mul_pos R_pos hj).le
    exact (pow_left_inj₀ h1 h2 two_ne_zero).mp hnorm
  apply mul_right_cancel₀ hr.ne'
  calc
    (a x*multiplier x-R*contactNorm x)*rho x=
        a x*(a x*j x-h x*rho x)-R*(R*j x) := by rw [← hm,← he]; ring
    _=(-a x*h x-j x*rho x)*rho x := by
      rw [show R*(R*j x)=j x*R^2 by ring,R_sq,show (-a x*h x-j x*rho x)*rho x=
        -a x*h x*rho x-j x*rho x^2 by ring,hr2]
      ring

/-- The actual original middle-to-low weak separator dominates the
contact expression.  Neither a chosen contact point nor the multiplier
lower bound is an input to this theorem. -/
theorem weak_separator {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (2/5:ℝ) (79/100))
    (hm : 0≤FrameLowMidGeometry.secondary true true b B x) :
    (1801/2000:ℝ)<FrameLowMidGeometry.midLowCost true true b B x := by
  have hlam : (4/5:ℝ) ≤ multiplier x := by linarith [multiplier_lower hx]
  have hs := middle_positive_source_rational hb hlam
  have hscaled := mul_nonneg (by linarith : 0 ≤ multiplier x) hm
  have ht := circle_linear_lower (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-FrameLowArc.u-multiplier x*Real.sin x)
    (multiplier x*Real.cos x-FrameLowArc.v)
  have hnorm : Real.sqrt ((-FrameLowArc.u-multiplier x*Real.sin x)^2+
      (multiplier x*Real.cos x-FrameLowArc.v)^2)=contactNorm x := by
    dsimp [contactNorm]
    congr 1
    ring
  rw [hnorm] at ht
  have hid := contact_identity hx
  have hbase := mul_le_mul_of_nonneg_left a0_precise.1.le
    (show 0≤FrameLowArc.u by norm_num [FrameLowArc.u])
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hF : F x≤FrameLowMidGeometry.midLowCost true true b B x := by
    dsimp [FrameLowMidGeometry.secondary] at hscaled
    rw [(first_width hxq).1] at hscaled
    dsimp [FrameLowMidGeometry.midLowCost,F,contactConstant,L]
    rw [(first_width hxq).2]
    simp only [sign,ite_true,one_mul] at hscaled ⊢
    simp only [a,delta,FrameLowMidContactPolynomial.delta] at hid ⊢
    linarith
  exact (lower hx).trans_le hF

end SquaresInCircles.Eight.FrameLowMidContact
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidSecondaryContinuation
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidGeometry

def lam : ℝ := 797/1000
def half : ℝ := (lam-9/50)/2
def P : ℝ := lam*a1-half
def Q : ℝ := half+lam*b1
def base : ℝ := (lam+9/50)/2+M1-L1-lam*b1
def F (x : ℝ) : ℝ := x+base-P*Real.sin x+Q*Real.cos x

theorem coefficient_bounds : 0≤P ∧ P≤727/1000 ∧ 0≤Q ∧ Q≤71/125 := by
  dsimp [P,Q,half,lam]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith [a1_precise.1,a1_precise.2,FrameLowMidArc.b1_precise.1,FrameLowMidArc.b1_precise.2]

theorem coefficient_norm : P^2+Q^2<1 := by
  have hb := coefficient_bounds
  have hp := pow_le_pow_left₀ hb.1 hb.2.1 2
  have hq := pow_le_pow_left₀ hb.2.2.1 hb.2.2.2 2
  nlinarith

theorem F_deriv (x : ℝ) : HasDerivAt F (1-P*Real.cos x-Q*Real.sin x) x := by
  refine (((hasDerivAt_id x).add_const base).sub
    ((Real.hasDerivAt_sin x).const_mul P)).add
      ((Real.hasDerivAt_cos x).const_mul Q) |>.congr_deriv ?_
  ring

theorem F_monotone : MonotoneOn F (Icc (79/100:ℝ) (19/20)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (F_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => F_deriv x
  · intro x hx
    have hh := harmonic_projection_lt_one (A := Q) (B := P) (x := x)
      (by nlinarith [coefficient_norm])
    linarith

theorem F_endpoint : (4503/5000:ℝ)<F (79/100:ℝ) := by
  have ht := FrameLowMidContact.endpoint_trig
  have hb := coefficient_bounds
  have hPu : P≤lam*(1298747249/1000000000)-half := by
    dsimp [P,lam]
    linarith [a1_precise.2]
  have hQl : half+lam*(1298747247/4000000000)≤Q := by
    dsimp [Q,lam]
    linarith [FrameLowMidArc.b1_precise.1]
  have hPupos : 0≤lam*(1298747249/1000000000)-half := by norm_num [lam,half]
  have hQpos : 0≤half+lam*(1298747247/4000000000) := by norm_num [lam,half]
  have hP := mul_le_mul hPu ht.2.1.le (by linarith [ht.1] : 0≤Real.sin (79/100:ℝ)) hPupos
  have hQ := mul_le_mul hQl ht.2.2.1.le (by norm_num : (0:ℝ)≤1759613289/2500000000) hb.2.2.1
  have hbase : (lam+9/50)/2+1523/5000-30683/100000-
      lam*(1298747249/4000000000)≤base := by
    dsimp [base,lam]
    linarith [M_endpoints.1,L1_precise.2,FrameLowMidArc.b1_precise.2]
  dsimp [F]
  norm_num [lam,half] at hP hQ hbase
  linarith

theorem F_lower {x : ℝ} (hx : x∈Icc (79/100:ℝ) (19/20)) : (1801/2000:ℝ)<F x := by
  have hh := F_monotone ⟨le_rfl,by norm_num⟩ hx hx.1
  linarith [F_endpoint]

theorem target_antitone {x : ℝ} (hx : x∈Icc (79/100:ℝ) (19/20)) :
    AntitoneOn (linear (-FrameLowArc.u-lam*Real.sin x)
      (lam*Real.cos x-FrameLowArc.v)) (Icc 0 b1) := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos] : -(Real.pi/2)≤x)
    (by linarith [FrameLowPair.pi_lower] : (19/20:ℝ)≤Real.pi/2) hx.2
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤79/100) (by linarith [hxq.2,Real.pi_pos]) hx.1
  have hsE := sin_upper_five (show (0:ℝ)≤19/20 by norm_num)
  have hcE := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤79/100 by norm_num)
  norm_num [HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hcE
  norm_num at hsE
  have hsU : Real.sin x≤407/500 := by linarith
  have hcU : Real.cos x≤88/125 := by linarith
  have hp : 0≤FrameLowArc.u+lam*Real.sin x := by
    dsimp [FrameLowArc.u,lam]
    linarith [ht.1]
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (linear_hasDerivAt ⟨hB.1,hB.2.trans b1_mem.2⟩ _ _).continuousAt.continuousWithinAt
  · intro B hB
    exact linear_hasDerivAt ⟨hB.1.le,hB.2.le.trans b1_mem.2⟩ _ _
  · intro B hB
    have hratio := slope_bounds (Ioo_subset_Icc_self hB)
    have hh := mul_le_mul_of_nonneg_left hratio.2.le hp
    have hAd : Ad B= -FrameLowArc.slope B := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp [FrameLowArc.u,FrameLowArc.v,lam] at hh ⊢
    linarith

theorem positive_weak_separator {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (79/100:ℝ) (19/20)) (hm : 0≤ secondary true true b B x) :
    (1801/2000:ℝ)< midLowCost true true b B x := by
  have hs := middle_small_source hb
  have ht := target_antitone hx hB ⟨b1_mem.1,le_rfl⟩ hB.2
  dsimp [linear] at ht
  rw [A_b1] at ht
  have hscaled := mul_nonneg (show (0:ℝ)≤lam by norm_num [lam]) hm
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hF : F x≤ midLowCost true true b B x := by
    dsimp [secondary] at hscaled
    rw [(first_width hxq).1] at hscaled
    dsimp [F,base,P,Q,half,midLowCost,L,L1]
    rw [(first_width hxq).2]
    norm_num [sign] at hscaled ⊢
    dsimp [lam] at ht hscaled ⊢
    nlinarith
  exact (F_lower hx).trans_le hF

def axialP : ℝ := a0-41/100
def axialF (x : ℝ) : ℝ :=
  x+59/100-M1+b1-axialP*Real.sin x+(41/100)*Real.cos x

theorem axial_norm : 0≤axialP ∧ axialP≤201/200 ∧
    axialP^2+(41/100:ℝ)^2<(109/100:ℝ)^2 := by
  have hp : 0≤axialP ∧ axialP≤201/200 := by
    dsimp [axialP]
    constructor <;> linarith [a0_precise.1,a0_precise.2]
  have hs := pow_le_pow_left₀ hp.1 hp.2 2
  exact ⟨hp.1,hp.2,by nlinarith⟩

theorem axial_deriv (x : ℝ) :
    HasDerivAt axialF (1-axialP*Real.cos x-(41/100)*Real.sin x) x := by
  refine (((((hasDerivAt_id x).add_const (59/100)).sub_const M1).add_const b1).sub
    ((Real.hasDerivAt_sin x).const_mul axialP)).add
      ((Real.hasDerivAt_cos x).const_mul (41/100)) |>.congr_deriv ?_
  ring

theorem axial_corrected_monotone :
    MonotoneOn (fun x => axialF x+(9/100)*x) (Icc (19/25:ℝ) (7/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact ((axial_deriv x).add ((hasDerivAt_id x).const_mul (9/100))).continuousAt.continuousWithinAt
  · exact fun x hx => (axial_deriv x).add ((hasDerivAt_id x).const_mul (9/100))
  · intro x hx
    have hh := FrameCoreArc.projection_lt (a := (41/100:ℝ)) (b := axialP)
      (x := x) (show (0:ℝ)<109/100 by norm_num) (by nlinarith [axial_norm.2.2])
    linarith

theorem axial_endpoint : (97/100:ℝ)<axialF (19/25:ℝ) := by
  have hs := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤19/25 by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤19/25 by norm_num)
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hc
  have hsU : Real.sin (19/25:ℝ)≤689/1000 := by linarith
  have hcL : (453/625:ℝ)≤Real.cos (19/25:ℝ) := by linarith
  have hs0 : 0≤Real.sin (19/25:ℝ) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by norm_num) (by linarith [FrameLowPair.pi_lower])
  have hp := mul_le_mul axial_norm.2.1 hsU hs0 (by norm_num : (0:ℝ)≤201/200)
  dsimp [axialF]
  linarith [M_endpoints.2.1,FrameLowMidArc.b1_precise.1]

theorem axial_lower {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) :
    (1801/2000:ℝ)<axialF x := by
  have hh := axial_corrected_monotone ⟨le_rfl,by norm_num⟩ hx hx.1
  linarith [axial_endpoint,hx.2]

theorem negative_weak_separator {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (19/25:ℝ) (7/5)) (hm : 0≤ secondary false false b B x) :
    (1801/2000:ℝ)< midLowCost false false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hsL := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(19/25:ℝ)) hxq.2 hx.1
  have hsE := Real.sin_ge_sub_cube (show (0:ℝ)≤19/25 by norm_num)
  norm_num at hsE
  have hp : FrameLowArc.u-Real.sin x≤0 := by dsimp [FrameLowArc.u]; linarith
  have hq : 0≤FrameLowArc.v-Real.cos x := by dsimp [FrameLowArc.v]; linarith [Real.cos_le_one x]
  have ht := linear_monotone hp hq ⟨le_rfl,by linarith [c0_bounds.1]⟩
    ⟨hB.1,hB.2.trans b1_mem.2⟩ hB.1
  dsimp [linear] at ht
  rw [A_zero] at ht
  have hs := middle_negative_source hb (show (1:ℝ)≤1 by norm_num)
  have hF : axialF x≤ midLowCost false false b B x := by
    dsimp [secondary] at hm
    rw [(first_width hxq).1] at hm
    dsimp [axialF,axialP,midLowCost,L]
    rw [(first_width hxq).2]
    norm_num [sign] at hm ⊢
    nlinarith
  exact (axial_lower hx).trans_le hF

end SquaresInCircles.Eight.FrameLowMidSecondaryContinuation
end
end
end
