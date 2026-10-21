module

public import SquaresInCircles.Eight.TableFree.FrameLowMidContactPolynomial
public import SquaresInCircles.Eight.TableFree.FrameLowMidGeometry

/-!
# The actual low-target transverse contact on its whole interval

The multiplier is chosen from the exact circle contact.  Its validity is
derived from a concave elementary lower bound; the contact itself is
strictly decreasing by the single polynomial proved in the preceding
module.  The final theorem applies to every original weak transverse
separator, including ties and both intrinsic arc endpoints.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidContact
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
  repeat' constructor <;> linarith

theorem domain_bounds {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    0<a x ∧ a x<71/100 ∧ h x<-(23/50:ℝ) ∧
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
  convert ((Real.hasDerivAt_sin x).const_mul FrameLowArc.u).sub
    ((Real.hasDerivAt_cos x).const_mul FrameLowArc.v) using 1 <;> dsimp [h,j] <;> ring
theorem j_deriv (x : ℝ) : HasDerivAt j (-h x) x := by
  convert ((Real.hasDerivAt_cos x).const_mul FrameLowArc.u).add
    ((Real.hasDerivAt_sin x).const_mul FrameLowArc.v) using 1 <;> dsimp [h,j] <;> ring
theorem rho_deriv {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    HasDerivAt rho (-a x*Real.cos x/rho x) x := by
  have hp : 0<Q0-(a x)^2 := by linarith [(domain_bounds hx).2.2.2.2.2]
  convert (((a_deriv x).pow 2).const_sub Q0).sqrt hp.ne' using 1
  · rfl
  · dsimp [rho]; ring

theorem f0_deriv (x : ℝ) : HasDerivAt f0 (f0d x) x := by
  convert (h_deriv x).neg.add (((a_deriv x).mul (j_deriv x)).div_const (1979/1000))
    using 1 <;> dsimp [f0,f0d] <;> ring

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
  all_goals repeat' constructor <;> linarith

theorem f0_endpoints : (99/100:ℝ)<f0 (2/5:ℝ) ∧ (17/20:ℝ)<f0 (79/100:ℝ) := by
  constructor
  · have ht := endpoint_trig_coarse false
    norm_num at ht
    have hs2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3894/10000) ht.1.le 2
    have hsc := mul_le_mul ht.1.le ht.2.2.1.le (by norm_num : (0:ℝ)≤9210/10000)
      (by linarith [ht.1] : 0≤Real.sin (2/5:ℝ))
    dsimp [f0,a,h,j,delta,FrameLowMidContactPolynomial.delta,FrameLowArc.u,FrameLowArc.v]
    nlinarith
  · have ht := endpoint_trig_coarse true
    norm_num at ht
    have hs2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7103/10000) ht.1.le 2
    have hsc := mul_le_mul ht.1.le ht.2.2.1.le (by norm_num : (0:ℝ)≤7038/10000)
      (by linarith [ht.1] : 0≤Real.sin (79/100:ℝ))
    dsimp [f0,a,h,j,delta,FrameLowMidContactPolynomial.delta,FrameLowArc.u,FrameLowArc.v]
    nlinarith

theorem multiplier_lower {x : ℝ} (hx : x∈Icc (2/5:ℝ) (79/100)) :
    (17/20:ℝ)<multiplier x := by
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
  convert hd using 1
  · rfl
  · dsimp [Fd,aa,bb]
    field_simp [(rho_pos hx).ne']
    nlinarith [rho_sq hx]

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
  have hlt : bb x<-(rho x*aa x) := by nlinarith
  have hdiv : bb x/rho x<-(aa x) := (div_lt_iff₀ hr).2 (by nlinarith)
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
  repeat' constructor <;> linarith

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
  have hnorm : (contactNorm x*rho x)^2=(R*j x)^2 := by
    calc
      _=(a x*j x)^2+(j x*rho x)^2 := by
        dsimp [multiplier] at hN2
        field_simp [hr.ne'] at hN2
        nlinarith only [hN2]
      _=(R*j x)^2 := by
        rw [mul_pow,mul_pow,mul_pow,R_sq]
        nlinarith only [congrArg (fun z : ℝ => (j x)^2*z) hr2]
  have he : contactNorm x*rho x=R*j x := by
    nlinarith [mul_nonneg hN0 hr.le,mul_pos R_pos hj]
  apply mul_right_cancel₀ hr.ne'
  have hm : multiplier x*rho x=a x*j x-h x*rho x := by
    dsimp [multiplier]
    field_simp [hr.ne']
    ring
  calc
    (a x*multiplier x-R*contactNorm x)*rho x=
        a x*(a x*j x-h x*rho x)-R*(R*j x) := by rw [← hm,← he]; ring
    _=(-a x*h x-j x*rho x)*rho x := by
      nlinarith only [congrArg (fun z : ℝ => j x*z) hr2,
        congrArg (fun z : ℝ => j x*z) R_sq]

/-- The actual original middle-to-low weak separator dominates the
contact expression.  Neither a chosen contact point nor the multiplier
lower bound is an input to this theorem. -/
theorem weak_separator {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (2/5:ℝ) (79/100))
    (hm : 0≤FrameLowMidGeometry.secondary true true b B x) :
    (1801/2000:ℝ)<FrameLowMidGeometry.midLowCost true true b B x := by
  have hλ : (4/5:ℝ)≤multiplier x := by linarith [multiplier_lower hx]
  have hs := middle_positive_source_rational hb hλ
  have hscaled := mul_nonneg (by linarith : 0≤multiplier x) hm
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
    dsimp [a,delta,FrameLowMidContactPolynomial.delta] at hid
    nlinarith
  exact (lower hx).trans_le hF

end SquaresInCircles.Eight.TableFree.FrameLowMidContact
