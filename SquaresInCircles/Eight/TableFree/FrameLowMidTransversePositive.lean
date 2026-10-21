module

public import SquaresInCircles.Eight.TableFree.FrameLowMidTransverseNorm

/-!
# The full positive low-to-middle transverse support

One quadratic norm majorant produces a second-harmonic polynomial.
Its third derivative is positive on the complete physical interval;
the upper-curvature chord gives a strict lower bound.  The proof retains
the actual radical support and the original weak separator.
Uncompiled source draft of HAND_FOUR_TYPE_SCALAR_REPLACEMENTS §5.1.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowMidTransversePositive
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc FramePairCalculus
open FrameLowMidTransverseNorm

def r : ℝ := 1978787508/1000000000
def lam : ℝ := 189/200
def m : ℝ := p^2+q^2
def e : ℝ := m+lam^2-(13/5)^2
def E0 : ℝ := K lam (-(1/100000))-
  r*(13/10+(5/26)*(m+lam^2))+(r/216)*(e^2+2*lam^2*m)
def ca : ℝ := lam-9/100-r*lam*p/(13/5)+(r/54)*e*lam*p
def cb : ℝ := -(9/100)+r*lam*q/(13/5)-(r/54)*e*lam*q
def cc : ℝ := -r*lam^2*p*q/54
def cd : ℝ := r*lam^2*(q^2-p^2)/108
def E (x : ℝ) : ℝ :=
  x+E0+ca*Real.sin x+cb*Real.cos x+cc*Real.sin (2*x)+cd*Real.cos (2*x)
def Ed (x : ℝ) : ℝ :=
  1+ca*Real.cos x-cb*Real.sin x+2*cc*Real.cos (2*x)-2*cd*Real.sin (2*x)
def Edd (x : ℝ) : ℝ :=
  -ca*Real.sin x-cb*Real.cos x-4*cc*Real.sin (2*x)-4*cd*Real.cos (2*x)
def Eddd (x : ℝ) : ℝ :=
  -ca*Real.cos x+cb*Real.sin x-8*cc*Real.cos (2*x)+8*cd*Real.sin (2*x)

theorem coefficient_signs : ca<0 ∧ (11/10:ℝ)<cb ∧
    -(39/500:ℝ)<cc ∧ cc<0 ∧ 0<cd := by
  norm_num [ca,cb,cc,cd,r,lam,e,m,p,q]

theorem second_harmonic_identity (x : ℝ) :
    E x=x+K lam (-(1/100000))+(lam-9/100)*Real.sin x-(9/100)*Real.cos x-
      r*(13/10+(5/26)*energy lam x-(energy lam x-(13/5)^2)^2/216) := by
  have hs : Real.sin (2*x)=2*Real.sin x*Real.cos x := by
    rw [two_mul,Real.sin_add]
    ring
  have hc : Real.cos (2*x)=(Real.cos x)^2-(Real.sin x)^2 := by
    rw [two_mul,Real.cos_add]
    ring
  dsimp [E,E0,ca,cb,cc,cd,e,m,energy]
  rw [hs,hc]
  dsimp [r,lam,p,q]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem norm_support {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) :
    E x≤F lam (-(1/100000)) false x := by
  have hλ : lam∈Icc (0:ℝ) 1 := by constructor <;> norm_num [lam]
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hn := N_positive hλ x
  have hnU : N lam x≤3 := by simpa [lam] using (N_first_upper hxq).le
  have hmajor := quadratic_majorant ⟨hn.le,hnU⟩
  have hR : R≤r := by simpa [r] using radius_precise.2.le
  have hr : 0≤r := by norm_num [r]
  have hscaled := mul_le_mul hR hmajor hn.le hr
  rw [N_square hλ x] at hscaled
  rw [second_harmonic_identity]
  dsimp [F,cosCoefficient]
  linarith

theorem E_deriv (x : ℝ) : HasDerivAt E (Ed x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert (((((hasDerivAt_id x).add_const E0).add
    ((Real.hasDerivAt_sin x).const_mul ca)).add
      ((Real.hasDerivAt_cos x).const_mul cb)).add (hs.const_mul cc)).add (hc.const_mul cd)
      using 1 <;> dsimp [E,Ed] <;> ring

theorem Ed_deriv (x : ℝ) : HasDerivAt Ed (Edd x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert (((((Real.hasDerivAt_cos x).const_mul ca).const_add 1).sub
    ((Real.hasDerivAt_sin x).const_mul cb)).add (hc.const_mul (2*cc))).sub
      (hs.const_mul (2*cd)) using 1 <;> dsimp [Ed,Edd] <;> ring

theorem Edd_deriv (x : ℝ) : HasDerivAt Edd (Eddd x) x := by
  have hs := (Real.hasDerivAt_sin (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  have hc := (Real.hasDerivAt_cos (2*x)).comp x ((hasDerivAt_id x).const_mul 2)
  convert ((((Real.hasDerivAt_sin x).const_mul (-ca)).sub
    ((Real.hasDerivAt_cos x).const_mul cb)).sub (hs.const_mul (4*cc))).sub
      (hc.const_mul (4*cd)) using 1 <;> dsimp [Edd,Eddd] <;> ring

theorem Eddd_positive {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) : 0<Eddd x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(19/25:ℝ)) hxq.2 hx.1
  have hs0 := Real.sin_ge_sub_cube (show (0:ℝ)≤19/25 by norm_num)
  norm_num at hs0
  have hsL : (17/25:ℝ)<Real.sin x := by linarith
  have hs2 : 0≤Real.sin (2*x) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hx.1]) (by linarith [hx.2,FrameLowPair.pi_lower])
  have hc2 := Real.neg_one_le_cos (2*x)
  dsimp [Eddd,ca,cb,cc,cd,r,lam,e,m,p,q]
  linarith

theorem Edd_monotone : MonotoneOn Edd (Icc (19/25:ℝ) (7/5)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (Edd_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => Edd_deriv x
  · exact fun x hx => (Eddd_positive (Ioo_subset_Icc_self hx)).le

theorem Edd_endpoint : Edd (7/5:ℝ)<21/100 := by
  have hs1 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤7/5 by norm_num)
  have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤7/5 by norm_num)
  have hs2 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤14/5 by norm_num)
  have hc2 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤14/5 by norm_num)
  norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs1 hc1 hs2 hc2
  norm_num [Edd,ca,cb,cc,cd,r,lam,e,m,p,q]
  linarith

theorem Edd_upper {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) : Edd x≤21/100 := by
  exact (Edd_monotone hx ⟨by norm_num,le_rfl⟩ hx.2).trans Edd_endpoint.le

theorem E_endpoints :
    (2301/2500:ℝ)<E (19/25:ℝ) ∧ (1137/1250:ℝ)<E (7/5:ℝ) := by
  constructor
  · have hs1 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤19/25 by norm_num)
    have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤19/25 by norm_num)
    have hs2 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤38/25 by norm_num)
    have hc2 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤38/25 by norm_num)
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs1 hc1 hs2 hc2
    norm_num [E,E0,K,ca,cb,cc,cd,r,lam,e,m,p,q,cM]
    linarith
  · have hs1 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤7/5 by norm_num)
    have hc1 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤7/5 by norm_num)
    have hs2 := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤14/5 by norm_num)
    have hc2 := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤14/5 by norm_num)
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs1 hc1 hs2 hc2
    norm_num [E,E0,K,ca,cb,cc,cd,r,lam,e,m,p,q,cM]
    linarith

def Q (x : ℝ) : ℝ :=
  2301/2500-(3363/40000)*(x-19/25)+(21/200)*(x-19/25)^2
def Qd (x : ℝ) : ℝ := -(3363/40000)+(21/100)*(x-19/25)

theorem Q_deriv (x : ℝ) : HasDerivAt Q (Qd x) x := by
  convert ((((hasDerivAt_id x).sub_const (19/25)).const_mul (-(3363/40000:ℝ))).
    const_add (2301/2500)).add
      ((((hasDerivAt_id x).sub_const (19/25)).pow 2).const_mul (21/200)) using 1
  · dsimp [Q]; funext z; ring
  · dsimp [Qd]; ring
theorem Qd_deriv (x : ℝ) : HasDerivAt Qd (21/100:ℝ) x := by
  convert (((hasDerivAt_id x).sub_const (19/25)).const_mul (21/100)).const_add
    (-(3363/40000:ℝ)) using 1 <;> dsimp [Qd] <;> ring

theorem E_lower {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) : (1801/2000:ℝ)<E x := by
  have hc : ConcaveOn ℝ (Icc (19/25:ℝ) (7/5)) (fun z => E z-Q z) := by
    apply concave_of_deriv2 (fun z _ => (E_deriv z).sub (Q_deriv z))
      (fun z _ => (Ed_deriv z).sub (Qd_deriv z))
    intro z hz
    linarith [Edd_upper hz]
  have hleft : (0:ℝ)<E (19/25:ℝ)-Q (19/25:ℝ) := by
    norm_num [Q]
    linarith [E_endpoints.1]
  have hright : (0:ℝ)<E (7/5:ℝ)-Q (7/5:ℝ) := by
    norm_num [Q]
    linarith [E_endpoints.2]
  have hh := concave_gt_of_endpoints hc hx hleft hright
  have hmin : (1801/2000:ℝ)<Q x := by
    dsimp [Q]
    nlinarith [sq_nonneg ((x-19/25)-1121/2800)]
  linarith

theorem lower {x : ℝ} (hx : x∈Icc (19/25:ℝ) (7/5)) :
    (1801/2000:ℝ)<F lam (-(1/100000)) false x :=
  (E_lower hx).trans_le (norm_support hx)

theorem weak_separator {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (19/25:ℝ) (7/5))
    (hm : 0≤FrameLowMidGeometry.secondary true true b B x) :
    (1801/2000:ℝ)<FrameLowMidGeometry.lowMidCost true true b B x := by
  have hs : -(1/100000:ℝ)≤sign true*(L b-lam*b) := by
    simpa [sign,lam] using low_positive_source hb
  have hdom : x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩
  exact (lower hx).trans_le (circle_support true
    (show lam∈Icc (0:ℝ) 1 by constructor <;> norm_num [lam]) hb hB hs false hdom hm)

end SquaresInCircles.Eight.TableFree.FrameLowMidTransversePositive
