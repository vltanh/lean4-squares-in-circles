module

public import SquaresInCircles.Eight.TableFree.GlobalAllHighBridgePositive

/-!
# Fixed dual supports on the complete low and middle arcs

The low-source loss is a direct circle difference identity and one
quadratic completion.  The middle source uses its whole shifted
circle.  All target minima retain the original low, middle or high
marker.  Uncompiled draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge

open FramePair ZeroPrimary GlobalOuterAnchor FrameCircleArc FrameLowArc FrameMidArc

def lowDualA (mu : ℝ) : ℝ := -kappa+rho*FrameHighArc.u+(rho+mu)*FrameLowArc.u
def lowDualB (mu : ℝ) : ℝ := -rho*FrameHighArc.v+(rho+mu)*FrameLowArc.v
def lowDualC (mu : ℝ) : ℝ := rho*FrameHighArc.k+(rho+mu)*FrameLowArc.u*a0
def midDualA (mu : ℝ) : ℝ := -kappa+rho*FrameHighArc.u+(rho+mu)*FrameMidArc.p
def midDualB (mu : ℝ) : ℝ := -rho*FrameHighArc.v+(rho+mu)*FrameMidArc.q
def midDualC (mu : ℝ) : ℝ := rho*FrameHighArc.k-(rho+mu)*FrameMidArc.cM
def midShiftC (mu : ℝ) : ℝ := midDualC mu+(midDualA mu+midDualB mu)/2
def sourceNorm (mu lambda z : ℝ) : ℝ :=
  Real.sqrt ((midDualA mu+lambda*Real.cos z)^2+(midDualB mu-lambda*Real.sin z)^2)

theorem arcK_low (mu b : ℝ) :
    arcK .low mu b=lowDualC mu-lowDualA mu*A b-lowDualB mu*b := by
  rw [arcK,arcPotential,arcMarker_low]
  dsimp [FrameHighArc.H,FrameLowArc.L,lowDualA,lowDualB,lowDualC]
  ring

theorem arcK_middle (mu b : ℝ) :
    arcK .middle mu b=midDualC mu-midDualA mu*A b-midDualB mu*b := by
  rw [arcK,arcPotential,arcMarker_middle]
  dsimp [FrameHighArc.H,FrameMidArc.M,midDualA,midDualB,midDualC]
  ring

theorem high_constant_lower : (118248/125000:ℝ)<FrameHighArc.k := by
  dsimp [FrameHighArc.k,FrameHighArc.u,FrameHighArc.v]
  linarith [Arithmetic.pi_hand_enclosure.1,c0_precise.1]

theorem dual_endpoint_constants :
    (2113/2500:ℝ)<arcK .low (17/10) b1 ∧
    -(1673/10000:ℝ)<arcK .low 5 b1 ∧
    (109221/10000:ℝ)< midShiftC (17/10) ∧
    (115297/5000:ℝ)< midShiftC 5 := by
  have hk := high_constant_lower
  have ha0 := a0_precise
  have ha1 := a1_precise
  have hb1 := b1_precise
  repeat' constructor
  all_goals first
    | rw [arcK_low,A_b1]
    | skip
  all_goals dsimp [midShiftC,midDualA,midDualB,midDualC,
    lowDualA,lowDualB,lowDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
    FrameLowArc.u,FrameLowArc.v,FrameMidArc.p,FrameMidArc.q,FrameMidArc.cM]
  all_goals linarith

theorem affine_arc_lower {p q c l u b g : ℝ} (hp : 0≤p)
    (hl : 0≤l) (hu : u≤c0) (hb : b∈Icc l u)
    (hleft : g<c+p*A l+q*l) (hright : g<c+p*A u+q*u) :
    g<c+p*A b+q*b := by
  have hh := linear_endpoint_lower (q := q) hp hl hu hb
  have he : g-c< min (linear p q l) (linear p q u) := by
    apply lt_min <;> dsimp [linear] <;> linarith
  have h := he.trans_le hh
  dsimp [linear] at h
  linarith

theorem low_dual_target (t : State) (ht : t.branch=.low) :
    -(4029/2500:ℝ)< -K t (17/10)-(59/25)*t.b := by
  rw [K_arc t (by simp [ht,Branch.type]),ht,arcK_low]
  have h := affine_arc_lower (p := lowDualA (17/10))
    (q := lowDualB (17/10)-59/25) (c := -lowDualC (17/10))
    (g := -(4029/2500:ℝ)) (by norm_num [lowDualA,kappa,rho,FrameHighArc.u,FrameLowArc.u])
    (by norm_num) b1_mem.2 (state_low_chart t ht).2
  have he0 : -(4029/2500:ℝ)< -lowDualC (17/10)+lowDualA (17/10)*A 0+
      (lowDualB (17/10)-59/25)*0 := by
    rw [A_zero]
    dsimp [lowDualA,lowDualB,lowDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
      FrameLowArc.u,FrameLowArc.v]
    linarith [FrameHighArc.k_bounds.2.1,a0_precise.2]
  have he1 : -(4029/2500:ℝ)< -lowDualC (17/10)+lowDualA (17/10)*A b1+
      (lowDualB (17/10)-59/25)*b1 := by
    rw [A_b1]
    dsimp [lowDualA,lowDualB,lowDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
      FrameLowArc.u,FrameLowArc.v]
    linarith [FrameHighArc.k_bounds.2.1,a0_precise.2,a1_precise.1,b1_precise.1]
  have hh := h he0 he1
  linarith

theorem nonlow_dual_target (t : State) (ht : t.branch=.middle ∨ t.branch=.high) :
    -(1357/1000:ℝ)< -K t 5-(93/20)*t.b := by
  rcases ht with ht | ht
  · rw [K_arc t (by simp [ht,Branch.type]),ht,arcK_middle]
    have h := affine_arc_lower (p := midDualA 5) (q := midDualB 5-93/20)
      (c := -midDualC 5) (g := -(1357/1000:ℝ))
      (by norm_num [midDualA,kappa,rho,FrameHighArc.u,FrameMidArc.p])
      b1_mem.1 b2_mem.2 (state_mid_chart t ht).2
    have he0 : -(1357/1000:ℝ)< -midDualC 5+midDualA 5*A b1+(midDualB 5-93/20)*b1 := by
      rw [A_b1]
      dsimp [midDualA,midDualB,midDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
        FrameMidArc.p,FrameMidArc.q,FrameMidArc.cM]
      linarith [FrameHighArc.k_bounds.2.1,a1_precise.1,b1_precise.1]
    have he1 : -(1357/1000:ℝ)< -midDualC 5+midDualA 5*A b2+(midDualB 5-93/20)*b2 := by
      rw [A_b2]
      dsimp [midDualA,midDualB,midDualC,kappa,rho,FrameHighArc.u,FrameHighArc.v,
        FrameMidArc.p,FrameMidArc.q,FrameMidArc.cM]
      linarith [FrameHighArc.k_bounds.2.1,a2_bounds.1,b2_precise.1]
    have hh := h he0 he1
    linarith
  · have hh := circle_product_support t
      (f := kappa+5*FrameHighArc.u) (g := 93/20-5*FrameHighArc.v)
      (K := 18689/2000) (by norm_num)
      (by norm_num [Q0,kappa,FrameHighArc.u,FrameHighArc.v])
    rw [K,potential_high t ht,unsigned_arc t (by simp [ht,Branch.type]),ht,arcMarker_high]
    dsimp [FrameHighArc.H] at *
    rw [← (FrameHighArc.state_high_chart t ht).1]
    have hk := high_constant_lower
    dsimp [kappa,FrameHighArc.u,FrameHighArc.v] at *
    linarith

theorem circle_endpoint_loss {x t X T a b e k loss : ℝ}
    (hc : x^2+t^2=X^2+T^2) (hX : 0<X) (ha : 0≤a)
    (hk : 0<k) (hcurv : 2*k*X≤a) (ht : t≤T)
    (hd : a*T-b*X≤e*X) (hdisc : e^2<4*k*loss) :
    -loss<(-a*x-b*t)-(-a*X-b*T) := by
  have hid : 2*X*((-a*x-b*t)-(-a*X-b*T))=
      a*(x-X)^2+a*(t-T)^2+2*(a*T-b*X)*(t-T) := by
    linear_combination -a*hc
  have h1 := mul_nonneg ha (sq_nonneg (x-X))
  have h2 := mul_nonneg (sub_nonneg.mpr hcurv) (sq_nonneg (t-T))
  have h3 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hd) (sub_nonpos.mpr ht)
  have hq := positive_quadratic (z := t-T) hk hdisc
  have hq' := mul_pos (show 0<2*X by linarith) hq
  nlinarith only [hid,h1,h2,h3,hq',hX]

theorem circle_endpoint_min {x t X T a b : ℝ}
    (hc : x^2+t^2=X^2+T^2) (hX : 0<X) (ha : 0≤a) (ht : t≤T)
    (hd : a*T-b*X≤0) : -a*X-b*T≤ -a*x-b*t := by
  have hid : 2*X*((-a*x-b*t)-(-a*X-b*T))=
      a*(x-X)^2+a*(t-T)^2+2*(a*T-b*X)*(t-T) := by
    linear_combination -a*hc
  have h1 := mul_nonneg ha (sq_nonneg (x-X))
  have h2 := mul_nonneg ha (sq_nonneg (t-T))
  have h3 := mul_nonneg_of_nonpos_of_nonpos hd (sub_nonpos.mpr ht)
  nlinarith only [hid,h1,h2,h3,hX]

def lowAngle (z : ℝ) : ℝ := Real.sin z+(459/1000)*Real.cos z

theorem lowAngle_deriv (z : ℝ) :
    HasDerivAt lowAngle (Real.cos z-(459/1000)*Real.sin z) z := by
  have h : HasDerivAt (fun x => Real.sin x+(459/1000)*Real.cos x)
      (Real.cos z+(459/1000)*(-Real.sin z)) z :=
    (Real.hasDerivAt_sin z).fun_add ((Real.hasDerivAt_cos z).const_mul (459/1000))
  exact h.congr_deriv (by ring)

theorem lowAngle_bound {z : ℝ} (hz : z∈Icc 0 frameCap) : lowAngle z<9953/10000 := by
  have hmono : MonotoneOn lowAngle (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun z _ => (lowAngle_deriv z).continuousAt.continuousWithinAt
    · exact fun z _ => lowAngle_deriv z
    · intro z hz
      have hh := transport_trig (Ioo_subset_Icc_self hz)
      linarith [hh.1,hh.2.2.2.1]
  have hh := hmono hz ⟨by norm_num [frameCap],le_rfl⟩ hz.2
  have hs := Arithmetic.sin_le_sin9 (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hc := Arithmetic.cos_le_cos8 (show (0:ℝ)≤frameCap by norm_num [frameCap])
  norm_num [Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8,frameCap] at hs hc
  dsimp [lowAngle,frameCap] at hh ⊢
  linarith

theorem low_source_derivative_bound {mu lambda e z : ℝ}
    (hz : z∈Icc 0 frameCap) (hl : 0≤lambda)
    (ha : 0≤lowDualA mu+lambda*Real.cos z)
    (he : (459/1000)*lowDualA mu-lowDualB mu+lambda*(9953/10000)≤e) :
    (lowDualA mu+lambda*Real.cos z)*(b1+1/2)-
      (lowDualB mu-lambda*Real.sin z)*(a1+1/2)≤e*(a1+1/2) := by
  have hr : b1+1/2≤(459/1000)*(a1+1/2) := by
    linarith [b1_precise.2,a1_precise.1]
  have hh := mul_le_mul_of_nonneg_left hr ha
  have hangle := mul_le_mul_of_nonneg_left (lowAngle_bound hz).le hl
  have hraw : (459/1000)*(lowDualA mu+lambda*Real.cos z)-
      (lowDualB mu-lambda*Real.sin z)≤e := by
    dsimp [lowAngle] at hangle
    nlinarith only [he,hangle]
  have hscaled := mul_le_mul_of_nonneg_right hraw
    (show 0≤a1+1/2 by linarith [a1_precise.1])
  nlinarith only [hh,hscaled]

theorem low_source_low_target (s : State) (hs : s.branch=.low)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    2113/2500-(59/25)*a1*Real.cos z+(59/25)*b1*Real.sin z-1/625<
      K s (17/10)-(59/25)*s.a*Real.cos z+(59/25)*s.b*Real.sin z := by
  have tr := transport_trig hz
  have hchart := state_low_chart s hs
  let f : ℝ := lowDualA (17/10)+(59/25)*Real.cos z
  let g : ℝ := lowDualB (17/10)-(59/25)*Real.sin z
  have hf : (253/100:ℝ)<f := by
    dsimp [f,lowDualA,kappa,rho,FrameHighArc.u,FrameLowArc.u]
    linarith [tr.1]
  have hcurv : 2*(7/10)*(a1+1/2)≤f := by linarith [a1_precise.2]
  have hd := low_source_derivative_bound (mu := (17/10:ℝ)) (lambda := (59/25:ℝ))
    (e := (13/200:ℝ)) hz (by norm_num) (show 0≤f by linarith)
    (by norm_num [lowDualA,lowDualB,kappa,rho,FrameHighArc.u,FrameHighArc.v,
      FrameLowArc.u,FrameLowArc.v])
  have hh := circle_endpoint_loss
    (x := s.a+1/2) (t := s.b+1/2) (X := a1+1/2) (T := b1+1/2)
    (a := f) (b := g) (e := (13/200:ℝ)) (k := (7/10:ℝ)) (loss := (1/625:ℝ))
    ((s.outer_eq (by simp [hs,Branch.type])).trans endpoint_circle.symm)
    (by linarith [a1_precise.1]) (by linarith) (by norm_num) hcurv
    (by linarith [hchart.2.2]) hd (by norm_num)
  have hcut := dual_endpoint_constants.1
  rw [K_arc s (by simp [hs,Branch.type]),hs,arcK_low]
  rw [arcK_low,A_b1] at hcut
  rw [← hchart.1]
  dsimp [f,g] at hh
  nlinarith only [hh,hcut]

theorem low_source_nonlow_target (s : State) (hs : s.branch=.low)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    -1673/10000-(93/20)*a1*Real.cos z+(93/20)*b1*Real.sin z<
      K s 5-(93/20)*s.a*Real.cos z+(93/20)*s.b*Real.sin z := by
  have tr := transport_trig hz
  have hchart := state_low_chart s hs
  let f : ℝ := lowDualA 5+(93/20)*Real.cos z
  let g : ℝ := lowDualB 5-(93/20)*Real.sin z
  have hf : 0≤f := by
    dsimp [f,lowDualA,kappa,rho,FrameHighArc.u,FrameLowArc.u]
    linarith [tr.1]
  have hd := low_source_derivative_bound (mu := (5:ℝ)) (lambda := (93/20:ℝ))
    (e := (0:ℝ)) hz (by norm_num) hf
    (by norm_num [lowDualA,lowDualB,kappa,rho,FrameHighArc.u,FrameHighArc.v,
      FrameLowArc.u,FrameLowArc.v])
  have hh := circle_endpoint_min
    (x := s.a+1/2) (t := s.b+1/2) (X := a1+1/2) (T := b1+1/2) (a := f) (b := g)
    ((s.outer_eq (by simp [hs,Branch.type])).trans endpoint_circle.symm)
    (by linarith [a1_precise.1]) hf (by linarith [hchart.2.2]) (by simpa using hd)
  have hcut := dual_endpoint_constants.2.1
  rw [K_arc s (by simp [hs,Branch.type]),hs,arcK_low]
  rw [arcK_low,A_b1] at hcut
  rw [← hchart.1]
  dsimp [f,g] at hh
  nlinarith only [hh,hcut]

theorem sourceNorm_nonnegative (mu lambda z : ℝ) : 0≤ sourceNorm mu lambda z :=
  Real.sqrt_nonneg _

theorem sourceNorm_sq (mu lambda z : ℝ) :
    (sourceNorm mu lambda z)^2=midDualA mu^2+midDualB mu^2+lambda^2+
      2*lambda*(midDualA mu*Real.cos z-midDualB mu*Real.sin z) := by
  rw [sourceNorm,Real.sq_sqrt (by positivity)]
  linear_combination lambda^2*(Real.sin_sq_add_cos_sq z)

theorem middle_source_support (s : State) (hs : s.branch=.middle) (mu lambda z : ℝ) :
    midShiftC mu+(lambda/2)*(Real.cos z-Real.sin z)-R*sourceNorm mu lambda z≤
      K s mu-lambda*s.a*Real.cos z+lambda*s.b*Real.sin z := by
  have hcircle := s.outer_eq (by simp [hs,Branch.type])
  have hh := circle_linear_lower hcircle (-midDualA mu-lambda*Real.cos z)
    (-midDualB mu+lambda*Real.sin z)
  have hnorm : Real.sqrt ((-midDualA mu-lambda*Real.cos z)^2+
      (-midDualB mu+lambda*Real.sin z)^2)=sourceNorm mu lambda z := by
    unfold sourceNorm
    congr 1
    ring
  rw [hnorm] at hh
  rw [K_arc s (by simp [hs,Branch.type]),hs,arcK_middle,
    ← (state_mid_chart s hs).1]
  dsimp [midShiftC]
  nlinarith only [hh]

end SquaresInCircles.Eight.TableFree.GlobalAllHigh.Bridge
