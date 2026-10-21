module

public import SquaresInCircles.Eight.TableFree.GlobalBTNominal
public import SquaresInCircles.Eight.TableFree.DirectedPowerBounds

/-!
# The full high-chart scalar in the linear-A return bound

The remaining high-chart radical is eliminated by one positive square.
Its degree-six polynomial has one centered quadratic certificate on
the whole interval [0,.3].  This replaces the second-derivative and
reference-root calculation while keeping the original marker.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open Polynomial FramePair FrameCircleArc FrameMidArc
open GlobalOuterAnchor GlobalZeroSign GlobalQuarterSign

def returnCut : ℝ := 29843/50000
def returnDistance (z : ℝ) : ℝ :=
  238500487341/250000000000-(249557/500000)*z-(9/200)*z^2-(3/200)*z^3

namespace ReturnPolynomial

def distance : ℚ[X] := C (238500487341/250000000000)-C (249557/500000)*X-
  C (9/200)*X^2-C (3/200)*X^3
def square : ℚ[X] := distance^2-C ((8898/15625)^2)*
  (C (9789/2500)-(C (29843/50000+1/2)+X)^2)
def centered : ℚ[X] := DirectedPowerBounds.shift (12157/50000) square

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_identity : centered=C (centered.coeff 0)+C (centered.coeff 1)*X+
    C (centered.coeff 2)*X^2+PowerTailBounds.tail centered 3 4 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem centered_reserves : (1/1000:ℚ)<centered.coeff 0 ∧
    |centered.coeff 1|<1/10000 ∧
    0≤centered.coeff 2-PowerTailBounds.norm centered 3 4 (1/4) := by decide

theorem square_positive {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) : 0<aeval z square := by
  have hx : |z-(12157/50000:ℝ)|≤1/4 := by rw [abs_le]; constructor <;> linarith [hz.1,hz.2]
  have hl := PowerTailBounds.quadratic_lower centered_identity
    (by norm_num : (0:ℚ)≤1/4) hx
  have h0 : (1/1000:ℝ)<(centered.coeff 0:ℝ) := by exact_mod_cast centered_reserves.1
  have h1 : |(centered.coeff 1:ℝ)|≤(1/10000:ℝ) := by
    exact_mod_cast centered_reserves.2.1.le
  have h2 : 0≤(centered.coeff 2:ℝ)-(PowerTailBounds.norm centered 3 4 (1/4):ℝ) := by
    exact_mod_cast centered_reserves.2.2
  have hprod := mul_le_mul h1 hx (abs_nonneg (z-(12157/50000:ℝ)))
    (by norm_num : (0:ℝ)≤1/10000)
  have hlin : -(1/40000:ℝ)≤(centered.coeff 1:ℝ)*(z-12157/50000) := by
    rw [← abs_mul] at hprod
    have hh := (abs_le.mp hprod).1
    norm_num at hh
    exact hh
  have hquad := mul_nonneg h2 (sq_nonneg (z-(12157/50000:ℝ)))
  have he : aeval (z-12157/50000) centered=aeval z square := by
    simp only [centered,DirectedPowerBounds.shift_eval]
    congr 1
    norm_num
    ring
  rw [he] at hl
  linarith

theorem distance_eval (z : ℝ) : aeval z distance=returnDistance z := by
  simp [distance,returnDistance]

theorem square_eval (z : ℝ) : aeval z square=
    (returnDistance z)^2-FrameHighArc.u^2*(Q0-(returnCut+z+1/2)^2) := by
  simp only [square,map_sub,map_mul,map_pow,aeval_C,aeval_X,distance_eval]
  norm_num [FrameHighArc.u,Q0,returnCut] <;> ring

end ReturnPolynomial

theorem return_distance_positive {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ)) :
    0<returnDistance z := by
  have h2 := pow_le_pow_left₀ hz.1 hz.2 2
  have h3 := pow_le_pow_left₀ hz.1 hz.2 3
  dsimp [returnDistance]
  norm_num at h2 h3
  nlinarith [hz.2]

theorem return_root_comparison {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ))
    (hb : returnCut+z∈Icc 0 c0) :
    FrameHighArc.u*(A (returnCut+z)+1/2)<returnDistance z := by
  have hp := ReturnPolynomial.square_positive hz
  rw [ReturnPolynomial.square_eval] at hp
  have hc := A_circle hb
  have ha := A_shift_pos hb
  have hd := return_distance_positive hz
  dsimp [FrameHighArc.u] at *
  nlinarith

theorem frameCost_cubic_lower {z : ℝ} (hz : 0≤z) :
    z/2-z^2/4-z^3/12≤frameCost z := by
  have hs := sin_lower_three hz
  have hc := cos_lower_two hz
  dsimp [frameCost]
  linarith

theorem return_distance_identity (z : ℝ) :
    returnDistance z=3*(8833/10000)+(314159/100000)/4+
      (FrameHighArc.u-FrameHighArc.v)*(449607/500000)-
      (kappa-FrameHighArc.v)*(returnCut+z)+FrameHighArc.u/2+
      (9/50)*(z/2-z^2/4-z^3/12)-returnThreshold := by
  norm_num [returnDistance,returnCut,FrameHighArc.u,FrameHighArc.v,
    kappa,returnThreshold] <;> ring

theorem high_short_scalar {z : ℝ} (hz : z∈Icc 0 (3/10:ℝ))
    (hb : returnCut+z∈Icc 0 c0) :
    returnThreshold<3*(8833/10000)+FrameHighArc.H (returnCut+z)-
      kappa*(returnCut+z)+(9/50)*frameCost z := by
  have hh := return_root_comparison hz hb
  rw [return_distance_identity] at hh
  have hw := frameCost_cubic_lower hz.1
  have hc := FrameHighArc.diagonal_bounds.1
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [FrameHighArc.H,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v] at hh ⊢
  nlinarith only [hh,hw,hc,hp]

theorem returnCut_mem : returnCut∈Icc b2 c0 := by
  dsimp [returnCut]
  constructor <;> linarith [b2_bounds.2,c0_bounds.1]

theorem high_return_below_cut {b gain : ℝ} (hb : b∈Icc b2 c0)
    (hcut : b≤returnCut) (hg : 0≤gain) :
    returnThreshold<3*(8833/10000)+FrameHighArc.H b-kappa*b+(9/50)*gain := by
  have hzero := high_short_scalar (z := 0) (by norm_num)
    (by simpa using And.intro (b2_mem.1.trans returnCut_mem.1) returnCut_mem.2)
  simp only [add_zero,frameCost_zero,mul_zero] at hzero
  have hmono := FrameHighArc.loss_antitone
    (lambda := kappa) (by norm_num [kappa,FrameHighArc.u,FrameHighArc.v])
    hb returnCut_mem hcut
  linarith

theorem high_return_large {b gain : ℝ} (hb : b∈Icc b2 c0)
    (hg : frameCost (3/10)≤gain) :
    returnThreshold<3*(8833/10000)+FrameHighArc.H b-kappa*b+(9/50)*gain := by
  have hmono := FrameHighArc.loss_antitone
    (lambda := kappa) (by norm_num [kappa,FrameHighArc.u,FrameHighArc.v])
    hb ⟨b2_mem.2,le_rfl⟩ hb.2
  rw [FrameHighArc.H_c0] at hmono
  have hw := frameCost_cubic_lower (by norm_num : (0:ℝ)≤3/10)
  have hc := FrameHighArc.diagonal_bounds.2
  have hp := Arithmetic.pi_hand_enclosure.1
  dsimp [returnThreshold,kappa] at *
  norm_num at hw
  linarith

/-- The entire scalar return reserve.  The short-error premise is the
actual three-projection endpoint inequality proved in GlobalBTNominal. -/
theorem return_marker_reserve (s : State) {R gain : ℝ}
    (hR : 0≤R) (hgain : frameCost (min R (3/10))≤gain)
    (hendpoint : R≤3/10 → s.b≤4*c0-3+R) :
    returnThreshold<3*(8833/10000)+ZeroPrimary.unsigned s-kappa*s.b+(9/50)*gain := by
  have hg0 : 0≤gain := by
    have hz : min R (3/10)∈Icc 0 (Real.pi/4) :=
      ⟨le_min hR (by norm_num),by linarith [min_le_right R (3/10:ℝ),Real.pi_gt_three]⟩
    exact (frameCost_nonneg hz).trans hgain
  cases hs : s.branch with
  | coreSide | coreCorner =>
      have hc : s.branch.type=0 := by simp [hs,Branch.type]
      have ha := (core_bounds s hc).1
      have hb := s.b_nonneg
      dsimp [ZeroPrimary.unsigned]
      rw [hs]
      dsimp [FramePair.label,kappa,returnThreshold]
      nlinarith
  | low =>
      have hm := marker_linear_lower s
      have ht : 4*s.b≤s.a := by simpa [hs,TypeMem] using s.type_mem
      have hu := (ZeroPrimary.coordinates s).2.1
      dsimp [kappa,returnThreshold]
      linarith
  | middle =>
      have hm := marker_linear_lower s
      have htype : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by
        simpa [hs,TypeMem] using s.type_mem
      have ht := htype.2
      have hu := (ZeroPrimary.coordinates s).2.1
      dsimp [kappa,returnThreshold]
      linarith
  | high =>
      have hb := FrameHighArc.state_high_chart s hs
      have hlabel : ZeroPrimary.unsigned s=FrameHighArc.H s.b := by
        dsimp [ZeroPrimary.unsigned]
        rw [hs,hb.1]
        dsimp [FramePair.label,FrameHighArc.H,FrameHighArc.k,
          FrameHighArc.u,FrameHighArc.v]
        ring
      rw [hlabel]
      by_cases hlarge : 3/10≤R
      · apply high_return_large hb.2
        simpa only [min_eq_right hlarge] using hgain
      · have hsmall : R≤3/10 := le_of_not_ge hlarge
        have he := hendpoint hsmall
        by_cases hcut : s.b≤returnCut
        · exact high_return_below_cut hb.2 hcut hg0
        · have hz0 : 0≤s.b-returnCut := by linarith
          have hzR : s.b-returnCut≤R := by
            have hc := FrameHighArc.diagonal_bounds.2
            dsimp [returnCut]
            linarith
          have hz : s.b-returnCut∈Icc 0 (3/10:ℝ) := ⟨hz0,hzR.trans hsmall⟩
          have hpoint : returnCut+(s.b-returnCut)=s.b := by ring
          have hscalar := high_short_scalar hz
            (by rw [hpoint]; exact ⟨b2_mem.1.trans hb.2.1,hb.2.2⟩)
          rw [hpoint] at hscalar
          have hm := frameCost_monotone
            (show s.b-returnCut∈Icc 0 (Real.pi/4) from
              ⟨hz0,by linarith [hz.2,Real.pi_gt_three]⟩)
            (show R∈Icc 0 (Real.pi/4) from
              ⟨hR,by linarith [hsmall,Real.pi_gt_three]⟩) hzR
          rw [min_eq_left hsmall] at hgain
          linarith

end SquaresInCircles.Eight.TableFree.GlobalBT
