module

public import SquaresInCircles.Eight.Owners.All.HighPotential

/-!
# Eight squares: the whole-arc quadratic reserve in the all-high correction

The low-arc reserve is concave.  Its curvature sign is proved directly
after multiplying by the positive cube of the actual circle radical;
one positive cubic bounds the resulting expression on the entire arc.
The middle reserve is concave up to its intrinsic primary threshold.
Both proofs retain the original marker and actual circle.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalAllHigh

open FramePair FrameCircleArc FrameLowArc FrameMidArc

def arcD (b : ℝ) : ℝ := quadraticR*(A b-1/2)-quadraticS*(b+1/2)
def lowAlpha : ℝ := 4*kappa*rho*quadraticR*(lowK+lowA)
def lowDelta : ℝ := 4*kappa*rho*(lowA*quadraticS-lowB*quadraticR)
def lowGamma : ℝ := 4*kappa*rho*(lowA*quadraticR+lowB*quadraticS)-kappa^2
def lowNu : ℝ := 4*kappa*rho*(-lowK*quadraticS+lowB*quadraticR)+2*kappa
def lowOmega : ℝ := 4*kappa*rho*(-lowK*quadraticR-lowA*quadraticR*Q0)-1

def lowReserve (b : ℝ) : ℝ :=
  lowAlpha*(A b+1/2)+lowDelta*(A b+1/2)*(b+1/2)+
    lowGamma*(b+1/2)^2+lowNu*(b+1/2)+lowOmega
def lowReserveD (b : ℝ) : ℝ :=
  lowAlpha*Ad b+lowDelta*(Ad b*(b+1/2)+(A b+1/2))+2*lowGamma*(b+1/2)+lowNu
def lowReserveDD (b : ℝ) : ℝ :=
  lowAlpha*FrameCircleArc.Add b+lowDelta*(FrameCircleArc.Add b*(b+1/2)+2*Ad b)+2*lowGamma

theorem lowReserve_identity {b : ℝ} (hb : b∈Icc 0 c0) :
    lowReserve b=4*kappa*rho*lowJ b*arcD b-(1-kappa*(b+1/2))^2 := by
  have hc := A_circle hb
  dsimp [lowReserve,lowAlpha,lowDelta,lowGamma,lowNu,lowOmega,lowJ,arcD]
  linear_combination 4*kappa*rho*lowA*quadraticR*hc

theorem lowReserve_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt lowReserve (lowReserveD b) b := by
  have hx := (A_hasDerivAt hb).add_const (1/2)
  have ht := (hasDerivAt_id b).add_const (1/2)
  have h := ((((hx.const_mul lowAlpha).add ((hx.mul ht).const_mul lowDelta)).add
    ((ht.pow 2).const_mul lowGamma)).add (ht.const_mul lowNu)).add_const lowOmega
  convert h using 1
  · funext x
    simp only [lowReserve,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id]
    ring
  · simp only [lowReserveD,id]
    ring

theorem lowReserve_second_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt lowReserveD (lowReserveDD b) b := by
  have hd := Ad_hasDerivAt hb
  have hx := (A_hasDerivAt hb).add_const (1/2)
  have ht := (hasDerivAt_id b).add_const (1/2)
  have h := (((hd.const_mul lowAlpha).add
    (((hd.mul ht).add hx).const_mul lowDelta)).add
    (ht.const_mul (2*lowGamma))).add_const lowNu
  convert h using 1
  · funext x
    simp only [lowReserveD,Pi.add_apply,Pi.mul_apply,id]
  · simp only [lowReserveDD,id]
    ring

theorem low_coefficients :
    (36/5:ℝ)<lowAlpha ∧ -(101/100:ℝ)<lowDelta ∧ lowDelta<0 ∧
      2*lowGamma<(29/10:ℝ) := by
  norm_num [lowAlpha,lowDelta,lowGamma,kappa,rho,quadraticR,quadraticS,
    lowK,lowA,lowB]

/-- Keeping the circle relation in the denominator yields this one
positive cubic; no partition of the original low arc is necessary. -/
theorem low_curvature_polynomial {t : ℝ} (ht : 1/2≤t) :
    0<(36/5)*Q0-(101/100)*t*(3*Q0-2*t^2)-
      (29/10)*(383/200)*(Q0-t^2) := by
  have hw : 0≤t-1/2 := by linarith
  have h3 := pow_nonneg hw 3
  have hs := sq_nonneg (t-1/2-24/85)
  dsimp [Q0]
  nlinarith only [h3,hs,sq_nonneg (t-1/2),hw]

theorem lowReserve_second_negative {b : ℝ} (hb : b∈Icc 0 b1) :
    lowReserveDD b<0 := by
  have hdom : b∈Icc 0 c0 := ⟨hb.1,hb.2.trans b1_mem.2⟩
  obtain ⟨x,hxdef⟩ : ∃ x,x=A b+1/2 := ⟨_,rfl⟩
  obtain ⟨t,htdef⟩ : ∃ t,t=b+1/2 := ⟨_,rfl⟩
  have hx : 0<x := hxdef ▸ A_shift_pos hdom
  have hx3 : 0<x^3 := pow_pos hx 3
  have hcircle : x^2+t^2=Q0 := by rw [hxdef,htdef]; exact A_circle hdom
  have hxu : x<383/200 := by
    have hh := (A_bounds hdom).2
    rw [hxdef]
    linarith [a0_bounds.2]
  have ht : 1/2≤t := by rw [htdef]; linarith [hb.1]
  have htu : t<8247/10000 := by
    rw [htdef]
    have hb1 : b1<3247/10000 := by dsimp [b1]; linarith [a1_precise.2]
    linarith [hb.2]
  have ht2 := pow_le_pow_left₀ (by linarith : 0≤t) htu.le 2
  have hfactor : 0<t*(3*Q0-2*t^2) := by
    apply mul_pos (by linarith)
    norm_num [Q0] at ht2 ⊢
    linarith
  have hbase := low_curvature_polynomial ht
  have hnum₁ := mul_lt_mul_of_pos_right low_coefficients.1 (by norm_num [Q0] : 0<Q0)
  have hnum₂ := mul_lt_mul_of_pos_right low_coefficients.2.1 hfactor
  have hgamma := mul_lt_mul_of_pos_right low_coefficients.2.2.2 hx3
  have hcube := mul_le_mul_of_nonneg_right hxu.le (sq_nonneg x)
  have hreserve : 2*lowGamma*x^3<
      lowAlpha*Q0+lowDelta*t*(3*Q0-2*t^2) := by
    nlinarith only [hbase,hnum₁,hnum₂,hgamma,hcube,hcircle]
  have hid₀ : lowReserveDD b*x^3=
      2*lowGamma*x^3-lowAlpha*Q0-lowDelta*t*(Q0+2*x^2) := by
    rw [lowReserveDD,Ad,FrameCircleArc.Add,← hxdef,← htdef]
    field_simp
    ring
  have hid₁ : Q0+2*x^2=3*Q0-2*t^2 := by linarith [hcircle]
  rw [hid₁] at hid₀
  have hnegative : lowReserveDD b*x^3<0 := by linarith
  exact neg_of_mul_neg_left hnegative hx3.le

theorem lowReserve_concave : ConcaveOn ℝ (Icc 0 b1) lowReserve := by
  apply concave_of_deriv2
    (fun b hb => lowReserve_derivative ⟨hb.1,hb.2.trans b1_mem.2⟩)
    (fun b hb => lowReserve_second_derivative ⟨hb.1,hb.2.trans b1_mem.2⟩)
  exact fun b hb => (lowReserve_second_negative hb).le

theorem low_arcD_positive {b : ℝ} (hb : b∈Icc 0 b1) : 0<arcD b := by
  have ha := (A_low_bounds hb).1
  have hbu : b1<3247/10000 := by dsimp [b1]; linarith [a1_precise.2]
  dsimp [arcD,quadraticR,quadraticS]
  linarith [a1_precise.1,hb.2]

theorem lowReserve_zero : 0<lowReserve 0 := by
  rw [lowReserve_identity ⟨le_rfl,by linarith [c0_bounds.1]⟩]
  have hj := lowJ_zero
  have hD : quadraticR*(91457/100000)-quadraticS/2<arcD 0 := by
    simp only [arcD,A_zero,zero_add]
    dsimp [quadraticR,quadraticS]
    linarith [a0_bounds.1]
  have hp := mul_nonneg (sub_nonneg.mpr hj.le) (sub_nonneg.mpr hD.le)
  dsimp [kappa,rho,quadraticR,quadraticS] at *
  nlinarith only [hj,hD,hp]

theorem lowReserve_b1 : 0<lowReserve b1 := by
  rw [lowReserve_identity b1_mem]
  have hj := lowJ_b1
  have hbu : b1<3247/10000 := by dsimp [b1]; linarith [a1_precise.2]
  have hbl : (3246/10000:ℝ)<b1 := by dsimp [b1]; linarith [a1_precise.1]
  have hD : quadraticR*(7984/10000)-quadraticS*(8247/10000)<arcD b1 := by
    rw [arcD,A_b1]
    dsimp [quadraticR,quadraticS]
    linarith [a1_precise.1]
  have hp := mul_nonneg (sub_nonneg.mpr hj.le) (sub_nonneg.mpr hD.le)
  have hsq : (1-kappa*(b1+1/2))^2≤(1-kappa*(8246/10000))^2 := by
    have hnonneg : 0≤1-kappa*(b1+1/2) := by dsimp [kappa]; linarith
    have hle : 1-kappa*(b1+1/2)≤1-kappa*(8246/10000) := by dsimp [kappa]; linarith
    exact pow_le_pow_left₀ hnonneg hle 2
  dsimp [kappa,rho,quadraticR,quadraticS] at *
  nlinarith only [hj,hD,hp,hsq]

theorem lowReserve_positive {b : ℝ} (hb : b∈Icc 0 b1) : 0<lowReserve b :=
  concave_gt_of_endpoints lowReserve_concave hb lowReserve_zero lowReserve_b1

def midQuadratic (b : ℝ) : ℝ := midJ b-(1-kappa*(b+1/2))^2
def midQuadraticD (b : ℝ) : ℝ := -midA*Ad b-midB+2*kappa*(1-kappa*(b+1/2))
def midQuadraticDD (b : ℝ) : ℝ := -midA*FrameCircleArc.Add b-2*kappa^2

theorem threshold_domain : b1<primaryThreshold ∧ primaryThreshold<b2 := by
  dsimp [primaryThreshold,kappa]
  constructor <;> linarith [b1_bounds.2,b2_bounds.1]

theorem threshold_root_lower {b : ℝ} (hb : b∈Icc 0 primaryThreshold) :
    (43/25:ℝ)<A b+1/2 := by
  have hdom : b∈Icc 0 c0 := ⟨hb.1,hb.2.trans (threshold_domain.2.le.trans b2_mem.2)⟩
  have hc := A_circle hdom
  have hx := A_shift_pos hdom
  have ht : b+1/2≤100/103 := by dsimp [primaryThreshold,kappa] at hb; linarith [hb.2]
  have hs := pow_le_pow_left₀ (by linarith [hb.1] : 0≤b+1/2) ht 2
  norm_num [Q0] at hc hs
  nlinarith

theorem midQuadratic_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt midQuadratic (midQuadraticD b) b := by
  have h := (midJ_derivative hb).sub
    (((((hasDerivAt_id b).add_const (1/2)).const_mul kappa).const_sub 1).pow 2)
  convert h using 1
  · funext x
    simp only [midQuadratic,Pi.sub_apply,Pi.pow_apply,id]
  · simp only [midQuadraticD,id]
    push_cast
    ring

theorem midQuadratic_second_derivative {b : ℝ} (hb : b∈Icc 0 c0) :
    HasDerivAt midQuadraticD (midQuadraticDD b) b := by
  have h := (((Ad_hasDerivAt hb).const_mul (-midA)).sub_const midB).add
    (((((hasDerivAt_id b).add_const (1/2)).const_mul kappa).const_sub 1).const_mul
      (2*kappa))
  convert h using 1
  · funext x
    simp only [midQuadraticD,Pi.add_apply,id]
  · simp only [midQuadraticDD]
    ring

theorem midQuadratic_concave : ConcaveOn ℝ (Icc b1 primaryThreshold) midQuadratic := by
  have hdom (b : ℝ) (hb : b∈Icc b1 primaryThreshold) : b∈Icc 0 c0 :=
    ⟨b1_mem.1.trans hb.1,hb.2.trans (threshold_domain.2.le.trans b2_mem.2)⟩
  apply concave_of_deriv2 (fun b hb => midQuadratic_derivative (hdom b hb))
    (fun b hb => midQuadratic_second_derivative (hdom b hb))
  intro b hb
  have hx := A_shift_pos (hdom b hb)
  have hl := threshold_root_lower ⟨b1_mem.1.trans hb.1,hb.2⟩
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤43/25) hl.le 3
  have hcoef : midA*Q0≤2*kappa^2*(A b+1/2)^3 := by
    dsimp [midA,Q0,kappa] at *
    norm_num at hcube
    linarith
  have hid : midQuadraticDD b=midA*Q0/(A b+1/2)^3-2*kappa^2 := by
    rw [midQuadraticDD,FrameCircleArc.Add]
    ring
  rw [hid]
  have hq := (div_le_iff₀ (pow_pos hx 3)).2 hcoef
  linarith

theorem midQuadratic_b1 : 0< midQuadratic b1 := by
  have hj : (7/250:ℝ)< midJ b1 := by
    rw [midJ,A_b1]
    have hb : b1<(3247/10000:ℝ) := by dsimp [b1]; linarith [a1_precise.2]
    dsimp [midK,midA,midB]
    linarith [a1_precise.2]
  have hbL : (3246/10000:ℝ)<b1 := by dsimp [b1]; linarith [a1_precise.1]
  have hbU : b1<3247/10000 := by dsimp [b1]; linarith [a1_precise.2]
  have hsq : (1-kappa*(b1+1/2))^2≤(1-kappa*(8246/10000))^2 := by
    apply pow_le_pow_left₀
    · dsimp [kappa]; linarith
    · dsimp [kappa]; linarith
  dsimp [midQuadratic,kappa] at *
  nlinarith only [hj,hsq]

theorem midQuadratic_threshold : 0< midQuadratic primaryThreshold := by
  have hb : primaryThreshold∈Icc 0 c0 :=
    ⟨b1_mem.1.trans threshold_domain.1.le,threshold_domain.2.le.trans b2_mem.2⟩
  have hh := midJ_positive hb
  have hz : 1-kappa*(primaryThreshold+1/2)=0 := by norm_num [primaryThreshold,kappa]
  rw [midQuadratic,hz]
  simpa using hh

theorem midQuadratic_positive {b : ℝ} (hb : b∈Icc b1 primaryThreshold) :
    0< midQuadratic b :=
  concave_gt_of_endpoints midQuadratic_concave hb midQuadratic_b1 midQuadratic_threshold

/-- The complete marker reserve for the negative original secondary
quarter; all admissible lower-chart states are included. -/
theorem correction_quadratic (s : State) (hs : s.branch.type≠0)
    (hb : s.b<primaryThreshold) :
    0<quadraticD s ∧
      (1-kappa*(s.b+1/2))^2<4*kappa*rho*J s*quadraticD s := by
  cases hbr : s.branch with
  | coreSide | coreCorner => simp [hbr,Branch.type] at hs
  | low =>
      have hc := state_low_chart s hbr
      have hD : quadraticD s=arcD s.b := by rw [quadraticD,hc.1]; rfl
      have hp := low_arcD_positive hc.2
      have hR := lowReserve_positive hc.2
      rw [lowReserve_identity ⟨hc.2.1,hc.2.2.trans b1_mem.2⟩] at hR
      have hJ := lowJ_below_original s hbr
      have hprod := mul_lt_mul_of_pos_right hJ hp
      rw [hD]
      refine ⟨hp,?_⟩
      dsimp [kappa,rho] at *
      nlinarith only [hR,hprod]
  | middle =>
      have hc := state_mid_chart s hbr
      have hl := threshold_root_lower ⟨s.b_nonneg,hb.le⟩
      have hD : (23/100:ℝ)<quadraticD s := by
        rw [quadraticD,hc.1]
        dsimp [quadraticR,quadraticS,primaryThreshold,kappa] at *
        linarith
      have hQ := midQuadratic_positive ⟨hc.2.1,hb.le⟩
      have hJ := midJ_below_original s hbr
      have hJstrong : (1-kappa*(s.b+1/2))^2<J s := by
        dsimp [midQuadratic] at hQ
        linarith
      have hJpos : 0<J s := (sq_nonneg _).trans_lt hJstrong
      have hp := mul_lt_mul_of_pos_left hD hJpos
      refine ⟨by linarith,?_⟩
      dsimp [kappa,rho] at *
      nlinarith only [hp,hJstrong,hJpos]
  | high =>
      have hc := (FrameHighArc.state_high_chart s hbr).2.1
      linarith [threshold_domain.2]

end SquaresInCircles.Eight.GlobalAllHigh
