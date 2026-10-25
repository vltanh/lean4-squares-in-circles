module

public import SquaresInCircles.Eight.Frames.High.Arc
public import SquaresInCircles.Eight.Frames.Pair.Shape

/-!
# Eight squares: explicit source-contact calculus in the parallel strip

At a fixed original target, contact determines the source transverse
coordinate explicitly.  The circle markers are evaluated on slightly
enlarged scalar domains.  All derivative signs below are proved from
the actual target arc and the displayed source-coordinate bounds.
-/

section
/-!
## Whole-arc source supports for the low/middle frame pair

The two intrinsic cuts are exact intersections with the original circle.
The estimates below retain both endpoints.  In particular the negative
low-source loss is proved directly from the circle equation, without a
partition of the arc or an assumption about a minimizing point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidArc
open FramePair FrameCircleArc FrameLowArc FrameMidArc FramePairCalculus

theorem a0_precise :
    (1414575670/1000000000:ℝ)<a0 ∧ a0<1414575672/1000000000 := by
  have hs := Real.sq_sqrt (show 0≤Q0-1/4 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (Q0-1/4)
  dsimp [a0,Q0] at *
  constructor <;> nlinarith

theorem radius_precise :
    (1978787507/1000000000:ℝ)<R ∧ R<1978787508/1000000000 := by
  have hs := R_sq
  have hn := R_pos
  norm_num [Q0] at hs
  constructor <;> nlinarith

theorem b1_precise :
    (1298747247/4000000000:ℝ)<b1 ∧ b1<1298747249/4000000000 := by
  dsimp [b1]
  constructor <;> linarith [a1_precise.1,a1_precise.2]

theorem b2_precise :
    (513966882/1000000000:ℝ)<b2 ∧ b2<128491721/250000000 := by
  dsimp [b2]
  constructor <;> linarith [a2_bounds.1,a2_bounds.2]

theorem L1_precise : (15341/50000:ℝ)<L1 ∧ L1<30683/100000 := by
  have ha0 := a0_precise
  have ha1 := a1_precise
  dsimp [L1,b1,FrameLowArc.u,FrameLowArc.v]
  constructor <;> linarith

theorem low_positive_source {b : ℝ} (hb : b∈Icc 0 b1) :
    -(1/100000:ℝ)≤L b-(189/200)*b := by
  apply label_loss_lower hb (by norm_num)
  linarith [L1_precise.1,b1_precise.2]

/-- A circle chord bounds the full low marker from above.  The quadratic
remainder supplies the small loss for the negative source sign. -/
theorem low_quadratic_upper {b : ℝ} (hb : b∈Icc 0 b1) :
    L b≤(9837/10000)*b-(1/10)*b^2 := by
  have ha := A_low_bounds hb
  have hc := A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hc0 := A_circle (show (0:ℝ)∈Icc 0 c0 from
    ⟨le_rfl,by linarith [c0_bounds.1]⟩)
  rw [A_zero] at hc0
  have hd : 0≤a0-A b := sub_nonneg.mpr ha.2
  have he : (a0-A b)*(A b+a0+1)=b+b^2 := by nlinarith [hc,hc0]
  have hcoef : (527/5000)*(A b+a0+1)≤FrameLowArc.u := by
    dsimp [FrameLowArc.u]
    linarith [ha.2,a0_precise.2]
  have hm := mul_le_mul_of_nonneg_left hcoef hd
  have he' : (a0-A b)*((527/5000)*(A b+a0+1))=
      (527/5000)*(b+b^2) := by rw [← he]; ring
  rw [he'] at hm
  dsimp [L,FrameLowArc.v]
  nlinarith [sq_nonneg b,hb.1]

theorem low_negative_source {b : ℝ} (hb : b∈Icc 0 b1) :
    -(1/25000:ℝ)≤-L b+(49/50)*b := by
  have hh := low_quadratic_upper hb
  nlinarith [sq_nonneg (b-37/2000)]

theorem low_unit_source {b : ℝ} (hb : b∈Icc 0 b1) :
    0≤-L b+b := by linarith [(L_bounds hb).2.1]

theorem middle_endpoint_slope :
    (797/1000)*(b2-b1)<M2-M1 ∧ M2-M1<(4/5)*(b2-b1) := by
  have he := M_endpoints
  have h1 := b1_precise
  have h2 := b2_precise
  constructor <;> linarith

theorem middle_loss_endpoints {b lam : ℝ} (hb : b∈Icc b1 b2) :
    min (M1-lam*b1) (M2-lam*b2)≤M b-lam*b := by
  have hh := linear_endpoint_lower (p := FrameMidArc.p) (q := FrameMidArc.q-lam)
    (by norm_num [FrameMidArc.p]) b1_mem.1 b2_mem.2 hb
  simp only [linear,A_b1,A_b2] at hh
  have h1 : min (M1-lam*b1) (M2-lam*b2)-cM≤
      FrameMidArc.p*a1+(FrameMidArc.q-lam)*b1 := by
    have hh := min_le_left (M1-lam*b1) (M2-lam*b2)
    have hM : M1=cM+FrameMidArc.p*a1+FrameMidArc.q*b1 := rfl
    linarith
  have h2 : min (M1-lam*b1) (M2-lam*b2)-cM≤
      FrameMidArc.p*a2+(FrameMidArc.q-lam)*b2 := by
    have hh := min_le_right (M1-lam*b1) (M2-lam*b2)
    have hM : M2=cM+FrameMidArc.p*a2+FrameMidArc.q*b2 := rfl
    linarith
  have hm := (le_min h1 h2).trans hh
  dsimp [M]
  linarith

theorem middle_positive_source {b lam : ℝ} (hb : b∈Icc b1 b2)
    (hlam : (4/5:ℝ)≤lam) : M2-lam*b2≤M b-lam*b := by
  have hm := mul_le_mul_of_nonneg_right hlam (sub_nonneg.mpr b1_lt_b2.le)
  have hord : M2-lam*b2≤M1-lam*b1 := by
    nlinarith [middle_endpoint_slope.2]
  simpa only [min_eq_right hord] using middle_loss_endpoints (lam := lam) hb

theorem middle_positive_source_rational {b lam : ℝ} (hb : b∈Icc b1 b2)
    (hlam : (4/5:ℝ)≤lam) :
    (911/2000:ℝ)-lam*(128491721/250000000)≤M b-lam*b := by
  have hh := middle_positive_source hb hlam
  have hm := mul_le_mul_of_nonneg_left b2_precise.2.le (by linarith : 0≤lam)
  linarith [M_endpoints.2.2.1]

theorem middle_small_source {b : ℝ} (hb : b∈Icc b1 b2) :
    M1-(797/1000)*b1≤M b-(797/1000)*b := by
  have hord : M1-(797/1000)*b1≤M2-(797/1000)*b2 := by
    linarith [middle_endpoint_slope.1]
  simpa only [min_eq_left hord] using middle_loss_endpoints (lam := (797/1000:ℝ)) hb

theorem middle_negative_source {b lam : ℝ} (hb : b∈Icc b1 b2)
    (hlam : (1:ℝ)≤lam) : -M1+lam*b1≤-M b+lam*b := by
  have hm : MonotoneOn (fun z => -M z+lam*z) (Icc b1 b2) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact ((M_deriv hz).neg.add
        ((hasDerivAt_id z).const_mul lam)).continuousAt.continuousWithinAt
    · intro z hz
      exact (M_deriv (Ioo_subset_Icc_self hz)).neg.add ((hasDerivAt_id z).const_mul lam)
    · intro z hz
      linarith [(Md_bounds (Ioo_subset_Icc_self hz)).2]
  simpa only [M_b1] using hm ⟨le_rfl,b1_lt_b2.le⟩ hb hb.1

theorem low_primary_source {b lam : ℝ} (hb : b∈Icc 0 b1)
    (hlam : lam∈Icc (0:ℝ) 1) : -L1-lam*a1≤-L b-lam*A b := by
  have hm : AntitoneOn (fun z => -L z-lam*A z) (Icc 0 b1) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact ((L_hasDerivAt hz).neg.sub
        ((A_hasDerivAt ⟨hz.1,hz.2.trans b1_mem.2⟩).const_mul
          lam)).continuousAt.continuousWithinAt
    · intro z hz
      exact (L_hasDerivAt (Ioo_subset_Icc_self hz)).neg.sub
        ((A_hasDerivAt ⟨hz.1.le,hz.2.le.trans b1_mem.2⟩).const_mul lam)
    · intro z hz
      have hr := slope_bounds (Ioo_subset_Icc_self hz)
      have hmul := mul_le_mul_of_nonneg_left hlam.2
        (by linarith [hr.1] : 0≤FrameLowArc.slope z)
      have hAd : Ad z= -FrameLowArc.slope z := by
        simp only [Ad,FrameLowArc.slope,neg_div]
      rw [hAd]
      dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
      linarith
  simpa only [L_b1,A_b1] using hm hb ⟨b1_mem.1,le_rfl⟩ hb.2

theorem middle_primary_source {b lam : ℝ} (hb : b∈Icc b1 b2)
    (hlam : lam∈Icc (0:ℝ) 1) : -M2-lam*a2≤-M b-lam*A b := by
  have hm : AntitoneOn (fun z => -M z-lam*A z) (Icc b1 b2) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact ((M_deriv hz).neg.sub
        ((A_hasDerivAt ⟨b1_mem.1.trans hz.1,hz.2.trans b2_mem.2⟩).const_mul
          lam)).continuousAt.continuousWithinAt
    · intro z hz
      exact (M_deriv (Ioo_subset_Icc_self hz)).neg.sub
        ((A_hasDerivAt ⟨b1_mem.1.trans hz.1.le,hz.2.le.trans b2_mem.2⟩).const_mul lam)
    · intro z hz
      have hr := slope_mid_bounds (Ioo_subset_Icc_self hz)
      have hmul := mul_le_mul_of_nonneg_left hlam.2
        (by linarith [hr.1] : 0≤FrameLowArc.slope z)
      have hAd : Ad z= -FrameLowArc.slope z := by
        simp only [Ad,FrameLowArc.slope,neg_div]
      rw [hAd]
      dsimp [Md,FrameMidArc.p,FrameMidArc.q]
      linarith
  simpa only [M_b2,A_b2] using hm hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2

end SquaresInCircles.Eight.FrameLowMidArc
end
end
end

section
/-!
## Circle calculus for the complete low/high pair

The ordinary low and high arcs and the continued circle used at a
quarter-turn contact share the same exact shifted-circle chart.
The continued interval is analytic data only; actual states retain
their original intrinsic type cuts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighArc
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc

def extendedDomain : Set ℝ := Icc (-(1/4:ℝ)) (6/5)
def slopeD (b : ℝ) : ℝ := Q0/(A b+1/2)^3
def G (b : ℝ) : ℝ := Real.pi/4-(FrameHighArc.u-FrameHighArc.v)*c0-
  FrameHighArc.v*A b+FrameHighArc.u*b
def Gd (b : ℝ) : ℝ := FrameHighArc.v*slope b+FrameHighArc.u
def Gdd (b : ℝ) : ℝ := FrameHighArc.v*slopeD b

theorem diagonal_precise : (179842813/200000000:ℝ)<c0 ∧ c0<449607033/500000000 := by
  have hc := c0_circle
  have hp := c0_bounds.1
  norm_num [Q0] at hc
  constructor <;> by_contra! hbad <;> nlinarith

theorem high_constant_lower : (9459/10000:ℝ)<FrameHighArc.k := by
  dsimp [FrameHighArc.k,FrameHighArc.u,FrameHighArc.v]
  linarith [diagonal_precise.1,Arithmetic.pi_hand_enclosure.1]

theorem high_label_endpoint : (23197/50000:ℝ)<FrameHighArc.H2 := by
  have hp := Arithmetic.pi_hand_enclosure.1
  have hc := diagonal_precise.1
  have ha := a2_bounds
  dsimp [FrameHighArc.H2,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,b2]
  linarith

theorem extended_radicand {b : ℝ} (hb : b∈extendedDomain) :
    0<Q0-(b+1/2)^2 := by
  have hbl : (1/4:ℝ)≤b+1/2 := by dsimp [extendedDomain] at hb; linarith [hb.1]
  have hbu : b+1/2≤17/10 := by dsimp [extendedDomain] at hb; linarith [hb.2]
  have hh := pow_le_pow_left₀ (by linarith : 0≤b+1/2) hbu 2
  norm_num [Q0]
  nlinarith

theorem extended_shift_pos {b : ℝ} (hb : b∈extendedDomain) : 0<A b+1/2 := by
  simpa [A] using Real.sqrt_pos.mpr (extended_radicand hb)

theorem extended_circle {b : ℝ} (hb : b∈extendedDomain) :
    (A b+1/2)^2+(b+1/2)^2=Q0 := by
  have hh := Real.sq_sqrt (extended_radicand hb).le
  dsimp [A]
  nlinarith

theorem extended_A_deriv {b : ℝ} (hb : b∈extendedDomain) : HasDerivAt A (Ad b) b := by
  have hh := ((hasDerivAt_const b Q0).sub
    (((hasDerivAt_id b).add_const (1/2)).pow 2)).sqrt (extended_radicand hb).ne'
  convert hh.sub_const (1/2) using 1
  · rfl
  · dsimp [Ad,A]; ring

theorem extended_Ad_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt Ad (Add b) b := by
  have hd := extended_A_deriv hb
  have hn := (extended_shift_pos hb).ne'
  have hc := extended_circle hb
  have hh := (((hasDerivAt_id' b).add_const (1/2)).fun_neg).fun_div (hd.add_const (1/2)) hn
  unfold Ad
  convert hh using 1
  simp only [FrameCircleArc.Add,Ad]
  rw [← hc]
  field_simp
  ring

theorem slope_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt slope (slopeD b) b := by
  have he : FrameLowArc.slope=fun y => -Ad y := by
    funext y
    simp only [FrameLowArc.slope,Ad,neg_div,neg_neg]
  rw [he]
  convert (extended_Ad_deriv hb).fun_neg using 1
  simp only [slopeD,FrameCircleArc.Add,neg_div,neg_neg]

theorem slopeD_positive {b : ℝ} (hb : b∈extendedDomain) : 0<slopeD b := by
  exact div_pos (by norm_num [Q0]) (pow_pos (extended_shift_pos hb) 3)

theorem extended_A_antitone : AntitoneOn A extendedDomain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun b hb => (extended_A_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => extended_A_deriv (Ioo_subset_Icc_self hb)
  · intro b hb
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [hb.1]
    · exact (extended_shift_pos (Ioo_subset_Icc_self hb)).le

theorem extended_slope_monotone : MonotoneOn slope extendedDomain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (slope_deriv hb).continuousAt.continuousWithinAt
  · exact fun b hb => slope_deriv (Ioo_subset_Icc_self hb)
  · exact fun b hb => (slopeD_positive (Ioo_subset_Icc_self hb)).le

theorem low_extended {b : ℝ} (hb : b∈Icc 0 b1) : b∈extendedDomain := by
  constructor <;> linarith [hb.1,hb.2,b1_bounds.2]

theorem high_extended {b : ℝ} (hb : b∈Icc b2 c0) : b∈extendedDomain := by
  constructor <;> linarith [hb.1,hb.2,b2_bounds.1,c0_bounds.2]

theorem low_slopeD_upper {b : ℝ} (hb : b∈Icc 0 b1) : slopeD b<27/40 := by
  have hA := A_low_bounds hb
  have hp := extended_shift_pos (low_extended hb)
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤899/500)
    (show (899/500:ℝ)≤A b+1/2 by linarith [a1_precise.1,hA.1]) 3
  dsimp [slopeD]
  apply (div_lt_iff₀ (pow_pos hp 3)).2
  norm_num [Q0] at *
  nlinarith

theorem high_Hd_lower {b : ℝ} (hb : b∈Icc b2 c0) :
    (73/100:ℝ)<FrameHighArc.Hd b := by
  have hh := FrameHighArc.slope_high_bounds hb
  dsimp [FrameHighArc.Hd,FrameHighArc.u,FrameHighArc.v]
  linarith

theorem high_Hdd_lower {b : ℝ} (hb : b∈Icc b2 c0) :
    (453/1000:ℝ)<FrameHighArc.u*slopeD b := by
  have hp := extended_shift_pos (high_extended hb)
  have hA := FrameHighArc.A_high_bounds hb
  have hcube := pow_le_pow_left₀ hp.le
    (show A b+1/2≤17/10 by linarith [hA.2,a2_bounds.2]) 3
  rw [slopeD,← mul_div_assoc]
  apply (lt_div_iff₀ (pow_pos hp 3)).2
  norm_num [FrameHighArc.u,Q0] at *
  nlinarith

theorem extended_L_deriv {b : ℝ} (hb : b∈extendedDomain) : HasDerivAt L (Ld b) b := by
  unfold FrameLowArc.L
  convert (((extended_A_deriv hb).sub_const a0).const_mul FrameLowArc.u).fun_add
    ((hasDerivAt_id' b).const_mul FrameLowArc.v) using 1
  simp only [FrameLowArc.Ld,Ad,FrameLowArc.slope]
  ring

theorem extended_Ld_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt Ld (-FrameLowArc.u*slopeD b) b := by
  unfold FrameLowArc.Ld
  convert ((slope_deriv hb).const_mul FrameLowArc.u).const_sub FrameLowArc.v using 1
  ring

theorem extended_H_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt FrameHighArc.H (FrameHighArc.Hd b) b := by
  unfold FrameHighArc.H
  convert (((extended_A_deriv hb).const_mul FrameHighArc.u).const_sub FrameHighArc.k).fun_add
    ((hasDerivAt_id' b).const_mul FrameHighArc.v) using 1
  simp only [FrameHighArc.Hd,Ad,FrameLowArc.slope]
  ring

theorem extended_Hd_deriv {b : ℝ} (hb : b∈extendedDomain) :
    HasDerivAt FrameHighArc.Hd (FrameHighArc.u*slopeD b) b := by
  exact ((slope_deriv hb).const_mul FrameHighArc.u).add_const FrameHighArc.v

theorem G_deriv {b : ℝ} (hb : b∈extendedDomain) : HasDerivAt G (Gd b) b := by
  unfold G
  convert (((extended_A_deriv hb).const_mul FrameHighArc.v).const_sub
    (Real.pi/4-(FrameHighArc.u-FrameHighArc.v)*c0)).fun_add
      ((hasDerivAt_id' b).const_mul FrameHighArc.u) using 1
  simp only [Gd,Ad,FrameLowArc.slope]
  ring

theorem Gd_deriv {b : ℝ} (hb : b∈extendedDomain) : HasDerivAt Gd (Gdd b) b :=
  ((slope_deriv hb).const_mul FrameHighArc.v).add_const FrameHighArc.u

@[simp] theorem G_c0 : G c0=Real.pi/4 := by rw [G,A_c0]; ring

theorem extended_involution {b : ℝ} (hb : b∈extendedDomain) : A (A b)=b := by
  have hc := extended_circle hb
  have he : Q0-(A b+1/2)^2=(b+1/2)^2 := by linarith
  have hp : 0≤b+1/2 := by dsimp [extendedDomain] at hb; linarith [hb.1]
  change Real.sqrt (Q0-(A b+1/2)^2)-1/2=b
  rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]
  ring

theorem quarter_label {b : ℝ} (hb : b∈Icc b2 c0) :
    G (A b)=Real.pi/2-FrameHighArc.H b := by
  rw [G,extended_involution (high_extended hb)]
  dsimp [FrameHighArc.H,FrameHighArc.k]
  ring

theorem low_norm_upper {b : ℝ} (hb : b∈Icc 0 b1) :
    (A b)^2+b^2<(283/200:ℝ)^2 := by
  have hc := A_circle ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hax := A_circle (show (0:ℝ)∈Icc 0 c0 from
    ⟨le_rfl,by linarith [c0_bounds.1]⟩)
  simp only [A_zero] at hax
  have hsum := linear_endpoint_lower (p := (1:ℝ)) (q := (1:ℝ))
    (by norm_num) (by norm_num) b1_mem.2 hb
  simp only [linear,A_zero,A_b1,one_mul,mul_zero,add_zero] at hsum
  have he : a0≤a1+b1 := by linarith [a0_precise.2,a1_precise.1,b1_bounds.1]
  rw [min_eq_left he] at hsum
  have ha0 := a0_precise
  nlinarith

theorem low_projection_lt (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) (x : ℝ) :
    A b*Real.sin x-sign i*b*Real.cos x<(283/200:ℝ) := by
  have hh := low_norm_upper hb
  cases i
  · have hp := FrameCoreArc.projection_lt (b := b) (by norm_num : (0:ℝ)<283/200) hh x
    simp only [sign]
    norm_num
    linarith
  · have he : (A b)^2+(-b)^2<(283/200:ℝ)^2 := by nlinarith
    have hp := FrameCoreArc.projection_lt (b := -b) (by norm_num : (0:ℝ)<283/200) he x
    simp only [sign]
    norm_num
    linarith

end SquaresInCircles.Eight.FrameLowHighArc
end
end
end

section
/-!
## Original signed low/middle coordinates and angular tails

The angle floors use only the ordered physical center gap and the
intrinsic low/middle cuts.  Both circle endpoints and every weak
separating-axis equality remain in the domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowMidGeometry
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc

def lowMidCost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*L b-sign k*M B
def midLowCost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+sign i*M b-sign k*L B
def secondary (i k : Bool) (b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-pairWidth x
def primary (k : Bool) (b B x : ℝ) : ℝ :=
  A b-A B*Real.cos x-sign k*B*Real.sin x-pairWidth x

def lowMidFloor (i k : Bool) : ℝ :=
  if i then (if k then 19/25 else 11/100) else (if k then 1 else 7/20)
def midLowFloor (i k : Bool) : ℝ :=
  if i then (if k then 7/20 else 11/100) else (if k then 1 else 19/25)
def lowMidTail (i k : Bool) : ℝ :=
  if i then (if k then 7/5 else 16/25) else (if k then 171/100 else 19/20)
def midLowTail (i k : Bool) : ℝ :=
  if i then (if k then 19/20 else 16/25) else (if k then 171/100 else 7/5)

theorem low_intrinsic (s : FramePair.State) (hs : s.branch=.low) :
    0≤Real.arctan (s.b/s.a) ∧
      Real.arctan (s.b/s.a)≤Real.arctan (1/4:ℝ) ∧
      Real.arctan (s.b/s.a)<49/200 := by
  have ht : 4*s.b≤ s.a := by simpa [hs,TypeMem] using s.type_mem
  have hlo : 0≤ s.b/s.a := div_nonneg s.b_nonneg s.a_pos.le
  have hhi : s.b/s.a≤1/4 := (div_le_iff₀ s.a_pos).2 (by linarith)
  have ha0 : 0≤Real.arctan (s.b/s.a) := Real.arctan_nonneg.2 hlo
  have hau := Arithmetic.arctan_le_atanUpper (show (0:ℝ)≤1/4 by norm_num)
  have hnum : Arithmetic.atanUpper (1/4:ℝ)<49/200 := by
    norm_num [Arithmetic.atanUpper]
  exact ⟨ha0,Real.arctan_mono hhi,
    (Real.arctan_mono hhi).trans_lt (hau.trans_lt hnum)⟩

theorem middle_intrinsic (s : FramePair.State) (hs : s.branch=.middle) :
    (6/25:ℝ)<Real.arctan (s.b/s.a) ∧
      Real.arctan (1/4:ℝ)≤Real.arctan (s.b/s.a) ∧
      Real.arctan (s.b/s.a)<81/200 := by
  have ht : s.a≤4*s.b ∧ 7*s.b≤3*s.a := by simpa [hs,TypeMem] using s.type_mem
  have hlo : (1/4:ℝ)≤ s.b/s.a := (le_div_iff₀ s.a_pos).2 (by linarith [ht.1])
  have hhi : s.b/s.a≤3/7 := (div_le_iff₀ s.a_pos).2 (by linarith [ht.2])
  have hal := Arithmetic.atanLower_le (show (0:ℝ)≤1/4 by norm_num)
  have hau := Arithmetic.arctan_le_atanUpper (show (0:ℝ)≤3/7 by norm_num)
  have hnumL : (6/25:ℝ)<Arithmetic.atanLower (1/4:ℝ) := by
    norm_num [Arithmetic.atanLower]
  have hnumU : Arithmetic.atanUpper (3/7:ℝ)<81/200 := by
    norm_num [Arithmetic.atanUpper]
  exact ⟨hnumL.trans_le (hal.trans (Real.arctan_mono hlo)),
    Real.arctan_mono hlo,
    (Real.arctan_mono hhi).trans_lt (hau.trans_lt hnumU)⟩

theorem low_mid_angle (s t : FramePair.State) (hs : s.branch=.low)
    (ht : t.branch=.middle) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    lowMidFloor s.positive t.positive≤x := by
  have hso := low_intrinsic s hs
  have hto := middle_intrinsic t ht
  have hord := hso.2.1.trans hto.2.1
  dsimp [State.gap,State.offset] at hgap
  cases hi : s.positive <;> cases hk : t.positive
  all_goals simp only [hi,hk,sign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] at hgap
  all_goals simp only [lowMidFloor,Bool.false_eq_true,↓reduceIte]
  all_goals linarith

theorem mid_low_angle (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.low) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) :
    midLowFloor s.positive t.positive≤x := by
  have hso := middle_intrinsic s hs
  have hto := low_intrinsic t ht
  have hord := hto.2.1.trans hso.2.1
  dsimp [State.gap,State.offset] at hgap
  cases hi : s.positive <;> cases hk : t.positive
  all_goals simp only [hi,hk,sign,Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] at hgap
  all_goals simp only [midLowFloor,Bool.false_eq_true,↓reduceIte]
  all_goals linarith

theorem low_mid_tail (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc b1 b2) (hx : lowMidTail i k≤x) :
    (1801/2000:ℝ)<lowMidCost i k b B x := by
  have hs := L_bounds hb
  have ht := M_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases k <;> dsimp [lowMidTail,lowMidCost,sign] at *
  all_goals linarith [L1_precise.2,M_endpoints.1,M_endpoints.2.2.2]

theorem mid_low_tail (i k : Bool) {b B x : ℝ}
    (hb : b∈Icc b1 b2) (hB : B∈Icc 0 b1) (hx : midLowTail i k≤x) :
    (1801/2000:ℝ)< midLowCost i k b B x := by
  have hs := M_bounds hb
  have ht := L_bounds hB
  have hch := CorePairGeometry.charge_upper x
  cases i <;> cases k <;> dsimp [midLowTail,midLowCost,sign] at *
  all_goals linarith [L1_precise.2,M_endpoints.1,M_endpoints.2.2.2]

theorem low_mid_weaken_source (i k : Bool) {b B x : ℝ} (hb : b∈Icc 0 b1) :
    lowMidCost false k b B x≤lowMidCost i k b B x := by
  have hp := (L_bounds hb).1
  cases i <;> dsimp [lowMidCost,sign] <;> linarith

theorem mid_low_weaken_source (i k : Bool) {b B x : ℝ} (hb : b∈Icc b1 b2) :
    midLowCost false k b B x≤ midLowCost i k b B x := by
  have hp : 0≤M b := by linarith [(M_bounds hb).1,M_endpoints.1]
  cases i <;> dsimp [midLowCost,sign] <;> linarith

theorem state_low_mid_cost (s t : FramePair.State) (hs : s.branch=.low)
    (ht : t.branch=.middle) (x : ℝ) :
    s.cost t x=lowMidCost s.positive t.positive s.b t.b x := by
  rw [State.cost,state_low_label s hs,state_mid_label t ht]
  rfl

theorem state_mid_low_cost (s t : FramePair.State) (hs : s.branch=.middle)
    (ht : t.branch=.low) (x : ℝ) :
    s.cost t x=midLowCost s.positive t.positive s.b t.b x := by
  rw [State.cost,state_mid_label s hs,state_low_label t ht]
  rfl

theorem state_secondary (s t : FramePair.State)
    (ht : t.branch.type≠0) (x : ℝ) :
    s.Feasible t 0 x ↔ 0≤ secondary s.positive t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,(state_outer_chart t ht).1]
  rfl

theorem state_primary (s t : FramePair.State)
    (hs : s.branch.type≠0) (ht : t.branch.type≠0) (x : ℝ) :
    s.Feasible t 3 x ↔ 0≤primary t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_outer_chart s hs).1,(state_outer_chart t ht).1]
  rfl

end SquaresInCircles.Eight.FrameLowMidGeometry
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighParallelCalculus
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus

def angleDomain (positive : Bool) : Set ℝ :=
  if positive then Icc (0:ℝ) (1/50) else Icc (-(1/50:ℝ)) 0
def width (positive : Bool) (x : ℝ) : ℝ :=
  if positive then (1+Real.sin x+Real.cos x)/2 else (1-Real.sin x+Real.cos x)/2
def widthD (positive : Bool) (x : ℝ) : ℝ :=
  if positive then (Real.cos x-Real.sin x)/2 else (-Real.cos x-Real.sin x)/2
def height (positive : Bool) (B x : ℝ) : ℝ :=
  width positive x-A B*Real.sin x-B*Real.cos x
def P (positive : Bool) (B x : ℝ) : ℝ :=
  A B*Real.cos x-B*Real.sin x-widthD positive x

theorem width_deriv (positive : Bool) (x : ℝ) :
    HasDerivAt (width positive) (widthD positive x) x := by
  have hs := Real.hasDerivAt_sin x
  have hc := Real.hasDerivAt_cos x
  cases positive
  · have e : width false=fun y => (1-Real.sin y+Real.cos y)/2 := by
      funext y; simp [width]
    rw [e]
    refine (((hs.const_sub 1).fun_add hc).div_const 2).congr_deriv ?_
    simp only [widthD,Bool.false_eq_true,↓reduceIte]
    ring
  · have e : width true=fun y => (1+Real.sin y+Real.cos y)/2 := by
      funext y; simp [width]
    rw [e]
    refine (((hs.const_add 1).fun_add hc).div_const 2).congr_deriv ?_
    simp only [widthD,↓reduceIte]
    ring

theorem height_deriv (positive : Bool) (B x : ℝ) :
    HasDerivAt (height positive B) (-P positive B x) x := by
  have h := ((width_deriv positive x).fun_sub ((Real.hasDerivAt_sin x).const_mul (A B))).fun_sub
    ((Real.hasDerivAt_cos x).const_mul B)
  refine h.congr_deriv ?_
  simp only [P]
  ring

theorem trig_small (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    -(1/50:ℝ)≤Real.sin x ∧ Real.sin x≤1/50 ∧
      (4999/5000:ℝ)≤Real.cos x ∧ Real.cos x≤1 ∧
        (if positive then 0≤Real.sin x else Real.sin x≤0) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hcu := Real.cos_le_one x
  cases positive with
  | false =>
      have hz : -x∈Icc (0:ℝ) (1/50) := by
        dsimp [angleDomain] at hx
        constructor <;> linarith [hx.1,hx.2]
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
        (by linarith [hz.2,FrameLowPair.pi_lower])
      have hsu := Real.sin_le hz.1
      have hsq := pow_le_pow_left₀ hz.1 hz.2 2
      simp only [Real.sin_neg,neg_sq] at hs hsu hsq
      simp only [Bool.false_eq_true,↓reduceIte]
      exact ⟨by linarith [hz.2],by linarith,by linarith,hcu,by linarith⟩
  | true =>
      have hz : x∈Icc (0:ℝ) (1/50) := by simpa [angleDomain] using hx
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
        (by linarith [hz.2,FrameLowPair.pi_lower])
      have hsu := Real.sin_le hz.1
      have hsq := pow_le_pow_left₀ hz.1 hz.2 2
      simp only [↓reduceIte]
      exact ⟨by linarith,by linarith [hz.2],by linarith,hcu,hs⟩

theorem width_eq (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    width positive x=pairWidth x := by
  have ht := trig_small positive hx
  cases positive
  · simp only [Bool.false_eq_true,↓reduceIte] at ht
    simp only [width,pairWidth,Bool.false_eq_true,↓reduceIte,abs_of_nonpos ht.2.2.2.2,
      abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos x)]
    ring
  · simp only [↓reduceIte] at ht
    simp only [width,pairWidth,↓reduceIte,abs_of_nonneg ht.2.2.2.2,
      abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos x)]

theorem widthD_bounds (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    if positive then (4899/10000:ℝ)≤widthD positive x ∧ widthD positive x≤1/2
    else -(1/2:ℝ)≤widthD positive x ∧ widthD positive x≤-(4899/10000:ℝ) := by
  have ht := trig_small positive hx
  cases positive <;> dsimp [widthD] at * <;> constructor <;> linarith

theorem P_positive (positive : Bool) {B x : ℝ} (hB : B∈Icc 0 c0)
    (hx : x∈angleDomain positive) : 0<P positive B x := by
  have ht := trig_small positive hx
  have hw := widthD_bounds positive hx
  have hA := A_bounds hB
  have hAc := mul_le_mul
    (show (899/1000:ℝ)≤A B by linarith [hA.1,c0_bounds.1]) ht.2.2.1
    (by norm_num : (0:ℝ)≤4999/5000) (by linarith [hA.1,c0_bounds.1] : 0≤A B)
  have hBs := mul_le_mul_of_nonneg_left ht.2.1 hB.1
  have hBup : B≤9/10 := by linarith [hB.2,c0_bounds.2]
  dsimp [P]
  cases positive <;> dsimp at hw <;> nlinarith

theorem height_antitone (positive : Bool) {B : ℝ} (hB : B∈Icc 0 c0) :
    AntitoneOn (height positive B) (angleDomain positive) := by
  have hd : ∀ x, HasDerivAt (height positive B) (-P positive B x) x := height_deriv positive B
  cases positive
  · apply antiOn_of_hasDeriv_nonpos (l := -(1/50:ℝ)) (u := 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    have hh := P_positive false hB
      (by simpa [angleDomain] using (Ioo_subset_Icc_self hx : x∈Icc (-(1/50:ℝ)) 0))
    linarith
  · apply antiOn_of_hasDeriv_nonpos (l := 0) (u := 1/50)
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    have hh := P_positive true hB
      (by simpa [angleDomain] using (Ioo_subset_Icc_self hx : x∈Icc (0:ℝ) (1/50)))
    linarith

@[simp] theorem height_zero (positive : Bool) (B : ℝ) : height positive B 0=1-B := by
  cases positive <;> simp [height,width]

theorem low_derivative_bounds {b : ℝ} (hb : b∈Icc (0:ℝ) (7/20)) :
    (89/100:ℝ)<Ld b ∧ Ld b<109/100 := by
  have hd : b∈extendedDomain := by constructor <;> linarith [hb.1,hb.2]
  have hc := extended_circle hd
  have hp := extended_shift_pos hd
  have hbsq := pow_le_pow_left₀ (by linarith [hb.1] : 0≤b+1/2)
    (show b+1/2≤17/20 by linarith [hb.2]) 2
  have hA : (89/50:ℝ)<A b+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hr0 : 0≤ slope b := div_nonneg (by linarith [hb.1]) hp.le
  have hrU : slope b<12/25 := by
    apply (div_lt_iff₀ hp).2
    linarith [hb.2,hA]
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  constructor <;> linarith

theorem low_label_monotone : MonotoneOn L (Icc (0:ℝ) (7/20)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact (extended_L_deriv (by constructor <;> linarith [hb.1,hb.2])).continuousAt.continuousWithinAt
  · intro b hb
    exact extended_L_deriv (by constructor <;> linarith [hb.1,hb.2])
  · exact fun b hb => by linarith [(low_derivative_bounds (Ioo_subset_Icc_self hb)).1]

theorem high_target_P (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) :
    if positive then P positive B x<711/1000 else (69/50:ℝ)<P positive B x := by
  have ht := trig_small positive hx
  have hw := widthD_bounds positive hx
  have hA := high_bounds hB
  have hB0 : 0≤B := b2_mem.1.trans hB.1
  cases positive with
  | false =>
      have hAc := mul_le_mul
        (show (899/1000:ℝ)≤A B by linarith [hA.2.2.1]) ht.2.2.1
        (by norm_num : (0:ℝ)≤4999/5000) (by linarith [hA.2.2.1] : 0≤A B)
      have hBs := mul_nonpos_of_nonneg_of_nonpos hB0 ht.2.2.2.2
      dsimp [P] at *
      linarith
  | true =>
      have hAc := mul_le_mul_of_nonneg_left ht.2.2.2.1 (by linarith [hA.2.2.1] : 0≤A B)
      have hBs := mul_nonneg hB0 ht.2.2.2.2
      dsimp [P] at *
      linarith

end SquaresInCircles.Eight.FrameLowHighParallelCalculus
end
end
end
