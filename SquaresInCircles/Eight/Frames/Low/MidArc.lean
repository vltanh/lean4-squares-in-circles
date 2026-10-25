module

public import SquaresInCircles.Eight.Frames.Pair.Calculus

/-!
# Eight squares: whole-arc source supports for the low/middle frame pair

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
