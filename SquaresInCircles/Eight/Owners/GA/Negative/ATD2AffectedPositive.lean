module

public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2AffectedPositiveCurves
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2UnaffectedPositive

/-!
# Eight squares: original affected-pair positive surplus reduces to equal angles

The normalized curves are exact identities for the original
secant weights. The AB minimum keeps both possible orders of its two
coefficients, and both branches agree when those coefficients coincide.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedPositive
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeEnvelope
open SecantBaseline AffectedPositiveCurves
open Certificate (Family)

def value (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c s z+
    if atG then U R k (NegativeAPositiveTD.secant l s) (s-z)
    else U R (min (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z))
      (max (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z)) (s-z)

theorem rotation_unit_norm {r s z : ℝ} (hc : 0<Real.cos s) :
    pairNorm r (1/Real.cos s) (s-z)=AffectedNorm.norm r z (Real.tan s) := by
  have ht := AffectedNorm.tan_identity hc
  have hsin : (1/Real.cos s)*Real.sin (s-z)=Real.tan s*Real.cos z-Real.sin z := by
    rw [Real.sin_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
  have hsin' := congrArg (fun x : ℝ => 2*r*x) hsin
  have he : r^2+(1/Real.cos s)^2+2*r*(1/Real.cos s)*Real.sin (s-z)=
      (AffectedNorm.norm r z (Real.tan s))^2 := by
    rw [AffectedNorm.norm_sq_expanded]
    nlinarith only [ht.2,hsin']
  dsimp [pairNorm]
  rw [he,Real.sqrt_sq (show 0≤AffectedNorm.norm r z (Real.tan s) from Real.sqrt_nonneg _)]

theorem rotation_norm {l s : ℝ} (hl : 0<l) (hc : 0<Real.cos s) (a z : ℝ) :
    pairNorm a (NegativeAPositiveTD.secant l s) (s-z)=
      l*AffectedNorm.norm (a/l) z (Real.tan s) := by
  have hh := pairNorm_homogeneous hl.le (a/l) (1/Real.cos s) (s-z)
  rw [show l*(a/l)=a by field_simp [hl.ne'],
    show l*(1/Real.cos s)=NegativeAPositiveTD.secant l s by
      dsimp [NegativeAPositiveTD.secant]; ring,
    rotation_unit_norm hc] at hh
  exact hh

theorem zero_norm {l : ℝ} (hl : 0<l) (a : ℝ) :
    pairNorm a l 0=l*OrdinaryCurvatureBounds.shape (a/l) := by
  have hh := FlatTStress.zero_norm_scale hl a 1
  simpa [OrdinaryCurvatureBounds.shape,add_comm] using hh

theorem GA_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    value true k l c s z=baseline true k l c 0 z+
      l*(upper (k/l) z s-1+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  rw [value,baseline_eq_extension true k l c z hs]
  simp only [angularBaseline,affected,↓reduceIte,FlatTStress.secantCharge,U]
  rw [rotation_norm hl hc k z,zero_norm hl k]
  dsimp [upper,NegativeAPositiveTD.secant]
  field_simp [hl.ne']
  ring

theorem branch_difference {r s z : ℝ} (hc : Real.cos s≠0) :
    upper r z s-lower r z s=(r-1/Real.cos s)*(PositiveAngularEnvelope.phi (s-z)-1) := by
  rw [lower_identity hc]
  dsimp [upper]
  ring

theorem AB_identity {k l c s z : ℝ} (hl : 0<l)
    (hs : s∈Icc 0 frameCap) (hz : z∈Icc 0 s) :
    value false k l c s z=baseline false k l c 0 z+
      l*(min (upper (PositiveTD.tilted c z/l) z s)
        (lower (PositiveTD.tilted c z/l) z s)-1+
          R*OrdinaryCurvatureBounds.shape (PositiveTD.tilted c z/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hdiff : s-z∈Icc 0 frameCap :=
    ⟨by linarith [hz.2],by linarith [hs.2,hz.1]⟩
  have hphi : 0≤PositiveAngularEnvelope.phi (s-z)-1 := sub_nonneg.mpr (CorrelatedSameBlock.one_le_phi hdiff)
  have hbranch := branch_difference (r:=PositiveTD.tilted c z/l) (z:=z) hc.ne'
  rcases le_total (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z) with hle | hle
  · have hr : 1/Real.cos s≤PositiveTD.tilted c z/l := by
      apply (le_div_iff₀ hl).2
      dsimp [NegativeAPositiveTD.secant] at hle
      rw [show 1/Real.cos s*l=l/Real.cos s by ring]
      exact hle
    have hh := mul_nonneg (sub_nonneg.mpr hr) hphi
    have hmin : lower (PositiveTD.tilted c z/l) z s≤upper (PositiveTD.tilted c z/l) z s := by
      linarith
    rw [min_eq_right hmin,value,baseline_eq_extension false k l c z hs]
    simp only [angularBaseline,affected,Bool.false_eq_true,↓reduceIte,FlatTStress.secantCharge,
      min_eq_left hle,max_eq_right hle,U]
    simp only [pairNorm_symm (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z)]
    rw [rotation_norm hl hc (PositiveTD.tilted c z) z,zero_norm hl (PositiveTD.tilted c z),
      lower_identity hc.ne']
    dsimp [NegativeAPositiveTD.secant]
    field_simp [hl.ne']
    ring
  · have hr : PositiveTD.tilted c z/l≤1/Real.cos s := by
      apply (div_le_iff₀ hl).2
      dsimp [NegativeAPositiveTD.secant] at hle
      rw [show 1/Real.cos s*l=l/Real.cos s by ring]
      exact hle
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hphi
    have hmin : upper (PositiveTD.tilted c z/l) z s≤lower (PositiveTD.tilted c z/l) z s := by
      linarith
    rw [min_eq_left hmin,value,baseline_eq_extension false k l c z hs]
    simp only [angularBaseline,affected,Bool.false_eq_true,↓reduceIte,FlatTStress.secantCharge,
      min_eq_right hle,max_eq_left hle,U]
    rw [rotation_norm hl hc (PositiveTD.tilted c z) z,zero_norm hl (PositiveTD.tilted c z)]
    dsimp [upper,NegativeAPositiveTD.secant]
    field_simp [hl.ne']
    ring

theorem AB_min_monotone {r z : ℝ}
    (hr : r∈Icc (4/5:ℝ) (71/50:ℝ)) (hz : z∈Icc 0 (19/50:ℝ)) :
    MonotoneOn (fun s => min (upper r z s) (lower r z s)) (Icc z (19/50:ℝ)) := by
  have hrr : r∈Icc (0:ℝ) (71/50:ℝ) := ⟨by linarith [hr.1],hr.2⟩
  have hlow := lower_monotone hrr hz
  by_cases hsmall : r≤(27/25:ℝ)
  · have hu := AB_upper_monotone ⟨hr.1,hsmall⟩ hz
    intro x hx y hy hxy
    exact min_le_min (hu hx hy hxy) (hlow hx hy hxy)
  · have he (s : ℝ) (hs : s∈Icc z (19/50:ℝ)) :
        min (upper r z s) (lower r z s)=lower r z s := by
      have hss : s∈Icc 0 (19/50:ℝ) := ⟨hz.1.trans hs.1,hs.2⟩
      have hcos := Explicit.AB_cut_cosine hss
      have hc : 0<Real.cos s := by linarith
      have hw : 1/Real.cos s≤(27/25:ℝ) := by
        apply (div_le_iff₀ hc).2
        linarith
      have hphi : 0≤PositiveAngularEnvelope.phi (s-z)-1 := by
        apply sub_nonneg.mpr
        apply CorrelatedSameBlock.one_le_phi
        exact ⟨by linarith [hs.1],by dsimp [frameCap]; linarith [hs.2,hz.1]⟩
      have hprod := mul_nonneg (show 0≤r-1/Real.cos s by linarith) hphi
      have hh := branch_difference (r:=r) (z:=z) hc.ne'
      exact min_eq_right (by linarith)
    intro x hx y hy hxy
    dsimp only
    rw [he x hx,he y hy]
    exact hlow hx hy hxy

theorem GA_reduces_to_equal (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (1/4:ℝ)) (hzs : z≤ s) :
    baseline true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z≤
      value true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z := by
  have hb := Explicit.family_basic_domain f hz
  have hl : 0<Explicit.l f z := (Explicit.family_positive f hz).2.1
  have hzf := Explicit.family_frame_domain f hz
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hr : Explicit.k f z/Explicit.l f z∈Icc (11/20:ℝ) (17/20:ℝ) := by
    constructor
    · exact (le_div_iff₀ hl).2 hb.2.2.2.2.1.le
    · apply (div_le_iff₀ hl).2
      linarith [hb.1.2,hb.2.2.1]
  have hm := GA_upper_monotone hr ⟨hzf.1,hzs.trans hs.2⟩
    (show z∈Icc z (1/4:ℝ) from ⟨le_rfl,hzs.trans hs.2⟩)
    (show s∈Icc z (1/4:ℝ) from ⟨hzs,hs.2⟩) hzs
  have hez := GA_identity (k:=Explicit.k f z) (c:=Explicit.c f z) (z:=z) hl hzf
  have hes := GA_identity (k:=Explicit.k f z) (c:=Explicit.c f z) (z:=z) hl hsf
  have hmul := mul_le_mul_of_nonneg_left hm hl.le
  have hzvalue : value true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z=
      baseline true (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z := by
    simp [value]
  rw [hzvalue] at hez
  linarith

theorem AB_reduces_to_equal (f : Family) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (19/50:ℝ)) (hzs : z≤ s) :
    baseline false (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z≤
      value false (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z := by
  have hb := Explicit.family_basic_domain f hz
  have hl : 0<Explicit.l f z := (Explicit.family_positive f hz).2.1
  have hzf := Explicit.family_frame_domain f hz
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩
  have hr : Explicit.m f z/Explicit.l f z∈Icc (4/5:ℝ) (71/50:ℝ) := by
    constructor
    · exact (le_div_iff₀ hl).2 (UnaffectedPositive.AB_ratio_after_equal f hz (hzs.trans hs.2)).le
    · exact (div_le_iff₀ hl).2 hb.2.2.2.2.2.2.le
  have hm := AB_min_monotone hr ⟨hzf.1,hzs.trans hs.2⟩
    (show z∈Icc z (19/50:ℝ) from ⟨le_rfl,hzs.trans hs.2⟩)
    (show s∈Icc z (19/50:ℝ) from ⟨hzs,hs.2⟩) hzs
  have hez := AB_identity (k:=Explicit.k f z) (c:=Explicit.c f z) (z:=z) hl hzf ⟨hzf.1,le_rfl⟩
  have hes := AB_identity (k:=Explicit.k f z) (c:=Explicit.c f z) (z:=z) hl hsf ⟨hzf.1,hzs⟩
  have hmul := mul_le_mul_of_nonneg_left hm hl.le
  have hzvalue : value false (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z=
      baseline false (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z := by
    simp [value]
  rw [hzvalue] at hez
  dsimp [Explicit.m] at hm hmul
  linarith

theorem all_positive_reduces_to_equal (f : Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hzs : z≤ s) (i : Fin 4) :
    baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) z z≤
      baseline atG (Explicit.k f z) (Explicit.l f z) (Explicit.c f z) s z+
        PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2)
          (Source.pWeights atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s)
          (Source.qWeights atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s) 3 i (s-z) := by
  by_cases hi : i=UnaffectedPositive.affectedIndex atG
  · subst i
    cases atG
    · simpa [value,UnaffectedPositive.affectedIndex,PositiveTD.Hybrid.positive,
        Source.pWeights,Source.qWeights,lambdaB,Explicit.m] using AB_reduces_to_equal f hz hs hzs
    · simpa [value,UnaffectedPositive.affectedIndex,PositiveTD.Hybrid.positive,
        Source.pWeights,Source.qWeights,lambdaG,Explicit.m] using GA_reduces_to_equal f hz hs hzs
  · exact UnaffectedPositive.reduces_to_equal f atG hz hs hzs i hi

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.AffectedPositive
