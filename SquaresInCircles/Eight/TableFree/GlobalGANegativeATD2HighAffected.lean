module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2AffectedNegativeCurvature
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2HighUnaffected

/-!
# Every high affected negative endpoint with its original secant pair

Uncompiled transcription of Section 10. The GA curve is affine minus
its rotated norm. The AB curve retains its intrinsic coefficient switch
and downward derivative jump. Both reduce on the full algebraic
interval to the already certified zero and equal-angle scalar values.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.HighAffected
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open SecantCoordinate SecantBaseline AffectedNegativeCurves

def value (atG : Bool) (k l c s z : ℝ) : ℝ :=
  baseline atG k l c s z+
    if atG then V R k (NegativeAPositiveTD.secant l s) (z-s)
    else V R (min (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z))
      (max (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z)) (z-s)
def curve (atG : Bool) (r z x : ℝ) : ℝ :=
  if atG then upper r z x else min (upper r z x) (lower r z x)
def ratio (atG : Bool) (z : ℝ) : ℝ :=
  basicRatio atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) z
def scalar (atG : Bool) (z x : ℝ) : ℝ :=
  baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) 0 z+
    Explicit.l .high z*(curve atG (ratio atG z) z x-1+
      R*OrdinaryCurvatureBounds.shape (ratio atG z))

theorem radical_tan {s : ℝ} (hs : s∈Icc 0 frameCap) :
    radical 1 (Real.tan s)=1/Real.cos s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hw := radical_positive (A:=1) (x:=Real.tan s) (by norm_num)
  have hw2 := radical_square (A:=1) (x:=Real.tan s) (by norm_num)
  have ht := (AffectedNorm.tan_identity hc).2
  have hp : 0<1/Real.cos s := one_div_pos.mpr hc
  nlinarith

theorem cosine_tan {s z : ℝ} (hs : s∈Icc 0 frameCap) :
    cosine z (Real.tan s)=Real.cos (z-s) := by
  rw [cosine_arctan,arctan_tan hs]

theorem GA_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    value true k l c s z=baseline true k l c 0 z+
      l*(upper (k/l) z (Real.tan s)-1+R*OrdinaryCurvatureBounds.shape (k/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hcos : Real.cos (z-s)/Real.cos s=Real.cos z+Real.tan s*Real.sin z := by
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring
  rw [value,baseline_eq_extension true k l c z hs]
  simp only [angularBaseline,affected,↓reduceIte,FlatTStress.secantCharge,V]
  rw [show -(z-s)=s-z by ring,AffectedPositive.rotation_norm hl hc k z,
    AffectedPositive.zero_norm hl k]
  dsimp [upper,NegativeAPositiveTD.secant]
  have hh := congrArg (fun a : ℝ => l*a) hcos
  field_simp [hl.ne',hc.ne'] at hh ⊢
  nlinarith only [hh]

theorem AB_identity {k l c s z : ℝ} (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    value false k l c s z=baseline false k l c 0 z+
      l*(min (upper (PositiveTD.tilted c z/l) z (Real.tan s))
        (lower (PositiveTD.tilted c z/l) z (Real.tan s))-1+
          R*OrdinaryCurvatureBounds.shape (PositiveTD.tilted c z/l)) := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hw := radical_tan hs
  have ht := cosine_tan (z:=z) hs
  have hcos : Real.cos (z-s)/Real.cos s=Real.cos z+Real.tan s*Real.sin z := by
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    ring
  have hbranch := branch_difference (PositiveTD.tilted c z/l) z (Real.tan s)
  rcases le_total (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z) with hle | hle
  · have hr : radical 1 (Real.tan s)≤PositiveTD.tilted c z/l := by
      rw [hw]
      apply (le_div_iff₀ hl).2
      dsimp [NegativeAPositiveTD.secant] at hle
      nlinarith only [hle]
    have hp := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hr)
      (sub_nonpos.mpr (cosine_le_one z (Real.tan s)))
    have hmin : lower (PositiveTD.tilted c z/l) z (Real.tan s)≤
        upper (PositiveTD.tilted c z/l) z (Real.tan s) := by linarith
    rw [min_eq_right hmin,value,baseline_eq_extension false k l c z hs]
    simp only [angularBaseline,affected,↓reduceIte,FlatTStress.secantCharge,
      min_eq_left hle,max_eq_right hle,V]
    simp only [pairNorm_symm (NegativeAPositiveTD.secant l s) (PositiveTD.tilted c z)]
    rw [show -(z-s)=s-z by ring,
      AffectedPositive.rotation_norm hl hc (PositiveTD.tilted c z) z,
      AffectedPositive.zero_norm hl (PositiveTD.tilted c z)]
    dsimp [lower]
    rw [hw,ht]
    dsimp [NegativeAPositiveTD.secant]
    field_simp [hl.ne']
    ring
  · have hr : PositiveTD.tilted c z/l≤radical 1 (Real.tan s) := by
      rw [hw]
      apply (div_le_iff₀ hl).2
      dsimp [NegativeAPositiveTD.secant] at hle
      nlinarith only [hle]
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr)
      (sub_nonpos.mpr (cosine_le_one z (Real.tan s)))
    have hmin : upper (PositiveTD.tilted c z/l) z (Real.tan s)≤
        lower (PositiveTD.tilted c z/l) z (Real.tan s) := by linarith
    rw [min_eq_left hmin,value,baseline_eq_extension false k l c z hs]
    simp only [angularBaseline,affected,↓reduceIte,FlatTStress.secantCharge,
      min_eq_right hle,max_eq_left hle,V]
    rw [show -(z-s)=s-z by ring,
      AffectedPositive.rotation_norm hl hc (PositiveTD.tilted c z) z,
      AffectedPositive.zero_norm hl (PositiveTD.tilted c z)]
    dsimp [upper,NegativeAPositiveTD.secant]
    have hh := congrArg (fun a : ℝ => l*a) hcos
    field_simp [hl.ne',hc.ne'] at hh ⊢
    nlinarith only [hh]

theorem scalar_at_original (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) (hs : s∈Icc 0 frameCap) :
    scalar atG z (Real.tan s)=
      value atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z := by
  have hl := (Explicit.family_positive .high hz).2.1
  cases atG
  · simpa [scalar,curve,ratio,basicRatio,affected] using (AB_identity hl hs).symm
  · simpa [scalar,curve,ratio,basicRatio,affected] using (GA_identity hl hs).symm

theorem curve_concave (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (curve atG (ratio atG z) z) := by
  have hzframe : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  cases atG
  · have hr := HighUnaffected.AB_ratio hz
    have hlarge : 1<ratio false z→z≤1/4 := by
      intro hh
      by_contra hnot
      have hm := Explicit.high_tilted_quarter ⟨(lt_of_not_ge hnot).le,hz.2⟩
      have hl := (Explicit.family_positive .high hz).2.1
      have hratio : ratio false z<1 := by
        change Explicit.m .high z/Explicit.l .high z<1
        exact (div_lt_one hl).2 hm
      linarith
    exact AffectedNegativeCurvature.minimum_concave hr hzframe hlarge
  · have hr := HighUnaffected.GA_ratio hz
    exact upper_concave (AffectedNorm.second_coordinate_pos
      ⟨hr.1,by linarith [hr.2]⟩ hzframe)

theorem scalar_concave (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    ConcaveOn ℝ (Icc 0 (Real.tan z)) (scalar atG z) := by
  have hcurve := curve_concave atG hz
  have hl := (Explicit.family_positive .high hz).2.1
  refine ⟨hcurve.1,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hcurve.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  have hp := mul_le_mul_of_nonneg_left hh hl.le
  dsimp [scalar]
  nlinarith [congrArg (fun t : ℝ => t*
    (baseline atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) 0 z+
      Explicit.l .high z*(-1+R*OrdinaryCurvatureBounds.shape (ratio atG z)))) hab]

theorem scalar_zero (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<scalar atG z 0 := by
  have he := scalar_at_original atG hz
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
  rw [Real.tan_zero] at he
  rw [he]
  cases atG
  · simpa [value,NegativeAPositiveTD.secant,baseline_zero,Explicit.m] using
      (Certificate.high_endpoints hz).2.2.1
  · simpa [value,NegativeAPositiveTD.secant,baseline_zero] using
      (Certificate.high_endpoints hz).2.1

theorem scalar_equal (atG : Bool) {z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ)) :
    0<scalar atG z (Real.tan z) := by
  rw [scalar_at_original atG hz ⟨by linarith [hz.1],hz.2⟩]
  cases atG
  · simpa [value] using (Certificate.high_endpoints hz).2.2.2.2
  · simpa [value] using (Certificate.high_endpoints hz).2.2.2.1

theorem original (atG : Bool) {s z : ℝ} (hz : z∈Icc (1/5:ℝ) (7/10:ℝ))
    (hs : s∈Icc 0 (Explicit.angleCut atG)) (hsz : s≤z) :
    0<value atG (Explicit.k .high z) (Explicit.l .high z) (Explicit.c .high z) s z := by
  have hsframe := (Explicit.angle_domain atG hs).2
  have hzframe : z∈Icc 0 frameCap := ⟨by linarith [hz.1],hz.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan z) :=
    ⟨tan_nonnegative hsframe,tan_monotone hsframe hzframe hsz⟩
  have hh := concave_gt_of_endpoints (scalar_concave atG hz) hx
    (scalar_zero atG hz) (scalar_equal atG hz)
  rwa [scalar_at_original atG hz hsframe] at hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.HighAffected
