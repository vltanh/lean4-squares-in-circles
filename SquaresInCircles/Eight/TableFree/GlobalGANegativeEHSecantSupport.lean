module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeESecantGain
public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveATD0ChargedPairs

/-!
# The charged H circle with a genuine negative EH1 secant

Uncompiled transcription of Section 2 of
`HAND_G3_CORE_E_NEGATIVE_EH1_SECANT_H_SUPPORT.md`.

The secant multiplier varies on the complete interval [1,1.033].
The existing universal ordinary-norm curvature proves separate
concavity on the two angle signs. At the two intrinsic angle endpoints
the H block itself has ample reserve: direct positive-square bounds
on its three norms suffice uniformly in the multiplier. This retains
the full actual H-circle support in the final statement.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHSecant
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity Secondary

abbrev k : ℝ := 39/50
abbrev L : ℝ := 103/100

def charged (u v : ℝ) : ℝ :=
  k*psi v-R*(pairNorm k u v-pairNorm k u 0)+L*v

def negative (u w : ℝ) : ℝ :=
  k*(Real.cos w-1)-R*(pairNorm k u (-w)-pairNorm k u 0)-L*w

def negativeD (u w : ℝ) : ℝ :=
  -k*Real.sin w+R*normD1 k u (-w)-L

theorem coefficient_range {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    0<k ∧ k≤u ∧ u≤2*k := by
  dsimp [k]
  exact ⟨by norm_num,by linarith [hu.1],by linarith [hu.2]⟩

theorem positive_concave {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    ConcaveOn ℝ (Icc 0 frameCap)
      (fun v => k*(phi v-1)-R*(pairNorm k u v-pairNorm k u 0)+L*v) := by
  have hc := coefficient_range hu
  have hh := PositiveATD0.chargedMixed_concave_P hc.1 hc.2.1 hc.2.2
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
  simpa [PositiveATD0.chargedMixed,mixedBlock,PositiveATD0.charge,L] using hh

theorem negative_hasDerivAt {u w : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ))
    (hw : w∈Icc 0 frameCap) : HasDerivAt (negative u) (negativeD u w) w := by
  have hc := coefficient_range hu
  have hn := (pairNorm_hasDerivAt hc.1 (hc.1.trans_le hc.2.1)
    (t := -w) (by simpa [abs_of_nonneg hw.1] using hw.2)).comp w
      (hasDerivAt_id w).neg
  convert (((((Real.hasDerivAt_cos w).sub_const 1).const_mul k).sub
    ((hn.sub_const (pairNorm k u 0)).const_mul R)).sub
      ((hasDerivAt_id w).const_mul L)) using 1
  · rfl
  · dsimp [negativeD]
    ring

theorem negativeD_hasDerivAt {u w : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ))
    (hw : w∈Icc 0 frameCap) :
    HasDerivAt (negativeD u) (curvature R k u (-w)-k*Real.cos w) w := by
  have hc := coefficient_range hu
  have hn := (normD1_hasDerivAt hc.1 (hc.1.trans_le hc.2.1)
    (t := -w) (by simpa [abs_of_nonneg hw.1] using hw.2)).comp w
      (hasDerivAt_id w).neg
  convert ((((Real.hasDerivAt_sin w).const_mul (-k)).add
    (hn.const_mul R)).sub_const L) using 1
  · rfl
  · dsimp [curvature]
    ring

theorem negative_concave {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    ConcaveOn ℝ (Icc 0 frameCap) (negative u) := by
  have hc := coefficient_range hu
  apply concave_of_deriv2 (fun w hw => negative_hasDerivAt hu hw)
    (fun w hw => negativeD_hasDerivAt hu hw)
  intro w hw
  have hupper := curvature_negative_upper (Real.sqrt_nonneg qCap)
    hc.1 (hc.1.trans_le hc.2.1)
    (show -w∈Icc (-frameCap) 0 by constructor <;> linarith [hw.1,hw.2])
  have hconstants := curvature_constant_bounds (R := R) (Real.sqrt_nonneg qCap)
    (by rw [radius_sq]) hc.1 hc.2.1 hc.2.2
  have hcos := (transport_trig hw).1
  dsimp [k] at *
  linarith [hconstants.1]

theorem norm_zero_lower {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    (6341/5000:ℝ)<pairNorm k u 0 := by
  have hc := coefficient_range hu
  have hs := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1)
    (t := 0) (by norm_num [frameCap])
  have hp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1)
    (t := 0) (by norm_num [frameCap])
  have hu2 : (1:ℝ)≤u^2 := by nlinarith [hu.1]
  norm_num [pairEnergy,pairProduct,k] at hs
  nlinarith

theorem norm_positive_upper {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    pairNorm k u frameCap<(33/20:ℝ) := by
  have hc := coefficient_range hu
  have hs := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1)
    (t := frameCap) (by norm_num [frameCap])
  have hp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1)
    (t := frameCap) (by norm_num [frameCap])
  have ht := transport_trig (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)
  have hu0 : 0≤u := by linarith [hu.1]
  have hu2 := pow_le_pow_left₀ hu0 hu.2 2
  have hm := mul_le_mul hu.2 ht.2.2.2.1.le ht.2.2.1
    (by norm_num : (0:ℝ)≤1033/1000)
  norm_num [pairEnergy,pairProduct,k] at hs
  nlinarith

theorem norm_negative_upper {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    pairNorm k u (-frameCap)<(799/1000:ℝ) := by
  have hc := coefficient_range hu
  have hs := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1)
    (t := -frameCap) (by norm_num [frameCap])
  have hp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1)
    (t := -frameCap) (by norm_num [frameCap])
  have ht := transport_trig (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)
  have hsin : (3221/5000:ℝ)<Real.sin frameCap := by
    have hh := cap_trig.1
    norm_num [Arithmetic.sin7,frameCap] at hh
    linarith
  have hfactor : 0≤(1033/1000:ℝ)+u-2*k*Real.sin frameCap := by
    dsimp [k]
    linarith [hu.1,ht.2.2.2.1]
  have hm := mul_nonneg (sub_nonneg.mpr hu.2) hfactor
  norm_num [pairEnergy,pairProduct,k,Real.sin_neg] at hs
  dsimp [k] at hm
  nlinarith

theorem positive_cap {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    0<k*(phi frameCap-1)-R*(pairNorm k u frameCap-pairNorm k u 0)+L*frameCap := by
  have hn0 := radius_norm_lower (by norm_num : (0:ℝ)<6341/5000) (norm_zero_lower hu)
  have hnp := radius_norm_upper (by norm_num : (0:ℝ)<33/20) (norm_positive_upper hu)
  have hphi := phi_cap_lower
  dsimp [k,L,frameCap] at *
  nlinarith

theorem negative_cap {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    0<negative u frameCap := by
  have hn0 := radius_norm_lower (by norm_num : (0:ℝ)<6341/5000) (norm_zero_lower hu)
  have hnn := radius_norm_upper (by norm_num : (0:ℝ)<799/1000) (norm_negative_upper hu)
  have hcos := (transport_trig
    (by norm_num [frameCap] : frameCap∈Icc 0 frameCap)).1
  dsimp [negative,k,L,frameCap]
  nlinarith

theorem charged_nonneg {u v : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ))
    (hv : |v|≤frameCap) : 0≤charged u v := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  by_cases hpos : 0≤v
  · have hvi : v∈Icc 0 frameCap := ⟨hpos,by simpa [abs_of_nonneg hpos] using hv⟩
    have hm := (positive_concave hu).min_le_of_mem_Icc hz hh hvi
    have hmin : 0≤min
        (k*(phi 0-1)-R*(pairNorm k u 0-pairNorm k u 0)+L*0)
        (k*(phi frameCap-1)-R*(pairNorm k u frameCap-pairNorm k u 0)+L*frameCap) :=
      le_min (by simp) (positive_cap hu).le
    have hval := hmin.trans hm
    simpa [charged,psi_positive hvi] using hval
  · have hvi : -v∈Icc 0 frameCap :=
      ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hpos)] using hv⟩
    have hm := (negative_concave hu).min_le_of_mem_Icc hz hh hvi
    have hmin : 0≤min (negative u 0) (negative u frameCap) :=
      le_min (by simp [negative]) (negative_cap hu).le
    have hval := hmin.trans hm
    have he : charged u v=negative u (-v) := by
      have hpsi := psi_negative hvi
      simp only [neg_neg] at hpsi
      simp [charged,negative,hpsi,Real.cos_neg]
      ring
    rw [he]
    exact hval

/-- The full support identity includes the secant H coefficient and the
original signed HG angle. -/
theorem support_lower {u v : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ))
    (hv : |v|≤frameCap) :
    k+u-fullSupport u k≤
      k*edgeWidth v+u-fullSupport (u+k*Real.sin v) (k*Real.cos v)+L*v := by
  have h := charged_nonneg hu hv
  have he := pair_full_identity (p := k) (q := u) (a := v) (b := 0)
    hv (by norm_num [frameCap])
  norm_num [Secondary.chargedPair,pairF,pairG] at he
  dsimp [charged] at h
  linarith

/-- Actual contained H may be used directly; no support maximizer is
substituted into the source cycle. -/
theorem actual_lower {q u v : ℝ} {H : SignedPoint}
    (hy : 0≤H.y) (hc : H.Contained q) (hq : q≤qCap)
    (hu : u∈Icc 1 (1033/1000:ℝ)) (hv : |v|≤frameCap) :
    k+u-fullSupport u k≤
      k*edgeWidth v+u-((u+k*Real.sin v)*H.a+k*Real.cos v*H.y)+L*v := by
  have hsup := actual_full_support (f := u+k*Real.sin v) (g := k*Real.cos v) hy hc hq
  have hlow := support_lower hu hv
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHSecant
