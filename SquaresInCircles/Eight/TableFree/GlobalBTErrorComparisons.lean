module

public import SquaresInCircles.Eight.TableFree.GlobalBTErrorScalars
public import SquaresInCircles.Eight.TableFree.GlobalBTNominal

/-!
# Pointwise comparisons of the original AB, BT and TD dual terms

These statements compare weighted necessary-inequality expressions on
unchanged states.  They never assert feasibility after changing an
error.  Both signed transverse coordinates and both original zero
owners are retained.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def zeroDual (primary : Bool) (s t : State) (d lambda : ℝ) : ℝ :=
  d+lambda*(width d-projection false s t d (leftOwner primary))
def ABweight (d : ℝ) : ℝ := if 0≤d then kappa else kappa/Real.cos d
def retainedNegative (d : ℝ) : ℝ := -max (-d) 0

theorem width_positive {z : ℝ} (hz : z∈Icc 0 frameCap) :
    width z=(1+Real.cos z+Real.sin z)/2 := by
  rw [width,abs_of_nonneg (transport_trig hz).2.2.1]

theorem width_negative {z : ℝ} (hz : z∈Icc 0 frameCap) :
    width (-z)=(1+Real.cos z+Real.sin z)/2 := by
  rw [width,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg (transport_trig hz).2.2.1]

theorem folded_positive_gain (s : State) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    0≤z+lambda*(width z-1-s.a*Real.sin z-s.b*(1-Real.cos z)) := by
  have hs := state_support s (Real.sin z) (1-Real.cos z)
  rw [GlobalEH.half_angle_norm hz] at hs
  have hs' : s.a*Real.sin z+s.b*(1-Real.cos z)≤
      2*R*Real.sin (z/2)-(Real.sin z+1-Real.cos z)/2 := by
    convert hs using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left hs' hl
  have hg := positive_zero_gain hl hlu hz
  rw [width_positive hz]
  dsimp [positiveZeroGain] at hg
  nlinarith only [hm,hg]

theorem positive_zero_delete (s t : State) (primary : Bool) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    lambda*(1-transverse s+transverse t)≤zeroDual primary s t z lambda := by
  have hcos : 0≤1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  cases primary with
  | false =>
      have hgain := folded_positive_gain t hl hlu hz
      have hy := (transverse_bounds t).2
      have hp := mul_nonneg (sub_nonneg.mpr hy) hcos
      have hm := mul_nonneg hl hp
      dsimp [zeroDual,leftOwner,projection]
      nlinarith only [hgain,hm]
  | true =>
      have hgain := folded_positive_gain s hl hlu hz
      have hy := (transverse_bounds s).1
      have hp := mul_nonneg (show 0≤s.b+transverse s by linarith) hcos
      have hm := mul_nonneg hl hp
      dsimp [zeroDual,leftOwner,projection]
      nlinarith only [hgain,hm]

theorem negative_zero_difference (s t : State) (primary : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    (zeroDual primary s t (-z) (kappa/Real.cos z)-
      kappa*(1-transverse s+transverse t)-(9/2000)*z)*Real.cos z=
      kappa*((if primary then s.a+1/2 else t.a+1/2)*Real.sin z+
        (if primary then transverse t+1/2 else 1/2-transverse s)*(1-Real.cos z))-
          (2009/2000)*z*Real.cos z := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  cases primary <;>
    simp only [zeroDual,leftOwner,projection,Bool.false_eq_true,Bool.true_eq_true,
      if_false,if_true,Matrix.cons_val_zero,Matrix.cons_val_two,
      width_negative hz,Real.cos_neg,Real.sin_neg]
  all_goals field_simp [hc]; ring

theorem negative_zero_delete (s t : State) (primary : Bool) {z : ℝ}
    (hz : z∈Icc 0 frameCap) :
    kappa*(1-transverse s+transverse t)+(9/2000)*z≤
      zeroDual primary s t (-z) (kappa/Real.cos z) := by
  have htr := transport_trig hz
  have hcos : 0<Real.cos z := by linarith [htr.1]
  have hdiff := negative_zero_difference s t primary hz
  have hg := negative_AB_gain_scaled hz
  have h1 : 0≤1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  have hsA := (ZeroPrimary.primary_lower s).le
  have htA := (ZeroPrimary.primary_lower t).le
  have hsY : transverse s≤9/10 := (transverse_bounds s).2.trans s.b_upper
  have htY : -(9/10:ℝ)≤transverse t := by
    linarith [(transverse_bounds t).1,t.b_upper]
  cases primary with
  | false =>
      have hpa := mul_nonneg (show 0≤t.a-447/800 by linarith) htr.2.2.1
      have hpy := mul_nonneg (show 0≤9/10-transverse s by linarith) h1
      simp only [Bool.false_eq_true,if_false] at hdiff
      have hscaled : 0≤(zeroDual false s t (-z) (kappa/Real.cos z)-
          kappa*(1-transverse s+transverse t)-(9/2000)*z)*Real.cos z := by
        dsimp [kappa] at hg hdiff ⊢
        nlinarith only [hdiff,hg,hpa,hpy]
      nlinarith only [hscaled,hcos]
  | true =>
      have hpa := mul_nonneg (show 0≤s.a-447/800 by linarith) htr.2.2.1
      have hpy := mul_nonneg (show 0≤transverse t+9/10 by linarith) h1
      simp only [Bool.true_eq_true,if_true] at hdiff
      have hscaled : 0≤(zeroDual true s t (-z) (kappa/Real.cos z)-
          kappa*(1-transverse s+transverse t)-(9/2000)*z)*Real.cos z := by
        dsimp [kappa] at hg hdiff ⊢
        nlinarith only [hdiff,hg,hpa,hpy]
      nlinarith only [hscaled,hcos]

theorem ABweight_positive {d : ℝ} (hd : |d|≤frameCap) : 0<ABweight d := by
  have hc : 0<Real.cos d := by
    linarith [(CommonQuarter.signed_cos (by simpa only [frameCap] using hd)).1]
  by_cases hp : 0≤d
  · simp [ABweight,hp,kappa]
  · rw [ABweight,if_neg hp]
    exact div_pos (by norm_num [kappa]) hc

/-- Both original AB owners and either B sign, at the original error. -/
theorem AB_delete (s t : State) (primary : Bool) {d : ℝ} (hd : |d|≤frameCap) :
    kappa*(1-transverse s+transverse t)≤zeroDual primary s t d (ABweight d) := by
  by_cases hp : 0≤d
  · rw [ABweight,if_pos hp]
    exact positive_zero_delete s t primary (by norm_num [kappa]) le_rfl
      ⟨hp,(le_abs_self d).trans hd⟩
  · have hz : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    have hh := negative_zero_delete s t primary hz
    rw [ABweight,if_neg hp]
    simp only [neg_neg,Real.cos_neg] at hh
    linarith [hz.1]

theorem rotated_positive_gain (s : State) {y lambda z : ℝ}
    (hy : y≤9/10) (hl : 0≤lambda) (hlu : lambda≤kappa)
    (hz : z∈Icc 0 frameCap) :
    0≤z+lambda*(width z-1-s.a*(Real.cos z-1)-y*Real.sin z) := by
  have ht := transport_trig hz
  have ha := ZeroPrimary.primary_lower s
  have hc := mul_nonneg (show 0≤s.a-1/2 by linarith)
    (sub_nonneg.mpr (Real.cos_le_one z))
  have hsin := Real.sin_le_self hz.1
  have hyprod := mul_nonneg (show 0≤9/10-y by linarith) ht.2.2.1
  have hbase : -(2/5)*z≤width z-1-s.a*(Real.cos z-1)-y*Real.sin z := by
    rw [width_positive hz]
    nlinarith only [hc,hyprod,hsin]
  have hm := mul_le_mul_of_nonneg_left hbase hl
  have hcoef : 0≤1-(2/5)*lambda := by dsimp [kappa] at hlu; linarith
  nlinarith only [hm,mul_nonneg hcoef hz.1]

theorem positive_BT0_delete (s t : State) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    lambda*(1-projection true s t 0 0)≤
      z+lambda*(width z-projection true s t z 0) := by
  have hh := rotated_positive_gain t ((transverse_bounds t).2.trans t.b_upper) hl hlu hz
  simp only [projection,Bool.true_eq_true,if_true,Matrix.cons_val_zero,
    Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero]
  linarith

theorem positive_DE2_delete (s t : State) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    lambda*(1-projection true s t 0 2)≤
      z+lambda*(width z-projection true s t z 2) := by
  have hy : -transverse s≤9/10 := by linarith [(transverse_bounds s).1,s.b_upper]
  have hh := rotated_positive_gain s hy hl hlu hz
  simp only [projection,Bool.true_eq_true,if_true,Matrix.cons_val_two,
    Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero]
  linarith

theorem positive_DE3_delete (s t : State) {lambda z : ℝ}
    (hl : 0≤lambda) (hlu : lambda≤kappa) (hz : z∈Icc 0 frameCap) :
    lambda*(1-projection true s t 0 2)≤
      z+lambda*(width z-projection true s t z 3) := by
  have hh := positive_zero_delete s t false hl hlu hz
  dsimp [zeroDual,leftOwner,projection] at hh
  simp only [projection,Bool.true_eq_true,if_true,Matrix.cons_val_two,Matrix.cons_val_three,
    Real.cos_zero,Real.sin_zero,mul_one,mul_zero,sub_zero]
  linarith

end SquaresInCircles.Eight.TableFree.GlobalBT
