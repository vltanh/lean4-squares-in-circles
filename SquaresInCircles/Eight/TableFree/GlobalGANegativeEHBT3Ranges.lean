module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Ranges

/-!
# Native EH1 / BT3 coefficient domains

Uncompiled range step. The small-high family is precisely the existing
nonnegative-total triangle at E total zero. The far families are the
existing EH families with the base coefficient renamed m and its tilted
coefficient renamed c. All comparisons retain the original A/BT split.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Explicit
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def left : Family→ℝ | .smallLow=>0 | .smallHigh=>L | .farLow=>0 | .farHigh=>u
def right : Family→ℝ | .smallLow=>L | .farLow=>u | _=>frameCap
def eLeft : Family→ℝ | .smallLow | .smallHigh=>0 | _=>v
def eRight : Family→ℝ | .smallLow | .smallHigh=>v | _=>u
def regime : Family→NegativeEHPositiveTD.Regime
  | .smallLow | .smallHigh=>.small | _=>.far

def p (f : Family) (t z : ℝ) : Fin 4→ℝ := PositiveBT3.pWeights (k f t) (l f t) (m f t) (c f t z)
def q (f : Family) (t z : ℝ) : Fin 4→ℝ := PositiveBT3.qWeights (k f t) (l f t) (m f t) (c f t z)

@[simp] theorem smallLow_k (t : ℝ) : k .smallLow t=PositiveBT3.lowK t := rfl
@[simp] theorem smallLow_l (t : ℝ) : l .smallLow t=1 := rfl
@[simp] theorem smallLow_m (t : ℝ) : m .smallLow t=PositiveBT3.lowM t := rfl
@[simp] theorem smallHigh_k (t : ℝ) :
    k .smallHigh t=NonnegativeTotals.Explicit.k .triangle (t-L) 0 := by
  simp [k,NonnegativeTotals.Explicit.k]
@[simp] theorem smallHigh_l (t : ℝ) :
    l .smallHigh t=NonnegativeTotals.Explicit.l .triangle (t-L) 0 := by
  simp [l,NonnegativeTotals.Explicit.l]
@[simp] theorem smallHigh_m (t : ℝ) :
    m .smallHigh t=NonnegativeTotals.Explicit.c .triangle (t-L) 0 := by
  simp [m,NonnegativeTotals.Explicit.c]
@[simp] theorem smallHigh_theta (t : ℝ) :
    NonnegativeTotals.Explicit.theta .triangle (t-L) 0=t := by
  dsimp [NonnegativeTotals.Explicit.theta,L]
  ring

theorem smallHigh_domain {t : ℝ} (ht : t∈Icc L frameCap) :
    NonnegativeTotals.Explicit.Domain .triangle (t-L) 0 := by
  dsimp [NonnegativeTotals.Explicit.Domain,L,frameCap] at *
  exact ⟨by linarith [ht.1],le_rfl,by linarith [ht.2]⟩

@[simp] theorem farLow_k (t : ℝ) : k .farLow t=NegativeEHPositiveTD.Explicit.k .far .low t := rfl
@[simp] theorem farLow_l (t : ℝ) : l .farLow t=NegativeEHPositiveTD.Explicit.l .far .low t := rfl
@[simp] theorem farLow_m (t : ℝ) : m .farLow t=NegativeEHPositiveTD.Explicit.c .far .low t := rfl
@[simp] theorem farLow_c (t z : ℝ) : c .farLow t z=NegativeEHPositiveTD.Explicit.m .far .low t z := rfl
@[simp] theorem farHigh_k (t : ℝ) : k .farHigh t=NegativeEHPositiveTD.Explicit.k .far .high t := rfl
@[simp] theorem farHigh_l (t : ℝ) : l .farHigh t=NegativeEHPositiveTD.Explicit.l .far .high t := rfl
@[simp] theorem farHigh_m (t : ℝ) : m .farHigh t=NegativeEHPositiveTD.Explicit.c .far .high t := rfl
@[simp] theorem farHigh_c (t z : ℝ) : c .farHigh t z=NegativeEHPositiveTD.Explicit.m .far .high t z := rfl

theorem total_frame (f : Family) {t : ℝ} (ht : t∈Icc (left f) (right f)) : t∈Icc 0 frameCap := by
  cases f <;> norm_num [left,right,L,u,frameCap] at ht ⊢ <;>
    constructor <;> linarith [ht.1,ht.2]

theorem eh_frame (f : Family) {s : ℝ} (hs : s∈Icc (eLeft f) (eRight f)) : s∈Icc 0 frameCap := by
  cases f <;> norm_num [eLeft,eRight,v,u,frameCap] at hs ⊢ <;>
    constructor <;> linarith [hs.1,hs.2]

@[simp] theorem errorCharge_eq (f : Family) :
    NegativeEHPositiveTD.Explicit.errorCharge (regime f)=epsilon f := by
  cases f <;> rfl
@[simp] theorem gain_eq (f : Family) (s : ℝ) :
    NegativeEHPositiveTD.Explicit.gain (regime f) s=charge f s := by
  cases f <;> rfl

theorem source_coefficients (f : Family) {t z : ℝ}
    (ht : t∈Icc (left f) (right f)) (hz : z∈Icc 0 t) :
    k f t∈Icc (1/2:ℝ) (17/20) ∧ k f t≤l f t ∧ 0<m f t ∧
      k f t≤c f t z ∧ c f t z<6/5 := by
  cases f
  · have hr := PositiveBT3.Analytic.low_ranges ht
    have hc := PositiveBT3.Analytic.low_tilted_ranges ht hz
    simp only [smallLow_k,smallLow_l,smallLow_m,c]
    dsimp [PositiveBT3.K,PositiveBT3.Cmax] at hr hc
    exact ⟨⟨by linarith [hr.1.1],by linarith [hr.1.2]⟩,
      by linarith [hr.1.2],by linarith [hr.2.1],by linarith [hr.1.2,hr.2.1,hc.1],by linarith [hc.2]⟩
  · have hd := smallHigh_domain ht
    have hb := NonnegativeTotals.Explicit.base_bounds .triangle hd
    have hz' : z∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (t-L) 0) := by simpa using hz
    have hlo := NonnegativeTotals.Explicit.tilted_lower .triangle hd hz'
    have hhi := NonnegativeTotals.Explicit.tilted_upper .triangle hd hz'
    simpa [c,NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,
      PositiveBT3.tilted,PositiveTD.tilted,smallHigh_k,smallHigh_l,smallHigh_m] using
      (show NonnegativeTotals.Explicit.k .triangle (t-L) 0∈Icc (1/2:ℝ) (17/20) ∧
        NonnegativeTotals.Explicit.k .triangle (t-L) 0≤NonnegativeTotals.Explicit.l .triangle (t-L) 0 ∧
        0<NonnegativeTotals.Explicit.c .triangle (t-L) 0 ∧
        NonnegativeTotals.Explicit.k .triangle (t-L) 0≤NonnegativeTotals.Explicit.tilted .triangle (t-L) 0 z ∧
        NonnegativeTotals.Explicit.tilted .triangle (t-L) 0 z<6/5 from
        ⟨⟨by linarith [hb.k_lower],by linarith [hb.k_upper]⟩,hb.k_le_l,hb.c_positive,hlo.le,hhi⟩)
  · have hr := NegativeEHPositiveTD.Explicit.far_low_ranges ht
    have hc := NegativeEHPositiveTD.Explicit.far_low_tilted ht hz
    simp only [farLow_k,farLow_l,farLow_m,farLow_c,NegativeEHPositiveTD.Explicit.k]
    exact ⟨by norm_num,by linarith [hr.2.1.1],by linarith [hr.2.2.1.1],
      by linarith [hr.2.2.1.1,hc.1],by linarith [hc.2.1]⟩
  · have hr := NegativeEHPositiveTD.Explicit.far_high_ranges ht
    have hc := NegativeEHPositiveTD.Explicit.far_high_tilted ht hz
    simp only [farHigh_k,farHigh_l,farHigh_m,farHigh_c]
    exact ⟨⟨by linarith [hr.1.1],by linarith [hr.1.2]⟩,
      by linarith [hr.1.2,hr.2.1.1],by linarith [hr.2.2.1.1],
      (hc.2.2.1.trans_le (min_le_right _ _)).le,
      (le_max_right _ _).trans_lt hc.2.2.2.1 |>.trans (by norm_num)⟩

theorem far_k (f : Family) {t : ℝ} (hf : far f=true)
    (ht : t∈Icc (left f) (right f)) : k f t∈Icc (3/5:ℝ) (4/5) := by
  cases f
  · simp [far] at hf
  · simp [far] at hf
  · norm_num [k]
  · exact NegativeEHPositiveTD.Explicit.far_k_domain .high ht

theorem smallHigh_pairs {t z : ℝ} (ht : t∈Icc L frameCap) (hz : z∈Icc 0 t) (i : Fin 4) :
    0<p .smallHigh t z i ∧ p .smallHigh t z i≤q .smallHigh t z i ∧
      2*q .smallHigh t z i≤3*p .smallHigh t z i := by
  have hd := smallHigh_domain ht
  have hh := PositiveBT3.Balanced.pair_domain .triangle hd (by simpa using hz) i
  simpa [p,q,c,smallHigh_k,smallHigh_l,smallHigh_m,NonnegativeTotals.Explicit.tilted,
    NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted,PositiveTD.tilted] using hh

theorem smallHigh_scale {t z : ℝ} (ht : t∈Icc L frameCap) (hz : z∈Icc 0 t) (i : Fin 4) :
    min 1 (l .smallHigh t)≤q .smallHigh t z i ∧
      q .smallHigh t z i≤(6/5)*min 1 (l .smallHigh t) := by
  have hh := PositiveBT3.Balanced.scale_bounds .triangle (smallHigh_domain ht) (by simpa using hz) i
  simpa [q,c,smallHigh_k,smallHigh_l,smallHigh_m,NonnegativeTotals.Explicit.tilted,
    NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted,PositiveTD.tilted] using hh

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Explicit
