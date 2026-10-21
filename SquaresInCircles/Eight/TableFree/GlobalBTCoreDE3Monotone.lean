module

public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3PrefixTransfer
public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Small
public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Base
public import SquaresInCircles.Eight.TableFree.GlobalBTCoreDE3Concentration

/-!
# Complete core-E negative-DE3 scalar closure

Both saturated prefix placements increase from their certified
aligned value.  Together with the full small-DE polynomial, this
closes both TD owners and every retained negative-error allocation.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3

open FrameCircleArc

theorem firstD_positive {p e : ℝ} (hp : p∈Icc 0 frameCap)
    (he : e∈Icc m (141/100:ℝ)) : 0<firstD p e := by
  have hm : 0<m := by norm_num [m]
  have hepos := hm.trans_le he.1
  have hc := weight_pos hp
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hNm := tailNorm_pos hm hc hzero
  have hNe := tailNorm_pos hepos hc hzero
  have hsm := tailNorm_sq hm hc hzero
  have hse := tailNorm_sq hepos hc hzero
  have hpow := pow_le_pow_left₀ hm.le he.1 2
  have hnorm : tailNorm m (weight p) 0≤tailNorm e (weight p) 0 := by
    simp only [Real.sin_zero,mul_zero,sub_zero] at hsm hse
    nlinarith only [hsm,hse,hpow,hNm,hNe]
  have hratio := div_le_div_of_nonneg_left hc.le hNm hnorm
  have hprod := mul_le_mul_of_nonneg_left hratio
    (show 0≤R*slope by exact mul_nonneg R_pos.le (by norm_num [slope]))
  have hbase := firstD_at_m_positive hp
  dsimp [firstD] at hbase ⊢
  nlinarith only [hbase,hprod]

theorem lastD_positive {p e : ℝ} (hp : p∈Icc 0 frameCap)
    (he : e∈Icc m (141/100:ℝ)) : 0<lastD p e := by
  have hratio := prefixRatio_monotone hp
    (show m∈Icc m (141/100:ℝ) by norm_num [m]) he he.1
  have hm := mul_le_mul_of_nonneg_left hratio R_pos.le
  have hbase := lastD_at_m_positive hp
  dsimp [lastD] at hbase ⊢
  nlinarith only [hbase,hm]

theorem first_monotone (t : ℝ) {e : ℝ} (he : e∈Icc m (141/100:ℝ)) :
    MonotoneOn (fun p => first p t e) (Icc 0 frameCap) := by
  have hepos : 0<e := by dsimp [m] at he; linarith [he.1]
  apply monoOn_of_hasDeriv_nonneg
  · exact fun p hp => (first_deriv (t := t) hp hepos).continuousAt.continuousWithinAt
  · exact fun p hp => first_deriv (t := t) (Ioo_subset_Icc_self hp) hepos
  · exact fun p hp => (firstD_positive (Ioo_subset_Icc_self hp) he).le

theorem last_monotone (t : ℝ) {e : ℝ} (he : e∈Icc m (141/100:ℝ)) :
    MonotoneOn (fun p => last p t e) (Icc 0 frameCap) := by
  have hepos : 0<e := by dsimp [m] at he; linarith [he.1]
  apply monoOn_of_hasDeriv_nonneg
  · exact fun p hp => (last_deriv (t := t) hp hepos).continuousAt.continuousWithinAt
  · exact fun p hp => last_deriv (t := t) (Ioo_subset_Icc_self hp) hepos
  · exact fun p hp => (lastD_positive (Ioo_subset_Icc_self hp) he).le

theorem first_zero_le {p t e : ℝ} (hp : p∈Icc 0 frameCap)
    (he : e∈Icc m (141/100:ℝ)) : first 0 t e≤first p t e :=
  first_monotone t he (by norm_num [frameCap]) hp hp.1

theorem last_zero_le {p t e : ℝ} (hp : p∈Icc 0 frameCap)
    (he : e∈Icc m (141/100:ℝ)) : last 0 t e≤last p t e :=
  last_monotone t he (by norm_num [frameCap]) hp hp.1

theorem endpoints_strict {p t : ℝ} (hp : p∈Icc 0 frameCap) (ht : t∈Icc 0 frameCap) :
    pathThreshold<first p t (endpointWeight t) ∧ pathThreshold<last p t (endpointWeight t) := by
  by_cases hsmall : t≤1/5
  · rw [endpointWeight,if_pos hsmall]
    exact small_endpoints hp ⟨ht.1,hsmall⟩
  · have hsat : t∈Icc (1/5:ℝ) frameCap := ⟨by linarith,ht.2⟩
    have he := saturated_weight_bounds ht
    have hbase := saturated_base hsat
    have hfirst := first_zero_le (t := t) hp ⟨he.1,he.2.le⟩
    have hlast := last_zero_le (t := t) hp ⟨he.1,he.2.le⟩
    rw [first_zero] at hfirst
    rw [last_zero] at hlast
    rw [endpointWeight,if_neg hsmall]
    exact ⟨hbase.trans_le hfirst,hbase.trans_le hlast⟩

/-- No residual scalar or derivative premise remains: both original
TD owners and the complete shared negative-error simplex are covered. -/
theorem tail_strict (second : Bool) {r s t : ℝ}
    (hr : 0≤r) (hs : 0≤s) (ht : 0≤t) (hcap : r+s+t≤frameCap) :
    pathThreshold<tail second (endpointWeight t) (weight (r+s)) r s t := by
  have hp : r+s∈Icc 0 frameCap := ⟨add_nonneg hr hs,by linarith⟩
  have htdom : t∈Icc 0 frameCap := ⟨ht,by linarith⟩
  have he : 0<endpointWeight t := by
    have hh := (endpointWeight_bounds htdom).1
    dsimp [kappa] at hh
    linarith
  have hends := endpoints_strict hp htdom
  exact (lt_min hends.1 hends.2).trans_le (concentrated_lower second hr hs hp.2 he)

end SquaresInCircles.Eight.TableFree.GlobalBT.CoreDE3
