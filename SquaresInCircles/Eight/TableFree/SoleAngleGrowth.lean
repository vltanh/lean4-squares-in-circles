module

public import SquaresInCircles.Eight.TableFree.SingleAngleConcentration
public import SquaresInCircles.Eight.TableFree.OrdinaryNegativeSlope
public import SquaresInCircles.Eight.TableFree.OrdinaryPositiveEnvelope

/-!
# Ordinary-angle growth at every radius in the working band

Uncompiled source. The negative growth estimate is uniform in the radius
and retains a one-angle anchor's actual negative coefficient. Together
with the positive-angle bound, it removes all separated and same-block
allocations in the middle and high sole-E coefficient families.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SoleAngleGrowth
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryAngleConcentration OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem radius_lower {R : ℝ} (hR : 0≤R) (hQ : qLow≤R^2) : 19787/10000<R := by
  norm_num [qLow] at hQ
  nlinarith

theorem endpoint_normalized_slope {R : ℝ} (hR : 0≤R) (hQ : qLow≤R^2) :
    (2/3 : ℝ)< -Real.sin frameCap+
      R*(2/3)*Real.cos frameCap/root (2/3) (Real.sin frameCap) := by
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hN := root_pos (2/3) (sin_mem hh)
  have hN2 := root_sq (2/3) (sin_mem hh)
  have hNhi : root (2/3) (Real.sin frameCap)<1913/2500 := by
    nlinarith [cap_sin_lower]
  have hc := (transport_trig hh).1
  have hs := (transport_trig hh).2.2.2.1
  have hC0 : 0<Real.cos frameCap := by linarith
  have hnum1 := mul_lt_mul_of_pos_right (radius_lower hR hQ) hC0
  have hnum2 := mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<19787/10000)
  have hupper := mul_lt_mul_of_pos_left hNhi
    (show 0<(2/3 : ℝ)+Real.sin frameCap by linarith [(transport_trig hh).2.2.1])
  have hupper2 := mul_lt_mul_of_pos_right hs (by norm_num : (0:ℝ)<1913/2500)
  have hcross : ((2/3 : ℝ)+Real.sin frameCap)*root (2/3) (Real.sin frameCap)<
      R*(2/3)*Real.cos frameCap := by nlinarith
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith

theorem Vd_lower {R p q t : ℝ} (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (ht : t∈Icc 0 frameCap) :
    (2/3)*q<Vd R p q t := by
  have hq := hp.trans_le hpq
  have hqp : q≤2*p := by linarith
  have hrlo : 2/3≤p/q := (le_div_iff₀ hq).2 hratio
  have hrhi : p/q≤1 := (div_le_one hq).2 hpq
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hfrac := normalized_fraction_mono (by norm_num : (0:ℝ)≤2/3) hrlo hrhi (sin_mem hh)
  have hmul := mul_le_mul_of_nonneg_left hfrac
    (mul_nonneg hR (show 0≤Real.cos frameCap by linarith [(transport_trig hh).1]))
  have hnorm : (2/3 : ℝ)< -Real.sin frameCap+
      R*(p/q)*Real.cos frameCap/root (p/q) (Real.sin frameCap) := by
    have hbase := endpoint_normalized_slope hR hQL
    nlinarith only [hmul,hbase]
  have hend : (2/3)*q<Vd R p q frameCap := by
    rw [Vd_normalized hq]
    nlinarith only [mul_lt_mul_of_pos_left hnorm hq]
  exact hend.trans_le ((Vd_antitone hR hQU hp hpq hqp) ht hh ht.2)

theorem VnuDeriv_lower {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) : (2/3)*q<VnuDeriv R p q nu t := by
  have hv := Vd_lower hR hQL hQU hp hpq hratio ht
  have hn := mul_le_mul_of_nonneg_right hnu (transport_trig ht).2.2.1
  dsimp [Vd,mixedNDerivative,VnuDeriv] at *
  simp only [zero_sub] at hv
  linarith

theorem Vnu_growth {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    (2/3)*q*(u-t)≤Vnu R p q nu u-Vnu R p q nu t := by
  exact derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx))
    (fun x hx => (VnuDeriv_lower hR hQL hQU hp hpq hratio hnu (Ioo_subset_Icc_self hx)).le)
    ht hu htu

theorem pure_growth {single : Bool} {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (2/3)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    (2/3)*q*(u-t)≤pure single R p q nu u-pure single R p q nu t := by
  cases single
  · simpa [pure] using Vnu_growth hR hQL hQU hp hpq hratio (le_refl q) ht hu htu
  · exact Vnu_growth hR hQL hQU hp hpq hratio hnu ht hu htu

/-- Once the coefficient intervals overlap by this explicit growth
reserve, every mixed allocation lies above the smallest pure charge. -/
theorem balanced_envelope {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (m : ι → Bool) (R : ℝ) (p q nu P N : ι → ℝ) {t L qlo qhi : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hratio : ∀ i,(2/3)*q i≤p i)
    (hnu : ∀ i,p i≤nu i ∧ nu i≤q i) (hqr : ∀ i,qlo≤q i ∧ q i≤qhi)
    (hreserve : (109/200)*qhi≤(2/3)*qlo)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (ht : t∈Icc 0 frameCap) (hbudget : (∑ i,P i)≤frameCap-t)
    (hbalance : (∑ i,N i)=t+∑ i,P i)
    (hsingle : ∀ i,m i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,L≤pure (m i) R (p i) (q i) (nu i) t) :
    L≤∑ i,F (m i) R (p i) (q i) (nu i) (P i) (N i) := by
  have hqp (i : ι) : q i≤2*p i := by linarith [hratio i]
  apply SingleAngleConcentration.lower_from_endpoints m R p q nu P N hR hQU hp hpq hqp
    (fun i => (hnu i).1) hP hN ht hbudget hbalance hsingle hpure
  · intro i hi
    have hv : L≤V R (p i) (q i) t := by simpa [pure,hi] using hpure i
    exact hv.trans (M_ge_V (hp i).le ((hp i).trans_le (hpq i)).le
      (by linarith [hratio i]) ht)
  · intro i j _
    have hlen : 0≤frameCap-t := by linarith [ht.2]
    have hU := OrdinaryPositiveEnvelope.U_lower hR hQU (hp i) (hpq i) (hqp i)
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
    have hV := pure_growth (single := m j) hR hQL hQU (hp j) (hpq j) (hratio j)
      (hnu j).2 ht (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
    have hcoef : (109/200)*q i≤(2/3)*q j := by
      linarith [(hqr i).2,(hqr j).1]
    have hm := mul_le_mul_of_nonneg_right hcoef hlen
    linarith [hpure j]

end SquaresInCircles.Eight.TableFree.SoleAngleGrowth
