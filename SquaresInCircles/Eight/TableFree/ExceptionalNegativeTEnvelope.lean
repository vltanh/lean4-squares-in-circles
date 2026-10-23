module

public import SquaresInCircles.Eight.TableFree.ExceptionalNegativeTOrdinaryData

/-!
# Full signed ordinary envelope for exceptional negative T

Uncompiled source. Both sign totals are concentrated continuously on
originally occupied blocks. For negative net balance the own-block
terminal chord pays the entire positive budget. For positive net balance
the mixed H/B alternative and separated alternatives retain the actual
ordinary signs and the original EH error.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.ExceptionalNegativeTEnvelope
open Candidate ExceptionalECoefficients ExceptionalNegativeTOrdinaryData
open CriticalNegativeTOrdinaryData (shortDomain short_small single)
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity CorrelatedSameBlock

def minimumThree (f : Fin 3 → ℝ) : ℝ := min (f 0) (min (f 1) (f 2))
theorem minimumThree_le (f : Fin 3 → ℝ) (i : Fin 3) : minimumThree f≤f i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
theorem lt_minimumThree {f : Fin 3 → ℝ} {a : ℝ} (h : ∀ i,a<f i) : a<minimumThree f :=
  lt_min (h 0) (lt_min (h 1) (h 2))

def lowerEnvelope (b : Band) (R t : ℝ) (face : Bool) (s : ℝ) : ℝ :=
  if s≤t then minimumThree (fun i => canonical b R t face i (t-s))
  else -positiveCost b*(s-t)

theorem canonical_zero (b : Band) (R t : ℝ) (face : Bool) (i : Fin 3) :
    canonical b R t face i 0=0 := by simp [canonical,Vnu]

theorem canonical_concave (face : Bool) {b : Band} {R t : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap) (ht : t∈domain b) (i : Fin 3) :
    ConcaveOn ℝ (Icc 0 frameCap) (canonical b R t face i) := by
  have hc := canonical_conditions face ht i
  exact Vnu_concave hR hQU hc.1 min_le_max hc.2.2.2 hc.2.1

theorem canonical_linear (face : Bool) {b : Band} {R t v : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hv : v∈Icc 0 frameCap) (i : Fin 3) :
    positiveCost b*v≤canonical b R t face i v := by
  have hh : 0<frameCap := by norm_num [frameCap]
  have hα : 0≤v/frameCap ∧ v/frameCap≤1 :=
    ⟨div_nonneg hv.1 hh.le,(div_le_one hh).2 hv.2⟩
  have hc := canonical_concave face hR hQU ht i
  have hch := hc.2 ⟨le_rfl,hh.le⟩ ⟨hh.le,le_rfl⟩
    (sub_nonneg.mpr hα.2) hα.1 (by ring)
  have he : (1-v/frameCap)*0+(v/frameCap)*frameCap=v := by field_simp [hh.ne']; ring
  simp only [smul_eq_mul,he,canonical_zero,mul_zero,zero_add] at hch
  have hend := canonical_growth face hR hQL hQU ht
    (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,(angle ht).1⟩) i
  rw [canonical_zero,sub_zero,sub_zero] at hend
  have hm := mul_le_mul_of_nonneg_left hend hα.1
  have hid : (v/frameCap)*(positiveCost b*frameCap)=positiveCost b*v := by
    field_simp [hh.ne']
    ring
  rw [hid] at hm
  exact hm.trans hch

theorem mixed_canonical (face : Bool) {b : Band} {t s : ℝ} {td : Bool}
    (ht : t∈domain b) (i : Fin 3) (hi : single td i=false) :
    p b t face td s i=canonicalP b t face i ∧
      q b t face td s i=canonicalQ b t face i ∧
      canonicalNu b t face i=canonicalQ b t face i := by
  rcases CriticalNegativeTOrdinaryData.mixed_indices hi with rfl | ⟨rfl,rfl⟩
  · simp [p,q,canonicalP,canonicalQ,canonicalNu,nu,CriticalNegativeTOrdinaryData.small,
      CriticalNegativeTOrdinaryData.large,CriticalNegativeTOrdinaryData.alpha,
      CriticalNegativeTOrdinaryData.beta,CriticalNegativeTOrdinaryData.nu]
  · have ho := coefficient_order ht
    simp [p,q,canonicalP,canonicalQ,canonicalNu,nu,CriticalNegativeTOrdinaryData.small,
      CriticalNegativeTOrdinaryData.large,CriticalNegativeTOrdinaryData.alpha,
      CriticalNegativeTOrdinaryData.beta,CriticalNegativeTOrdinaryData.nu,
      CriticalNegativeTOrdinaryData.bWeight,max_eq_right ho.2.2.1]

theorem mixed_ratio (face : Bool) {b : Band} {t s : ℝ} {td : Bool}
    (ht : t∈domain b) (i : Fin 3) (hi : single td i=false) :
    (117/200)*q b t face td s i≤p b t face td s i := by
  rw [(mixed_canonical face ht i hi).1,(mixed_canonical face ht i hi).2.1]
  by_cases hb : b=.low
  · subst b
    have hh := low_canonical face ht i
    have hq0 : 0≤canonicalQ .low t face i := by linarith [hh.2.2.2.2.1]
    nlinarith [hh.2.2.2.2.2,mul_nonneg ht.1 hq0]
  · have hh := balanced_canonical face hb ht i
    nlinarith [hh.2.2.2.1,hh.2.2.2.2.1]

theorem mixed_negative (face : Bool) {b : Band} {R t s d : ℝ} {td : Bool}
    (ht : t∈domain b) (hd : d∈Icc 0 t) (i : Fin 3) (hi : single td i=false) :
    canonical b R t face i d≤M R (p b t face td s i) (q b t face td s i) d := by
  have he := mixed_canonical face ht i hi
  have hc := canonical_conditions face ht i
  have hq0 := hc.1.trans_le (min_le_max : canonicalP b t face i≤canonicalQ b t face i)
  have hd' : d∈Icc 0 frameCap := ⟨hd.1,hd.2.trans (angle ht).2⟩
  rw [he.1,he.2.1]
  change Vnu R (canonicalP b t face i) (canonicalQ b t face i) (canonicalNu b t face i) d≤_
  rw [he.2.2,Vnu_larger]
  by_cases hb : b=.low
  · subst b
    have hr := (low_canonical face ht i).2.2.2.2.2
    have hcorr : PositiveStressCoefficients.ratio d*canonicalQ .low t face i≤canonicalP .low t face i := by
      dsimp [PositiveStressCoefficients.ratio]
      nlinarith [mul_nonneg (show 0≤(7/20)*t-(1/5)*d by linarith [ht.1,hd.2]) hq0.le]
    have hm := CorrelatedSameBlock.negative_surplus (R := R) hq0.le hcorr hd'
      (show (0:ℝ)∈Icc 0 d from ⟨le_rfl,hd.1⟩)
    have hid : mixedBlock R (canonicalP .low t face i) (canonicalQ .low t face i)
        (frameCap-d) frameCap=M R (canonicalP .low t face i) (canonicalQ .low t face i) d := by
      simpa only [show d+(frameCap-d)=frameCap by ring] using
        mixedBlock_saturated R (canonicalP .low t face i) (canonicalQ .low t face i) d
    simpa only [sub_zero,hid] using hm
  · exact M_ge_V hc.1.le hq0.le (balanced_canonical face hb ht i).2.2.2.1 hd'

theorem negative_balance (face : Bool) {b : Band} {R t s : ℝ} {td : Bool} (P N : Fin 3 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hs : s∈shortDomain td) (hst : s≤t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t-s+∑i,P i)
    (hsingle : ∀ i,single td i=true → P i=0 ∨ N i=0) :
    minimumThree (fun i => canonical b R t face i (t-s))≤
      ∑i,F (single td i) R (p b t face td s i) (q b t face td s i) (nu b t face td s i) (P i) (N i) := by
  have hs0 := (short_small hs).1
  have hd : t-s∈Icc 0 t := ⟨sub_nonneg.mpr hst,by linarith⟩
  have hd' : t-s∈Icc 0 frameCap := ⟨hd.1,hd.2.trans (angle ht).2⟩
  apply SingleAngleConcentration.lower_from_endpoints (single td) R
    (p b t face td s) (q b t face td s) (nu b t face td s) P N
    hR hQU (fun i => (actual_conditions face ht hs i).1) (fun _ => min_le_max)
    (fun i => (actual_conditions face ht hs i).2.2.2.1)
    (fun i => (actual_conditions face ht hs i).2.1)
    hP hN hd' (by linarith) hbalance hsingle
  · intro i
    exact (minimumThree_le _ i).trans (canonical_le_pure face hR ht hs hd' i)
  · intro i hi
    exact (minimumThree_le _ i).trans (mixed_negative face ht hd i hi)
  · intro i j _
    have hu := positive_lower face hR hQU ht hs
      (show frameCap-(t-s)∈Icc 0 frameCap from ⟨by linarith [hd'.2],by linarith [hd'.1]⟩) i
    have hg := canonical_growth face hR hQL hQU ht hd j
    have hv := canonical_le_pure face hR ht hs (by norm_num [frameCap]) j
    have hm := minimumThree_le (fun i => canonical b R t face i (t-s)) j
    linarith

def data (face : Bool) {b : Band} {R t s : ℝ} {td : Bool}
    (hR : 0≤R) (hQU : R^2≤qCap) (ht : t∈domain b) (hs : s∈shortDomain td) :
    OccupiedSignedConcentration.Data (Fin 3) where
  U := fun i => U R (p b t face td s i) (q b t face td s i)
  V := fun i => pure (single td i) R (p b t face td s i) (q b t face td s i) (nu b t face td s i)
  F := fun i => F (single td i) R (p b t face td s i) (q b t face td s i) (nu b t face td s i)
  single := single td
  U_zero := fun i => U_zero _ _ _
  V_zero := fun i => pure_zero _ _ _ _ _
  F_left := fun i N => F_zero_left _ _ _ _ _ N
  F_right := fun i P => F_zero_right _ _ _ _ _ P
  U_concave := fun i => U_concave hR hQU (actual_conditions face ht hs i).1
    min_le_max (actual_conditions face ht hs i).2.2.2.1
  V_concave := fun i => pure_concave hR hQU (actual_conditions face ht hs i).1
    min_le_max (actual_conditions face ht hs i).2.2.2.1 (actual_conditions face ht hs i).2.1
  F_concave_P := fun i N hN => F_concave_P hR hQU (actual_conditions face ht hs i).1
    min_le_max (actual_conditions face ht hs i).2.2.2.1 hN
  F_concave_N := fun i P hP => F_concave_N hR hQU (actual_conditions face ht hs i).1
    min_le_max (actual_conditions face ht hs i).2.2.2.1 (actual_conditions face ht hs i).2.1 hP

theorem mixed_positive_line {R a b d : ℝ} (ha : 0<a) (hb : 0<b) (hd : d∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc d frameCap) (fun P => mixedBlock R a b P (P-d)) := by
  have hc : ConcaveOn ℝ (Icc d frameCap)
      (fun P => a*(phi P-1)+b*(Real.cos (P-d)-1)-R*(pairNorm a b d-pairNorm a b 0)) := by
    apply concave_of_deriv2
      (f' := fun P => a*(Real.cos P-Real.sin P)-b*Real.sin (P-d))
      (f'' := fun P => -a*(Real.sin P+Real.cos P)-b*Real.cos (P-d))
    · intro P hP
      have hA := ((phi_hasDerivAt P).sub_const 1).const_mul a
      have hB := ((((hasDerivAt_id P).sub_const d).cos).sub_const 1).const_mul b
      convert (hA.add hB).sub_const (R*(pairNorm a b d-pairNorm a b 0)) using 1 <;> ring
    · intro P hP
      have hA := ((Real.hasDerivAt_cos P).sub (Real.hasDerivAt_sin P)).const_mul a
      have hB := (((hasDerivAt_id P).sub_const d).sin).const_mul b
      convert hA.sub hB using 1 <;> ring
    · intro P hP
      have hP' : P∈Icc 0 frameCap := ⟨hd.1.trans hP.1,hP.2⟩
      have hN' : P-d∈Icc 0 frameCap := ⟨sub_nonneg.mpr hP.1,by linarith [hP.2,hd.1]⟩
      have hA := transport_trig hP'
      have hB := transport_trig hN'
      nlinarith [mul_nonneg ha.le (show 0≤Real.sin P+Real.cos P by linarith [hA.1,hA.2.2.1]),
        mul_nonneg hb.le (show 0≤Real.cos (P-d) by linarith [hB.1])]
  convert hc using 1
  funext P
  simp only [mixedBlock,show P-(P-d)=d by ring]

theorem positive_balance (face : Bool) {b : Band} {R t s : ℝ} {td : Bool} (P N : Fin 3 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hs : s∈shortDomain td) (hts : t≤s)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t-s+∑i,P i)
    (hsingle : ∀ i,single td i=true → P i=0 ∨ N i=0) :
    -positiveCost b*(s-t)≤
      ∑i,F (single td i) R (p b t face td s i) (q b t face td s i) (nu b t face td s i) (P i) (N i) := by
  let D := data face hR hQU ht hs
  have hs' := short_small hs
  have hd : s-t∈Icc 0 frameCap := ⟨sub_nonneg.mpr hts,by linarith [hs'.2,(angle ht).1]⟩
  apply D.lower_from_endpoints P N hP hN (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    hd (by linarith [(angle ht).1]) (by linarith) hsingle
  · intro i hi
    have hp := (actual_conditions face ht hs i).1
    have hq := hp.trans_le (min_le_max : p b t face td s i≤q b t face td s i)
    have hh := mixed_positive_line (R := R) hp hq hd
    simpa [D,data,F,hi,max_eq_right hd.1,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hh
  · intro hz i
    have heq : s-t=0 := le_antisymm hz hd.1
    simp [D,data,heq]
  · intro _ i
    simpa only [sub_zero] using positive_lower face hR hQU ht hs hd i
  · intro i hi
    have hp := (actual_conditions face ht hs i).1
    have hq := hp.trans_le (min_le_max : p b t face td s i≤q b t face td s i)
    have hm := CorrelatedSameBlock.positive_surplus (R := R) hq.le (mixed_ratio face ht i hi)
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
      (show frameCap-(s-t)∈Icc 0 frameCap from ⟨by linarith [hd.2],by linarith [hd.1]⟩)
    have hu := positive_lower face hR hQU ht hs hd i
    simp only [show frameCap-(frameCap-(s-t))=s-t by ring] at hm
    simpa [D,data,F,hi] using hu.trans hm
  · intro i j _
    have hu := positive_lower face hR hQU ht hs (by norm_num [frameCap]) i
    have hv0 : frameCap-(s-t)∈Icc 0 frameCap := ⟨by linarith [hd.2],by linarith [hd.1]⟩
    have hvc := canonical_linear face hR hQL hQU ht hv0 j
    have hv := canonical_le_pure face hR ht hs hv0 j
    change -positiveCost b*(s-t)≤_+_
    linarith

theorem ordinary_lower (face : Bool) {b : Band} {R t s : ℝ} {td : Bool} (P N : Fin 3 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (ht : t∈domain b) (hs : s∈shortDomain td)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t-s+∑i,P i)
    (hsingle : ∀ i,single td i=true → P i=0 ∨ N i=0) :
    lowerEnvelope b R t face s≤
      ∑i,F (single td i) R (p b t face td s i) (q b t face td s i) (nu b t face td s i) (P i) (N i) := by
  by_cases hst : s≤t
  · simpa [lowerEnvelope,hst] using
      negative_balance face P N hR hQL hQU ht hs hst hP hN hbudget hbalance hsingle
  · simpa [lowerEnvelope,hst] using
      positive_balance face P N hR hQL hQU ht hs (lt_of_not_ge hst).le hP hN hbudget hbalance hsingle

end SquaresInCircles.Eight.TableFree.ExceptionalNegativeTEnvelope
