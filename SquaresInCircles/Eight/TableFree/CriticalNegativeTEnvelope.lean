module

public import SquaresInCircles.Eight.TableFree.CriticalNegativeTOrdinaryData

/-!
# Critical negative-T concentration with an arbitrary EH error

Uncompiled source. Removing the genuine negative primary leaves balance
N−P=t−s. For s≤t the admissible budget is enlarged to h−(t−s), so the
existing continuous endpoint principle applies directly. The pure
minimum retains both A and B; the mixed H block is never suppressed.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CriticalNegativeTEnvelope
open Candidate CriticalECoefficients CriticalNegativeTOrdinaryData
open CriticalNegativeTContinuation PositiveAngularEnvelope
open OrdinaryAngleConcavity OrdinaryAngleConcentration OrdinaryNegativeSlope
open SingleAngleConcavity SoleNormGain CorrelatedSameBlock

theorem B_short {R t k l c eta v : ℝ} (hR : 0≤R) (hQU : R^2≤qCap)
    (h : Bounds t k l c eta) (hv : v∈Icc 0 frameCap) : V R l c v≤(23/20)*v := by
  have ho := h.order
  have hc : 0<c := by linarith [h.c_lower]
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hanti := Vd_antitone hR hQU h.ell_pos ho.2.2.1 ho.2.2.2.2.1
  have hd := derivative_reserve (f := fun x => -V R l c x)
    (df := fun x => -Vd R l c x) (k := -Vd R l c 0)
    (fun x hx => (V_hasDerivAt h.ell_pos hc hx).neg.continuousAt.continuousWithinAt)
    (fun x hx => (V_hasDerivAt h.ell_pos hc (Ioo_subset_Icc_self hx)).neg)
    (fun x hx => neg_le_neg (hanti hz (Ioo_subset_Icc_self hx) hx.1.le)) hz hv hv.1
  have hm := mul_le_mul_of_nonneg_right (CriticalEPureCharges.B_zero_slope ⟨hR,hR2⟩ h) hv.1
  simp only [V_zero,neg_zero,sub_zero] at hd
  linarith

theorem B_charge_lower {R t k l c eta x e s v : ℝ} {td : Bool}
    (hR : 0≤R) (h : Bounds t k l c eta) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 frameCap) :
    V R l c v≤pure (single td 2) R (small k l c eta x e s td 2)
      (large k l c eta x e s td 2) (nu k l c eta x e s td 2) v := by
  obtain ⟨_,_,hp,hq⟩ := AB_data (x := x) (e := e) h hs
  rw [hp,hq]
  cases td
  · have hb := b_bounds h hs
    have hm := HalfRatioNormGain.larger_monotone hR h.ell_pos h.order.2.2.1 hb.1 hb.2.2.2.1 hv
    have hpen := mul_nonneg (sub_nonneg.mpr h.order.2.2.1)
      (show 0≤1-Real.cos v by linarith [Real.cos_le_one v])
    simp only [single,nu,Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,
      Bool.not_false,pure,if_true,Bool.false_eq_true,if_false]
    dsimp [V,Vnu,normGain] at *
    linarith
  · simp [single,nu,bWeight,pure]

theorem pure_near {R t k l c eta x e s v : ℝ} {td : Bool}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 (4/25:ℝ)) (i : Fin 3) :
    min (Vnu R l k l v) (V R l c v)≤pure (single td i) R
      (small k l c eta x e s td i) (large k l c eta x e s td i)
      (nu k l c eta x e s td i) v := by
  have hv' : v∈Icc 0 frameCap := ⟨hv.1,by dsimp [frameCap]; linarith [hv.2]⟩
  fin_cases i
  · have hw := wide_data td h hx he
    have hh := SoleLowChargeBounds.wide_short hR hQL hw.1 min_le_max
      (show large k l c eta x e s td 0∈Icc 1 (28/25:ℝ) from ⟨hw.2.1,by linarith [hw.2.2]⟩)
      (show large k l c eta x e s td 0≤28/25 by linarith [hw.2.2])
      (show v∈SoleECoefficients.domain .low from ⟨hv.1,by linarith [hv.2]⟩)
    have hB := B_short hR hQU h hv'
    have hlow := min_le_right (Vnu R l k l v) (V R l c v)
    simp only [single,Matrix.cons_val_zero,pure,if_false]
    rw [← Vnu_larger]
    nlinarith
  · obtain ⟨hp,hq,_,_⟩ := AB_data (x := x) (e := e) h hs
    rw [hp,hq]
    simpa [single,nu,pure] using min_le_left (Vnu R l k l v) (V R l c v)
  · exact (min_le_right _ _).trans (B_charge_lower hR h hs hv')

theorem pure_far {R t k l c eta x e s : ℝ} {td : Bool}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (i : Fin 3) :
    V R l c frameCap≤pure (single td i) R (small k l c eta x e s td i)
      (large k l c eta x e s td i) (nu k l c eta x e s td i) frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  fin_cases i
  · have hw := wide_data td h hx he
    have hh := SoleLowChargeBounds.wide_cap hR hQL hw.1 min_le_max
      (show large k l c eta x e s td 0∈Icc 1 (28/25:ℝ) from ⟨hw.2.1,by linarith [hw.2.2]⟩)
      (show large k l c eta x e s td 0≤28/25 by linarith [hw.2.2])
    have hB := CriticalEPureCharges.B_cap ⟨hR,hR2⟩ h
    simp only [single,Matrix.cons_val_zero,pure,if_false]
    rw [← Vnu_larger]
    linarith
  · obtain ⟨hp,hq,_,_⟩ := AB_data (x := x) (e := e) h hs
    rw [hp,hq]
    simpa [single,nu,pure] using CriticalEPureCharges.A_ge_B_at_cap ⟨hR,hR2⟩ h
  · exact B_charge_lower hR h hs (by norm_num [frameCap])

theorem B_gap {R t k l c eta v : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hQU : R^2≤qCap) (h : Bounds t k l c eta) (hv : v∈Icc 0 (4/25:ℝ)) :
    gamma*(frameCap-v)<V R l c frameCap-V R l c v := by
  have hh := ExceptionalSmallGap.scaled_gap hR hQL hQU
    (show ExceptionalSmallGap.scale≤c by dsimp [ExceptionalSmallGap.scale]; linarith [h.c_lower])
    h.order.2.2.1 h.order.2.2.2.1
    (show v∈Icc 0 (9/50:ℝ) from ⟨hv.1,by linarith [hv.2]⟩)
  have hlen : 0≤frameCap-v := by dsimp [frameCap]; linarith [hv.2]
  dsimp [ExceptionalSmallGap.scale,gamma] at *
  nlinarith

theorem negative_balance {R t k l c eta x e s : ℝ} {td : Bool} (P N : Fin 3 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (hst : s≤t)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t-s+∑i,P i)
    (hsingle : ∀ i,single td i=true → P i=0 ∨ N i=0) :
    min (Vnu R l k l (t-s)) (V R l c (t-s))≤
      ∑ i,F (single td i) R (small k l c eta x e s td i)
        (large k l c eta x e s td i) (nu k l c eta x e s td i) (P i) (N i) := by
  have hs' := short_small hs
  have hd : t-s∈Icc 0 (4/25:ℝ) := ⟨sub_nonneg.mpr hst,by linarith [h.angle_upper,hs'.1]⟩
  have hd' : t-s∈Icc 0 frameCap := ⟨hd.1,by dsimp [frameCap]; linarith [hd.2]⟩
  apply SingleAngleConcentration.lower_from_endpoints (single td) R
    (small k l c eta x e s td) (large k l c eta x e s td) (nu k l c eta x e s td) P N
    hR hQU (fun i => (conditions h hx he hs i).1) (fun _ => min_le_max)
    (fun i => (conditions h hx he hs i).2.2.2.1) (fun i => (conditions h hx he hs i).2.1)
    hP hN hd' (by linarith [hs'.1]) hbalance hsingle
    (fun i => pure_near hR hQL hQU h hx he hs hd i)
  · intro i hi
    have hr := mixed_ratio h hx he hs i hi
    have hq0 := (conditions h hx he hs i).1.trans_le
      (min_le_max : small k l c eta x e s td i≤large k l c eta x e s td i)
    have hc : PositiveStressCoefficients.ratio (t-s)*large k l c eta x e s td i≤
        small k l c eta x e s td i := by
      dsimp [PositiveStressCoefficients.ratio]
      nlinarith [mul_le_mul_of_nonneg_right hd.2 hq0.le]
    have hm := CorrelatedSameBlock.negative_surplus (R := R) hq0.le hc hd'
      (show (0:ℝ)∈Icc 0 (t-s) from ⟨le_rfl,hd.1⟩)
    have hpu := pure_near hR hQL hQU h hx he hs hd i
    simp only [pure,hi,if_false] at hpu
    have hid : mixedBlock R (small k l c eta x e s td i) (large k l c eta x e s td i)
        (frameCap-(t-s)) frameCap=M R (small k l c eta x e s td i)
          (large k l c eta x e s td i) (t-s) := by
      simpa only [show t-s+(frameCap-(t-s))=frameCap by ring] using
        mixedBlock_saturated R (small k l c eta x e s td i) (large k l c eta x e s td i) (t-s)
    simpa only [sub_zero,hid] using hpu.trans hm
  · intro i j _
    have hu := positive_lower hR hQU h hx he hs
      (show frameCap-(t-s)∈Icc 0 frameCap from ⟨by linarith [hd'.2],by linarith [hd'.1]⟩) i
    have hv := pure_far hR hQL hQU h hx he hs j
    have hg := B_gap hR hQL hQU h hd
    have hl := min_le_right (Vnu R l k l (t-s)) (V R l c (t-s))
    linarith

theorem mixed_positive_line {R t k l c eta x e s d : ℝ} {td : Bool}
    (h : Bounds t k l c eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t)
    (hs : s∈shortDomain td) (hd : d∈Icc 0 frameCap) (i : Fin 3) (hi : single td i=false) :
    ConcaveOn ℝ (Icc d frameCap) (fun P =>
      F (single td i) R (small k l c eta x e s td i) (large k l c eta x e s td i)
        (nu k l c eta x e s td i) P (P-d)) := by
  let p := small k l c eta x e s td i
  let q := large k l c eta x e s td i
  have hp : 0<p := (conditions h hx he hs i).1
  have hq : 0<q := hp.trans_le min_le_max
  have hc : ConcaveOn ℝ (Icc d frameCap)
      (fun P => p*(phi P-1)+q*(Real.cos (P-d)-1)-R*(pairNorm p q d-pairNorm p q 0)) := by
    apply concave_of_deriv2
      (f' := fun P => p*(Real.cos P-Real.sin P)-q*Real.sin (P-d))
      (f'' := fun P => -p*(Real.sin P+Real.cos P)-q*Real.cos (P-d))
    · intro P hP
      have ha := ((phi_hasDerivAt P).sub_const 1).const_mul p
      have hb := ((((hasDerivAt_id P).sub_const d).cos).sub_const 1).const_mul q
      convert (ha.add hb).sub_const (R*(pairNorm p q d-pairNorm p q 0)) using 1 <;> ring
    · intro P hP
      have ha := ((Real.hasDerivAt_cos P).sub (Real.hasDerivAt_sin P)).const_mul p
      have hb := (((hasDerivAt_id P).sub_const d).sin).const_mul q
      convert ha.sub hb using 1 <;> ring
    · intro P hP
      have hP' : P∈Icc 0 frameCap := ⟨hd.1.trans hP.1,hP.2⟩
      have hN' : P-d∈Icc 0 frameCap := ⟨sub_nonneg.mpr hP.1,by linarith [hP.2,hd.1]⟩
      have ha := transport_trig hP'
      have hb := transport_trig hN'
      nlinarith [mul_nonneg hp.le (show 0≤Real.sin P+Real.cos P by linarith [ha.1,ha.2.2.1]),
        mul_nonneg hq.le (show 0≤Real.cos (P-d) by linarith [hb.1])]
  convert hc using 1
  funext P
  simp only [F,hi,if_false,mixedBlock]
  rw [show P-(P-d)=d by ring]

theorem positive_balance {R t k l c eta x e s : ℝ} {td : Bool} (P N : Fin 3 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (hts : t≤s)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t-s+∑i,P i)
    (hsingle : ∀ i,single td i=true → P i=0 ∨ N i=0) :
    -gamma*(s-t)≤∑ i,F (single td i) R (small k l c eta x e s td i)
      (large k l c eta x e s td i) (nu k l c eta x e s td i) (P i) (N i) := by
  let D := data hR hQU h hx he hs
  have hs' := short_small hs
  have hd : s-t∈Icc 0 frameCap := ⟨sub_nonneg.mpr hts,by linarith [hs'.2,h.angle.1]⟩
  apply D.lower_from_endpoints P N hP hN (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    hd (by linarith [h.angle.1]) (by linarith) hsingle
  · intro i hi
    have hh := mixed_positive_line (R := R) h hx he hs hd i hi
    simpa [D,data,max_eq_right hd.1,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hh
  · intro hz i
    have heq : s-t=0 := le_antisymm hz hd.1
    simp [D,data,heq]
  · intro _ i
    simpa only [sub_zero] using positive_lower hR hQU h hx he hs hd i
  · intro i hi
    have hp := (conditions h hx he hs i).1
    have hq := hp.trans_le (min_le_max : small k l c eta x e s td i≤large k l c eta x e s td i)
    have hr := mixed_ratio h hx he hs i hi
    have hm := CorrelatedSameBlock.positive_surplus (R := R) hq.le
      (show (117/200)*large k l c eta x e s td i≤small k l c eta x e s td i by nlinarith)
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
      (show frameCap-(s-t)∈Icc 0 frameCap from ⟨by linarith [hd.2],by linarith [hd.1]⟩)
    have hu := positive_lower hR hQU h hx he hs hd i
    simp only [show frameCap-(frameCap-(s-t))=s-t by ring] at hm
    simpa [D,data,F,hi] using hu.trans hm
  · intro i j _
    have hu := positive_lower hR hQU h hx he hs (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) i
    have hv := negative_linear hR hQL hQU h hx he hs
      (show frameCap-(s-t)∈Icc 0 frameCap from ⟨by linarith [hd.2],by linarith [hd.1]⟩) j
    change -gamma*(s-t)≤_+_
    linarith

theorem ordinary_lower {R t k l c eta x e s : ℝ} {td : Bool} (P N : Fin 3 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑i,P i)≤frameCap-t) (hbalance : (∑i,N i)=t-s+∑i,P i)
    (hsingle : ∀ i,single td i=true → P i=0 ∨ N i=0) :
    lowerEnvelope R k l c t s≤∑ i,F (single td i) R (small k l c eta x e s td i)
      (large k l c eta x e s td i) (nu k l c eta x e s td i) (P i) (N i) := by
  by_cases hst : s≤t
  · simpa [lowerEnvelope,hst] using
      negative_balance P N hR hQL hQU h hx he hs hst hP hN hbudget hbalance hsingle
  · simpa [lowerEnvelope,hst] using
      positive_balance P N hR hQL hQU h hx he hs (lt_of_not_ge hst).le hP hN hbudget hbalance hsingle

end SquaresInCircles.Eight.TableFree.CriticalNegativeTEnvelope
