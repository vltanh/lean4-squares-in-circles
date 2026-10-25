module

public import SquaresInCircles.Eight.Owners.Critical.EExclusion
public import SquaresInCircles.Eight.Owners.Critical.NegativeTOrdinaryData
public import SquaresInCircles.Eight.Owners.Critical.PositiveTEnvelope
public import SquaresInCircles.Eight.Owners.Critical.PositiveTScalar
public import SquaresInCircles.Eight.Owners.Exceptional.NegativeTSortedGain
public import SquaresInCircles.Eight.Owners.Exceptional.ELowEnvelope
public import SquaresInCircles.Eight.Owners.Exceptional.PositiveTSupport
public import SquaresInCircles.Eight.Owners.Sole.AllTExclusion

/-!
# Eight squares: positive T at the EH contact of the stationary radius

On the critical strip the scalar is nonnegative at `z = 0` and strictly increasing on the triangle
of fixed `t`, and the G face is strict whenever its length is positive; concavity in the G/E split
then forces both primary errors to vanish (`CriticalPositiveTExclusion.original_G_T_zero`).
Outside the strip the scalar reserve is strict, so the same conclusion holds on the whole domain
(`ExceptionalPositiveTComplete.original_G_T_zero`). The points, the EH contact and the common
ceiling are those of the cycle.
-/

section
/-!
## Critical negative-T concentration with any EH error

Removing the negative primary of angle `s` leaves the balance `N - P = t - s` of the ordinary
errors. For `s ≤ t` the admissible budget is enlarged to `h - (t - s)`, and the continuous
endpoint principle applies directly: the ordinary blocks are at least the smaller of the pure A
and B charges (`negative_balance`). For `t ≤ s` they are at least `-gamma (s - t)`
(`positive_balance`). The pure minimum keeps both A and B, and the mixed H block stays in the
sum; together these give `ordinary_lower`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CriticalNegativeTEnvelope
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
    have e1 : single false 2=true := rfl
    have e2 : nu k l c eta x e s false 2=l := rfl
    rw [e1,e2]
    simp only [SingleAngleConcavity.pure,↓reduceIte]
    dsimp only [V,Vnu,normGain] at hm ⊢
    linarith
  · have e1 : single true 2=false := rfl
    have hb : bWeight true c s=c := rfl
    rw [e1,hb]
    simp only [SingleAngleConcavity.pure,Bool.false_eq_true,↓reduceIte,le_refl]

theorem pure_near {R t k l c eta x e s v : ℝ} {td : Bool}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (hv : v∈Icc 0 (4/25:ℝ)) (i : Fin 3) :
    min (Vnu R l k l v) (V R l c v)≤pure (single td i) R
      (small k l c eta x e s td i) (large k l c eta x e s td i)
      (nu k l c eta x e s td i) v := by
  have hv' : v∈Icc 0 frameCap := ⟨hv.1,by show v≤7/10; linarith [hv.2]⟩
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hw := wide_data (s := s) td h hx he
    have hh := SoleLowChargeBounds.wide_short (q := large k l c eta x e s td 0) hR hQL hw.1
      min_le_max
      (show large k l c eta x e s td 0∈Icc 1 (28/25:ℝ) from ⟨hw.2.1,by linarith [hw.2.2]⟩)
      (show large k l c eta x e s td 0≤28/25 by linarith [hw.2.2])
      (show v∈SoleECoefficients.domain .low from ⟨hv.1,by linarith [hv.2]⟩)
    have hB := B_short hR hQU h hv'
    have hlow := min_le_right (Vnu R l k l v) (V R l c v)
    have e1 : single td 0=false := rfl
    have e2 : nu k l c eta x e s td 0=large k l c eta x e s td 0 := rfl
    rw [e1,e2]
    simp only [SingleAngleConcavity.pure,Bool.false_eq_true,↓reduceIte]
    have hh' : 117/100*v≤V R (small k l c eta x e s td 0) (large k l c eta x e s td 0) v := hh
    linarith [hv.1]
  · obtain ⟨hp,hq,_,_⟩ := AB_data (x := x) (e := e) h hs
    have e1 : single td 1=true := rfl
    have e2 : nu k l c eta x e s td 1=l := rfl
    rw [hp,hq,e1,e2]
    simp only [SingleAngleConcavity.pure,↓reduceIte]
    exact min_le_left _ _
  · exact (min_le_right _ _).trans (B_charge_lower hR h hs hv')

theorem pure_far {R t k l c eta x e s : ℝ} {td : Bool}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (i : Fin 3) :
    V R l c frameCap≤pure (single td i) R (small k l c eta x e s td i)
      (large k l c eta x e s td i) (nu k l c eta x e s td i) frameCap := by
  have hR2 : R≤2 := by norm_num [qCap] at hQU; nlinarith
  fin_cases i <;> dsimp only [Fin.reduceFinMk]
  · have hw := wide_data (s := s) td h hx he
    have hh := SoleLowChargeBounds.wide_cap (q := large k l c eta x e s td 0) hR hQL hw.1
      min_le_max
      (show large k l c eta x e s td 0∈Icc 1 (28/25:ℝ) from ⟨hw.2.1,by linarith [hw.2.2]⟩)
      (show large k l c eta x e s td 0≤28/25 by linarith [hw.2.2])
    have hB := CriticalEPureCharges.B_cap ⟨hR,hR2⟩ h
    have e1 : single td 0=false := rfl
    have e2 : nu k l c eta x e s td 0=large k l c eta x e s td 0 := rfl
    rw [e1,e2]
    simp only [SingleAngleConcavity.pure,Bool.false_eq_true,↓reduceIte]
    have hh' : 31/40<V R (small k l c eta x e s td 0) (large k l c eta x e s td 0) frameCap := hh
    linarith
  · obtain ⟨hp,hq,_,_⟩ := AB_data (x := x) (e := e) h hs
    have e1 : single td 1=true := rfl
    have e2 : nu k l c eta x e s td 1=l := rfl
    rw [hp,hq,e1,e2]
    simp only [SingleAngleConcavity.pure,↓reduceIte]
    exact CriticalEPureCharges.A_ge_B_at_cap ⟨hR,hR2⟩ h
  · exact B_charge_lower hR h hs (by norm_num [frameCap])

theorem B_gap {R t k l c eta v : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (hQU : R^2≤qCap) (h : Bounds t k l c eta) (hv : v∈Icc 0 (4/25:ℝ)) :
    gamma*(frameCap-v)<V R l c frameCap-V R l c v := by
  have hh := ExceptionalSmallGap.scaled_gap hR hQL hQU
    (show ExceptionalSmallGap.scale≤c by dsimp [ExceptionalSmallGap.scale]; linarith [h.c_lower])
    h.order.2.2.1 h.order.2.2.2.1
    (show v∈Icc 0 (9/50:ℝ) from ⟨hv.1,by linarith [hv.2]⟩)
  have hlen : 0≤frameCap-v := by show 0≤7/10-v; linarith [hv.2]
  dsimp only [ExceptionalSmallGap.scale] at hh
  simp only [gamma]
  generalize frameCap=F at hh hlen ⊢
  linarith

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
  have hd' : t-s∈Icc 0 frameCap := ⟨hd.1,by show t-s≤7/10; linarith [hd.2]⟩
  apply SingleAngleConcentration.lower_from_endpoints (single td) R
    (small k l c eta x e s td) (large k l c eta x e s td) (nu k l c eta x e s td) P N
    hR hQU (fun i => (conditions h hx he hs i).1) (fun _ => min_le_max)
    (fun i => (conditions h hx he hs i).2.2.2.1) (fun i => (conditions h hx he hs i).2.1)
    hP hN hd' (by linarith [hs'.1]) hbalance hsingle
    (fun i => pure_near hR hQL hQU h hx he hs hd i)
  · intro i hi
    have hr := mixed_ratio h hx he hs i hi
    have hq0 : 0<large k l c eta x e s td i := lt_of_lt_of_le (conditions h hx he hs i).1 min_le_max
    have hc : PositiveStressCoefficients.ratio (t-s)*large k l c eta x e s td i≤ small k l c eta x e s td i := by
      have hm := mul_le_mul_of_nonneg_right hd.2 hq0.le
      dsimp only [PositiveStressCoefficients.ratio]
      linarith
    have hm := CorrelatedSameBlock.negative_surplus (R := R) hq0.le hc hd'
      (show (0:ℝ)∈Icc 0 (t-s) from ⟨le_rfl,hd.1⟩)
    have hpu := pure_near hR hQL hQU h hx he hs hd i
    simp only [SingleAngleConcavity.pure,hi,Bool.false_eq_true,↓reduceIte] at hpu
    have hid : mixedBlock R (small k l c eta x e s td i) (large k l c eta x e s td i) (frameCap-(t-s)) frameCap=
        M R (small k l c eta x e s td i) (large k l c eta x e s td i) (t-s) := by
      simpa only [show t-s+(frameCap-(t-s))=frameCap by ring] using
        mixedBlock_saturated R (small k l c eta x e s td i) (large k l c eta x e s td i) (t-s)
    rw [sub_zero,sub_zero,hid] at hm
    exact hpu.trans hm
  · intro i j _
    have hu := positive_lower hR hQU h hx he hs
      (show frameCap-(t-s)∈Icc 0 frameCap from ⟨by linarith [hd'.2],by linarith [hd'.1]⟩) i
    have hv := pure_far hR hQL hQU h hx he hs j
    have hg := B_gap hR hQL hQU h hd
    have hl := min_le_right (Vnu R l k l (t-s)) (V R l c (t-s))
    generalize frameCap=F at hu hv hg ⊢
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
      (fun P => p*(PositiveAngularEnvelope.phi P-1)+q*(Real.cos (P-d)-1)-R*(pairNorm p q d-pairNorm p q 0)) := by
    apply concave_of_deriv2
      (f' := fun P => p*(Real.cos P-Real.sin P)-q*Real.sin (P-d))
      (f'' := fun P => -p*(Real.sin P+Real.cos P)-q*Real.cos (P-d))
    · intro P _
      have ha : HasDerivAt (fun y => p*(PositiveAngularEnvelope.phi y-1)) (p*(Real.cos P-Real.sin P)) P :=
        ((CorrelatedSameBlock.phi_hasDerivAt P).sub_const 1).const_mul p
      have hb : HasDerivAt (fun y => q*(Real.cos (y-d)-1)) (q*(-Real.sin (P-d)*1)) P :=
        ((((hasDerivAt_id' P).sub_const d).cos).sub_const 1).const_mul q
      have hab : HasDerivAt (fun y => p*(PositiveAngularEnvelope.phi y-1)+q*(Real.cos (y-d)-1)-
          R*(pairNorm p q d-pairNorm p q 0))
          (p*(Real.cos P-Real.sin P)+q*(-Real.sin (P-d)*1)) P :=
        (ha.fun_add hb).sub_const _
      exact hab.congr_deriv (by ring)
    · intro P _
      have ha : HasDerivAt (fun y => p*(Real.cos y-Real.sin y)) (p*(-Real.sin P-Real.cos P)) P :=
        ((Real.hasDerivAt_cos P).fun_sub (Real.hasDerivAt_sin P)).const_mul p
      have hb : HasDerivAt (fun y => q*Real.sin (y-d)) (q*(Real.cos (P-d)*1)) P :=
        (((hasDerivAt_id' P).sub_const d).sin).const_mul q
      exact (ha.fun_sub hb).congr_deriv (by ring)
    · intro P hP
      have hP' : P∈Icc 0 frameCap := ⟨hd.1.trans hP.1,hP.2⟩
      have hN' : P-d∈Icc 0 frameCap := ⟨sub_nonneg.mpr hP.1,by linarith [hP.2,hd.1]⟩
      have ha := transport_trig hP'
      have hb := transport_trig hN'
      have h1 := mul_nonneg hp.le (show 0≤Real.sin P+Real.cos P by linarith [ha.1,ha.2.2.1])
      have h2 := mul_nonneg hq.le (show 0≤Real.cos (P-d) by linarith [hb.1])
      linarith
  refine hc.congr (fun P _ => ?_)
  simp only [F,hi,Bool.false_eq_true,↓reduceIte,mixedBlock,show P-(P-d)=d by ring]
  rfl

theorem positive_balance {R t k l c eta x e s : ℝ} {td : Bool} (P N : Fin 3 → ℝ)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap) (h : Bounds t k l c eta)
    (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td) (hts : t≤ s)
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
    rw [sub_zero,sub_zero,max_eq_right hd.1]
    refine hh.congr (fun P _ => ?_)
    show F (single td i) R (small k l c eta x e s td i) (large k l c eta x e s td i) (nu k l c eta x e s td i) P (P-(s-t))=
      F (single td i) R (small k l c eta x e s td i) (large k l c eta x e s td i) (nu k l c eta x e s td i) P (0-(s-t)+P)
    congr 1
    ring
  · intro hz i
    have heq : s-t=0 := le_antisymm hz hd.1
    show -gamma*(s-t)≤SingleAngleConcavity.pure (single td i) R (small k l c eta x e s td i) (large k l c eta x e s td i) (nu k l c eta x e s td i) (0-(s-t))
    rw [heq,sub_zero,pure_zero,mul_zero]
  · intro _ i
    show -gamma*(s-t)≤U R (small k l c eta x e s td i) (large k l c eta x e s td i) (s-t-0)
    rw [sub_zero]
    exact positive_lower hR hQU h hx he hs hd i
  · intro i hi
    have hp := (conditions h hx he hs i).1
    have hq : 0<large k l c eta x e s td i := lt_of_lt_of_le hp min_le_max
    have hr := mixed_ratio h hx he hs i hi
    have hm := CorrelatedSameBlock.positive_surplus (R := R) hq.le
      (show (117/200)*large k l c eta x e s td i≤ small k l c eta x e s td i by linarith)
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
      (show frameCap-(s-t)∈Icc 0 frameCap from ⟨by linarith [hd.2],by linarith [hd.1]⟩)
    have hu := positive_lower hR hQU h hx he hs hd i
    rw [show frameCap-(frameCap-(s-t))=s-t by ring] at hm
    show -gamma*(s-t)≤F (single td i) R (small k l c eta x e s td i) (large k l c eta x e s td i) (nu k l c eta x e s td i) (frameCap-0) (frameCap-(s-t))
    have hi' : single td i=false := hi
    rw [hi',sub_zero]
    simp only [F,Bool.false_eq_true,↓reduceIte]
    exact hu.trans hm
  · intro i j _
    have hu := positive_lower hR hQU h hx he hs
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) i
    have hv := negative_linear hR hQL hQU h hx he hs
      (show frameCap-(s-t)∈Icc 0 frameCap from ⟨by linarith [hd.2],by linarith [hd.1]⟩) j
    show -gamma*(s-t)≤U R (small k l c eta x e s td i) (large k l c eta x e s td i) (frameCap-0)+
      SingleAngleConcavity.pure (single td j) R (small k l c eta x e s td j)
        (large k l c eta x e s td j) (nu k l c eta x e s td j) (frameCap-(s-t))
    rw [sub_zero]
    generalize frameCap=F at hu hv ⊢
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

end SquaresInCircles.Eight.CriticalNegativeTEnvelope
end
end
end

section
/-!
## Original signed blocks for exceptional negative T

The three ordinary blocks are extracted directly
from the original seven errors. Both AB weak-owner choices are kept.
The aligned TD0 hypothesis is used only in the BT3 row, where it is the
actual alignment supplied by entry; it removes the otherwise present
D argument and does not alter any source point or frame.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CriticalNegativeTBlocks
open Candidate ActualOrdinaryBlocks ActualCoreEBlocks PositiveAngularEnvelope
open ExceptionalContactStress ExceptionalNegativeTStress
open CriticalECoefficients CriticalNegativeTOrdinaryData
open SingleAngleConcavity CriticalNegativeTContinuation

def blocks (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ) : Fin 3 → Block :=
  ![⟨k*tilt eta x,tilt eta e,delta C.theta H,delta C.theta E⟩,
    ⟨l,k,if ab=0 then 0 else delta C.theta A,0⟩,
    ⟨l,bWeight td c s,if ab=0 then delta C.theta A else 0,if td then delta C.theta B else 0⟩]

theorem sum_parts (C : SignedCycle) {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (td : Bool) (k l c eta s x e : ℝ) (F : ℝ → ℝ) (hF : F 0=0)
    (halign : td=false → delta C.theta T=0) :
    (∑ i,(F (blocks C ab td k l c eta s x e i).u+F (blocks C ab td k l c eta s x e i).v))=
      (∑ j,F (delta C.theta j))-F (delta C.theta G)-F (delta C.theta D)-F (primary C td) := by
  have hT := halign
  simp only [T] at hT
  rcases hab with rfl | rfl <;> cases td <;>
    simp [blocks,primary,Fin.sum_univ_succ,H,G,A,B,T,D,E,hF,hT] <;> ring

theorem original_budgets {C : SignedCycle} {ab : Fin 4} (hab : ab=0 ∨ ab=2)
    (td : Bool) (k l c eta x e : ℝ) {t s : ℝ}
    (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hs : 0≤ s)
    (hsource : primary C td= -s) (htotal : delta C.theta G+delta C.theta D=t)
    (halign : td=false → delta C.theta T=0) :
    (∑i,(blocks C ab td k l c eta s x e i).P)≤frameCap-t ∧
      (∑i,(blocks C ab td k l c eta s x e i).N)=t-s+∑i,(blocks C ab td k l c eta s x e i).P := by
  have hp := sum_parts C hab td k l c eta s x e positivePart positivePart_zero halign
  have hn := sum_parts C hab td k l c eta s x e negativePart negativePart_zero halign
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hG
  have hPD : positivePart (delta C.theta D)=delta C.theta D := max_eq_left hD
  have hPT : positivePart (primary C td)=0 := by rw [hsource]; exact max_eq_right (by linarith)
  have hNG : negativePart (delta C.theta G)=0 := max_eq_right (by linarith)
  have hND : negativePart (delta C.theta D)=0 := max_eq_right (by linarith)
  have hNT : negativePart (primary C td)=s := by simp [hsource,negativePart,max_eq_left hs]
  change (∑i,(blocks C ab td k l c eta s x e i).P)=
    positiveVariation C.theta-positivePart (delta C.theta G)-positivePart (delta C.theta D)-
      positivePart (primary C td) at hp
  change (∑i,(blocks C ab td k l c eta s x e i).N)=
    negativeVariation C.theta-negativePart (delta C.theta G)-negativePart (delta C.theta D)-
      negativePart (primary C td) at hn
  rw [hPG,hPD,hPT] at hp
  rw [hNG,hND,hNT] at hn
  have hv := variations_equal C.theta
  constructor <;> linarith

theorem coefficients (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (i : Fin 3) :
    (blocks C ab td k l c eta s x e i).p=small k l c eta x e s td i ∧
      (blocks C ab td k l c eta s x e i).q=large k l c eta x e s td i := by
  fin_cases i <;> simp [blocks,Block.p,Block.q,small,large,CriticalNegativeTOrdinaryData.alpha,CriticalNegativeTOrdinaryData.beta,min_comm,max_comm]

theorem single_data (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (i : Fin 3) (hi : single td i=true) :
    (blocks C ab td k l c eta s x e i).v=0 ∧
      (blocks C ab td k l c eta s x e i).alpha=nu k l c eta x e s td i := by
  fin_cases i <;> cases td <;> simp_all [single,blocks,nu]

theorem single_parts (C : SignedCycle) (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (i : Fin 3) (hi : single td i=true) :
    (blocks C ab td k l c eta s x e i).P=0 ∨ (blocks C ab td k l c eta s x e i).N=0 := by
  have hv := (single_data C ab td k l c eta s x e i hi).1
  by_cases hu : 0≤(blocks C ab td k l c eta s x e i).u
  · right
    simp [Block.N,hv,negativePart,max_eq_right
      (show -(blocks C ab td k l c eta s x e i).u≤0 by linarith)]
  · left
    simp [Block.P,hv,positivePart,max_eq_right (le_of_lt (lt_of_not_ge hu))]

theorem angles_small {C : SignedCycle} (ab : Fin 4) (td : Bool) (k l c eta s x e : ℝ)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (i : Fin 3) :
    |(blocks C ab td k l c eta s x e i).u|≤frameCap ∧
      |(blocks C ab td k l c eta s x e i).v|≤frameCap := by
  have hz : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have hA : |if ab=0 then 0 else delta C.theta A|≤frameCap := by
    split_ifs <;> first | exact hz | exact ha A
  have hB : |if ab=0 then delta C.theta A else 0|≤frameCap := by
    split_ifs <;> first | exact hz | exact ha A
  fin_cases i <;> cases td <;> simp [blocks,ha H,ha E,ha B,hA,hB]
  all_goals norm_num [frameCap]

theorem increment_eq {C : SignedCycle} {ab : Fin 4} (td : Bool) (R k l c eta s x e : ℝ)
    (hab : ab=0 ∨ ab=2) (halign : td=false → delta C.theta T=0) :
    ExceptionalNegativeTStress.increment C ab td R k l c eta s x e=
      ∑ i,(blocks C ab td k l c eta s x e i).increment R := by
  rcases hab with rfl | rfl <;> cases td <;>
    simp [ExceptionalNegativeTStress.increment,blocks,Block.increment,
      SoleEStress.increment,SoleEStress.anchorNorms,SoleEStress.zeroNorms,
      btOwner,tdOwner,bWeight,tWeight,ordinaryDE,ordinaryEH,halign,
      Fin.sum_univ_succ,pairNorm_symm k l,pairNorm_symm (k*tilt eta x) (tilt eta e)] <;> ring

theorem individual_budgets {C : SignedCycle} {ab : Fin 4} {td : Bool} {k l c eta t s x e : ℝ}
    (ht : 0≤t) (hs : 0≤ s)
    (hP : (∑i,(blocks C ab td k l c eta s x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab td k l c eta s x e i).N)=t-s+∑i,(blocks C ab td k l c eta s x e i).P)
    (i : Fin 3) :
    (blocks C ab td k l c eta s x e i).P≤frameCap ∧
      (blocks C ab td k l c eta s x e i).N≤frameCap := by
  have hp := Finset.single_le_sum (fun j _ => (blocks C ab td k l c eta s x e j).P_nonneg)
    (Finset.mem_univ i)
  have hn := Finset.single_le_sum (fun j _ => (blocks C ab td k l c eta s x e j).N_nonneg)
    (Finset.mem_univ i)
  constructor <;> linarith

theorem block_minorant {C : SignedCycle} {ab : Fin 4} {td : Bool} {R k l c eta t s x e : ℝ}
    (ht : 0≤t) (hs : 0≤ s) (hp : ∀ i,0≤ small k l c eta x e s td i)
    (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hP : (∑i,(blocks C ab td k l c eta s x e i).P)≤frameCap-t)
    (hN : (∑i,(blocks C ab td k l c eta s x e i).N)=t-s+∑i,(blocks C ab td k l c eta s x e i).P)
    (i : Fin 3) :
    F (single td i) R (small k l c eta x e s td i) (large k l c eta x e s td i)
      (nu k l c eta x e s td i) (blocks C ab td k l c eta s x e i).P
        (blocks C ab td k l c eta s x e i).N≤(blocks C ab td k l c eta s x e i).increment R := by
  obtain ⟨hsmall,hlarge⟩ := coefficients C ab td k l c eta s x e i
  obtain ⟨hbP,hbN⟩ := individual_budgets ht hs hP hN i
  by_cases hi : single td i=true
  · obtain ⟨hv,hn⟩ := single_data C ab td k l c eta s x e i hi
    have hh := SoleOriginalBlocks.one_angle_minorant (blocks C ab td k l c eta s x e i) R hv
      (angles_small ab td k l c eta s x e ha i).1
    simpa only [hi,hsmall,hlarge,hn] using hh
  · have hi' : single td i=false := Bool.eq_false_of_not_eq_true hi
    have hh := (blocks C ab td k l c eta s x e i).minorant R
      (by rw [hsmall]; exact hp i) hbP hbN
    simpa only [F,hi',Bool.false_eq_true,↓reduceIte,hsmall,hlarge] using hh

theorem original_lower {C : SignedCycle} {ab : Fin 4} {td : Bool} {R t k l c eta x e s : ℝ}
    (hab : ab=0 ∨ ab=2) (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t k l c eta) (hx : x∈Icc 0 t) (he : e∈Icc 0 t) (hs : s∈shortDomain td)
    (ha : ∀ i,|delta C.theta i|≤frameCap) (hvar : positiveVariation C.theta≤frameCap)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (hsource : primary C td= -s) (htotal : delta C.theta G+delta C.theta D=t)
    (halign : td=false → delta C.theta T=0) :
    lowerEnvelope R k l c t s≤ExceptionalNegativeTStress.increment C ab td R k l c eta s x e := by
  have hs0 := (short_small hs).1
  obtain ⟨hP,hN⟩ := original_budgets hab td k l c eta x e hvar hG hD hs0 hsource htotal halign
  have hlow := CriticalNegativeTEnvelope.ordinary_lower
    (fun i => (blocks C ab td k l c eta s x e i).P)
    (fun i => (blocks C ab td k l c eta s x e i).N) hR hQL hQU h hx he hs
    (fun i => (blocks C ab td k l c eta s x e i).P_nonneg)
    (fun i => (blocks C ab td k l c eta s x e i).N_nonneg) hP hN
    (single_parts C ab td k l c eta s x e)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    block_minorant (R := R) h.angle.1 hs0 (fun i => (conditions h hx he hs i).1.le) ha hP hN i)
  rw [increment_eq td R k l c eta s x e hab halign]
  exact hlow.trans hsum

end SquaresInCircles.Eight.CriticalNegativeTBlocks
end
end
end

section
/-!
## Negative T on the critical strip

On a necessary cycle at a radius `q ≤ d.q` below a stationary configuration, with total G–D error
in the critical strip, a negative T primary forces the G error to vanish (`negative_TD_G_zero`,
`negative_BT_G_zero`). The entry is local and at the radius `q` itself: an available secondary
owner is selected again at the same points and frames; otherwise T is on the flat core, and its
work gives a strict endpoint gain at the sharp support radius (`flat_false`). This covers both
weak owners of AB, either sign of G, any EH error and every signed ordinary allocation.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalNegativeTExclusion
open Candidate CriticalEExclusion CriticalECoefficients ExceptionalContactStress
open CriticalNegativeTOrdinaryData CriticalNegativeTContinuation ExceptionalNegativeTStress
open NegativeSecondaryEExclusion PositiveAngularEnvelope

theorem flat_false {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4} (td : Bool) {t s : ℝ}
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (htotal : delta C.theta G+delta C.theta D=t)
    (hs : s∈shortDomain td) (hs0 : 0<s) (hsource : primary C td= -s)
    (hflat : (C.point T).a=7/12) (halign : td=false → delta C.theta T=0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) : False := by
  have h := coefficient_bounds hsharp ht
  have hr := radius_bounds hsharp
  have hq0 : 0≤d.q := by norm_num [qLow] at hsharp; linarith [hsharp.1]
  have hsq := Real.sq_sqrt hq0
  have hcap : d.q≤qCap := hsharp.2.trans uniform_radius_order.2.2.1.le
  have hc : ∀ i,(C.point i).Contained ((Real.sqrt d.q)^2) := by
    intro i
    rw [hsq]
    exact (hC.contained i).trans hq
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => ((hC.contained i).trans hq).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hx : delta C.theta G∈Icc 0 t := ⟨hG,by linarith⟩
  have hz : (0:ℝ)∈Icc 0 t := ⟨le_rfl,h.angle.1⟩
  have ht' : t∈Icc 0 t := ⟨h.angle.1,le_rfl⟩
  have hgain : OrdinaryAngleConcavity.V (Real.sqrt d.q) (L d.q t) (Cc d.q t) t<
      gain td (Real.sqrt d.q) (L d.q t) (Cc d.q t) s+
        lowerEnvelope (Real.sqrt d.q) (K d.q t) (L d.q t) (Cc d.q t) t s := by
    cases td
    · simpa [gain,CriticalNegativeTPolynomials.shortAngle] using
        BT_gain hsharp ht (show s∈Ioc 0 CriticalNegativeTPolynomials.shortAngle from
          ⟨hs0,by simpa [shortDomain,CriticalNegativeTPolynomials.shortAngle] using hs.2⟩)
    · simpa [gain] using TD_gain hsharp ht
        (show s∈Ioc 0 (3/10:ℝ) from ⟨hs0,by simpa [shortDomain] using hs.2⟩)
  have hinc0 := CriticalNegativeTBlocks.original_lower hab hr.1 hr.2.1 hr.2.2.1 h hz ht'
    hs ha hvar hG hD hsource htotal halign
  have hinc1 := CriticalNegativeTBlocks.original_lower hab hr.1 hr.2.1 hr.2.2.1 h ht' hz
    hs ha hvar hG hD hsource htotal halign
  have hv0 := ExceptionalNegativeTStress.value_lower (k:=K d.q t) (l:=L d.q t) (c:=Cc d.q t) td hab hr.1
    (show 0≤Eta d.q t by linarith [h.eta_lower]) h.angle hz (short_small hs)
    hC.sorted hc hn ha hcontact hsource hflat halign
  have hv1 := ExceptionalNegativeTStress.value_lower (k:=K d.q t) (l:=L d.q t) (c:=Cc d.q t) td hab hr.1
    (show 0≤Eta d.q t by linarith [h.eta_lower]) h.angle ht' (short_small hs)
    hC.sorted hc hn ha hcontact hsource hflat halign
  rw [sub_zero,ExceptionalContactSupport.baseline_at_E h.angle] at hv0
  rw [sub_self,ExceptionalContactSupport.baseline_at_G h.angle] at hv1
  obtain ⟨hE,hGG⟩ := scalar_endpoints hd hsharp ht
  have h0 : 0<ExceptionalNegativeTStress.value C ab td (Real.sqrt d.q)
      (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t s 0 := by linarith
  have h1 : 0<ExceptionalNegativeTStress.value C ab td (Real.sqrt d.q)
      (K d.q t) (L d.q t) (Cc d.q t) (Eta d.q t) t s t := by linarith
  have hconc := ExceptionalNegativeTStress.concave (l:=L d.q t) (c:=Cc d.q t) (s:=s) ab td hr.1 hr.2.2.1
    (show K d.q t∈Icc (431/500:ℝ) 1 by constructor <;> linarith [h.k_lower,h.k_upper])
    (show Eta d.q t∈Icc (1/4:ℝ) (327/1000) by constructor <;> linarith [h.eta_lower,h.eta_upper])
    h.angle hC.sorted hcCap ha hEy
  have hpos := (lt_min h0 h1).trans_le (hconc.min_le_of_mem_Icc hz ht' hx)
  have hnec := ExceptionalNegativeTStress.necessary (k:=K d.q t) (l:=L d.q t) (c:=Cc d.q t) (eta:=Eta d.q t) (s:=s) td hab hr.1
    h.order.1.le h.ell_pos.le (by linarith [h.c_lower]) (by linarith [h.eta_lower])
    h.angle (short_small hs) hG hD htotal hC.sorted hc hn hcontact hf
  exact (not_lt_of_ge hnec) hpos

theorem negative_TD_G_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : delta C.theta G+delta C.theta D∈Icc (1/10:ℝ) (4/25))
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 3 0 i)) : delta C.theta G=0 := by
  let s := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hsource : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hsource]
    exact (TD_contact C 2).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hcap : q≤qCap := hq.trans (hsharp.2.trans uniform_radius_order.2.2.1.le)
  obtain hsecondary | ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_TD_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core T) (hC.core D) hcap hn.D_nonpos hs hBT hTD
  · have hsame : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hsource] using hsecondary)
    exact CriticalEExclusion.original_G_zero hd hsharp hq hC hn hvar hab hG hD ht hEy hcontact
      (SoleNegativeTExclusion.reselect_TD hf hsame)
  · exact (flat_false hd hsharp true hq hC hn hvar hab hG hD ht rfl
      (show s∈shortDomain true from ⟨hs.1.le,hshort.le⟩) hs.1 hsource hflat
      (by intro h; cases h) hEy hcontact hf).elim

theorem negative_BT_G_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4}
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D)
    (ht : delta C.theta G+delta C.theta D∈Icc (1/10:ℝ) (4/25))
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 3 0 i)) : delta C.theta G=0 := by
  by_cases hsecondary : C.Feasible B 2
  · exact CriticalEExclusion.original_G_zero hd hsharp hq hC hn hvar hab hG hD ht hEy hcontact
      (SoleNegativeTExclusion.reselect_BT hf hsecondary)
  let s := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hsource : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hsource]
    exact (BT_contact C 3).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hsource] using hh))
  have hcap : q≤qCap := hq.trans (hsharp.2.trans uniform_radius_order.2.2.1.le)
  obtain ⟨hcore,hflat,hy,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hcap hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact (flat_false hd hsharp false hq hC hn hvar hab hG hD ht rfl
    (show s∈shortDomain false from ⟨hs.1.le,hshort.le⟩) hs.1 hsource hflat
    (fun _ => halign) hEy hcontact hf).elim

end SquaresInCircles.Eight.CriticalNegativeTExclusion
end
end
end

section
/-!
## Strict growth from the original hard-chain zero

The supporting chain is the exact minimizing
position at q,t. At z=0 the scalar is the previously proved sharp
endpoint; on the entire triangle its derivative exceeds 9/5000.
Neither the exact zero nor the original stationary radius is perturbed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTDerivative
open Stationary.FiveCornerGeometry ExceptionalContactStress ExceptionalContactSupport
open CriticalPositiveTCoefficients

def k (q t z : ℝ) : ℝ := adaptedK (CriticalEExclusion.K q t) z
def ell (q t z : ℝ) : ℝ := adaptedL (CriticalEExclusion.L q t) z
def c (q t z : ℝ) : ℝ := adaptedC (CriticalEExclusion.Cc q t) z
def eta (q t : ℝ) : ℝ := CriticalEExclusion.Eta q t
def p (q t z : ℝ) : ℝ := tilt (eta q t) (t-z)
def m (q t z : ℝ) : ℝ := c q t z*tilt (eta q t) z

def scalar (q t z : ℝ) : ℝ :=
  CriticalPositiveTScalar.scalar (Real.sqrt q) (CriticalEExclusion.K q t)
    (CriticalEExclusion.L q t) (CriticalEExclusion.Cc q t) (eta q t) t z
def slope (q t z : ℝ) : ℝ :=
  CriticalPositiveTScalar.slope (Real.sqrt q) (CriticalEExclusion.K q t)
    (CriticalEExclusion.L q t) (CriticalEExclusion.Cc q t) (eta q t) t z

theorem scalar_formula (q t z : ℝ) :
    scalar q t z=3*k q t z+2*ell q t z+c q t z*contactScalar (Real.sqrt q) (eta q t) z+
      contactScalar (Real.sqrt q) (eta q t) (t-z)+m q t z*(Real.cos t-1)-
      Real.sqrt q*(Real.sqrt (p q t z^2+k q t z^2)+Real.sqrt (k q t z^2+ell q t z^2)+
        Real.sqrt (ell q t z^2+m q t z^2-2*ell q t z*m q t z*Real.sin t)+
        Real.sqrt (1+c q t z^2)) := rfl

theorem coefficients {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) :
    Bounds t z (k q t z) (ell q t z) (c q t z) (m q t z) (eta q t) :=
  adapted_bounds (CriticalEExclusion.coefficient_bounds hq ht) hz

theorem hasDerivAt_scalar {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) :
    HasDerivAt (scalar q t) (slope q t z) z :=
  CriticalPositiveTScalar.hasDerivAt_scalar (CriticalEExclusion.coefficient_bounds hq ht) hz

theorem slope_lower {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) : 9/5000<slope q t z := by
  have h := CriticalPositiveTModel.minimizing_derivative_lower hq ht hz
  rw [CriticalPositiveTScalar.model_value] at h
  exact h

theorem deriv_lower {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) :
    9/5000<deriv (scalar q t) z := by
  rw [(hasDerivAt_scalar hq ht hz).deriv]
  exact slope_lower hq ht hz

/-- Exact cancellation of the unshifted B norm at the hard endpoint. -/
theorem scalar_zero (q t : ℝ) :
    scalar q t 0=atE (Real.sqrt q) (CriticalEExclusion.K q t) (CriticalEExclusion.L q t)
      (CriticalEExclusion.Cc q t) (eta q t) t+
      OrdinaryAngleConcavity.V (Real.sqrt q) (CriticalEExclusion.L q t) (CriticalEExclusion.Cc q t) t := by
  simp only [scalar,CriticalPositiveTScalar.scalar,CriticalPositiveTScalar.p,
    CriticalPositiveTScalar.hSquare,CriticalPositiveTScalar.aSquare,CriticalPositiveTScalar.bSquare,
    CriticalPositiveTScalar.dSquare,adaptedK,adaptedL,adaptedC,adaptedM,tilt,
    atE,contactScalar,OrdinaryAngleConcavity.V,PositiveAngularEnvelope.pairNorm,
    Real.sin_zero,Real.cos_zero,Real.sin_neg,mul_zero,sub_zero,add_zero,mul_one,one_pow]
  ring

theorem scalar_zero_nonneg {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    0≤ scalar d.q t 0 := by
  rw [scalar_zero]
  exact (CriticalEExclusion.scalar_endpoints hd hq ht).1

/-- The strict derivative inequality is used on the full interval.
The endpoint itself is still the exact supporting-chain scalar. -/
theorem scalar_growth {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Ioc 0 t) :
    scalar q t 0+(9/5000)*z<scalar q t z := by
  have hc : ContinuousOn (scalar q t) (Icc 0 t) := by
    intro s hs
    exact (hasDerivAt_scalar hq ht hs).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (scalar q t) (interior (Icc 0 t)) := by
    intro s hs
    exact (hasDerivAt_scalar hq ht (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hl : ∀s∈interior (Icc 0 t),(9/5000:ℝ)<deriv (scalar q t) s := by
    intro s hs
    exact deriv_lower hq ht (interior_subset hs)
  have h := (convex_Icc (0:ℝ) t).mul_sub_lt_image_sub_of_lt_deriv hc hd hl
    0 (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,by linarith [ht.1]⟩)
    z (Ioc_subset_Icc_self hz) hz.1
  linarith

theorem scalar_pos_of_z_pos {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {t z : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Ioc 0 t) :
    (9/5000)*z<scalar d.q t z := by
  have h0 := scalar_zero_nonneg hd hq ht
  have h := scalar_growth hq ht hz
  linarith

theorem scalar_nonneg {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hq : d.q∈Icc qLow qTrial) {t z : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t) : 0≤ scalar d.q t z := by
  rcases eq_or_lt_of_le hz.1 with hzero | hpos
  · subst z
    exact scalar_zero_nonneg hd hq ht
  · have h := scalar_pos_of_z_pos hd hq ht ⟨hpos,hz.2⟩
    nlinarith

end SquaresInCircles.Eight.CriticalPositiveTDerivative
end
end
end

section
/-!
## The two original fixed-z faces of the critical contact stress

The BT baseline is at least
the TD baseline by the exact comparison of norm increments. The G
face is at least the E face, strictly so when its G error is positive.
The remaining E/TD expression is exactly the derivative scalar.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTEndpoints
open Candidate CriticalPositiveTCoefficients ExceptionalContactStress
open ExceptionalContactSupport PositiveAngularEnvelope OrdinaryAngleConcavity

theorem contact_coefficient_negative {R eta : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (heta : eta≤31/100) : 1+2*eta-R*Real.sqrt (1+eta^2)<0 := by
  have hs : (1:ℝ)≤Real.sqrt (1+eta^2) := by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤1+eta^2 by nlinarith [sq_nonneg eta])
  have hm := mul_le_mul_of_nonneg_left hs hR
  have hr := SoleAngleGrowth.radius_lower hR hQL
  linarith

theorem contact_le_three {R eta a : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (heta : eta≤31/100) (ha : a∈Icc 0 (4/25:ℝ)) : contactScalar R eta a≤3 := by
  have hn := contact_coefficient_negative hR hQL heta
  have hs := (transport_trig (show a∈Icc 0 frameCap from
    ⟨ha.1,by dsimp [frameCap]; linarith [ha.2]⟩)).2.2.1
  have hp := mul_nonpos_of_nonpos_of_nonneg hn.le hs
  dsimp [contactScalar]
  linarith [Real.cos_le_one a]

theorem contact_lt_three {R eta a : ℝ} (hR : 0≤R) (hQL : qLow≤R^2)
    (heta : eta≤31/100) (ha : a∈Ioc 0 (4/25:ℝ)) : contactScalar R eta a<3 := by
  have hn := contact_coefficient_negative hR hQL heta
  have hs0 := Real.sin_ge_sub_cube ha.1.le
  have ha2 : a^2≤(4/25:ℝ)^2 := pow_le_pow_left₀ ha.1.le ha.2 2
  have ha3 := mul_le_mul_of_nonneg_right ha2 ha.1.le
  have hs : 0<Real.sin a := by nlinarith [ha.1]
  have hp := mul_neg_of_neg_of_pos hn hs
  dsimp [contactScalar]
  linarith [Real.cos_le_one a]

theorem td_le_bt {R t z k l c m eta x e : ℝ} (hR : 0≤R)
    (h : Bounds t z k l c m eta) (hm : m=c*tilt eta z) :
    ExceptionalPositiveTStress.baseline true R k l c eta z x e≤
      ExceptionalPositiveTStress.baseline false R k l c eta z x e := by
  have hn := PositiveSplitComparison.norm_increment_comparison h.ell_pos.le
    (show l≤1 by linarith [h.ell_upper]) (show 0<c by linarith [h.c_lower]) h.c_le_m
  have hh := mul_le_mul_of_nonneg_left hn hR
  simp only [ExceptionalPositiveTStress.baseline,ExceptionalPositiveTStress.bWeight,
    ExceptionalPositiveTStress.tWeight,ite_true,Bool.false_eq_true,ite_false,
    SoleEStress.zeroNorms,pairNorm_zero,one_pow,← hm]
  linarith

theorem td_le_row {R t z k l c m eta x e : ℝ} (td : Bool) (hR : 0≤R)
    (h : Bounds t z k l c m eta) (hm : m=c*tilt eta z) :
    ExceptionalPositiveTStress.baseline true R k l c eta z x e≤
      ExceptionalPositiveTStress.baseline td R k l c eta z x e := by
  cases td
  · exact td_le_bt hR h hm
  · exact le_rfl

theorem split_difference (td : Bool) (R k l c eta z a : ℝ) :
    ExceptionalPositiveTStress.baseline td R k l c eta z a 0-
      ExceptionalPositiveTStress.baseline td R k l c eta z 0 a=
      (1-k)*(3-contactScalar R eta a)+
        R*(pairNorm (tilt eta a) k 0-pairNorm 1 (k*tilt eta a) 0) := by
  simp [ExceptionalPositiveTStress.baseline,SoleEStress.zeroNorms,ExceptionalContactStress.tilt,
    contactScalar]
  ring_nf

theorem E_le_G {R t z k l c m eta : ℝ} (td : Bool)
    (hR : 0≤R) (hQL : qLow≤R^2) (h : Bounds t z k l c m eta) :
    ExceptionalPositiveTStress.baseline td R k l c eta z 0 (t-z)≤
      ExceptionalPositiveTStress.baseline td R k l c eta z (t-z) 0 := by
  have ha : t-z∈Icc 0 t := ⟨by linarith [h.z_le],by linarith [h.z_nonneg]⟩
  have hn := endpoint_norm_order
    (show k∈Icc 0 1 from ⟨by linarith [h.k_lower],by linarith [h.k_upper]⟩)
    (h.tilt ha).1
  have hC := contact_le_three hR hQL h.eta_upper.le ⟨ha.1,ha.2.trans h.angle_upper⟩
  have hfirst := mul_nonneg (show 0≤1-k by linarith [h.k_upper]) (sub_nonneg.mpr hC)
  have hsecond := mul_nonneg hR (sub_nonneg.mpr hn)
  have hid := split_difference td R k l c eta z (t-z)
  linarith

theorem E_lt_G {R t z k l c m eta : ℝ} (td : Bool)
    (hR : 0≤R) (hQL : qLow≤R^2) (h : Bounds t z k l c m eta) (ha : 0<t-z) :
    ExceptionalPositiveTStress.baseline td R k l c eta z 0 (t-z)<
      ExceptionalPositiveTStress.baseline td R k l c eta z (t-z) 0 := by
  have ha' : t-z∈Icc 0 t := ⟨ha.le,by linarith [h.z_nonneg]⟩
  have hn := endpoint_norm_order
    (show k∈Icc 0 1 from ⟨by linarith [h.k_lower],by linarith [h.k_upper]⟩)
    (h.tilt ha').1
  have hC := contact_lt_three hR hQL h.eta_upper.le ⟨ha,ha'.2.trans h.angle_upper⟩
  have hfirst := mul_pos (show 0<1-k by linarith [h.k_upper]) (sub_pos.mpr hC)
  have hsecond := mul_nonneg hR (sub_nonneg.mpr hn)
  have hid := split_difference td R k l c eta z (t-z)
  linarith

theorem scalar_eq (q t z : ℝ) :
    CriticalPositiveTDerivative.scalar q t z=
      ExceptionalPositiveTStress.baseline true (Real.sqrt q)
        (CriticalPositiveTDerivative.k q t z) (CriticalPositiveTDerivative.ell q t z)
        (CriticalPositiveTDerivative.c q t z) (CriticalPositiveTDerivative.eta q t) z 0 (t-z)+
      V (Real.sqrt q) (CriticalPositiveTDerivative.ell q t z) (CriticalPositiveTDerivative.m q t z) t := by
  rw [CriticalPositiveTDerivative.scalar_formula]
  simp only [ExceptionalPositiveTStress.baseline,ExceptionalPositiveTStress.bWeight,
    ExceptionalPositiveTStress.tWeight,SoleEStress.zeroNorms,OrdinaryAngleConcavity.V,pairNorm,
    CriticalPositiveTDerivative.p,CriticalPositiveTDerivative.m,ExceptionalContactStress.tilt,
    contactScalar,↓reduceIte,Real.sin_zero,Real.cos_zero,Real.sin_neg]
  ring_nf

theorem value_lower {C : SignedCycle} {ab : Fin 4} (td : Bool)
    {R t z k l c m eta x : ℝ} (hab : ab=0 ∨ ab=2)
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (h : Bounds t z k l c m eta) (hm : m=c*tilt eta z) (hx : x∈Icc 0 (t-z))
    (hsource : ExceptionalPositiveTStress.primary C td=z)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained (R^2))
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td=t)
    (hcontact : Contact C) :
    ExceptionalPositiveTStress.baseline td R k l c eta z x (t-z-x)+V R l m t≤
      ExceptionalPositiveTStress.value C ab td R k l c eta t z x := by
  have hx' : x∈Icc 0 t := ⟨hx.1,by linarith [hx.2,h.z_nonneg]⟩
  have he : t-z-x∈Icc 0 t := ⟨by linarith [hx.2],by linarith [hx.1,h.z_nonneg]⟩
  have hT : 0≤ExceptionalPositiveTStress.primary C td := by rw [hsource]; exact h.z_nonneg
  have hi := CriticalPositiveTEnvelope.original_increment td hab hR hQL hQU h hx' he
    ha hvar hG hD hT htotal
  have hid : ExceptionalPositiveTBlocks.increment C ab td (weights td k l c m eta x (t-z-x)) R=
      ExceptionalPositiveTStress.increment C ab td R k l c eta z x (t-z-x) := by
    cases td <;> simp [ExceptionalPositiveTBlocks.increment,weights,
      ExceptionalPositiveTStress.increment,ExceptionalPositiveTStress.bWeight,
      ExceptionalPositiveTStress.tWeight,hm]
  rw [hid] at hi
  have hv := ExceptionalPositiveTSupport.value_lower (k:=k) (l:=l) (c:=c) td hab hR
    (show 0≤eta by linarith [h.eta_lower]) h.angle ⟨h.z_nonneg,h.z_le⟩ hx hsource hs hc hn ha hcontact
  linarith

theorem fixed_endpoints {q t z : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hz : z∈Icc 0 t)
    {C : SignedCycle} {ab : Fin 4} (td : Bool) (hab : ab=0 ∨ ab=2)
    (hsource : ExceptionalPositiveTStress.primary C td=z)
    (hs : ∀ i,(C.point i).Sorted) (hc : ∀ i,(C.point i).Contained q)
    (hn : C.NormalAnchors) (ha : ∀ i,|delta C.theta i|≤frameCap)
    (hvar : positiveVariation C.theta≤frameCap) (hG : 0≤delta C.theta G)
    (hD : 0≤delta C.theta D)
    (htotal : delta C.theta G+delta C.theta D+ExceptionalPositiveTStress.primary C td=t)
    (hcontact : Contact C) :
    CriticalPositiveTDerivative.scalar q t z≤ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
      (CriticalPositiveTDerivative.k q t z) (CriticalPositiveTDerivative.ell q t z)
      (CriticalPositiveTDerivative.c q t z) (CriticalPositiveTDerivative.eta q t) t z 0 ∧
    CriticalPositiveTDerivative.scalar q t z≤ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
      (CriticalPositiveTDerivative.k q t z) (CriticalPositiveTDerivative.ell q t z)
      (CriticalPositiveTDerivative.c q t z) (CriticalPositiveTDerivative.eta q t) t z (t-z) ∧
    (0<t-z → CriticalPositiveTDerivative.scalar q t z<
      ExceptionalPositiveTStress.value C ab td (Real.sqrt q)
        (CriticalPositiveTDerivative.k q t z) (CriticalPositiveTDerivative.ell q t z)
        (CriticalPositiveTDerivative.c q t z) (CriticalPositiveTDerivative.eta q t) t z (t-z)) := by
  have hb := CriticalPositiveTDerivative.coefficients hq ht hz
  have hR := Real.sqrt_nonneg q
  have hR2 := Real.sq_sqrt (show 0≤q by norm_num [qLow] at hq; linarith [hq.1])
  have hRL : qLow≤(Real.sqrt q)^2 := by simpa only [hR2] using hq.1
  have hRU : (Real.sqrt q)^2≤qCap := by rw [hR2]; exact hq.2.trans uniform_radius_order.2.2.1.le
  have hc' : ∀ i,(C.point i).Contained ((Real.sqrt q)^2) := by simpa only [hR2] using hc
  have hzero : (0:ℝ)∈Icc 0 (t-z) := ⟨le_rfl,by linarith [hz.2]⟩
  have hright : t-z∈Icc 0 (t-z) := ⟨by linarith [hz.2],le_rfl⟩
  have hv0 := value_lower td hab hR hRL hRU hb rfl hzero hsource hs hc' hn ha hvar hG hD htotal hcontact
  have hv1 := value_lower td hab hR hRL hRU hb rfl hright hsource hs hc' hn ha hvar hG hD htotal hcontact
  simp only [sub_zero,sub_self] at hv0 hv1
  have hrow := td_le_row td (x:=0) (e:=t-z) hR hb rfl
  have hsplit := E_le_G td hR hRL hb
  have hid := scalar_eq q t z
  refine ⟨by linarith,by linarith,?_⟩
  intro hpos
  have hstrict := E_lt_G td hR hRL hb hpos
  linarith

end SquaresInCircles.Eight.CriticalPositiveTEndpoints
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CriticalPositiveTExclusion
open Candidate ExceptionalContactStress ExceptionalPositiveTStress

theorem original_G_T_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4} (td : Bool)
    (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤primary C td)
    (ht : delta C.theta G+delta C.theta D+primary C td∈Icc (1/10:ℝ) (4/25))
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) :
    delta C.theta G=0 ∧ primary C td=0 := by
  let z := primary C td
  let t := delta C.theta G+delta C.theta D+z
  have htotal : delta C.theta G+delta C.theta D+primary C td=t := rfl
  have ht' : t∈Icc (1/10:ℝ) (4/25) := ht
  have hz : z∈Icc 0 t := ⟨hT,by dsimp [t]; linarith⟩
  have hx : delta C.theta G∈Icc 0 (t-z) := ⟨hG,by dsimp [t]; linarith⟩
  have hb := CriticalPositiveTDerivative.coefficients hsharp ht' hz
  have hR := Real.sqrt_nonneg d.q
  have hR2 := Real.sq_sqrt (show 0≤d.q by norm_num [qLow] at hsharp; linarith [hsharp.1])
  have hcap : d.q≤qCap := hsharp.2.trans uniform_radius_order.2.2.1.le
  have hc : ∀ i,(C.point i).Contained d.q := fun i => (hC.contained i).trans hq
  have hc' : ∀ i,(C.point i).Contained ((Real.sqrt d.q)^2) := by simpa only [hR2] using hc
  have hcCap : ∀ i,(C.point i).Contained qCap := fun i => (hc i).trans hcap
  have ha : ∀ i,|delta C.theta i|≤frameCap := fun i => hC.spread (next i) i
  have hconc := ExceptionalPositiveTStress.concave ab td hR
    (by simpa only [hR2] using hcap)
    (show CriticalPositiveTDerivative.k d.q t z∈Icc (431/500:ℝ) (521/500) by
      constructor <;> linarith [hb.k_lower,hb.k_upper])
    (show CriticalPositiveTDerivative.eta d.q t∈Icc (1/4:ℝ) (327/1000) by
      constructor <;> linarith [hb.eta_lower,hb.eta_upper])
    hb.angle hz hC.sorted hcCap ha hEy
    (l:=CriticalPositiveTDerivative.ell d.q t z) (c:=CriticalPositiveTDerivative.c d.q t z)
  obtain ⟨h0,h1,hstrict⟩ := CriticalPositiveTEndpoints.fixed_endpoints hsharp ht' hz td hab
    rfl hC.sorted hc hn ha hvar hG hD htotal hcontact
  have hnonneg := CriticalPositiveTDerivative.scalar_nonneg hd hsharp ht' hz
  have hnec := ExceptionalPositiveTStress.necessary td hab hR
    (show 0≤CriticalPositiveTDerivative.k d.q t z by linarith [hb.k_lower]) hb.ell_pos.le
    (show 0≤CriticalPositiveTDerivative.c d.q t z by linarith [hb.c_lower])
    (show 0≤CriticalPositiveTDerivative.eta d.q t by linarith [hb.eta_lower])
    hb.angle hz rfl hG hD (by simpa only [z] using htotal) hC.sorted hc' hn hcontact hf
  constructor
  · by_contra hne
    have hGpos : 0<delta C.theta G := lt_of_le_of_ne hG (Ne.symm hne)
    have hright : 0<t-z := hGpos.trans_le hx.2
    have hpos := ExceptionalContactCurvature.positive_of_positive_right hconc
      ⟨hGpos,hx.2⟩ (hnonneg.trans h0) (hnonneg.trans_lt (hstrict hright))
    exact (not_lt_of_ge hnec) hpos
  · by_contra hne
    have hzpos : 0<z := lt_of_le_of_ne hz.1 (Ne.symm hne)
    have hs := CriticalPositiveTDerivative.scalar_pos_of_z_pos hd hsharp ht' ⟨hzpos,hz.2⟩
    have hscalar : 0<CriticalPositiveTDerivative.scalar d.q t z := by nlinarith
    have hmin := hconc.min_le_of_mem_Icc
      (show (0:ℝ)∈Icc 0 (t-z) from ⟨le_rfl,by linarith [hz.2]⟩)
      (show t-z∈Icc 0 (t-z) from ⟨by linarith [hz.2],le_rfl⟩) hx
    have hpos := (lt_min (hscalar.trans_le h0) (hscalar.trans_le h1)).trans_le hmin
    exact (not_lt_of_ge hnec) hpos

end SquaresInCircles.Eight.CriticalPositiveTExclusion

namespace SquaresInCircles.Eight.ExceptionalPositiveTComplete
open Candidate ExceptionalContactStress ExceptionalPositiveTStress

/-- On the whole domain, a nonnegative T primary at the EH contact forces `delta C.theta G = 0` and
`primary C td = 0`: outside the critical strip the scalar reserve is strict, and on the strip the
sharp zero forces both primary errors to vanish. -/
theorem original_G_T_zero {d : Stationary.Coordinates} (hd : d.IsStationary)
    (hsharp : d.q∈Icc qLow qTrial) {C : SignedCycle} {q : ℝ} {ab : Fin 4} (td : Bool)
    (hQL : qLow≤q) (hq : q≤d.q) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hvar : positiveVariation C.theta≤frameCap) (hab : ab=0 ∨ ab=2)
    (hG : 0≤delta C.theta G) (hD : 0≤delta C.theta D) (hT : 0≤primary C td)
    (hEy : 0≤(C.point E).y) (hcontact : Contact C)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab (btOwner td) (tdOwner td) 3 0 i)) :
    delta C.theta G=0 ∧ primary C td=0 := by
  by_cases ht : delta C.theta G+delta C.theta D+primary C td∈Icc (1/10:ℝ) (4/25)
  · exact CriticalPositiveTExclusion.original_G_T_zero hd hsharp td hq hC hn hvar hab
      hG hD hT ht hEy hcontact hf
  · have hout : delta C.theta G+delta C.theta D+primary C td≤1/10 ∨
        4/25≤delta C.theta G+delta C.theta D+primary C td := by
      by_cases hl : delta C.theta G+delta C.theta D+primary C td≤1/10
      · exact Or.inl hl
      · exact Or.inr (by by_contra! hh; exact ht ⟨(lt_of_not_ge hl).le,hh.le⟩)
    exact (ExceptionalPositiveTOutside.original_false td hQL (hq.trans hsharp.2) hC hn hvar
      hab hG hD hT hEy hcontact hout hf).elim

end SquaresInCircles.Eight.ExceptionalPositiveTComplete
end
end
end
