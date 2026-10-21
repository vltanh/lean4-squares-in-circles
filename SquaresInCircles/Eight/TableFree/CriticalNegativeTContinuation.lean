module

public import SquaresInCircles.Eight.TableFree.CriticalNegativeTCurvature

/-!
# Strict negative-T gain on every critical primary interval

Uncompiled source. Endpoint certificates and whole-interval curvature
cover every genuine negative primary. The signed ordinary envelope
keeps the smaller of the original A and B charges when s≤t, and the
uniform positive-surplus cost when s≥t. The coefficients and radius
are selected from the same actual critical supporting chain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalNegativeTContinuation
open Candidate CriticalEExclusion CriticalECoefficients CriticalNegativeTGain
open CriticalNegativeTCurvature FlatTStress PositiveAngularEnvelope
open OrdinaryAngleConcavity SingleAngleConcavity

def gamma : ℝ := (109/200)*(21/20)

def lowerEnvelope (R k l c t s : ℝ) : ℝ :=
  if s≤t then min (Vnu R l k l (t-s)) (V R l c (t-s)) else -gamma*(s-t)

theorem radius_bounds {q : ℝ} (hq : q∈Icc qLow qTrial) :
    0≤Real.sqrt q ∧ qLow≤(Real.sqrt q)^2 ∧ (Real.sqrt q)^2≤qCap ∧ Real.sqrt q≤2 := by
  have hq0 : 0≤q := by norm_num [qLow] at hq; linarith [hq.1]
  have he := Real.sq_sqrt hq0
  have hcap := hq.2.trans uniform_radius_order.2.2.1.le
  refine ⟨Real.sqrt_nonneg q,by simpa only [he] using hq.1,
    by simpa only [he] using hcap,?_⟩
  norm_num [qCap] at hcap
  nlinarith [Real.sqrt_nonneg q]

theorem TD_negative_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Ioc 0 t) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) 1 s+
        min (Vnu (Real.sqrt q) (L q t) (K q t) (L q t) (t-s))
          (V (Real.sqrt q) (L q t) (Cc q t) (t-s)) := by
  have h := coefficient_bounds hq ht
  have hr := radius_bounds hq
  have ho := h.order
  have hA := CriticalEPureCharges.A_ge_B ⟨hr.1,hr.2.2.2⟩ h
  have hG := TD_endpoint hq ht
  have hconcA := TD_concave hr.1 hr.2.1 hr.2.2.1 h ho.2.1 ho.2.2.2.2.2.1 (le_refl _)
  have hconcB := TD_concave hr.1 hr.2.1 hr.2.2.1 h ho.2.2.1 ho.2.2.2.2.1 ho.2.2.1
  have hzero : secantCharge (Real.sqrt q) (Cc q t) 1 0=0 := by simp [secantCharge]
  have hleftA : 0≤pairValue (Real.sqrt q) (Cc q t) 1 (L q t) (K q t) (L q t) t 0-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simpa [pairValue,hzero] using sub_nonneg.mpr hA
  have hrightA : 0<pairValue (Real.sqrt q) (Cc q t) 1 (L q t) (K q t) (L q t) t t-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simpa [pairValue] using sub_pos.mpr hG
  have hleftB : 0≤pairValue (Real.sqrt q) (Cc q t) 1 (L q t) (Cc q t) (Cc q t) t 0-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simp [pairValue,hzero]
  have hrightB : 0<pairValue (Real.sqrt q) (Cc q t) 1 (L q t) (Cc q t) (Cc q t) t t-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simpa [pairValue] using sub_pos.mpr hG
  have hsa := ExceptionalContactCurvature.positive_of_positive_right
    (hconcA.sub_const (V (Real.sqrt q) (L q t) (Cc q t) t)) hs hleftA hrightA
  have hsb := ExceptionalContactCurvature.positive_of_positive_right
    (hconcB.sub_const (V (Real.sqrt q) (L q t) (Cc q t) t)) hs hleftB hrightB
  dsimp [pairValue] at hsa hsb
  rw [Vnu_larger] at hsb
  rw [add_min]
  exact lt_min (by linarith) (by linarith)

theorem TD_positive_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Icc t (3/10:ℝ)) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) 1 s-gamma*(s-t) := by
  have h := coefficient_bounds hq ht
  have hG := TD_endpoint hq ht
  have hd := TD_late_growth hq h hs
  have hlen : 0≤s-t := sub_nonneg.mpr hs.1
  dsimp [gamma]
  nlinarith

theorem BT_negative_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Ioc 0 shortAngle) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) (L q t) s+
        min (Vnu (Real.sqrt q) (L q t) (K q t) (L q t) (t-s))
          (V (Real.sqrt q) (L q t) (Cc q t) (t-s)) := by
  have h := coefficient_bounds hq ht
  have hr := radius_bounds hq
  have ho := h.order
  have hA := CriticalEPureCharges.A_ge_B ⟨hr.1,hr.2.2.2⟩ h
  have hG := BT_endpoints hq ht
  have hconcA := BT_concave hr.1 hr.2.1 hr.2.2.1 h ho.2.1 ho.2.2.2.2.2.1 (le_refl _)
  have hconcB := BT_concave hr.1 hr.2.1 hr.2.2.1 h ho.2.2.1 ho.2.2.2.2.1 ho.2.2.1
  have hzero : secantCharge (Real.sqrt q) (Cc q t) (L q t) 0=0 := by simp [secantCharge]
  have hleftA : 0≤pairValue (Real.sqrt q) (Cc q t) (L q t) (L q t) (K q t) (L q t) t 0-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simpa [pairValue,hzero] using sub_nonneg.mpr hA
  have hrightA : 0<pairValue (Real.sqrt q) (Cc q t) (L q t) (L q t) (K q t) (L q t) t shortAngle-
      V (Real.sqrt q) (L q t) (Cc q t) t := by dsimp [pairValue]; linarith [hG.2]
  have hleftB : 0≤pairValue (Real.sqrt q) (Cc q t) (L q t) (L q t) (Cc q t) (Cc q t) t 0-
      V (Real.sqrt q) (L q t) (Cc q t) t := by simp [pairValue,hzero]
  have hrightB : 0<pairValue (Real.sqrt q) (Cc q t) (L q t) (L q t) (Cc q t) (Cc q t) t shortAngle-
      V (Real.sqrt q) (L q t) (Cc q t) t := by
    simp only [pairValue,Vnu_larger]
    linarith [hG.1]
  have hsa := ExceptionalContactCurvature.positive_of_positive_right
    (hconcA.sub_const (V (Real.sqrt q) (L q t) (Cc q t) t)) hs hleftA hrightA
  have hsb := ExceptionalContactCurvature.positive_of_positive_right
    (hconcB.sub_const (V (Real.sqrt q) (L q t) (Cc q t) t)) hs hleftB hrightB
  dsimp [pairValue] at hsa hsb
  rw [Vnu_larger] at hsb
  rw [add_min]
  exact lt_min (by linarith) (by linarith)

theorem TD_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Ioc 0 (3/10:ℝ)) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) 1 s+
        lowerEnvelope (Real.sqrt q) (K q t) (L q t) (Cc q t) t s := by
  by_cases hst : s≤t
  · simpa [lowerEnvelope,hst] using TD_negative_gain hq ht ⟨hs.1,hst⟩
  · simpa [lowerEnvelope,hst,sub_eq_add_neg] using
      TD_positive_gain hq ht ⟨(lt_of_not_ge hst).le,hs.2⟩

theorem BT_gain {q t s : ℝ} (hq : q∈Icc qLow qTrial)
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hs : s∈Ioc 0 shortAngle) :
    V (Real.sqrt q) (L q t) (Cc q t) t<
      secantCharge (Real.sqrt q) (Cc q t) (L q t) s+
        lowerEnvelope (Real.sqrt q) (K q t) (L q t) (Cc q t) t s := by
  have hst : s≤t := by dsimp [shortAngle] at hs; linarith [hs.2,ht.1]
  simpa [lowerEnvelope,hst] using BT_negative_gain hq ht hs

end SquaresInCircles.Eight.TableFree.CriticalNegativeTContinuation
