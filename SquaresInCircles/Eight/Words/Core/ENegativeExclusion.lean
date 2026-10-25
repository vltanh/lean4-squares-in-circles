module

public import SquaresInCircles.Eight.Owners.Negative.SecondaryEExclusion
public import SquaresInCircles.Eight.Owners.Positive.SecondaryEExclusion
public import SquaresInCircles.Eight.Words.Core.EOrdinaryEnvelope

/-!
# Eight squares: core E with nonnegative primary total, including all preprocessed T cases

A negative T primary is classified at its original boundary point. An available secondary is
reselected at that same point (`reselect_TD`, `reselect_BT`); otherwise the flat-coordinate and
short-angle theorems supply the secant stress (`flat_negative_TD_false`,
`flat_negative_BT_false`). The original E point, both E owners and both E frame errors stay
unchanged throughout. `preprocessed_core_E_false` collects all preprocessed T owners.
-/

section
/-!
## Nonnegative E charge with a negative T primary

The negative T magnitude is kept in both ordinary variation caps and in its secant coefficient.
For a nonnegative ordinary imbalance, concavity leaves E-total zero, the far endpoint and the
pure-sign junction. For a negative imbalance the low-angle ordinary bounds absorb the whole E
charge directly. Together they give the lower bound `mixed_sum_lower`.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CoreENegativeEnvelope
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open PositiveStressCoefficients PositiveOrdinaryEnvelope NegativeOrdinaryParameters
open OrdinaryNegativeEnvelope RemovedPrimaryConcentration
open PositiveScalarTransfer (J)

def zeroLower (d : ℝ) : ℝ :=
  min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)
def farLower (d : ℝ) : ℝ :=
  min (J (frameCap-d)+lN d-87/1250) (J (frameCap-d)+lambdaN d*frameCap)
def lower (d : ℝ) : ℝ := min (zeroLower d) (farLower d)

theorem far_single {d s b t : ℝ} (h : Bounds d s b t) (hb : b≤26/25)
    (i : Fin 4) :
    lN d-87/1250<V (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) frameCap := by
  have hp := PositiveOrdinaryParameters.familyN h.angle
  have hl := (CoreEOrdinaryEnvelope.coefficient_intervals h.angle).2
  have hi := domains h i
  have hk : k=863/1000 := rfl
  fin_cases i
  · have hr : (87/100)*SecondaryEStress.tiltedWeight k (19/50) d<
        V (Real.sqrt qCap) (SecondaryEStress.tiltedWeight k (19/50) d) 1 frameCap :=
      V_endpoint_lower sqrt_cap_lower hi.1 hi.2.1 hi.2.2.1
    have hn := hp.H_lower
    show lN d-87/1250<V (Real.sqrt qCap) (SecondaryEStress.tiltedWeight k (19/50) d) 1 frameCap
    linarith [hl.2]
  · exact CoreEFarEndpoint.rectangle_lower hl
      (show k∈Icc (863/1000) (26/25) by norm_num [k])
  · exact CoreEFarEndpoint.rectangle_lower hl ⟨h.B_lower,hb⟩
  · have hr : (87/100)*min 1 t<V (Real.sqrt qCap) (min 1 t) (max 1 t) frameCap :=
      V_endpoint_lower sqrt_cap_lower hi.1 hi.2.1 hi.2.2.1
    have ht : k ≤ min 1 t := le_min (by norm_num [k]) h.D_lower
    show lN d-87/1250<V (Real.sqrt qCap) (min 1 t) (max 1 t) frameCap
    linarith [hl.2]

theorem far_chord {d s b t : ℝ} (h : Bounds d s b t) (hb : b≤26/25)
    (j : Fin 4) :
    min (lN d-87/1250) (lambdaN d*frameCap)≤lambdaN d*s+
      V (Real.sqrt qCap)
        (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j)
        (qs b t j) (frameCap-s) := by
  let p := ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j
  let q := qs b t j
  let m := min (lN d-87/1250) (lambdaN d*frameCap)
  have hj := domains h j
  have hs : 0≤(10/7)*s ∧ (10/7)*s≤1 := by
    constructor <;> linarith [h.short.1,h.short.2]
  have hc := V_concave (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hj.1 hj.2.1 hj.2.2.1
  have hch := hc.2 (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap from ⟨by norm_num [frameCap],le_rfl⟩)
    hs.1 (sub_nonneg.mpr hs.2) (by ring)
  have heq : ((10/7)*s)*0+(1-(10/7)*s)*frameCap=frameCap-s := by
    simp only [frameCap]
    ring
  simp only [smul_eq_mul] at hch
  rw [heq,V_zero,mul_zero,zero_add] at hch
  have hfar := mul_le_mul_of_nonneg_left (far_single h hb j).le (sub_nonneg.mpr hs.2)
  have h1 := mul_nonneg (sub_nonneg.mpr hs.2)
    (sub_nonneg.mpr (show m≤lN d-87/1250 from min_le_left _ _))
  have h2 := mul_nonneg hs.1
    (sub_nonneg.mpr (show m≤lambdaN d*frameCap from min_le_right _ _))
  have hfc : frameCap=7/10 := rfl
  change m≤lambdaN d*s+V (Real.sqrt qCap) p q (frameCap-s)
  change (1-(10/7)*s)*V (Real.sqrt qCap) p q frameCap≤V (Real.sqrt qCap) p q (frameCap-s) at hch
  change (1-(10/7)*s)*(lN d-87/1250)≤(1-(10/7)*s)*V (Real.sqrt qCap) p q frameCap at hfar
  generalize V (Real.sqrt qCap) p q frameCap=V1 at hch hfar
  generalize V (Real.sqrt qCap) p q (frameCap-s)=V2 at hch ⊢
  generalize m=M at h1 h2 ⊢
  rw [hfc] at h2
  linarith

theorem far_charge {d s b t : ℝ} (h : Bounds d s b t) (hb : b≤26/25)
    (j : Fin 4) :
    farLower d≤J (frameCap-d)+lambdaN d*s+
      V (Real.sqrt qCap)
        (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j)
        (qs b t j) (frameCap-s) := by
  have hh := far_chord h hb j
  rcases min_choice (lN d-87/1250) (lambdaN d*frameCap) with hm | hm
  · rw [hm] at hh
    have hf : farLower d≤J (frameCap-d)+lN d-87/1250 := min_le_left _ _
    linarith
  · rw [hm] at hh
    have hf : farLower d≤J (frameCap-d)+lambdaN d*frameCap := min_le_right _ _
    generalize J (frameCap-d)=J0 at hf ⊢
    generalize lambdaN d*frameCap=L at hh hf
    linarith

theorem zero_saturated {d s b t : ℝ} (h : Bounds d s b t) (i j : Fin 4) :
    zeroLower d≤lambdaN d*s+
      (if i=j then mixedBlock (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i)
          (qs b t i) (frameCap-d) (frameCap-s)
       else U (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i)
          (qs b t i) (frameCap-d)+
        V (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j)
          (qs b t j) (frameCap-s)) := by
  have hP0 : 0≤frameCap-d := by linarith [h.angle.2]
  have hN0 : 0≤frameCap-s := by dsimp [frameCap]; linarith [h.short.2]
  have hP (a : Fin 4) : 0≤ massAt i (frameCap-d) a := by
    simp only [massAt]
    split_ifs <;> linarith
  have hN (a : Fin 4) : 0≤ massAt j (frameCap-s) a := by
    simp only [massAt]
    split_ifs <;> linarith
  have hsP : (∑ a : Fin 4,massAt i (frameCap-d) a)=frameCap-d := by simp [massAt]
  have hsN : (∑ a : Fin 4,massAt j (frameCap-s) a)=frameCap-s := by simp [massAt]
  have hh := NegativeOrdinaryEnvelope.mixed_sum_lower h
    (massAt i (frameCap-d)) (massAt j (frameCap-s)) hP hN (by rw [hsP])
    (by rw [hsP,hsN]; ring)
  rw [concentrated_sum] at hh
  exact hh

theorem pure_lower {d s b t e : ℝ} (h : Bounds d s b t) (hb : b≤26/25)
    (he : e∈Icc 0 (frameCap-d)) (hsd : s≤d+e) (j : Fin 4) :
    lower d≤J e+lambdaN d*s+V (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j)
      (qs b t j) (d+e-s) := by
  let a := max 0 (s-d)
  have hj := domains h j
  have ha0 : 0≤a := le_max_left _ _
  have has : s-d≤a := le_max_right _ _
  have hae : a≤e := max_le he.1 (by linarith)
  have hau : a≤frameCap-d := hae.trans he.2
  have hJ := CoreECharge.J_concave.subset
    (Icc_subset_Icc ha0 (by linarith [h.angle.1])) (convex_Icc a (frameCap-d))
  have hV := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hj.1 hj.2.1 hj.2.2.1)
    (a := 1) (b := d-s) (l := a) (u := frameCap-d)
    (fun u hu => ⟨by linarith [hu.1],by linarith [hu.2,h.short.1]⟩)
  have hconc : ConcaveOn ℝ (Icc a (frameCap-d))
      (fun u => J u+lambdaN d*s+V (Real.sqrt qCap)
        (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j) (d+u-s)) := by
    refine ((hJ.add_const (lambdaN d*s)).add hV).congr ?_
    intro u _
    simp only [Pi.add_apply]
    rw [show 1*u+(d-s)=d+u-s by ring]
  have hleft : lower d≤J a+lambdaN d*s+V (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j) (d+a-s) := by
    by_cases hsd0 : s≤d
    · have ha : a=0 := max_eq_left (by linarith)
      have hv := NegativeOrdinaryParameters.single_negative_lower h hsd0
        (show d-s∈Icc 0 (d-s) from ⟨by linarith,le_rfl⟩) j
      have hg := NegativeOrdinaryEnvelope.gain_junction h.angle ⟨h.short.1,hsd0⟩
      have hm : lower d≤zeroLower d := min_le_left _ _
      rw [ha]
      simp only [J,Real.sin_zero,Real.cos_zero,zero_div,neg_zero,sub_self,mul_zero,
        zero_add,add_zero]
      dsimp only [zeroLower] at *
      linarith
    · have hds : d ≤ s := (lt_of_not_ge hsd0).le
      have ha : a=s-d := max_eq_right (by linarith)
      have hlam : 1111/1250≤lambdaN d := by
        dsimp [lambdaN]
        linarith [h.angle.1]
      have he' : s-d∈Icc 0 frameCap :=
        ⟨by linarith,by dsimp [frameCap]; linarith [h.short.2,h.angle.1]⟩
      have hg := CoreECharge.charge_gain_junction hlam he'
      have hm : lower d≤lambdaN d*d :=
        (min_le_left _ _).trans (min_le_right _ _)
      rw [ha,show d+(s-d)-s=0 by ring,V_zero,add_zero]
      linarith
  have hright : lower d≤J (frameCap-d)+lambdaN d*s+V (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j)
      (d+(frameCap-d)-s) := by
    have hh := far_charge h hb j
    have hm : lower d≤farLower d := min_le_right _ _
    rw [show d+(frameCap-d)-s=frameCap-s by ring]
    exact hm.trans hh
  exact (le_min hleft hright).trans
    (hconc.min_le_of_mem_Icc ⟨le_rfl,hau⟩ ⟨hau,le_rfl⟩ ⟨hae,he.2⟩)

theorem saturated_lower {d s b t e : ℝ} (h : Bounds d s b t) (hb : b≤26/25)
    (he : e∈Icc 0 (frameCap-d)) (i j : Fin 4) :
    lower d≤J e+lambdaN d*s+
      (if i=j then mixedBlock (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i)
          (qs b t i) (frameCap-d-e) (frameCap-s)
       else U (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i)
          (qs b t i) (frameCap-d-e)+
        V (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j)
          (qs b t j) (frameCap-s)) := by
  let p := ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t
  let q := qs b t
  let f (u : ℝ) := if i=j then
      mixedBlock (Real.sqrt qCap) (p i) (q i) (frameCap-d-u) (frameCap-s)
    else U (Real.sqrt qCap) (p i) (q i) (frameCap-d-u)+
      V (Real.sqrt qCap) (p j) (q j) (frameCap-s)
  have hi := domains h i
  have hR := Real.sqrt_nonneg qCap
  have hQ := (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
  have hN : frameCap-s∈Icc 0 frameCap :=
    ⟨by dsimp [frameCap]; linarith [h.short.2],by linarith [h.short.1]⟩
  have harg (u : ℝ) (hu : u∈Icc 0 (frameCap-d)) :
      -1*u+(frameCap-d)∈Icc 0 frameCap :=
    ⟨by linarith [hu.2],by linarith [hu.1,h.angle.1]⟩
  have hf : ConcaveOn ℝ (Icc 0 (frameCap-d)) f := by
    by_cases hij : i=j
    · have hc := concave_affine_argument
        (mixedBlock_concave_positive hR hQ hi.1 hi.2.1 hi.2.2.1 hN)
        (a := -1) (b := frameCap-d) harg
      convert hc using 1
      funext u
      simp only [f,ite_eq_left hij]
      congr 1
      ring
    · have hc := (concave_affine_argument (U_concave hR hQ hi.1 hi.2.1 hi.2.2.1)
        (a := -1) (b := frameCap-d) harg).add_const
          (V (Real.sqrt qCap) (p j) (q j) (frameCap-s))
      convert hc using 1
      funext u
      simp only [f,ite_eq_right hij]
      congr 2
      ring
  have hconc := ((CoreEOrdinaryEnvelope.J_restricted h.angle).add_const (lambdaN d*s)).add hf
  have hleft : lower d≤J 0+lambdaN d*s+f 0 := by
    have hz := zero_saturated h i j
    have hm : lower d≤zeroLower d := min_le_left _ _
    simpa [J,f,p,q] using hm.trans hz
  have hright : lower d≤J (frameCap-d)+lambdaN d*s+f (frameCap-d) := by
    have hz := far_charge h hb j
    have hm : lower d≤farLower d := min_le_right _ _
    by_cases hij : i=j
    · subst j
      simpa [f,p,q] using hm.trans hz
    · simpa [f,p,q,hij] using hm.trans hz
  have hh : 0≤frameCap-d := by linarith [h.angle.2]
  exact (le_min hleft hright).trans
    (hconc.min_le_of_mem_Icc ⟨le_rfl,hh⟩ ⟨hh,le_rfl⟩ he)

theorem positive_imbalance {d s b t e : ℝ} (h : Bounds d s b t)
    (he : e∈Icc 0 (frameCap-d)) (hds : d+e≤ s)
    (P N : Fin 4 → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d-e)
    (hbalance : (∑ i,N i)=d+e-s+∑ i,P i) :
    lambdaN d*d≤J e+lambdaN d*s+∑ i,mixedBlock (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (P i) (N i) := by
  let p := ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t
  let q := qs b t
  have hd : d≤3/10 := by linarith [he.1,h.short.2]
  have hPt : (∑ i,P i)≤frameCap := by linarith [h.angle.1,he.1]
  have hNt : (∑ i,N i)≤frameCap := by linarith [h.short.1]
  have hP0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hP i)
  have hN0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hN i)
  obtain ⟨i,j,hconc⟩ := both_signs_concentrate (Real.sqrt qCap) p q P N
    (Real.sqrt_nonneg qCap) (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (fun i => (domains h i).1) (fun i => (domains h i).2.1)
    (fun i => (domains h i).2.2.1) hP hN hPt hNt
  have hlow : -(571/1000)*(s-d-e)≤
      if i=j then mixedBlock (Real.sqrt qCap) (p i) (q i) (∑ k,P k) (∑ k,N k)
      else U (Real.sqrt qCap) (p i) (q i) (∑ k,P k)+
        V (Real.sqrt qCap) (p j) (q j) (∑ k,N k) := by
    by_cases hij : i=j
    · rw [ite_eq_left hij]
      have hi := domains h i
      have hq0 : 0≤q i := (hi.1.trans_le hi.2.1).le
      have hratio : (29/50)*q i≤p i := by
        have hr : 29/50≤ratio d-31/10000 := by dsimp [ratio]; linarith [h.angle.1]
        exact (mul_le_mul_of_nonneg_right hr hq0).trans hi.2.2.2.1
      have hs := RelaxedSameBlock.positive_surplus (R := Real.sqrt qCap) hq0 hratio
        ⟨hP0,hPt⟩ (show (∑ k,N k)∈Icc 0 (∑ k,P k) from ⟨hN0,by linarith⟩)
      have heq : (∑ k,P k)-(∑ k,N k)=s-d-e := by linarith
      rw [heq] at hs
      exact (NegativeOrdinaryEnvelope.low_U_lower h hd i
        (show s-d-e∈Icc 0 frameCap from
          ⟨by linarith,by dsimp [frameCap]; linarith [h.short.2,h.angle.1,he.1]⟩)).trans hs
    · rw [ite_eq_right hij]
      have hu := NegativeOrdinaryEnvelope.low_U_lower h hd i ⟨hP0,hPt⟩
      have hv := NegativeOrdinaryEnvelope.low_V_lower h hd j ⟨hN0,hNt⟩
      have hm := mul_le_mul_of_nonneg_right
        (NegativeOrdinaryEnvelope.low_constants ⟨h.angle.1,hd⟩).1 hN0
      dsimp [p,q] at *
      nlinarith
  have hsum := hlow.trans hconc
  have hJ := CoreECharge.J_linear_lower
    (show e∈Icc 0 frameCap from ⟨he.1,by linarith [he.2,h.angle.1]⟩)
  have hlam : 1111/1250≤lambdaN d := by dsimp [lambdaN]; linarith [h.angle.1]
  have hreserve := mul_nonneg (show 0≤lambdaN d-783/1000 by linarith)
    (show 0≤ s-d by linarith [he.1])
  have heReserve : 0≤(212/1000)*(s-d-e) := by nlinarith
  dsimp [p,q] at *
  nlinarith

theorem mixed_sum_lower {d s b t e : ℝ} (h : Bounds d s b t) (hb : b≤26/25)
    (he : e∈Icc 0 (frameCap-d))
    (P N : Fin 4 → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d-e)
    (hbalance : (∑ i,N i)=d+e-s+∑ i,P i) :
    lower d≤J e+lambdaN d*s+∑ i,mixedBlock (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (P i) (N i) := by
  by_cases hds : d+e≤ s
  · exact ((min_le_left _ _).trans (min_le_right _ _)).trans
      (positive_imbalance h he hds P N hP hN hbudget hbalance)
  have hsd : s≤d+e := (lt_of_not_ge hds).le
  have hd : d+e∈Icc 0 frameCap :=
    ⟨by linarith [h.angle.1,he.1],by linarith [he.2]⟩
  obtain ⟨i,j,hconc⟩ := negative_concentration (Real.sqrt qCap)
    (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t) (qs b t) P N
    (Real.sqrt_nonneg qCap) (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (fun i => (domains h i).1) (fun i => (domains h i).2.1)
    (fun i => (domains h i).2.2.1) hP hN hd ⟨h.short.1,hsd⟩
    (by linarith) hbalance
  have hpure := pure_lower h hb he hsd j
  have hsat := saturated_lower h hb he i j
  have hmin : lower d-J e-lambdaN d*s≤ min
      (V (Real.sqrt qCap)
        (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j) (d+e-s))
      (if i=j then mixedBlock (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i)
          (frameCap-(d+e)) (frameCap-s)
       else U (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i)
          (frameCap-(d+e))+
        V (Real.sqrt qCap)
          (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j)
          (frameCap-s)) := by
    rw [show frameCap-(d+e)=frameCap-d-e by ring]
    exact le_min (by linarith) (by linarith)
  have hh := hmin.trans hconc
  linarith

end SquaresInCircles.Eight.CoreENegativeEnvelope
end
end
end

section
/-!
## Actual signed budgets with negative T and either E owner

Positive and negative removed masses are exact
finite sums of the original angles. No chosen analytic concentration is
interpreted as a geometric change. The E-primary sum may contain an
opposite-signed pair; its common extra variation is discarded only in
the weaker analytic budget.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.CoreENegativeBlocks
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PositiveStressCoefficients
open SecondaryEStress PositiveOrdinaryEnvelope NegativeOrdinaryParameters ActualCoreEBlocks

theorem budgets {C : SignedCycle} {ab bt td de eh : Fin 4} {n k l b t d s : ℝ}
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap)
    (hpos : positivePart (delta C.theta G)+
      (if bt=3 then positivePart (delta C.theta B) else 0)+
      (if td=2 then positivePart (delta C.theta T) else 0)=d)
    (hneg : negativePart (delta C.theta G)+
      (if bt=3 then negativePart (delta C.theta B) else 0)+
      (if td=2 then negativePart (delta C.theta T) else 0)=s)
    (_he : 0≤eTotal C de eh) :
    eTotal C de eh≤frameCap-d ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).P)≤frameCap-d-eTotal C de eh ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).N)≤frameCap-s ∧
    (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
      d+eTotal C de eh-s+∑ i,(blocks C ab bt td de eh n k l b t i).P := by
  have hp := sum_parts C hab hbt htd hde heh n k l b t positivePart positivePart_zero
  have hn := sum_parts C hab hbt htd hde heh n k l b t negativePart negativePart_zero
  have hp' : (∑ i,(blocks C ab bt td de eh n k l b t i).P)=
      positiveVariation C.theta-d-positivePart (primaryDE C de)-positivePart (primaryEH C eh) := by
    change (∑ i,(positivePart (blocks C ab bt td de eh n k l b t i).u+
      positivePart (blocks C ab bt td de eh n k l b t i).v))=_
    rw [hp]
    dsimp [positiveVariation]
    linarith
  have hn' : (∑ i,(blocks C ab bt td de eh n k l b t i).N)=
      negativeVariation C.theta-s-negativePart (primaryDE C de)-negativePart (primaryEH C eh) := by
    change (∑ i,(negativePart (blocks C ab bt td de eh n k l b t i).u+
      negativePart (blocks C ab bt td de eh n k l b t i).v))=_
    rw [hn]
    dsimp [negativeVariation]
    linarith
  have hd := positive_sub_negative (primaryDE C de)
  have hh := positive_sub_negative (primaryEH C eh)
  have hnd := negativePart_nonneg (primaryDE C de)
  have hnh := negativePart_nonneg (primaryEH C eh)
  have heq := variations_equal C.theta
  have hP0 := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => (blocks C ab bt td de eh n k l b t i).P_nonneg)
  dsimp [eTotal] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem actual_lower {C : SignedCycle} {q d s b t : ℝ} {ab bt td de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (hab : ab=0 ∨ ab=2) (hbt : bt=2 ∨ bt=3) (htd : td=0 ∨ td=2)
    (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap)
    (hpos : positivePart (delta C.theta G)+
      (if bt=3 then positivePart (delta C.theta B) else 0)+
      (if td=2 then positivePart (delta C.theta T) else 0)=d)
    (hneg : negativePart (delta C.theta G)+
      (if bt=3 then negativePart (delta C.theta B) else 0)+
      (if td=2 then negativePart (delta C.theta T) else 0)=s)
    (he : 0≤eTotal C de eh) (h : Bounds d s b t) (hb : b≤26/25) :
    CoreENegativeEnvelope.lower d≤lambdaN d*s+
      CoreEStress.increment C ab bt td de eh (tiltedWeight k (19/50) d) k (lN d) b t
        (Real.sqrt qCap)+charge C de eh := by
  obtain ⟨Bs,hBs⟩ : ∃ Bs,Bs=blocks C ab bt td de eh (tiltedWeight k (19/50) d) k (lN d) b t :=
    ⟨_,rfl⟩
  have hbud := budgets (n := tiltedWeight k (19/50) d) (k := k) (l := lN d)
    (b := b) (t := t) hab hbt htd hde heh hvar hpos hneg he
  rw [← hBs] at hbud
  have hP := fun i => (Bs i).P_nonneg
  have hN := fun i => (Bs i).N_nonneg
  have hsumP : (∑ i,(Bs i).P)≤frameCap := by linarith [hbud.2.1,h.angle.1]
  have hsumN : (∑ i,(Bs i).N)≤frameCap := by linarith [hbud.2.2.1,h.short.1]
  have hPi (i : Fin 4) : (Bs i).P≤frameCap :=
    (Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ i)).trans hsumP
  have hNi (i : Fin 4) : (Bs i).N≤frameCap :=
    (Finset.single_le_sum (fun j _ => hN j) (Finset.mem_univ i)).trans hsumN
  have hc (i : Fin 4) :
      (Bs i).p=ps (tiltedWeight k (19/50) d) (lN d) t i ∧ (Bs i).q=qs b t i := by
    have h1 := ActualCoreEBlocks.block_coefficients C ab bt td de eh
      (tiltedWeight k (19/50) d) k (lN d) b t i
    have h2 := NegativeOrdinaryParameters.block_coefficients h C ab bt td i
    rw [hBs]
    exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩
  have hminor : (∑ i,mixedBlock (Real.sqrt qCap)
      (ps (tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (Bs i).P (Bs i).N)≤
        ∑ i,(Bs i).increment (Real.sqrt qCap) := by
    apply Finset.sum_le_sum
    intro i _
    have hh := (Bs i).minorant (Real.sqrt qCap)
      (by rw [(hc i).1]; exact (domains h i).1.le) (hPi i) (hNi i)
    simpa only [(hc i).1,(hc i).2] using hh
  have henv := CoreENegativeEnvelope.mixed_sum_lower h hb ⟨he,hbud.1⟩
    (fun i => (Bs i).P) (fun i => (Bs i).N) hP hN hbud.2.1 hbud.2.2.2
  have hcharge := charge_lower hC hcore
    (show eTotal C de eh∈Icc 0 frameCap from ⟨he,by linarith [hbud.1,h.angle.1]⟩)
  rw [CoreEStress.increment_eq C hab hbt htd,← hBs]
  linarith

theorem TD_B_upper {d : ℝ} (hd : d∈Icc 0 frameCap) : cN d≤26/25 := by
  have hh := (PositiveOrdinaryParameters.familyN hd).B_upper
  linarith

theorem BT_B_upper {d s : ℝ} (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 (9/100)) :
    cN d/Real.cos s≤26/25 := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x := s)
  have hs2 := pow_le_pow_left₀ hs.1 hs.2 2
  have hc : 19919/20000≤Real.cos s := by nlinarith
  have hcp : 0<Real.cos s := by linarith
  apply (div_le_iff₀ hcp).2
  have hh := (PositiveOrdinaryParameters.familyN hd).B_upper
  linarith

theorem TD_lower {C : SignedCycle} {q s : ℝ} {ab de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap)
    (hd : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 (3/10))
    (hT : delta C.theta T= -s) (he : 0≤eTotal C de eh) :
    CoreENegativeEnvelope.lower (delta C.theta G)≤lambdaN (delta C.theta G)*s+
      CoreEStress.increment C ab 2 2 de eh (tiltedWeight k (19/50) (delta C.theta G))
        k (lN (delta C.theta G)) (cN (delta C.theta G))
        (cN (delta C.theta G)/Real.cos s) (Real.sqrt qCap)+charge C de eh := by
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hd.1
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith [hd.1] : -delta C.theta G≤0)
  have hPT : positivePart (delta C.theta T)=0 := by
    rw [hT]
    exact max_eq_right (by linarith [hs.1] : -s≤0)
  have hNT : negativePart (delta C.theta T)=s := by
    rw [hT]
    simpa [negativePart] using max_eq_left hs.1
  exact actual_lower hC hcore hab (Or.inl rfl) (Or.inr rfl) hde heh hvar
    (by simp [hPG,hPT]) (by simp [hNG,hNT]) he (familyTD hd hs) (TD_B_upper hd)

theorem BT_lower {C : SignedCycle} {q s : ℝ} {ab de eh : Fin 4}
    (hC : C.Necessary q) (hcore : (C.point E).Core)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hvar : positiveVariation C.theta≤frameCap)
    (hd : delta C.theta G∈Icc 0 frameCap) (hs : s∈Icc 0 (9/100))
    (hB : delta C.theta B= -s) (he : 0≤eTotal C de eh) :
    CoreENegativeEnvelope.lower (delta C.theta G)≤lambdaN (delta C.theta G)*s+
      CoreEStress.increment C ab 3 0 de eh (tiltedWeight k (19/50) (delta C.theta G))
        k (lN (delta C.theta G)) (cN (delta C.theta G)/Real.cos s)
        (cN (delta C.theta G)) (Real.sqrt qCap)+charge C de eh := by
  have hPG : positivePart (delta C.theta G)=delta C.theta G := max_eq_left hd.1
  have hNG : negativePart (delta C.theta G)=0 :=
    max_eq_right (by linarith [hd.1] : -delta C.theta G≤0)
  have hPB : positivePart (delta C.theta B)=0 := by
    rw [hB]
    exact max_eq_right (by linarith [hs.1] : -s≤0)
  have hNB : negativePart (delta C.theta B)=s := by
    rw [hB]
    simpa [negativePart] using max_eq_left hs.1
  exact actual_lower hC hcore hab (Or.inr rfl) (Or.inl rfl) hde heh hvar
    (by simp [hPG,hPB]) (by simp [hNG,hNB]) he (familyBT hd hs) (BT_B_upper hd hs)

end SquaresInCircles.Eight.CoreENegativeBlocks
end
end
end

section
/-!
## Positive GA with core E and nonnegative signed E-primary total

The three owner regimes of a nonnegative T (`secondary_T_false`, `positive_TD_false`,
`positive_BT_false`) are excluded directly from the original weak witnesses. Either normal owner
is allowed on both E edges, and each E angle may have either sign; the only assumption on the E
angles is that the sum of the retained primary errors is nonnegative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CoreEPositiveExclusion
open Candidate PositiveStressCoefficients SecondaryEStress PositivePrimaryBaselines
open PositiveOrdinaryParameters ActualOrdinaryBlocks ActualCoreEBlocks

theorem P_strict {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveSplitComparison.familyPBaseline d+
      CoreEOrdinaryEnvelope.lower d (lP d) := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hV := hh.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hV
  have hE := hh.2.2.1
  have hmin := lt_min (by linarith : -PositiveSplitComparison.familyPBaseline d<
      OrdinaryAngleConcavity.V (Real.sqrt qCap) (lP d) k d)
    (by linarith : -PositiveSplitComparison.familyPBaseline d<
      PositiveScalarTransfer.J (frameCap-d)+lP d-87/1250)
  dsimp [CoreEOrdinaryEnvelope.lower]
  linarith

theorem N_strict {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveScalarTransfer.BN d+CoreEOrdinaryEnvelope.lower d (lN d) := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hV := hh.2.2.2.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hV
  have hE := hh.2.2.2.2.2.1
  have hmin := lt_min (by linarith : -PositiveScalarTransfer.BN d<
      OrdinaryAngleConcavity.V (Real.sqrt qCap) (lN d) k d)
    (by linarith : -PositiveScalarTransfer.BN d<
      PositiveScalarTransfer.J (frameCap-d)+lN d-87/1250)
  dsimp [CoreEOrdinaryEnvelope.lower]
  linarith

theorem secondary_T_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i)) : False := by
  let d : ℝ := delta C.theta G
  have hb := ActualCoreEBlocks.block_budgets hab (Or.inl rfl) (Or.inl rfl)
    hde heh 0 0 0 0 0 hvar hG
    (by intro h; norm_num at h) (by intro h; norm_num at h) he
  have hd : d∈Icc 0 frameCap := by simpa [removed,d] using hb.1
  have hp := familyN hd
  have hinc := CoreEOrdinaryEnvelope.actual_lower hC hcore hab (Or.inl rfl)
    (Or.inl rfl) hde heh hvar hG (by intro h; norm_num at h)
    (by intro h; norm_num at h) he
    (by simpa [removed,d] using hp) (CoreEOrdinaryEnvelope.coefficient_intervals hd).2
  have hc := coefficient_bounds hd
  have hnec := CoreEStress.secondary_necessary (k:=k) (l:=lN d) (c:=cN d) (η:=19/50)
    hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hc.2.2.1])
    (by have hh := hc.2.2.2.2.1; norm_num [k] at hh; linarith)
    (by norm_num : (0:ℝ)≤19/50) hG hf
  have hstrict := N_strict hd
  have heq : PositiveScalarTransfer.BN d=
      secondaryBaseline (Real.sqrt qCap) k (lN d) (cN d) (19/50) d := rfl
  rw [heq] at hstrict
  simp only [removed,show (2:Fin 4)≠3 by decide,show (0:Fin 4)≠2 by decide,
    ite_false,add_zero] at hinc
  dsimp [d] at hinc hstrict
  linarith

theorem positive_TD_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hT : 0≤delta C.theta T) (he : 0≤eTotal C de eh)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let x : ℝ := delta C.theta G
  let z : ℝ := delta C.theta T
  let d : ℝ := x+z
  have hb := ActualCoreEBlocks.block_budgets hab (Or.inl rfl) (Or.inr rfl)
    hde heh 0 0 0 0 0 hvar hG (by intro h; norm_num at h) (by intro _; exact hT) he
  have hd : d∈Icc 0 frameCap := by simpa [removed,d,x,z] using hb.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hT,by dsimp [d,x,z]; linarith⟩
  have hp := familyP_td hd hx hz
  have hinc := CoreEOrdinaryEnvelope.actual_lower hC hcore hab (Or.inl rfl)
    (Or.inr rfl) hde heh hvar hG (by intro h; norm_num at h)
    (by intro _; exact hT) he (by simpa [removed,d,x,z] using hp)
    (CoreEOrdinaryEnvelope.coefficient_intervals hd).1
  have hc := coefficient_bounds hd
  have hnec := CoreEStress.td_necessary (k:=k) (l:=lP d) (η:=etaP d) hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hc.1])
    (by linarith [hc.2.2.2.2.2.2.1]) hG hT hf
  have hbase := PositiveSplitConcavity.tdBaseline_ge_familyP hd hG hT
    (show delta C.theta G+delta C.theta T=d by rfl)
  have hstrict := P_strict hd
  have hdEq : removed C 2 2=d := by simp [removed,d,x,z]
  rw [hdEq] at hinc
  linarith

theorem positive_BT_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (hB : 0≤delta C.theta B) (he : 0≤eTotal C de eh)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  let x : ℝ := delta C.theta G
  let z : ℝ := delta C.theta B
  let d : ℝ := x+z
  have hb := ActualCoreEBlocks.block_budgets hab (Or.inr rfl) (Or.inl rfl)
    hde heh 0 0 0 0 0 hvar hG (by intro _; exact hB) (by intro h; norm_num at h) he
  have hd : d∈Icc 0 frameCap := by simpa [removed,d,x,z] using hb.1
  have hx : x∈Icc 0 d := ⟨hG,by dsimp [d,x,z]; linarith⟩
  have hz : z∈Icc 0 d := ⟨hB,by dsimp [d,x,z]; linarith⟩
  have hp := familyP_bt hd hx hz
  have hinc := CoreEOrdinaryEnvelope.actual_lower hC hcore hab (Or.inr rfl)
    (Or.inl rfl) hde heh hvar hG (by intro _; exact hB)
    (by intro h; norm_num at h) he (by simpa [removed,d,x,z] using hp)
    (CoreEOrdinaryEnvelope.coefficient_intervals hd).1
  have hc := coefficient_bounds hd
  have hnec := CoreEStress.bt_necessary (k:=k) (l:=lP d) (η:=etaP d) hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hc.1])
    (by linarith [hc.2.2.2.2.2.2.1]) hG hB hf
  have hbase := PositiveSplitConcavity.btBaseline_ge_familyP hd hG hB
    (show delta C.theta G+delta C.theta B=d by rfl)
  have hstrict := P_strict hd
  have hdEq : removed C 3 0=d := by simp [removed,d,x,z]
  rw [hdEq] at hinc
  linarith

end SquaresInCircles.Eight.CoreEPositiveExclusion
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CoreENegativeExclusion
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity PositiveStressCoefficients
open SecondaryEStress PositivePrimaryBaselines ActualCoreEBlocks
open NegativeSecondaryEExclusion (BT_contact TD_contact)

theorem scalar_positive {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0<PositiveScalarTransfer.BN d+CoreENegativeEnvelope.lower d := by
  have hh := PositiveScalarTransfer.seven_scalar_bounds hd
  have hV := hh.2.2.2.1
  rw [PositiveSecondaryEExclusion.scalar_V_eq] at hV
  have hL := hh.2.2.2.2.1
  have hE := hh.2.2.2.2.2.1
  have hET := hh.2.2.2.2.2.2
  have hz : -PositiveScalarTransfer.BN d<CoreENegativeEnvelope.zeroLower d :=
    lt_min (by linarith) (by linarith)
  have he : -PositiveScalarTransfer.BN d<CoreENegativeEnvelope.farLower d :=
    lt_min (by linarith) (by linarith)
  have hm := lt_min hz he
  dsimp [CoreENegativeEnvelope.lower]
  linarith

theorem flat_negative_TD_false {C : SignedCycle} {q s : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hs : s∈Ioc 0 (3/10)) (hT : delta C.theta T= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  have hd : delta C.theta G∈Icc 0 frameCap :=
    ⟨hG,(le_abs_self _).trans (hC.spread (next G) G)⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := PositiveOrdinaryParameters.familyN hd
  have hc : 0<cN (delta C.theta G) := by
    have hh := hb.B_lower
    norm_num [k] at hh
    linarith
  have hnec := CoreENegativeStress.negative_TD_necessary (k := k) (l := lN (delta C.theta G))
    (c := cN (delta C.theta G)) (η := 19/50) hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hb.ell_lower]) hc (by norm_num : (0:ℝ)≤19/50)
    hG hs' hT hflat hf
  have hinc := CoreENegativeBlocks.TD_lower hC hcore hab hde heh hvar hd
    (Ioc_subset_Icc_self hs) hT he
  have hgain := PositiveSecantGain.negative_TD_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd (show s∈Ioc 0 frameCap from ⟨hs.1,hs'.2⟩)
  have hstrict := scalar_positive hd
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN (delta C.theta G)) (cN (delta C.theta G))
    (19/50) (delta C.theta G)+CoreENegativeEnvelope.lower (delta C.theta G) at hstrict
  linarith

theorem flat_negative_BT_false {C : SignedCycle} {q s : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hs : s∈Ioc 0 (9/100)) (hB : delta C.theta B= -s) (hflat : (C.point T).a=7/12)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  have hd : delta C.theta G∈Icc 0 frameCap :=
    ⟨hG,(le_abs_self _).trans (hC.spread (next G) G)⟩
  have hs' : s∈Icc 0 frameCap := ⟨hs.1.le,by dsimp [frameCap]; linarith [hs.2]⟩
  have hb := PositiveOrdinaryParameters.familyN hd
  have hc : 0<cN (delta C.theta G) := by
    have hh := hb.B_lower
    norm_num [k] at hh
    linarith
  have hnec := CoreENegativeStress.negative_BT_necessary (k := k) (l := lN (delta C.theta G))
    (c := cN (delta C.theta G)) (η := 19/50) hq hC hn hab hde heh
    (by norm_num [k]) (by linarith [hb.ell_lower]) hc (by norm_num : (0:ℝ)≤19/50)
    hG hs' hB hflat hf
  have hinc := CoreENegativeBlocks.BT_lower hC hcore hab hde heh hvar hd
    (Ioc_subset_Icc_self hs) hB he
  have hgain := ShortSecantGain.negative_BT_gain (q := qCap)
    (by norm_num [qCap]) le_rfl hd hs
  have hstrict := scalar_positive hd
  change 0<secondaryBaseline (Real.sqrt qCap) k (lN (delta C.theta G)) (cN (delta C.theta G))
    (19/50) (delta C.theta G)+CoreENegativeEnvelope.lower (delta C.theta G) at hstrict
  linarith

theorem reselect_TD {C : SignedCycle} {ab td de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 td de eh i)) (hT : C.Feasible T 0) :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  fin_cases i
  · have h := hf 0
    change C.Feasible 0 2 at h
    exact h
  · have h := hf 1
    change C.Feasible 1 1 at h
    exact h
  · have h := hf 2
    change C.Feasible 2 ab at h
    exact h
  · have h := hf 3
    change C.Feasible 3 2 at h
    exact h
  · exact hT
  · have h := hf 5
    change C.Feasible 5 de at h
    exact h
  · have h := hf 6
    change C.Feasible 6 eh at h
    exact h

theorem reselect_BT {C : SignedCycle} {ab bt de eh : Fin 4}
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt 0 de eh i)) (hB : C.Feasible B 2) :
    ∀ i,C.Feasible i (CoreEStress.owners ab 2 0 de eh i) := by
  intro i
  fin_cases i
  · have h := hf 0
    change C.Feasible 0 2 at h
    exact h
  · have h := hf 1
    change C.Feasible 1 1 at h
    exact h
  · have h := hf 2
    change C.Feasible 2 ab at h
    exact h
  · exact hB
  · have h := hf 4
    change C.Feasible 4 0 at h
    exact h
  · have h := hf 5
    change C.Feasible 5 de at h
    exact h
  · have h := hf 6
    change C.Feasible 6 eh at h
    exact h

theorem negative_TD_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hTb : (C.point T).Boundary q) (hT : delta C.theta T<0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 2 2 de eh i)) : False := by
  let s : ℝ := -delta C.theta T
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next T) T)⟩
  have hTs : delta C.theta T= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 2 :=
    (BT_contact C 2).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) (-s) 2 := by
    rw [← hTs]
    exact (TD_contact C 2).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hent := NegativeTEntry.negative_TD_entry (hC.sorted B) (hC.sorted T) (hC.sorted D)
    (hC.contained B) hTb (hC.contained D) (hC.core T) (hC.core D)
    hq hn.D_nonpos hs hBT hTD
  rcases hent with hsecondary | ⟨hcoreT,hflat,hyT,hyu,hshort⟩
  · have hsecondary' : C.Feasible T 0 := (TD_contact C 0).2 (by simpa [hTs] using hsecondary)
    exact CoreEPositiveExclusion.secondary_T_false hq hC hn hcore hvar hab hde heh
      hG he (reselect_TD hf hsecondary')
  · exact flat_negative_TD_false hq hC hn hcore hvar hab hde heh hG he
      ⟨hs.1,hshort.le⟩ hTs hflat hf

theorem negative_BT_aligned_false {C : SignedCycle} {q : ℝ} {ab de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hTb : (C.point T).Boundary q) (hB : delta C.theta B<0) (halign : delta C.theta T=0)
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab 3 0 de eh i)) : False := by
  by_cases hsecondary : C.Feasible B 2
  · exact CoreEPositiveExclusion.secondary_T_false hq hC hn hcore hvar hab hde heh
      hG he (reselect_BT hf hsecondary)
  let s : ℝ := -delta C.theta B
  have hs : s∈Ioc 0 frameCap :=
    ⟨by dsimp [s]; linarith,(neg_le_abs _).trans (hC.spread (next B) B)⟩
  have hBs : delta C.theta B= -s := by dsimp [s]; ring
  have hBT : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    rw [← hBs]
    exact (BT_contact C 3).1 (by simpa [CoreEStress.owners,B] using hf B)
  have hTD : zeroFeasible (C.point T) (C.point D) 0 0 := by
    rw [← halign]
    exact (TD_contact C 0).1 (by simpa [CoreEStress.owners,T] using hf T)
  have hnot : ¬quarterFeasible (C.point B) (C.point T) (-s) 2 := by
    intro hh
    exact hsecondary ((BT_contact C 2).2 (by simpa [hBs] using hh))
  obtain ⟨hcoreT,hflat,hyT,hyu,hshort⟩ := NegativeTEntry.negative_BT_aligned_entry
    (hC.sorted B) (hC.sorted T) (hC.sorted D) (hC.contained B) hTb (hC.contained D)
    (hC.core D) hq hn.B_nonpos hn.D_nonpos hs hBT hTD hnot
  exact flat_negative_BT_false hq hC hn hcore hvar hab hde heh hG he
    ⟨hs.1,hshort.le⟩ hBs hflat hf

/-- All preprocessed T owners at a nonnegative signed E-primary total. Negative BT uses only the
TD alignment given by the T-pair preprocessing. -/
theorem preprocessed_core_E_false {C : SignedCycle} {q : ℝ} {ab bt td de eh : Fin 4}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (hcore : (C.point E).Core)
    (hvar : positiveVariation C.theta≤frameCap)
    (hab : ab=0 ∨ ab=2) (hde : de=2 ∨ de=3) (heh : eh=0 ∨ eh=1)
    (hG : 0≤delta C.theta G) (he : 0≤eTotal C de eh)
    (hTb : (C.point T).Boundary q)
    (hT : (bt=2 ∧ td=0) ∨ (bt=2 ∧ td=2) ∨
      (bt=3 ∧ td=0 ∧ (delta C.theta B<0 → delta C.theta T=0)))
    (hf : ∀ i,C.Feasible i (CoreEStress.owners ab bt td de eh i)) : False := by
  rcases hT with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl,halign⟩
  · exact CoreEPositiveExclusion.secondary_T_false hq hC hn hcore hvar hab hde heh hG he hf
  · by_cases ht : 0≤delta C.theta T
    · exact CoreEPositiveExclusion.positive_TD_false hq hC hn hcore hvar hab hde heh hG ht he hf
    · exact negative_TD_false hq hC hn hcore hvar hab hde heh hG he hTb (lt_of_not_ge ht) hf
  · by_cases hb : 0≤delta C.theta B
    · exact CoreEPositiveExclusion.positive_BT_false hq hC hn hcore hvar hab hde heh hG hb he hf
    · have hb' : delta C.theta B<0 := lt_of_not_ge hb
      exact negative_BT_aligned_false hq hC hn hcore hvar hab hde heh hG he hTb hb'
        (halign hb') hf

end SquaresInCircles.Eight.CoreENegativeExclusion
end
end
end
