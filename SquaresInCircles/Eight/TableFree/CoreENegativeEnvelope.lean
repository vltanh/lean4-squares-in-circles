module

public import SquaresInCircles.Eight.TableFree.CoreEOrdinaryEnvelope
public import SquaresInCircles.Eight.TableFree.NegativeOrdinaryBlocks

/-!
# Nonnegative E charge with a genuine negative T primary

Uncompiled source draft. The negative T magnitude is retained in both
ordinary variation caps and in its actual secant coefficient. For a
nonnegative ordinary imbalance, concavity leaves E-total zero, the far
endpoint, and the pure-sign junction. For a negative imbalance the
existing low-angle ordinary bounds absorb the entire E charge directly.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.CoreENegativeEnvelope
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
      simp only [f,if_pos hij]
      congr 1
      ring
    · have hc := (concave_affine_argument (U_concave hR hQ hi.1 hi.2.1 hi.2.2.1)
        (a := -1) (b := frameCap-d) harg).add_const
          (V (Real.sqrt qCap) (p j) (q j) (frameCap-s))
      convert hc using 1
      funext u
      simp only [f,if_neg hij]
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
    · rw [if_pos hij]
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
    · rw [if_neg hij]
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

end SquaresInCircles.Eight.TableFree.CoreENegativeEnvelope
