module

public import SquaresInCircles.Eight.TableFree.NegativeOrdinaryParameters
public import SquaresInCircles.Eight.TableFree.RemovedPrimaryConcentration

/-!
# Complete ordinary envelope with one negative primary removed

Uncompiled source draft. This proves the full four-block inequality for
the actual negative-T coefficients. Both signs are allowed in every
ordinary block. The two removed primary angles remain independent, and
the result includes the junction where their imbalance changes sign.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.NegativeOrdinaryEnvelope
open PositiveAngularEnvelope PositivePrimaryBaselines PositiveStressCoefficients
open OrdinaryAngleConcavity OrdinaryAngleConcentration OrdinaryPositiveEnvelope
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope PositiveOrdinaryEnvelope
open NegativeOrdinaryParameters OrdinaryShortSecantGrowth RemovedPrimaryConcentration

theorem affine_concave (a b l u : ℝ) :
    ConcaveOn ℝ (Icc l u) (fun x => a*x+b) := by
  refine ⟨convex_Icc l u,?_⟩
  intro x hx y hy α β hα hβ hsum
  simp only [smul_eq_mul]
  have hc : (α+β)*b=b := by rw [hsum,one_mul]
  nlinarith only [hc]

theorem gain_junction {d s : ℝ} (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d) :
    min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)≤
      lambdaN d*s+V (Real.sqrt qCap) (lN d) k (d-s) := by
  have hb := PositiveOrdinaryParameters.familyN hd
  have hV := V_concave (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
    (by linarith [hb.ell_lower] : 0<lN d) hb.ell_upper.le
    (by norm_num [k]; linarith [hb.ell_lower] : k≤2*lN d)
  have hc := concave_affine_argument hV (a := -1) (b := d) (l := 0) (u := d)
    (fun x hx => ⟨by linarith [hx.2],by linarith [hd.2,hx.1]⟩)
  have hl := affine_concave (lambdaN d) 0 0 d
  have hconc : ConcaveOn ℝ (Icc 0 d)
      (fun x => lambdaN d*x+V (Real.sqrt qCap) (lN d) k (d-x)) := by
    convert hl.add hc using 1
    funext x
    congr 1 <;> ring
  have hh := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 d from ⟨le_rfl,hd.1⟩)
    (show d∈Icc 0 d from ⟨hd.1,le_rfl⟩) hs
  simpa only [sub_zero,sub_self,mul_zero,zero_add,V_zero,add_zero] using hh

theorem low_U_lower {d s b t z : ℝ} (h : Bounds d s b t) (hd : d≤3/10)
    (i : Fin 4) (hz : z∈Icc 0 frameCap) :
    -(571/1000)*z≤U (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) z := by
  have hi := domains h i
  have hlo := (low_domains h hd i).2
  have hc := short_cos h.short
  have hq0 : 0≤qs b t i := (hi.1.trans_le hi.2.1).le
  have hqcos := (le_div_iff₀ hc.2.1).1 hlo
  have hqmul := mul_le_mul_of_nonneg_left hc.1 hq0
  have hcoef : (109/200)*qs b t i≤571/1000 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hcoef hz.1
  have hU := U_lower (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hi.1 hi.2.1 hi.2.2.1 hz
  nlinarith

theorem low_V_lower {d s b t z : ℝ} (h : Bounds d s b t) (hd : d≤3/10)
    (i : Fin 4) (hz : z∈Icc 0 frameCap) :
    (87/70)*lP d*z≤V (Real.sqrt qCap)
      (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) z := by
  have hi := domains h i
  have hv := V_chord_lower hi.1 hi.2.1 hi.2.2.1 hz
  have hm := mul_le_mul_of_nonneg_right (low_domains h hd i).1 hz.1
  nlinarith

theorem low_constants {d : ℝ} (hd : d∈Icc 0 (3/10)) :
    571/1000≤(87/70)*lP d ∧ (87/70)*lP d≤lambdaN d ∧
    571/1000≤lambdaN d ∧
    0<(87/100)*lP d-(26/25)*d-(571/1000)*(frameCap-d) := by
  have hd2 : d^2≤(3/10)*d := by nlinarith [hd.1,hd.2]
  have hd2' := pow_le_pow_left₀ hd.1 hd.2 2
  dsimp [lP,lambdaN,frameCap]
  constructor
  · nlinarith
  constructor
  · nlinarith [sq_nonneg d]
  constructor
  · linarith [hd.1]
  · nlinarith [hd.1,hd.2]

theorem low_separated {d s b t : ℝ} (h : Bounds d s b t) (hd : d≤3/10)
    (i j : Fin 4) :
    V (Real.sqrt qCap) (lN d) k d≤lambdaN d*s+
      U (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (frameCap-d)+
      V (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j) (frameCap-s) := by
  have hU := low_U_lower h hd i
    (show frameCap-d∈Icc 0 frameCap from ⟨by linarith [h.angle.2],by linarith [h.angle.1]⟩)
  have hV := low_V_lower h hd j
    (show frameCap-s∈Icc 0 frameCap from ⟨by dsimp [frameCap]; linarith [h.short.2],
      by linarith [h.short.1]⟩)
  have hc := low_constants ⟨h.angle.1,hd⟩
  have hg := mul_le_mul_of_nonneg_right hc.2.1 h.short.1
  have htarget := target_low_upper (PositiveOrdinaryParameters.familyN h.angle) hd
  dsimp [frameCap] at *
  nlinarith

theorem high_separated {d s b t : ℝ} (h : Bounds d s b t)
    (hd : 3/10≤d) (hsd : s≤d) (i j : Fin 4) :
    V (Real.sqrt qCap) (lN d) k (d-s)≤
      U (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (frameCap-d)+
      V (Real.sqrt qCap) (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t j) (qs b t j) (frameCap-s) := by
  have hi := domains h i
  have hj := domains h j
  have ha : frameCap-d∈Icc 0 frameCap := ⟨by linarith [h.angle.2],by linarith [h.angle.1]⟩
  have hw : d-s∈Icc 0 (frameCap-s) := ⟨by linarith,by linarith [h.angle.2]⟩
  have hu : frameCap-s∈Icc 0 (frameCap-s) :=
    ⟨by dsimp [frameCap]; linarith [h.short.2],le_rfl⟩
  have hU := U_lower (Real.sqrt_nonneg qCap)
    (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hi.1 hi.2.1 hi.2.2.1 ha
  have hV := shortened_growth hj.1 hj.2.1 (high_domains h hd j) h.short.1 hw hu
    (by linarith [h.angle.2])
  have hsingle := single_negative_lower h hsd ⟨hw.1,le_rfl⟩ j
  have hqi := mul_le_mul_of_nonneg_left hi.2.2.2.2.2.1 (by norm_num : (0:ℝ)≤109/200)
  have hqj := mul_le_mul_of_nonneg_left hj.2.2.2.2.1
    (show 0≤2/3+s/4 by linarith [h.short.1])
  have hcoef : (109/200)*qs b t i≤(2/3+s/4)*qs b t j := by
    have hc := secant_compensation h.short
    rw [mul_div_assoc] at hc
    linarith only [hqi,hqj,hc]
  have hm := mul_le_mul_of_nonneg_right hcoef ha.1
  linarith

theorem mixed_sum_lower {d s b t : ℝ} (h : Bounds d s b t)
    (P N : Fin 4 → ℝ) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hbudget : (∑ i,P i)≤frameCap-d)
    (hbalance : (∑ i,N i)=d-s+∑ i,P i) :
    min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)≤
      lambdaN d*s+∑ i,mixedBlock (Real.sqrt qCap)
        (ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t i) (qs b t i) (P i) (N i) := by
  classical
  let p := ps (SecondaryEStress.tiltedWeight k (19/50) d) (lN d) t
  let q := qs b t
  let L := min (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)
  have hR := Real.sqrt_nonneg qCap
  have hQ := (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
  have hp (i : Fin 4) : 0<p i := (domains h i).1
  have hpq (i : Fin 4) : p i≤q i := (domains h i).2.1
  have hqp (i : Fin 4) : q i≤2*p i := (domains h i).2.2.1
  by_cases hsd : s≤d
  · obtain ⟨i,j,hconc⟩ := negative_concentration (Real.sqrt qCap) p q P N
      hR hQ hp hpq hqp hP hN h.angle ⟨h.short.1,hsd⟩ hbudget hbalance
    have hjunction := gain_junction h.angle ⟨h.short.1,hsd⟩
    have hpure : L≤lambdaN d*s+V (Real.sqrt qCap) (p j) (q j) (d-s) := by
      have hh := single_negative_lower h hsd ⟨by linarith,le_rfl⟩ j
      dsimp [L]
      linarith
    have hsat : L≤lambdaN d*s+
        (if i=j then mixedBlock (Real.sqrt qCap) (p i) (q i) (frameCap-d) (frameCap-s)
         else U (Real.sqrt qCap) (p i) (q i) (frameCap-d)+
           V (Real.sqrt qCap) (p j) (q j) (frameCap-s)) := by
      by_cases hij : i=j
      · rw [if_pos hij]
        have hi := domains h i
        have hs := RelaxedSameBlock.negative_surplus (R := Real.sqrt qCap)
          ((hp i).trans_le (hpq i)).le hi.2.2.2.1 h.angle ⟨h.short.1,hsd⟩
        have hsingle := single_negative_lower h hsd ⟨by linarith,le_rfl⟩ i
        dsimp [L,p,q] at *
        linarith
      · rw [if_neg hij]
        by_cases hd : d≤3/10
        · have hh := low_separated h hd i j
          have hmin := min_le_left (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)
          dsimp [L,p,q] at *
          linarith
        · have hh := high_separated h (lt_of_not_ge hd).le hsd i j
          dsimp [L,p,q] at *
          linarith
    have hmin : L-lambdaN d*s≤ min (V (Real.sqrt qCap) (p j) (q j) (d-s))
        (if i=j then mixedBlock (Real.sqrt qCap) (p i) (q i) (frameCap-d) (frameCap-s)
         else U (Real.sqrt qCap) (p i) (q i) (frameCap-d)+
           V (Real.sqrt qCap) (p j) (q j) (frameCap-s)) :=
      le_min (by linarith) (by linarith)
    have hh := hmin.trans hconc
    change L≤lambdaN d*s+_
    linarith
  · have hds : d≤ s := (lt_of_not_ge hsd).le
    have hd : d≤3/10 := hds.trans h.short.2
    have hPt : (∑ i,P i)≤frameCap := by linarith [h.angle.1]
    have hNt : (∑ i,N i)≤frameCap := by rw [hbalance]; linarith [h.short.1]
    have hP0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hP i)
    have hN0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hN i)
    obtain ⟨i,j,hconc⟩ := both_signs_concentrate (Real.sqrt qCap) p q P N
      hR hQ hp hpq hqp hP hN hPt hNt
    have hconstants := low_constants ⟨h.angle.1,hd⟩
    have hlambda : (571/1000)*(s-d)≤lambdaN d*(s-d) :=
      mul_le_mul_of_nonneg_right hconstants.2.2.1 (by linarith)
    have hlower : -(571/1000)*(s-d)≤
        (if i=j then mixedBlock (Real.sqrt qCap) (p i) (q i) (∑ k,P k) (∑ k,N k)
         else U (Real.sqrt qCap) (p i) (q i) (∑ k,P k)+
           V (Real.sqrt qCap) (p j) (q j) (∑ k,N k)) := by
      by_cases hij : i=j
      · rw [if_pos hij]
        have hi := domains h i
        have hq0 := ((hp i).trans_le (hpq i)).le
        have hratio : (29/50)*q i≤p i := by
          have hr : 29/50≤ratio d-31/10000 := by dsimp [ratio]; linarith [h.angle.1]
          exact (mul_le_mul_of_nonneg_right hr hq0).trans hi.2.2.2.1
        have hs := RelaxedSameBlock.positive_surplus (R := Real.sqrt qCap) hq0 hratio
          ⟨hP0,hPt⟩ (show (∑ k,N k)∈Icc 0 (∑ k,P k) from ⟨hN0,by linarith⟩)
        have he : (∑ k,P k)-(∑ k,N k)=s-d := by linarith
        rw [he] at hs
        have hU := low_U_lower h hd i
          (show s-d∈Icc 0 frameCap from ⟨by linarith,by linarith [h.short.2,h.angle.1,
            show frameCap=(7/10 : ℝ) from rfl]⟩)
        exact hU.trans hs
      · rw [if_neg hij]
        have hU := low_U_lower h hd i ⟨hP0,hPt⟩
        have hV := low_V_lower h hd j ⟨hN0,hNt⟩
        have hm := mul_le_mul_of_nonneg_right hconstants.1 hN0
        dsimp [p,q] at *
        nlinarith
    have hactual := hlower.trans hconc
    have hmin := min_le_right (V (Real.sqrt qCap) (lN d) k d) (lambdaN d*d)
    dsimp [p,q] at *
    nlinarith

end SquaresInCircles.Eight.TableFree.NegativeOrdinaryEnvelope
