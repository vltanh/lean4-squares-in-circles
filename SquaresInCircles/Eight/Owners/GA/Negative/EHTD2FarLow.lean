module

public import SquaresInCircles.Eight.Frames.Ordinary.ShortSecantGrowth
public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongEndpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3LowScalar
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSecant
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSeparated
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSlopes
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2FarLowSplit
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Balanced
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeEndpoints
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSplit
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Source

/-!
# Eight squares: complete far-low four-block scalar exclusion

Every
pure alternative is proved for both surplus signs. Every saturated
ordinary same-block alternative retains its two masses until the charged
comparison is applied. The exceptional D block is treated as separated,
even when both signs lie on that same original DE2 singleton. No owner,
signed-mass budget, or continuous concentration alternative is omitted.
-/

section
/-!
## Positivity for every longer-E negative-A magnitude with BT3

The four ordinary coefficients remain
fixed while s varies. The common negative-A gain and the negative
ordinary increment are concave, so zero and min(e,19/50) suffice.
The small-total comparison retains the exact s/600 gain reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem upper_endpoint_positive (r : NonnegativeTotals.Region) (i : Fin 3)
    {x y : ℝ} (hd : NonnegativeTotals.Explicit.Domain r x y) :
    0<scalar (NonnegativeTotals.Explicit.k r x y) (NonnegativeTotals.Explicit.l r x y)
      (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.theta r x y)
      (NonnegativeTotals.Explicit.e r x y) (min (NonnegativeTotals.Explicit.e r x y) (19/50)) i := by
  cases r with
  | triangle =>
    by_cases he : y≤19/50
    · have hh := Analytic.endpoint_positive .TE i hd
      simpa only [Analytic.endpoint,Explicit.k,NegativeA.LongE.Explicit.k,Explicit.l,NegativeA.LongE.Explicit.l,Explicit.m,NegativeA.LongE.Explicit.c,Explicit.z,NegativeA.LongE.Explicit.z,Explicit.e,NegativeA.LongE.Explicit.e,
        Explicit.s,NegativeA.LongE.Explicit.s,Explicit.baseRegion,NegativeA.LongE.Explicit.baseRegion,Explicit.baseY,NegativeA.LongE.Explicit.baseY,NonnegativeTotals.Explicit.e,min_eq_left he] using hh
    · have hdom : Explicit.Domain .TC x (y-19/50) :=
        ⟨hd.1,by linarith,by linarith [hd.2.2]⟩
      have hy : Explicit.baseY .TC x (y-19/50)=y := by dsimp [Explicit.baseY,NegativeA.LongE.Explicit.baseY]; ring
      have hh := Analytic.endpoint_positive .TC i hdom
      simpa only [Analytic.endpoint,Explicit.k,NegativeA.LongE.Explicit.k,Explicit.l,NegativeA.LongE.Explicit.l,Explicit.m,NegativeA.LongE.Explicit.c,Explicit.z,NegativeA.LongE.Explicit.z,Explicit.e,NegativeA.LongE.Explicit.e,
        Explicit.s,NegativeA.LongE.Explicit.s,Explicit.baseRegion,NegativeA.LongE.Explicit.baseRegion,hy,NonnegativeTotals.Explicit.e,min_eq_right (le_of_not_ge he)] using hh
  | rectangle =>
    by_cases he : x+y≤19/50
    · have hdom : Explicit.Domain .RE x y := ⟨hd.1,⟨hd.2.1,by linarith⟩⟩
      have hh := Analytic.endpoint_positive .RE i hdom
      simpa only [Analytic.endpoint,Explicit.k,NegativeA.LongE.Explicit.k,Explicit.l,NegativeA.LongE.Explicit.l,Explicit.m,NegativeA.LongE.Explicit.c,Explicit.z,NegativeA.LongE.Explicit.z,Explicit.e,NegativeA.LongE.Explicit.e,
        Explicit.s,NegativeA.LongE.Explicit.s,Explicit.baseRegion,NegativeA.LongE.Explicit.baseRegion,Explicit.baseY,NegativeA.LongE.Explicit.baseY,NonnegativeTotals.Explicit.e,min_eq_left he] using hh
    · have hdom : Explicit.Domain .RC x (x+y-19/50) :=
        ⟨hd.1,⟨by linarith,by linarith [hd.2.2]⟩⟩
      have hy : Explicit.baseY .RC x (x+y-19/50)=y := by dsimp [Explicit.baseY,NegativeA.LongE.Explicit.baseY]; ring
      have hh := Analytic.endpoint_positive .RC i hdom
      simpa only [Analytic.endpoint,Explicit.k,NegativeA.LongE.Explicit.k,Explicit.l,NegativeA.LongE.Explicit.l,Explicit.m,NegativeA.LongE.Explicit.c,Explicit.z,NegativeA.LongE.Explicit.z,Explicit.e,NegativeA.LongE.Explicit.e,
        Explicit.s,NegativeA.LongE.Explicit.s,Explicit.baseRegion,NegativeA.LongE.Explicit.baseRegion,hy,NonnegativeTotals.Explicit.e,min_eq_right (le_of_not_ge he)] using hh

theorem scalar_concave (r : NonnegativeTotals.Region) (i : Fin 3) {x y : ℝ}
    (hd : NonnegativeTotals.Explicit.Domain r x y) :
    ConcaveOn ℝ (Icc 0 (min (NonnegativeTotals.Explicit.e r x y) (19/50)))
      (fun s => scalar (NonnegativeTotals.Explicit.k r x y) (NonnegativeTotals.Explicit.l r x y)
        (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.theta r x y)
        (NonnegativeTotals.Explicit.e r x y) s i) := by
  have hb := NonnegativeTotals.Explicit.base_bounds r hd
  have hθ := (NonnegativeTotals.Explicit.domains hd).1
  have hE := (NonnegativeTotals.Explicit.domains hd).2.1
  have ht := (NonnegativeTotals.Explicit.domains hd).2.2
  have hθmem : NonnegativeTotals.Explicit.theta r x y∈Icc 0 (NonnegativeTotals.Explicit.theta r x y) :=
    ⟨hθ.1,le_rfl⟩
  have hp := PositiveBT3.Balanced.pair_domain r hd hθmem i.castSucc
  have hcV := V_concave (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1
    (show PositiveBT3.qWeights (NonnegativeTotals.Explicit.k r x y) (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.tilted r x y (NonnegativeTotals.Explicit.theta r x y)) i.castSucc≤
      2*PositiveBT3.pWeights (NonnegativeTotals.Explicit.k r x y) (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.tilted r x y (NonnegativeTotals.Explicit.theta r x y)) i.castSucc by
      linarith [hp.2.2])
  have hcneg : ConcaveOn ℝ (Icc 0 frameCap)
      (fun t => NonnegativeTotals.Analytic.negative (NonnegativeTotals.Explicit.k r x y)
        (NonnegativeTotals.Explicit.l r x y)
        (NonnegativeTotals.Explicit.c r x y) t i) := by
    fin_cases i <;> simpa [NonnegativeTotals.Analytic.negative,
      PositiveBT3.pWeights,PositiveBT3.qWeights] using hcV
  have hcarg := concave_affine_argument (a:=(-1:ℝ))
    (b:=NonnegativeTotals.Explicit.theta r x y+NonnegativeTotals.Explicit.e r x y)
    (l:=0) (u:=min (NonnegativeTotals.Explicit.e r x y) (19/50)) hcneg (by
      intro s hs
      have hse := hs.2.trans (min_le_left _ _)
      dsimp [NonnegativeTotals.Explicit.delta] at ht
      constructor <;> linarith [hθ.1,hs.1,ht.2])
  have hgain := NegativeA.LongE.gain_concave.subset
    (Icc_subset_Icc le_rfl (min_le_right (NonnegativeTotals.Explicit.e r x y) (19/50)))
    (convex_Icc _ _)
  refine ⟨convex_Icc _ _,?_⟩
  intro a ha b hb' u v hu hv huv
  have hG := mul_le_mul_of_nonneg_left (hgain.2 ha hb' hu hv huv) hb.l_positive.le
  have hV := hcarg.2 ha hb' hu hv huv
  simp only [smul_eq_mul] at hG hV ⊢
  have hconst := congrArg (fun t : ℝ => t*
    (PositiveBT3.Analytic.fullBaseline (NonnegativeTotals.Explicit.k r x y)
      (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
      (NonnegativeTotals.Explicit.theta r x y)+
        TwoPositive.ASupport.charge (NonnegativeTotals.Explicit.e r x y))) huv
  dsimp [scalar]
  simp only [neg_one_mul] at hV
  have harg (w : ℝ) : -w+(NonnegativeTotals.Explicit.theta r x y+NonnegativeTotals.Explicit.e r x y)=
      NonnegativeTotals.Explicit.theta r x y+NonnegativeTotals.Explicit.e r x y-w := by ring
  simp only [harg] at hV
  nlinarith only [hG,hV,hconst]

theorem large_scalar_positive (r : NonnegativeTotals.Region) (i : Fin 3)
    {x y s : ℝ} (hd : NonnegativeTotals.Explicit.Domain r x y)
    (hs : s∈Icc 0 (min (NonnegativeTotals.Explicit.e r x y) (19/50))) :
    0<scalar (NonnegativeTotals.Explicit.k r x y) (NonnegativeTotals.Explicit.l r x y)
      (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.theta r x y)
      (NonnegativeTotals.Explicit.e r x y) s i := by
  have hzero : 0<scalar (NonnegativeTotals.Explicit.k r x y) (NonnegativeTotals.Explicit.l r x y)
      (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.theta r x y)
      (NonnegativeTotals.Explicit.e r x y) 0 i := by
    simpa [scalar,PositiveBT3.Analytic.largeEndpoint,PositiveBT3.Analytic.largeScalar,
      NonnegativeTotals.Analytic.aAt,NegativeA.LongE.gain_zero] using
        PositiveBT3.Analytic.T_endpoint_positive r i hd
  exact concave_gt_of_endpoints (f := fun s => scalar (NonnegativeTotals.Explicit.k r x y)
      (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
      (NonnegativeTotals.Explicit.theta r x y) (NonnegativeTotals.Explicit.e r x y) s i)
    (scalar_concave r i hd) ⟨hs.1,hs.2⟩ hzero (upper_endpoint_positive r i hd)

/-- The balanced comparison at an arbitrary remaining total, with the
family fixed at its original z and e. -/
theorem balanced_lower (r : NonnegativeTotals.Region) {x y t : ℝ}
    (hd : NonnegativeTotals.Explicit.Domain r x y) (ht : t∈Icc 0 frameCap)
    (i j : Fin 4) :
    TwoPositive.balancedEnvelope (NonnegativeTotals.Explicit.k r x y)
      (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y) t≤
    PositiveBT3.endpoint (NonnegativeTotals.Explicit.k r x y)
      (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
      (PositiveBT3.tilted (NonnegativeTotals.Explicit.c r x y)
        (NonnegativeTotals.Explicit.theta r x y)) t i j := by
  have hb := NonnegativeTotals.Explicit.base_bounds r hd
  have hu : NonnegativeTotals.Explicit.theta r x y∈Icc 0 (NonnegativeTotals.Explicit.theta r x y) :=
    ⟨(NonnegativeTotals.Explicit.domains hd).1.1,le_rfl⟩
  have hc := PositiveBT3.Balanced.pair_domain r hd hu
  have hpure (j : Fin 4) :
      TwoPositive.balancedEnvelope (NonnegativeTotals.Explicit.k r x y)
        (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y) t≤
      V R (PositiveBT3.pWeights (NonnegativeTotals.Explicit.k r x y)
          (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
          (NonnegativeTotals.Explicit.tilted r x y (NonnegativeTotals.Explicit.theta r x y)) j)
        (PositiveBT3.qWeights (NonnegativeTotals.Explicit.k r x y)
          (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
          (NonnegativeTotals.Explicit.tilted r x y (NonnegativeTotals.Explicit.theta r x y)) j) t := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
    · exact (min_le_left _ _).trans (NonnegativeTotals.TD0.D_redundant
        ⟨hb.k_lower,by linarith [hb.k_upper]⟩
        (NonnegativeTotals.Explicit.tilted_lower r hd hu).le
        (NonnegativeTotals.Explicit.tilted_upper r hd hu).le ht)
  have htil : PositiveBT3.tilted (NonnegativeTotals.Explicit.c r x y)
      (NonnegativeTotals.Explicit.theta r x y)=
      NonnegativeTotals.Explicit.tilted r x y (NonnegativeTotals.Explicit.theta r x y) := rfl
  rw [htil]
  unfold PositiveBT3.endpoint
  apply le_min (hpure j)
  by_cases hij : i=j
  · subst j
    simp only []
    exact (hpure i).trans (OrdinaryAngleConcentration.M_ge_V (hc i).1.le
      ((hc i).1.trans_le (hc i).2.1).le (by linarith [(hc i).2.2]) ht)
  · simp only [ite_eq_right hij]
    have hlen : 0≤frameCap-t := by linarith [ht.2]
    have hU := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
      (hc i).1 (hc i).2.1 (by linarith [(hc i).1,(hc i).2.2])
      (show frameCap-t∈Icc 0 frameCap from ⟨hlen,by linarith [ht.1]⟩)
    have hV := OrdinaryNegativeSlope.V_growth (hc j).1 (hc j).2.1
      (by linarith [(hc j).2.2]) ht
      (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht.2
    have hi := PositiveBT3.Balanced.scale_bounds r hd hu i
    have hj := PositiveBT3.Balanced.scale_bounds r hd hu j
    have hmargin : 0≤
        (2/3)*PositiveBT3.qWeights (NonnegativeTotals.Explicit.k r x y)
          (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
          (NonnegativeTotals.Explicit.tilted r x y (NonnegativeTotals.Explicit.theta r x y)) j-
        (109/200)*PositiveBT3.qWeights (NonnegativeTotals.Explicit.k r x y)
          (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
          (NonnegativeTotals.Explicit.tilted r x y (NonnegativeTotals.Explicit.theta r x y)) i := by
      have hp := (hc j).1.trans_le (hc j).2.1
      linarith
    rw [show Real.sqrt qCap=R from rfl] at hU hV
    linarith [mul_nonneg hmargin hlen,hpure j]

def concentrationScalar (k l m z e s : ℝ) (i j : Fin 4) : ℝ :=
  PositiveBT3.Analytic.fullBaseline k l m z+l*gain s+TwoPositive.ASupport.charge e+
    PositiveBT3.endpoint k l m (PositiveBT3.tilted m z) (z+e-s) i j

theorem large_concentration_positive (r : NonnegativeTotals.Region) {x y s : ℝ}
    (hd : NonnegativeTotals.Explicit.Domain r x y)
    (hs : s∈Icc 0 (min (NonnegativeTotals.Explicit.e r x y) (19/50))) (i j : Fin 4) :
    0<concentrationScalar (NonnegativeTotals.Explicit.k r x y)
      (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
      (NonnegativeTotals.Explicit.theta r x y) (NonnegativeTotals.Explicit.e r x y) s i j := by
  have h0 := large_scalar_positive r 0 hd hs
  have h1 := large_scalar_positive r 1 hd hs
  have h2 := large_scalar_positive r 2 hd hs
  have hθ := (NonnegativeTotals.Explicit.domains hd).1
  have ht := (NonnegativeTotals.Explicit.domains hd).2.2
  have hδ : NonnegativeTotals.Explicit.theta r x y+NonnegativeTotals.Explicit.e r x y-s∈Icc 0 frameCap := by
    have hse := hs.2.trans (min_le_left _ _)
    dsimp [NonnegativeTotals.Explicit.delta] at ht
    constructor <;> linarith [hθ.1,hs.1,ht.2]
  have hbalanced := balanced_lower r hd hδ i j
  have hmin : 0<PositiveBT3.Analytic.fullBaseline (NonnegativeTotals.Explicit.k r x y)
      (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
      (NonnegativeTotals.Explicit.theta r x y)+NonnegativeTotals.Explicit.l r x y*gain s+
      TwoPositive.ASupport.charge (NonnegativeTotals.Explicit.e r x y)+
      TwoPositive.balancedEnvelope (NonnegativeTotals.Explicit.k r x y)
        (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
        (NonnegativeTotals.Explicit.theta r x y+NonnegativeTotals.Explicit.e r x y-s) := by
    unfold TwoPositive.balancedEnvelope
    rw [add_min,add_min]
    exact lt_min h0 (lt_min h1 h2)
  dsimp [concentrationScalar]
  linarith

theorem low_scalar_positive {z e s : ℝ} (hz : 0≤z) (hs : 0≤ s)
    (hse : s≤e) (ht : z+e≤1/6) :
    0<PositiveBT3.Analytic.lowBaseline (PositiveBT3.lowK (z+e-s))
      (PositiveBT3.lowM (z+e-s)) z+gain s+TwoPositive.ASupport.charge e+
      V R (PositiveBT3.lowK (z+e-s)) 1 (z+e-s) := by
  have hδ : z+e-s∈Icc 0 (1/6:ℝ) := ⟨by linarith,by linarith⟩
  have he : e-s∈Icc 0 (z+e-s) := ⟨by linarith,by linarith⟩
  have href := PositiveBT3.Analytic.low_scalar_positive hδ he
  have hgain := NegativeA.LongE.small_transfer (l:=1) le_rfl hs hse (by linarith : e≤1/6)
  have heq : z+e-s-(e-s)=z := by ring
  simp only [PositiveBT3.Analytic.lowScalar,heq] at href
  simp only [one_mul] at hgain
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
end
end
end

section
/-!
## Original negative-A / positive-BT3 exclusion when e≥s

All twelve endpoints,
their concavity, both signed budgets, and the original A gain are
discharged internally. The actual T point has no tangent-sign or
radial-kind restriction, and TD0 retains its arbitrary original error.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

namespace Source

theorem large_actual_false {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (19/50:ℝ)) (ha : aError C atG= -s)
    (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hlarge : 1/6≤delta C.theta B+eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have hb0 := budgets hg atG de eh 1 1 1 hvar hs.1 ha hz he
  obtain ⟨r,x,y,hd,hZ,hE⟩ := NonnegativeTotals.Explicit.coordinates hz hb0.e_domain.1
    ⟨hlarge,hb0.total_upper⟩
  let k := NonnegativeTotals.Explicit.k r x y
  let l := NonnegativeTotals.Explicit.l r x y
  let m := NonnegativeTotals.Explicit.c r x y
  have hsf : s∈Icc 0 (min (NonnegativeTotals.Explicit.e r x y) (19/50)) :=
    ⟨hs.1,le_min (by rwa [hE]) hs.2⟩
  have hz' : delta C.theta B∈Icc 0 (NonnegativeTotals.Explicit.theta r x y) := ⟨hz,by rw [hZ]⟩
  have hc := PositiveBT3.Balanced.pair_domain r hd hz'
  have hbase := NonnegativeTotals.Explicit.base_bounds r hd
  have hb := budgets hg atG de eh k l m hvar hs.1 ha hz he
  have hsum := full_stress_lower atG de eh hsorted hcontained hq hHy hGy hBy hDy
    hvar hs.1 ha hz he hgain hhg
    (show k≤1 by dsimp [k]; linarith [hbase.k_upper]) hbase.k_le_l
    hbase.l_positive.le hbase.c_positive.le (fun i => (hc i).1)
  have haux : ∀ {p q : ℝ},0<p → 2*q≤3*p → q≤2*p := fun h1 h2 => by linarith
  obtain ⟨i,j,hendpoint⟩ := ordinary_concentration R
    (PositiveBT3.pWeights k l m (PositiveBT3.tilted m (delta C.theta B)))
    (PositiveBT3.qWeights k l m (PositiveBT3.tilted m (delta C.theta B)))
    (fun i => (blocks C hg atG de eh k l m i).P)
    (fun i => (blocks C hg atG de eh k l m i).N)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hc i).1) (fun i => (hc i).2.1)
    (fun i => haux (hc i).1 (hc i).2.2)
    (fun i => (blocks C hg atG de eh k l m i).P_nonneg)
    (fun i => (blocks C hg atG de eh k l m i).N_nonneg)
    hb.residual_domain hb.positive_bound hb.balance
  change PositiveBT3.endpoint k l m (PositiveBT3.tilted m (delta C.theta B))
    (effective C de eh s) i j≤_ at hendpoint
  have hpositive := large_concentration_positive r hd hsf i j
  rw [hZ,hE] at hpositive
  have hupper := stress_nonpositive atG de eh
    (show 0≤k by dsimp [k]; linarith [hbase.k_lower]) hbase.l_positive.le
    hbase.c_positive hb.bt_domain hHG hGA hAB hBT hTD hDE hEH
  dsimp [concentrationScalar,effective] at hpositive hendpoint
  linarith

theorem low_actual_false {q s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool) (hsorted : ∀i,(C.point i).Sorted)
    (hcontained : ∀i,(C.point i).Contained q) (hq : q≤qCap)
    (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta B) (he : s≤eTotal C de eh)
    (hsmall : delta C.theta B+eTotal C de eh≤1/6)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 3)
    (hTD : C.Feasible T 0) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  let t := effective C de eh s
  let k := PositiveBT3.lowK t
  let m := PositiveBT3.lowM t
  have ht : t∈Icc 0 (1/6:ℝ) := by dsimp [t,effective]; constructor <;> linarith
  have hb := budgets hg atG de eh k 1 m hvar hs ha hz he
  have henv := PositiveBT3.LowEnvelope.lower ht
    (fun i => (blocks C hg atG de eh k 1 m i).P)
    (fun i => (blocks C hg atG de eh k 1 m i).N)
    (fun i => (blocks C hg atG de eh k 1 m i).P_nonneg)
    (fun i => (blocks C hg atG de eh k 1 m i).N_nonneg)
    hb.balance hb.positive_bound
  have hminor := low_stress_lower atG de eh hsorted hcontained hq hHy hGy hBy hDy
    hvar hs ha hz he hgain hhg ht
  have hpositive := low_scalar_positive hz hs he hsmall
  have hr := PositiveBT3.Analytic.low_ranges ht
  have hupper := stress_nonpositive atG de eh
    (show 0≤k by dsimp [k,t]; linarith [hr.1.1]) (by norm_num : (0:ℝ)≤1)
    (show 0< m by dsimp [m,t]; linarith [hr.2.1]) hb.bt_domain
    hHG hGA hAB hBT hTD hDE hEH
  change 0<PositiveBT3.Analytic.lowBaseline k m (delta C.theta B)+gain s+
    TwoPositive.ASupport.charge (eTotal C de eh)+V R k 1 t at hpositive
  linarith

end Source

theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : Source.aError C atG= -s) (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (he : s≤PairedE.cycleTotal C de eh) (hz : 0≤delta C.theta B)
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 0)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have he0 : 0≤PairedE.cycleTotal C de eh := hs.1.trans he
  by_cases hsecondary : atG=true ∧ C.Feasible G 2
  · rcases hsecondary with ⟨rfl,hGA2⟩
    have hHG' : C.Feasible H 0∨C.Feasible H 2 := by
      rcases hhg with rfl|rfl
      · exact Or.inl hHG
      · exact Or.inr hHG
    exact PositiveBT3.Source.actual_false false false de eh hsorted hcontained hq
      hHy hGy hBy hDy hvar (by simp [PositiveBT3.Source.aTotal,PairedE.total,PairedE.selected])
      hz he0 hHG' hGA2 (by simpa using hAB) hBT hTD hDE hEH
  have hnot : atG=true → ¬C.Feasible G 2 := by
    intro hh hf
    exact hsecondary ⟨hh,hf⟩
  have hgain := Source.gain_lower atG hsorted hcontained hq hGy hBy hflat hAy hs ha hnot hGA hAB
  have hs' : s∈Icc 0 (19/50:ℝ) := by
    refine ⟨hs.1,?_⟩
    cases atG <;> simp only [NegativeAPositiveTD.Explicit.angleCut,ite_true,ite_false,
      Bool.false_eq_true] at hs <;> linarith [hs.2]
  by_cases hsmall : delta C.theta B+PairedE.cycleTotal C de eh≤1/6
  · exact Source.low_actual_false atG de eh hsorted hcontained hq hHy hGy hBy hDy
      hvar hs.1 ha hz he hsmall hgain hhg hHG hGA hAB hBT hTD hDE hEH
  · exact Source.large_actual_false atG de eh hsorted hcontained hq hHy hGy hBy hDy
      hvar hs' ha hz he (lt_of_not_ge hsmall).le hgain hhg hHG hGA hAB hBT hTD hDE hEH

end SquaresInCircles.Eight.GlobalGA.NegativeABT3.LongE
end
end
end

section
/-!
## All pure positive and negative far-low EH alternatives

Positive surplus is moved
only in the actual EH magnitude, with all coefficients fixed. Its first
endpoint is max(.1,theta). Negative surplus is concave in that magnitude
and retains both intrinsic endpoints .1 and theta. The distinguished D
positive term remains its literal linear cost.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLowPure
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open NegativeAPositiveTD.PositiveSlope OrdinaryNegativeSlope

def positivePart (θ z : ℝ) (i : Fin 4) (s : ℝ) : ℝ :=
  NegativeEH.G s+Blocks.positive .far .low θ z (s-θ) i

def positiveSlope (θ z : ℝ) (i : Fin 4) (s : ℝ) : ℝ :=
  if i=3 then NegativeEH.GD s-(Blocks.dCost+Explicit.errorCharge .far)
  else NegativeEH.GD s+Ud (Blocks.p .far .low θ z i) (Blocks.q .far .low θ z i) (s-θ)-
    Explicit.errorCharge .far

lemma positive_derivative {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (hs : s∈Icc (max (1/10) θ) (1/4)) (i : Fin 4) :
    HasDerivAt (positivePart θ z i) (positiveSlope θ z i s) s := by
  have hp := FarLowSlopes.pair_data hθ hz i
  have hx : s-θ∈Icc 0 frameCap :=
    ⟨by linarith [le_max_right (1/10:ℝ) θ,hs.1],
      by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩
  by_cases hi : i=3
  · subst i
    have h1 : HasDerivAt (fun t => (Blocks.dCost+Explicit.errorCharge .far)*(t-θ))
        ((Blocks.dCost+Explicit.errorCharge .far)*1) s :=
      ((hasDerivAt_id' s).sub_const θ).const_mul _
    convert (NegativeEH.G_hasDerivAt s).fun_sub h1 using 1
    · funext t
      rw [positivePart,Blocks.positive_D]
      ring
    · simp [positiveSlope]
  · have hU : HasDerivAt (fun t => U R (Blocks.p .far .low θ z i) (Blocks.q .far .low θ z i) (t-θ))
        (Ud (Blocks.p .far .low θ z i) (Blocks.q .far .low θ z i) (s-θ)) s :=
      HasDerivAt.comp_sub_const s θ (U_hasDerivAt
        (show 0<Blocks.p .far .low θ z i by linarith [hp.1])
        (show 0<Blocks.q .far .low θ z i by linarith [hp.1,hp.2.1]) hx)
    have h1 : HasDerivAt (fun t => Explicit.errorCharge .far*(t-θ))
        (Explicit.errorCharge .far*1) s :=
      ((hasDerivAt_id' s).sub_const θ).const_mul _
    convert ((NegativeEH.G_hasDerivAt s).fun_add hU).fun_sub h1 using 1
    · funext t
      simp only [positivePart,Blocks.positive,ChargedHybridConcentration.positive,
        PositiveTD.Hybrid.positive,ite_eq_right hi]
      ring
    · simp [positiveSlope,hi]

lemma positive_slope {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (hs : s∈Icc (max (1/10) θ) (1/4)) (i : Fin 4) :
    0<positiveSlope θ z i s := by
  have hsf : s∈Icc (1/10:ℝ) (1/4) :=
    ⟨(le_max_left _ _).trans hs.1,hs.2⟩
  have hG := NegativeEH.far_slope hsf
  have hp := FarLowSlopes.pair_data hθ hz i
  by_cases hi : i=3
  · simp only [positiveSlope,ite_eq_left hi]
    dsimp [Blocks.dCost,Explicit.errorCharge,NegativeEH.epsilon]
    linarith [diagonal_bounds.2]
  · have hx : s-θ∈Icc 0 frameCap :=
      ⟨by linarith [le_max_right (1/10:ℝ) θ,hs.1],
        by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩
    have hU := NegativeDEPositiveTD.OrdinarySlope.positive_derivative_whole
      (show 0<Blocks.p .far .low θ z i by linarith [hp.1]) hp.2.1
      (show Blocks.q .far .low θ z i≤2*Blocks.p .far .low θ z i by linarith [hp.1,hp.2.2]) hx
    simp only [positiveSlope,ite_eq_right hi]
    dsimp [Explicit.errorCharge,NegativeEH.epsilon]
    linarith [FarLowSlopes.q_upper hθ hz i]

lemma positive_monotone {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    MonotoneOn (positivePart θ z i) (Icc (max (1/10) θ) (1/4)) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hs => (positive_derivative hθ hz hs i).continuousAt.continuousWithinAt)
    (fun _ hs => positive_derivative hθ hz (Ioo_subset_Icc_self hs) i)
    (fun _ hs => (positive_slope hθ hz (Ioo_subset_Icc_self hs) i).le)

lemma positive_start {a z : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/10))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 4) :
    0<Explicit.baseline .far .low a z+positivePart (a+z) z i (1/10) := by
  have ht : a+z∈Icc (0:ℝ) (1/4) := ⟨hθ.1,by linarith [hθ.2]⟩
  have hsplit : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hd : 1/10-(a+z)∈Icc 0 frameCap :=
    ⟨by linarith [hθ.2],by norm_num [frameCap]; linarith [hθ.1]⟩
  have hH := FarLowSplit.positive_H hθ ha hz
  fin_cases i
  · simpa [positivePart,Blocks.positive,ChargedHybridConcentration.positive,
      PositiveTD.Hybrid.positive,Blocks.p,Blocks.q,Explicit.p,Explicit.q,
      Explicit.errorCharge,add_assoc,sub_eq_add_neg] using hH
  · have hcmp := FarLowSlopes.H_le_G ht hsplit hd
    dsimp [Explicit.U,Explicit.p,Explicit.q] at hcmp
    change 0<Explicit.baseline .far .low a z+(NegativeEH.G (1/10)+
      (U R (Explicit.k .far .low (a+z)) (Explicit.l .far .low (a+z)) (1/10-(a+z))-
        NegativeEH.epsilon*(1/10-(a+z))))
    linarith
  · have hB := FarLowSplit.positive_B hθ ha hz
    have horder := (Explicit.far_low_tilted ht hsplit).2.2.1.le
    simpa [positivePart,Blocks.positive,ChargedHybridConcentration.positive,
      PositiveTD.Hybrid.positive,Blocks.p,Blocks.q,Explicit.p,Explicit.q,
      Explicit.errorCharge,min_eq_left horder,max_eq_right horder,
      add_assoc,sub_eq_add_neg] using hB
  · have hcmp := NegativeEH.PositiveD.H_le_D
      (k:=Explicit.k .far .low (a+z)) (ε:=NegativeEH.epsilon)
      (by norm_num [Explicit.k]) hd
    change 0<Explicit.baseline .far .low a z+(NegativeEH.G (1/10)+
      Blocks.positive .far .low (a+z) z (1/10-(a+z)) 3)
    rw [Blocks.positive_D]
    dsimp [Blocks.dCost,Explicit.errorCharge]
    linarith

theorem positive_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4))
    (horder : a+z≤ s) (i : Fin 4) :
    0<Explicit.baseline .far .low a z+positivePart (a+z) z i s := by
  have hsplit : z∈Icc 0 (a+z) := ⟨hz,by linarith⟩
  have hsm : s∈Icc (max (1/10) (a+z)) (1/4) := ⟨max_le hs.1 horder,hs.2⟩
  have hm := positive_monotone hθ hsplit i
  by_cases hlow : a+z≤1/10
  · have hstart := positive_start ⟨hθ.1,hlow⟩ ha hz i
    have hh := hm (show (1/10:ℝ)∈Icc (max (1/10) (a+z)) (1/4) by
      rw [max_eq_left hlow]; norm_num) hsm hs.1
    linarith
  · have hstart := FarLowSplit.equal_positive ⟨by linarith,hθ.2⟩ ha hz
    have hh := hm (show a+z∈Icc (max (1/10) (a+z)) (1/4) by
      rw [max_eq_right (by linarith : (1/10:ℝ)≤a+z)]; exact ⟨le_rfl,hθ.2⟩) hsm horder
    have he : positivePart (a+z) z i (a+z)=NegativeEH.G (a+z) := by
      by_cases hi : i=3
      · subst i
        simp [positivePart,Blocks.positive_D]
      · simp [positivePart,Blocks.positive,ChargedHybridConcentration.positive,
          PositiveTD.Hybrid.positive,hi,U_zero]
    rw [he] at hh
    linarith

lemma negative_start {a z : ℝ} (hθ : a+z∈Icc (1/10:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (i : Fin 4) :
    0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      Blocks.negative .far .low (a+z) z (a+z-1/10) i := by
  have hH := FarLowSplit.negative_H hθ ha hz
  have hG := FarLowSplit.negative_G hθ ha hz
  fin_cases i
  · exact hH
  · exact hG
  · have hcmp := FarLowSlopes.H_le_B
      (show a+z∈Icc (0:ℝ) (1/4) from ⟨by linarith [hθ.1],hθ.2⟩)
      (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
      (show a+z-1/10∈Icc 0 frameCap from
        ⟨by linarith [hθ.1],by norm_num [frameCap]; linarith [hθ.2]⟩)
    change 0<Explicit.baseline .far .low a z+NegativeEH.G (1/10)+
      Explicit.V .far .low (a+z) z 2 (a+z-1/10)
    have e0 : Explicit.V .far .low (a+z) z 0 (a+z-1/10)=
        V R (Explicit.k .far .low (a+z)) 1 (a+z-1/10) := rfl
    linarith
  · exact hH

theorem negative_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4))
    (horder : s≤a+z) (i : Fin 4) :
    0<Explicit.baseline .far .low a z+NegativeEH.G s+
      Blocks.negative .far .low (a+z) z (a+z-s) i := by
  have ht : a+z∈Icc (1/10:ℝ) (1/4) := ⟨hs.1.trans horder,hθ.2⟩
  have hp := FarLowSlopes.pair_data hθ ⟨hz,by linarith⟩ i
  have hg := NegativeEH.G_concave.subset
    (Icc_subset_Icc (by norm_num : (0:ℝ)≤1/10)
      (by norm_num [frameCap]; linarith [hθ.2] : a+z≤frameCap))
    (convex_Icc (1/10:ℝ) (a+z))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le
      (show 0<Blocks.p .far .low (a+z) z i by linarith [hp.1]) hp.2.1
      (show Blocks.q .far .low (a+z) z i≤2*Blocks.p .far .low (a+z) z i by
        linarith [hp.1,hp.2.2]))
    (a:=-1) (b:=a+z) (l:=1/10) (u:=a+z)
    (fun t ht => ⟨by linarith [ht.2],by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc := OrdinaryMixedShortReserve.constant_add (hg.add hv) (Explicit.baseline .far .low a z)
  have hh := concave_gt_of_endpoints hc ⟨hs.1,horder⟩
    (by simpa [Blocks.negative,neg_one_mul,neg_add_eq_sub,add_assoc]
      using negative_start ht ha hz i)
    (by simpa [V_zero] using FarLowSplit.equal_positive ht ha hz)
  simpa [Blocks.negative,neg_one_mul,neg_add_eq_sub,add_assoc] using hh

theorem pure_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4)) (i j : Fin 4) :
    0<Explicit.stressBase .far .low a z s+Blocks.pure .far .low (a+z) z s i j := by
  by_cases horder : s≤a+z
  · have hh := negative_positive hθ ha hz hs horder j
    simpa [Explicit.stressBase,Explicit.gain,Blocks.pure,ChargedHybridConcentration.pure,
      horder,Blocks.negative] using hh
  · have hh := positive_positive hθ ha hz hs (by linarith) i
    simpa [Explicit.stressBase,Explicit.gain,Blocks.pure,ChargedHybridConcentration.pure,
      horder,positivePart,Blocks.positive,add_assoc] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLowPure
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLow
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma ordinary_same_lower {θ z s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (hs : s∈Icc (1/10:ℝ) (1/4))
    (i : Fin 4) (hi : i≠3) :
    Blocks.pure .far .low θ z s i i≤Blocks.saturated .far .low θ z s i i := by
  have hp := FarLowSlopes.pair_data hθ hz i
  have hP : 0≤frameCap-θ := by norm_num [frameCap]; linarith [hθ.2]
  have hN : 0≤frameCap-s := by norm_num [frameCap]; linarith [hs.2]
  have hNcap : frameCap-s≤3/5 := by norm_num [frameCap]; linarith [hs.1]
  have hPcap : frameCap-θ≤frameCap := by linarith [hθ.1]
  by_cases horder : s≤θ
  · have hPN : frameCap-θ≤frameCap-s := by linarith
    have hh := NegativeEH.SameBlock.negative_charged hp.1 hp.2.2 hP hPN hNcap
    simpa only [Blocks.pure,Blocks.saturated,ChargedHybridConcentration.pure,
      ChargedHybridConcentration.saturated,ite_eq_left horder,↓reduceIte,
      ChargedHybridConcentration.block,PositiveTD.Hybrid.block,ite_eq_right hi,
      Explicit.errorCharge,show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  · have hNP : frameCap-s≤frameCap-θ := by linarith
    have hh := NegativeEH.SameBlock.positive_charged hp.1 hp.2.2 hN hNP hPcap hNcap
    simpa only [Blocks.pure,Blocks.saturated,ChargedHybridConcentration.pure,
      ChargedHybridConcentration.saturated,ite_eq_right horder,↓reduceIte,
      ChargedHybridConcentration.positive,ChargedHybridConcentration.block,
      PositiveTD.Hybrid.positive,PositiveTD.Hybrid.block,ite_eq_right hi,
      Explicit.errorCharge,show frameCap-θ-(frameCap-s)=s-θ by ring] using hh

lemma saturated_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4)) (i j : Fin 4) :
    0<Explicit.stressBase .far .low a z s+Blocks.saturated .far .low (a+z) z s i j := by
  by_cases he : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      have hh := FarLowSeparated.original_positive hθ ha hz hs 3 3
      have heq : Blocks.saturated .far .low (a+z) z s 3 3=
          Blocks.block .far .low (a+z) z (frameCap-(a+z)) (frameCap-s) 3 := by
        simp only [Blocks.saturated,ChargedHybridConcentration.saturated,↓reduceIte,Blocks.block]
      rw [heq,Blocks.block_D]
      linarith
    · have hl := ordinary_same_lower hθ ⟨hz,by linarith⟩ hs i hi
      have hh := FarLowPure.pure_positive hθ ha hz hs i i
      linarith
  · have hh := FarLowSeparated.original_positive hθ ha hz hs i j
    simpa only [Blocks.saturated,ChargedHybridConcentration.saturated,ite_eq_right he,
      Blocks.positive,Blocks.negative,add_assoc] using hh

theorem scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (0:ℝ) (1/4)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<Explicit.stressBase .far .low a z s+
      ∑i,Blocks.block .far .low (a+z) z (P i) (N i) i := by
  obtain ⟨i,j,hij⟩ := Blocks.concentrate .far .low P N hθ
    ⟨hz,by linarith⟩ hs hP hN hPb hNb hbalance
  have hpure := FarLowPure.pure_positive hθ ha hz hs i j
  have hsat := saturated_positive hθ ha hz hs i j
  have hmin : -Explicit.stressBase .far .low a z s<
      min (Blocks.pure .far .low (a+z) z s i j) (Blocks.saturated .far .low (a+z) z s i j) :=
    lt_min (by linarith) (by linarith)
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.FarLow
end
end
end
