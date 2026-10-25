module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongEndpoints
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3Balanced
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LargeEndpoints
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSplit

/-!
# Eight squares: positivity for every longer-E negative-A magnitude with BT3

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

