module

public import SquaresInCircles.Eight.Owners.GA.Negative.ABT3LongEndpoints
public import SquaresInCircles.Eight.Owners.GA.Negative.ALongESourceData
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsScalar
public import SquaresInCircles.Eight.Owners.GA.Nonnegative.TotalsSource
public import SquaresInCircles.Eight.Owners.GA.Paired.ECharge
public import SquaresInCircles.Eight.Owners.GA.EZero

/-!
# Eight squares: the exclusion of a single negative A with a longer E

Both A-owner choices and all four E-owner choices are covered. The only inputs are the geometric
conditions of the cycle, its weak contacts and the local entry bounds of the flat A; the weights
and every strict scalar reserve are built in the proof (`original_concentration`, `original`).
-/

section
/-!
## The complete longer-E scalar comparison

The weights are fixed
while the negative A magnitude varies. Concavity reduces to zero and
min(e,19/50); the latter is exactly one of the four certified domains.
The low-total branch uses the earlier small-total stress at e-s.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE
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
      simpa only [Analytic.endpoint,Explicit.k,Explicit.l,Explicit.c,Explicit.z,Explicit.e,
        Explicit.s,Explicit.baseRegion,Explicit.baseY,NonnegativeTotals.Explicit.e,min_eq_left he] using hh
    · have hdom : Explicit.Domain .TC x (y-19/50) :=
        ⟨hd.1,by linarith,by linarith [hd.2.2]⟩
      have hy : Explicit.baseY .TC x (y-19/50)=y := by dsimp [Explicit.baseY]; ring
      have hh := Analytic.endpoint_positive .TC i hdom
      simpa only [Analytic.endpoint,Explicit.k,Explicit.l,Explicit.c,Explicit.z,Explicit.e,
        Explicit.s,Explicit.baseRegion,hy,NonnegativeTotals.Explicit.e,min_eq_right (le_of_not_ge he)] using hh
  | rectangle =>
    by_cases he : x+y≤19/50
    · have hdom : Explicit.Domain .RE x y := ⟨hd.1,⟨hd.2.1,by linarith⟩⟩
      have hh := Analytic.endpoint_positive .RE i hdom
      simpa only [Analytic.endpoint,Explicit.k,Explicit.l,Explicit.c,Explicit.z,Explicit.e,
        Explicit.s,Explicit.baseRegion,Explicit.baseY,NonnegativeTotals.Explicit.e,min_eq_left he] using hh
    · have hdom : Explicit.Domain .RC x (x+y-19/50) :=
        ⟨hd.1,⟨by linarith,by linarith [hd.2.2]⟩⟩
      have hy : Explicit.baseY .RC x (x+y-19/50)=y := by dsimp [Explicit.baseY]; ring
      have hh := Analytic.endpoint_positive .RC i hdom
      simpa only [Analytic.endpoint,Explicit.k,Explicit.l,Explicit.c,Explicit.z,Explicit.e,
        Explicit.s,Explicit.baseRegion,hy,NonnegativeTotals.Explicit.e,min_eq_right (le_of_not_ge he)] using hh

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
  have hp := NonnegativeTotals.Explicit.pair_domain r hd hθmem i.castSucc
  have hcV := V_concave (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1
    (show NonnegativeTotals.Explicit.qWeights r x y (NonnegativeTotals.Explicit.theta r x y) i.castSucc≤
      2*NonnegativeTotals.Explicit.pWeights r x y (NonnegativeTotals.Explicit.theta r x y) i.castSucc by
      linarith [hp.2.2])
  have hcneg : ConcaveOn ℝ (Icc 0 frameCap)
      (fun t => NonnegativeTotals.Analytic.negative (NonnegativeTotals.Explicit.k r x y)
        (NonnegativeTotals.Explicit.l r x y)
        (PositiveTD.tilted (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.theta r x y)) t i) := by
    have e : (fun t => NonnegativeTotals.Analytic.negative (NonnegativeTotals.Explicit.k r x y)
        (NonnegativeTotals.Explicit.l r x y)
        (PositiveTD.tilted (NonnegativeTotals.Explicit.c r x y)
          (NonnegativeTotals.Explicit.theta r x y)) t i)=
        V (Real.sqrt qCap)
          (NonnegativeTotals.Explicit.pWeights r x y (NonnegativeTotals.Explicit.theta r x y) i.castSucc)
          (NonnegativeTotals.Explicit.qWeights r x y (NonnegativeTotals.Explicit.theta r x y) i.castSucc) := by
      funext t
      fin_cases i <;> rfl
    rw [e]
    exact hcV
  have hcarg := concave_affine_argument (a:=(-1:ℝ))
    (b:=NonnegativeTotals.Explicit.theta r x y+NonnegativeTotals.Explicit.e r x y)
    (l:=0) (u:=min (NonnegativeTotals.Explicit.e r x y) (19/50)) hcneg (by
      intro s hs
      have hse := hs.2.trans (min_le_left _ _)
      dsimp [NonnegativeTotals.Explicit.delta] at ht
      constructor <;> linarith [hθ.1,hs.1,ht.2])
  have hgain := gain_concave.subset
    (Icc_subset_Icc le_rfl (min_le_right (NonnegativeTotals.Explicit.e r x y) (19/50)))
    (convex_Icc _ _)
  refine ⟨convex_Icc _ _,?_⟩
  intro a ha b hb' u v hu hv huv
  have hG := mul_le_mul_of_nonneg_left (hgain.2 ha hb' hu hv huv) hb.l_positive.le
  have hV := hcarg.2 ha hb' hu hv huv
  simp only [smul_eq_mul] at hG hV ⊢
  have hconst := congrArg (fun t : ℝ => t*
    (NonnegativeTotals.Analytic.fullBaseline (NonnegativeTotals.Explicit.k r x y)
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
    simpa [scalar,NonnegativeTotals.Analytic.endpoint,NonnegativeTotals.Analytic.largeScalar,
      NonnegativeTotals.Analytic.aAt,gain_zero] using
        NonnegativeTotals.Analytic.endpoint_positive r .atT i hd
  exact concave_gt_of_endpoints (f := fun s => scalar (NonnegativeTotals.Explicit.k r x y)
      (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
      (NonnegativeTotals.Explicit.theta r x y) (NonnegativeTotals.Explicit.e r x y) s i)
    (scalar_concave r i hd) ⟨hs.1,hs.2⟩ hzero (upper_endpoint_positive r i hd)

def concentrationScalar (k l c z e s : ℝ) (i j : Fin 4) : ℝ :=
  PositiveTD.baseline k l c z+l*gain s+TwoPositive.ASupport.charge e+
    TwoPositive.endpoint k l (PositiveTD.tilted c z) (z+e-s) i j

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
  have hz : NonnegativeTotals.Explicit.theta r x y∈Icc 0 (NonnegativeTotals.Explicit.theta r x y) :=
    ⟨hθ.1,le_rfl⟩
  have hδ : NonnegativeTotals.Explicit.theta r x y+NonnegativeTotals.Explicit.e r x y-s∈Icc 0 frameCap := by
    have hse := hs.2.trans (min_le_left _ _)
    dsimp [NonnegativeTotals.Explicit.delta] at ht
    constructor <;> linarith [hθ.1,hs.1,ht.2]
  have hbalanced := TwoPositive.balanced_endpoint_lower
    (fun i => (NonnegativeTotals.Explicit.pair_domain r hd hz i).1)
    (fun i => (NonnegativeTotals.Explicit.pair_domain r hd hz i).2.1)
    (fun i => (NonnegativeTotals.Explicit.pair_domain r hd hz i).2.2)
    (NonnegativeTotals.Explicit.pairwise_ratio r hd hz) hδ i j
  have hmin : 0<NonnegativeTotals.Analytic.fullBaseline (NonnegativeTotals.Explicit.k r x y)
      (NonnegativeTotals.Explicit.l r x y) (NonnegativeTotals.Explicit.c r x y)
      (NonnegativeTotals.Explicit.theta r x y)+NonnegativeTotals.Explicit.l r x y*gain s+
      TwoPositive.ASupport.charge (NonnegativeTotals.Explicit.e r x y)+
      TwoPositive.balancedEnvelope (NonnegativeTotals.Explicit.k r x y)
        (NonnegativeTotals.Explicit.l r x y)
        (PositiveTD.tilted (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.theta r x y))
        (NonnegativeTotals.Explicit.theta r x y+NonnegativeTotals.Explicit.e r x y-s) := by
    unfold TwoPositive.balancedEnvelope
    rw [add_min,add_min]
    exact lt_min h0 (lt_min h1 h2)
  have hbase := NonnegativeTotals.Analytic.fullBaseline_le
    (NonnegativeTotals.Explicit.k r x y) (NonnegativeTotals.Explicit.l r x y)
    (NonnegativeTotals.Explicit.c r x y) (NonnegativeTotals.Explicit.theta r x y)
  rw [NonnegativeTotals.Explicit.tilted_eq] at hbalanced
  dsimp [concentrationScalar]
  linarith

theorem low_concentration_positive {z e s : ℝ} (hz : 0≤z) (_he : 0≤e)
    (hs : 0≤ s) (hse : s≤e) (ht : z+e≤1/6) (i j : Fin 4) :
    0<concentrationScalar (PositiveTD.Explicit.lowK (z+e-s))
      (PositiveTD.Explicit.lowL (z+e-s)) (PositiveTD.Explicit.lowC (z+e-s)) z e s i j := by
  have hδ : z+e-s∈Icc 0 (1/6:ℝ) := ⟨by linarith,by linarith⟩
  have hl := (PositiveTD.Explicit.low_ranges hδ).2.2.1
  have htransfer := small_transfer hl.le hs hse (show e≤1/6 by linarith)
  have href := NonnegativeTotals.low_scalar_positive (a:=0) (z:=z) (e:=e-s)
    (by norm_num) hz (by linarith) (by linarith) i j
  have heq : 0+z+(e-s)=z+e-s := by ring
  simp only [NonnegativeTotals.scalar,heq,TwoPositive.ASupport.charge_zero,mul_zero,add_zero] at href
  dsimp [concentrationScalar]
  linarith

/-- Constructed weights discharge every concentration endpoint for the
full longer-E interval. The coefficient domain is the original TD2 one. -/
theorem explicit_positive {z e s : ℝ} (hz : 0≤z) (he : 0≤e)
    (hs : s∈Icc 0 (19/50:ℝ)) (hse : s≤e) (ht : z+e≤frameCap) :
    ∃k l c : ℝ,k∈Icc (1/2:ℝ) (17/20) ∧ l∈Icc k (2*k) ∧ c∈Icc k 2 ∧
      (l≤2*PositiveTD.tilted c z ∧ PositiveTD.tilted c z≤2*l) ∧
      ∀i j : Fin 4,0<concentrationScalar k l c z e s i j := by
  by_cases hlow : z+e≤1/6
  · have hδ : z+e-s∈Icc 0 (1/6:ℝ) := ⟨by linarith [hs.1],by linarith [hs.1]⟩
    have hzd : z∈Icc 0 (z+e-s) := ⟨hz,by linarith⟩
    have hc := TwoPositive.low_split_domain hδ hzd
    exact ⟨PositiveTD.Explicit.lowK (z+e-s),PositiveTD.Explicit.lowL (z+e-s),
      PositiveTD.Explicit.lowC (z+e-s),hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,
      low_concentration_positive hz he hs.1 hse hlow⟩
  · obtain ⟨r,x,y,hd,hθ,hE⟩ := NonnegativeTotals.Explicit.coordinates hz he
      (show z+e∈Icc (1/6:ℝ) frameCap from ⟨(lt_of_not_ge hlow).le,ht⟩)
    have hz' : z∈Icc 0 (NonnegativeTotals.Explicit.theta r x y) := ⟨hz,by rw [hθ]⟩
    have hc := NonnegativeTotals.Explicit.coefficient_domain r hd hz'
    refine ⟨NonnegativeTotals.Explicit.k r x y,NonnegativeTotals.Explicit.l r x y,
      NonnegativeTotals.Explicit.c r x y,hc.1,hc.2.1,hc.2.2.1,⟨hc.2.2.2.1,hc.2.2.2.2⟩,?_⟩
    intro i j
    have hs' : s∈Icc 0 (min (NonnegativeTotals.Explicit.e r x y) (19/50)) :=
      ⟨hs.1,le_min (by rwa [hE]) hs.2⟩
    simpa only [hθ,hE] using large_concentration_positive r hd hs' i j

end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE
end
end
end

section
/-!
## The longer-E stress on the unchanged original cycle

The A gain is bounded on its original point, the two E
primaries are charged together, and every ordinary block keeps its
original signed angular budgets.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Source
open Candidate Secondary SignedStress PositiveAngularEnvelope OrdinaryAngleConcavity
open ActualOrdinaryBlocks
open NegativePrimary (erase)

theorem decomposition (C : SignedCycle) {hg : Fin 4} (atG de eh : Bool)
    (hhg : hg=0∨hg=2) (k l c s : ℝ) :
    actualStress C hg atG de eh k l c=
      PositiveTD.baseline k l c (delta C.theta T)+l*gain s+
        TwoPositive.ASupport.charge (eTotal C de eh)+
        (∑i,actualBlocks C hg atG de eh k l c i)+PositiveTD.tReserve C c+
        l*(PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A)-gain s)+
        NonnegativeTotals.Source.eReserve C de eh := by
  have hh := NonnegativeTotals.Source.decomposition C atG (!atG) de eh hhg k l c
  dsimp [actualStress,actualBlocks,eTotal,PairedE.cycleTotal,
    NonnegativeTotals.Source.aReserve,NonnegativeTotals.Source.eTotal] at ⊢ hh
  linarith

theorem stress_nonpositive {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool) {k l c : ℝ}
    (hk : 0≤k) (hl : 0≤l) (hc : 0<c) (hz : delta C.theta T∈Icc 0 frameCap)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) :
    actualStress C hg atG de eh k l c≤0 := by
  have hAB' : C.Feasible A (if !atG then 2 else 0) := by
    cases atG <;> simpa using hAB
  exact NonnegativeTotals.Source.stress_nonpositive atG (!atG) de eh
    hk hl hc hz hHG hGA hAB' hBT hTD hDE hEH

theorem block_family_lower {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs0 : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l)
    (i : Fin 4) :
    PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
      (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
      (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T))) 3 i
      (blocks C hg atG de eh k l c i).P (blocks C hg atG de eh k l c i).N≤
        actualBlocks C hg atG de eh k l c i := by
  have hb := budgets hg atG de eh k l c hvar hs0 ha hz he
  have hw := PositiveTD.coefficient_domain hk hl hcoef hb.td_domain hratio
  have hordinary (i : Fin 4) {P : SignedPoint} (hy : 0≤P.y) (hP : P.Contained q) :
      mixedBlock R
        (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)) i)
        (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T)) i)
        (blocks C hg atG de eh k l c i).P (blocks C hg atG de eh k l c i).N≤
          PositiveTD.actualPairIncrement (blocks C hg atG de eh k l c i) P := by
    have hco := NonnegativeTotals.Source.block_coefficients (C:=C) (hg:=hg) (c:=c)
      atG (!atG) de eh (show k≤1 by linarith [hk.2]) hl.1 i
    change (blocks C hg atG de eh k l c i).p=_ ∧
      (blocks C hg atG de eh k l c i).q=_ at hco
    have hp : 0≤(blocks C hg atG de eh k l c i).p := by rw [hco.1]; exact (hw i).1.le
    have hbud := block_budgets hg atG de eh k l c hvar hs0 ha hz he i
    have hh := PositiveTD.actual_block_minorant hy hP hq hp hbud.1 hbud.2
    rwa [hco.1,hco.2] at hh
  fin_cases i
  · simpa [PositiveTD.Hybrid.block,actualBlocks,NonnegativeTotals.Source.actualBlocks,blocks]
      using hordinary 0 hHy (hc H)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,NonnegativeTotals.Source.actualBlocks,blocks]
      using hordinary 1 (P:=(C.point G).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy) (by simpa using hc G)
  · simpa [PositiveTD.Hybrid.block,actualBlocks,NonnegativeTotals.Source.actualBlocks,blocks]
      using hordinary 2 (P:=(C.point B).reflect)
        (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy) (by simpa using hc B)
  · have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
    have hsmall := NegativePrimary.erase_abs_bound de (original_error_bound hvar hn D)
    have hh := PositiveTD.actual_D_signed_minorant (P:=(C.point D).reflect)
      (by simpa using hs D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
      (by simpa using hc D) hq hk hcoef hsmall
    simpa [PositiveTD.Hybrid.block,actualBlocks,NonnegativeTotals.Source.actualBlocks,
      blocks,NonnegativeTotals.Source.blocks,Block.P,Block.N,
      PositiveTD.pWeights,PositiveTD.qWeights] using hh

theorem stress_lower {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs0 : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2)
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l) :
    PositiveTD.baseline k l c (delta C.theta T)+l*gain s+
      TwoPositive.ASupport.charge (eTotal C de eh)+
      (∑i,PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2)
        (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
        (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T))) 3 i
        (blocks C hg atG de eh k l c i).P (blocks C hg atG de eh k l c i).N)≤
      actualStress C hg atG de eh k l c := by
  have hb := budgets hg atG de eh k l c hvar hs0 ha hz he
  have hn : negativeVariation C.theta≤frameCap := by rw [←variations_equal]; exact hvar
  have hsum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => block_family_lower (hg:=hg) atG de eh hs hc hq hHy hGy hBy hDy
      hvar hs0 ha hz he hk hl hcoef hratio i)
  have hT := PositiveTD.tReserve_nonneg (hs T) (hc T) hq
    (show 0≤c by linarith [hk.1,hcoef.1]) hb.td_domain
  have hA := mul_nonneg (show 0≤l by linarith [hk.1,hl.1]) (sub_nonneg.mpr hgain)
  have hE := PairedE.selected_charge de eh (hs E) (hc E) hq
    (original_error_bound hvar hn D) (original_error_bound hvar hn E) hb.e_domain
  have hE' : 0≤NonnegativeTotals.Source.eReserve C de eh := by
    exact sub_nonneg.mpr hE
  rw [decomposition C atG de eh hhg k l c s]
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE.Source
end
end
end

section
/-!
## All E owners at a small nonnegative A total

`original_HG`: the HG witness of a source domain is HG0 or HG2. At a small nonnegative A total, an
outer E is reselected on its secondaries at the same state, and a core E is brought to its E-only
normal form, with both mixed-sign moves and the paired-negative intrinsic endpoint. A resulting
single negative EH1 either has EH0 feasible, or its entry cut gives the short secant domain. Every
point, error and selected witness of A and T is kept.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeELowA
open Candidate SignedCycle PairedE

theorem original_HG {q : ℝ} {C : SignedCycle} (I : SourceDomain q C) :
    C.Feasible H 0∨C.Feasible H 2 := by
  have ho : I.owner H=0∨I.owner H=2 := by simpa [highGAOwners,H] using I.allowed H
  rcases ho with ho|ho
  · exact Or.inl (by simpa [ho] using I.feasible H)
  · exact Or.inr (by simpa [ho] using I.feasible H)

end SquaresInCircles.Eight.GlobalGA.NegativeELowA
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeA.LongE
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

namespace Source

theorem original_concentration {q k l c s : ℝ} {C : SignedCycle} {hg : Fin 4}
    (atG de eh : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs0 : 0≤ s) (ha : aError C atG= -s) (hz : 0≤delta C.theta T) (he : s≤eTotal C de eh)
    (hgain : gain s≤PairedE.primaryGain (C.point A) atG (!atG) (delta C.theta G) (delta C.theta A))
    (hhg : hg=0∨hg=2)
    (hHG : C.Feasible H hg) (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2)) (hBT : C.Feasible B 2)
    (hTD : C.Feasible T 2) (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0))
    (hk : k∈Icc (1/2:ℝ) (17/20)) (hl : l∈Icc k (2*k)) (hcoef : c∈Icc k 2)
    (hratio : l≤2*PositiveTD.tilted c (delta C.theta T) ∧ PositiveTD.tilted c (delta C.theta T)≤2*l) :
    ∃i j : Fin 4,concentrationScalar k l c (delta C.theta T) (eTotal C de eh) s i j≤0 := by
  have hb := budgets hg atG de eh k l c hvar hs0 ha hz he
  have hw := PositiveTD.coefficient_domain hk hl hcoef hb.td_domain hratio
  obtain ⟨i,j,hendpoint⟩ := PositiveTD.Hybrid.concentrate R (GlobalGA.Secondary.diagonal-1/2)
    (PositiveTD.pWeights k l (PositiveTD.tilted c (delta C.theta T)))
    (PositiveTD.qWeights k l (PositiveTD.tilted c (delta C.theta T)))
    (fun i => (blocks C hg atG de eh k l c i).P)
    (fun i => (blocks C hg atG de eh k l c i).N) (3:Fin 4)
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (hw i).1) (fun i => (hw i).2.1) (fun i => (hw i).2.2)
    (fun i => (blocks C hg atG de eh k l c i).P_nonneg)
    (fun i => (blocks C hg atG de eh k l c i).N_nonneg)
    hb.residual_domain hb.positive_bound hb.balance
  have hupper := stress_nonpositive atG de eh
    (show 0≤k by linarith [hk.1]) (show 0≤l by linarith [hk.1,hl.1])
    (show 0<c by linarith [hk.1,hcoef.1]) hb.td_domain hHG hGA hAB hBT hTD hDE hEH
  have hlower := stress_lower atG de eh hs hc hq hHy hGy hBy hDy
    hvar hs0 ha hz he hgain hhg hk hl hcoef hratio
  change TwoPositive.endpoint k l (PositiveTD.tilted c (delta C.theta T))
    (effective C de eh s) i j≤_ at hendpoint
  refine ⟨i,j,?_⟩
  dsimp [concentrationScalar,effective] at ⊢ hendpoint
  linarith

end Source

/-- A signed cycle with the necessary conditions is impossible when its nonnegative selected E
total is at least the magnitude of the single negative A primary. -/
theorem original {q s : ℝ} {C : SignedCycle} {hg : Fin 4} (atG de eh : Bool)
    (hsorted : ∀i,(C.point i).Sorted) (hcontained : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap)
    (hs : s∈Icc 0 (NegativeAPositiveTD.Explicit.angleCut atG))
    (ha : Source.aError C atG= -s) (hflat : (C.point A).a=7/12) (hAy : 0≤(C.point A).y)
    (he : s≤PairedE.cycleTotal C de eh) (hz : 0≤delta C.theta T)
    (hhg : hg=0∨hg=2) (hHG : C.Feasible H hg)
    (hGA : C.Feasible G (if atG then 3 else 2))
    (hAB : C.Feasible A (if atG then 0 else 2))
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 2)
    (hDE : C.Feasible D (if de then 3 else 2))
    (hEH : C.Feasible E (if eh then 1 else 0)) : False := by
  have he0 : 0≤PairedE.cycleTotal C de eh := hs.1.trans he
  by_cases hsecondary : atG=true ∧ C.Feasible G 2
  · rcases hsecondary with ⟨rfl,hGA2⟩
    have hHG' : C.Feasible H 0∨C.Feasible H 2 := by
      rcases hhg with rfl|rfl
      · exact Or.inl hHG
      · exact Or.inr hHG
    exact NonnegativeTotals.Source.actual_false false false de eh hsorted hcontained hq
      hHy hGy hBy hDy hvar (by simp [NonnegativeTotals.Source.aTotal,PairedE.total,PairedE.selected])
      hz he0 hHG' hGA2 (by simpa using hAB) hBT hTD hDE hEH
  have hnot : atG=true → ¬C.Feasible G 2 := by
    intro hh hf
    exact hsecondary ⟨hh,hf⟩
  have hgain := Source.gain_lower atG hsorted hcontained hq hGy hBy hflat hAy hs ha hnot hGA hAB
  have hb := Source.budgets hg atG de eh 1 1 1 hvar hs.1 ha hz he
  have hs' : s∈Icc 0 (19/50:ℝ) := by
    refine ⟨hs.1,?_⟩
    cases atG <;> simp only [NegativeAPositiveTD.Explicit.angleCut,ite_true,ite_false,
      Bool.false_eq_true] at hs <;> linarith [hs.2]
  obtain ⟨k,l,c,hk,hl,hcoef,hratio,hpositive⟩ := explicit_positive hz he0 hs' he hb.total_upper
  obtain ⟨i,j,hnonpositive⟩ := Source.original_concentration atG de eh hsorted hcontained hq
    hHy hGy hBy hDy hvar hs.1 ha hz he hgain hhg hHG hGA hAB hBT hTD hDE hEH
    hk hl hcoef hratio
  exact (not_le_of_gt (hpositive i j)) hnonpositive

end SquaresInCircles.Eight.GlobalGA.NegativeA.LongE
end
end
end
