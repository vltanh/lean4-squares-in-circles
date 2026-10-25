module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeALongEEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsScalar

/-!
# The complete longer-E scalar comparison

Uncompiled transcription of Sections 3--4 and 8. The weights are fixed
while the negative A magnitude varies. Concavity reduces to zero and
min(e,19/50); the latter is exactly one of the four certified domains.
The low-total branch uses the earlier small-total stress at e-s.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
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

theorem low_concentration_positive {z e s : ℝ} (hz : 0≤z) (he : 0≤e)
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeA.LongE
