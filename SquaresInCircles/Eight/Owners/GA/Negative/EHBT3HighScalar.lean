module

public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3HighMass
public import SquaresInCircles.Eight.Owners.GA.Negative.EHBT3HighSplit

/-!
# Eight squares: both complete high-total EH1/BT3 scalar exclusions

Every original A/BT split is included.
The actual EH magnitude is reduced by concavity only after all common
mass has been paid. The fourth negative alternative is compared with H
using its actual moving coefficient. The result has only the two signed
budgets and their exact balance as mass hypotheses.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.HighScalar
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

@[simp] lemma charge_small_high (s : ℝ) : charge .smallHigh s=NegativeEH.g s := by
  dsimp [charge,far,gain,NegativeEH.g,NegativeEH.K,NegativeEH.beta]

@[simp] lemma charge_far_high (s : ℝ) : charge .farHigh s=NegativeEH.G s := by
  dsimp [charge,far,gain,NegativeEH.G,NegativeEH.g,NegativeEH.K,NegativeEH.beta,NegativeEH.p]

private lemma r76_ordinaryP_eq (f : Family) (θ z : ℝ) (i : Fin 3) :
    Blocks.ordinaryP f θ i=Blocks.p f θ z i.castSucc := by
  fin_cases i <;> rfl

private lemma r76_ordinaryQ_eq (f : Family) (θ z : ℝ) (i : Fin 3) :
    Blocks.ordinaryQ f θ i=Blocks.q f θ z i.castSucc := by
  fin_cases i <;> rfl

lemma small_high_ordinary_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 3) :
    0<baseline .smallHigh (a+z) a z+charge .smallHigh s+
      Blocks.ordinaryV .smallHigh (a+z) i (a+z-s) := by
  have hp := Blocks.small_high_pairs hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) i.castSucc
  have hpi : 0<Blocks.ordinaryP .smallHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z]; exact hp.1
  have hpq : Blocks.ordinaryP .smallHigh (a+z) i≤Blocks.ordinaryQ .smallHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z,r76_ordinaryQ_eq _ _ z]; exact hp.2.1
  have hqp : Blocks.ordinaryQ .smallHigh (a+z) i≤2*Blocks.ordinaryP .smallHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z,r76_ordinaryQ_eq _ _ z]
    linarith [hp.1,hp.2.2]
  have hg := NegativeEH.g_concave.subset
    (Icc_subset_Icc le_rfl (by norm_num [frameCap] : (1/10:ℝ)≤frameCap))
    (convex_Icc 0 (1/10:ℝ))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hpi hpq hqp)
    (a:=-1) (b:=a+z) (l:=0) (u:=1/10)
    (fun t ht => ⟨by linarith [ht.2,hθ.1],
      by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc : ConcaveOn ℝ (Icc 0 (1/10)) (fun s => baseline .smallHigh (a+z) a z+
      charge .smallHigh s+Blocks.ordinaryV .smallHigh (a+z) i (a+z-s)) := by
    refine ((hg.add hv).add_const (baseline .smallHigh (a+z) a z)).congr ?_
    intro t _
    simp only [Pi.add_apply,neg_one_mul,neg_add_eq_sub,charge_small_high,Blocks.ordinaryV]
    ring
  have h0 := HighSplit.small_high_zero hθ ha hz i
  have h1 := HighSplit.small_high_cut hθ ha hz i
  have h0' : 0<baseline .smallHigh (a+z) a z+charge .smallHigh 0+
      Blocks.ordinaryV .smallHigh (a+z) i (a+z-0) := by
    simpa [NegativeEH.g] using h0
  have hh := concave_gt_of_endpoints hc ⟨hs.1,hs.2⟩ h0' h1
  exact hh

lemma far_high_ordinary_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (i : Fin 3) :
    0<baseline .farHigh (a+z) a z+charge .farHigh s+
      Blocks.ordinaryV .farHigh (a+z) i (a+z-s) := by
  have hp := Blocks.far_high_pairs hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩) i.castSucc
  have hpi : 0<Blocks.ordinaryP .farHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z]
    linarith [hp.1]
  have hpq : Blocks.ordinaryP .farHigh (a+z) i≤Blocks.ordinaryQ .farHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z,r76_ordinaryQ_eq _ _ z]; exact hp.2.1
  have hqp : Blocks.ordinaryQ .farHigh (a+z) i≤2*Blocks.ordinaryP .farHigh (a+z) i := by
    rw [r76_ordinaryP_eq _ _ z,r76_ordinaryQ_eq _ _ z]
    linarith [hp.1,hp.2.2.1]
  have hg := NegativeEH.G_concave.subset
    (Icc_subset_Icc (by norm_num : (0:ℝ)≤1/10)
      (by norm_num [frameCap] : (1/4:ℝ)≤frameCap)) (convex_Icc (1/10:ℝ) (1/4))
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hpi hpq hqp)
    (a:=-1) (b:=a+z) (l:=1/10) (u:=1/4)
    (fun t ht => ⟨by linarith [ht.2,hθ.1],
      by norm_num [frameCap]; linarith [ht.1,hθ.2]⟩)
  have hc : ConcaveOn ℝ (Icc (1/10) (1/4)) (fun s => baseline .farHigh (a+z) a z+
      charge .farHigh s+Blocks.ordinaryV .farHigh (a+z) i (a+z-s)) := by
    refine ((hg.add hv).add_const (baseline .farHigh (a+z) a z)).congr ?_
    intro t _
    simp only [Pi.add_apply,neg_one_mul,neg_add_eq_sub,charge_far_high,Blocks.ordinaryV]
    ring
  have h0 := HighSplit.far_high_cut false hθ ha hz i
  have h1 := HighSplit.far_high_cut true hθ ha hz i
  simp only [Bool.false_eq_true,↓reduceIte] at h0 h1
  have hh := concave_gt_of_endpoints hc ⟨hs.1,hs.2⟩ h0 h1
  exact hh

lemma small_high_D_lower {θ z t : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Blocks.ordinaryV .smallHigh θ 0 t≤Blocks.negative .smallHigh θ z t 3 := by
  have hd := Blocks.small_high_domain hθ
  have hb := NonnegativeTotals.Explicit.base_bounds .triangle hd
  have hz' : z∈Icc 0 (NonnegativeTotals.Explicit.theta .triangle (θ-1/6) 0) := by
    simpa [NonnegativeTotals.Explicit.theta] using hz
  have hh := Blocks.D_redundant
    (k:=NonnegativeTotals.Explicit.k .triangle (θ-1/6) 0)
    (c:=NonnegativeTotals.Explicit.tilted .triangle (θ-1/6) 0 z)
    ⟨by linarith [hb.k_lower],by linarith [hb.k_upper]⟩
    (NonnegativeTotals.Explicit.tilted_lower .triangle hd hz').le
    (NonnegativeTotals.Explicit.tilted_upper .triangle hd hz').le ht
  simpa [Blocks.ordinaryV,Blocks.ordinaryP,Blocks.ordinaryQ,Blocks.negative,
    Blocks.p,Blocks.q,PositiveBT3.pWeights,PositiveBT3.qWeights,
    Explicit.k,Explicit.l,Explicit.m,Explicit.c,L,
    NonnegativeTotals.Explicit.k,NonnegativeTotals.Explicit.l,NonnegativeTotals.Explicit.c,
    NonnegativeTotals.Explicit.tilted,NonnegativeTotals.Explicit.tilt,PositiveBT3.tilted] using hh

lemma far_high_D_lower {θ z t : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (ht : t∈Icc 0 frameCap) :
    Blocks.ordinaryV .farHigh θ 0 t≤Blocks.negative .farHigh θ z t 3 := by
  have hr := NegativeEHPositiveTD.Explicit.far_high_ranges hθ
  have hc := NegativeEHPositiveTD.Explicit.far_high_tilted hθ hz
  have hkc : Explicit.k .farHigh θ≤Explicit.c .farHigh θ z :=
    (lt_min_iff.mp hc.2.2.1).2.le
  have hc1 : Explicit.c .farHigh θ z<1 := (max_lt_iff.mp hc.2.2.2.1).2
  have hh := Blocks.D_redundant (k:=Explicit.k .farHigh θ) (c:=Explicit.c .farHigh θ z)
    ⟨by change 0<NegativeEHPositiveTD.Explicit.k .far .high θ; linarith [hr.1.1],
      by change NegativeEHPositiveTD.Explicit.k .far .high θ≤1; linarith [hr.1.2]⟩
    hkc (by linarith) ht
  exact hh

lemma small_high_pure_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (i : Fin 4) :
    0<baseline .smallHigh (a+z) a z+charge .smallHigh s+
      Blocks.negative .smallHigh (a+z) z (a+z-s) i := by
  fin_cases i
  · exact small_high_ordinary_positive hθ ha hz hs 0
  · exact small_high_ordinary_positive hθ ha hz hs 1
  · exact small_high_ordinary_positive hθ ha hz hs 2
  · have hcmp := small_high_D_lower hθ ⟨hz,by linarith⟩
      (show a+z-s∈Icc 0 frameCap from ⟨by linarith [hθ.1,hs.2],
        by norm_num [frameCap]; linarith [hθ.2,hs.1]⟩)
    exact (small_high_ordinary_positive hθ ha hz hs 0).trans_le (add_le_add le_rfl hcmp)

lemma far_high_pure_positive {a z s : ℝ}
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (i : Fin 4) :
    0<baseline .farHigh (a+z) a z+charge .farHigh s+
      Blocks.negative .farHigh (a+z) z (a+z-s) i := by
  fin_cases i
  · exact far_high_ordinary_positive hθ ha hz hs 0
  · exact far_high_ordinary_positive hθ ha hz hs 1
  · exact far_high_ordinary_positive hθ ha hz hs 2
  · have hcmp := far_high_D_lower hθ ⟨hz,by linarith⟩
      (show a+z-s∈Icc 0 frameCap from ⟨by linarith [hθ.1,hs.2],
        by norm_num [frameCap]; linarith [hθ.2,hs.1]⟩)
    exact (far_high_ordinary_positive hθ ha hz hs 0).trans_le (add_le_add le_rfl hcmp)

/-- The entire small-EH, high-total allocation domain. -/

theorem small_high_scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/6:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (0:ℝ) (1/10)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline .smallHigh (a+z) a z+charge .smallHigh s+
      ∑i,Blocks.block .smallHigh (a+z) z (P i) (N i) i := by
  obtain ⟨i,hi⟩ := HighMass.small_high_to_negative P N hθ ⟨hz,by linarith⟩ hs
    hP hN hPb hNb hbalance
  have hh := small_high_pure_positive hθ ha hz hs i
  linarith

/-- The entire far-EH, high-total allocation domain, including the .005 charge. -/
theorem far_high_scalar_positive {a z s : ℝ} (P N : Fin 4→ℝ)
    (hθ : a+z∈Icc (1/4:ℝ) (7/10)) (ha : 0≤a) (hz : 0≤z)
    (hs : s∈Icc (1/10:ℝ) (1/4)) (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPb : (∑i,P i)≤frameCap-(a+z)) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=a+z-s) :
    0<baseline .farHigh (a+z) a z+charge .farHigh s+
      ∑i,Blocks.block .farHigh (a+z) z (P i) (N i) i := by
  obtain ⟨i,hi⟩ := HighMass.far_high_to_negative P N hθ ⟨hz,by linarith⟩ hs
    hP hN hPb hNb hbalance
  have hh := far_high_pure_positive hθ ha hz hs i
  linarith

end SquaresInCircles.Eight.GlobalGA.NegativeEHBT3.HighScalar
