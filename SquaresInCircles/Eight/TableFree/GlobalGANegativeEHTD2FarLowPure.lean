module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2FarLowSlopes
public import SquaresInCircles.Eight.TableFree.OrdinaryMixedShortReserve

/-!
# All pure positive and negative far-low EH alternatives

Uncompiled source of the far-low companion. Positive surplus is moved
only in the actual EH magnitude, with all coefficients fixed. Its first
endpoint is max(.1,theta). Negative surplus is concave in that magnitude
and retains both intrinsic endpoints .1 and theta. The distinguished D
positive term remains its literal linear cost.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLowPure
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
    convert (NegativeEH.G_hasDerivAt s).sub
      (((hasDerivAt_id s).sub_const θ).const_mul (Blocks.dCost+Explicit.errorCharge .far)) using 1
    · funext t
      rw [positivePart,Blocks.positive_D]
      ring
    · simp [positiveSlope]
  · have hU := (U_hasDerivAt
        (show 0<Blocks.p .far .low θ z i by linarith [hp.1])
        (show 0<Blocks.q .far .low θ z i by linarith [hp.1,hp.2.1]) hx).
      comp s ((hasDerivAt_id s).sub_const θ)
    convert ((NegativeEH.G_hasDerivAt s).add hU).sub
      (((hasDerivAt_id s).sub_const θ).const_mul (Explicit.errorCharge .far)) using 1
    · funext t
      simp only [positivePart,Blocks.positive,ChargedHybridConcentration.positive,
        PositiveTD.Hybrid.positive,if_neg hi]
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
  · simp only [positiveSlope,if_pos hi]
    dsimp [Blocks.dCost,Explicit.errorCharge,NegativeEH.epsilon]
    linarith [diagonal_bounds.2]
  · have hx : s-θ∈Icc 0 frameCap :=
      ⟨(le_max_right _ _).trans hs.1 |> sub_nonneg.mpr,
        by norm_num [frameCap]; linarith [hs.2,hθ.1]⟩
    have hU := NegativeDEPositiveTD.OrdinarySlope.positive_derivative_whole
      (show 0<Blocks.p .far .low θ z i by linarith [hp.1]) hp.2.1
      (show Blocks.q .far .low θ z i≤2*Blocks.p .far .low θ z i by linarith [hp.1,hp.2.2]) hx
    simp only [positiveSlope,if_neg hi]
    dsimp [Explicit.errorCharge,NegativeEH.epsilon]
    linarith [FarLowSlopes.q_upper hθ hz i]

lemma positive_monotone {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4))
    (hz : z∈Icc 0 θ) (i : Fin 4) :
    MonotoneOn (positivePart θ z i) (Icc (max (1/10) θ) (1/4)) :=
  monoOn_of_hasDeriv_nonneg
    (fun s hs => (positive_derivative hθ hz hs i).continuousAt.continuousWithinAt)
    (fun s hs => positive_derivative hθ hz (Ioo_subset_Icc_self hs) i)
    (fun s hs => (positive_slope hθ hz (Ioo_subset_Icc_self hs) i).le)

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
    simp only [positivePart,Blocks.positive,ChargedHybridConcentration.positive,
      PositiveTD.Hybrid.positive,Blocks.p,Blocks.q,Explicit.p,Explicit.q,
      Explicit.errorCharge,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk,
      Fin.isValue,reduceCtorEq,if_false]
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
    rw [positivePart,Blocks.positive_D]
    dsimp [Blocks.dCost,Explicit.errorCharge]
    linarith

theorem positive_positive {a z s : ℝ} (hθ : a+z∈Icc (0:ℝ) (1/4))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (1/10:ℝ) (1/4))
    (horder : a+z≤s) (i : Fin 4) :
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

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.FarLowPure
