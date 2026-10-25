module

public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3Blocks
public import SquaresInCircles.Eight.Owners.GA.Secant.DCorrectionGrowth

/-!
# Eight squares: all pure-positive DE3 / BT3 allocations have the same intrinsic endpoint

The total angle and the original A/BT split stay fixed. The
secant-D correction is used across its actual sorted-support switch.
Ordinary positive mass is paid by the whole-interval U lower bound;
the original TD0 singleton uses the proved secant penalty comparison.
The closed zero-surplus endpoint is included for every block index.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.PositivePure
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma q_upper (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 3) :
    Explicit.q f θ i≤(5821/5000:ℝ) := by
  cases f
  · have hm := (Explicit.low_bounds hθ).2
    fin_cases i
    · norm_num [Explicit.q]
    · norm_num [Explicit.q,Explicit.l]
    · change max 1 (Explicit.m .low θ)≤(5821/5000:ℝ)
      exact max_le (by norm_num) hm.2
  · exact (Explicit.high_q_bounds hθ i).2.le.trans (by norm_num)

lemma ordinary_lower (f : Family) {θ t : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f))
    (ht : t∈Icc 0 frameCap) (i : Fin 3) :
    -(109/200)*(5821/5000)*t≤Explicit.U f θ i t := by
  have hp := Explicit.family_pairs f hθ i
  have hu := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le
    hp.1 hp.2.1 hp.2.2 ht
  have hq := mul_le_mul_of_nonneg_right (q_upper f hθ i) ht.1
  change -(109/200)*Explicit.q f θ i*t≤Explicit.U f θ i t at hu
  nlinarith only [hu,hq]

/-- The coefficients are evaluated at a+z, not at the varying DE magnitude. -/
theorem ordinary_intrinsic_lower (f : Family) {a z s : ℝ}
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) frameCap) (i : Fin 3) :
    Explicit.baseline f a z (a+z)≤
      Explicit.baseline f a z s+Explicit.U f (a+z) i (s-(a+z)) := by
  have ht := Explicit.frame_domain f hθ
  obtain ⟨_,_,_,_,hc,_⟩ := Explicit.source_coefficients f hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
  have hsf : s∈Icc 0 frameCap := ⟨ht.1.trans hs.1,hs.2⟩
  have hd : s-(a+z)∈Icc 0 frameCap :=
    ⟨sub_nonneg.mpr hs.1,by linarith [hs.2,ht.1]⟩
  have hg := SecantD.PositiveEndpoint.correction_growth hc ht hsf hs.1
  have hu := ordinary_lower f hθ hd i
  rw [Explicit.baseline_correction f a z (a+z),
    Explicit.baseline_correction f a z s]
  nlinarith only [hg,hu,hd.1]

/-- The actual D coefficient is max(sec s,c), including its weak support tie. -/
theorem D_intrinsic_lower (f : Family) {a z s : ℝ}
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) frameCap) :
    Explicit.baseline f a z (a+z)≤Explicit.baseline f a z s+
      Blocks.positive f (a+z) z s (s-(a+z)) 3 := by
  have ht := Explicit.frame_domain f hθ
  obtain ⟨_,_,_,_,hc,_⟩ := Explicit.source_coefficients f hθ
    (show z∈Icc 0 (a+z) from ⟨hz,by linarith⟩)
  have hh := SecantD.PositiveEndpoint.intrinsic_lower hc ht hs
  rw [Blocks.positive_D,Explicit.baseline_correction f a z (a+z),
    Explicit.baseline_correction f a z s]
  dsimp [Explicit.gamma]
  linarith only [hh]

theorem block_intrinsic_lower (f : Family) {a z s : ℝ}
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) frameCap) (i : Fin 4) :
    Explicit.baseline f a z (a+z)≤Explicit.baseline f a z s+
      Blocks.positive f (a+z) z s (s-(a+z)) i := by
  by_cases hi : i=3
  · subst i
    exact D_intrinsic_lower f hθ ha hz hs
  · have hlt : i.val<3 := by
      have h4 := i.isLt
      have h3 : i.val≠3 := fun h => hi (Fin.ext h)
      omega
    obtain ⟨j,hj⟩ : ∃j : Fin 3,j.castSucc=i := ⟨⟨i.val,hlt⟩,Fin.ext rfl⟩
    subst i
    rw [Blocks.positive_ordinary]
    exact ordinary_intrinsic_lower f hθ ha hz hs j

/-- Every positive-surplus concentration alternative, including s=theta. -/
theorem pure_intrinsic_lower (f : Family) {a z s : ℝ}
    (hθ : a+z∈Icc (Explicit.left f) (Explicit.right f))
    (ha : 0≤a) (hz : 0≤z) (hs : s∈Icc (a+z) frameCap) (i j : Fin 4) :
    Explicit.baseline f a z (a+z)≤Explicit.baseline f a z s+
      Blocks.pure f (a+z) z s i j := by
  by_cases he : s≤a+z
  · have hsEq : s=a+z := le_antisymm he hs.1
    subst s
    simp [Blocks.pure,ChargedHybridConcentration.pure,V_zero]
  · have hh := block_intrinsic_lower f hθ ha hz hs i
    simpa only [Blocks.pure,ChargedHybridConcentration.pure,ite_eq_right he,
      Blocks.positive] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.PositivePure
