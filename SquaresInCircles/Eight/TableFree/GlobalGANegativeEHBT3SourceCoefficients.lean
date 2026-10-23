module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3Scalar
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHBT3LowStress

/-!
# Coefficients needed at the original EH1/BT3 source

Uncompiled whole-domain bounds. The H comparison needs the literal
interval [1/2,17/20], and the far multiplier needs [3/5,4/5]. These are
proved for the actual selected family, independently of any endpoint
allocation or favorable source owner.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma small_high_k {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Explicit.k .smallHigh θ∈Icc (1/2:ℝ) (17/20) := by
  let x : ℝ := θ-1/6
  have hx : x∈Icc (0:ℝ) (8/15) := ⟨by dsimp [x]; linarith [hθ.1],by dsimp [x]; linarith [hθ.2]⟩
  have hlow : 0≤(2609/5000:ℝ)-(1489/2500)*x+(527/1250)*x^2 := by
    nlinarith [sq_nonneg ((527/625:ℝ)*x-1489/2500)]
  have hupp : 0≤(2609/5000:ℝ)-(1489/2500)*(8/15+x)+
      (527/1250)*((8/15)^2+(8/15)*x+x^2) := by
    nlinarith [sq_nonneg ((527/625:ℝ)*x-(1489/2500-(527/1250)*(8/15)))]
  have hprod0 := mul_nonneg hx.1 hlow
  have hprod1 := mul_nonneg (sub_nonneg.mpr hx.2) hupp
  have h0 : Explicit.k .smallHigh θ-1673/2500=
      x*((2609/5000)-(1489/2500)*x+(527/1250)*x^2) := by
    dsimp [Explicit.k,L,x]; ring
  have h1 : (7104683/8437500:ℝ)-Explicit.k .smallHigh θ=
      (8/15-x)*((2609/5000)-(1489/2500)*(8/15+x)+
        (527/1250)*((8/15)^2+(8/15)*x+x^2)) := by
    dsimp [Explicit.k,L,x]; ring
  exact ⟨by linarith,by linarith⟩

lemma coefficients (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (Scalar.left f) (Scalar.right f)) (hz : z∈Icc 0 θ) :
    Explicit.k f θ∈Icc (1/2:ℝ) (17/20) ∧
    0<Explicit.l f θ ∧ 0<Explicit.m f θ ∧ Explicit.k f θ≤Explicit.l f θ := by
  cases f
  · refine ⟨⟨?_,?_⟩,by norm_num [Explicit.l],?_,?_⟩
    all_goals dsimp [Explicit.k,Explicit.l,Explicit.m]; linarith [hθ.1,hθ.2]
  · have hb := NonnegativeTotals.Explicit.base_bounds .triangle (Blocks.small_high_domain hθ)
    exact ⟨small_high_k hθ,hb.l_positive,hb.c_positive,(Blocks.small_high_pairs hθ hz 1).2.1⟩
  · have hr := FarLow.coefficient_ranges hθ hz
    exact ⟨by norm_num [Explicit.k],by linarith [hr.2.1.1],
      by linarith [hr.2.2.1.1],by rw [hr.1]; linarith [hr.2.1.1]⟩
  · have hr := NegativeEHPositiveTD.Explicit.far_high_ranges hθ
    exact ⟨⟨by linarith [hr.1.1],by linarith [hr.1.2]⟩,
      by linarith [hr.2.1.1],by linarith [hr.2.2.1.1],
      by linarith [hr.1.2,hr.2.1.1]⟩

lemma far_k (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Scalar.left f) (Scalar.right f)) (hf : far f=true) :
    Explicit.k f θ∈Icc (3/5:ℝ) (4/5) := by
  cases f
  · simp [far] at hf
  · simp [far] at hf
  · norm_num [Explicit.k]
  · have hr := (NegativeEHPositiveTD.Explicit.far_high_ranges hθ).1
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩

lemma full_pair_positive (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (Scalar.left f) (Scalar.right f)) (hz : z∈Icc 0 θ) (i : Fin 4) :
    0<Blocks.p f θ z i := by
  have hc := coefficients f hθ hz
  have hzf : z∈Icc 0 frameCap := ⟨hz.1,hz.2.trans (Scalar.frame_domain f hθ).2⟩
  have hrot : 0<Explicit.c f θ z := PositiveTD.tilted_pos hc.2.2.1 hzf
  fin_cases i <;> simp only [Blocks.p,PositiveBT3.pWeights,
    Matrix.cons_val_succ,Matrix.cons_val_zero]
  · linarith [hc.1.1]
  · linarith [hc.1.1]
  · exact lt_min hc.2.1 hc.2.2.1
  · exact lt_min (by norm_num) hrot

lemma epsilon_nonnegative (f : Family) : 0≤epsilon f := by
  cases f <;> norm_num [epsilon,far]

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHBT3.Source
