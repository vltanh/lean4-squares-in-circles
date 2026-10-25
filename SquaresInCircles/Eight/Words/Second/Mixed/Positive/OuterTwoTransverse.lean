module

public import SquaresInCircles.Eight.Words.Second.Mixed.Positive.OuterTwoData
public import SquaresInCircles.Eight.Words.Second.Mixed.TransverseSupport
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts

/-!
# Eight squares: all transverse support ranges for the positive outer target

A stronger separator multiplier and the tangent at zero handle the
whole early contact range.  The later range uses the interior tangent.
Every range is controlled by strict concavity and its actual endpoints.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
open CommonQuarter CorePairGeometry Arithmetic
open PositiveThree (lowerAngle Lower)
open MixedTransverseSupport

def early (φ : ℝ) : ℝ := lower (7/5) (1061/1000) (-c+1449/100000) φ
def late (φ : ℝ) : ℝ := lower g p (-c-k) φ
def upperTransverse (x : ℝ) : ℝ := upper g p (-c-k) x

lemma early_left : (101/100:ℝ)<early 1 := by
  have ht := PointProducts.trig (show (0:ℝ)≤1 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (841/1000:ℝ)<Real.sin 1 := by linarith [ht.1.1]
  have hc : (27/50:ℝ)<Real.cos 1 := by linarith [ht.2.1]
  have hn := lower_sq (g := (7/5:ℝ)) (p := (1061/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num) 1
  have hN : lowerN (7/5) (1061/1000) 1<(609/500:ℝ) := by
    have hsq : (lowerN (7/5) (1061/1000) 1)^2<(609/500:ℝ)^2 := by
      rw [hn]
      norm_num
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<609/500))
  dsimp only [early,lower,c]
  linarith

lemma early_right : (47/50:ℝ)<early (6/5) := by
  have ht := PointProducts.trig (show (0:ℝ)≤6/5 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (233/250:ℝ)<Real.sin (6/5) := by linarith [ht.1.1]
  have hc : (3623/10000:ℝ)<Real.cos (6/5) := by linarith [ht.2.1]
  have hn := lower_sq (g := (7/5:ℝ)) (p := (1061/1000:ℝ))
    (by norm_num) (by norm_num) (by norm_num) (6/5)
  have hN : lowerN (7/5) (1061/1000) (6/5)<(709/500:ℝ) := by
    have hsq : (lowerN (7/5) (1061/1000) (6/5))^2<(709/500:ℝ)^2 := by
      rw [hn]
      norm_num
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<709/500))
  dsimp only [early,lower,c]
  linarith

theorem early_lower {φ : ℝ} (hφ : φ∈Icc (1:ℝ) (6/5)) : (47/50:ℝ)<early φ := by
  have hc : ConcaveOn ℝ (Icc (1:ℝ) (6/5)) early :=
    concave_of_deriv2
      (fun x _ => lower_hasDerivAt (by norm_num) (by norm_num) (by norm_num) (-c+1449/100000) x)
      (fun x _ => lowerD_hasDerivAt (by norm_num) (by norm_num) (by norm_num) x)
      (fun x hx => (lower_curvature (by norm_num) (by norm_num) (by norm_num)
        (show Lower x from ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],
          by linarith [hx.2,pi_hand_enclosure.1]⟩)).le)
  exact concave_gt_of_endpoints hc hφ (by linarith [early_left]) early_right

lemma late_left : (9/10:ℝ)<late (6/5) := by
  have ht := PointProducts.trig (show (0:ℝ)≤6/5 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (93203/100000:ℝ)<Real.sin (6/5) := by linarith [ht.1.1]
  have hc : (7247/20000:ℝ)<Real.cos (6/5) := by linarith [ht.2.1]
  have hn := lower_sq (g := g) (p := p)
    (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) (6/5)
  have hN : lowerN g p (6/5)<(101271/100000:ℝ) := by
    have hsq : (lowerN g p (6/5))^2<(101271/100000:ℝ)^2 := by
      rw [hn]
      norm_num [g,p]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<101271/100000))
  dsimp only [late,lower]
  simp only [c,g,p,k] at hRN ⊢
  linarith

lemma late_aligned : γ<late (Real.pi/2) := by
  have he : late (Real.pi/2)=γ+MixedPrimarySupport.minus g p K 0 := by
    simp [late,lower,lowerN,CircularNorm.norm,CircularNorm.energy,
      MixedPrimarySupport.minus,MixedPrimarySupport.N,K]
    ring
  rw [he]
  linarith [primary_zero]

theorem late_lower {φ : ℝ} (hφ : φ∈Icc (6/5:ℝ) (Real.pi/2)) : γ<late φ := by
  have hc : ConcaveOn ℝ (Icc (6/5:ℝ) (Real.pi/2)) late :=
    concave_of_deriv2
      (fun x _ => lower_hasDerivAt (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) (-c-k) x)
      (fun x _ => lowerD_hasDerivAt (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) x)
      (fun x hx => (lower_curvature (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p])
        (show Lower x from ⟨by dsimp [lowerAngle]; linarith [hx.1,pi_hand_enclosure.2],hx.2⟩)).le)
  exact concave_gt_of_endpoints hc hφ (by norm_num [γ]; linarith [late_left]) late_aligned

lemma upper_aligned : γ<upperTransverse 0 := by
  have he : upperTransverse 0=late (Real.pi/2) := by
    simp [upperTransverse,upper,upperN,late,lower,lowerN,CircularNorm.norm,CircularNorm.energy]
  rw [he]
  exact late_aligned

lemma upper_right : (69/50:ℝ)<upperTransverse (7/10) := by
  have ht := PointProducts.trig (show (0:ℝ)≤7/10 by norm_num)
  norm_num [ReferenceTrig.sin11,sin9,sin7,cos10,cos8,ReferenceTrig.cos12] at ht
  have hs : (3221/5000:ℝ)<Real.sin (7/10) ∧ Real.sin (7/10)<(32211/50000:ℝ) :=
    ⟨by linarith [ht.1.1],by linarith [ht.1.2]⟩
  have hc : (478/625:ℝ)<Real.cos (7/10) := by linarith [ht.2.1]
  have hn := upper_sq (g := g) (p := p)
    (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) (7/10)
  have hN : upperN g p (7/10)<(15587/10000:ℝ) := by
    have hsq : (upperN g p (7/10))^2<(15587/10000:ℝ)^2 := by
      rw [hn]
      norm_num [g,p]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hRN := (mul_lt_mul_of_pos_left hN
    (by linarith [radius_bounds.1] : 0<CommonQuarter.radius)).trans
      (mul_lt_mul_of_pos_right radius_bounds.2 (by norm_num : (0:ℝ)<15587/10000))
  dsimp only [upperTransverse,upper]
  simp only [c,g,p,k] at hRN ⊢
  linarith [pi_hand_enclosure.1]

theorem upper_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (7/10)) : γ<upperTransverse x :=
  concave_gt_of_endpoints
    (upper_concave (by norm_num [g]) (by norm_num [p]) (by norm_num [g,p]) (-c-k))
    hx upper_aligned (by norm_num [γ]; linarith [upper_right])

end SquaresInCircles.Eight.SecondWord.MixedTwo.PositiveOuter
