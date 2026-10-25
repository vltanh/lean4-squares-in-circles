module

public import SquaresInCircles.Eight.TableFree.GlobalGAOneAngle

/-!
# Two-error bounds on the original high-GA support points

Uncompiled source.  The two signed error budgets come directly from the
original seven-cycle variations.  The support identity is exact for the
actual point and does not assume a maximizing radial state.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
open Candidate PositiveAngularEnvelope

def pairF (p q a b : ℝ) : ℝ := q*Real.cos b+p*Real.sin a
def pairG (p q a b : ℝ) : ℝ := p*Real.cos a+q*Real.sin b

def pairIncrement (p q a b : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth a-1)+q*(edgeWidth b-1)-
    (pairF p q a b*P.a+pairG p q a b*P.y)+
    fullSupport q p+charge*(a+b)

theorem pair_force_norm (p q a b : ℝ) :
    Real.sqrt ((pairF p q a b)^2+(pairG p q a b)^2)=pairNorm p q (a+b) := by
  simpa [rotatedPair,pairF,pairG,pairNorm_symm,add_comm] using
    rotatedPair_norm q p a b

theorem pair_full_identity {p q a b : ℝ}
    (ha : |a|≤frameCap) (hb : |b|≤frameCap) :
    p*(edgeWidth a-1)+q*(edgeWidth b-1)-
      fullSupport (pairF p q a b) (pairG p q a b)+
      fullSupport q p+charge*(a+b)=chargedPair p q a b := by
  rw [fullSupport_pair p q]
  unfold fullSupport
  rw [pair_force_norm]
  have ha' := width_add_half_phi ha
  have hb' := width_add_half_phi hb
  dsimp [chargedPair,pairF,pairG,PositiveAngularEnvelope.phi] at *
  nlinarith [congrArg (fun x : ℝ => p*x) ha',
    congrArg (fun x : ℝ => q*x) hb']

theorem actual_pair_lower {r p q a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (ha : |a|≤frameCap) (hb : |b|≤frameCap) :
    chargedPair p q a b≤pairIncrement p q a b P := by
  have hs := actual_full_support (f:=pairF p q a b) (g:=pairG p q a b) hy hc hr
  rw [← pair_full_identity ha hb]
  dsimp [pairIncrement]
  linarith

theorem two_positive_errors_le (θ : Vertex → ℝ) {i j : Vertex} (hij : i≠j) :
    positivePart (delta θ i)+positivePart (delta θ j)≤positiveVariation θ := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s:=({i,j}:Finset Vertex)) (t:=Finset.univ)
    (f:=fun v => positivePart (delta θ v))
    (by simp) (fun v _ _ => positivePart_nonneg (delta θ v))
  simpa [positiveVariation,hij] using h

theorem two_negative_errors_le (θ : Vertex → ℝ) {i j : Vertex} (hij : i≠j) :
    negativePart (delta θ i)+negativePart (delta θ j)≤negativeVariation θ := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s:=({i,j}:Finset Vertex)) (t:=Finset.univ)
    (f:=fun v => negativePart (delta θ v))
    (by simp) (fun v _ _ => negativePart_nonneg (delta θ v))
  simpa [negativeVariation,hij] using h

theorem pair_error_bounds {a b : ℝ}
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    |a|≤frameCap ∧ |b|≤frameCap ∧ |a+b|≤frameCap := by
  have ha := positive_sub_negative a
  have hb := positive_sub_negative b
  have hpa := positivePart_nonneg a
  have hpb := positivePart_nonneg b
  have hna := negativePart_nonneg a
  have hnb := negativePart_nonneg b
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem original_pair_budgets {θ : Vertex → ℝ} {i j : Vertex}
    (hP : positiveVariation θ≤frameCap)
    (hN : negativeVariation θ≤frameCap) (hij : i≠j) :
    positivePart (delta θ i)+positivePart (delta θ j)≤frameCap ∧
      negativePart (delta θ i)+negativePart (delta θ j)≤frameCap :=
  ⟨(two_positive_errors_le θ hij).trans hP,
    (two_negative_errors_le θ hij).trans hN⟩

theorem original_error_bound {θ : Vertex → ℝ}
    (hP : positiveVariation θ≤frameCap) (hN : negativeVariation θ≤frameCap)
    (i : Vertex) : |delta θ i|≤frameCap := by
  have hp := (positive_error_le_variation θ i).trans hP
  have hn := (negative_error_le_variation θ i).trans hN
  have he := positive_sub_negative (delta θ i)
  exact abs_le.mpr ⟨by linarith [positivePart_nonneg (delta θ i)],
    by linarith [negativePart_nonneg (delta θ i)]⟩

theorem actual_G_pair {r a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(576/10000:ℝ)<pairIncrement k l a b P := by
  have he := pair_error_bounds hP hN
  exact (G_pair_lower hP hN).trans_le (actual_pair_lower hy hc hr he.1 he.2.1)

theorem actual_H_pair {r a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(22/10000:ℝ)<pairIncrement k 1 a b P := by
  have he := pair_error_bounds hP hN
  exact (H_pair_lower hP hN).trans_le (actual_pair_lower hy hc hr he.1 he.2.1)

theorem actual_B_pair {r a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    -(44/10000:ℝ)<pairIncrement l 2 a b P := by
  have he := pair_error_bounds hP hN
  exact (B_pair_lower hP hN).trans_le (actual_pair_lower hy hc hr he.1 he.2.1)

end SquaresInCircles.Eight.TableFree.GlobalGA.Secondary
