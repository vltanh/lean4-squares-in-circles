module

public import SquaresInCircles.Eight.Owners.GA.Negative.Primary.Stress
public import SquaresInCircles.Eight.Owners.GA.One.Angle

/-!
# Eight squares: whole-domain four-circle reserve after deleting negative arguments

Each erased argument decreases both signed variation sums (`erased_pair_budgets`). The one- and
two-error circle estimates therefore apply to the reference expression directly, although its
angular arguments need not sum to zero (`zero_reference_reserve`, `two_reference_reserve`). Their
charges stay in the stress identity.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GlobalGA.NegativePrimary

open Candidate Secondary

theorem erase_positive_le (p : Bool) (d : ℝ) :
    positivePart (erase p d)≤positivePart d := by
  cases p
  · simp [erase]
  · simpa [erase] using positivePart_nonneg d

theorem erase_negative_le (p : Bool) (d : ℝ) :
    negativePart (erase p d)≤negativePart d := by
  cases p
  · simp [erase]
  · simpa [erase] using negativePart_nonneg d

theorem erase_abs_bound (p : Bool) {d : ℝ} (hd : |d|≤frameCap) :
    |erase p d|≤frameCap := by
  cases p
  · simpa [erase] using hd
  · norm_num [erase,frameCap]

theorem erased_pair_budgets {θ : Vertex→ℝ} {i j : Vertex}
    (hP : positiveVariation θ≤frameCap) (hN : negativeVariation θ≤frameCap)
    (hij : i≠j) (p r : Bool) :
    positivePart (erase p (delta θ i))+positivePart (erase r (delta θ j))≤frameCap ∧
      negativePart (erase p (delta θ i))+negativePart (erase r (delta θ j))≤frameCap := by
  have hh := original_pair_budgets hP hN hij
  exact ⟨(add_le_add (erase_positive_le p _) (erase_positive_le r _)).trans hh.1,
    (add_le_add (erase_negative_le p _) (erase_negative_le r _)).trans hh.2⟩

theorem zero_reference_reserve {q : ℝ} {C : SignedCycle} (ga ab td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    (7/10000:ℝ)<zeroReference ga ab td C := by
  have hn : negativeVariation C.theta≤frameCap := by rwa [← variations_equal]
  have hH := actual_H_one (x:=delta C.theta E) hHy (hc H) hq
    (original_error_bound hvar hn E)
  have hgb := erased_pair_budgets (i:=H) (j:=G) hvar hn (by norm_num [H,G]) false ga
  simp only [erase_false] at hgb
  have hG := actual_G_pair (P:=(C.point G).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (by simpa using hc G) hq hgb.1 hgb.2
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab false
  simp only [erase_false] at hbb
  have hB := actual_B_pair (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) td false
  simp only [erase_false] at hdb
  have hde := pair_error_bounds hdb.1 hdb.2
  have hD := actual_dIncrement_nonneg (P:=(C.point D).reflect)
    (by simpa using hs D)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  unfold zeroReference
  linarith [baseStress_reserve]

theorem two_reference_reserve {q : ℝ} {C : SignedCycle} (ga ab td : Bool)
    (hs : ∀i,(C.point i).Sorted) (hc : ∀i,(C.point i).Contained q)
    (hq : q≤qCap) (hHy : 0≤(C.point H).y) (hGy : (C.point G).y≤0)
    (hBy : (C.point B).y≤0) (hDy : (C.point D).y≤0)
    (hvar : positiveVariation C.theta≤frameCap) :
    (561/10000:ℝ)<twoReference ga ab td C := by
  have hn : negativeVariation C.theta≤frameCap := by rwa [← variations_equal]
  have hhb := original_pair_budgets (i:=H) (j:=E) hvar hn (by norm_num [H,E])
  have hH := actual_H_pair hHy (hc H) hq hhb.1 hhb.2
  have hG := actual_G_one (P:=(C.point G).reflect)
    (x:=erase ga (delta C.theta G))
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hGy)
    (by simpa using hc G) hq (erase_abs_bound ga (original_error_bound hvar hn G))
  have hbb := erased_pair_budgets (i:=A) (j:=B) hvar hn (by norm_num [A,B]) ab false
  simp only [erase_false] at hbb
  have hB := actual_B_pair (P:=(C.point B).reflect)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa using hc B) hq hbb.1 hbb.2
  have hdb := erased_pair_budgets (i:=T) (j:=D) hvar hn (by norm_num [T,D]) td false
  simp only [erase_false] at hdb
  have hde := pair_error_bounds hdb.1 hdb.2
  have hD := actual_dIncrement_nonneg (P:=(C.point D).reflect)
    (by simpa using hs D)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hq hde.1 hde.2.1 hde.2.2
  unfold twoReference
  linarith [baseStress_reserve]

end SquaresInCircles.Eight.GlobalGA.NegativePrimary
