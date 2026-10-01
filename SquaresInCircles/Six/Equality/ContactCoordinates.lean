import SquaresInCircles.Six.Equality.LocalCenters

/-!
# Eight candidate-frame contacts determine all six centers

This is a scalar geometric theorem. Four central contacts and four exterior
contacts, with their original directions, are summed with the exact positive
candidate multipliers. Each of five contained exterior squares has its exact
support upper bound. The sum of those bounds equals the weighted threshold,
so every bound is tight. Unique disk support then fixes all exterior centers;
the opposite central inequalities fix the central center.

No angle-domain classification, balanced-closure theorem, finite cover or
certificate result is imported. The argument does not require an assumed
coordinate equality or a separate rigidity oracle.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality.ContactCoordinates
open Stress Normalization

/-- E,N,W,D,S signed side-frame coordinates, after the angles are fixed. -/
structure Contacts (c : Point) (a b : Fin 5 → ℝ) : Prop where
  east : 1+c.1 ≤ a 0
  north : 1+c.2 ≤ a 1
  west : 1 ≤ a 2+c.1
  south : 1 ≤ a 4+c.2
  northwest : 1 ≤ a 2-b 1
  eastsouth : 1 ≤ a 4+b 0
  westDiagonal : 1/2+Six.hStar ≤ Six.hStar*(a 3+b 3)-b 2
  diagonalSouth : 1/2+Six.hStar ≤ b 4+Six.hStar*(a 3-b 3)

structure Coordinates (a b : Fin 5 → ℝ) : Prop where
  east_radial : a 0=1+Six.sStar
  east_transverse : b 0=Six.sStar
  north_radial : a 1=1+Six.sStar
  north_transverse : b 1= -Six.sStar
  west_radial : a 2=1-Six.sStar
  west_transverse : b 2= -Six.tStar
  south_radial : a 4=1-Six.sStar
  south_transverse : b 4=Six.tStar
  diagonal_radial : a 3=rhoStar
  diagonal_transverse : b 3=0

private def northUpper : ℝ := northVertex 1 (-rStar)
private def westUpper : ℝ := northVertex (1+rStar) (-mStar)

private lemma north_positive_support :
    scalarSupport Six.radius 1 rStar=northUpper := by
  calc
    scalarSupport Six.radius 1 rStar=scalarSupport Six.radius 1 (-rStar) :=
      (scalarSupport_neg_second _ _ _).symm
    _=northUpper := candidate_north_exact_support

private lemma west_positive_support :
    scalarSupport Six.radius (1+rStar) mStar=westUpper := by
  calc
    scalarSupport Six.radius (1+rStar) mStar=
        scalarSupport Six.radius (1+rStar) (-mStar) :=
      (scalarSupport_neg_second _ _ _).symm
    _=westUpper := candidate_west_exact_support

private lemma total_upper_identity :
    2*northUpper+2*westUpper+diagonalK*rhoStar=4+2*rStar+mStar+diagonalK := by
  have hp := pairBase_vertex_identity
  have hd := pairBase_diagonal_identity
  change 2*pairBase+diagonalK*(1-rhoStar)=0 at hd
  dsimp [northUpper,westUpper]
  nlinarith only [hp,hd]

/-- The eight real contacts yield the lower bound on the five support works. -/
lemma work_lower {c : Point} {a b : Fin 5 → ℝ} (h : Contacts c a b) :
    4+2*rStar+mStar+diagonalK ≤
      (a 0+rStar*b 0)+(a 1-rStar*b 1)+
      ((1+rStar)*a 2-mStar*b 2)+((1+rStar)*a 4+mStar*b 4)+diagonalK*a 3 := by
  have hNW := mul_le_mul_of_nonneg_left h.northwest rStar_pos.le
  have hES := mul_le_mul_of_nonneg_left h.eastsouth rStar_pos.le
  have hWD := mul_le_mul_of_nonneg_left h.westDiagonal mStar_pos.le
  have hDS := mul_le_mul_of_nonneg_left h.diagonalSouth mStar_pos.le
  dsimp [diagonalK]
  nlinarith only [h.east,h.north,h.west,h.south,hNW,hES,hWD,hDS]

/-- Equality propagates to every individual exterior support without invoking
an equality case of either a search procedure or a global pattern theorem. -/
theorem support_tight {c : Point} {a b : Fin 5 → ℝ}
    (h : Contacts c a b)
    (hbox : ∀ i, (|a i|+1/2)^2+(|b i|+1/2)^2 ≤ Six.radius^2) :
    a 0+rStar*b 0=scalarSupport Six.radius 1 rStar ∧
    a 1-rStar*b 1=scalarSupport Six.radius 1 (-rStar) ∧
    (1+rStar)*a 2-mStar*b 2=scalarSupport Six.radius (1+rStar) (-mStar) ∧
    (1+rStar)*a 4+mStar*b 4=scalarSupport Six.radius (1+rStar) mStar ∧
    diagonalK*a 3=scalarSupport Six.radius diagonalK 0 := by
  have he : a 0+rStar*b 0 ≤ northUpper := by
    simpa only [one_mul,north_positive_support] using
      scalar_center_support (x := (1:ℝ)) (y := rStar) radius_gt_half (hbox 0)
  have hn : a 1-rStar*b 1 ≤ northUpper := by
    simpa only [one_mul,neg_mul,sub_eq_add_neg,candidate_north_exact_support,northUpper] using
      scalar_center_support (x := (1:ℝ)) (y := -rStar) radius_gt_half (hbox 1)
  have hw : (1+rStar)*a 2-mStar*b 2 ≤ westUpper := by
    simpa only [neg_mul,sub_eq_add_neg,candidate_west_exact_support,westUpper] using
      scalar_center_support (x := 1+rStar) (y := -mStar) radius_gt_half (hbox 2)
  have hs : (1+rStar)*a 4+mStar*b 4 ≤ westUpper := by
    simpa only [west_positive_support] using
      scalar_center_support (x := 1+rStar) (y := mStar) radius_gt_half (hbox 4)
  have hD : diagonalK*a 3 ≤ diagonalK*rhoStar := by
    have hd := scalar_center_support (x := diagonalK) (y := (0:ℝ)) radius_gt_half (hbox 3)
    rw [scalarSupport_positive_axis diagonalK_pos.le] at hd
    change diagonalK*a 3+0*b 3 ≤ rhoStar*diagonalK at hd
    linarith
  have hlo := work_lower h
  have hid := total_upper_identity
  have heq : a 0+rStar*b 0=northUpper := by nlinarith only [he,hn,hw,hs,hD,hlo,hid]
  have hnq : a 1-rStar*b 1=northUpper := by nlinarith only [he,hn,hw,hs,hD,hlo,hid]
  have hwq : (1+rStar)*a 2-mStar*b 2=westUpper := by nlinarith only [he,hn,hw,hs,hD,hlo,hid]
  have hsq : (1+rStar)*a 4+mStar*b 4=westUpper := by nlinarith only [he,hn,hw,hs,hD,hlo,hid]
  have hdq : diagonalK*a 3=diagonalK*rhoStar := by nlinarith only [he,hn,hw,hs,hD,hlo,hid]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [north_positive_support] using heq
  · simpa only [candidate_north_exact_support,northUpper] using hnq
  · simpa only [candidate_west_exact_support,westUpper] using hwq
  · simpa only [west_positive_support] using hsq
  · rw [scalarSupport_positive_axis diagonalK_pos.le]
    change diagonalK*a 3=rhoStar*diagonalK
    rw [hdq,mul_comm]

/-- A finite contact graph and actual disk containment fix all local coordinates. -/
theorem coordinates_of_contacts {c : Point} {a b : Fin 5 → ℝ}
    (h : Contacts c a b)
    (hbox : ∀ i, (|a i|+1/2)^2+(|b i|+1/2)^2 ≤ Six.radius^2) : Coordinates a b := by
  obtain ⟨he,hn,hw,hs,hd⟩ := support_tight h hbox
  have ce := north_center_unique (sgn := (1:ℝ)) (Or.inl rfl) (hbox 0)
    (by simpa only [one_mul] using he)
  have cn := north_center_unique (sgn := (-1:ℝ)) (Or.inr rfl) (hbox 1)
    (by simpa only [neg_one_mul,neg_mul,one_mul,sub_eq_add_neg] using hn)
  have cw := west_center_unique (sgn := (-1:ℝ)) (Or.inr rfl) (hbox 2)
    (by simpa only [neg_one_mul,neg_mul,one_mul,sub_eq_add_neg] using hw)
  have cs := west_center_unique (sgn := (1:ℝ)) (Or.inl rfl) (hbox 4)
    (by simpa only [one_mul] using hs)
  have cd := diagonal_center_unique (hbox 3) hd
  exact ⟨ce.1,by simpa using ce.2,cn.1,by simpa using cn.2,
    cw.1,by simpa using cw.2,cs.1,by simpa using cs.2,cd.1,cd.2⟩

/-- Opposite central inequalities determine the central center once the exterior
radial coordinates have been fixed. No independent center-rigidity premise. -/
theorem center_of_contacts {c : Point} {a b : Fin 5 → ℝ}
    (h : Contacts c a b) (hc : Coordinates a b) : c=(Six.sStar,Six.sStar) := by
  apply Prod.ext
  · have he := h.east
    have hw := h.west
    rw [hc.east_radial] at he
    rw [hc.west_radial] at hw
    linarith
  · have hn := h.north
    have hs := h.south
    rw [hc.north_radial] at hn
    rw [hc.south_radial] at hs
    linarith

end SquaresInCircles.Six.Equality.ContactCoordinates
