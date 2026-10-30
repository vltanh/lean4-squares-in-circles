module

public import SquaresInCircles.Eight.Equality
public import SquaresInCircles.Eight.BoundaryReduction

/-!
# Eight squares: the parameters of the central square

Every unit square is, as a set of points, the central square of parameters with the same centre
and with the frame parameter `w` in the half-open interval `[1 - √2, √2 - 1)`
(`central_parameters_exist`). One of the four quarter turns of its frame makes an angle in
`[-π/4, π/4)` with the horizontal (`halfopen_quarter_exists`), and for that frame `(c, s)` the
parameter is recovered algebraically as `w = s/(1 + c)` (`halfAngle_recover`,
`halfAngle_halfopen`). The lower end of the interval is included and the upper end excluded, as in
the admissible domain, so a frame along a diagonal gets only one parameter.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ExactFamily
open Coordinates EqualityParameters

theorem sameSquare_of_center_physical {K L : UnitSquare}
    (hc : K.center=L.center) (hf : SamePhysicalFrame K L) : SameSquare K L := by
  have ha : SameAxes L K := by
    rcases hf with h | h | h | h
    · right
      dsimp [relativeS]
      rw [h.1,h.2]
      ring
    · left
      dsimp [relativeC]
      rw [h.1,h.2]
      ring
    · right
      dsimp [relativeS]
      rw [h.1,h.2]
      ring
    · left
      dsimp [relativeC]
      rw [h.1,h.2]
      ring
  have ho := same_axes_open hc ha
  exact ⟨ho,same_open_same_closed K L ho⟩

theorem halfopen_quarter_exists (K : UnitSquare) :
    ∃ k : Fin 4, 0<(turnSquare k K).cosine ∧
      -(turnSquare k K).cosine≤(turnSquare k K).sine ∧
      (turnSquare k K).sine<(turnSquare k K).cosine := by
  by_cases hc : 0<K.cosine
  · by_cases hs : K.sine < -K.cosine
    · refine ⟨1,?_⟩
      norm_num [turnSquare]
      exact ⟨by linarith,by linarith,by linarith⟩
    · have hsl : -K.cosine≤K.sine := le_of_not_gt hs
      by_cases hsu : K.sine<K.cosine
      · exact ⟨0,by simpa [turnSquare] using And.intro hc ⟨hsl,hsu⟩⟩
      · refine ⟨3,?_⟩
        have hh : K.cosine≤K.sine := le_of_not_gt hsu
        norm_num [turnSquare]
        exact ⟨by linarith,by linarith,by linarith⟩
  · have hc' : K.cosine≤0 := le_of_not_gt hc
    by_cases hs : 0<K.sine
    · by_cases hu : -K.cosine<K.sine
      · refine ⟨3,?_⟩
        norm_num [turnSquare]
        exact ⟨hs,by linarith,hu⟩
      · refine ⟨2,?_⟩
        have hh : K.sine≤ -K.cosine := le_of_not_gt hu
        norm_num [turnSquare]
        exact ⟨by linarith,by linarith,by linarith⟩
    · have hs' : K.sine≤0 := le_of_not_gt hs
      by_cases hcs : K.cosine<K.sine
      · refine ⟨2,?_⟩
        norm_num [turnSquare]
        exact ⟨by linarith,by linarith,by linarith⟩
      · have hsc : K.sine≤K.cosine := le_of_not_gt hcs
        have hsneg : K.sine<0 := by
          by_contra! hn
          have hsz : K.sine=0 := by linarith
          have hcz : K.cosine=0 := by linarith
          nlinarith [K.unit]
        refine ⟨1,?_⟩
        norm_num [turnSquare]
        exact ⟨by linarith,hsc,by linarith⟩

theorem halfAngle_recover {c s : ℝ} (hu : c^2+s^2=1) (hc : 0<c) :
    halfAngleCos (s/(1+c))=c ∧ halfAngleSin (s/(1+c))=s := by
  have hd : 0<1+c := by linarith
  have hD : 1+(s/(1+c))^2=2/(1+c) := by
    field_simp [ne_of_gt hd]
    nlinarith
  have hN : 1-(s/(1+c))^2=2*c/(1+c) := by
    field_simp [ne_of_gt hd]
    nlinarith
  constructor
  · rw [halfAngleCos,hD,hN]
    field_simp [ne_of_gt hd]
  · rw [halfAngleSin,hD]
    field_simp [ne_of_gt hd]

theorem halfAngle_halfopen {c s : ℝ} (hu : c^2+s^2=1)
    (hc : 0<c) (hlo : -c≤ s) (hhi : s<c) :
    1-Real.sqrt 2≤ s/(1+c) ∧ s/(1+c)<Real.sqrt 2-1 := by
  let w := s/(1+c)
  have hw := halfAngle_recover hu hc
  have hD := halfAngle_den_pos w
  have hDc : (1+w^2)*c=1-w^2 := by
    rw [← hw.1]
    dsimp [halfAngleCos,w]
    field_simp [ne_of_gt (halfAngle_den_pos (s/(1+c)))]
  have hDs : (1+w^2)*s=2*w := by
    rw [← hw.2]
    dsimp [halfAngleSin,w]
    field_simp [ne_of_gt (halfAngle_den_pos (s/(1+c)))]
  have hl := mul_le_mul_of_nonneg_left hlo hD.le
  have hh := mul_lt_mul_of_pos_left hhi hD
  have hlpoly : (w-1)^2≤2 := by nlinarith
  have hhpoly : (w+1)^2<2 := by nlinarith
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hs2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  constructor
  · change 1-Real.sqrt 2≤w
    by_contra! h
    have hp := mul_pos (by linarith : 0<1-w-Real.sqrt 2)
      (by linarith : 0<1-w+Real.sqrt 2)
    nlinarith
  · change w<Real.sqrt 2-1
    by_contra! h
    have hp := mul_nonneg (by linarith : 0≤w+1-Real.sqrt 2)
      (by linarith : 0≤w+1+Real.sqrt 2)
    nlinarith

private theorem centralParameters_unitSquare_eq {K L : UnitSquare} (h1 : K.center=L.center)
    (h2 : K.cosine=L.cosine) (h3 : K.sine=L.sine) : K=L := by
  cases K; cases L
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem central_parameters_exist (K : UnitSquare) (Z η : ℝ) :
    ∃ p : EqualityParameters, SameSquare p.centralSquare K ∧
      p.centralSquare.center=K.center ∧
      (1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1) ∧ p.z=Z ∧ p.eta=η := by
  obtain ⟨k,hc,hl,hu⟩ := halfopen_quarter_exists K
  let L := turnSquare k K
  let p : EqualityParameters :=
    ⟨K.center.1,K.center.2,L.sine/(1+L.cosine),Z,η⟩
  have hw := halfAngle_recover L.unit hc
  have hframe := halfAngle_halfopen L.unit hc hl hu
  have hL : p.centralSquare=L := by
    refine centralParameters_unitSquare_eq ?_ ?_ ?_
    · rfl
    · show halfAngleCos (L.sine/(1+L.cosine))=L.cosine
      exact hw.1
    · show halfAngleSin (L.sine/(1+L.cosine))=L.sine
      exact hw.2
  refine ⟨p,?_,?_,hframe,rfl,rfl⟩
  · rw [hL]
    exact turnSquare_sameSquare k K
  · rfl

end SquaresInCircles.Eight.ExactFamily
