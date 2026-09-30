module
public import SquaresInCircles.Six.Analytic.FixedPinInclusions
public import SquaresInCircles.Six.Normalization.PinData
public import SquaresInCircles.Six.DiagonalReflection

@[expose] public section

/-!
# Point-set and phase bookkeeping before the pin-labelled model exists

These identities use the fixed five pins directly. They do not construct a
PinPacking, invoke a window certificate, or consume the global D reflection.
The four cases below are the four primary quadrants, not a numerical cover.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Normalization.Certificates

def fixedPinPhase : Fin 5 → ℝ :=
  ![0,Real.pi/2,11*Real.pi/12,5*Real.pi/4,19*Real.pi/12]

def diagonalPinIndex : Fin 5 → Fin 5 := ![1,0,4,3,2]

lemma fixedPin_eq_polar (i : Fin 5) : fixedPin i=polarPin (9/10) (fixedPinPhase i) := by
  fin_cases i <;> simp [fixedPin,fixedPinPhase,polarPin,div_eq_mul_inv,mul_assoc]

lemma diagonal_pin_phase (i : Fin 5) :
    (fixedPinPhase (diagonalPinIndex i):Direction)=(Real.pi/2-fixedPinPhase i:ℝ) := by
  apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
  fin_cases i
  · exact ⟨0,by norm_num [fixedPinPhase,diagonalPinIndex]⟩
  · exact ⟨0,by norm_num [fixedPinPhase,diagonalPinIndex]⟩
  · exact ⟨1,by dsimp [fixedPinPhase,diagonalPinIndex]; ring⟩
  · exact ⟨1,by dsimp [fixedPinPhase,diagonalPinIndex]; ring⟩
  · exact ⟨1,by dsimp [fixedPinPhase,diagonalPinIndex]; ring⟩

lemma fixedPin_diagonal_identity (i : Fin 5) :
    Six.diagonalPoint (fixedPin i)=fixedPin (diagonalPinIndex i) := by
  have hc := congrArg (fun z:Direction => z.cos) (diagonal_pin_phase i)
  have hs := congrArg (fun z:Direction => z.sin) (diagonal_pin_phase i)
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub] at hc hs
  rw [fixedPin_eq_polar,fixedPin_eq_polar]
  apply Prod.ext <;> simp only [Six.diagonalPoint,polarPin,hc,hs]

lemma square_phase_open {t u a b : ℝ} (h:(t:Direction)=(u:Direction)) (p:Point) :
    openSquare (orientedSquare t a b) p ↔ openSquare (orientedSquare u a b) p := by
  have hc := congrArg (fun z:Direction => z.cos) h
  have hs := congrArg (fun z:Direction => z.sin) h
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] at hc hs
  simp only [openSquare,orientedSquare_localX,orientedSquare_localY,hc,hs]

lemma margin_phase_eq {t u : ℝ} (h:(t:Direction)=(u:Direction))
    (k:CentralAxis) (a b cx cy:ℝ) : centralMargin k t a b cx cy=centralMargin k u a b cx cy := by
  have hc := congrArg (fun z:Direction => z.cos) h
  have hs := congrArg (fun z:Direction => z.sin) h
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] at hc hs
  cases k <;> simp only [centralMargin,centralNormal,centralTransverse,centerX,centerY,
    angularWidth,hc,hs]

lemma own_margin_diagonal_identity (t a b cx cy:ℝ) :
    centralMargin .own (Real.pi/2-t) a (-b) cy cx=centralMargin .own t a b cx cy := by
  simp only [centralMargin,centralNormal,angularWidth,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

lemma square_diagonal_membership (t a b:ℝ) (p:Point) :
    openSquare (orientedSquare (Real.pi/2-t) a (-b)) p ↔
      openSquare (orientedSquare t a b) (Six.diagonalPoint p) := by
  have hx : localX (orientedSquare (Real.pi/2-t) a (-b)) p=
      localX (orientedSquare t a b) (Six.diagonalPoint p) := by
    simp only [orientedSquare_localX,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      Six.diagonalPoint]
    ring
  have hy : localY (orientedSquare (Real.pi/2-t) a (-b)) p=
      -localY (orientedSquare t a b) (Six.diagonalPoint p) := by
    simp only [orientedSquare_localY,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
      Six.diagonalPoint]
    ring
  simp only [openSquare,hx,hy,abs_neg]

/-- A real primary phase has exactly one of four quadrant descriptions, up to
harmless boundary overlaps. The west case includes both ends of the principal lift. -/
theorem four_primary_quadrants (t:ℝ) :
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(v:Direction)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(Real.pi/2-v:ℝ)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(Real.pi+v:ℝ)) ∨
    (∃ v, |v|≤Real.pi/4 ∧ (t:Direction)=(-Real.pi/2-v:ℝ)) := by
  let z := (t:Direction).toReal
  have hz0 : -Real.pi≤z := (t:Direction).neg_pi_lt_toReal.le
  have hz1 : z≤Real.pi := (t:Direction).toReal_le_pi
  have hz : (z:Direction)=(t:Direction) := Real.Angle.coe_toReal _
  by_cases h0 : -Real.pi/4≤z
  · by_cases h1 : z≤Real.pi/4
    · exact Or.inl ⟨z,abs_le.mpr ⟨h0,h1⟩,hz.symm⟩
    · by_cases h2 : z≤3*Real.pi/4
      · right; left
        refine ⟨Real.pi/2-z,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
        have h : Real.pi/2-(Real.pi/2-z)=z := by ring
        rw [h]; exact hz.symm
      · right; right; left
        refine ⟨z-Real.pi,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
        have h : Real.pi+(z-Real.pi)=z := by ring
        rw [h]; exact hz.symm
  · by_cases h2 : z≤-3*Real.pi/4
    · right; right; left
      refine ⟨z+Real.pi,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
      have h : Real.pi+(z+Real.pi)=z+2*Real.pi := by ring
      rw [h,Real.Angle.coe_add,Real.Angle.coe_two_pi,add_zero]
      exact hz.symm
    · right; right; right
      refine ⟨-Real.pi/2-z,abs_le.mpr ⟨by linarith,by linarith⟩,?_⟩
      have h : -Real.pi/2-(-Real.pi/2-z)=z := by ring
      rw [h]; exact hz.symm

lemma phase_eq_of_short_difference {t u:ℝ} (he:(t:Direction)=(u:Direction))
    (hshort:|t-u|<2*Real.pi) : t=u := by
  obtain ⟨k,hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp he
  have hb := abs_lt.mp hshort
  rw [hk] at hb
  have hp : 0<2*Real.pi := by positivity
  have hlo : (-1:ℝ)<(k:ℝ) := (mul_lt_mul_left hp).mp (by simpa using hb.1)
  have hhi : (k:ℝ)<1 := (mul_lt_mul_left hp).mp (by simpa using hb.2)
  have hlo' : (-1:ℤ)<k := by exact_mod_cast hlo
  have hhi' : k<1 := by exact_mod_cast hhi
  have hz : k=0 := by omega
  simp only [hz,Int.cast_zero,mul_zero] at hk
  linarith

/-- The pin-centred lift is unique once the new phase is strictly inside it. -/
lemma phase_eq_in_centered_window {t u c:ℝ}
    (ht:-Real.pi≤t-c ∧ t-c≤Real.pi) (hu:|u-c|<Real.pi)
    (he:(t:Direction)=(u:Direction)) : t=u := by
  apply phase_eq_of_short_difference he
  have h1 : |t-c|≤Real.pi := abs_le.mpr ht
  have h2 := abs_sub (t-c) (u-c)
  have hid : (t-c)-(u-c)=t-u := by ring
  rw [hid] at h2
  linarith

end SquaresInCircles.Six.Analytic
