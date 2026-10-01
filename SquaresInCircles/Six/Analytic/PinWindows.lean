import SquaresInCircles.Six.Analytic.PinLocations

/-!
# Windows and central axes from the pins

The pin covering places the phase of a square in its quadrant, together with
the pins the square may hold there. A square that holds pin `i` and no other
pin has its phase in the window of `i`, since the pins it does not hold cut
the quadrant down to that window. A square that holds pin `i` is separated
from C only along an axis allowed for `i`: by the coordinates of the pins, a
square beyond a side of C that does not face pin `i` cannot hold that pin, and
the secondary axes never separate a square that avoids the core.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Normalization.Certificates

private lemma window_inside_pi (i:Fin 5) {v:ℝ}
    (hv:(windowLower i:ℝ)<v ∧ v<(windowUpper i:ℝ)) : |v|<Real.pi := by
  apply abs_lt.mpr
  fin_cases i <;> norm_num [windowLower,windowUpper] at hv <;>
    constructor <;> linarith [hv.1,hv.2,Real.pi_gt_d2]

private lemma window_transport (i:Fin 5) {t u:ℝ}
    (ht:-Real.pi≤t-phaseCenter i ∧ t-phaseCenter i≤Real.pi)
    (he:(t:Direction)=(u:Direction))
    (hu:(windowLower i:ℝ)<u-phaseCenter i ∧ u-phaseCenter i<(windowUpper i:ℝ)) :
    (windowLower i:ℝ)<t-phaseCenter i ∧ t-phaseCenter i<(windowUpper i:ℝ) := by
  have htu := phase_eq_in_centered_window ht (window_inside_pi i hu) he
  simpa only [htu] using hu

/-- A square at a pin location that holds pin `i` and no other pin has its phase
in the window of `i`. -/
theorem window_for_unique_pin {t a b:ℝ} (i:Fin 5) (hloc:PinLocation t a b)
    (ht:-Real.pi≤t-phaseCenter i ∧ t-phaseCenter i≤Real.pi)
    (huniq:∀ j:Fin 5,openSquare (orientedSquare t a b) (fixedPin j) → j=i) :
    (windowLower i:ℝ)<t-phaseCenter i ∧ t-phaseCenter i<(windowUpper i:ℝ) := by
  rcases hloc with hE | hN | hW | hS
  · obtain ⟨v,hv,he,hp⟩ := hE
    have hi : i=0 := (huniq 0 hp).symm
    subst i
    apply window_transport 0 ht he
    simpa [windowLower,windowUpper,phaseCenter] using hv
  · obtain ⟨v,hv,he,hp⟩ := hN
    have hi : i=1 := (huniq 1 hp).symm
    subst i
    apply window_transport 1 ht he
    simpa [windowLower,windowUpper,phaseCenter] using hv
  · obtain ⟨v,hv,he,hcover,hleft,hupper⟩ := hW
    rcases hcover with hpW | hpD
    · have hi : i=2 := (huniq 2 hpW).symm
      subst i
      apply window_transport 2 ht he
      simpa [windowLower,windowUpper,phaseCenter] using And.intro hv.1 (hupper hpW)
    · have hi : i=3 := (huniq 3 hpD).symm
      subst i
      have hvlo : -Real.pi/12<v := by
        by_contra! hbad
        have hne := huniq 2 (hleft hbad)
        norm_num at hne
      apply window_transport 3 ht he
      norm_num [windowLower,windowUpper,phaseCenter]
      constructor <;> linarith [hv.2,Real.pi_lt_d2]
  · obtain ⟨v,hv,he,hcover,hright,hlower⟩ := hS
    rcases hcover with hpS | hpD
    · have hi : i=4 := (huniq 4 hpS).symm
      subst i
      apply window_transport 4 ht he
      norm_num [windowLower,windowUpper,phaseCenter]
      constructor <;> linarith [hlower hpS,hv.2]
    · have hi : i=3 := (huniq 3 hpD).symm
      subst i
      have hvhi : v<Real.pi/12 := by
        by_contra! hbad
        have hne := huniq 4 (hright hbad)
        norm_num at hne
      apply window_transport 3 ht he
      norm_num [windowLower,windowUpper,phaseCenter]
      constructor <;> linarith [hv.1,Real.pi_lt_d2]

/-- A contained square that avoids the core, is separated from C, and holds pin
`i` and no other pin, has its phase in the window of `i`. -/
theorem labelled_window {t a b cx cy:ℝ} (i:Fin 5) (hc:ContainedChart a |b|)
    (hcore:AvoidsCore a |b|) (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hs:∃ k,0≤centralMargin k t a b cx cy)
    (ht:-Real.pi≤t-phaseCenter i ∧ t-phaseCenter i≤Real.pi)
    (huniq:∀ j:Fin 5,openSquare (orientedSquare t a b) (fixedPin j) → j=i) :
    (windowLower i:ℝ)<t-phaseCenter i ∧ t-phaseCenter i<(windowUpper i:ℝ) :=
  window_for_unique_pin i (pin_location_of_separation hc hcore hx0 hy0 hx hy hs) ht huniq

lemma fixed_pin_coordinates (i:Fin 5) : fixedPin i =
    ![(9/10,0),(0,9/10),
      (-(9/10)*Real.cos (Real.pi/12),(9/10)*Real.sin (Real.pi/12)),
      (-(9/10)*Real.cos (Real.pi/4),-(9/10)*Real.sin (Real.pi/4)),
      ((9/10)*Real.sin (Real.pi/12),-(9/10)*Real.cos (Real.pi/12))] i := by
  fin_cases i
  · rfl
  · rfl
  · have h : (11/12)*Real.pi=Real.pi-Real.pi/12 := by ring
    simp [fixedPin,h,Real.cos_pi_sub,Real.sin_pi_sub]
  · have h : (5/4)*Real.pi=Real.pi/4+Real.pi := by ring
    simp [fixedPin,h,Real.cos_add_pi,Real.sin_add_pi]
  · have h : (19/12)*Real.pi=(Real.pi/12-Real.pi/2)+2*Real.pi := by ring
    simp [fixedPin,h,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub]

private lemma pin_trig_signs :
    0≤Real.cos (Real.pi/12) ∧ 0≤Real.sin (Real.pi/12) ∧
      Real.sin (Real.pi/12)≤1/3 ∧
      0≤Real.cos (Real.pi/4) ∧ 0≤Real.sin (Real.pi/4) := by
  have hcos : 0≤Real.cos (Real.pi/12) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤Real.pi/12 by positivity) (show Real.pi/12≤Real.pi by linarith [Real.pi_pos])
  have hu : Real.sin (Real.pi/12)≤1/3 := by
    have h := Real.sin_le (show 0≤Real.pi/12 by positivity)
    linarith [Real.pi_lt_d2]
  exact ⟨hcos,hsin,hu,by linarith [quarter_trig_lower.1],by linarith [quarter_trig_lower.2]⟩

lemma non_east_pin_x (i:Fin 5) (hi:i≠0) : (fixedPin i).1≤3/10 := by
  rw [fixed_pin_coordinates]
  have h := pin_trig_signs
  revert hi
  fin_cases i <;> norm_num <;>
    nlinarith [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,Real.sqrt_nonneg 2]

lemma non_north_pin_y (i:Fin 5) (hi:i≠1) : (fixedPin i).2≤3/10 := by
  rw [fixed_pin_coordinates]
  have h := pin_trig_signs
  revert hi
  fin_cases i <;> norm_num <;>
    nlinarith [h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,Real.sqrt_nonneg 2]

lemma non_west_pin_x (i:Fin 5) (hiW:i≠2) (hiD:i≠3) : 0≤(fixedPin i).1 := by
  rw [fixed_pin_coordinates]
  have h := pin_trig_signs
  revert hiW hiD
  fin_cases i <;> norm_num
  nlinarith [h.2.1]

lemma non_south_pin_y (i:Fin 5) (hiD:i≠3) (hiS:i≠4) : 0≤(fixedPin i).2 := by
  rw [fixed_pin_coordinates]
  have h := pin_trig_signs
  revert hiD hiS
  fin_cases i <;> norm_num
  nlinarith [h.2.1]

/-- A square that holds pin `i` is separated from C only along an axis allowed
for `i`. -/
theorem allowed_axis_of_pin {t a b cx cy:ℝ} (i:Fin 5) (hc:ContainedChart a |b|)
    (hcore:AvoidsCore a |b|) (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hpin:openSquare (orientedSquare t a b) (fixedPin i))
    (k:CentralAxis) (hk:0≤centralMargin k t a b cx cy) : k∈allowed i := by
  have hp : closedSquare (orientedSquare t a b) (fixedPin i) := ⟨hpin.1.le,hpin.2.le⟩
  have hsec := Normalization.secondary_separators_fail (hc.u_le_U0 hcore) hx0 hy0 hx hy (t:=t)
  cases k
  · fin_cases i <;> simp [allowed]
  · change 0≤b-1/2-(-cx*Real.sin t+cy*Real.cos t)-(|Real.cos t|+|Real.sin t|)/2 at hk
    linarith [hsec.1]
  · change 0≤(-cx*Real.sin t+cy*Real.cos t)-1/2-(|Real.cos t|+|Real.sin t|)/2-b at hk
    linarith [hsec.2]
  · by_cases hi:i=0
    · subst i; simp [allowed]
    · have hcap := east_margin_cap hk _ hp
      have hbound := non_east_pin_x i hi
      linarith
  · by_cases hiW:i=2
    · subst i; simp [allowed]
    · by_cases hiD:i=3
      · subst i; simp [allowed]
      · have hcap := west_margin_cap hk _ hp
        have hbound := non_west_pin_x i hiW hiD
        linarith [c0_lt_23_200]
  · by_cases hi:i=1
    · subst i; simp [allowed]
    · have hcap := north_margin_cap hk _ hp
      have hbound := non_north_pin_y i hi
      linarith
  · by_cases hiD:i=3
    · subst i; simp [allowed]
    · by_cases hiS:i=4
      · subst i; simp [allowed]
      · have hcap := south_margin_cap hk _ hp
        have hbound := non_south_pin_y i hiD hiS
        linarith [c0_lt_23_200]

end SquaresInCircles.Six.Analytic
