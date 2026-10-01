import SquaresInCircles.Six.Analytic.CapFixedPins
import SquaresInCircles.Six.Normalization.SecondarySeparation

/-!
# The pins covered by an exterior square

Let an exterior square lie in the disk and avoid the core, and let it be
separated from C, with the centre of C in `[0, c0]²`. Then its phase lies in
a window about one of the four directions of the sides of C, and it covers
the matching pins: pin `0` to the east, pin `1` to the north, pin `2` or `3` to
the west and pin `4` or `3` to the south, with finer conditions for the last
two. A separation along the second axis of the square is impossible. For a
separation along its own axis the radial bounds of the square locate it, for
one along a side of C the cap beyond that side, and the north and south cases
are the east and west cases reflected in the diagonal. In particular the
square covers one of the five pins.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic
open Normalization Normalization.Certificates

def EastPinData (t a b:ℝ) : Prop :=
  ∃ v : ℝ, (-5/12<v ∧ v<3/10) ∧ (t:Direction)=(v:Direction) ∧
    openSquare (orientedSquare t a b) (fixedPin 0)

def NorthPinData (t a b:ℝ) : Prop :=
  ∃ v, (-3/10<v ∧ v<5/12) ∧ (t:Direction)=(Real.pi/2+v:ℝ) ∧
    openSquare (orientedSquare t a b) (fixedPin 1)

def WestPinData (t a b:ℝ) : Prop :=
  ∃ v, (-2/3<v ∧ v≤Real.pi/4) ∧ (t:Direction)=(Real.pi+v:ℝ) ∧
    (openSquare (orientedSquare t a b) (fixedPin 2) ∨
      openSquare (orientedSquare t a b) (fixedPin 3)) ∧
    (v≤-Real.pi/12 → openSquare (orientedSquare t a b) (fixedPin 2)) ∧
    (openSquare (orientedSquare t a b) (fixedPin 2) → v<5/8)

def SouthPinData (t a b:ℝ) : Prop :=
  ∃ v, (-Real.pi/4≤v ∧ v<2/3) ∧ (t:Direction)=(3*Real.pi/2+v:ℝ) ∧
    (openSquare (orientedSquare t a b) (fixedPin 4) ∨
      openSquare (orientedSquare t a b) (fixedPin 3)) ∧
    (Real.pi/12≤v → openSquare (orientedSquare t a b) (fixedPin 4)) ∧
    (openSquare (orientedSquare t a b) (fixedPin 4) → -5/8<v)

def PinLocation (t a b:ℝ) : Prop :=
  EastPinData t a b ∨ NorthPinData t a b ∨ WestPinData t a b ∨ SouthPinData t a b

lemma own_east_data {t v a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hv:|v|≤Real.pi/4) (he:(t:Direction)=(v:Direction))
    (ho:0≤centralMargin .own t a b cx cy) : EastPinData t a b := by
  have hov : 0≤centralMargin .own v a b cx cy := by
    simpa only [margin_phase_eq he] using ho
  obtain ⟨hw,hp⟩ := own_east_fixed_pin hc hb hx0 hy0 hx hy hv hov
  refine ⟨v,hw,he,?_⟩
  apply (square_phase_open he _).mpr
  simpa [fixedPin,polarPin] using hp

lemma own_west_data {t v a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx:cx≤c0) (hy0:0≤cy) (hy:cy≤c0)
    (hv:|v|≤Real.pi/4) (he:(t:Direction)=(Real.pi+v:ℝ))
    (ho:0≤centralMargin .own t a b cx cy) : WestPinData t a b := by
  have hov : 0≤centralMargin .own (Real.pi+v) a b cx cy := by
    simpa only [margin_phase_eq he] using ho
  have hw := own_west_lower_window hc hx hy0 hv hov
  have hcover := own_west_fixed_pins hc hb hx hy0 hv hov
  have hW : openSquare (orientedSquare t a b) (fixedPin 2) ↔
      openSquare (orientedSquare (Real.pi+v) a b) (polarPin (9/10) (11*Real.pi/12)) := by
    rw [square_phase_open he,fixedPin_eq_polar]
    rfl
  have hD : openSquare (orientedSquare t a b) (fixedPin 3) ↔
      openSquare (orientedSquare (Real.pi+v) a b) (polarPin (9/10) (5*Real.pi/4)) := by
    rw [square_phase_open he,fixedPin_eq_polar]
    rfl
  refine ⟨v,⟨hw,(abs_le.mp hv).2⟩,he,?_,?_,?_⟩
  · exact hcover.elim (fun h => Or.inl (hW.mpr h)) (fun h => Or.inr (hD.mpr h))
  · intro hleft
    exact hW.mpr (own_west_left_pin hc hb hx hy0 hv hleft hov)
  · intro hp
    exact own_west_pin_upper hc hx hy hv hov (hW.mp hp)

lemma east_data_diagonal {t a b:ℝ} (h:EastPinData (Real.pi/2-t) a (-b)) : NorthPinData t a b := by
  obtain ⟨v,hv,he,hp⟩ := h
  have ht : (t:Direction)=(Real.pi/2-v:ℝ) := by
    have hid : t=Real.pi/2-(Real.pi/2-t) := by ring
    calc
      (t:Direction) = (Real.pi/2-(Real.pi/2-t):ℝ) := congrArg (fun x:ℝ => (x:Direction)) hid
      _ = _ := by simp only [Real.Angle.coe_sub,he]
  have hpoint := (square_diagonal_membership t a b (fixedPin 0)).mp hp
  rw [fixedPin_diagonal_identity] at hpoint
  refine ⟨-v,⟨by linarith [hv.2],by linarith [hv.1]⟩,?_,?_⟩
  · simpa only [sub_eq_add_neg] using ht
  · exact hpoint

lemma west_data_diagonal {t a b:ℝ} (h:WestPinData (Real.pi/2-t) a (-b)) : SouthPinData t a b := by
  obtain ⟨v,hv,he,hcover,hleft,hupper⟩ := h
  have ht : (t:Direction)=(3*Real.pi/2-v:ℝ) := by
    have hid : t=Real.pi/2-(Real.pi/2-t) := by ring
    have hsum : 3*Real.pi/2-v=(Real.pi/2-(Real.pi+v))+2*Real.pi := by ring
    rw [hsum,Real.Angle.coe_add,Real.Angle.coe_two_pi,add_zero]
    calc
      (t:Direction) = (Real.pi/2-(Real.pi/2-t):ℝ) := congrArg (fun x:ℝ => (x:Direction)) hid
      _ = _ := by simp only [Real.Angle.coe_sub,he]
  have hW : openSquare (orientedSquare (Real.pi/2-t) a (-b)) (fixedPin 2) ↔
      openSquare (orientedSquare t a b) (fixedPin 4) := by
    have h := square_diagonal_membership t a b (fixedPin 2)
    rw [fixedPin_diagonal_identity] at h
    exact h
  have hD : openSquare (orientedSquare (Real.pi/2-t) a (-b)) (fixedPin 3) ↔
      openSquare (orientedSquare t a b) (fixedPin 3) := by
    have h := square_diagonal_membership t a b (fixedPin 3)
    rw [fixedPin_diagonal_identity] at h
    exact h
  refine ⟨-v,⟨by linarith [hv.2],by linarith [hv.1]⟩,?_,?_,?_,?_⟩
  · simpa only [sub_eq_add_neg] using ht
  · exact hcover.elim (fun h => Or.inl (hW.mp h)) (fun h => Or.inr (hD.mp h))
  · intro hlow
    exact hW.mp (hleft (by linarith))
  · intro hp
    linarith [hupper (hW.mpr hp)]

lemma own_pin_location {t a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (ho:0≤centralMargin .own t a b cx cy) : PinLocation t a b := by
  have hcn : ContainedChart a |-b| := by simpa only [abs_neg] using hc
  have hbn : |-b|<1/2 := by simpa only [abs_neg] using hb
  have hor : 0≤centralMargin .own (Real.pi/2-t) a (-b) cy cx := by
    simpa only [own_margin_diagonal_identity] using ho
  rcases four_primary_quadrants t with hE | hN | hW | hS
  · obtain ⟨v,hv,he⟩ := hE
    exact Or.inl (own_east_data hc hb hx0 hy0 hx hy hv he ho)
  · obtain ⟨v,hv,he⟩ := hN
    have hr : ((Real.pi/2-t:ℝ):Direction)=(v:Direction) := by
      have hid : Real.pi/2-(Real.pi/2-v)=v := by ring
      calc
        ((Real.pi/2-t:ℝ):Direction) = (Real.pi/2-(Real.pi/2-v):ℝ) := by
          simp only [Real.Angle.coe_sub,he]
        _ = _ := congrArg (fun x:ℝ => (x:Direction)) hid
    exact Or.inr (Or.inl (east_data_diagonal (own_east_data hcn hbn hy0 hx0 hy hx hv hr hor)))
  · obtain ⟨v,hv,he⟩ := hW
    exact Or.inr (Or.inr (Or.inl (own_west_data hc hb hx hy0 hy hv he ho)))
  · obtain ⟨v,hv,he⟩ := hS
    have hr : ((Real.pi/2-t:ℝ):Direction)=(Real.pi+v:ℝ) := by
      have hid : Real.pi/2-(-Real.pi/2-v)=Real.pi+v := by ring
      calc
        ((Real.pi/2-t:ℝ):Direction) = (Real.pi/2-(-Real.pi/2-v):ℝ) := by
          simp only [Real.Angle.coe_sub,he]
        _ = _ := congrArg (fun x:ℝ => (x:Direction)) hid
    exact Or.inr (Or.inr (Or.inr (west_data_diagonal (own_west_data hcn hbn hy hx0 hx hv hr hor))))

lemma east_cap_data {t a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx0:0≤cx) (he:0≤centralMargin .east t a b cx cy) : EastPinData t a b := by
  have hm : (1/2+cx)+angularWidth t≤centerX t a b := by
    dsimp [centralMargin] at he
    linarith
  obtain ⟨v,hv,hphase,hpin⟩ := east_cap_fixed_pin hc hb (by linarith) hm
  have hbv := abs_lt.mp hv
  exact ⟨v,⟨by linarith [hbv.1],by linarith [hbv.2]⟩,hphase,
    by simpa [fixedPin,polarPin] using hpin⟩

lemma west_cap_data {t a b cx cy:ℝ} (hc:ContainedChart a |b|) (hb:|b|<1/2)
    (hx:cx≤c0) (hw:0≤centralMargin .west t a b cx cy) : WestPinData t a b := by
  have hcore : coreRadius≤1/2-cx := by linarith [c0_add_coreRadius]
  have hm : (1/2-cx)+angularWidth (t-Real.pi)≤centerX (t-Real.pi) a b := by
    rw [west_cap_rotated_identity] at hw
    linarith
  obtain ⟨v,hv,he,hmv⟩ := positive_cap_direction hc hcore hm
  have hphase : (t:Direction)=(Real.pi+v:ℝ) := by
    have hid : t=(t-Real.pi)+Real.pi := by ring
    have hcomm : v+Real.pi=Real.pi+v := by ring
    calc
      (t:Direction) = ((t-Real.pi)+Real.pi:ℝ) := congrArg (fun x:ℝ => (x:Direction)) hid
      _ = (v+Real.pi:ℝ) := by simp only [Real.Angle.coe_add,he]
      _ = _ := congrArg (fun x:ℝ => (x:Direction)) hcomm
  have hW : openSquare (orientedSquare t a b) (fixedPin 2) ↔
      openSquare (orientedSquare v a b) (polarPin (9/10) (-Real.pi/12)) := by
    rw [square_phase_open hphase,fixedPin_eq_polar]
    change openSquare (orientedSquare (Real.pi+v) a b) (polarPin (9/10) (11*Real.pi/12)) ↔ _
    have hT : Real.pi+v=v+Real.pi := by ring
    have hQ : 11*Real.pi/12=(-Real.pi/12)+Real.pi := by ring
    rw [hT,hQ,polar_rotate]
  have hD : openSquare (orientedSquare t a b) (fixedPin 3) ↔
      openSquare (orientedSquare v a b) (polarPin (9/10) (Real.pi/4)) := by
    rw [square_phase_open hphase,fixedPin_eq_polar]
    change openSquare (orientedSquare (Real.pi+v) a b) (polarPin (9/10) (5*Real.pi/4)) ↔ _
    have hT : Real.pi+v=v+Real.pi := by ring
    have hQ : 5*Real.pi/4=Real.pi/4+Real.pi := by ring
    rw [hT,hQ,polar_rotate]
  have hcovers := west_cap_fixed_pins hc hb hcore hv hmv
  have hvr := abs_lt.mp hv
  refine ⟨v,⟨by linarith [hvr.1],by linarith [hvr.2,Real.pi_gt_d2]⟩,hphase,?_,?_,?_⟩
  · exact hcovers.elim (fun h => Or.inl (hW.mpr h)) (fun h => Or.inr (hD.mpr h))
  · intro hleft
    exact hW.mpr (west_cap_left_pin hc hb hcore hv hleft hmv)
  · intro _
    linarith [hvr.2]

lemma north_east_diagonal_margin (t a b cx cy:ℝ) :
    centralMargin .east (Real.pi/2-t) a (-b) cy cx=centralMargin .north t a b cx cy := by
  simp only [centralMargin,centerX,centerY,angularWidth,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

lemma south_west_diagonal_margin (t a b cx cy:ℝ) :
    centralMargin .west (Real.pi/2-t) a (-b) cy cx=centralMargin .south t a b cx cy := by
  simp only [centralMargin,centerX,centerY,angularWidth,Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub]
  ring

/-- An exterior square separated from C lies in one of the four pin locations. -/
theorem pin_location_of_separation {t a b cx cy:ℝ} (hc:ContainedChart a |b|)
    (hcore:AvoidsCore a |b|) (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hs:∃ k,0≤centralMargin k t a b cx cy) : PinLocation t a b := by
  have hb := hc.u_lt_half hcore
  have hsec := Normalization.secondary_separators_fail (hc.u_le_U0 hcore) hx0 hy0 hx hy (t:=t)
  have hcn : ContainedChart a |-b| := by simpa only [abs_neg] using hc
  have hbn : |-b|<1/2 := by simpa only [abs_neg] using hb
  obtain ⟨k,hk⟩ := hs
  cases k
  · exact own_pin_location hc hb hx0 hy0 hx hy hk
  · change 0≤b-1/2-(-cx*Real.sin t+cy*Real.cos t)-(|Real.cos t|+|Real.sin t|)/2 at hk
    linarith [hsec.1]
  · change 0≤(-cx*Real.sin t+cy*Real.cos t)-1/2-(|Real.cos t|+|Real.sin t|)/2-b at hk
    linarith [hsec.2]
  · exact Or.inl (east_cap_data hc hb hx0 hk)
  · exact Or.inr (Or.inr (Or.inl (west_cap_data hc hb hx hk)))
  · have hr : 0≤centralMargin .east (Real.pi/2-t) a (-b) cy cx := by
      simpa only [north_east_diagonal_margin] using hk
    exact Or.inr (Or.inl (east_data_diagonal (east_cap_data hcn hbn hy0 hr)))
  · have hr : 0≤centralMargin .west (Real.pi/2-t) a (-b) cy cx := by
      simpa only [south_west_diagonal_margin] using hk
    exact Or.inr (Or.inr (Or.inr (west_data_diagonal (west_cap_data hcn hbn hy hr))))

/-- An exterior square separated from C covers one of the five pins. -/
theorem five_pin_cover {t a b cx cy:ℝ} (hc:ContainedChart a |b|) (hcore:AvoidsCore a |b|)
    (hx0:0≤cx) (hy0:0≤cy) (hx:cx≤c0) (hy:cy≤c0)
    (hs:∃ k,0≤centralMargin k t a b cx cy) :
    ∃ i:Fin 5,openSquare (orientedSquare t a b) (fixedPin i) := by
  rcases pin_location_of_separation hc hcore hx0 hy0 hx hy hs with h | h | h | h
  · obtain ⟨v,hv,he,hp⟩ := h
    exact ⟨0,hp⟩
  · obtain ⟨v,hv,he,hp⟩ := h
    exact ⟨1,hp⟩
  · obtain ⟨v,hv,he,hp,_⟩ := h
    exact hp.elim (fun h=>⟨2,h⟩) (fun h=>⟨3,h⟩)
  · obtain ⟨v,hv,he,hp,_⟩ := h
    exact hp.elim (fun h=>⟨4,h⟩) (fun h=>⟨3,h⟩)

end SquaresInCircles.Six.Analytic
