import SquaresInCircles.Seven.LabelBoundary
import SquaresInCircles.Seven.Support
import SquaresInCircles.Seven.Analysis

/-!
# Segments of constant label

At a fixed label the support is affine in the state, so it is extreme at the
ends of the admissible segment of that label. The segments end on the axial
line, on the circle `φ = 13/4` and on the diagonal.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Boundary

lemma circle_radicand_pos {u : ℝ} (hu : 0 ≤ u ∧ u ≤ rd) :
    0 < targetSq-(u+1/2)^2 := by
  have hrd := rd_sq
  have hmul := mul_nonneg (sub_nonneg.mpr hu.2)
    (show 0 ≤ rd+u+1 by linarith [hu.1,rd_bounds.1])
  dsimp [targetSq] at *
  linarith

lemma circle_eq {u : ℝ} (hu : 0 ≤ u ∧ u ≤ rd) :
    (circle u+1/2)^2+(u+1/2)^2=targetSq := by
  have hs := Real.sq_sqrt (circle_radicand_pos hu).le
  dsimp [circle]
  linarith

lemma circle_ge_coordinate {u : ℝ} (hu : 0 ≤ u ∧ u ≤ rd) : u ≤ circle u := by
  have he := circle_eq hu
  have hs : 0 ≤ circle u+1/2 := by
    dsimp [circle]; linarith [Real.sqrt_nonneg (targetSq-(u+1/2)^2)]
  have hrd := rd_sq
  have hm := mul_nonneg (sub_nonneg.mpr hu.2)
    (show 0 ≤ rd+u+1 by linarith [hu.1,rd_bounds.1])
  nlinarith

lemma circle_state {u : ℝ} (hu : 0 ≤ u ∧ u ≤ rd) : Admissible (circle u) u := by
  have he := circle_eq hu
  have ha := circle_ge_coordinate hu
  have hr := rd_bounds
  have hroot : 0 ≤ circle u+1/2 := by
    dsimp [circle]; linarith [Real.sqrt_nonneg (targetSq-(u+1/2)^2)]
  have ha0 : 1/2 ≤ circle u := by
    dsimp [targetSq] at he
    nlinarith
  exact ⟨hu.1,ha,ha0,by dsimp [phi]; linarith⟩

lemma circle_order {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ rd) :
    circle v ≤ circle u ∧ circle u-circle v ≤ v-u := by
  have hu' : 0 ≤ u ∧ u ≤ rd := ⟨hu,huv.trans hv⟩
  have hv' : 0 ≤ v ∧ v ≤ rd := ⟨hu.trans huv,hv⟩
  have eu := circle_eq hu'
  have ev := circle_eq hv'
  have au := circle_state hu'
  have av := circle_state hv'
  have hprod := mul_nonneg (sub_nonneg.mpr huv) (show 0 ≤ u+v+1 by linarith)
  have hanti : circle v ≤ circle u := by nlinarith [au.a_nonneg,av.a_nonneg]
  have hid : (circle u-circle v)*(circle u+circle v+1)=(v-u)*(u+v+1) := by
    linarith
  have hwidth := mul_nonneg (sub_nonneg.mpr huv)
    (show 0 ≤ circle u+circle v-u-v by linarith [au.u_le,av.u_le])
  have hpos : 0 < circle u+circle v+1 := by linarith [au.a_nonneg,av.a_nonneg]
  refine ⟨hanti,?_⟩
  by_contra hn
  have hm := mul_pos (show 0 < circle u-circle v-(v-u) by linarith) hpos
  linarith

lemma circle_u0 : circle u0=a0 := by
  have h := transition_coarse
  have he := circle_eq (u := u0) ⟨by linarith,by linarith [rd_bounds.1]⟩
  have hp := transition_circle
  have hc := circle_state (u := u0) ⟨by linarith,by linarith [rd_bounds.1]⟩
  dsimp [a0,u0] at *
  nlinarith [hc.a_nonneg]

lemma circle_switch_left {u : ℝ} (hu : 0 ≤ u ∧ u ≤ u0) :
    circle u ≤ axialLine u := by
  have hr : u0 ≤ rd := by linarith [transition_coarse.2.2.2.1,rd_bounds.1]
  have ho := circle_order hu.1 hu.2 hr
  rw [circle_u0] at ho
  have hl := transition_line
  dsimp [axialLine]
  linarith

lemma circle_switch_right {u : ℝ} (hu : u0 ≤ u ∧ u ≤ rd) :
    axialLine u ≤ circle u := by
  have hu0 : 0 ≤ u0 := by linarith [transition_coarse.2.2.1]
  have ho := circle_order hu0 hu.1 hu.2
  rw [circle_u0] at ho
  have hl := transition_line
  dsimp [axialLine]
  linarith

lemma axialTop_left {u : ℝ} (hu : 0 ≤ u ∧ u ≤ u0) : axialTop u=circle u :=
  min_eq_left (circle_switch_left hu)

lemma axialTop_right {u : ℝ} (hu : u0 ≤ u ∧ u ≤ rd) : axialTop u=axialLine u :=
  min_eq_right (circle_switch_right hu)

lemma a_le_circle {a u : ℝ} (h : Admissible a u) : a ≤ circle u := by
  have hp := h.phi_le
  have hr : 0 ≤ targetSq-(u+1/2)^2 := by
    dsimp [phi] at hp
    linarith [sq_nonneg (a+1/2)]
  have hs := Real.sq_sqrt hr
  have hn := Real.sqrt_nonneg (targetSq-(u+1/2)^2)
  dsimp [circle,phi] at *
  nlinarith [h.a_nonneg]

lemma axial_upper {a u : ℝ} (h : Admissible a u)
    (hA : label a u=axial u) : a ≤ axialTop u := by
  apply le_min (a_le_circle h)
  have hh := axial_tie_line h hA
  dsimp [axialLine]
  linarith

lemma axialTop_state {u : ℝ} (hu : 0 ≤ u ∧ u ≤ Real.pi/5) :
    Admissible (axialTop u) u ∧ label (axialTop u) u=axial u := by
  have huR : u ≤ rd := by linarith [hu.2,pi_lt_22_over_7,rd_bounds.1]
  have hc := circle_state ⟨hu.1,huR⟩
  have hlineU : u ≤ axialLine u := by dsimp [axialLine]; linarith [hu.2,pi_lt_22_over_7]
  have hlineA : 1/2 ≤ axialLine u := by dsimp [axialLine]; linarith [hu.2,pi_lt_22_over_7]
  have htop : 1/2 ≤ axialTop u := le_min hc.half_le hlineA
  have hgeU : u ≤ axialTop u := le_min hc.u_le hlineU
  have hle : axialTop u ≤ circle u := min_le_left _ _
  have hphi : phi (axialTop u) u ≤ targetSq := by
    have hm := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ circle u+axialTop u+1 by linarith [hc.a_nonneg])
    have he := circle_eq ⟨hu.1,huR⟩
    dsimp [phi]
    linarith
  have ha : Admissible (axialTop u) u := ⟨hu.1,hgeU,htop,hphi⟩
  have hside : axial u ≤ side (axialTop u) u := by
    have hh : axialTop u ≤ axialLine u := min_le_right _ _
    dsimp [axialLine,axial,side] at *
    linarith
  have hcap : axial u ≤ Real.pi/4 := by dsimp [axial]; linarith [hu.2]
  exact ⟨ha,by simp only [label,min_eq_left hside,min_eq_left hcap]⟩

lemma side_state_transition_bounds {a u : ℝ} (h : Admissible a u)
    (hT : label a u=side a u) : u0 ≤ u ∧ a ≤ a0 ∧ s0 ≤ label a u := by
  have ht := h.label_le_axial
  rw [hT] at ht
  have hline : 2*Real.pi+7 ≤ 9*a+11*u := by dsimp [side,axial] at ht; linarith
  have h0 := transition_coarse
  have he := transition_circle
  have hl := transition_line
  have hphi := h.phi_le
  have hu : u0 ≤ u := by
    by_contra hn
    have hd : 0 < u0-u := by linarith
    have ha : 0 < a-a0 := by linarith
    have hweighted := mul_nonneg
      (show 0 ≤ (a-a0)-(11/9)*(u0-u) by linarith)
      (show 0 ≤ 2*X0 by dsimp [a0] at h0; linarith)
    have hpositive := mul_pos hd
      (show 0 < (22/9)*X0-2*Y0 by dsimp [a0,u0] at h0; linarith)
    have hid : phi a u-targetSq =
        2*X0*(a-a0)+2*Y0*(u-u0)+(a-a0)^2+(u-u0)^2 := by
      dsimp [phi,a0,u0] at *
      linarith
    linarith [sq_nonneg (a-a0),sq_nonneg (u-u0)]
  have ha : a ≤ a0 := by
    have hp := mul_nonneg (sub_nonneg.mpr hu)
      (show 0 ≤ u+u0+1 by linarith [h.u_nonneg])
    dsimp [phi,a0,u0] at *
    nlinarith [h.a_nonneg]
  have hs : s0 ≤ label a u := by
    rw [hT]
    have heq := transition_labels.2
    have heq' : side a0 u0=s0 := by
      rw [← heq,transition_labels.1]
      dsimp [s0,axial]; ring
    rw [← heq']
    dsimp [side]
    linarith
  exact ⟨hu,ha,hs⟩

lemma circle_state_at_label {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    Admissible (sideA t) (sideU t) ∧ label (sideA t) (sideU t)=side (sideA t) (sideU t) ∧
      side (sideA t) (sideU t)=t := by
  have hb := circle_bounds ht
  have he := circle_identities ht
  have ha : Admissible (sideA t) (sideU t) := by
    refine ⟨?_,?_,?_,?_⟩
    · have h0 := transition_coarse
      dsimp [u0] at h0
      dsimp [sideU]; linarith [h0.2.2.1]
    · dsimp [sideA,sideU]; linarith
    · dsimp [sideA]; linarith
    · dsimp [phi,sideA,sideU]; linarith [he.1]
  have hcircle : circle (sideU t)=sideA t := by
    have hX : Real.sqrt (targetSq-(sideU t+1/2)^2) = X t := by
      rw [Real.sqrt_eq_iff_eq_sq (by dsimp [sideU]; linarith [he.1,sq_nonneg (X t)])
        (by linarith)]
      dsimp [sideU]
      linarith [he.1]
    dsimp [circle,sideA]
    rw [hX]
  have huR : sideU t ≤ rd := by
    have hrd := rd_sq
    have hm := mul_nonneg (sub_nonneg.mpr hb.2.2.1) (show 0 ≤ X t+Y t by linarith)
    dsimp [sideU]
    nlinarith [he.1,rd_bounds.1]
  have hu0 : u0 ≤ sideU t := by dsimp [u0,sideU]; linarith [hb.2.1]
  have hsw := circle_switch_right ⟨hu0,huR⟩
  rw [hcircle] at hsw
  have hTA : side (sideA t) (sideU t) ≤ axial (sideU t) := by
    dsimp [axialLine,side,axial] at hsw ⊢
    linarith
  have hcap : side (sideA t) (sideU t) ≤ Real.pi/4 := by
    rw [circle_label ht]
    exact ht.2.trans td_bounds.2.le
  exact ⟨ha,by simp only [label,min_eq_right hTA,min_eq_left hcap],circle_label ht⟩

lemma diagonal_state {t : ℝ} (ht : td ≤ t ∧ t ≤ Real.pi/4) :
    Admissible (diagonal t) (diagonal t) ∧
      label (diagonal t) (diagonal t)=side (diagonal t) (diagonal t) ∧
      side (diagonal t) (diagonal t)=t := by
  have hd := diagonal_td
  have hupper : diagonal t ≤ rd := by rw [← hd]; dsimp [diagonal]; linarith [ht.1]
  have hlower : 1/2 < diagonal t := by dsimp [diagonal]; linarith [ht.2,pi_lt_22_over_7]
  have hphi : phi (diagonal t) (diagonal t) ≤ targetSq := by
    have hrd := rd_sq
    have hp := mul_nonneg (sub_nonneg.mpr hupper)
      (show 0 ≤ rd+diagonal t+1 by linarith [rd_bounds.1])
    dsimp [phi]
    linarith
  have he : side (diagonal t) (diagonal t)=t := by dsimp [side,diagonal]; ring
  have hTA : side (diagonal t) (diagonal t) ≤ axial (diagonal t) := by
    rw [he]
    dsimp [diagonal,axial]
    linarith [ht.2,pi_lt_22_over_7]
  refine ⟨⟨by linarith,le_rfl,hlower.le,hphi⟩,?_,he⟩
  rw [he] at hTA
  simp only [label,he,min_eq_right hTA,min_eq_left ht.2]

lemma sideTop_state {t : ℝ} (ht : s0 ≤ t ∧ t ≤ Real.pi/4) :
    Admissible (sideTopA t) (sideTopU t) ∧
      label (sideTopA t) (sideTopU t)=side (sideTopA t) (sideTopU t) ∧
      side (sideTopA t) (sideTopU t)=t := by
  by_cases hc : t ≤ td
  · simp only [sideTopA,sideTopU,ite_eq_left hc]
    exact circle_state_at_label ⟨ht.1,hc⟩
  · simp only [sideTopA,sideTopU,ite_eq_right hc]
    exact diagonal_state ⟨(lt_of_not_ge hc).le,ht.2⟩

lemma tie_state {t : ℝ} (ht : s0 ≤ t ∧ t ≤ Real.pi/4) :
    Admissible (tieA t) ((4/5)*t) ∧
      label (tieA t) ((4/5)*t)=t ∧ side (tieA t) ((4/5)*t)=t := by
  have hu : 0 ≤ (4/5)*t ∧ (4/5)*t ≤ Real.pi/5 := by
    have hs := transition_coarse
    constructor <;> linarith [ht.1,ht.2]
  have hu0 : u0 ≤ (4/5)*t := by dsimp [s0] at ht; linarith [ht.1]
  have hur : (4/5)*t ≤ rd := by linarith [hu.2,pi_lt_22_over_7,rd_bounds.1]
  have he : axialTop ((4/5)*t)=tieA t := by
    rw [axialTop_right ⟨hu0,hur⟩]
    dsimp [axialLine,tieA]; ring
  obtain ⟨ha,hA⟩ := axialTop_state hu
  rw [he] at ha hA
  exact ⟨ha,by rw [hA]; dsimp [axial]; ring,by dsimp [side,tieA]; ring⟩

/-- Along the axial tie line, a state with label `s` moving with the direction
`x` raises the support `-(A - 1/2) sin x + (v + 1/2) cos x` at this rate,
positive while `sin x ≤ (9/4) cos x`. -/
lemma tie_slope_pos {s x : ℝ} (hs : s0 ≤ s ∧ s ≤ Real.pi/4) (hC : 0 < Real.cos x)
    (hS : 0 ≤ Real.sin x) (hCS : Real.sin x ≤ (9/4)*Real.cos x) :
    0 < (43/90-(4/5)*s)*Real.sin x+(13/10-tieA s)*Real.cos x := by
  have hA : tieA s < 9/8 := by
    have hh : tieA s ≤ tieA s0 := by dsimp [tieA]; linarith [hs.1]
    linarith [transition_coarse.2.1,tieA_s0]
  rcases le_total 0 (43/90-(4/5)*s) with hb | hb
  · nlinarith [mul_nonneg hb hS,mul_pos (show 0 < 13/10-tieA s by linarith) hC]
  · have hcoef : (91:ℝ)/360 ≤ (13/10-tieA s)+(9/4)*(43/90-(4/5)*s) := by
      dsimp [tieA]
      linarith [hs.2,pi_lt_22_over_7]
    nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hCS),
      mul_pos (show 0 < (13/10-tieA s)+(9/4)*(43/90-(4/5)*s) by linarith) hC]

/-- A state with side label `t` lies on the line of slope `4/9` through the
axial tie `(tieA t, 4t/5)`. -/
lemma tie_of_side {a u t : ℝ} (h : side a u=t) : a=tieA t+(4/9)*(u-(4/5)*t) := by
  rw [← h]
  dsimp [side,tieA]
  ring

lemma side_segment {a u : ℝ} (h : Admissible a u)
    (hT : label a u=side a u) :
    (4/5)*label a u ≤ u ∧ u ≤ sideTopU (label a u) ∧
      a=tieA (label a u)+(4/9)*(u-(4/5)*label a u) := by
  let t := label a u
  have ht : s0 ≤ t ∧ t ≤ Real.pi/4 :=
    ⟨(side_state_transition_bounds h hT).2.2,h.label_le_quarter⟩
  have hlin : a=tieA t+(4/9)*(u-(4/5)*t) := tie_of_side hT.symm
  have hlow : (4/5)*t ≤ u := by
    have hh := h.label_le_axial
    dsimp [axial] at hh
    linarith
  have hupp : u ≤ sideTopU t := by
    by_cases hc : t ≤ td
    · obtain ⟨htop,-,htopT⟩ := sideTop_state ht
      have htoplin := tie_of_side htopT
      have hnorm : phi (sideTopA t) (sideTopU t)=targetSq := by
        simp only [sideTopA,sideTopU,ite_eq_left hc]
        have he := (circle_identities ⟨ht.1,hc⟩).1
        dsimp [phi,sideA,sideU]
        linarith
      by_contra hn
      have hu' : sideTopU t < u := lt_of_not_ge hn
      have ha' : sideTopA t < a := by linarith
      have hmu := mul_pos (sub_pos.mpr hu')
        (show 0 < u+sideTopU t+1 by linarith [h.u_nonneg,htop.1])
      have hma := mul_pos (sub_pos.mpr ha')
        (show 0 < a+sideTopA t+1 by linarith [h.a_nonneg,htop.a_nonneg])
      have hp := h.phi_le
      dsimp [phi] at hnorm hp
      linarith
    · simp only [sideTopU,ite_eq_right hc]
      dsimp [diagonal,tieA] at hlin ⊢
      linarith [h.u_le]
  exact ⟨hlow,hupp,hlin⟩

/-! Displacements along the pieces of the boundary, which avoid differentiating
the minimum at its corner. -/

lemma axialTop_antitone {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.pi/5) :
    axialTop v ≤ axialTop u := by
  have hvr : v ≤ rd := by linarith [hv,pi_lt_22_over_7,rd_bounds.1]
  have hc := (circle_order hu huv hvr).1
  have hl : axialLine v ≤ axialLine u := by dsimp [axialLine]; linarith
  exact min_le_min hc hl

lemma axialTop_displacement {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.pi/5) :
    axialTop u-axialTop v ≤ (11/9)*(v-u) := by
  have hvr : v ≤ rd := by linarith [hv,pi_lt_22_over_7,rd_bounds.1]
  have hc := (circle_order hu huv hvr).2
  by_cases hm : circle v ≤ axialLine v
  · have hv' : axialTop v=circle v := min_eq_left hm
    have hu' : axialTop u ≤ circle u := min_le_left _ _
    rw [hv']
    linarith
  · have hv' : axialTop v=axialLine v := min_eq_right (le_of_not_ge hm)
    have hu' : axialTop u ≤ axialLine u := min_le_right _ _
    rw [hv']
    dsimp [axialLine] at hu' ⊢
    linarith

lemma circle_displacement_half {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ u0) :
    circle u-circle v ≤ (1/2)*(v-u) := by
  have hur : v ≤ rd := by linarith [hv,transition_coarse.2.2.2.1,rd_bounds.1]
  have ho := circle_order hu huv hur
  have h0u := circle_order hu (huv.trans hv)
    (show u0 ≤ rd by linarith [transition_coarse.2.2.2.1,rd_bounds.1])
  have h0v := circle_order (hu.trans huv) hv
    (show u0 ≤ rd by linarith [transition_coarse.2.2.2.1,rd_bounds.1])
  rw [circle_u0] at h0u h0v
  have eu := circle_eq ⟨hu,huv.trans hur⟩
  have ev := circle_eq ⟨hu.trans huv,hur⟩
  have hbounds := transition_bounds
  have hratio : 2*(u+v+1) ≤ circle u+circle v+1 := by linarith
  have hid : (circle u-circle v)*(circle u+circle v+1) = (v-u)*(u+v+1) := by
    linarith
  have hmul := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hratio)
  have hden : 0 < circle u+circle v+1 := by linarith [transition_coarse.1]
  by_contra hn
  have hh := mul_pos
    (show 0 < circle u-circle v-(1/2)*(v-u) by linarith) hden
  linarith

lemma sideA_displacement {t s : ℝ}
    (ht : s0 ≤ t) (hts : t ≤ s) (hs : s ≤ td) :
    sideA t-sideA s ≤ (12/13)*(s-t) := by
  let f : ℝ → ℝ := fun x => sideA x+(12/13)*x
  have hm : MonotoneOn f (Icc t s) := by
    apply monoOn_of_hasDeriv_nonneg (d := fun x => 12/13-Y x/Z x)
      (fun x hx => by
        have hh := (hasDerivAt_X ⟨ht.trans hx.1,hx.2.trans hs⟩).sub_const (1/2)
        exact (hh.add ((hasDerivAt_id x).const_mul (12/13))).continuousAt.continuousWithinAt)
    · intro x hx
      exact (((hasDerivAt_X ⟨by linarith [hx.1],by linarith [hx.2]⟩).sub_const (1/2)).fun_add
        ((hasDerivAt_id' x).const_mul (12/13))).congr_deriv (by ring)
    · intro x hx
      have hx' : s0 ≤ x ∧ x ≤ td := ⟨by linarith [hx.1],by linarith [hx.2]⟩
      have hb := circle_bounds hx'
      have he := (circle_identities hx').2.2
      have hZ := Z_pos hx'
      have hle : Y x/Z x ≤ 12/13 := (div_le_iff₀ hZ).mpr (by linarith [hb.2.2.1])
      linarith
  have h := hm ⟨le_rfl,hts⟩ ⟨hts,le_rfl⟩ hts
  dsimp [f] at h
  linarith

lemma side_radial_upper {a u : ℝ} (h : Admissible a u)
    (hT : label a u=side a u) : a ≤ sideTopA (label a u) := by
  have hs := side_segment h hT
  have htop := tie_of_side (sideTop_state
    ⟨(side_state_transition_bounds h hT).2.2,h.label_le_quarter⟩).2.2
  linarith [hs.2.1,hs.2.2]

end Boundary
end SquaresInCircles.Seven
