module

public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJMinimum
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameCap
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameDiagonalLate
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameStationaryShape
public import SquaresInCircles.Eight.Words.Wrong.ZeroOriginalOwners

/-!
# Eight squares: all eight same-sign outer zero-secondary families of the short word

The four favorable coupled estimates and four
unfavorable supports are restored to the original role, radial states,
and original weak owner. Reflection/reversal is only an exact algebraic
exchange of the original pair; the literal cycle labels are unchanged.
-/

section
/-!
## The complete coupled stationary-point exclusion

The first curved row
uses its full height interval. The last row retains the source-height
chord and the written increasing quadratic on [.5,.78]. Together with
the affine row, a stationary contact has either negative angular
curvature or a strictly negative target derivative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
open CommonQuarter CorePairGeometry Arithmetic

lemma height_mass (r : Row) (b : ℝ) : mass r b=Q0+1-2*height r b := by
  dsimp [height]
  ring

lemma fraction_upper {r : Row} {b Z L H : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hz : z b≤Z) (hZ : 0≤Z)
    (hl : l r b≤L) (hH : height r b≤H) (hT : 0<Q0+1-2*H) :
    z b*l r b/mass r b≤Z*L/(Q0+1-2*H) := by
  have hpos := l_positive r hb
  have hL : 0≤L := hpos.le.trans hl
  have hnum := mul_le_mul hz hl hpos.le hZ
  have hmass : Q0+1-2*H≤ mass r b := by rw [height_mass]; linarith
  have hfirst := div_le_div_of_nonneg_right hnum (mass_positive r hb).le
  have hsecond := div_le_div_of_nonneg_left (mul_nonneg hZ hL) hT hmass
  exact hfirst.trans hsecond

lemma row_one_target_negative {b : ℝ} (hb : b∈sourceDomain) (hG : G 1 b≤0) :
    stationaryTarget 1 b<0 := by
  have hcut := row_one_source hb hG
  have hH := row_one_height ⟨hb.1,hcut.le⟩
  have hdom : height 1 b∈Icc (1747/1000:ℝ) (951/500) :=
    ⟨by linarith [hH.1],by linarith [hH.2.1]⟩
  have hratio := targetRatio_upper hdom (by norm_num : (0:ℝ)≤923/500)
    hH.1.le (by norm_num : (0:ℝ)<387/1000) (by norm_num [Q0])
  have hratio0 := targetRatio_nonneg (show 0<height 1 b by linarith [hH.1])
  have hfrac := fraction_upper (source_outer hb)
    (show z b≤(1/10:ℝ) by dsimp [z]; linarith) (by norm_num)
    hH.2.2.le hH.2.1.le (by norm_num [Q0] : 0<Q0+1-2*(1891/1000))
  have hbracket : P 1+z b*l 1 b/mass 1 b≤
      P 1+(1/10)*(943/1000)/(Q0+1-2*(1891/1000)) := by linarith
  have hp := mul_le_mul_of_nonneg_left hbracket hratio0
  have hq := mul_le_mul_of_nonneg_right hratio.le
    (by norm_num [P,Q0] : (0:ℝ)≤P 1+(1/10)*(943/1000)/(Q0+1-2*(1891/1000)))
  have hf := f_monotone hdom (by norm_num) hH.2.1.le
  have href : f (1891/1000)+(387/1000)*
      (P 1+(1/10)*(943/1000)/(Q0+1-2*(1891/1000)))-t 1< -(6/625:ℝ) := by
    norm_num [f,P,t,Q0]
  dsimp [stationaryTarget]
  linarith

abbrev lastHeight : ℝ := 92117/50000
abbrev lastMass : ℝ := Q0+1-2*lastHeight
abbrev chordSlope : ℝ := (2367/25000)/(487/1000)
def ratioLine (b : ℝ) : ℝ := 82969/25000-(158863/100000)*chordHeight b
def finalBracket (b : ℝ) : ℝ := P 3+(233/250)*(b-1/2)/lastMass

def quadratic (b : ℝ) : ℝ := f lastHeight+ratioLine b*finalBracket b-t 3
def quadraticD (b : ℝ) : ℝ :=
  -(158863/100000)*chordSlope*finalBracket b+ratioLine b*(233/250)/lastMass

lemma quadratic_hasDerivAt (b : ℝ) : HasDerivAt quadratic (quadraticD b) b := by
  have hR : HasDerivAt ratioLine (-(158863/100000)*chordSlope) b := by
    have h : HasDerivAt (fun y => (82969/25000:ℝ)-(158863/100000)*
        ((4369/2500:ℝ)+(2367/25000)/(487/1000)*(y-293/1000)))
        (-((158863/100000)*((2367/25000)/(487/1000)*1))) b :=
      ((((hasDerivAt_id' b).sub_const (293/1000:ℝ)).const_mul
        ((2367/25000)/(487/1000):ℝ)).const_add (4369/2500:ℝ)).const_mul
          (158863/100000:ℝ) |>.const_sub (82969/25000:ℝ)
    exact h.congr_deriv (by simp only [chordSlope]; ring)
  have hB : HasDerivAt finalBracket ((233/250)/lastMass) b := by
    have h : HasDerivAt (fun y => P 3+(233/250)*(y-1/2)/lastMass)
        ((233/250)*1/lastMass) b :=
      ((((hasDerivAt_id' b).sub_const (1/2:ℝ)).const_mul (233/250:ℝ)).div_const
        lastMass).const_add (P 3)
    exact h.congr_deriv (by ring)
  have h : HasDerivAt (fun y => f lastHeight+ratioLine y*finalBracket y-t 3)
      (-(158863/100000)*chordSlope*finalBracket b+ratioLine b*((233/250)/lastMass)) b :=
    ((hR.mul hB).const_add (f lastHeight)).sub_const (t 3)
  exact h.congr_deriv (by simp only [quadraticD]; ring)

lemma quadratic_derivative_positive {b : ℝ} (hb : b∈Icc (1/2:ℝ) (39/50)) :
    (16/125:ℝ)<quadraticD b := by
  norm_num [quadraticD,finalBracket,ratioLine,chordHeight,chordSlope,lastMass,lastHeight,P,Q0]
  linarith [hb.1,hb.2]

lemma quadratic_negative {b : ℝ} (hb : b∈Icc (1/2:ℝ) (39/50)) : quadratic b<0 := by
  have hm : MonotoneOn quadratic (Icc (1/2:ℝ) (39/50)) :=
    monoOn_of_hasDeriv_nonneg
      (fun b _ => (quadratic_hasDerivAt b).continuousAt.continuousWithinAt)
      (fun b _ => quadratic_hasDerivAt b)
      (fun b hb => by linarith [quadratic_derivative_positive (Ioo_subset_Icc_self hb)])
  have hh := hm hb (by norm_num) hb.2
  have href : quadratic (39/50)< -(629/100000:ℝ) := by
    norm_num [quadratic,f,ratioLine,chordHeight,finalBracket,lastHeight,lastMass,P,t,Q0]
  linarith

lemma row_three_early_target_negative {b : ℝ} (hb : b∈sourceDomain)
    (hG : G 3 b≤0) (hsmall : b≤1/2) : stationaryTarget 3 b<0 := by
  have hcut := row_three_source hb hG
  have hH := row_three_height ⟨hb.1,hcut.le⟩
  have hdom : height 3 b∈Icc (1747/1000:ℝ) (951/500) :=
    ⟨by linarith [hH.1],by linarith [hH.2.1]⟩
  have hratio := targetRatio_upper hdom (by norm_num : (0:ℝ)≤4369/2500)
    hH.1.le (by norm_num : (0:ℝ)<533/1000) (by norm_num [Q0])
  have hratio0 := targetRatio_nonneg (show 0<height 3 b by linarith [hH.1])
  have hfrac : z b*l 3 b/mass 3 b≤0 :=
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by dsimp [z]; linarith) (l_positive 3 (source_outer hb)).le)
      (mass_positive 3 (source_outer hb)).le
  have hp := mul_le_mul_of_nonneg_left
    (show P 3+z b*l 3 b/mass 3 b≤P 3 by linarith) hratio0
  have hq := mul_le_mul_of_nonneg_right hratio.le (by norm_num [P] : (0:ℝ)≤P 3)
  have hf := f_monotone hdom (by norm_num [lastHeight]) hH.2.1.le
  have href : f lastHeight+(533/1000)*P 3-t 3< -(21/500:ℝ) := by
    norm_num [f,lastHeight,P,t,Q0]
  dsimp [stationaryTarget]
  linarith

lemma row_three_late_target_negative {b : ℝ} (hb : b∈sourceDomain)
    (hG : G 3 b≤0) (hlarge : 1/2≤b) : stationaryTarget 3 b<0 := by
  have hcut := row_three_source hb hG
  have hsrc : b∈Icc (293/1000:ℝ) (39/50) := ⟨hb.1,hcut.le⟩
  have hH := row_three_height hsrc
  have hdom : height 3 b∈ratioDomain := ⟨hH.1.le,hH.2.1.le⟩
  have hchord := row_three_chord hsrc
  have hratio := targetRatio_tangent hdom
  have hbound : targetRatio (height 3 b)<ratioLine b := by
    dsimp only [ratioLine]
    linarith
  have hratio0 := targetRatio_nonneg (show 0<height 3 b by linarith [hH.1])
  have hfrac := fraction_upper (source_outer hb) (le_refl (z b))
    (show 0≤z b by dsimp [z]; linarith) hH.2.2.le hH.2.1.le
    (by norm_num [Q0,lastHeight] : 0<Q0+1-2*lastHeight)
  have he : z b*(233/250)/(Q0+1-2*(92117/50000))=(233/250)*(b-1/2)/lastMass := by
    simp only [z,lastMass,lastHeight]
    ring
  have hbracket : P 3+z b*l 3 b/mass 3 b≤finalBracket b := by
    dsimp only [finalBracket]
    linarith
  have hm : 0<lastMass := by norm_num [lastMass,lastHeight,Q0]
  have hB0 : 0≤finalBracket b := by
    have hq := div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤233/250) (sub_nonneg.mpr hlarge)) hm.le
    have hP : (0:ℝ)≤P 3 := by norm_num [P]
    dsimp only [finalBracket]
    linarith
  have hprod := mul_le_mul_of_nonneg_left hbracket hratio0
  have hprodU := mul_le_mul_of_nonneg_right hbound.le hB0
  have hf := f_monotone (ratio_domain_inclusion hdom) (by norm_num [lastHeight]) hH.2.1.le
  have hupper : stationaryTarget 3 b≤quadratic b := by
    dsimp only [stationaryTarget,quadratic]
    linarith
  exact hupper.trans_lt (quadratic_negative ⟨hlarge,hcut.le⟩)

lemma row_three_target_negative {b : ℝ} (hb : b∈sourceDomain) (hG : G 3 b≤0) :
    stationaryTarget 3 b<0 := by
  rcases le_total b (1/2) with hsmall | hlarge
  · exact row_three_early_target_negative hb hG hsmall
  · exact row_three_late_target_negative hb hG hlarge

lemma target_negative (r : Row) (hr : Coupled r) {b : ℝ}
    (hb : b∈sourceDomain) (hG : G r b≤0) : stationaryTarget r b<0 := by
  fin_cases r
  · exact row_zero_target_negative hb hG
  · exact row_one_target_negative hb hG
  · exact (hr rfl).elim
  · exact row_three_target_negative hb hG

/-- The two alternatives in equation (14), at the actual original contact. -/
theorem stationary_descent (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) (hstat : angleFirst r B x=0) :
    angleSecond r B x<0 ∨ targetFirst r B x<0 := by
  have hsource : contact B x∈sourceDomain :=
    ⟨(SecondWord.SameZero.b_lower hd.1 hd.2.1).le,hd.2.2.2⟩
  by_cases hG : G r (contact B x)≤0
  · right
    rw [actual_target r hd hstat]
    exact target_negative r hr hsource hG
  · left
    rw [actual_second r hd hstat]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (l_positive r hd.2.2)) (lt_of_not_ge hG)

end SquaresInCircles.Eight.ShortOuterZero.Same.Stationary
end
end
end

section
/-!
## The favorable same-sign outer zero contact

Compactness is applied to the whole contact region. The target axis, the late source diagonal and
the interior stationary alternatives are excluded by feasible descents
(`minimum_not_zero_target`, `minimum_not_late_diagonal`, `interior_not_minimum`); the early
diagonal and the final angle have strict bounds (`minimum_lower`, `whole_contact_lower`). The
original weak separator is restored at the end (`original`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterZero.Same
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open SecondWord (outer_domain outer_zero_mem)

lemma angleSecond_continuousAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    ContinuousAt (angleSecond r B) x := by
  have hb := (SecondWord.SameZero.b_angle_hasDerivAt B x).continuousAt
  have hv := (SecondWord.SameZero.v_angle_hasDerivAt B x).continuousAt
  have hα := ContinuousAt.comp (x := x) (alpha_hasDerivAt r hd.2.2).continuousAt hb
  have hl := ContinuousAt.comp (x := x) (l_hasDerivAt r hd.2.2).continuousAt hb
  exact (hα.mul (hv.pow 2)).sub (hl.mul (hb.sub continuousAt_const))

lemma minimum_not_zero_target (r : Row) (hr : Coupled r) {x : ℝ}
    (hd : Domain 0 x) (hinterior : contact 0 x<outerDiagonal)
    (hmin : ∀B y, Domain B y → cost r 0 x≤cost r B y) : False := by
  let O : Set ℝ := (fun B => contact B x) ⁻¹' Ioo 0 outerDiagonal
  have hcont : Continuous (fun B => contact B x) := by
    dsimp [contact,SecondWord.SameZero.b,arc]
    fun_prop
  have hO : IsOpen O := isOpen_Ioo.preimage hcont
  have hmem : (0:ℝ)∈O := ⟨by linarith [SecondWord.SameZero.b_lower hd.1 hd.2.1],hinterior⟩
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hmem
  let u := min ε outerDiagonal
  have hu : 0<u := lt_min hε (by linarith [outer_endpoint_bounds.2.2.1])
  have hdom {B : ℝ} (hB : B∈Icc 0 u) : Domain B x := by
    have hsource := hsub (show B∈Icc (0-ε) (0+ε) from
      ⟨by linarith [hB.1],by have hh := hB.2.trans (min_le_left ε outerDiagonal); linarith⟩)
    exact ⟨⟨hB.1,hB.2.trans (min_le_right _ _)⟩,hd.2.1,Ioo_subset_Icc_self hsource⟩
  have hnecessary := ContactMinimumDerivatives.left_endpoint hu
    (targetFirst_hasDerivAt r hd).continuousAt
    (fun B hB => cost_target_hasDerivAt r (hdom hB))
    (fun B hB => hmin B x (hdom hB))
  exact (not_lt_of_ge hnecessary) (Axial.target_negative r hr hd)

lemma minimum_not_late_diagonal (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) (hdiag : contact B x=outerDiagonal) (hx : 3/10≤x)
    (hmin : ∀C y, Domain C y → cost r B x≤cost r C y) : False := by
  have hBpos : 0<B := by
    by_contra! hBnon
    have hBzero : B=0 := le_antisymm hBnon hd.1.1
    subst B
    obtain ⟨e,he⟩ := Event.exists_event
    have heU : e<(3/10:ℝ) := by
      have h2 : e<1072633/10000000 := he.1.2
      linarith
    have hh := Event.zero_decrease (Event.angle_mem he) hd.2.1 (by linarith)
    rw [he.2,hdiag] at hh
    linarith
  have hdom {C : ℝ} (hC : C∈Icc 0 B) : Domain C x := by
    have hCi : C∈Icc 0 outerDiagonal := ⟨hC.1,hC.2.trans hd.1.2⟩
    have hm : contact C x≤contact B x :=
      SecondWord.SameZero.b_target_monotone hd.2.1 hCi hd.1 hC.2
    rw [hdiag] at hm
    exact ⟨hCi,hd.2.1,⟨by linarith [SecondWord.SameZero.b_lower hCi hd.2.1],hm⟩⟩
  have hnecessary := ContactMinimumDerivatives.right_endpoint hBpos
    (targetFirst_hasDerivAt r hd).continuousAt
    (fun C hC => cost_target_hasDerivAt r (hdom hC))
    (fun C hC => hmin C x (hdom hC))
  exact (not_lt_of_ge hnecessary) (Diagonal.original_late_slope r hr hd hdiag hx)

lemma interior_not_minimum (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) (hB : B∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hb : contact B x∈Ioo 0 outerDiagonal)
    (hmin : ∀C y, Domain C y → cost r B x≤cost r C y) : False := by
  let O : Set ℝ := Ioo 0 (7/10) ∩ (contact B) ⁻¹' Ioo 0 outerDiagonal
  have hc : Continuous (contact B) := continuous_iff_continuousAt.2 fun y =>
    (SecondWord.SameZero.b_angle_hasDerivAt B y).continuousAt
  have hO : IsOpen O := isOpen_Ioo.inter (isOpen_Ioo.preimage hc)
  have hmem : x∈O := ⟨hx,hb⟩
  have hdom {y : ℝ} (hy : y∈O) : Domain B y :=
    ⟨hd.1,Ioo_subset_Icc_self hy.1,Ioo_subset_Icc_self hy.2⟩
  have hlocal : IsLocalMin (cost r B) x := by
    filter_upwards [hO.mem_nhds hmem] with y hy
    exact hmin B y (hdom hy)
  have hstat : angleFirst r B x=0 := hlocal.hasDerivAt_eq_zero (cost_angle_hasDerivAt r hd)
  have hsecond : 0≤angleSecond r B x :=
    ContactMinimumDerivatives.second_nonnegative hO hmem
      (fun y hy => hmin B y (hdom hy))
      (fun y hy => cost_angle_hasDerivAt r (hdom hy))
      (fun y hy => angleFirst_hasDerivAt r (hdom hy))
      (angleSecond_continuousAt r hd)
  rcases Stationary.stationary_descent r hr hd hstat with hcurv | htarget
  · exact (not_lt_of_ge hsecond) hcurv
  · let T : Set ℝ := Ioo 0 outerDiagonal ∩ (fun C => contact C x) ⁻¹' Ioo 0 outerDiagonal
    have hcont : Continuous (fun C => contact C x) := by
      dsimp [contact,SecondWord.SameZero.b,arc]
      fun_prop
    have hT : IsOpen T := isOpen_Ioo.inter (isOpen_Ioo.preimage hcont)
    have hmemT : B∈T := ⟨hB,hb⟩
    have hlocalT : IsLocalMin (fun C => cost r C x) B := by
      filter_upwards [hT.mem_nhds hmemT] with C hC
      exact hmin C x ⟨Ioo_subset_Icc_self hC.1,hd.2.1,Ioo_subset_Icc_self hC.2⟩
    have he := hlocalT.hasDerivAt_eq_zero (cost_target_hasDerivAt r hd)
    linarith

lemma minimum_lower (r : Row) (hr : Coupled r) {B x : ℝ} (hd : Domain B x)
    (hmin : ∀C y, Domain C y → cost r B x≤cost r C y) :
    (11226/12500:ℝ)<cost r B x := by
  by_cases hcap : x=7/10
  · subst x
    exact Cap.lower r hr hd
  by_cases hdiag : contact B x=outerDiagonal
  · by_cases hearly : x≤3/10
    · exact Diagonal.original_early_lower r hr hd hdiag hearly
    · exact (minimum_not_late_diagonal r hr hd hdiag (le_of_not_ge hearly) hmin).elim
  have hsource : contact B x∈Ioo 0 outerDiagonal :=
    ⟨by linarith [SecondWord.SameZero.b_lower hd.1 hd.2.1],lt_of_le_of_ne hd.2.2.2 hdiag⟩
  by_cases hBzero : B=0
  · subst B
    exact (minimum_not_zero_target r hr hd hsource.2 hmin).elim
  have hB : B∈Ioo 0 outerDiagonal :=
    ⟨lt_of_le_of_ne hd.1.1 (Ne.symm hBzero),SecondWord.SameZero.PJ.target_strict hd⟩
  have hx : x∈Ioo 0 (7/10) := ⟨angle_positive hd,lt_of_le_of_ne hd.2.1.2 hcap⟩
  exact (interior_not_minimum r hr hd hB hx hsource hmin).elim

/-- The bound on the whole contact region, with no stationary or boundary hypothesis. -/
theorem whole_contact_lower (r : Row) (hr : Coupled r) {B x : ℝ}
    (hd : Domain B x) : (11226/12500:ℝ)<cost r B x := by
  let guard : ℝ×ℝ→ℝ := fun p => outerDiagonal-contact p.1 p.2
  let objective : ℝ×ℝ→ℝ := fun p => cost r p.1 p.2
  have hg : Continuous guard := by dsimp [guard,contact,SecondWord.SameZero.b,arc]; fun_prop
  have hf : Continuous objective := by dsimp [objective,cost,contact,SecondWord.SameZero.b,arc]; fun_prop
  obtain ⟨p,hp,hbetter,hmin⟩ := contact_region_minimum hg hf
    (p₀ := (B,x)) ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2.2⟩
  have hpd : Domain p.1 p.2 := ⟨hp.1,hp.2.1,
    ⟨by linarith [SecondWord.SameZero.b_lower hp.1 hp.2.1],sub_nonneg.mp hp.2.2⟩⟩
  have hl := minimum_lower r hr hpd (fun C y hCy =>
    hmin (C,y) hCy.1 hCy.2.1 (sub_nonneg.mpr hCy.2.2.2))
  exact hl.trans_le hbetter

/-- All four rows at the original weak source-secondary owner. -/
theorem original (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (449/500:ℝ)<x+c r+p r*a+q r*b-P r*A-t r*B := by
  by_cases htwo : r=2
  · subst r
    exact PositiveCoefficient.original hs ht hx hm
  · have hcontact := original_to_contact r hs ht hx hm
    have hl := whole_contact_lower r htwo hcontact.1
    linarith [hcontact.2]

end SquaresInCircles.Eight.ShortOuterZero.Same
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ShortOuterZero.SameCycle
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

lemma roles (i : Vertex) (σ : Bool)
    (hi : WordProblems.wrongWord .short i=0)
    (ha : WordProblems.allowed .short i σ σ) :
    (i=0 ∧ σ=true) ∨ (i=1 ∧ σ=false) ∨ (i=3 ∧ σ=true) ∨ (i=3 ∧ σ=false) := by
  revert hi ha
  fin_cases i <;> cases σ <;>
    norm_num [WordProblems.allowed,WordProblems.wrongWord,next]

private lemma reverse_target {a b A B x σ : ℝ}
    (hm : 0≤Eight.forwardMargin 2 a b A B σ σ x) :
    0≤Eight.forwardMargin 0 A B a b (-σ) (-σ) x := by
  simp only [Eight.forwardMargin,Matrix.cons_val] at hm ⊢
  linarith

macro "short_same_literal" : tactic => `(tactic|
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,next,
    Same.c,Same.p,Same.q,Same.P,Same.t,
    Unfavorable.c,Unfavorable.p,Unfavorable.q,Unfavorable.P,Unfavorable.t] at *
  <;> linarith)

/-- Every literal same-sign outer zero-secondary row on its full closed domain. -/
theorem original (i : Vertex) (σ : Bool)
    (hi : WordProblems.wrongWord .short i=0)
    (ha : WordProblems.allowed .short i σ σ)
    {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : |x|≤7/10) (j : Fin 4) (hj : j=0 ∨ j=2)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign σ) x) :
    (449/500:ℝ)<x+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) .outer σ A B := by
  rcases roles i σ hi ha with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases hj with rfl | rfl
    · have hh := Same.original (0:Same.Row) hs ht hx (by simpa [WordProblems.sign] using hm)
      short_same_literal
    · have hrev := reverse_target (by simpa [WordProblems.sign] using hm :
        0≤Eight.forwardMargin 2 a b A B 1 1 x)
      have hh := Unfavorable.original_cost (0:Unfavorable.Row) ht hs hx (by simpa using hrev)
      short_same_literal
  · rcases hj with rfl | rfl
    · have hh := Unfavorable.original_cost (1:Unfavorable.Row) hs ht hx
        (by simpa [WordProblems.sign] using hm)
      short_same_literal
    · have hrev := reverse_target (by simpa [WordProblems.sign] using hm :
        0≤Eight.forwardMargin 2 a b A B (-1) (-1) x)
      have hh := Same.original (1:Same.Row) ht hs hx (by simpa using hrev)
      short_same_literal
  · rcases hj with rfl | rfl
    · have hh := Same.original (2:Same.Row) hs ht hx (by simpa [WordProblems.sign] using hm)
      short_same_literal
    · have hrev := reverse_target (by simpa [WordProblems.sign] using hm :
        0≤Eight.forwardMargin 2 a b A B 1 1 x)
      have hh := Unfavorable.original_cost (2:Unfavorable.Row) ht hs hx (by simpa using hrev)
      short_same_literal
  · rcases hj with rfl | rfl
    · have hh := Unfavorable.original_cost (3:Unfavorable.Row) hs ht hx
        (by simpa [WordProblems.sign] using hm)
      short_same_literal
    · have hrev := reverse_target (by simpa [WordProblems.sign] using hm :
        0≤Eight.forwardMargin 2 a b A B (-1) (-1) x)
      have hh := Same.original (3:Same.Row) ht hs hx (by simpa using hrev)
      short_same_literal

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hword : WordProblems.wrongWord .short i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .short hw i
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have haxis : j=0 ∨ j=2 := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hm := original_margin C F hgap i j howner
  have hh := original i (positiveOf C i) hword (by simpa [←hsg] using ha)
    hsource htarget hx j haxis (by simpa [←hsg] using hm)
  simpa only [wrongMarker,hs,ht,←hsg] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) :
    (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  exact actual_owner C F hgap hw i hi hs ht hsg j
    (by simpa only [←hj] using C.feasible i)

end SquaresInCircles.Eight.ShortOuterZero.SameCycle
end
end
end
