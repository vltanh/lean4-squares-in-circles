module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameStationaryExclusion
public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameDiagonalLate
public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameCap
public import SquaresInCircles.Eight.TableFree.ContactMinimumDerivatives
public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJMinimum

/-!
# The complete favorable same-sign outer zero contact

Uncompiled transcription of Section 7. Compactness is applied to the
entire genuine contact region. The target axis, late source diagonal,
and interior stationary alternatives are excluded by their proved
feasible descents; the early diagonal and final angle have the strict
written bounds. The original weak separator is restored at the end.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)
open SecondWord (outer_domain outer_zero_mem)

lemma angleSecond_continuousAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    ContinuousAt (angleSecond r B) x := by
  have hb := (SecondWord.SameZero.b_angle_hasDerivAt B x).continuousAt
  have hv := (SecondWord.SameZero.v_angle_hasDerivAt B x).continuousAt
  have hα := (alpha_hasDerivAt r hd.2.2).continuousAt.comp x hb
  have hl := (l_hasDerivAt r hd.2.2).continuousAt.comp x hb
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
    have heU : e<(3/10:ℝ) := by norm_num [Event.hi] at he; linarith [he.1.2]
    have hh := Event.zero_decrease (Event.angle_mem he) hd.2.1 (by linarith)
    rw [he.2,hdiag] at hh
    linarith
  have hdom {C : ℝ} (hC : C∈Icc 0 B) : Domain C x := by
    have hCi : C∈Icc 0 outerDiagonal := ⟨hC.1,hC.2.trans hd.1.2⟩
    have hm := SecondWord.SameZero.b_target_monotone hd.2.1 hCi hd.1 hC.2
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
  have hc : Continuous (contact B) := by dsimp [contact,SecondWord.SameZero.b]; fun_prop
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

/-- No extra stationary or boundary hypothesis is retained in this export. -/
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

/-- All four literal rows at the original weak source-secondary owner. -/
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

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same
