module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameSecondaryPositiveZero

/-!
# All positive halves of the three same-sign secondary owners

Uncompiled transcription of Section 2 of
`HAND_SHORT_WORD_SAME_SIGN_SECONDARY_COMPLETE_WITHOUT_TABLES.md`.
Compactness is applied to the entire genuine contact strip. Its moving
zero-source and diagonal-target boundaries increase from alignment;
an interior target minimum has a positive angular derivative. The
independent whole-arc floor covers all later angles.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Positive
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)

lemma diagonal_first_positive (r : Row) {x : ℝ} (hx : x∈Icc 0 strip) :
    0<first r outerDiagonal x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  have hd : Domain outerDiagonal x := ⟨hdiag,hx,(contact_target_diagonal hx).1.le⟩
  have hl := slope_bounds r (source_mem hd)
  have ht := strip_trig hx
  have hf := positive_trig (angle_full hx)
  have he : contactAngle outerDiagonal x=
      -(outerDiagonal-1/2)*(Real.cos x-Real.sin x) := by
    dsimp [contactAngle,D,SecondWord.U,SecondWord.W]
    rw [SameContact.arc_diagonal]
    ring
  have hmu0 : 0≤(outerDiagonal-1/2)*(Real.cos x-Real.sin x) :=
    mul_nonneg (by linarith [outer_endpoint_bounds.2.2.1]) (by linarith [ht.2.2.2])
  have hmu := mul_le_mul
    (show outerDiagonal-1/2≤(2/5:ℝ) by linarith [outer_endpoint_bounds.2.2.2])
    (show Real.cos x-Real.sin x≤1 by linarith [hf.2.1,ht.2.1])
    (by linarith [ht.2.2.2]) (by norm_num)
  have hprod := mul_le_mul hl.2.le hmu hmu0 (by norm_num : (0:ℝ)≤6/5)
  rw [first,he]
  nlinarith

lemma diagonal_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 strip) :
    (8981/10000:ℝ)<cost r outerDiagonal x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  have hdom : ∀y∈Icc 0 strip,Domain outerDiagonal y :=
    fun y hy => ⟨hdiag,hy,(contact_target_diagonal hy).1.le⟩
  have hm : MonotoneOn (cost r outerDiagonal) (Icc 0 strip) := monoOn_of_hasDeriv_nonneg
    (fun y hy => (cost_angle_hasDerivAt r (hdom y hy)).continuousAt.continuousWithinAt)
    (fun y hy => cost_angle_hasDerivAt r (hdom y (Ioo_subset_Icc_self hy)))
    (fun y hy => (diagonal_first_positive r (Ioo_subset_Icc_self hy)).le)
  have h0 : (0:ℝ)∈Icc 0 strip := by norm_num [strip]
  exact (initial_lower r (hdom 0 h0)).trans_le (hm h0 hx hx.1)

lemma interior_not_minimum (r : Row) {B x : ℝ} (hd : Domain B x)
    (hx : 0<x) (hB : B<outerDiagonal) (hb : 0<contact B x)
    (hmin : ∀C y,Domain C y→cost r B x≤cost r C y) : False := by
  let T : Set ℝ := Ioo 0 outerDiagonal ∩ (fun C => contact C x) ⁻¹' Ioi 0
  have hcontactT : Continuous (fun C => contact C x) := by dsimp [contact,arc]; fun_prop
  have hT : IsOpen T := isOpen_Ioo.inter (isOpen_Ioi.preimage hcontactT)
  have hmemT : B∈T := ⟨⟨target_positive hd,hB⟩,hb⟩
  have hlocalT : IsLocalMin (fun C => cost r C x) B := by
    filter_upwards [hT.mem_nhds hmemT] with C hC
    exact hmin C x ⟨Ioo_subset_Icc_self hC.1,hd.2.1,hC.2.le⟩
  have hstat : targetFirst r B x=0 :=
    hlocalT.hasDerivAt_eq_zero (cost_target_hasDerivAt r hd)
  have hfirst : (33/100:ℝ)<first r B x := by
    rw [stationary_first r hd hstat]
    exact transport_lower r hd.1 hd.2.1
  let O : Set ℝ := Ioi 0 ∩ (contact B) ⁻¹' Ioi 0
  have hcontactO : Continuous (contact B) := by dsimp [contact]; fun_prop
  have hO : IsOpen O := isOpen_Ioi.inter (isOpen_Ioi.preimage hcontactO)
  have hmemO : x∈O := ⟨hx,hb⟩
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hmemO
  have hdom {y : ℝ} (hy : y∈Icc (x-ε) x) : Domain B y := by
    have hh := hsub (show y∈Icc (x-ε) (x+ε) from ⟨hy.1,by linarith [hy.2]⟩)
    exact ⟨hd.1,⟨hh.1.le,hy.2.trans hd.2.1.2⟩,hh.2.le⟩
  have hn := ContactMinimumDerivatives.right_endpoint (show x-ε<x by linarith)
    (first_continuousAt r hd) (fun y hy => cost_angle_hasDerivAt r (hdom hy))
    (fun y hy => hmin B y (hdom hy))
  linarith

lemma minimum_lower (r : Row) {B x : ℝ} (hd : Domain B x)
    (hmin : ∀C y,Domain C y→cost r B x≤cost r C y) :
    (8981/10000:ℝ)<cost r B x := by
  by_cases hx : x=0
  · subst x
    exact initial_lower r hd
  by_cases hb : contact B x=0
  · exact Zero.original_lower r hd hb
  by_cases hB : B=outerDiagonal
  · subst B
    exact diagonal_lower r hd.2.1
  exact (interior_not_minimum r hd (lt_of_le_of_ne hd.2.1.1 (Ne.symm hx))
    (lt_of_le_of_ne hd.1.2 hB) (lt_of_le_of_ne hd.2.2 (Ne.symm hb)) hmin).elim

theorem contact_lower (r : Row) {B x : ℝ} (hd : Domain B x) :
    (8981/10000:ℝ)<cost r B x := by
  let guard : ℝ×ℝ→ℝ := fun z => contact z.1 z.2
  let objective : ℝ×ℝ→ℝ := fun z => cost r z.1 z.2
  have hg : Continuous guard := by dsimp [guard,contact,arc]; fun_prop
  have hf : Continuous objective := by dsimp [objective,cost,target,targetCost,contact,arc]; fun_prop
  obtain ⟨z,hz,hbetter,hmin⟩ := contact_region_minimum hg hf
    (p₀ := (B,x)) ⟨hd.1,hd.2.1,hd.2.2⟩
  have hzd : Domain z.1 z.2 := ⟨hz.1,hz.2.1,hz.2.2⟩
  have hh := minimum_lower r hzd (fun C y hCy => hmin (C,y) hCy.1 hCy.2.1 hCy.2.2)
  exact hh.trans_le hbetter

lemma original_strip (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 strip)
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x) :
    (8981/10000:ℝ)<Real.pi/2+x+c r-P r*a+t r*b+p r*A-q r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hc : contact B x≤b := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2+x+c r+target r b+targetCost r B=
      Real.pi/2+x+c r-P r*a+t r*b+p r*A-q r*B := by
    have hh := original_cost r hs ht
    linarith
  rw [←hcost]
  by_cases hactive : 0≤contact B x
  · have hd : Domain B x := ⟨hB,hx,hactive⟩
    have hsource := target_monotone r (source_mem hd) hb hc
    have hh := contact_lower r hd
    dsimp [cost] at hh
    linarith
  · have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
      ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
    have hcont : Continuous (fun D => contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,he⟩ := intermediate_value_Icc hB.2 hcont.continuousOn
      (show (0:ℝ)∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨by linarith,(contact_target_diagonal hx).1.le⟩)
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hB.1.trans hD.1,hD.2⟩
    have htarget := targetCost_antitone r hB hDouter hD.1
    have hsource := target_monotone r
      (show (0:ℝ)∈Icc 0 outerDiagonal from ⟨le_rfl,hdiag.1⟩) hb hb.1
    have hh := contact_lower r (show Domain D x from ⟨hDouter,hx,he.ge⟩)
    dsimp [cost] at hh
    rw [he] at hh
    linarith

theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x) :
    (449/500:ℝ)<Real.pi/2+x+c r-P r*a+t r*b+p r*A-q r*B := by
  by_cases hstrip : x≤strip
  · linarith [original_strip r hs ht ⟨hx.1,hstrip⟩ hm]
  · have hh := independent_lower (x := x) r hs ht
    dsimp [strip] at hstrip
    linarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Same.Secondary.Positive
