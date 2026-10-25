module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroPlusDiagonalBoundary
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroNegativePJ

/-!
# The complete original asymmetric opposite zero-quarter pair

Uncompiled source draft.  Positive contacts decrease in angle to
alignment or the proved source diagonal.  A weak original separator
lowers its source, or its target after the source reaches zero, to an
actual contact.  Negative contacts lower only their source.  Both
literal P/J orders are retained throughout.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Asymmetric
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def F (reverse : Bool) : RoleLabel := if reverse then JLabel else PLabel
def G (reverse : Bool) : RoleLabel := if reverse then PLabel else JLabel

lemma label_monotone (reverse : Bool) : MonotoneOn (F reverse).outer (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun t ht => ((F reverse).outer_hasDerivAt (outer_domain ht)).continuousAt.continuousWithinAt)
    (fun t ht => (F reverse).outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht)))
  intro t ht
  cases reverse <;> dsimp [F] <;>
    first | linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1] |
      linarith [(J_first_bounds (Ioo_subset_Icc_self ht)).1]

lemma positive_derivative (reverse : Bool) {B x : ℝ} (hd : PlusDomain B x) :
    0<plusFirst (F reverse) B x := by
  cases reverse
  · exact PositivePJ.P_positive hd
  · exact PositivePJ.J_positive hd

theorem plus_lower (reverse : Bool) {B x : ℝ} (hd : PlusDomain B x) :
    (44889/50000:ℝ)<plusCost (F reverse) (G reverse) B x := by
  have hplus0 : plus B 0=1-B := by simp only [plus,Real.cos_zero,Real.sin_zero]; ring
  have hexists : ∃y∈Icc 0 x, PlusDomain B y ∧ (y=0 ∨ plus B y=outerDiagonal) := by
    by_cases hz : 1-B≤outerDiagonal
    · refine ⟨0,⟨le_rfl,hd.2.1.1⟩,⟨hd.1,by norm_num,?_⟩,Or.inl rfl⟩
      rw [hplus0]
      exact ⟨by linarith [hd.1.2,outer_endpoint_bounds.2.2.2],hz⟩
    · have hc : Continuous (plus B) :=
        continuous_iff_continuousAt.2 fun y => (plus_hasDerivAt B y).continuousAt
      obtain ⟨y,hy,he⟩ := intermediate_value_Icc hd.2.1.1 hc.neg.continuousOn
        (show -outerDiagonal∈Icc (-plus B 0) (-plus B x) by
          rw [hplus0]; constructor <;> linarith [hd.2.2.2])
      have hcontact : plus B y=outerDiagonal := by rw [Pi.neg_apply] at he; linarith
      have hyd : PlusDomain B y := ⟨hd.1,⟨hy.1,hy.2.trans hd.2.1.2⟩,
        by rw [hcontact]; exact ⟨outer_zero_mem.2,le_rfl⟩⟩
      exact ⟨y,hy,hyd,Or.inr hcontact⟩
  obtain ⟨y,hy,hyd,hexit⟩ := hexists
  have hdom : ∀t∈Icc y x,PlusDomain B t := by
    intro t ht
    have hti : t∈Icc 0 (7/10) := ⟨hyd.2.1.1.trans ht.1,ht.2.trans hd.2.1.2⟩
    exact ⟨hd.1,hti,⟨hd.2.2.1.trans (plus_angle_antitone hd.1 hti hd.2.1 ht.2),
      (plus_angle_antitone hd.1 hyd.2.1 hti ht.1).trans hyd.2.2.2⟩⟩
  have hmono : MonotoneOn (plusCost (F reverse) (G reverse) B) (Icc y x) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (plusCost_hasDerivAt _ _ (hdom t ht)).continuousAt.continuousWithinAt)
      (fun t ht => plusCost_hasDerivAt _ _ (hdom t (Ioo_subset_Icc_self ht)))
      (fun t ht => (positive_derivative reverse (hdom t (Ioo_subset_Icc_self ht))).le)
  have hbetter := hmono ⟨le_rfl,hy.2⟩ ⟨hy.2,le_rfl⟩ hy.2
  have hlower : (44889/50000:ℝ)<plusCost (F reverse) (G reverse) B y := by
    rcases hexit with rfl | he
    · have hsource := hyd.2.2
      rw [hplus0] at hsource
      have h0 : plusCost (F reverse) (G reverse) B 0=(F reverse).outer (1-B)+(G reverse).outer B := by
        simp only [plusCost,hplus0]; ring
      rw [h0]
      cases reverse
      · exact AlignedPJ.original hsource hd.1 (by ring)
      · have hh := AlignedPJ.original hd.1 hsource (by ring)
        simp only [F,G,↓reduceIte]
        linarith
    · obtain ⟨hbranch,hB⟩ := PlusDiagonal.original hyd he
      have hh := PlusDiagonal.lower reverse hbranch
      have he' : plusCost (F reverse) (G reverse) B y=PlusDiagonal.cost
          (if reverse then JLabel else PLabel) (if reverse then PLabel else JLabel) y := by
        simp only [plusCost,PlusDiagonal.cost,he,hB,F,G]
      rw [he']
      exact hh
  exact hlower.trans_le hbetter

theorem minus_lower (reverse : Bool) {B x : ℝ} (hd : MinusDomain B x) :
    (44889/50000:ℝ)< minusCost (F reverse) (G reverse) B x := by
  cases reverse
  · exact NegativePJ.P_lower hd
  · exact NegativePJ.J_lower hd

theorem original_positive (reverse : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (44889/50000:ℝ)<x+(F reverse).eval a b+(G reverse).eval A B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hm' : plus B x≤b := by
    have hw := signed_width (show |x|≤7/10 from abs_le.mpr ⟨by linarith [hx.1],hx.2⟩)
    rw [abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin] at hm
    rw [hw] at hm
    dsimp only [plus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have htargetMono : MonotoneOn (G reverse).outer (Icc 0 outerDiagonal) := by
    cases reverse
    · exact label_monotone true
    · exact label_monotone false
  have hcontact : ∃C, C∈Icc 0 B ∧ PlusDomain C x ∧ plus C x≤b := by
    by_cases hp : 0≤plus B x
    · exact ⟨B,⟨hB.1,le_rfl⟩,⟨hB,hx,⟨hp,hm'.trans hb.2⟩⟩,hm'⟩
    · have hzero : 0<plus 0 x := by
        have hh := SameZero.b_lower outer_zero_mem hx
        have he : plus 0 x=SameZero.b 0 x := by dsimp only [plus,SameZero.b]; ring
        linarith
      have hc : ContinuousOn (fun C => plus C x) (Icc 0 B) := fun C hC =>
        (plus_target_hasDerivAt ⟨hC.1,hC.2.trans hB.2⟩ x).continuousAt.continuousWithinAt
      obtain ⟨C,hC,he⟩ := intermediate_value_Icc hB.1 hc.neg
        (show (0:ℝ)∈Icc (-plus 0 x) (-plus B x) by constructor <;> linarith)
      have hplus : plus C x=0 := by rw [Pi.neg_apply] at he; linarith
      refine ⟨C,hC,⟨⟨hC.1,hC.2.trans hB.2⟩,hx,?_⟩,?_⟩
      · rw [hplus]; exact outer_zero_mem
      · rw [hplus]; exact hb.1
  obtain ⟨C,hC,hd,hbC⟩ := hcontact
  have h1 := label_monotone reverse hd.2.2 hb hbC
  have h2 := htargetMono hd.1 hB hC.2
  have hh := plus_lower reverse hd
  rw [(F reverse).outer_actual hs] at h1
  rw [(G reverse).outer_actual ht] at h2
  dsimp only [plusCost] at hh
  linarith

theorem original_negative (reverse : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) (-x)) :
    (44889/50000:ℝ)< -x+(F reverse).eval a b+(G reverse).eval A B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hm' : minus B x≤b := by
    have hw := signed_width (show |-x|≤7/10 by rw [abs_neg,abs_of_nonneg hx.1]; exact hx.2)
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg (positive_trig hx).2.2.1] at hw
    norm_num [Eight.forwardMargin,Real.sin_neg,Real.cos_neg] at hm
    rw [hw] at hm
    dsimp [minus]
    rw [(ShortOuterOne.SameContact.actual_arc ht).1]
    linarith
  have hd : MinusDomain B x := ⟨hB,hx,⟨by
    linarith [minus_aligned_le hB hx,hB.2,outer_endpoint_bounds.2.2.2],hm'.trans hb.2⟩⟩
  have h1 := label_monotone reverse hd.2.2 hb hm'
  rw [(F reverse).outer_actual hs] at h1
  have hh := minus_lower reverse hd
  dsimp [minusCost] at hh
  rw [(G reverse).outer_actual ht] at hh
  linarith

theorem original (reverse : Bool) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (44889/50000:ℝ)<x+(F reverse).eval a b+(G reverse).eval A B := by
  rcases le_total 0 x with hpos | hneg
  · exact original_positive reverse hs ht ⟨hpos,(abs_le.mp hx).2⟩ hm
  · have hxn : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    simpa only [neg_neg] using original_negative reverse hs ht hxn (by simpa using hm)

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeZero.Asymmetric
