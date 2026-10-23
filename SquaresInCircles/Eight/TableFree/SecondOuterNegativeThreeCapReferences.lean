module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeCapCalculus

/-!
# The two named references and the true endpoint of the angle-cap arc

All cages are obtained from the original circle and the already proved
Taylor bounds at `.7`.  The two interior references are `.4` and
`.275034`; the final rational point lies strictly beyond the actual
diagonal-target endpoint.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Cap

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo.CapCurve (height k k1 Domain target_mem)

def reference : ℝ := 137517/500000
def endpointUpper : ℝ := 375927951/500000000

lemma four_mem : (2/5:ℝ)∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num)
lemma reference_mem : reference∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [reference])
lemma endpointUpper_mem : endpointUpper∈Icc 0 outerDiagonal :=
  Asymmetric.rational_outer_mem (by norm_num [endpointUpper])

lemma four_radical :
    U (2/5)∈Icc (35245425235057/20000000000000) (88113563087643/50000000000000) := by
  have hh := shifted_chart_reference (outer_domain four_mem)
    (l := (35245425235057/20000000000000:ℝ))
    (u := (88113563087643/50000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma reference_radical :
    U reference∈Icc (36413856147593/20000000000000) (91034640368983/50000000000000) := by
  have hh := shifted_chart_reference (outer_domain reference_mem)
    (l := (36413856147593/20000000000000:ℝ))
    (u := (91034640368983/50000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [reference,W,Q0]) (by norm_num [reference,W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma endpointUpper_radical :
    U endpointUpper∈Icc (76623377643963/50000000000000) (153246755287927/100000000000000) := by
  have hh := shifted_chart_reference (outer_domain endpointUpper_mem)
    (l := (76623377643963/50000000000000:ℝ))
    (u := (153246755287927/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [endpointUpper,W,Q0])
    (by norm_num [endpointUpper,W,Q0])
  exact ⟨hh.1.le,hh.2.le⟩

lemma four_cage :
    height (2/5)∈Icc (4967786993/10000000000) (4967786999/10000000000) ∧
      (2587/2500:ℝ)<k (2/5) ∧ k (2/5)<207/200 ∧ (342/625:ℝ)<k1 (2/5) := by
  have hh := NegativeTwo.CapCurve.reference_cage four_mem four_radical (by norm_num)
  norm_num [NegativeTwo.CapCurve.sLo,NegativeTwo.CapCurve.sHi,
    NegativeTwo.CapCurve.cLo,NegativeTwo.CapCurve.cHi,Q0] at hh
  exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith,by linarith⟩

lemma reference_cage :
    height reference∈Icc (3715901291/10000000000) (3715901296/10000000000) ∧
      k reference∈Icc (1212245417/1250000000) (4848981671/5000000000) := by
  have hh := NegativeTwo.CapCurve.reference_cage reference_mem reference_radical (by norm_num)
  norm_num [reference,NegativeTwo.CapCurve.sLo,NegativeTwo.CapCurve.sHi,
    NegativeTwo.CapCurve.cLo,NegativeTwo.CapCurve.cHi,Q0] at hh
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma four_domain : Domain (2/5) :=
  ⟨four_mem,by linarith [four_cage.1.2,fine_outer_endpoint_bounds.2]⟩

lemma reference_domain : Domain reference :=
  ⟨reference_mem,by linarith [reference_cage.1.2,fine_outer_endpoint_bounds.2]⟩

lemma four_target_radical :
    U (height (2/5))∈Icc (42734882/25000000) (4273488201/2500000000) := by
  have hc := UW_circle (outer_domain (target_mem four_domain))
  have hp := U_positive (outer_domain (target_mem four_domain))
  norm_num [W,Q0] at hc
  constructor <;> nlinarith [four_cage.1.1,four_cage.1.2]

lemma reference_target_radical :
    U (height reference)∈Icc (3552987839/2000000000) (8882469599/5000000000) := by
  have hc := UW_circle (outer_domain (target_mem reference_domain))
  have hp := U_positive (outer_domain (target_mem reference_domain))
  norm_num [W,Q0] at hc
  constructor <;> nlinarith [reference_cage.1.1,reference_cage.1.2]

lemma endpointUpper_outside : outerDiagonal<height endpointUpper := by
  have hh := NegativeTwo.CapCurve.reference_cage endpointUpper_mem endpointUpper_radical (by norm_num)
  norm_num [endpointUpper,NegativeTwo.CapCurve.sLo,NegativeTwo.CapCurve.sHi,
    NegativeTwo.CapCurve.cLo,NegativeTwo.CapCurve.cHi,Q0] at hh
  linarith [diagonal_fine.2]

lemma true_endpoint : ∃ e : ℝ, e∈Icc (2/5) endpointUpper ∧ height e=outerDiagonal := by
  have hcont : Continuous height := by
    dsimp [height,NegativeTwo.TargetContact.B,ShortOuterOne.SameContact.arc]
    fun_prop
  obtain ⟨e,he,hc⟩ := intermediate_value_Icc
    (show (2/5:ℝ)≤endpointUpper by norm_num [endpointUpper]) hcont.continuousOn
    (show outerDiagonal∈Icc (height (2/5)) (height endpointUpper) from
      ⟨four_domain.2,endpointUpper_outside.le⟩)
  exact ⟨e,he,hc⟩

lemma endpoint_domain {e : ℝ} (he : e∈Icc (2/5) endpointUpper)
    (hc : height e=outerDiagonal) : Domain e :=
  ⟨⟨by linarith [he.1],he.2.trans endpointUpper_mem.2⟩,by rw [hc]⟩

lemma source_bounded_by_end {b e : ℝ} (hb : Domain b)
    (he : e∈Icc (2/5) endpointUpper) (hc : height e=outerDiagonal) : b≤e := by
  have hed := endpoint_domain he hc
  have hmono : MonotoneOn (fun t => height t-(4/5)*t) (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => ((NegativeTwo.CapCurve.height_hasDerivAt ht).sub
        ((hasDerivAt_id t).const_mul (4/5))).continuousAt.continuousWithinAt)
      (fun t ht => (NegativeTwo.CapCurve.height_hasDerivAt (Ioo_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).const_mul (4/5)))
      (fun t ht => by linarith [(NegativeTwo.CapCurve.k_bounds (Ioo_subset_Icc_self ht)).1])
  rcases le_total b e with h | h
  · exact h
  · have hh := hmono hed.1 hb.1 h
    rw [hc] at hh
    linarith [hb.2]

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Cap
