module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreePrimary

/-!
# The aligned negative edge-three minimum

The transformed source slope is below `.9` up to primary coordinate
one, while the necessary small target slope is above `.901`.  Beyond
one the source label increases.  Thus the actual aligned constraint
reduces to one physical circle point.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def aligned (a : ℝ) : ℝ := Real.pi/2+TPrimaryLabel.outer a+K (1-a)

lemma aligned_reference : (93/100:ℝ)<Real.pi/2+TPrimaryLabel.outer 1+K 0 := by
  have hs := ShortOuterOne.SameContact.primary_state primary_one_mem
  have hb := NegativeTwo.source_mem hs
  have hc := hs.2.2
  have hbox : arc 1∈Icc (1581/2000) (791/1000) := by
    norm_num [Q0] at hc
    constructor <;> nlinarith [hb.1]
  have hU : U (arc 1)∈Icc (3/2) (3/2) := by
    have he := (ShortOuterOne.SameContact.actual_arc hs).1
    dsimp [U]
    rw [he]
    norm_num
  have ht := FixedReference.target hb hbox hU (by norm_num) (by norm_num)
  have hT : T (arc 1)<(61/100:ℝ) := by
    norm_num [FixedReference.valueLo,FixedReference.valueHi,FixedReference.firstLo,
      FixedReference.firstHi,FixedReference.secondLo,FixedReference.secondHi,Q0] at ht
    linarith
  have he := primary_actual hs
  rw [he]
  linarith [pi_hand_enclosure.1,K_zero_bounds.1]

lemma aligned_hasDerivAt {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    HasDerivAt aligned (TPrimaryLabel.d1 a-KLabel.d1 (1-a)) a := by
  have hh := NegativeTwo.aligned_domain ha
  have ht := (KLabel.outer_hasDerivAt (outer_domain hh.2.1)).comp a
    ((hasDerivAt_id' a).const_sub 1)
  have hd := ((TPrimaryLabel.outer_hasDerivAt (primary_domain hh.1)).const_add
    (Real.pi/2)).add ht
  exact hd.congr_deriv (by ring)

lemma aligned_antitone : AntitoneOn aligned (Icc outerDiagonal 1) :=
  antiOn_of_hasDeriv_nonpos
    (fun a ha => (aligned_hasDerivAt ha).continuousAt.continuousWithinAt)
    (fun a ha => aligned_hasDerivAt (Ioo_subset_Icc_self ha))
    (fun a ha => by
      have h := Ioo_subset_Icc_self ha
      linarith [primary_first_small h,K_first_small (NegativeTwo.aligned_domain h).2.2])

lemma aligned_lower {a : ℝ} (ha : a∈Icc outerDiagonal 1) :
    (93/100:ℝ)<aligned a := by
  have hmono := aligned_antitone ha (show (1:ℝ)∈Icc outerDiagonal 1 from
    ⟨primary_one_mem.1,le_rfl⟩) ha.2
  have hbase := aligned_reference
  unfold aligned at hmono ⊢
  rw [sub_self] at hmono
  linarith

theorem original_aligned {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (halign : 1≤a+B) :
    (93/100:ℝ)<value b B (Real.pi/2) := by
  have ha := NegativeTwo.primary_mem hs
  have hB := NegativeTwo.source_mem ht
  have hactual := primary_actual hs
  rcases le_total 1 a with h | h
  · have hM := primary_monotone primary_one_mem ha h
    have hK := K_lower hB
    rw [hactual] at hM
    dsimp [value]
    linarith [aligned_reference]
  · have hdom := NegativeTwo.aligned_domain (show a∈Icc outerDiagonal 1 from ⟨ha.1,h⟩)
    have hK := K_monotone hdom.2.1 hB (by linarith)
    have hbase := aligned_lower (show a∈Icc outerDiagonal 1 from ⟨ha.1,h⟩)
    dsimp [aligned] at hbase
    rw [hactual] at hbase
    dsimp [value]
    linarith

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree
