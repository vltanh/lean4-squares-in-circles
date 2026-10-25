module

public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeTwoLowerPrimaryGeometry

/-!
# The original weak lower source-primary owner

The original separator bounds the increasing physical contact by the
original source primary coordinate.  The entire backward path remains
on the same circle; its cost increases from the already proved aligned
point.  Both equality endpoints and weak owners are retained.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo

open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_source_primary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤forwardMargin 3 a b A B (-1) 1 (Real.pi/2-x)) :
    (44889/50000:ℝ)<value b B (Real.pi/2-x) := by
  have hcut : lowerPrimary A B x≤a := by
    have hw := lower_width hx
    norm_num [forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
    dsimp [lowerPrimary]
    linarith
  have hdom {t : ℝ} (htx : t∈Icc 0 x) :
      lowerPrimary A B t∈Icc 1 outerAxial :=
    lower_contact_domain ht hx (outer_bounds hs).2.1 hcut htx
  let f : ℝ→ℝ := fun t => Real.pi/2-t+
    PPrimaryLabel.outer (lowerPrimary A B t)-V B
  have hd {t : ℝ} (htx : t∈Icc 0 x) :
      HasDerivAt f (-1+PPrimaryLabel.d1 (lowerPrimary A B t)*lowerSpeed A B t) t := by
    have hh := (PPrimaryLabel.outer_hasDerivAt (primary_domain
      (target_primary_domain (hdom htx)))).comp t (lowerPrimary_hasDerivAt A B t)
    exact (((hasDerivAt_id' t).const_sub (Real.pi/2)).fun_add hh).sub_const (V B)
  have hmono : MonotoneOn f (Icc 0 x) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t htx => (hd htx).continuousAt.continuousWithinAt
    · exact fun t htx => hd (Ioo_subset_Icc_self htx)
    · intro t htx
      have hI := Ioo_subset_Icc_self htx
      have ht' : t∈Icc 0 (7/10) := ⟨hI.1,hI.2.trans hx.2⟩
      have hs' := lowerSpeed_eq_primarySpeed ht ht' (hdom hI)
      have hM := M_first_lower (target_primary_domain (hdom hI))
      have hv := (primarySpeed_data (hdom hI)).1
      rw [←hs'] at hv
      have hp := mul_lt_mul hM hv.le (by norm_num)
        (by linarith : 0≤PPrimaryLabel.d1 (lowerPrimary A B t))
      linarith
  have hstep := hmono ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1
  have hsource := M_monotone (target_primary_domain (hdom ⟨hx.1,le_rfl⟩))
    (primary_mem hs) hcut
  have he : PPrimaryLabel.outer a= -P b := PLabel.primary_actual hs
  rw [he] at hsource
  have hB : B∈Icc 0 (outerAxial-1) := by
    have hz := hdom ⟨le_rfl,hx.1⟩
    rw [lowerPrimary_zero] at hz
    exact ⟨ht.1,by linarith [hz.2]⟩
  have hbase := aligned_right hB
  dsimp [f] at hstep
  rw [lowerPrimary_zero] at hstep
  norm_num only [sub_zero] at hstep
  dsimp [value]
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.OppositeTwo
