module

public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJZeroCap
public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJDiagonal

/-!
# The complete original P/J same-sign contact

Uncompiled source draft.  Compactness supplies a minimum on the entire
physical contact region.  Its only possible boundary types are the
three now proved boundaries; the explicit inverse curve excludes an
interior minimum.  The original weak separator then lowers to contact.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

lemma target_strict {B x : ℝ} (hd : Domain B x) : B<outerDiagonal := by
  by_contra! hn
  have he : B=outerDiagonal := le_antisymm hd.1.2 hn
  have hh := b_angle_antitone hd.1 hd.2.1 (by norm_num : (7/10:ℝ)∈Icc 0 (7/10)) hd.2.1.2
  have ht := positive_trig (by norm_num : (7/10:ℝ)∈Icc 0 (7/10))
  have h1 := mul_le_mul
    (show (1399/1000:ℝ)≤outerDiagonal+1/2 by linarith [fine_outer_endpoint_bounds.2])
    ht.1.le (by norm_num) (by linarith [fine_outer_endpoint_bounds.2] : 0≤outerDiagonal+1/2)
  have h2 := mul_le_mul
    (show outerDiagonal-1/2≤(2/5:ℝ) by linarith [outer_endpoint_bounds.2.2.2])
    ht.2.2.2.1.le ht.2.2.1 (by norm_num)
  rw [he] at hh
  norm_num [b,ShortOuterOne.SameContact.arc_diagonal] at hh
  linarith [hd.2.2.2,outer_endpoint_bounds.2.2.2]

lemma angle_positive {B x : ℝ} (hd : Domain B x) : 0<x := by
  by_contra! hn
  have he : x=0 := le_antisymm hn hd.2.1.1
  have hh := hd.2.2.2
  rw [he] at hh
  norm_num [b] at hh
  linarith [hd.1.1,outer_endpoint_bounds.2.2.2]

theorem whole_contact_lower {B x : ℝ} (hd : Domain B x) :
    (89777/100000:ℝ)<value PLabel JLabel B x := by
  let guard : ℝ×ℝ→ℝ := fun p => outerDiagonal-b p.1 p.2
  let cost : ℝ×ℝ→ℝ := fun p => value PLabel JLabel p.1 p.2
  have hg : Continuous guard := by dsimp [guard,b,arc]; fun_prop
  have hc : Continuous cost := by dsimp [cost,value,RoleLabel.outer,RoleLabel.eval,b,arc]; fun_prop
  obtain ⟨p,hp,hbetter,hmin⟩ := contact_region_minimum hg hc
    (p₀ := (B,x)) ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2.2⟩
  have hpd : Domain p.1 p.2 := ⟨hp.1,hp.2.1,
    ⟨by linarith [b_lower hp.1 hp.2.1],sub_nonneg.mp hp.2.2⟩⟩
  have hboundary : p.1=0 ∨ b p.1 p.2=outerDiagonal ∨ p.2=7/10 := by
    by_contra hn
    simp only [not_or] at hn
    apply interior_not_minimum
      ⟨lt_of_le_of_ne hpd.1.1 (Ne.symm hn.1),target_strict hpd⟩
      ⟨angle_positive hpd,lt_of_le_of_ne hpd.2.1.2 hn.2.2⟩
      ⟨by linarith [b_lower hp.1 hp.2.1],lt_of_le_of_ne hpd.2.2.2 hn.2.1⟩
    intro C y hCy
    exact hmin (C,y) hCy.1 hCy.2.1 (sub_nonneg.mpr hCy.2.2.2)
  have hlower : (89777/100000:ℝ)<value PLabel JLabel p.1 p.2 := by
    rcases hboundary with hzero | hdiag | hcap
    · simpa [hzero] using zero_boundary_lower (by simpa [hzero] using hpd)
    · exact Diagonal.original_lower hpd hdiag
    · simpa [hcap] using cap_boundary_lower (by simpa [hcap] using hpd)
  exact hlower.trans_le hbetter

theorem original_primary {a b₀ A B x : ℝ} (hs : OuterState a b₀)
    (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b₀ A B 1 1 x) :
    (89777/100000:ℝ)<x+PLabel.eval a b₀-JLabel.eval A B := by
  obtain ⟨hd,hcut⟩ := original_contact hs ht hx hm
  have hmono : MonotoneOn PLabel.outer (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (PLabel.outer_hasDerivAt (outer_domain ht)).continuousAt.continuousWithinAt)
      (fun t ht => PLabel.outer_hasDerivAt (outer_domain (Ioo_subset_Icc_self ht)))
      (fun t ht => by linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1])
  have hsource := hmono hd.2.2 ⟨hs.1,(outer_bounds hs).2.2.2.1⟩ hcut
  rw [PLabel.outer_actual hs] at hsource
  have hh := whole_contact_lower hd
  dsimp [value] at hh
  rw [JLabel.outer_actual ht] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.SameZero.PJ
