module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveLowerPrimaryReference

/-!
# Both original lower-primary opposite edge-five tuples

Uncompiled completion of Section 3. The original source coordinate
decreases to its actual contact; the whole physical target segment is
bounded by its axial tangent parabola. The final completed square uses
the same 1.14 curvature and -.024 slope as the hand proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerPrimary
open CommonQuarter CorePairGeometry Arithmetic

def source (r : Bool) (a : ℝ) : ℝ := p r*a-q r*SameContact.arc a
def sourceD (r : Bool) (a : ℝ) : ℝ := p r+q r*SameContact.ratio a
theorem source_hasDerivAt (r : Bool) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (source r) (sourceD r a) a := by
  convert ((hasDerivAt_id a).const_mul (p r)).sub
    ((SameContact.arc_hasDerivAt (Same.primary_domain ha)).const_mul (q r)) using 1 <;>
    dsimp [source,sourceD] <;> ring
theorem source_monotone (r : Bool) : MonotoneOn (source r) (Icc outerDiagonal outerAxial) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun a ha => (source_hasDerivAt r ha).continuousAt.continuousWithinAt)
    (fun a ha => source_hasDerivAt r (Ioo_subset_Icc_self ha))
  intro a ha
  have hc := coefficient_bounds r
  have hh := mul_le_mul_of_nonneg_left (Same.primary_ratio_lower (Ioo_subset_Icc_self ha))
    (show 0≤q r by linarith [hc.2.2.1])
  dsimp [sourceD]
  linarith [hc.1,hc.2.2.1]

theorem contact_lower (r : Bool) {y u : ℝ} (hd : Domain y u) : threshold<value r y u := by
  have hbase := reference_domain hd
  have ht := curvature_tangent (l:=(1/2:ℝ)) (u:=y) (x:=y) (t:=(1/2:ℝ)) (κ:=(57/50:ℝ))
    (f:=fun Y => value r Y u) (d:=fun Y => targetFirst r Y u) (dd:=fun Y => targetSecond r Y u)
    ⟨hd.2.1.1,le_rfl⟩ ⟨le_rfl,hd.2.1.1⟩
    (fun Y hY => value_target_hasDerivAt r (target_interval hd hY))
    (fun Y hY => targetFirst_hasDerivAt r (target_interval hd hY))
    (fun Y hY => by linarith [targetSecond_lower r (target_interval hd hY)])
  have hv := reference_value r hbase
  have hs := reference_slope_lower r hbase
  have hm := mul_le_mul_of_nonneg_right hs.le (show 0≤y-1/2 by linarith [hd.2.1.1])
  have hsq := sq_nonneg ((57/50)*(y-1/2)-(3/125:ℝ))
  dsimp [threshold]
  nlinarith only [ht,hv,hm,hsq]

theorem original_contact_lower (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : width u≤a-A*Real.sin u-B*Real.cos u) :
    value r (B+1/2) u≤Real.pi/2-u+c+p r*a-q r*b-P r*A-t r*B := by
  have hd := actual_domain hs ht hu hm
  have ha : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hcontact : K (B+1/2) u-1/2∈Icc outerDiagonal outerAxial := by
    constructor
    · dsimp [K]
      linarith [(contact_bounds hd).1,outer_endpoint_bounds.2.2.2]
    · have hh := hd.2.2
      rw [X0_eq] at hh
      linarith
  have hle : K (B+1/2) u-1/2≤a := by
    rw [K,z,actual_X ht]
    dsimp [width] at hm
    nlinarith
  have hsource := source_monotone r hcontact ha hle
  rw [source,(SameContact.actual_arc hs).2] at hsource
  have he : value r (B+1/2) u=
      Real.pi/2-u+c+source r (K (B+1/2) u-1/2)-P r*A-t r*B := by
    dsimp [value,cShift,V,source]
    rw [root_eq_arc,actual_X ht]
    ring
  rw [he]
  linarith

theorem original (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : width u≤a-A*Real.sin u-B*Real.cos u) :
    threshold<Real.pi/2-u+c+p r*a-q r*b-P r*A-t r*B :=
  (contact_lower r (actual_domain hs ht hu hm)).trans_le (original_contact_lower r hs ht hu hm)

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerPrimary
