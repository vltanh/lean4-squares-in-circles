module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryNegativeScalars

/-!
# Every original lower-half opposite primary contact

Uncompiled source assembly of the negative-primary hand note. Five
intrinsic rows use the two concave target endpoints. The sixth retains
its negative primary coefficient and proves the original axial support
criterion on the whole separator-forced angle interval. The result
keeps the actual original source and target states and weak owner.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Negative
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport

theorem original_circle_support (r : Row) {a b : ℝ} (hs : OuterState a b) :
    S r≤(p r-weight r)*a-q r*b := by
  have hh := outer_circle_lower (X:=p r-weight r) (Y:=-(q r)) hs
  rw [show (-(q r))^2=(q r)^2 by ring] at hh
  dsimp [S]
  linarith

theorem positive_primary_axial {x : ℝ} (hx : x∈Icc 0 cap) :
    X 1 x<0 ∧ 0<(outerAxial+1/2)*Y 1 x-X 1 x/2 := by
  have tr := small_trig hx
  have hX : X 1 x<0 := by norm_num [X,P,weight]; linarith [tr.2.2]
  have hpos : 0<P 1-weight 1*Real.sin x := by dsimp [X] at hX; linarith
  have hr := mul_lt_mul_of_pos_right rho_bounds.1 hpos
  have hpositive : 0<Y 1 x-rho*X 1 x := by
    norm_num [X,Y,P,t,weight] at hr ⊢
    nlinarith [tr.1,tr.2.2]
  have hh := mul_pos
    (show 0<outerAxial+1/2 by linarith [outer_endpoint_bounds.1]) hpositive
  have hid : (outerAxial+1/2)*(Y 1 x-rho*X 1 x)=
      (outerAxial+1/2)*Y 1 x-X 1 x/2 := by
    calc
      (outerAxial+1/2)*(Y 1 x-rho*X 1 x)=
        (outerAxial+1/2)*Y 1 x-((outerAxial+1/2)*rho)*X 1 x := by ring
      _=(outerAxial+1/2)*Y 1 x-X 1 x/2 := by rw [rho_identity]; ring
  exact ⟨hX,hid ▸ hh⟩

theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10)) (hm : width x≤a-A*Real.sin x-B*Real.cos x) :
    threshold r<cost r false a b A B x := by
  have hx' : x∈Icc 0 cap := ⟨hx.1,(forced_cap hs ht hx hm).le⟩
  have hsource := original_circle_support r hs
  have hp := mul_le_mul_of_nonneg_left hm (weight_positive r).le
  by_cases hr : r=1
  · subst r
    have ha := positive_primary_axial hx'
    have htarget := outer_axial_lower ht ha.1.le ha.2.le
    have hv := axial_lower 1 hx'
    dsimp [X,Y,axialValue,width,cost,Unit.angle,Unit.direction] at htarget hp hv ⊢
    nlinarith only [hsource,hp,htarget,hv]
  have hX : 0≤X r x := by
    have hh := mul_nonneg (weight_positive r).le (small_trig hx').2.1
    dsimp [X]
    linarith [P_nonpositive r hr]
  by_cases hmin : X r x*outerAxial≤(X r x+Y r x)*outerDiagonal
  · have htarget := outer_concave_lower ht hX le_rfl hmin
    have hv := axial_lower r hx'
    dsimp [X,Y,axialValue,width,cost,Unit.angle,Unit.direction] at htarget hp hv ⊢
    nlinarith only [hsource,hp,htarget,hv]
  · have htarget := outer_concave_lower ht hX (lt_of_not_ge hmin).le le_rfl
    have hv := diagonal_lower r hr hx'
    dsimp [X,Y,diagonalValue,width,cost,Unit.angle,Unit.direction] at htarget hp hv ⊢
    nlinarith only [hsource,hp,htarget,hv]

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Negative
