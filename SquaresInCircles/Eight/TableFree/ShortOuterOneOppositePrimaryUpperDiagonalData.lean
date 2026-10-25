module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperDiagonalGeometry
public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryUpperAxial

/-!
# The diagonal reference cost and its exact state and angle derivatives

Uncompiled transcription of the common diagonal formulas in the two
upper-primary notes. The reference agrees with the actual contact value
and with the axial curve at the unique event.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)

def G (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2+x+c r+(p r-q r)*outerDiagonal-P r*(U x-1/2)-t r*(V x-1/2)
def G1 (r : Row) (x : ℝ) : ℝ := 1-(t r*U x-P r*V x)*omega x
def G2 (r : Row) (x : ℝ) : ℝ :=
  (omega x)^2*(P r*U x+t r*V x)-omegaD x*(t r*U x-P r*V x)
def J (r : Row) (x : ℝ) : ℝ :=
  (p r+q r)*Real.cos x-t r+((p r+q r)*Real.sin x+P r)*(V x/U x)
def J1 (r : Row) (x : ℝ) : ℝ :=
  (p r+q r)*z x/U x+((p r+q r)*Real.sin x+P r)*Q0*omega x/(U x)^2

theorem V_hasDerivAt {x : ℝ} (hx : DiagonalDomain x) :
    HasDerivAt V (diagonalSpeed x) x := by
  have h := (SecondWord.SameZero.PJ.Diagonal.height_hasDerivAt hx.1).add_const (1/2)
  convert h using 1
  funext y
  simp only [V,SecondWord.SameZero.PJ.Diagonal.height,sub_add_cancel]

theorem G_hasDerivAt (r : Row) {x : ℝ} (hx : DiagonalDomain x) :
    HasDerivAt (G r) (G1 r x) x := by
  have h := ((((hasDerivAt_id' x).const_add (Real.pi/2+c r)).add_const
    ((p r-q r)*outerDiagonal)).fun_sub
      (((SecondWord.SameZero.PJ.Diagonal.horizontal_hasDerivAt hx.1).sub_const (1/2)).const_mul
        (P r))).fun_sub (((V_hasDerivAt hx).sub_const (1/2)).const_mul (t r))
  convert h using 1
  · funext y
    simp only [G]
    ring
  · simp only [G1,diagonalSpeed,SecondWord.SameZero.PJ.Diagonal.speed]
    ring

theorem G1_hasDerivAt (r : Row) {x : ℝ} (hx : DiagonalDomain x) :
    HasDerivAt (G1 r) (G2 r x) x := by
  have h := ((((SecondWord.SameZero.PJ.Diagonal.horizontal_hasDerivAt hx.1).const_mul (t r)).fun_sub
    ((V_hasDerivAt hx).const_mul (P r))).fun_mul
      (SecondWord.SameZero.PJ.Diagonal.factor_hasDerivAt hx.1)).const_sub 1
  convert h using 1
  · funext y
    rfl
  · simp only [G2,diagonalSpeed,SecondWord.SameZero.PJ.Diagonal.speed]
    ring

theorem diagonal_ratio_hasDerivAt {x : ℝ} (hx : DiagonalDomain x) :
    HasDerivAt (fun y => V y/U y) (Q0*omega x/(U x)^2) x := by
  have hU : U x≠0 := ne_of_gt (by linarith [(diagonal_coordinate_bounds hx).1])
  have hc := diagonal_circle hx
  have h := (V_hasDerivAt hx).div (SecondWord.SameZero.PJ.Diagonal.horizontal_hasDerivAt hx.1) hU
  refine h.congr_deriv ?_
  rw [← hc]
  simp only [diagonalSpeed,SecondWord.SameZero.PJ.Diagonal.speed]
  ring

theorem J_hasDerivAt (r : Row) {x : ℝ} (hx : DiagonalDomain x) :
    HasDerivAt (J r) (J1 r x) x := by
  have hU : U x≠0 := ne_of_gt (by linarith [(diagonal_coordinate_bounds hx).1])
  have hz := (diagonal_projection hx).2
  have hh := (((Real.hasDerivAt_cos x).const_mul (p r+q r)).sub_const (t r)).fun_add
    ((((Real.hasDerivAt_sin x).const_mul (p r+q r)).add_const (P r)).fun_mul
      (diagonal_ratio_hasDerivAt hx))
  refine hh.congr_deriv ?_
  simp only [J1]
  rw [← hz]
  field_simp
  ring

theorem G_value (r : Row) {x : ℝ} (hx : DiagonalDomain x) :
    G r x=value r (diagonalB x) x := by
  have hc : contact (diagonalB x) x=outerDiagonal := SecondWord.SameZero.PJ.Diagonal.contact hx
  rw [value,hc,source,target,SameContact.arc_diagonal,diagonal_target_arc hx]
  dsimp [G,diagonalB,SecondWord.SameZero.PJ.Diagonal.height]
  ring

theorem J_first (r : Row) {x : ℝ} (hx : DiagonalDomain x) :
    J r x=first r (diagonalB x) x := by
  have hc : contact (diagonalB x) x=outerDiagonal := SecondWord.SameZero.PJ.Diagonal.contact hx
  rw [first,hc,sourceD,ratio_diagonal]
  dsimp [stateSpeed,SecondWord.SameZero.k]
  rw [(diagonal_ratio hx).1]
  dsimp [J]
  ring

theorem G1_speed (r : Row) {x : ℝ} (hx : DiagonalDomain x) :
    G1 r x=1-(t r-P r*(V x/U x))*diagonalSpeed x := by
  have hU : U x≠0 := ne_of_gt (by linarith [(diagonal_coordinate_bounds hx).1])
  dsimp [G1,diagonalSpeed,SecondWord.SameZero.PJ.Diagonal.speed]
  field_simp [hU]

theorem diagonal_at_event_coordinates {e : ℝ} (he : IsEvent e) :
    U e=outerAxial+1/2 ∧ V e=1/2 := by
  have hx := (diagonal_at_event he).1
  have hB := (diagonal_at_event he).2
  have hu := diagonal_target_arc hx
  rw [hB,SameContact.arc_zero] at hu
  have hv : V e=1/2 := by
    dsimp [diagonalB,SecondWord.SameZero.PJ.Diagonal.height] at hB
    linarith
  exact ⟨by linarith,hv⟩

theorem G_at_event (r : Row) {e : ℝ} (he : IsEvent e) : G r e=F r e := by
  rw [G_value r (diagonal_at_event he).1,(diagonal_at_event he).2]
  rfl
theorem J_at_event (r : Row) {e : ℝ} (he : IsEvent e) : J r e=H r e := by
  rw [J_first r (diagonal_at_event he).1,(diagonal_at_event he).2]
  rfl

theorem diagonal_simple_slope (r : Row) (hr : r=0∨r=2∨r=3∨r=4∨r=5)
    {x : ℝ} (hx : DiagonalDomain x) : 0<G1 r x := by
  have hs := diagonal_speed_bounds hx
  have hc := diagonal_coordinate_bounds hx
  have hw := diagonal_omega_bounds hx
  by_cases hthree : r=3
  · subst r
    rw [G1_speed 3 hx]
    norm_num [P,t]
    nlinarith [hs.2]
  by_cases hfour : r=4
  · subst r
    have hspeed : diagonalSpeed x<(1077/1000:ℝ) := by linarith [hs.2]
    have hV : V x<(109/100:ℝ) := by linarith [hc.2.2.2.1]
    have hprod := mul_le_mul hV.le hw.2.le
      (by linarith [hw.1] : 0≤omega x) (by norm_num)
    have hid : G1 4 x=1-t 4*diagonalSpeed x+P 4*V x*omega x := by
      dsimp [G1,diagonalSpeed,SecondWord.SameZero.PJ.Diagonal.speed]
      ring
    rw [hid]
    norm_num [P,t]
    nlinarith
  have hr' : r=0∨r=2∨r=5 := by
    rcases hr with h | h | h | h | h <;> tauto
  have hP : P r≤0 := by rcases hr' with rfl | rfl | rfl <;> norm_num [P]
  have hfactor : t r-P r*(V x/U x)≤t r+(33/50)*(-P r) := by
    have hh := mul_le_mul_of_nonneg_left hc.2.2.2.2.2.le (neg_nonneg.mpr hP)
    linarith
  have hfactor0 : 0≤t r-P r*(V x/U x) := by
    have hh := mul_nonpos_of_nonpos_of_nonneg hP hc.2.2.2.2.1.le
    linarith [(coefficients r).2.2.2.2.2.1]
  have hp := mul_le_mul hfactor hs.2.le hs.1.le (by linarith)
  rw [G1_speed r hx]
  rcases hr' with rfl | rfl | rfl <;> norm_num [P,t] at hp ⊢ <;> linarith

theorem G_simple_increasing (r : Row) (hr : r=0∨r=2∨r=3∨r=4∨r=5)
    {e : ℝ} (he : IsEvent e) : MonotoneOn (G r) (Icc e (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x hx => (G_hasDerivAt r (after_diagonal_domain he hx)).continuousAt.continuousWithinAt)
    (fun x hx => G_hasDerivAt r (after_diagonal_domain he (Ioo_subset_Icc_self hx)))
    (fun x hx => (diagonal_simple_slope r hr (after_diagonal_domain he (Ioo_subset_Icc_self hx))).le)

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
