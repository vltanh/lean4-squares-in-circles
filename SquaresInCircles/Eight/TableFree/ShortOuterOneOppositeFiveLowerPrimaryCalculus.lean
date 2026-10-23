module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveLowerPrimaryGeometry

/-!
# Exact lower-primary contact derivatives

Uncompiled transcription of Section 3, equations (20)--(24).
The second target derivative is first obtained directly from the two
circle coordinates, then rewritten into the hand proof's numerator.
The axial angular derivative keeps its original signed coefficient.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerPrimary
open CommonQuarter CorePairGeometry Arithmetic

def value (r : Bool) (y u : ℝ) : ℝ :=
  Real.pi/2-u+cShift r+p r*K y u-q r*V y u-P r*X y-t r*y
def coefficient (r : Bool) (y u : ℝ) : ℝ := p r+q r*K y u/V y u
def targetFirst (r : Bool) (y u : ℝ) : ℝ :=
  coefficient r y u*T y u/X y+P r*y/X y-t r
def targetSecond (r : Bool) (y u : ℝ) : ℝ :=
  Q0/(X y)^3*(P r-p r*Real.sin u+
    q r*((T y u)^2*X y-Real.sin u*K y u*(V y u)^2)/(V y u)^3)
def J (r : Bool) (u : ℝ) : ℝ := coefficient r (1/2) u*T (1/2) u
def JD (r : Bool) (u : ℝ) : ℝ := q r/(V (1/2) u)^3*
  (Q0*(T (1/2) u)^2-K (1/2) u*(K (1/2) u-1)*(V (1/2) u)^2)-p r*(K (1/2) u-1)

theorem ratio_hasDerivAt {v : ℝ} (hv : RootDomain v) :
    HasDerivAt (fun w => w/root w) (Q0/(root v)^3) v := by
  convert (rootD_hasDerivAt hv).neg using 1 <;> dsimp [rootD,rootDD] <;> ring
theorem V_target_hasDerivAt {y u : ℝ} (hd : Domain y u) :
    HasDerivAt (fun Y => V Y u) (-K y u/V y u*(T y u/X y)) y := by
  exact (root_hasDerivAt (contact_root hd)).comp y (K_target_hasDerivAt hd.2.1)
theorem V_angle_hasDerivAt {y u : ℝ} (hd : Domain y u) :
    HasDerivAt (V y) (-K y u/V y u*T y u) u :=
  (root_hasDerivAt (contact_root hd)).comp u (K_angle_hasDerivAt y u)
theorem coefficient_target_hasDerivAt (r : Bool) {y u : ℝ} (hd : Domain y u) :
    HasDerivAt (fun Y => coefficient r Y u) (q r*Q0/(V y u)^3*(T y u/X y)) y := by
  convert (((ratio_hasDerivAt (contact_root hd)).comp y
    (K_target_hasDerivAt hd.2.1)).const_mul (q r)).const_add (p r) using 1 <;>
    dsimp [coefficient,V] <;> ring
theorem coefficient_angle_hasDerivAt (r : Bool) {y u : ℝ} (hd : Domain y u) :
    HasDerivAt (coefficient r y) (q r*Q0/(V y u)^3*T y u) u := by
  convert (((ratio_hasDerivAt (contact_root hd)).comp u
    (K_angle_hasDerivAt y u)).const_mul (q r)).const_add (p r) using 1 <;>
    dsimp [coefficient,V] <;> ring
theorem target_speed_hasDerivAt {y u : ℝ} (hy : Target y) :
    HasDerivAt (fun Y => T Y u/X Y) (-Q0*Real.sin u/(X y)^3) y := by
  have hh := (T_target_hasDerivAt (u:=u) hy).div (X_hasDerivAt hy) (X_positive hy).ne'
  convert hh using 1
  · rfl
  · field_simp [(X_positive hy).ne']
    dsimp [T,z]
    linear_combination -(Real.sin u)*(X_sq hy)
theorem target_ratio_hasDerivAt {y : ℝ} (hy : Target y) :
    HasDerivAt (fun Y => Y/X Y) (Q0/(X y)^3) y := ratio_hasDerivAt (target_root hy)
theorem value_target_hasDerivAt (r : Bool) {y u : ℝ} (hd : Domain y u) :
    HasDerivAt (fun Y => value r Y u) (targetFirst r y u) y := by
  convert (((((K_target_hasDerivAt hd.2.1).const_mul (p r)).const_add
    (Real.pi/2-u+cShift r)).sub ((V_target_hasDerivAt hd).const_mul (q r))).sub
      ((X_hasDerivAt hd.2.1).const_mul (P r))).sub ((hasDerivAt_id y).const_mul (t r)) using 1
  · rfl
  · dsimp [targetFirst,coefficient]
    ring
theorem targetFirst_hasDerivAt (r : Bool) {y u : ℝ} (hd : Domain y u) :
    HasDerivAt (fun Y => targetFirst r Y u) (targetSecond r y u) y := by
  have hh := (((coefficient_target_hasDerivAt r hd).mul
    (target_speed_hasDerivAt hd.2.1)).add
      ((target_ratio_hasDerivAt hd.2.1).const_mul (P r))).sub_const (t r)
  convert hh using 1
  · ext Y
    dsimp [targetFirst]
    ring
  · dsimp [targetSecond,coefficient]
    field_simp [(X_positive hd.2.1).ne',(V_positive hd).ne']
    ring

theorem numerator_identity {y u : ℝ} (hd : Domain y u) :
    (T y u)^2*X y-Real.sin u*K y u*(V y u)^2=
      Real.cos u*(T y u)^3+Real.sin u*(3*(z y u)^2+3*z y u+1-Q0) := by
  calc
    _=Real.cos u*(T y u)^3+Real.sin u*
        (z y u*(T y u)^2-K y u*(V y u)^2) := by rw [X_inverse y u]; ring
    _=_ := by
      rw [show (T y u)^2=Q0-(z y u)^2 by linarith [circle (u:=u) hd.2.1],V_sq hd]
      dsimp [K]
      ring
theorem targetSecond_identity (r : Bool) {y u : ℝ} (hd : Domain y u) :
    targetSecond r y u=Q0/(X y)^3*(P r-p r*Real.sin u+
      q r*(Real.cos u*(T y u)^3+Real.sin u*(3*(z y u)^2+3*z y u+1-Q0))/(V y u)^3) := by
  rw [targetSecond,numerator_identity hd]

theorem value_angle_hasDerivAt (r : Bool) {y u : ℝ} (hd : Domain y u) :
    HasDerivAt (value r y) (-1+coefficient r y u*T y u) u := by
  convert (((((hasDerivAt_id u).neg).const_add
    (Real.pi/2+cShift r-P r*X y-t r*y)).add
      ((K_angle_hasDerivAt y u).const_mul (p r))).sub
        ((V_angle_hasDerivAt hd).const_mul (q r))) using 1 <;> dsimp [value,coefficient] <;> ring
theorem J_hasDerivAt (r : Bool) {u : ℝ} (hd : Domain (1/2) u) : HasDerivAt (J r) (JD r u) u := by
  have hh := (coefficient_angle_hasDerivAt r hd).mul (T_angle_hasDerivAt (1/2) u)
  convert hh using 1
  · rfl
  · dsimp [JD,coefficient,K]
    field_simp [(V_positive hd).ne']
    ring
theorem reference_slope (r : Bool) (u : ℝ) :
    targetFirst r (1/2) u=J r u/X0+P r/(2*X0)-t r := by
  dsimp [targetFirst,J,X]
  rw [root_half]
  ring

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerPrimary
