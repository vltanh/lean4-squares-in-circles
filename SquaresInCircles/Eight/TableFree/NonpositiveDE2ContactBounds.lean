module

public import SquaresInCircles.Eight.TableFree.BelowERotatedCycle

/-!
# Whole-interval bounds for the original-circle rotated DE2 curve

Uncompiled reconstruction.  The source E primary greater than one
keeps the original-circle radical above 3/2.  The original D coordinate
bounds give the exact contact tangent and its positive derivative.
A circle projection and a single completed square bound the remaining
angular coefficient on the entire frame interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NonpositiveDE2Contact

def b (D : SignedPoint) (z : ℝ) : ℝ :=
  1/2-(D.a-1/2)*Real.cos z+(1/2-D.y)*Real.sin z

def K (D : SignedPoint) (z : ℝ) : ℝ :=
  (D.a-1/2)*Real.sin z+(1/2-D.y)*Real.cos z

def Y (D : SignedPoint) (z : ℝ) : ℝ := b D z+1/2
def X (E D : SignedPoint) (z : ℝ) : ℝ := OriginalECircle.root E (b D z)
def U (E D : SignedPoint) (z : ℝ) : ℝ := X E D z-K D z

def J (E D H : SignedPoint) (α z : ℝ) : ℝ :=
  OriginalECircle.eh E H (α+z) (b D z)

@[simp] theorem b_zero (D : SignedPoint) : b D 0=1-D.a := by simp [b]; ring

theorem b_derivative (D : SignedPoint) (z : ℝ) : HasDerivAt (b D) (K D z) z := by
  have h := (((Real.hasDerivAt_cos z).const_mul (D.a-1/2)).const_sub (1/2)).add
    ((Real.hasDerivAt_sin z).const_mul (1/2-D.y))
  convert h using 1
  · funext x; simp only [b,Pi.add_apply]
  · simp only [K]; ring

theorem K_lower {D : SignedPoint} {z : ℝ}
    (hDa : 1/2≤D.a) (hDy : 353/500< -D.y) (hz : z∈Icc 0 (7/10:ℝ)) :
    (9/10:ℝ)<K D z := by
  have ht := transport_trig hz
  have hfirst := mul_nonneg (sub_nonneg.mpr hDa) ht.2.2.1
  have hsecond := mul_lt_mul_of_pos_left ht.1 (show 0<1/2-D.y by linarith)
  dsimp [K]
  nlinarith

theorem b_growth {D : SignedPoint} {x y : ℝ}
    (hDa : 1/2≤D.a) (hDy : 353/500< -D.y)
    (hx : x∈Icc 0 (7/10:ℝ)) (hy : y∈Icc 0 (7/10:ℝ)) (hxy : x≤y) :
    (9/10)*(y-x)≤b D y-b D x := by
  exact derivative_reserve
    (fun z _ => (b_derivative D z).continuousAt.continuousWithinAt)
    (fun z _ => b_derivative D z)
    (fun z hz => (K_lower hDa hDy (Ioo_subset_Icc_self hz)).le) hx hy hxy

theorem b_monotone {D : SignedPoint}
    (hDa : 1/2≤D.a) (hDy : 353/500< -D.y) : MonotoneOn (b D) (Icc 0 (7/10:ℝ)) := by
  intro x hx y hy hxy
  have hh := b_growth hDa hDy hx hy hxy
  linarith

theorem DE2_slack (E D : SignedPoint) {z : ℝ} (y : ℝ) (hz : z∈Icc 0 (7/10:ℝ)) :
    quarterProjection D (OriginalECircle.point E y) (-z) 2-edgeWidth (-z)=y-b D z := by
  rw [edgeWidth_negative_formula hz]
  simp [quarterProjection,OriginalECircle.point,b]
  ring

theorem eh_tangent_antitone (E H : SignedPoint) {p y₁ y₂ : ℝ}
    (hp : p∈Icc 0 (7/10:ℝ)) (hy₁ : 0≤y₁) (hy : y₁≤y₂) :
    OriginalECircle.eh E H p y₂≤OriginalECircle.eh E H p y₁ := by
  have hsq := pow_le_pow_left₀ (show 0≤y₁+1/2 by linarith)
    (show y₁+1/2≤y₂+1/2 by linarith) 2
  have hroot := Real.sqrt_le_sqrt (show E.circle-(y₂+1/2)^2≤E.circle-(y₁+1/2)^2 by linarith)
  have ht := transport_trig hp
  have hmajor := mul_le_mul_of_nonneg_right hroot ht.2.2.1
  have hminor := mul_le_mul_of_nonneg_right hy (show 0≤Real.cos p by linarith [ht.1])
  dsimp [OriginalECircle.eh,OriginalECircle.primary,OriginalECircle.root]
  nlinarith

def upper (z : ℝ) : ℝ := ((773/1000)-Real.sin z)/Real.cos z
def upperD (z : ℝ) : ℝ := ((773/1000)*Real.sin z-1)/(Real.cos z)^2

theorem upper_derivative {z : ℝ} (hz : z∈Icc 0 (7/10:ℝ)) :
    HasDerivAt upper (upperD z) z := by
  have hc : Real.cos z≠0 := ne_of_gt (by linarith [(transport_trig hz).1])
  convert ((Real.hasDerivAt_sin z).const_sub (773/1000)).div
    (Real.hasDerivAt_cos z) hc using 1
  · rfl
  · dsimp [upperD]
    field_simp [hc]
    nlinarith [Real.sin_sq_add_cos_sq z]

theorem upper_rate {z : ℝ} (hz : z∈Icc 0 (7/10:ℝ)) : upperD z< -(4/5) := by
  have hc : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hquad : 0<(4/5)*(Real.sin z)^2-(773/1000)*Real.sin z+1/5 := by
    nlinarith [sq_nonneg (Real.sin z-773/1600)]
  apply (div_lt_iff₀ (sq_pos_of_pos hc)).2
  nlinarith [Real.sin_sq_add_cos_sq z]

theorem upper_linear {z : ℝ} (hz : z∈Icc 0 (7/10:ℝ)) :
    upper z≤773/1000-(4/5)*z := by
  have hh := derivative_reserve
    (f := fun z => -upper z) (df := fun z => -upperD z) (k := (4/5:ℝ))
    (fun z hz => (upper_derivative hz).neg.continuousAt.continuousWithinAt)
    (fun z hz => (upper_derivative (Ioo_subset_Icc_self hz)).neg)
    (fun z hz => by linarith [upper_rate (Ioo_subset_Icc_self hz)])
    (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hz hz.1
  have hzero : upper 0=773/1000 := by norm_num [upper]
  rw [hzero] at hh
  linarith

theorem U_upper {E D : SignedPoint} {z : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.circle≤qCap)
    (hDy : 353/500< -D.y) (hz : z∈Icc 0 (7/10:ℝ))
    (hb : b D z∈Icc 0 (-E.y)) :
    U E D z<773/1000-(4/5)*z := by
  have hr := OriginalECircle.root_bounds hEs hEy hb
  have hnorm : (X E D z)^2+(Y D z)^2=E.circle := by
    dsimp [X,Y]
    linarith [hr.2.2]
  have hrotation : (X E D z*Real.cos z+Y D z*Real.sin z)^2+
      (X E D z*Real.sin z-Y D z*Real.cos z)^2=E.circle := by
    have hh := circle_rotation_identity (X E D z) (-(Y D z)) z
    nlinarith
  have hproject : X E D z*Real.cos z+Y D z*Real.sin z<1979/1000 := by
    have hs := sq_nonneg (X E D z*Real.sin z-Y D z*Real.cos z)
    dsimp [qCap] at hEc
    nlinarith
  have hKidentity : K D z*Real.cos z+Y D z*Real.sin z=1/2-D.y+Real.sin z := by
    dsimp [K,Y,b]
    linear_combination (1/2-D.y)*(Real.sin_sq_add_cos_sq z)
  have hscaled : U E D z*Real.cos z<773/1000-Real.sin z := by
    dsimp [U]
    nlinarith
  have hc : 0<Real.cos z := by linarith [(transport_trig hz).1]
  have hu : U E D z<upper z := (lt_div_iff₀ hc).2 hscaled
  exact hu.trans_le (upper_linear hz)

theorem Y_upper {D : SignedPoint} {z : ℝ}
    (hDa : 353/500<D.a) (hDy : -D.y<9/10) (hz : z∈Icc 0 (7/10:ℝ)) :
    Y D z<(1399/1000)*(3/5+(11/10)*z) := by
  have ht := transport_trig hz
  have hcos : 0<Real.cos z := by linarith [ht.1]
  have hA := mul_lt_mul_of_pos_right (show 103/500<D.a-1/2 by linarith) hcos
  have hB := mul_le_mul_of_nonneg_right (show 1/2-D.y≤7/5 by linarith) ht.2.2.1
  have hsin := Real.sin_le hz.1
  have hcoslower := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hquad := mul_nonneg hz.1 (show 0≤7/10-z by linarith [hz.2])
  dsimp [Y,b]
  nlinarith

theorem ratio_upper {E D : SignedPoint} {z : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 1<E.a)
    (hDa : 353/500<D.a) (hDy : -D.y<9/10) (hz : z∈Icc 0 (7/10:ℝ))
    (hb : b D z∈Icc 0 (-E.y)) :
    Y D z/X E D z<3/5+(11/10)*z := by
  have hr := OriginalECircle.root_bounds hEs hEy hb
  have hX : (1399/1000:ℝ)<X E D z := by dsimp [X]; linarith [hr.2.1]
  have hX0 : 0<X E D z := by linarith
  have hrpos : 0<(3/5:ℝ)+(11/10)*z := by linarith [hz.1]
  have hY := Y_upper hDa hDy hz
  have hprod := mul_lt_mul_of_pos_right hX hrpos
  apply (div_lt_iff₀ hX0).2
  nlinarith

end SquaresInCircles.Eight.TableFree.NonpositiveDE2Contact
