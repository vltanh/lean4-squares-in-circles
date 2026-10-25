module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositeFiveLowerData

/-!
# The original lower-primary edge-five contact coordinates

Uncompiled transcription of Section 3, equation (19). The target
coordinate y traverses its genuine outer arc. The actual contact bound
K ≤ X₀ is retained, and every interval down to the axial reference stays
in that same contact domain.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerPrimary
open CommonQuarter CorePairGeometry Arithmetic

abbrev cap := Opposite.Primary.Negative.cap
def X (y : ℝ) : ℝ := root y
def z (y u : ℝ) : ℝ := Real.sin u*X y+Real.cos u*y
def K (y u : ℝ) : ℝ := 1+z y u
def V (y u : ℝ) : ℝ := root (K y u)
def T (y u : ℝ) : ℝ := Real.cos u*X y-Real.sin u*y
def Target (y : ℝ) : Prop := y∈Icc (1/2) (outerDiagonal+1/2)
def Domain (y u : ℝ) : Prop := u∈Icc 0 cap ∧ Target y ∧ K y u≤X0

theorem target_root {y : ℝ} (hy : Target y) : RootDomain y :=
  ⟨hy.1,hy.2.trans (by rw [X0_eq]; linarith [SameContact.diagonal_le_axial])⟩
theorem target_state {y : ℝ} (hy : Target y) : OuterState (X y-1/2) (y-1/2) := by
  have hs := SameContact.arc_state (show y-1/2∈Icc 0 outerDiagonal from ⟨by linarith [hy.1],by linarith [hy.2]⟩)
  simpa [X,root_eq_arc] using hs
theorem X_positive {y : ℝ} (hy : Target y) : 0<X y := root_positive (target_root hy)
theorem X_sq {y : ℝ} (hy : Target y) : (X y)^2=Q0-y^2 := root_sq (target_root hy)
theorem X_bounds {y : ℝ} (hy : Target y) : y≤X y ∧ X y≤X0 := by
  have hs := target_state hy
  exact ⟨by linarith [hs.2.1],root_le_X0 (target_root hy)⟩
theorem small_trig {u : ℝ} (hu : u∈Icc 0 cap) :
    (487/500:ℝ)<Real.cos u ∧ 0≤Real.sin u ∧ Real.sin u<9/40 := by
  have hh := Opposite.Primary.Negative.small_trig hu
  exact ⟨by linarith [hh.1],hh.2.1,by linarith [hh.2.2]⟩
theorem T_positive {y u : ℝ} (hy : Target y) (hu : u∈Icc 0 cap) : 0<T y u := by
  have ht := small_trig hu
  have hX := X_bounds hy
  have hprod := mul_le_mul_of_nonneg_left hX.1 (show 0≤Real.cos u by linarith [ht.1])
  have hpos := mul_pos (show 0<y by linarith [hy.1]) (show 0<Real.cos u-Real.sin u by linarith [ht.1,ht.2.2])
  dsimp [T]
  nlinarith
theorem z_lower {y u : ℝ} (hy : Target y) (hu : u∈Icc 0 cap) : (1/2:ℝ)≤z y u := by
  have tr := positive_trig (Opposite.Primary.Negative.small_angle hu)
  have hX : (1/2:ℝ)≤X y := hy.1.trans (X_bounds hy).1
  have hs := mul_le_mul_of_nonneg_right hX tr.2.2.1
  have hk := mul_le_mul_of_nonneg_right hy.1 (show 0≤Real.cos u by linarith [tr.1])
  dsimp [z]
  nlinarith [tr.2.2.2.2.2]
theorem circle {y u : ℝ} (hy : Target y) : (T y u)^2+(z y u)^2=Q0 := by
  have hh := X_sq hy
  dsimp [T,z]
  linear_combination hh+((X y)^2+y^2)*(Real.sin_sq_add_cos_sq u)
theorem X_inverse (y u : ℝ) : X y=Real.cos u*T y u+Real.sin u*z y u := by
  dsimp [T,z]
  linear_combination -(X y)*(Real.sin_sq_add_cos_sq u)
theorem contact_root {y u : ℝ} (hd : Domain y u) : RootDomain (K y u) :=
  ⟨by dsimp [K]; linarith [z_lower hd.2.1 hd.1],hd.2.2⟩
theorem V_positive {y u : ℝ} (hd : Domain y u) : 0<V y u := root_positive (contact_root hd)
theorem V_sq {y u : ℝ} (hd : Domain y u) : (V y u)^2=Q0-(K y u)^2 := root_sq (contact_root hd)
theorem contact_bounds {y u : ℝ} (hd : Domain y u) :
    (1/2:ℝ)≤z y u ∧ z y u<183/200 ∧ (7/4:ℝ)<T y u ∧ V y u<1291/1000 ∧ X y<383/200 := by
  have hz := z_lower hd.2.1 hd.1
  have hzu : z y u<183/200 := by
    have hk := hd.2.2
    dsimp [K] at hk
    linarith [X0_bounds.2]
  have hT := T_positive hd.2.1 hd.1
  have hcircle := circle (u:=u) hd.2.1
  have hK : (3/2:ℝ)≤K y u := by dsimp [K]; linarith
  have hVt : V y u≤root (3/2) := root_antitone
    (show RootDomain (3/2) from ⟨by norm_num,by linarith [X0_bounds.1]⟩) (contact_root hd) hK
  rw [root_three_halves] at hVt
  refine ⟨hz,hzu,?_,by linarith [T0_bounds.2],?_⟩
  · norm_num [Q0] at hcircle
    nlinarith
  · linarith [(X_bounds hd.2.1).2,X0_bounds.2]

theorem X_hasDerivAt {y : ℝ} (hy : Target y) : HasDerivAt X (-y/X y) y := root_hasDerivAt (target_root hy)
theorem K_target_hasDerivAt {y u : ℝ} (hy : Target y) :
    HasDerivAt (fun Y => K Y u) (T y u/X y) y := by
  have hh := (((X_hasDerivAt hy).const_mul (Real.sin u)).add
    ((hasDerivAt_id y).const_mul (Real.cos u))).const_add 1
  convert hh using 1
  · rfl
  · dsimp [T]
    field_simp [(X_positive hy).ne']
    ring
theorem K_angle_hasDerivAt (y u : ℝ) : HasDerivAt (K y) (T y u) u := by
  have hh := (((Real.hasDerivAt_sin u).mul_const (X y)).fun_add
    ((Real.hasDerivAt_cos u).mul_const y)).const_add 1
  exact hh.congr_deriv (by dsimp [T]; ring)
theorem T_target_hasDerivAt {y u : ℝ} (hy : Target y) :
    HasDerivAt (fun Y => T Y u) (-z y u/X y) y := by
  convert ((X_hasDerivAt hy).const_mul (Real.cos u)).sub
    ((hasDerivAt_id y).const_mul (Real.sin u)) using 1
  · rfl
  · dsimp [z]
    field_simp [(X_positive hy).ne']
    ring
theorem T_angle_hasDerivAt (y u : ℝ) : HasDerivAt (T y) (-z y u) u := by
  have hh := ((Real.hasDerivAt_cos u).mul_const (X y)).fun_sub
    ((Real.hasDerivAt_sin u).mul_const y)
  exact hh.congr_deriv (by dsimp [z]; ring)
theorem K_target_monotone {u : ℝ} (hu : u∈Icc 0 cap) :
    MonotoneOn (fun y => K y u) (Icc (1/2) (outerDiagonal+1/2)) :=
  monoOn_of_hasDeriv_nonneg
    (fun y hy => (K_target_hasDerivAt hy).continuousAt.continuousWithinAt)
    (fun y hy => K_target_hasDerivAt (Ioo_subset_Icc_self hy))
    (fun y hy => (div_pos (T_positive (Ioo_subset_Icc_self hy) hu)
      (X_positive (Ioo_subset_Icc_self hy))).le)
theorem K_angle_monotone {y : ℝ} (hy : Target y) : MonotoneOn (K y) (Icc 0 cap) :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (K_angle_hasDerivAt y u).continuousAt.continuousWithinAt)
    (fun u _ => K_angle_hasDerivAt y u)
    (fun u hu => (T_positive hy (Ioo_subset_Icc_self hu)).le)
theorem target_interval {y u Y : ℝ} (hd : Domain y u) (hY : Y∈Icc (1/2) y) : Domain Y u := by
  have hYt : Target Y := ⟨hY.1,hY.2.trans hd.2.1.2⟩
  exact ⟨hd.1,hYt,(K_target_monotone hd.1 hYt hd.2.1 hY.2).trans hd.2.2⟩
theorem angle_interval {y u v : ℝ} (hd : Domain y u) (hv : v∈Icc 0 u) : Domain y v :=
  ⟨⟨hv.1,hv.2.trans hd.1.2⟩,hd.2.1,
    (K_angle_monotone hd.2.1 ⟨hv.1,hv.2.trans hd.1.2⟩ hd.1 hv.2).trans hd.2.2⟩
theorem reference_domain {y u : ℝ} (hd : Domain y u) : Domain (1/2) u :=
  target_interval hd ⟨le_rfl,hd.2.1.1⟩

theorem actual_X {A B : ℝ} (ht : OuterState A B) : X (B+1/2)=A+1/2 := by
  rw [X,root_eq_arc]
  simpa using congrArg (fun v : ℝ => v+1/2) (SameContact.actual_arc ht).1
theorem actual_domain {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤a-A*Real.sin u-B*Real.cos u) : Domain (B+1/2) u := by
  have hcap := Opposite.Primary.Negative.forced_cap hs ht hu (by simpa [width,Opposite.Primary.width] using hm)
  refine ⟨⟨hu.1,hcap.le⟩,⟨by linarith [ht.1],by linarith [(outer_bounds ht).2.2.2.1]⟩,?_⟩
  have ha := (outer_bounds hs).2.1
  rw [K,z,actual_X ht,X0_eq]
  dsimp [width] at hm
  nlinarith

end SquaresInCircles.Eight.TableFree.ShortOuterOne.OppositeFive.LowerPrimary
