module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveUpperPrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryNegativeGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.PositivePrimary

/-!
# Eight squares: the increasing lower-primary axial reference

At
alignment the two literal tuples have the stated value and slope
reserves. Monotonicity of the original signed product J transports both
reserves through every feasible angle, without changing its endpoint.
-/

section
/-!
## The four literal same-sign edge-five normalizations

Rows 0 and 1 are A₀ and A₁; rows 2 and 3 are B₀ and B₁. The
normalizations are exact reflection/reversals of original owners.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.EdgeFive
open CommonQuarter CorePairGeometry Arithmetic

abbrev Row := Fin 4
abbrev angle := ShortWord.MixedQuarter.angle
abbrev direction := ShortWord.MixedQuarter.direction
def c : Row→ℝ := ![23152/100000,48239/100000,48239/100000,23152/100000]
def p : Row→ℝ := ![0,-18602/100000,-20967/100000,-21826/100000]
def q : Row→ℝ := ![86884/100000,80996/100000,83048/100000,83472/100000]
def P : Row→ℝ := ![21826/100000,20967/100000,18602/100000,0]
def t : Row→ℝ := ![83472/100000,83048/100000,80996/100000,86884/100000]
def positive : Row→Bool := ![true,true,false,false]
def σ (r : Row) : ℝ := WordProblems.sign (positive r)
def ARows (r : Row) : Prop := r=0∨r=1
def BRows (r : Row) : Prop := r=2∨r=3
def width (x : ℝ) : ℝ := (1+Real.cos x+Real.sin x)/2
def cost (r : Row) (upper : Bool) (a b A B x : ℝ) : ℝ :=
  angle upper x+c r+p r*a+σ r*q r*b-P r*A-σ r*t r*B
def Secondary (r : Row) (upper : Bool) (_a b A B x : ℝ) : Prop :=
  width x≤σ r*b+A*Real.cos x+σ r*direction upper*B*Real.sin x
def Primary (r : Row) (upper : Bool) (a _b A B x : ℝ) : Prop :=
  width x≤a+direction upper*A*Real.sin x-σ r*B*Real.cos x

theorem A_sign {r : Row} (hr : ARows r) : σ r=1 := by
  rcases hr with rfl|rfl <;> norm_num [σ,positive,WordProblems.sign]
theorem B_sign {r : Row} (hr : BRows r) : σ r= -1 := by
  rcases hr with rfl|rfl <;> norm_num [σ,positive,WordProblems.sign]
theorem coefficient_bounds (r : Row) :
    p r≤0 ∧ 0≤P r ∧ (809/1000:ℝ)<q r ∧ q r<87/100 ∧
      (809/1000:ℝ)<t r ∧ t r<87/100 := by
  fin_cases r <;> norm_num [p,P,q,t]
theorem A_bounds (r : Row) (hr : ARows r) :
    (209/1000:ℝ)<P r ∧ P r<219/1000 ∧ 83/100<t r ∧ t r≤5217/6250 := by
  rcases hr with rfl|rfl <;> norm_num [P,t]

theorem secondary_support (r : Row) (upper : Bool) {a b A B x lam S T : ℝ}
    (hlam : 0≤lam) (hm : Secondary r upper a b A B x)
    (hs : S≤p r*a+σ r*(q r-lam)*b)
    (ht : T≤(-P r-lam*Real.cos x)*A+σ r*(-direction upper*lam*Real.sin x-t r)*B) :
    angle upper x+c r+lam*width x+S+T≤cost r upper a b A B x := by
  have hh := mul_le_mul_of_nonneg_left hm hlam
  dsimp [Secondary,cost] at *
  nlinarith
theorem primary_support (r : Row) (upper : Bool) {a b A B x lam S T : ℝ}
    (hlam : 0≤lam) (hm : Primary r upper a b A B x)
    (hs : S≤(p r-lam)*a+σ r*q r*b)
    (ht : T≤(-P r-direction upper*lam*Real.sin x)*A+σ r*(lam*Real.cos x-t r)*B) :
    angle upper x+c r+lam*width x+S+T≤cost r upper a b A B x := by
  have hh := mul_le_mul_of_nonneg_left hm hlam
  dsimp [Primary,cost] at *
  nlinarith

theorem outer_endpoint_support {a b X Y : ℝ} (hs : OuterState a b) (hY : 0≤Y) :
    min (X*outerAxial) ((X+Y)*outerDiagonal)≤X*a+Y*b :=
  outer_endpoints_lower hs hY (min_le_left _ _) (min_le_right _ _)

theorem trigonometric_norm (X Y x : ℝ) :
    |X*Real.cos x+Y*Real.sin x|≤Real.sqrt (X^2+Y^2) := by
  have hs := Real.sq_sqrt (show 0≤X^2+Y^2 by positivity)
  have hp := Real.sqrt_nonneg (X^2+Y^2)
  have hid : (X*Real.cos x+Y*Real.sin x)^2+(X*Real.sin x-Y*Real.cos x)^2=X^2+Y^2 := by
    linear_combination (X^2+Y^2)*(Real.sin_sq_add_cos_sq x)
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (X*Real.sin x-Y*Real.cos x)]
theorem axial_norm_bound : Real.sqrt ((1/2:ℝ)^2+(outerAxial-1/2)^2)<1043/1000 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hs := Real.sq_sqrt (show 0≤(1/2:ℝ)^2+(outerAxial-1/2)^2 by positivity)
  have hp := Real.sqrt_nonneg ((1/2:ℝ)^2+(outerAxial-1/2)^2)
  nlinarith
theorem axial_trig_upper (x : ℝ) :
    (1/2)*Real.cos x+(outerAxial-1/2)*Real.sin x<1043/1000 :=
  (le_abs_self _).trans_lt
    ((trigonometric_norm (1/2) (outerAxial-1/2) x).trans_lt axial_norm_bound)

theorem secondary_margin (r : Row) (upper : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (σ r) (σ r) (angle upper x)) :
    Secondary r upper a b A B x := by
  dsimp [Eight.forwardMargin] at hm
  rw [ShortWord.MixedQuarter.angle_sin,ShortWord.MixedQuarter.angle_cos,
    ShortWord.MixedQuarter.angle_width upper hx] at hm
  dsimp [Secondary,width]
  linarith
theorem primary_margin (r : Row) (upper : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (σ r) (σ r) (angle upper x)) :
    Primary r upper a b A B x := by
  dsimp [Eight.forwardMargin] at hm
  rw [ShortWord.MixedQuarter.angle_sin,ShortWord.MixedQuarter.angle_cos,
    ShortWord.MixedQuarter.angle_width upper hx] at hm
  dsimp [Primary,width]
  linarith

end SquaresInCircles.Eight.ShortOuterOne.EdgeFive
end
end
end

section
/-!
## Translated circle coordinates for the lower opposite edge-five contacts

The square roots are the actual positive circle coordinates. Their
domain includes every interval between a contact and its axial reference.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive
open CommonQuarter CorePairGeometry Arithmetic

def width (u : ℝ) : ℝ := (1+Real.cos u+Real.sin u)/2
def root (v : ℝ) : ℝ := Real.sqrt (Q0-v^2)
def rootD (v : ℝ) : ℝ := -v/root v
def rootDD (v : ℝ) : ℝ := -Q0/(root v)^3
def RootDomain (v : ℝ) : Prop := v∈Icc (1/2) X0
def cShift (r : Bool) : ℝ := c+(-p r+q r+P r+t r)/2
def D (r : Bool) (u : ℝ) : ℝ := P r*Real.cos u-t r*Real.sin u
def E (r : Bool) (u : ℝ) : ℝ := P r*Real.sin u+t r*Real.cos u
def axialZ (u : ℝ) : ℝ := 1/2+Real.cos u
def axialT (u : ℝ) : ℝ := root (axialZ u)
def axial (r : Bool) (u : ℝ) : ℝ := Real.pi/2-u+c+p r*outerAxial+
  (P r+t r)/2-D r u*axialZ u-E r u*axialT u

lemma root_domain_iff {v : ℝ} : RootDomain v↔v-1/2∈Icc 0 outerAxial := by
  rw [RootDomain,X0_eq]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
lemma root_eq_arc {v : ℝ} : root v=SameContact.arc (v-1/2)+1/2 := by
  dsimp [root,SameContact.arc]
  rw [show v-1/2+1/2=v by ring]
  ring
lemma root_positive {v : ℝ} (hv : RootDomain v) : 0<root v := by
  rw [root_eq_arc]
  exact SameContact.shifted_positive (root_domain_iff.1 hv)
lemma root_sq {v : ℝ} (hv : RootDomain v) : (root v)^2=Q0-v^2 := by
  have hsq := pow_le_pow_left₀ (show 0≤v by linarith [hv.1]) hv.2 2
  exact Real.sq_sqrt (by nlinarith [X0_sq])
lemma root_le_X0 {v : ℝ} (hv : RootDomain v) : root v≤X0 := by
  have hv2 : (1/4:ℝ)≤v^2 := by nlinarith [hv.1]
  nlinarith [root_sq hv,X0_sq,root_positive hv,X0_bounds.1]

lemma root_hasDerivAt {v : ℝ} (hv : RootDomain v) : HasDerivAt root (rootD v) v := by
  have hp : 0<Q0-v^2 := by rw [←root_sq hv]; exact pow_pos (root_positive hv) 2
  have h1 : HasDerivAt (fun y : ℝ => Q0-y^2) (-(2*v)) v := by
    simpa using (hasDerivAt_pow 2 v).const_sub Q0
  have hh : HasDerivAt root (-(2*v)/(2*Real.sqrt (Q0-v^2))) v := h1.sqrt hp.ne'
  exact hh.congr_deriv (by simp only [rootD,root]; ring)
lemma rootD_hasDerivAt {v : ℝ} (hv : RootDomain v) : HasDerivAt rootD (rootDD v) v := by
  have hh := ((hasDerivAt_id v).neg).div (root_hasDerivAt hv) (root_positive hv).ne'
  convert hh using 1
  · rfl
  · dsimp [rootD,rootDD]
    field_simp [(root_positive hv).ne']
    nlinarith [root_sq hv]
lemma root_antitone : AntitoneOn root (Icc (1/2) X0) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun v hv => (root_hasDerivAt hv).continuousAt.continuousWithinAt)
    (fun v hv => root_hasDerivAt (Ioo_subset_Icc_self hv))
  intro v hv
  dsimp [rootD]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [hv.1])
    (root_positive (Ioo_subset_Icc_self hv)).le

lemma axialZ_domain {u : ℝ} (hu : u∈Icc 0 (7/10)) : RootDomain (axialZ u) := by
  have ht := positive_trig hu
  exact ⟨by dsimp [axialZ]; linarith [ht.1],by dsimp [axialZ]; linarith [ht.2.1,X0_bounds.1]⟩
lemma axialT_positive {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<axialT u := root_positive (axialZ_domain hu)
lemma axialT_sq {u : ℝ} (hu : u∈Icc 0 (7/10)) : (axialT u)^2=Q0-(axialZ u)^2 :=
  root_sq (axialZ_domain hu)
lemma root_half : root (1/2)=X0 := by norm_num [root,X0]
lemma root_three_halves : root (3/2)=T0 := by norm_num [root,T0]

lemma width_ge_one {u : ℝ} (hu : u∈Icc 0 (7/10)) : 1≤width u := by
  dsimp [width]
  linarith [(positive_trig hu).2.2.2.2.2]

lemma E_positive (r : Bool) {u : ℝ} (hu : u∈Icc 0 (7/10)) : 0<E r u := by
  have ht := positive_trig hu
  have hP := mul_nonneg (show 0≤P r by linarith [(coefficient_bounds r).2.2.2.2.1]) ht.2.2.1
  have ht' := mul_pos (show 0<t r by linarith [(coefficient_bounds r).2.2.2.2.2.2.1])
    (show 0<Real.cos u by linarith [ht.1])
  dsimp [E]
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive
end
end
end

section
/-!
## The original lower-primary edge-five contact coordinates

The target coordinate `y` traverses its outer arc (`target_state`). The contact bound `K ≤ X₀` is
kept, and every interval down to the axial reference stays in that same contact domain
(`target_interval`, `angle_interval`, `reference_domain`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
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
    (fun _ hy => (K_target_hasDerivAt hy).continuousAt.continuousWithinAt)
    (fun _ hy => K_target_hasDerivAt (Ioo_subset_Icc_self hy))
    (fun _ hy => (div_pos (T_positive (Ioo_subset_Icc_self hy) hu)
      (X_positive (Ioo_subset_Icc_self hy))).le)
theorem K_angle_monotone {y : ℝ} (hy : Target y) : MonotoneOn (K y) (Icc 0 cap) :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (K_angle_hasDerivAt y u).continuousAt.continuousWithinAt)
    (fun u _ => K_angle_hasDerivAt y u)
    (fun _ hu => (T_positive hy (Ioo_subset_Icc_self hu)).le)
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

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
end
end
end

section
/-!
## Exact lower-primary contact derivatives

The second target derivative is first obtained directly from the two circle coordinates
(`targetFirst_hasDerivAt`), then rewritten with the numerator of `numerator_identity`
(`targetSecond_identity`). The axial angular derivative keeps its original signed coefficient
(`value_angle_hasDerivAt`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
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
  have hh := (rootD_hasDerivAt hv).neg
  have e : (fun w => w/root w) = -rootD := by
    funext w
    simp only [rootD, Pi.neg_apply]
    ring
  rw [e]
  exact hh.congr_deriv (by simp only [rootDD]; ring)
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
  have hh := (((ratio_hasDerivAt (contact_root hd)).comp u
    (K_angle_hasDerivAt y u)).const_mul (q r)).const_add (p r)
  have e : coefficient r y = fun x => p r+q r*((fun w => w/root w) ∘ K y) x := by
    funext x
    simp only [coefficient, V, Function.comp_apply]
    ring
  rw [e]
  exact hh.congr_deriv (by simp only [V]; ring)
theorem target_speed_hasDerivAt {y u : ℝ} (hy : Target y) :
    HasDerivAt (fun Y => T Y u/X Y) (-Q0*Real.sin u/(X y)^3) y := by
  have hX := X_positive hy
  have hh := (T_target_hasDerivAt (u:=u) hy).fun_div (X_hasDerivAt hy) hX.ne'
  refine hh.congr_deriv ?_
  have hQ : Q0=(X y)^2+y^2 := by linarith [X_sq hy]
  rw [hQ]
  field_simp
  dsimp [T,z]
  ring
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
  have hh := (((coefficient_target_hasDerivAt r hd).fun_mul
    (target_speed_hasDerivAt (u:=u) hd.2.1)).fun_add
      ((target_ratio_hasDerivAt hd.2.1).const_mul (P r))).sub_const (t r)
  have e : (fun Y => targetFirst r Y u) =
      fun Y => coefficient r Y u*(T Y u/X Y)+P r*(Y/X Y)-t r := by
    funext Y
    simp only [targetFirst]
    ring
  rw [e]
  refine hh.congr_deriv ?_
  have hX := (X_positive hd.2.1).ne'
  have hV := (V_positive hd).ne'
  simp only [targetSecond, coefficient]
  field_simp
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
  have hh := (((hasDerivAt_id' u).const_mul (-1)).const_add
    (Real.pi/2+cShift r-P r*X y-t r*y)).fun_add
      ((K_angle_hasDerivAt y u).const_mul (p r)) |>.fun_sub
        ((V_angle_hasDerivAt hd).const_mul (q r))
  have e : value r y = fun x => (Real.pi/2+cShift r-P r*X y-t r*y)+(-1)*x+p r*K y x-q r*V y x := by
    funext x
    simp only [value]
    ring
  rw [e]
  refine hh.congr_deriv ?_
  have hV := (V_positive hd).ne'
  simp only [coefficient]
  field_simp
  ring
theorem J_hasDerivAt (r : Bool) {u : ℝ} (hd : Domain (1/2) u) : HasDerivAt (J r) (JD r u) u := by
  have hh := (coefficient_angle_hasDerivAt r hd).fun_mul (T_angle_hasDerivAt (1/2) u)
  refine hh.congr_deriv ?_
  have hV := (V_positive hd).ne'
  simp only [JD, coefficient, K]
  field_simp
  ring
theorem reference_slope (r : Bool) (u : ℝ) :
    targetFirst r (1/2) u=J r u/X0+P r/(2*X0)-t r := by
  dsimp [targetFirst,J,X]
  rw [root_half]
  ring

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
end
end
end

section
/-!
## Whole-domain curvature and the increasing axial derivative

The
original numerical comparison gives C_yy > 1.20, hence the common 1.14
used in the completed square. The axial angular derivative increases
throughout every feasible prefix of the original angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
open CommonQuarter CorePairGeometry Arithmetic

def numeratorFloor : ℝ := (487/500)*(7/4:ℝ)^3-(9/40)*(Q0-13/4)
def bracketFloor : ℝ := 20967/100000+(83048/100000)*numeratorFloor/(1291/1000:ℝ)^3
theorem fixed_curvature :
    0<numeratorFloor ∧ 0<bracketFloor ∧ (6/5:ℝ)<Q0/(383/200:ℝ)^3*bracketFloor := by
  norm_num [numeratorFloor,bracketFloor,Q0]

theorem numerator_lower {y u : ℝ} (hd : Domain y u) :
    numeratorFloor<Real.cos u*(T y u)^3+Real.sin u*(3*(z y u)^2+3*z y u+1-Q0) := by
  have hb := contact_bounds hd
  have tr := small_trig hd.1
  have hT := T_positive hd.2.1 hd.1
  have hcube := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/4) hb.2.2.1.le 3
  have hk := mul_lt_mul_of_pos_right tr.1 (pow_pos hT 3)
  have hcub := mul_le_mul_of_nonneg_left hcube (by norm_num : (0:ℝ)≤487/500)
  have hz : (13/4:ℝ)≤3*(z y u)^2+3*z y u+1 := by nlinarith [hb.1]
  have hdrop := mul_le_mul_of_nonneg_left
    (show (13/4:ℝ)-Q0≤3*(z y u)^2+3*z y u+1-Q0 by linarith) tr.2.1
  have hsmall := mul_le_mul_of_nonpos_right tr.2.2.le (by norm_num [Q0] : (13/4:ℝ)-Q0≤0)
  dsimp [numeratorFloor]
  nlinarith only [hk,hcub,hdrop,hsmall]

theorem targetSecond_lower (r : Bool) {y u : ℝ} (hd : Domain y u) :
    (6/5:ℝ)<targetSecond r y u := by
  obtain ⟨N, hNdef⟩ : ∃ N, N=Real.cos u*(T y u)^3+Real.sin u*(3*(z y u)^2+3*z y u+1-Q0) :=
    ⟨_, rfl⟩
  have hN : numeratorFloor<N := hNdef ▸ numerator_lower hd
  have hc := coefficient_bounds r
  have hq : 0<q r := by linarith [hc.2.2.1]
  have hV := V_positive hd
  have hX := X_positive hd.2.1
  have hb := contact_bounds hd
  have hVc := pow_le_pow_left₀ hV.le hb.2.2.2.1.le 3
  have hXc := pow_le_pow_left₀ hX.le hb.2.2.2.2.le 3
  have hqN := mul_lt_mul_of_pos_left hN hq
  have hqfloor := mul_le_mul_of_nonneg_right hc.2.2.1 fixed_curvature.1.le
  have hterm : (83048/100000)*numeratorFloor/(1291/1000:ℝ)^3<q r*N/(V y u)^3 := by
    apply (lt_div_iff₀ (pow_pos hV 3)).mpr
    have hh := mul_le_mul_of_nonneg_left hVc
      (show 0≤(83048/100000)*numeratorFloor/(1291/1000:ℝ)^3 from
        div_nonneg (mul_nonneg (by norm_num) fixed_curvature.1.le) (by norm_num))
    norm_num at hh ⊢
    linarith only [hh,hqN,hqfloor]
  have hp := mul_nonpos_of_nonpos_of_nonneg (show p r≤0 by linarith [hc.2.1]) (small_trig hd.1).2.1
  have hbracket : bracketFloor<P r-p r*Real.sin u+q r*N/(V y u)^3 := by
    dsimp [bracketFloor]
    linarith [hc.2.2.2.2.1]
  have hQ : 0<Q0 := by norm_num [Q0]
  have hmul := mul_lt_mul_of_pos_left hbracket hQ
  have hX3 := pow_pos hX 3
  have hA : 0<Q0*bracketFloor := mul_pos hQ fixed_curvature.2.1
  have h1 : Q0/(383/200:ℝ)^3*bracketFloor≤Q0*bracketFloor/(X y)^3 := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left hA.le hX3 hXc
  have h2 : Q0*bracketFloor/(X y)^3<Q0/(X y)^3*(P r-p r*Real.sin u+q r*N/(V y u)^3) := by
    rw [div_mul_eq_mul_div]
    exact div_lt_div_of_pos_right hmul hX3
  rw [targetSecond_identity r hd,← hNdef]
  exact fixed_curvature.2.2.trans (h1.trans_lt h2)

theorem axial_numerator_positive {u : ℝ} (hd : Domain (1/2) u) :
    0<Q0*(T (1/2) u)^2-K (1/2) u*(K (1/2) u-1)*(V (1/2) u)^2 := by
  have hb := contact_bounds hd
  have hc := circle (u:=u) hd.2.1
  have hv := V_sq hd
  have hk : (3/2:ℝ)≤K (1/2) u ∧ K (1/2) u<383/200 := by
    dsimp [K]
    exact ⟨by linarith [hb.1],by linarith [hb.2.1]⟩
  have hT : Q0-(183/200:ℝ)^2<(T (1/2) u)^2 := by nlinarith [hb.1,hb.2.1]
  have hV : (V (1/2) u)^2≤Q0-9/4 := by nlinarith [hk.1]
  have hKz : K (1/2) u*(K (1/2) u-1)≤(383/200:ℝ)*(183/200) := by
    have hh := mul_le_mul hk.2.le
      (show K (1/2) u-1≤183/200 by linarith [hk.2])
      (by linarith [hk.1]) (by norm_num : (0:ℝ)≤383/200)
    exact hh
  have hprod := mul_le_mul hKz hV (sq_nonneg (V (1/2) u)) (by norm_num : (0:ℝ)≤(383/200)*(183/200))
  have hQT := mul_lt_mul_of_pos_left hT (by norm_num [Q0] : 0<Q0)
  norm_num [Q0] at hprod hQT ⊢
  linarith
theorem JD_positive (r : Bool) {u : ℝ} (hd : Domain (1/2) u) : 0<JD r u := by
  have hc := coefficient_bounds r
  have hq : 0<q r/(V (1/2) u)^3 :=
    div_pos (by linarith [hc.2.2.1]) (pow_pos (V_positive hd) 3)
  have hh := mul_pos hq (axial_numerator_positive hd)
  have hp := mul_nonpos_of_nonpos_of_nonneg (show p r≤0 by linarith [hc.2.1])
    (show 0≤K (1/2) u-1 by dsimp [K]; linarith [(contact_bounds hd).1])
  dsimp [JD]
  linarith
theorem J_monotone (r : Bool) {u : ℝ} (hd : Domain (1/2) u) :
    MonotoneOn (J r) (Icc 0 u) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hv => (J_hasDerivAt r (angle_interval hd hv)).continuousAt.continuousWithinAt)
    (fun _ hv => J_hasDerivAt r (angle_interval hd (Ioo_subset_Icc_self hv)))
    (fun _ hv => (JD_positive r (angle_interval hd (Ioo_subset_Icc_self hv))).le)

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

theorem X_half : X (1/2)=X0 := root_half
theorem K_initial : K (1/2) 0=3/2 := by norm_num [K,z]
theorem V_initial : V (1/2) 0=T0 := by rw [V,K_initial,root_three_halves]
theorem T_initial : T (1/2) 0=X0 := by
  simp only [T, X_half, Real.cos_zero, Real.sin_zero]
  ring
theorem J_initial_formula (r : Bool) : J r 0=(p r+q r*(3/2)/T0)*X0 := by
  rw [J,coefficient,K_initial,V_initial,T_initial]
theorem value_initial_formula (r : Bool) :
    value r (1/2) 0=Real.pi/2+cShift r+p r*(3/2)-q r*T0-P r*X0-t r/2 := by
  rw [value,K_initial,V_initial,X_half]
  ring
theorem slope_initial_formula (r : Bool) :
    targetFirst r (1/2) 0=p r+q r*(3/2)/T0+P r/(2*X0)-t r := by
  rw [reference_slope,J_initial_formula]
  field_simp [show X0≠0 by linarith [X0_bounds.1]]

private theorem r85_cast_lo {a b : ℝ} (e : a=b) (h : Interval a=Interval b) (I : Interval b) :
    (h.mpr I).lo=I.lo := by
  subst e
  rfl

def X0Box : Interval X0 := Interval.of_bounds ⟨X0_bounds.1.le,X0_bounds.2.le⟩
def T0Box : Interval T0 := Interval.of_bounds ⟨T0_bounds.1.le,T0_bounds.2.le⟩
def JBox (r : Bool) : Interval (J r 0) := by
  rw [J_initial_formula]
  exact ((Interval.point (p r)).add
    ((Interval.point (q r*(3/2))).div T0Box (by norm_num [T0Box,Interval.of_bounds]))).mul X0Box
def valueBox (r : Bool) : Interval (value r (1/2) 0) := by
  rw [value_initial_formula]
  exact (((((halfPi.add (Interval.point (cShift r))).add (Interval.point (p r*(3/2)))).sub
    ((Interval.point (q r)).mul T0Box)).sub ((Interval.point (P r)).mul X0Box)).sub (Interval.point (t r/2)))
def slopeBox (r : Bool) : Interval (targetFirst r (1/2) 0) := by
  rw [slope_initial_formula]
  exact (((Interval.point (p r)).add
    ((Interval.point (q r*(3/2))).div T0Box (by norm_num [T0Box,Interval.of_bounds]))).add
      ((Interval.point (P r)).div ((Interval.point 2).mul X0Box)
        (by norm_num [X0Box,Interval.of_bounds,Interval.mul,Interval.point]))).sub (Interval.point (t r))

theorem initial_J (r : Bool) : (143/100:ℝ)<J r 0 := by
  have hh : (143/100:ℝ)<(JBox r).lo := by
    unfold JBox
    rw [r85_cast_lo (J_initial_formula r)]
    cases r <;> dsimp [X0Box,T0Box,p,q,pQ,qQ] <;> mixed_fixed
  exact hh.trans_le (JBox r).mem.1
theorem initial_value (r : Bool) : (4493/5000:ℝ)<value r (1/2) 0 := by
  have hh : (4493/5000:ℝ)<(valueBox r).lo := by
    unfold valueBox
    rw [r85_cast_lo (value_initial_formula r)]
    cases r <;> dsimp [X0Box,T0Box,cShift,c,p,q,P,t,pQ,qQ,PQ,tQ] <;> mixed_fixed
  exact hh.trans_le (valueBox r).mem.1
theorem initial_slope (r : Bool) : -(3/125:ℝ)<targetFirst r (1/2) 0 := by
  have hh : -(3/125:ℝ)<(slopeBox r).lo := by
    unfold slopeBox
    rw [r85_cast_lo (slope_initial_formula r)]
    cases r <;> dsimp [X0Box,T0Box,p,q,P,t,pQ,qQ,PQ,tQ] <;> mixed_fixed
  exact hh.trans_le (slopeBox r).mem.1

theorem reference_J (r : Bool) {u : ℝ} (hd : Domain (1/2) u) : (143/100:ℝ)<J r u :=
  (initial_J r).trans_le (J_monotone r hd ⟨le_rfl,hd.1.1⟩ ⟨hd.1.1,le_rfl⟩ hd.1.1)
theorem reference_value (r : Bool) {u : ℝ} (hd : Domain (1/2) u) :
    (4493/5000:ℝ)<value r (1/2) u := by
  have hm : MonotoneOn (value r (1/2)) (Icc 0 u) :=
    monoOn_of_hasDeriv_nonneg
      (fun v hv => (value_angle_hasDerivAt r (angle_interval hd hv)).continuousAt.continuousWithinAt)
      (fun v hv => value_angle_hasDerivAt r (angle_interval hd (Ioo_subset_Icc_self hv)))
      (fun v hv => by
        have hh := reference_J r (angle_interval hd (Ioo_subset_Icc_self hv))
        dsimp [J] at hh
        linarith)
  exact (initial_value r).trans_le (hm ⟨le_rfl,hd.1.1⟩ ⟨hd.1.1,le_rfl⟩ hd.1.1)
theorem reference_slope_lower (r : Bool) {u : ℝ} (hd : Domain (1/2) u) :
    -(3/125:ℝ)<targetFirst r (1/2) u := by
  have hm := J_monotone r hd ⟨le_rfl,hd.1.1⟩ ⟨hd.1.1,le_rfl⟩ hd.1.1
  have hh := div_le_div_of_nonneg_right hm (show 0≤X0 by linarith [X0_bounds.1])
  have h0 := initial_slope r
  rw [reference_slope] at h0 ⊢
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
end
end
end
