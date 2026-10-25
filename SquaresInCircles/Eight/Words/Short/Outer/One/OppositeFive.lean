module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveAxial
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerPrimaryReference
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerSecondaryCurvature
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveUpperPrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperOneDiagonal
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeSecondary

/-!
# Eight squares: all four original opposite-sign edge-five owners

Both angle halves are covered (`secondary`, `primary`). The target-owned axes are recovered by
reversing the two adjacent coefficient tuples (`original_owner`). All original weak owner ties are
kept, and the cycle statement `actual_owner` uses the original role-five and role-six markers.
-/

section
/-!
## Both original lower-primary opposite edge-five tuples

The original source coordinate decreases to its contact (`original_contact_lower`); the whole
physical target segment is bounded by its axial tangent parabola (`contact_lower`). The final
completed square uses the curvature `1.14` and the slope `-.024`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
open CommonQuarter CorePairGeometry Arithmetic

def source (r : Bool) (a : ℝ) : ℝ := p r*a-q r*SameContact.arc a
def sourceD (r : Bool) (a : ℝ) : ℝ := p r+q r*SameContact.ratio a
theorem source_hasDerivAt (r : Bool) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (source r) (sourceD r a) a := by
  have h : HasDerivAt (source r) (p r*1-q r*(-SameContact.ratio a)) a :=
    ((hasDerivAt_id' a).const_mul (p r)).fun_sub
      ((SameContact.arc_hasDerivAt (Same.primary_domain ha)).const_mul (q r))
  exact h.congr_deriv (by simp only [sourceD]; ring)
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
  unfold source at hsource
  rw [(SameContact.actual_arc hs).2] at hsource
  have he : value r (B+1/2) u=
      Real.pi/2-u+c+source r (K (B+1/2) u-1/2)-P r*A-t r*B := by
    dsimp [value,cShift,V,source]
    rw [root_eq_arc,actual_X ht]
    ring
  rw [he]
  unfold source
  linarith

theorem original (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : width u≤a-A*Real.sin u-B*Real.cos u) :
    threshold<Real.pi/2-u+c+p r*a-q r*b-P r*A-t r*B :=
  (contact_lower r (actual_domain hs ht hu hm)).trans_le (original_contact_lower r hs ht hu hm)

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerPrimary
end
end
end

section
/-!
## The whole-angle axial slope bound for the lower secondary contact

The rotated horizontal projection is compared to 3/(2 T0) by the
written squared-difference identity. Its remaining bracket is one
decreasing quadratic on the entire sine interval. This supplies the
uniform axial derivative bound for both literal coefficient tuples.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
open CommonQuarter CorePairGeometry Arithmetic

def rotationU (u : ℝ) : ℝ := Real.cos u*axialZ u+Real.sin u*axialT u
def rotationV (u : ℝ) : ℝ := -Real.sin u*axialZ u+Real.cos u*axialT u
def ak (u : ℝ) : ℝ := (Real.cos u+2)/(Real.cos u+1)
def rho0 : ℝ := 3/(2*T0)
def bracket (u : ℝ) : ℝ := 2*rho0*(axialT u)^2-
  Q0*Real.sin u*(1+ak u/T0^2)
def quadratic (s : ℝ) : ℝ :=
  2*(29/25)*(T0^2+(3/2)*s^2)-Q0*s*(1+(157/100)/T0^2)

lemma T0_positive : 0<T0 := by linarith [T0_bounds.1]
lemma rho0_lower : (29/25:ℝ)<rho0 := by
  rw [rho0,lt_div_iff₀ (show 0<2*T0 by linarith [T0_bounds.1])]
  linarith [T0_bounds.2]
lemma rho0_sq : rho0^2*T0^2=9/4 := by
  dsimp [rho0]
  field_simp [T0_positive.ne']
  ring

lemma ak_bounds {u : ℝ} (hu : u∈Icc 0 cap) : (3/2:ℝ)≤ak u ∧ ak u<157/100 := by
  have ht := small_trig hu
  have hd : 0<Real.cos u+1 := by linarith [ht.1]
  constructor
  · rw [ak,le_div_iff₀ hd]
    linarith [ht.2.1]
  · rw [ak,div_lt_iff₀ hd]
    linarith [ht.1]

lemma axial_radical_identity {u : ℝ} (hu : u∈Icc 0 cap) :
    (axialT u)^2=T0^2+ak u*(Real.sin u)^2 := by
  have hk : Real.cos u+1≠0 := by linarith [(small_trig hu).1]
  have hroot := axialT_sq (small_angle hu)
  have ha : ak u*(Real.cos u+1)=Real.cos u+2 := by
    dsimp [ak]
    field_simp [hk]
  have he : ((axialT u)^2-T0^2)*(Real.cos u+1)=
      (Real.cos u+2)*(Real.sin u)^2 := by
    rw [hroot,T0_sq]
    dsimp [axialZ]
    linear_combination -(Real.cos u+2)*(Real.sin_sq_add_cos_sq u)
  have hz : ((axialT u)^2-T0^2-ak u*(Real.sin u)^2)*(Real.cos u+1)=0 := by
    linear_combination he-(Real.sin u)^2*ha
  rcases mul_eq_zero.mp hz with hh | hh
  · linarith
  · exact (hk hh).elim

lemma squared_projection_identity {u : ℝ} (hu : u∈Icc 0 cap) :
    (Real.cos u*axialZ u)^2-((rho0-Real.sin u)*axialT u)^2=Real.sin u*bracket u := by
  have hcircle : (Real.cos u)^2+(Real.sin u)^2=1 := by linarith [Real.sin_sq_add_cos_sq u]
  have hz : (axialZ u)^2+(axialT u)^2=Q0 := by linarith [axialT_sq (small_angle hu)]
  have hT := axial_radical_identity hu
  have hr := rho0_sq
  have hbase := T0_sq
  have hquot : (axialZ u)^2-rho0^2*(axialT u)^2=
      -Q0*ak u*(Real.sin u)^2/T0^2 := by
    apply (eq_div_iff (pow_ne_zero 2 T0_positive.ne')).2
    linear_combination T0^2*hz-(axialT u)^2*hbase-(axialT u)^2*hr-Q0*hT
  calc
    (Real.cos u*axialZ u)^2-((rho0-Real.sin u)*axialT u)^2=
      ((Real.cos u)^2+(Real.sin u)^2)*(axialZ u)^2-rho0^2*(axialT u)^2+
        2*rho0*Real.sin u*(axialT u)^2-(Real.sin u)^2*((axialZ u)^2+(axialT u)^2) := by ring
    _=(axialZ u)^2-rho0^2*(axialT u)^2+
        2*rho0*Real.sin u*(axialT u)^2-(Real.sin u)^2*Q0 := by rw [hcircle,hz]; ring
    _=Real.sin u*bracket u := by rw [hquot]; dsimp [bracket]; ring

lemma quadratic_positive {s : ℝ} (hs : s∈Icc 0 (13/20:ℝ)) : 0<quadratic s := by
  have href : (0:ℝ)<quadratic (13/20) := by norm_num [quadratic,T0_sq,Q0]
  have hf : 0≤Q0*(1+(157/100)/T0^2)-(87/25)*(s+13/20) := by
    rw [T0_sq]
    norm_num [Q0]
    linarith [hs.2]
  have hp := mul_nonneg (show 0≤(13/20:ℝ)-s by linarith [hs.2]) hf
  have he : quadratic s-quadratic (13/20)=
      (13/20-s)*(Q0*(1+(157/100)/T0^2)-(87/25)*(s+13/20)) := by
    dsimp [quadratic]
    ring
  linarith

lemma bracket_positive {u : ℝ} (hu : u∈Icc 0 cap) : 0<bracket u := by
  have ht := small_trig hu
  have hA := ak_bounds hu
  have hT := axial_radical_identity hu
  have hAlow := mul_le_mul_of_nonneg_right hA.1 (sq_nonneg (Real.sin u))
  have hTlow : T0^2+(3/2)*(Real.sin u)^2≤(axialT u)^2 := by linarith
  have hrho := mul_le_mul_of_nonneg_right rho0_lower.le (show 0≤2*(axialT u)^2 by positivity)
  have hroot := mul_le_mul_of_nonneg_left hTlow (by norm_num : (0:ℝ)≤2*(29/25))
  have hAdiv := div_le_div_of_nonneg_right hA.2.le (sq_nonneg T0)
  have hneg := mul_le_mul_of_nonneg_left hAdiv
    (mul_nonneg (by norm_num [Q0] : 0≤Q0) ht.2.2.1)
  have hquad := quadratic_positive ⟨ht.2.2.1,ht.2.2.2.le⟩
  dsimp [bracket,quadratic] at *
  nlinarith only [hrho,hroot,hneg,hquad]

lemma horizontal_ratio {u : ℝ} (hu : u∈Icc 0 cap) : rho0≤rotationU u/axialT u := by
  have ht := small_trig hu
  have hT := axialT_positive (small_angle hu)
  have hZ : 0<axialZ u := by dsimp [axialZ]; linarith [ht.1]
  have hleft := mul_pos (show 0<Real.cos u by linarith [ht.1]) hZ
  have hright := mul_pos (show 0<rho0-Real.sin u by linarith [rho0_lower,ht.2.2.2]) hT
  have hid := squared_projection_identity hu
  have hsq := mul_nonneg ht.2.2.1 (bracket_positive hu).le
  have hroot : (rho0-Real.sin u)*axialT u≤Real.cos u*axialZ u := by nlinarith only [hid,hsq,hleft,hright]
  apply (le_div_iff₀ hT).2
  dsimp [rotationU]
  nlinarith only [hroot]

lemma vertical_ratio {u : ℝ} (hu : u∈Icc 0 cap) : rotationV u/axialT u≤1 := by
  have ht := small_trig hu
  have hT := axialT_positive (small_angle hu)
  have hZ : 0≤axialZ u := by dsimp [axialZ]; linarith [ht.1]
  have hk := mul_le_mul_of_nonneg_right ht.2.1 hT.le
  have hs := mul_nonneg ht.2.2.1 hZ
  apply (div_le_one hT).2
  dsimp [rotationV]
  linarith

lemma first_axial_identity (r : Bool) {u : ℝ} (hu : u∈Icc 0 cap) :
    first r (1/2) u=(-p r)/(2*X0)-q r+t r*(rotationU u/axialT u)-P r*(rotationV u/axialT u) := by
  have hT := axialT_positive (small_angle hu)
  have hX : 0<X0 := by linarith [X0_bounds.1]
  have h1 : rootD (1/2)=-(1/2)/X0 := by rw [rootD,root_half]
  have h2 : rootD (Z (1/2) u)=-axialZ u/axialT u := rfl
  simp only [first,h1,h2,D,E,rotationU,rotationV]
  field_simp
  ring

lemma fixed_slope (r : Bool) : (-3/125:ℝ)<(-p r)/(2*X0)-q r+3*t r/(2*T0)-P r := by
  have hp : 0≤-p r := by linarith [(coefficient_bounds r).2.1]
  have ht : 0≤3*t r := by linarith [(coefficient_bounds r).2.2.2.2.2.2.1]
  have hX : 0<2*X0 := by linarith [X0_bounds.1]
  have hT : 0<2*T0 := by linarith [T0_bounds.1]
  have hx := div_le_div_of_nonneg_left hp hX
    (show 2*X0≤2*(1914575672/1000000000:ℝ) by linarith [X0_bounds.2])
  have hv := div_le_div_of_nonneg_left ht hT
    (show 2*T0≤2*(1290581265/1000000000:ℝ) by linarith [T0_bounds.2])
  have hfixed : (-3/125:ℝ)<(-p r)/(2*(1914575672/1000000000:ℝ))-q r+
      3*t r/(2*(1290581265/1000000000:ℝ))-P r := by
    cases r <;> norm_num [p,q,P,t,pQ,qQ,PQ,tQ]
  linarith

theorem first_axial_lower (r : Bool) {u : ℝ} (hu : u∈Icc 0 cap) : (-3/125:ℝ)<first r (1/2) u := by
  have hU := mul_le_mul_of_nonneg_left (horizontal_ratio hu)
    (show 0≤t r by linarith [(coefficient_bounds r).2.2.2.2.2.2.1])
  have hV := mul_le_mul_of_nonneg_left (vertical_ratio hu)
    (show 0≤P r by linarith [(coefficient_bounds r).2.2.2.2.1])
  rw [first_axial_identity r hu]
  have hh := fixed_slope r
  have e : t r*rho0=3*t r/(2*T0) := by dsimp [rho0]; ring
  rw [e] at hU
  rw [mul_one] at hV
  linarith only [hU,hV,hh]

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
end
end
end

section
/-!
## Both full lower secondary owners on opposite edge five

The whole axial polynomial, the whole-angle slope comparison, and
the actual contact curvature combine by the stated completed square.
The result starts with the original two states and the weak owner.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
open CommonQuarter CorePairGeometry Arithmetic

theorem contact_lower (r : Bool) {v u : ℝ} (hd : Domain v u) (hx : half u≤halfCap) :
    threshold<cost r v u := by
  have hvalue := Axial.lower r (small_angle hd.1) hx
  have hslope := first_axial_lower r hd.1
  have htangent := tangent r hd
  have hfirst := mul_le_mul_of_nonneg_right hslope.le
    (show 0≤v-1/2 by linarith [hd.2.1.1])
  have hsquare := sq_nonneg (v-1/2-2/95)
  dsimp [threshold]
  nlinarith only [hvalue,htangent,hfirst,hsquare]

theorem original (r : Bool) {a b A B u : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hu : u∈Icc 0 (7/10))
    (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    threshold<Real.pi/2-u+c+p r*a-q r*b-P r*A-t r*B := by
  have hd := contact_domain hs ht hu hm
  have hhalf := forced_half_cap hu (feasible hs ht hu hm)
  exact (contact_lower r hd hhalf.le).trans_le (original_to_contact r hs ht hu hm)

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem secondary (r : Bool) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B (-1) 1 φ) :
    threshold<φ+c+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨high,u,hu,rfl⟩ := Unit.angle_cover hφ
  have hsep := OppositeSecondary.margin high hu hm
  cases high
  · have hh := LowerSecondary.original r hs ht hu (by
      simp only [Unit.direction,width,Bool.false_eq_true,↓reduceIte] at hsep ⊢
      linarith)
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hh := UpperSecondary.original r hs ht hu (by
      simp only [Unit.direction,ite_true] at hsep
      linarith)
    simp only [Unit.angle,Unit.direction,ite_true,threshold]
    linarith

theorem primary (r : Bool) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 φ) :
    threshold<φ+c+p r*a-q r*b-P r*A-t r*B := by
  obtain ⟨high,u,hu,rfl⟩ := Unit.angle_cover hφ
  have hsep := Opposite.Primary.normalized_margin high hu hm
  cases high
  · have hh := LowerPrimary.original r hs ht hu (by
      simp only [Unit.direction,width,Opposite.Primary.width,Bool.false_eq_true,
        ↓reduceIte] at hsep ⊢
      linarith)
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hh := UpperPrimary.original r hs ht hu (by
      simp only [Unit.direction,Opposite.Primary.width,ite_true] at hsep
      linarith)
    simp only [Unit.angle,Unit.direction,ite_true,threshold]
    linarith

theorem original_owner (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    threshold<φ+c+p false*a-q false*b-P false*A-t false*B := by
  fin_cases j
  · exact secondary false hs ht hφ hm
  · have hh := primary true ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [p,q,P,t,pQ,qQ,PQ,tQ] at hh ⊢
    linarith
  · have hh := secondary true ht hs hφ (by simpa [Eight.forwardMargin,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using hm)
    norm_num [p,q,P,t,pQ,qQ,PQ,tQ] at hh ⊢
    linarith
  · exact primary false hs ht hφ hm

theorem original {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : ∃j : Fin 4,0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    threshold<φ+c+p false*a-q false*b-P false*A-t false*B := by
  obtain ⟨j,hj⟩ := hm
  exact original_owner j hs ht hφ hj

theorem marker_owner (j : Fin 4) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (-1) 1 φ) :
    (WordProblems.wrongGamma .short 5:ℝ)<φ+wrongValue .short 5 .outer false a b-
      wrongValue .short (next 5) .outer true A B := by
  have hh := original_owner j hs ht hφ hm
  norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
    WordProblems.signIndex,WordProblems.sign,WordProblems.wrongGamma,next,
    threshold,c,p,q,P,t,pQ,qQ,PQ,tQ] at hh ⊢
  linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (_hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer) (hrole : i=5)
    (hσ : positiveOf C i=false) (hτ : positiveOf C (next i)=true)
    (j : Fin 4) (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  subst hrole
  have he : phaseValue F hgap 5-Real.pi/2=difference F 5 := by
    simp [phaseValue,hi]
  have hφ : |phaseValue F hgap 5-Real.pi/2|≤7/10 := by
    rw [he]
    exact (difference_small F 5).le
  have hsource : OuterState (C.a 5) (C.b 5) := by
    simpa [State,hs] using actual_state C 5
  have htarget : OuterState (C.a (next 5)) (C.b (next 5)) := by
    simpa [State,ht] using actual_state C (next 5)
  have hm := original_margin C F hgap 5 j howner
  simp only [hσ,hτ,WordProblems.sign,Bool.false_eq_true,ite_false,ite_true,
    Rat.cast_neg,Rat.cast_one] at hm
  have hh := marker_owner j hsource htarget hφ hm
  simpa only [wrongMarker,hs,ht,hσ,hτ] using hh

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive
end
end
end
