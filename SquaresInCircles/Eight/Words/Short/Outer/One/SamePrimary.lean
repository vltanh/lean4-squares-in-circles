module

public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.System
public import SquaresInCircles.Eight.Words.Second.Outer.Negative.ThreeAligned
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryUpperAxial
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryNegativeGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryDiagonalData
public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePositiveGeometry

/-!
# Eight squares: both full halves of the three remaining same-sign primary owners

The exact reflection/reversal restores the third original owner and
its literal adjacent role labels. All original weak owner ties remain.
-/

section
/-!
## The exact angular-stationarity event of the exceptional upper owner

At a stationary target coordinate the angular derivative is
bounded below by the displayed axial expression Omega. Its unique
zero is obtained from its two named rational endpoint signs.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.Stationary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open SameContact (arc ratio)
open ShortWord.MixedQuarter.Reference

def targetU (B : ℝ) : ℝ := arc B+1/2
def targetV (B : ℝ) : ℝ := B+1/2
def targetProjection (B x : ℝ) : ℝ := targetU B*Real.cos x+targetV B*Real.sin x
def targetCharge (B : ℝ) : ℝ := t 1*targetU B-P 1*targetV B
def axisProjection (x : ℝ) : ℝ := (outerAxial+1/2)*Real.cos x+Real.sin x/2
def axisCharge : ℝ := t 1*(outerAxial+1/2)-P 1/2
def Omega (x : ℝ) : ℝ := 1-axisCharge*(1-Real.cos x/axisProjection x)
def Omega1 (x : ℝ) : ℝ := -axisCharge/(2*(axisProjection x)^2)
def IsEvent (s : ℝ) : Prop := s∈Ioo (9/100:ℝ) (134/1250) ∧ Omega s=0

theorem axisCharge_positive : 0<axisCharge := by
  norm_num [axisCharge,t,P]
  linarith [ShortOuterZero.fine_axial_bounds.1]

theorem projection_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    0<targetProjection B x ∧ Real.cos x<targetProjection B x := by
  have hh := SecondWord.SameZero.v_positive hB hx
  have he : targetProjection B x-Real.cos x=angleSpeed B x := by
    dsimp [targetProjection,targetU,targetV,angleSpeed,SecondWord.SameZero.v]
    ring
  have hc : 0<Real.cos x := by linarith [(positive_trig hx).1]
  exact ⟨by linarith,by linarith⟩

theorem axisProjection_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<axisProjection x := by
  have hh := (projection_positive zero_mem hx).1
  have he : targetProjection 0 x=axisProjection x := by
    simp only [targetProjection,targetU,targetV,axisProjection,SameContact.arc_zero]
    ring
  rwa [he] at hh

theorem axisProjection_hasDerivAt (x : ℝ) :
    HasDerivAt axisProjection (-(outerAxial+1/2)*Real.sin x+Real.cos x/2) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (outerAxial+1/2)).fun_add
    ((Real.hasDerivAt_sin x).div_const 2)
  exact h.congr_deriv (by ring)

theorem Omega_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    HasDerivAt Omega (Omega1 x) x := by
  have hp := axisProjection_positive hx
  have key : -Real.sin x*axisProjection x-
      Real.cos x*(-(outerAxial+1/2)*Real.sin x+Real.cos x/2)=-1/2 := by
    simp only [axisProjection]
    linear_combination (-1/2:ℝ)*Real.sin_sq_add_cos_sq x
  have h := ((((Real.hasDerivAt_cos x).div (axisProjection_hasDerivAt x) hp.ne').const_sub
    1).const_mul axisCharge).const_sub 1
  refine h.congr_deriv ?_
  rw [key]
  simp only [Omega1]
  ring

theorem Omega_strictAnti : StrictAntiOn Omega (Icc (0:ℝ) (7/10)) := by
  have hint : interior (Icc (0:ℝ) (7/10)) = Ioo 0 (7/10) := interior_Icc
  have hm : StrictMonoOn (fun x => -Omega x) (Icc (0:ℝ) (7/10)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 (7/10)) (f' := fun x => -Omega1 x)
    · exact fun x hx => (Omega_hasDerivAt hx).neg.continuousAt.continuousWithinAt
    · intro x hx
      rw [hint] at hx ⊢
      exact (Omega_hasDerivAt (Ioo_subset_Icc_self hx)).neg.hasDerivWithinAt
    · intro x hx
      rw [hint] at hx
      have hp := axisProjection_positive (Ioo_subset_Icc_self hx)
      have hh := div_pos axisCharge_positive
        (mul_pos (by norm_num : (0:ℝ)<2) (pow_pos hp 2))
      simpa only [Omega1,neg_div,neg_neg] using hh
  intro x hx y hy hxy
  have hh := hm hx hy hxy
  simp only at hh
  linarith

def axisProjectionBox (x : ℝ) (hx : 0≤x) : Interval (axisProjection x) := by
  convert ((axial.add (Interval.point (1/2))).mul (cosine hx)).add
    ((sine hx).div (Interval.point 2) (by norm_num [Interval.point])) using 1
  rfl
def axisChargeBox : Interval axisCharge := by
  convert ((Interval.point (t 1)).mul (axial.add (Interval.point (1/2)))).sub
    (Interval.point (P 1/2)) using 1
  rfl
private theorem r86_mpr_lo {a b : ℝ} (e : a=b) (h : Interval a=Interval b) (X : Interval b) :
    (h.mpr X).lo=X.lo := by
  subst e
  rfl
private theorem r86_mpr_hi {a b : ℝ} (e : a=b) (h : Interval a=Interval b) (X : Interval b) :
    (h.mpr X).hi=X.hi := by
  subst e
  rfl
private theorem r86_axisProjectionBox_lo (x : ℝ) (hx : 0≤x) : (axisProjectionBox x hx).lo=
    (((axial.add (Interval.point (1/2))).mul (cosine hx)).add
      ((sine hx).div (Interval.point 2) (by norm_num [Interval.point]))).lo :=
  r86_mpr_lo rfl _ _
private theorem r86_axisProjectionBox_hi (x : ℝ) (hx : 0≤x) : (axisProjectionBox x hx).hi=
    (((axial.add (Interval.point (1/2))).mul (cosine hx)).add
      ((sine hx).div (Interval.point 2) (by norm_num [Interval.point]))).hi :=
  r86_mpr_hi rfl _ _
private theorem r86_axisChargeBox_lo : axisChargeBox.lo=
    (((Interval.point (t 1)).mul (axial.add (Interval.point (1/2)))).sub
      (Interval.point (P 1/2))).lo :=
  r86_mpr_lo rfl _ _
private theorem r86_axisChargeBox_hi : axisChargeBox.hi=
    (((Interval.point (t 1)).mul (axial.add (Interval.point (1/2)))).sub
      (Interval.point (P 1/2))).hi :=
  r86_mpr_hi rfl _ _

def OmegaBox (x : ℝ) (hx : 0≤x) (hD : 0<(axisProjectionBox x hx).lo) : Interval (Omega x) :=
  (Interval.point 1).sub (axisChargeBox.mul
    ((Interval.point 1).sub ((cosine hx).div (axisProjectionBox x hx) hD)))

theorem endpoint_signs : (49/25000:ℝ)<Omega (9/100) ∧ Omega (134/1250)< -(131/50000:ℝ) := by
  have hD0 : 0<(axisProjectionBox (9/100) (by norm_num)).lo := by
    rw [r86_axisProjectionBox_lo]
    mixed_fixed
  have hD1 : 0<(axisProjectionBox (134/1250) (by norm_num)).lo := by
    rw [r86_axisProjectionBox_lo]
    mixed_fixed
  have h0 : (49/25000:ℝ)<(OmegaBox (9/100) (by norm_num) hD0).lo := by
    simp only [OmegaBox,Interval.point,Interval.sub,Interval.mul,Interval.div,Interval.inv,
      r86_axisProjectionBox_lo,r86_axisProjectionBox_hi,r86_axisChargeBox_lo,
      r86_axisChargeBox_hi,t,P]
    mixed_fixed
  have h1 : (OmegaBox (134/1250) (by norm_num) hD1).hi < -(131/50000:ℝ) := by
    simp only [OmegaBox,Interval.point,Interval.sub,Interval.mul,Interval.div,Interval.inv,
      r86_axisProjectionBox_lo,r86_axisProjectionBox_hi,r86_axisChargeBox_lo,
      r86_axisChargeBox_hi,t,P]
    mixed_fixed
  exact ⟨h0.trans_le (OmegaBox (9/100) (by norm_num) hD0).mem.1,
    (OmegaBox (134/1250) (by norm_num) hD1).mem.2.trans_lt h1⟩

theorem exists_event : ∃s,IsEvent s := by
  have hc : ContinuousOn (fun x => -Omega x) (Icc (9/100:ℝ) (134/1250)) := by
    intro x hx
    exact (Omega_hasDerivAt (show x∈Icc 0 (7/10) from
      ⟨by linarith [hx.1],by linarith [hx.2]⟩)).neg.continuousAt.continuousWithinAt
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc (by norm_num : (9/100:ℝ)≤134/1250) hc
    (show (0:ℝ)∈Icc (-Omega (9/100)) (-Omega (134/1250)) from
      ⟨by linarith [endpoint_signs.1],by linarith [endpoint_signs.2]⟩)
  have he : Omega s=0 := by linarith
  refine ⟨s,⟨?_,?_⟩,he⟩
  · apply lt_of_le_of_ne hs.1
    intro h
    rw [←h] at he
    linarith [endpoint_signs.1]
  · apply lt_of_le_of_ne hs.2
    intro h
    rw [h] at he
    linarith [endpoint_signs.2]

theorem positive_before {s x : ℝ} (hs : IsEvent s) (hx : 0≤x) (hxs : x<s) : 0<Omega x := by
  have hh := Omega_strictAnti
    (show x∈Icc 0 (7/10) from ⟨hx,by linarith [hs.1.2]⟩)
    (show s∈Icc 0 (7/10) from ⟨by linarith [hs.1.1],by linarith [hs.1.2]⟩) hxs
  rw [hs.2] at hh
  exact hh

theorem projection_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun D => targetProjection D x) (Real.sin x-Real.cos x*ratio B) B := by
  have h := (((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).add_const (1/2)).mul_const
    (Real.cos x)).fun_add (((hasDerivAt_id' B).add_const (1/2)).mul_const (Real.sin x))
  exact h.congr_deriv (by ring)

theorem projection_le_axis {B e x : ℝ} (he : Upper.IsEvent e)
    (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 e) : targetProjection B x≤axisProjection x := by
  have hm : AntitoneOn (fun D => targetProjection D x) (Icc 0 outerDiagonal) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun D hD => (projection_target_hasDerivAt hD x).continuousAt.continuousWithinAt)
      (fun D hD => projection_target_hasDerivAt (Ioo_subset_Icc_self hD) x)
    intro D hD
    have hr := (target_ratio (Ioo_subset_Icc_self hD)).1
    have hc := early_cos he hx
    have hs := (axial_bounds he hx).2.2.2.2.2.2.2
    have hp := mul_le_mul hc.le (rho_bounds.1.le.trans hr)
      (by norm_num) (by linarith [hc] : 0≤Real.cos x)
    linarith
  have hh := hm zero_mem hB hB.1
  have he : targetProjection 0 x=axisProjection x := by
    simp only [targetProjection,targetU,targetV,axisProjection,SameContact.arc_zero]
    ring
  simp only at hh
  rwa [he] at hh

theorem targetCharge_bounds {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    0<targetCharge B ∧ targetCharge B≤axisCharge := by
  have hs := SameContact.arc_state hB
  have hb := outer_bounds hs
  have hU : 0<targetU B := by dsimp [targetU]; linarith [(target_root_bounds hB).1]
  have hUV : targetV B≤targetU B := by dsimp [targetV,targetU]; linarith [hs.2.1]
  dsimp [targetCharge,axisCharge,targetU,targetV] at *
  norm_num [P,t]
  constructor <;> nlinarith [hb.2.1,hB.1]

theorem stationary_identity {B x : ℝ} (hd : Domain B x) (hf : first 1 B x=0) :
    angleFirst 1 B x=1-targetCharge B*(1-Real.cos x/targetProjection B x) := by
  have hU : 0<targetU B := by dsimp [targetU]; linarith [(target_root_bounds hd.1).1]
  have hD := (projection_positive hd.1 hd.2.1).1
  have hL : sourceD 1 (contact B x)*targetProjection B x=targetCharge B := by
    dsimp [first,stateSpeed,SecondWord.SameZero.k,ratio] at hf
    change sourceD 1 (contact B x)*(Real.cos x+targetV B/targetU B*Real.sin x)+
      P 1*(targetV B/targetU B)-t 1=0 at hf
    field_simp [hU.ne'] at hf
    dsimp [targetProjection,targetCharge]
    nlinarith
  have hs : angleSpeed B x=targetProjection B x-Real.cos x := by
    dsimp [angleSpeed,SecondWord.SameZero.v,targetProjection,targetU,targetV]
    ring
  rw [angleFirst,hs]
  calc
    1-sourceD 1 (contact B x)*(targetProjection B x-Real.cos x)=
      1-(sourceD 1 (contact B x)*targetProjection B x)*(1-Real.cos x/targetProjection B x) := by
        field_simp [hD.ne']
    _ = _ := by rw [hL]

theorem stationary_angle_lower {B e x : ℝ} (he : Upper.IsEvent e)
    (hd : Domain B x) (hx : x≤e) (hf : first 1 B x=0) : Omega x≤angleFirst 1 B x := by
  have hD := projection_positive hd.1 hd.2.1
  have hA := axisProjection_positive hd.2.1
  have hDA := projection_le_axis he hd.1 ⟨hd.2.1.1,hx⟩
  have hcharge := targetCharge_bounds hd.1
  have hcos : 0<Real.cos x := by linarith [(positive_trig hd.2.1).1]
  have hfactor : 0≤1-Real.cos x/targetProjection B x := by
    have hh := (div_lt_one hD.1).2 hD.2
    linarith
  have hfactor' : 1-Real.cos x/targetProjection B x≤1-Real.cos x/axisProjection x := by
    have hh := div_le_div_of_nonneg_left hcos.le hD.1 hDA
    linarith
  have hp := mul_le_mul hcharge.2 hfactor' hfactor axisCharge_positive.le
  rw [stationary_identity hd hf]
  dsimp [Omega]
  linarith

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper.Stationary
end
end
end

section
/-!
## The complete positive halves of the three same-sign primary owners

The two cases are the signs of the actual initial angle derivative.
After an active contact reaches the source diagonal, its original
target slack decreases to contact or to the axial endpoint. The axial
continuation increases with slope one.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Positive
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)

theorem active_lower (r : Row) {B x : ℝ} (hd : Domain B x) :
    (44901/50000:ℝ)<cost r B x := by
  have hdom : ∀y∈Icc 0 x,Domain B y := fun y hy => physical_before hd hy
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ := (19/100:ℝ)) (fun y hy => cost_hasDerivAt r (hdom y hy))
    (fun y hy => first_hasDerivAt r (hdom y hy))
    (fun y hy => (curvature r (hdom y hy)).le)
    (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hd.2.1.1⟩)
    (show x∈Icc 0 x from ⟨hd.2.1.1,le_rfl⟩)
  rw [initial_cost,initial_first] at ht
  have hB := (active_ranges hd).1
  by_cases he : 0≤ initialAngle r B
  · have hp := mul_nonneg he hd.2.1.1
    have hvalue := aligned_lower r hB
    nlinarith [sq_nonneg x]
  · have hnegative := lt_of_not_ge he
    have hsmall := initialAngle_negative_location r hB hnegative
    have hvalue := aligned_initial_lower r ⟨hB.1,hsmall.le⟩
    have hderiv := initialAngle_lower r hB
    have hprod := mul_nonneg (show 0≤ initialAngle r B+1/50 by linarith)
      (show 0≤1/50-initialAngle r B by linarith)
    have hsquare := sq_nonneg ((19/100)*x+initialAngle r B)
    nlinarith

lemma physical_state_cost (r : Row) {a b A B : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) :
    source r a+target r B=p r*a-q r*b-P r*A+t r*B := by
  rw [source,target,(SameContact.actual_arc hs).2,(SameContact.actual_arc ht).1]
  ring

/-- The complete original weak primary inequality, on the whole positive
angle half. The final target motion includes both of its closed endpoints. -/
theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x+B*Real.cos x) :
    (44901/50000:ℝ)<Real.pi/2+x+c r+p r*a-q r*b-P r*A+t r*B := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have ha : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hd : outerDiagonal∈Icc outerDiagonal outerAxial := ⟨le_rfl,SameContact.diagonal_le_axial⟩
  have hzero : (0:ℝ)∈Icc 0 outerDiagonal := ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hcontact : contact B x≤a := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2+x+c r+source r a+target r B=
      Real.pi/2+x+c r+p r*a-q r*b-P r*A+t r*B := by
    have hh := physical_state_cost r hs ht
    linarith
  rw [←hcost]
  by_cases hactive : outerDiagonal≤contact B x
  · have hdom : Domain B x := ⟨hB,hx,hactive⟩
    have hmono := source_monotone r (primary_mem hdom) ha hcontact
    have hh := active_lower r hdom
    dsimp [cost] at hh
    linarith
  · have hsource := source_monotone r hd ha ha.1
    by_cases haxial : outerDiagonal≤contact 0 x
    · have hc : Continuous (fun D : ℝ => -contact D x) := by dsimp [contact,arc]; fun_prop
      obtain ⟨D,hD,hDe⟩ := intermediate_value_Icc hB.1 hc.continuousOn
        (show -outerDiagonal∈Icc (-contact 0 x) (-contact B x) from
          ⟨by linarith,by linarith⟩)
      have he : contact D x=outerDiagonal := by linarith
      have hDouter : D∈Icc 0 outerDiagonal := ⟨hD.1,hD.2.trans hB.2⟩
      have htarget := target_monotone r hDouter hB hD.2
      have hh := active_lower r (show Domain D x from ⟨hDouter,hx,he.ge⟩)
      dsimp [cost] at hh
      rw [he] at hh
      linarith
    · obtain ⟨e,he,heq⟩ := exists_axial_event
      have heDom : e∈Icc 0 (7/10) := ⟨by linarith [he.1],by linarith [he.2]⟩
      have hex : e≤x := by
        by_contra! hbad
        have hh := axial_strictAnti hx heDom hbad
        rw [heq] at hh
        linarith
      have htarget := target_monotone r hzero hB hB.1
      have hh := active_lower r (show Domain 0 e from ⟨hzero,heDom,heq.ge⟩)
      dsimp [cost] at hh
      rw [heq] at hh
      linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Positive
end
end
end

section
/-!
## The complete negative halves of the same-sign primary owners

The original circle identity gives a positive angular derivative at
every physical active contact. Decreasing the angle reaches alignment
or the complete source-diagonal curve. Target slack decreases until
that original contact is attained.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Negative
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)

def contact (B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x+(arc B+1/2)*Real.sin x
def speed (B x : ℝ) : ℝ :=
  (arc B+1/2)*Real.cos x+(B-1/2)*Real.sin x
def Domain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ contact B x∈Icc outerDiagonal outerAxial
def cost (r : Row) (B x : ℝ) : ℝ :=
  Real.pi/2-x+c r+source r (contact B x)+target r B
def first (r : Row) (B x : ℝ) : ℝ := -1+sourceD r (contact B x)*speed B x

lemma contact_hasDerivAt (B x : ℝ) : HasDerivAt (contact B) (speed B x) x := by
  convert (((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (arc B+1/2)) using 1
  · funext y; simp only [contact,Pi.add_apply]
  · simp only [speed]; ring

lemma speed_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    0<speed B x := by
  have hA := (outer_bounds (SameContact.arc_state hB)).1
  have ht := positive_trig hx
  have hp := mul_le_mul
    (show (1399/1000:ℝ)≤arc B+1/2 by linarith [ShortMixedZero.fine_diagonal_bounds.1])
    (show (191/250:ℝ)≤Real.cos x by linarith [ht.1]) (by norm_num)
    (by linarith [outer_endpoint_bounds.2.2.1] : 0≤arc B+1/2)
  have hs := mul_le_mul_of_nonneg_right (show -(1/2:ℝ)≤B-1/2 by linarith [hB.1]) ht.2.2.1
  dsimp [speed]
  nlinarith [ht.2.2.2.1]

lemma contact_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (contact B) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
  (fun x _ => (contact_hasDerivAt B x).continuousAt.continuousWithinAt)
  (fun x _ => contact_hasDerivAt B x)
  (fun _ hx => (speed_positive hB (Ioo_subset_Icc_self hx)).le)

lemma contact_zero (B : ℝ) : contact B 0=1-B := by norm_num [contact]; ring

lemma speed_circle {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (speed B x)^2=Q0-2*B-(contact B x-1/2)^2 := by
  have hc := SameContact.arc_circle (SameContact.outer_domain hB)
  dsimp [speed,contact]
  linear_combination hc+((arc B+1/2)^2+(B-1/2)^2)*(Real.sin_sq_add_cos_sq x)

lemma first_positive (r : Row) {B x : ℝ} (hd : Domain B x) : 0<first r B x := by
  have hspeed := speed_positive hd.1 hd.2.1
  have hcircle := speed_circle (x := x) hd.1
  have hB : B<(9/10:ℝ) := hd.1.2.trans_lt outer_endpoint_bounds.2.2.2
  have ha : 0≤contact B x-1/2 ∧ contact B x-1/2<(183/200:ℝ) :=
    ⟨by linarith [hd.2.2.1,outer_endpoint_bounds.2.2.1],
      by linarith [hd.2.2.2,outer_endpoint_bounds.2.1]⟩
  have hsquare := pow_le_pow_left₀ ha.1 ha.2.le 2
  have hreserve : (1:ℝ)<(94766/100000)*speed B x := by
    norm_num [Q0] at hcircle
    nlinarith
  have hL := mul_le_mul_of_nonneg_right (sourceD_lower r hd.2.2) hspeed.le
  dsimp [first]
  linarith

lemma cost_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (cost r B) (first r B x) x := by
  convert ((((hasDerivAt_id x).neg).const_add (Real.pi/2+c r)).add
    ((source_hasDerivAt r hd.2.2).comp x (contact_hasDerivAt B x))).add_const
      (target r B) using 1
  · funext y; simp only [cost,Pi.add_apply,Pi.neg_apply,id_eq,Function.comp_apply]; ring
  · simp only [first]

lemma physical_between {B x y z : ℝ} (hd : Domain B x)
    (hy : y∈Icc 0 x) (hcontact : outerDiagonal≤contact B y) (hz : z∈Icc y x) : Domain B z := by
  have hy' : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hd.2.1.2⟩
  have hz' : z∈Icc 0 (7/10) := ⟨hy.1.trans hz.1,hz.2.trans hd.2.1.2⟩
  exact ⟨hd.1,hz',hcontact.trans (contact_monotone hd.1 hy' hz' hz.1),
    (contact_monotone hd.1 hz' hd.2.1 hz.2).trans hd.2.2.2⟩

lemma cost_monotone_between (r : Row) {B x y : ℝ} (hd : Domain B x)
    (hy : y∈Icc 0 x) (hcontact : outerDiagonal≤contact B y) :
    MonotoneOn (cost r B) (Icc y x) := monoOn_of_hasDeriv_nonneg
  (fun _ hz => (cost_hasDerivAt r (physical_between hd hy hcontact hz)).continuousAt.continuousWithinAt)
  (fun _ hz => cost_hasDerivAt r (physical_between hd hy hcontact (Ioo_subset_Icc_self hz)))
  (fun _ hz => (first_positive r (physical_between hd hy hcontact (Ioo_subset_Icc_self hz))).le)

lemma initial_cost (r : Row) (B : ℝ) : cost r B 0=aligned r B := by
  rw [cost,contact_zero]
  simp [aligned]

lemma diagonal_cost (r : Row) {B x : ℝ} (hB : B∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) (he : contact B x=outerDiagonal) :
    (8981/10000:ℝ)<cost r B x := by
  have hh := Diagonal.original_contact r (SameContact.arc_state hB) hx
    (by simpa [contact] using he)
  dsimp [cost,source,target]
  rw [he,SameContact.arc_diagonal]
  nlinarith only [hh]

theorem active_lower (r : Row) {B x : ℝ} (hd : Domain B x) :
    (8981/10000:ℝ)<cost r B x := by
  by_cases hzero : outerDiagonal≤contact B 0
  · have hB : B∈Icc 0 b0 := ⟨hd.1.1,by rw [contact_zero] at hzero; dsimp [b0]; linarith⟩
    have hh := aligned_lower r hB
    have hm := cost_monotone_between r hd (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hd.2.1.1⟩) hzero
      (show (0:ℝ)∈Icc 0 x from ⟨le_rfl,hd.2.1.1⟩)
      (show x∈Icc 0 x from ⟨hd.2.1.1,le_rfl⟩) hd.2.1.1
    rw [initial_cost] at hm
    exact hh.trans_le hm
  · have hc : Continuous (contact B) := by
      have he : contact B = fun x => 1/2+(1/2-B)*Real.cos x+(arc B+1/2)*Real.sin x := rfl
      rw [he]; fun_prop
    obtain ⟨y,hy,he⟩ := intermediate_value_Icc hd.2.1.1 hc.continuousOn
      (show outerDiagonal∈Icc (contact B 0) (contact B x) from ⟨by linarith,hd.2.2.1⟩)
    have hy' : y∈Icc 0 (7/10) := ⟨hy.1,hy.2.trans hd.2.1.2⟩
    have hh := diagonal_cost r hd.1 hy' he
    have hm := cost_monotone_between r hd hy he.ge
      (show y∈Icc y x from ⟨le_rfl,hy.2⟩)
      (show x∈Icc y x from ⟨hy.2,le_rfl⟩) hy.2
    exact hh.trans_le hm

theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤a-A*Real.sin x+B*Real.cos x) :
    (8981/10000:ℝ)<Real.pi/2-x+c r+p r*a-q r*b-P r*A+t r*B := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have ha : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hd : outerDiagonal∈Icc outerDiagonal outerAxial := ⟨le_rfl,SameContact.diagonal_le_axial⟩
  have hzero : (0:ℝ)∈Icc 0 outerDiagonal := ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hcontact : contact B x≤a := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2-x+c r+source r a+target r B=
      Real.pi/2-x+c r+p r*a-q r*b-P r*A+t r*B := by
    have hh := Positive.physical_state_cost r hs ht
    linarith
  rw [←hcost]
  by_cases hactive : outerDiagonal≤contact B x
  · have hdom : Domain B x := ⟨hB,hx,hactive,hcontact.trans ha.2⟩
    have hmono := source_monotone r hdom.2.2 ha hcontact
    have hh := active_lower r hdom
    dsimp [cost] at hh
    linarith
  · have hsource := source_monotone r hd ha ha.1
    have haxial := contact_monotone hzero (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1
    rw [contact_zero] at haxial
    have hc : Continuous (fun D : ℝ => -contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,hDe⟩ := intermediate_value_Icc hB.1 hc.continuousOn
      (show -outerDiagonal∈Icc (-contact 0 x) (-contact B x) from
        ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith⟩)
    have he : contact D x=outerDiagonal := by linarith
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hD.1,hD.2.trans hB.2⟩
    have htarget := target_monotone r hDouter hB hD.2
    have hh := diagonal_cost r hDouter hx he
    dsimp [cost] at hh
    rw [he] at hh
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Negative
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Primary
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem normalized (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) φ) :
    (449/500:ℝ)<φ+c r+p r*a-q r*b-P r*A+t r*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hh := RoleFour.secondary_margin high hx hm
  cases high
  · have hh' : (1+Real.cos x+Real.sin x)/2≤a-A*Real.sin x+B*Real.cos x := by
      simp only [Unit.direction,Bool.false_eq_true,↓reduceIte] at hh
      linarith
    have hv := Negative.original r hs ht hx hh'
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hh' : (1+Real.cos x+Real.sin x)/2≤a+A*Real.sin x+B*Real.cos x := by
      simp only [Unit.direction,↓reduceIte] at hh
      linarith
    have hv := Positive.original r hs ht hx hh'
    simp only [Unit.angle,Unit.direction,↓reduceIte]
    linarith

def OriginalOwner (i : Vertex) (σ : Bool) (j : Fin 4) : Prop :=
  ((i=2 ∨ i=4) ∧ σ=false ∧ j=3) ∨ (i=6 ∧ σ=true ∧ j=1)

theorem original_owner (i : Vertex) (σ : Bool) (j : Fin 4) (hrole : OriginalOwner i σ j)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) .outer σ A B := by
  rcases hrole with ⟨hi,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · rcases hi with rfl | rfl
    · have hh := normalized 0 hs ht hφ (by simpa [WordProblems.sign] using hm)
      norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
        WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
      linarith
    · have hh := normalized 1 hs ht hφ (by simpa [WordProblems.sign] using hm)
      norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
        WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
      linarith
  · have hh := normalized 2 ht hs hφ (by simpa [WordProblems.sign,Eight.forwardMargin,
      add_comm,add_left_comm,add_assoc] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
    linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (_hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (hrole : OriginalOwner i (positiveOf C i) j)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hm := original_margin C F hgap i j howner
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hh := original_owner i (positiveOf C i) j hrole
    hsource htarget hφ (by simpa [←hsg] using hm)
  have hh' : (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by simpa only [wrongMarker,hs,ht,←hsg] using hh
  exact (ShortWord.Zero.threshold_le i).trans_lt hh'

end SquaresInCircles.Eight.ShortOuterOne.Same.Primary
end
end
end
