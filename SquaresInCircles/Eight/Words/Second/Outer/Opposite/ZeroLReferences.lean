module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroPositiveSpeeds
public import SquaresInCircles.Eight.Words.Second.WordData

/-!
# Eight squares: the L references of the symmetric whole-angle proof

Each declaration below is one exact rational comparison for the label L or its derivatives at a
fixed reference point. The circle radical is carried by the reference enclosures
(`Reference.valueAt`, `Reference.firstAt`, `Reference.secondAt`).
-/

section
/-!
## The symmetric aligned quartic

The two
actual circle radicals determine their sum; their difference eliminates
the transverse coordinate.  The resulting quartic is bounded on the
single rational interval [3.28,3.42] by its strong tangent at 3.3974.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.AlignedL
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def R : ℝ := Q0-1
def rad (x : ℝ) : ℝ := Real.sqrt (Q0-(1+x)^2)
def radSum (x : ℝ) : ℝ := rad x+rad (-x)
def radFirst (x : ℝ) : ℝ := -(1+x)/rad x
def radSecond (x : ℝ) : ℝ := -Q0/(rad x)^3
def quartic (u : ℝ) : ℝ :=
  161761/12500+(572020119/31250000)*u-(42944417/7812500)*u^2-
    (284163/100000)*u^3+(37437/50000)*u^4
def quarticFirst (u : ℝ) : ℝ :=
  572020119/31250000-2*(42944417/7812500)*u-
    3*(284163/100000)*u^2+4*(37437/50000)*u^3
def quarticSecond (u : ℝ) : ℝ :=
  -2*(42944417/7812500)-6*(284163/100000)*u+12*(37437/50000)*u^2

lemma radical_data {x : ℝ} (hx : x∈Icc (-(2/5):ℝ) (2/5)) :
    0<rad x ∧ (rad x)^2=Q0-(1+x)^2 := by
  have hp : 0<Q0-(1+x)^2 := by norm_num [Q0]; nlinarith [hx.1,hx.2]
  exact ⟨Real.sqrt_pos.mpr hp,Real.sq_sqrt hp.le⟩
lemma rad_hasDerivAt {x : ℝ} (hx : x∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt rad (radFirst x) x := by
  have hp := (radical_data hx).1
  have hn : Q0-(1+x)^2≠0 := by nlinarith [(radical_data hx).2]
  refine (((((hasDerivAt_id' x).const_add 1).pow 2).const_sub Q0).sqrt hn).congr_deriv ?_
  change _=-(1+x)/rad x
  have hr : Real.sqrt (Q0-(1+x)^2)=rad x := rfl
  simp only [Pi.pow_apply]
  rw [hr]
  field_simp
  ring
lemma radFirst_hasDerivAt {x : ℝ} (hx : x∈Icc (-(2/5):ℝ) (2/5)) :
    HasDerivAt radFirst (radSecond x) x := by
  have hp := (radical_data hx).1
  convert ((((hasDerivAt_id x).const_add 1).neg).div (rad_hasDerivAt hx) hp.ne') using 1
  · rfl
  · dsimp [radFirst,radSecond]
    field_simp [hp.ne']
    nlinarith [(radical_data hx).2]

lemma sum_bounds {x : ℝ} (hx : x∈Icc (-(2/5):ℝ) (2/5)) :
    (82/25:ℝ)<radSum x ∧ radSum x<171/50 := by
  have hneg {t : ℝ} (ht : t∈Icc (-(2/5):ℝ) (2/5)) : -t∈Icc (-(2/5):ℝ) (2/5) := by
    constructor <;> linarith [ht.1,ht.2]
  have hc : ConcaveOn ℝ (Icc (-(2/5):ℝ) (2/5)) radSum :=
    concave_of_deriv2 (f' := fun t => radFirst t-radFirst (-t))
      (f'' := fun t => radSecond t+radSecond (-t))
      (fun t ht => ((rad_hasDerivAt ht).add ((rad_hasDerivAt (hneg ht)).comp t
          (hasDerivAt_id' t).neg)).congr_deriv (by ring))
      (fun t ht => ((radFirst_hasDerivAt ht).sub ((radFirst_hasDerivAt (hneg ht)).comp t
          (hasDerivAt_id' t).neg)).congr_deriv (by ring))
      (fun t ht => by
        dsimp only [radSecond]
        have h1 := (radical_data ht).1
        have h2 := (radical_data (hneg ht)).1
        have hQ : 0<Q0 := by norm_num [Q0]
        exact add_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hQ.le) (by positivity))
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hQ.le) (by positivity)))
  have hp : (699/500:ℝ)<rad (2/5) := by
    have h := radical_data (show (2/5:ℝ)∈Icc (-(2/5)) (2/5) by norm_num)
    norm_num [Q0] at h
    nlinarith
  have hm : (377/200:ℝ)<rad (-(2/5)) := by
    have h := radical_data (show (-(2/5):ℝ)∈Icc (-(2/5)) (2/5) by norm_num)
    norm_num [Q0] at h
    nlinarith
  have hend : (82/25:ℝ)<radSum (2/5) := by dsimp [radSum]; linarith
  have heven (t : ℝ) : radSum (-t)=radSum t := by simp [radSum,add_comm]
  have hl := concave_gt_of_endpoints hc hx (by rw [heven]; exact hend) hend
  have hv := hc.2 hx (hneg hx) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  have hzero : radSum 0<(171/50:ℝ) := by
    have h := radical_data (show (0:ℝ)∈Icc (-(2/5)) (2/5) by norm_num)
    norm_num [Q0] at h
    norm_num [radSum]
    nlinarith
  have hmid : (1/2:ℝ)•x+(1/2:ℝ)•(-x)=0 := by simp only [smul_eq_mul]; ring
  rw [hmid,heven,smul_eq_mul] at hv
  exact ⟨hl,by linarith⟩

lemma quartic_hasDerivAt (u : ℝ) : HasDerivAt quartic (quarticFirst u) u := by
  have h := ((((hasDerivAt_const u (161761/12500:ℝ)).add
    ((hasDerivAt_id' u).const_mul (572020119/31250000:ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (42944417/7812500:ℝ))).sub
        ((hasDerivAt_pow 3 u).const_mul (284163/100000:ℝ))).add
          ((hasDerivAt_pow 4 u).const_mul (37437/50000:ℝ))
  exact h.congr_deriv (by simp only [quarticFirst]; push_cast; ring)
lemma quarticFirst_hasDerivAt (u : ℝ) : HasDerivAt quarticFirst (quarticSecond u) u := by
  have h := (((hasDerivAt_const u (572020119/31250000:ℝ)).sub
    ((hasDerivAt_id' u).const_mul (2*(42944417/7812500):ℝ))).sub
      ((hasDerivAt_pow 2 u).const_mul (3*(284163/100000):ℝ))).add
        ((hasDerivAt_pow 3 u).const_mul (4*(37437/50000):ℝ))
  exact h.congr_deriv (by simp only [quarticSecond]; push_cast; ring)
lemma quartic_curvature {u : ℝ} (hu : u∈Icc (82/25:ℝ) (171/50)) :
    (29:ℝ)<quarticSecond u := by
  have hx : 0≤u-82/25 := sub_nonneg.mpr hu.1
  dsimp [quarticSecond]
  nlinarith [sq_nonneg (u-82/25)]

lemma quartic_lower {u : ℝ} (hu : u∈Icc (82/25:ℝ) (171/50)) :
    (19/10000:ℝ)<quartic u := by
  have ht := curvature_tangent (f := quartic) (d := quarticFirst) (dd := quarticSecond)
    (κ := 29) hu (show (16987/5000:ℝ)∈Icc (82/25) (171/50) by norm_num)
    (fun t _ => quartic_hasDerivAt t) (fun t _ => quarticFirst_hasDerivAt t)
    (fun t ht => (quartic_curvature ht).le)
  have hv : (487/250000:ℝ)<quartic (16987/5000) := by norm_num [quartic]
  have hd : |quarticFirst (16987/5000)|<(3/2000:ℝ) := by norm_num [quarticFirst]
  have hs := sq_nonneg (29*(u-16987/5000)+quarticFirst (16987/5000))
  have hh := abs_lt.mp hd
  nlinarith

theorem original {b B : ℝ} (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal)
    (he : b+B=1) : (89777/100000:ℝ)<LLabel.outer b+LLabel.outer B := by
  obtain ⟨x,hxd⟩ : ∃ x : ℝ, x=b-1/2 := ⟨_,rfl⟩
  obtain ⟨z,hzd⟩ : ∃ z : ℝ, z=x^2 := ⟨_,rfl⟩
  obtain ⟨S,hSd⟩ : ∃ S : ℝ, S=U b+U B := ⟨_,rfl⟩
  have heB : B=1-b := by linarith
  have hx : x∈Icc (-(2/5):ℝ) (2/5) := by
    rw [hxd]; constructor <;> linarith [hb.2,hB.2,outer_endpoint_bounds.2.2.2]
  have hS : S=radSum x := by
    have e1 : U b=rad x := by
      simp only [U,arc,rad]
      rw [show (1:ℝ)+x=b+1/2 by rw [hxd]; ring]
      ring
    have e2 : U B=rad (-x) := by
      simp only [U,arc,rad]
      rw [show (1:ℝ)+-x=B+1/2 by rw [hxd]; linarith]
      ring
    rw [hSd,e1,e2]
    rfl
  have hSb := sum_bounds hx
  rw [←hS] at hSb
  have hSp : 0<S := by linarith [hSb.1]
  have hu := UW_circle (outer_domain hb)
  have hv := UW_circle (outer_domain hB)
  simp only [W] at hu hv
  have hdiff : (U b-U B)*S= -4*x := by
    rw [hSd,hxd]
    subst heB
    linear_combination hu-hv
  have hsum : S^2+(U b-U B)^2=4*(R-z) := by
    rw [hSd,hzd,hxd]
    simp only [R]
    subst heB
    linear_combination 2*hu+2*hv
  have hsquare : (U b-U B)^2*S^2=16*z := by
    rw [hzd]
    linear_combination ((U b-U B)*S-4*x)*hdiff
  have hz : z=S^2*(4*R-S^2)/(4*(S^2+4)) := by
    apply (eq_div_iff (by positivity : 4*(S^2+4)≠0)).2
    linear_combination S^2*hsum-hsquare
  have hxu : x*(U b-U B)= -4*z/S := by
    rw [eq_div_iff hSp.ne',hzd]
    linear_combination x*hdiff
  have hlabels : LLabel.outer b+LLabel.outer B-(17953/20000:ℝ)=
      161761/50000-(94721/100000)*S-(37437/12500)*z+(94721/12500)*z/S := by
    simp only [RoleLabel.outer,RoleLabel.eval,LLabel]
    have hab : arc b=U b-1/2 := by simp only [U]; ring
    have haB : arc B=U B-1/2 := by simp only [U]; ring
    rw [hab,haB]
    subst heB
    subst hSd hzd hxd
    linear_combination (-189442/100000:ℝ)*hxu
  have hidentity : LLabel.outer b+LLabel.outer B-(17953/20000:ℝ)=quartic S/(S^2+4) := by
    rw [hlabels,hz]
    simp only [quartic,R,Q0]
    field_simp
    ring
  have hp := quartic_lower ⟨hSb.1.le,hSb.2.le⟩
  have hden : S^2+4<(39241/2500:ℝ) := by nlinarith [hSb.2]
  have hreserve : (3/25000:ℝ)<quartic S/(S^2+4) := by
    apply (lt_div_iff₀ (by positivity : 0<S^2+4)).2
    linarith
  rw [←hidentity] at hreserve
  linarith

end SquaresInCircles.Eight.SecondWord.OppositeZero.AlignedL
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
open CommonQuarter CorePairGeometry Arithmetic
open Reference
open StationaryPrimitives (Interval)

private lemma r82_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r82_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl
private lemma r82_mp_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).lo = S.lo := by subst e; rfl
private lemma r82_mp_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval x) :
    (Eq.mp h S).hi = S.hi := by subst e; rfl

private lemma r82_rootAt_lo {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).lo =
    (OppositeThree.ReferenceAlgebra.rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2)
      (by linarith [hb.2]) (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).lo := by
  unfold rootAt
  rw [r82_mpr_lo, r82_mp_lo]
  all_goals simp [U,ShortOuterOne.SameContact.arc]
private lemma r82_rootAt_hi {b : ℝ} (hb : b∈Icc 0 (9/10)) : (rootAt b hb).hi =
    (OppositeThree.ReferenceAlgebra.rootThree (Interval.point (Q0-(b+1/2)^2)) (2-b/2)
      (by linarith [hb.2]) (by norm_num [Interval.point,Q0]; nlinarith [hb.1,hb.2])).hi := by
  unfold rootAt
  rw [r82_mpr_hi, r82_mp_hi]
  all_goals simp [U,ShortOuterOne.SameContact.arc]

private lemma r82_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r82_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r82_mpr_lo r82_coordinate_eq (congrArg _ r82_coordinate_eq) _
private lemma r82_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r82_mpr_hi r82_coordinate_eq (congrArg _ r82_coordinate_eq) _
private lemma r82_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r82_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (OppositeThree.ReferenceAlgebra.labelBox H Y X).lo =
      (((((Interval.point H.c).add ((Interval.point H.p).mul
        (OppositeThree.ReferenceAlgebra.coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((OppositeThree.ReferenceAlgebra.coordinate X).mul Y))).lo :=
  r82_mpr_lo (r82_label_eq H) (congrArg _ (r82_label_eq H)) _

private lemma r82_valueAt_lo (H : RoleLabel) (b : ℝ) (hb : b∈Icc 0 (9/10)) :
    (valueAt H b hb).lo =
      (((((Interval.point H.c).add ((Interval.point H.p).mul
        (OppositeThree.ReferenceAlgebra.coordinate (rootAt b hb)))).add
      ((Interval.point H.q).mul (Interval.point b))).add
        ((Interval.point H.r).mul (Interval.point b).square)).add
        ((Interval.point H.s).mul ((OppositeThree.ReferenceAlgebra.coordinate (rootAt b hb)).mul
          (Interval.point b)))).lo :=
  r82_labelBox_lo H _ _

attribute [local simp ↓] r82_rootAt_lo r82_rootAt_hi r82_coordinate_lo r82_coordinate_hi
  r82_valueAt_lo

private lemma first_lower {b l : ℝ} (hb : b∈Icc 0 (9/10))
    (h : l<(firstAt LLabel b hb).lo) : l<LLabel.d1 b :=
  h.trans_le (firstAt LLabel b hb).mem.1
private lemma first_upper {b u : ℝ} (hb : b∈Icc 0 (9/10))
    (h : (firstAt LLabel b hb).hi<u) : LLabel.d1 b<u :=
  (firstAt LLabel b hb).mem.2.trans_lt h
private lemma second_lower {b l : ℝ} (hb : b∈Icc 0 (9/10))
    (h : l<(secondAt LLabel b hb).lo) : l<LLabel.d2 b :=
  h.trans_le (secondAt LLabel b hb).mem.1
private lemma second_upper {b u : ℝ} (hb : b∈Icc 0 (9/10))
    (h : (secondAt LLabel b hb).hi<u) : LLabel.d2 b<u :=
  (secondAt LLabel b hb).mem.2.trans_lt h

lemma L_tenth_first : LLabel.d1 (1/10)<(51/50:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_85_first : LLabel.d1 (17/20)<(51/50:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_fifth_first : LLabel.d1 (1/5)<(17/20:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_76_first : LLabel.d1 (19/25)<(17/20:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_four_first : (649/1000:ℝ)<LLabel.d1 (2/5) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_six_first : (649/1000:ℝ)<LLabel.d1 (3/5) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_six_first_upper : LLabel.d1 (3/5)<(7/10:ℝ) :=
  first_upper (by norm_num) (by opposite_reference_arithmetic)

lemma L_six_second : (1/2:ℝ)<LLabel.d2 (3/5) :=
  second_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_56_first : (15817/25000:ℝ)<LLabel.d1 (14/25) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_56_second : (29/100:ℝ)<LLabel.d2 (14/25) :=
  second_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_66_first : (6933/10000:ℝ)<LLabel.d1 (33/50) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_66_second : (93/100:ℝ)<LLabel.d2 (33/50) :=
  second_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_67_first : (703/1000:ℝ)<LLabel.d1 (67/100) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_seven_first : (1473/2000:ℝ)<LLabel.d1 (7/10) :=
  first_lower (by norm_num) (by opposite_reference_arithmetic)

lemma L_seven_second : (6/5:ℝ)<LLabel.d2 (7/10) :=
  second_lower (by norm_num) (by opposite_reference_arithmetic)

def charge : ℝ := 400/391

lemma L_small_chord_reference :
    LLabel.outer 0+charge*(3/20)<LLabel.outer (3/20) := by
  have h := (valueAt LLabel (3/20) (by norm_num)).mem.1
  have hr : (793/20000:ℝ)+(400/391)*(3/20)<
      (valueAt LLabel (3/20) (by norm_num)).lo := by opposite_reference_arithmetic
  have h0 : LLabel.outer 0=793/20000 := by norm_num [RoleLabel.outer,RoleLabel.eval,LLabel]
  rw [h0]
  dsimp only [charge]
  linarith

lemma support_references :
    -(15957/100000:ℝ)<LLabel.outer (3/5)-charge*(3/5) ∧
    -(7977/50000:ℝ)<LLabel.outer (17/20)-charge*(17/20) ∧
    |LLabel.d1 (17/20)-charge|<(1/200:ℝ) := by
  have h1 := (valueAt LLabel (3/5) (by norm_num)).mem.1
  have h2 := (valueAt LLabel (17/20) (by norm_num)).mem.1
  have h3 := (firstAt LLabel (17/20) (by norm_num)).mem
  have r1 : -(15957/100000:ℝ)+(400/391)*(3/5)<
      (valueAt LLabel (3/5) (by norm_num)).lo := by opposite_reference_arithmetic
  have r2 : -(7977/50000:ℝ)+(400/391)*(17/20)<
      (valueAt LLabel (17/20) (by norm_num)).lo := by opposite_reference_arithmetic
  have r3 : (400/391)-(1/200:ℝ)<(firstAt LLabel (17/20) (by norm_num)).lo := by opposite_reference_arithmetic
  have r4 : (firstAt LLabel (17/20) (by norm_num)).hi<(400/391)+(1/200:ℝ) := by opposite_reference_arithmetic
  dsimp [charge]
  refine ⟨by linarith,by linarith,abs_lt.mpr ⟨?_,?_⟩⟩ <;> linarith [h3.1,h3.2]

end SquaresInCircles.Eight.SecondWord.OppositeZero.Symmetric
end
end
end
