module

public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuterNegativeSide

/-!
# Eight squares: the named references for the twelve negative-core endpoint curves

Eight references bound H-H'^2/1.3, and the other
four curves use their initial positive derivative. Every radical is
enclosed on its actual expression by positive rational square bounds.
The whole-interval curvature was proved before these substitutions.
-/

section
/-!
## The one polynomial curvature reserve for every core endpoint

The expansion is a single polynomial identity. Its odd
powers are bounded by absolute values and its remaining quadratic is
completed to a square on the whole height interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Curvature
open CommonQuarter Arithmetic

def K0 : ℝ := 112479/100000
def E (u : ℝ) : ℝ := Q0*(K0-(u-1)^2)-u*(u-1)*(Q0-u^2)
def E1 (u : ℝ) : ℝ := 4*u^3-3*u^2-4*Q0*u+3*Q0
def E2 (u : ℝ) : ℝ := 12*u^2-6*u-4*Q0
def E3 (u : ℝ) : ℝ := 24*u-6
def A (u : ℝ) : ℝ := (13/20)/(767/1000)+(253/1000)*(u-1)
def P (u : ℝ) : ℝ := E u^2-A u^2*(Q0-u^2)^3

theorem E_hasDerivAt (u : ℝ) : HasDerivAt E (E1 u) u := by
  have h := (((hasDerivAt_const u K0).sub (((hasDerivAt_id' u).sub_const 1).pow 2)).const_mul
    Q0).sub (((hasDerivAt_id' u).mul ((hasDerivAt_id' u).sub_const 1)).mul
      ((hasDerivAt_const u Q0).sub ((hasDerivAt_id' u).pow 2)))
  exact h.congr_deriv (by simp only [E1]; norm_num; ring)
theorem E1_hasDerivAt (u : ℝ) : HasDerivAt E1 (E2 u) u := by
  have h := (((((hasDerivAt_id' u).pow 3).const_mul 4).sub
    (((hasDerivAt_id' u).pow 2).const_mul 3)).sub
      ((hasDerivAt_id' u).const_mul (4*Q0))).add_const (3*Q0)
  exact h.congr_deriv (by simp only [E2]; norm_num; ring)
theorem E2_hasDerivAt (u : ℝ) : HasDerivAt E2 (E3 u) u := by
  have h := ((((hasDerivAt_id' u).pow 2).const_mul 12).sub
    ((hasDerivAt_id' u).const_mul 6)).sub_const (4*Q0)
  exact h.congr_deriv (by simp only [E3]; norm_num; ring)
theorem E1_negative {u : ℝ} (hu : HeightRange u) : E1 u< -(389/100:ℝ) := by
  have hc : ConcaveOn ℝ (Icc (33/25) (17/10)) (fun u => -E1 u) :=
    concave_of_deriv2 (fun u _ => (E1_hasDerivAt u).neg)
      (fun u _ => (E2_hasDerivAt u).neg)
      (fun u hu => by dsimp [E3]; linarith [hu.1])
  have h := concave_gt_of_endpoints hc hu
    (show (389/100:ℝ)< -E1 (33/25) by norm_num [E1,Q0])
    (show (389/100:ℝ)< -E1 (17/10) by norm_num [E1,Q0])
  linarith
theorem E_antitone : AntitoneOn E (Icc (33/25) (17/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (E_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => E_hasDerivAt u)
    (fun u hu => by linarith [E1_negative (Ioo_subset_Icc_self hu)])
theorem E_positive {u : ℝ} (hu : HeightRange u) : (253/200:ℝ)<E u := by
  have h := E_antitone hu (show (17/10:ℝ)∈Icc (33/25) (17/10) by norm_num) hu.2
  have he : (253/200:ℝ)<E (17/10) := by norm_num [E,K0,Q0]
  linarith
theorem A_positive {u : ℝ} (hu : HeightRange u) : 0<A u := by
  dsimp [A]
  linarith [hu.1]

def e0 : ℝ := 27/16+Q0*(K0-1)
def e1 : ℝ := 27/4-3*Q0
def e2 : ℝ := 9-2*Q0
def a0 : ℝ := (13/20)/(767/1000)+253/2000
def a1 : ℝ := 253/1000
def z0 : ℝ := Q0-9/4
def c0 : ℝ := z0^3
def c1 : ℝ := -9*z0^2
def c2 : ℝ := 27*z0-3*z0^2
def c3 : ℝ := 18*z0-27
def c4 : ℝ := 3*z0-27
def c5 : ℝ := -9
def c6 : ℝ := -1
def p0 : ℝ := e0^2-a0^2*c0
def p1 : ℝ := 2*e0*e1-(a0^2*c1+2*a0*a1*c0)
def p2 : ℝ := e1^2+2*e0*e2-(a0^2*c2+2*a0*a1*c1+a1^2*c0)
def p3 : ℝ := 10*e0+2*e1*e2-(a0^2*c3+2*a0*a1*c2+a1^2*c1)
def p4 : ℝ := 2*e0+10*e1+e2^2-(a0^2*c4+2*a0*a1*c3+a1^2*c2)
def p5 : ℝ := 2*e1+10*e2-(a0^2*c5+2*a0*a1*c4+a1^2*c3)
def p6 : ℝ := 2*e2+25-(a0^2*c6+2*a0*a1*c5+a1^2*c4)
def p7 : ℝ := 10-(2*a0*a1*c6+a1^2*c5)
def p8 : ℝ := 1-a1^2*c6

theorem expansion (t : ℝ) :
    P (3/2+t)=p0+p1*t+p2*t^2+p3*t^3+p4*t^4+p5*t^5+p6*t^6+p7*t^7+p8*t^8 := by
  dsimp [P,E,A,p0,p1,p2,p3,p4,p5,p6,p7,p8,e0,e1,e2,a0,a1,z0,c0,c1,c2,c3,c4,c5,c6]
  ring

theorem coefficients :
    (3523/10000:ℝ)<p0 ∧ |p1|≤3401/10000 ∧ 72993/10000<p2 ∧
      |p3|≤921/100 ∧ -(27193/1000:ℝ)<p4 ∧ |p5|≤4177/200 ∧
        0≤p6 ∧ |p7|≤11069/1000 ∧ 0≤p8 := by
  norm_num [p0,p1,p2,p3,p4,p5,p6,p7,p8,e0,e1,e2,a0,a1,z0,c0,c1,c2,c3,c4,c5,c6,Q0,K0]

theorem signed_power_lower {c B t : ℝ} (hc : |c|≤B) (n : ℕ) : -B*|t|^n≤c*t^n := by
  have hp := mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg t) n)
  have hneg := neg_abs_le (c*t^n)
  rw [abs_mul,abs_pow] at hneg
  linarith

theorem absolute_lower (t : ℝ) :
    (3523/10000:ℝ)-(3401/10000)*|t|+
      t^2*((72993/10000)-(921/100)*|t|-(27193/1000)*t^2-
        (4177/200)*|t|^3-(11069/1000)*|t|^5)<P (3/2+t) := by
  have hc := coefficients
  have h1 := signed_power_lower (t:=t) hc.2.1 1
  have h2 := mul_le_mul_of_nonneg_right hc.2.2.1.le (sq_nonneg t)
  have h3 := signed_power_lower (t:=t) hc.2.2.2.1 3
  have h4 := mul_le_mul_of_nonneg_right hc.2.2.2.2.1.le (by positivity : 0≤t^4)
  have h5 := signed_power_lower (t:=t) hc.2.2.2.2.2.1 5
  have h6 := mul_nonneg hc.2.2.2.2.2.2.1 (by positivity : 0≤t^6)
  have h7 := signed_power_lower (t:=t) hc.2.2.2.2.2.2.2.1 7
  have h8 := mul_nonneg hc.2.2.2.2.2.2.2.2 (by positivity : 0≤t^8)
  have ha2 : |t|^2=t^2 := sq_abs t
  have ha3 : |t|^3=t^2*|t| := by rw [pow_succ,ha2]
  have ha5 : |t|^5=t^2*|t|^3 := by rw [show 5=2+3 by rfl,pow_add,ha2]
  have ha7 : |t|^7=t^2*|t|^5 := by rw [show 7=2+5 by rfl,pow_add,ha2]
  rw [expansion]
  simp only [pow_one,ha3,ha5,ha7] at h1 h3 h5 h7 ⊢
  linarith [hc.1]

theorem brace_lower {t : ℝ} (ht : |t|≤1/5) :
    (419/100:ℝ)<(72993/10000)-(921/100)*|t|-(27193/1000)*t^2-
      (4177/200)*|t|^3-(11069/1000)*|t|^5 := by
  have ht2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
  have ht3 := pow_le_pow_left₀ (abs_nonneg t) ht 3
  have ht5 := pow_le_pow_left₀ (abs_nonneg t) ht 5
  rw [sq_abs] at ht2
  norm_num at ht2 ht3 ht5
  linarith

theorem P_positive {u : ℝ} (hu : HeightRange u) : (69/200:ℝ)<P u := by
  let t := u-3/2
  have ht : |t|≤1/5 := abs_le.mpr ⟨by dsimp [t]; linarith [hu.1],by dsimp [t]; linarith [hu.2]⟩
  have hpoly := absolute_lower t
  have hbrace := mul_le_mul_of_nonneg_left (brace_lower ht).le (sq_nonneg t)
  have hsq := sq_nonneg ((419/50)*|t|-3401/10000)
  have ha2 : |t|^2=t^2 := sq_abs t
  have he : 3/2+t=u := by dsimp [t]; ring
  rw [he] at hpoly
  nlinarith

theorem radical_reserve {u : ℝ} (hu : HeightRange u) : A u*(v u)^3<E u := by
  have hv := height_v_bounds hu
  have he := source_v_square (height_source_domain hu)
  simp only [sub_add_cancel] at he
  have hE := E_positive hu
  have hA := A_positive hu
  have hP := P_positive hu
  have hp : 0≤A u*(v u)^3 := mul_nonneg hA.le (pow_nonneg (by linarith [hv.1]) 3)
  have hid : (A u*(v u)^3)^2=A u^2*(Q0-u^2)^3 := by
    calc
      _ = A u^2*((v u)^2)^3 := by ring
      _ = _ := by rw [he]
  dsimp [P] at hP
  nlinarith

/-- Equation (5), retaining the actual endpoint radius K. -/
theorem endpoint_second_lower {p q K u d2 : ℝ}
    (hq : (767/1000:ℝ)<q) (hp : p<(253/1000)*q) (hK : K0<K)
    (hu : HeightRange u)
    (hid : d2*(v u)^3=q*(Q0*(K-(u-1)^2)-u*(u-1)*(Q0-u^2))-p*(u-1)*(v u)^3) :
    (13/20:ℝ)<d2 := by
  have hv := height_v_bounds hu
  have hv3 : 0<(v u)^3 := pow_pos (by linarith [hv.1]) 3
  have hu1 : 0<u-1 := by linarith [hu.1]
  have hrad := mul_lt_mul_of_pos_left (radical_reserve hu) (show 0<q by linarith)
  have hp' := mul_lt_mul_of_pos_right hp (mul_pos hu1 hv3)
  have hk := mul_pos (mul_pos (show 0<q by linarith) (show 0<Q0 by norm_num [Q0]))
    (sub_pos.mpr hK)
  have hq' := mul_lt_mul_of_pos_right hq (show 0<(13/20:ℝ)/(767/1000) by norm_num)
  have hqv := mul_lt_mul_of_pos_right hq' hv3
  dsimp [A,E] at hrad
  have hprod : (13/20)*(v u)^3<d2*(v u)^3 := by nlinarith
  exact (mul_lt_mul_iff_of_pos_right hv3).mp hprod

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Curvature
end
end
end

section
/-!
## The twelve continued endpoint curves

Each curve is the original source circle at one of
the two intrinsic core endpoints. The shared polynomial curvature
reserve is applied on the entire early angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Endpoint
open CommonQuarter CorePairGeometry Arithmetic

def AA (diagonal : Bool) : ℝ := if diagonal then CoreAngleEndpoint.diagonal+1/2 else 13/12
def BB (diagonal : Bool) : ℝ := if diagonal then CoreAngleEndpoint.diagonal-1/2 else 0
def bC (diagonal : Bool) : ℝ := if diagonal then CoreAngleEndpoint.diagonal else 1/2
def K (diagonal : Bool) : ℝ := AA diagonal^2+BB diagonal^2
def height (diagonal : Bool) (φ : ℝ) : ℝ := 1+AA diagonal*Real.cos φ-BB diagonal*Real.sin φ
def speed (diagonal : Bool) (φ : ℝ) : ℝ := AA diagonal*Real.sin φ+BB diagonal*Real.cos φ
def H (r : Row) (diagonal : Bool) (φ : ℝ) : ℝ :=
  φ+ocC r+M r (height diagonal φ-1/2)+ocG r*bC diagonal
def Hd (r : Row) (diagonal : Bool) (φ : ℝ) : ℝ :=
  1-M1 r (height diagonal φ-1/2)*speed diagonal φ
def Hdd (r : Row) (diagonal : Bool) (φ : ℝ) : ℝ :=
  M2 r (height diagonal φ-1/2)*(speed diagonal φ)^2-
    M1 r (height diagonal φ-1/2)*(height diagonal φ-1)

theorem endpoint_mem (diagonal : Bool) : bC diagonal∈SecondWord.MixedCorner.domain := by
  cases diagonal <;> dsimp [bC,SecondWord.MixedCorner.domain] <;>
    constructor <;> linarith [CoreAngleEndpoint.diagonal_bounds.1]
theorem height_contact (diagonal : Bool) (φ : ℝ) :
    height diagonal φ=contactPrimary (bC diagonal) φ+1/2 := by
  cases diagonal
  · dsimp [height,AA,BB,bC,contactPrimary]
    rw [SecondWord.MixedCorner.join]
    ring
  · dsimp [height,AA,BB,bC,contactPrimary]
    rw [SecondWord.MixedCorner.diagonal]
    ring
theorem height_range (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    HeightRange (height diagonal φ) := by
  rw [height_contact]
  exact contact_height_range (endpoint_mem diagonal) hφ
theorem height_domain (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    SourceDomain (height diagonal φ-1/2) := height_source_domain (height_range diagonal hφ)
theorem mass_lower (diagonal : Bool) : Curvature.K0<K diagonal := by
  cases diagonal
  · norm_num [Curvature.K0,K,AA,BB]
  · have hs := CoreAngleEndpoint.diagonal_sq
    have hd := CoreAngleEndpoint.diagonal_bounds.1
    dsimp [Curvature.K0,K,AA,BB]
    nlinarith

theorem height_hasDerivAt (diagonal : Bool) (φ : ℝ) :
    HasDerivAt (height diagonal) (-speed diagonal φ) φ := by
  have h := (((Real.hasDerivAt_cos φ).const_mul (AA diagonal)).const_add 1).sub
    ((Real.hasDerivAt_sin φ).const_mul (BB diagonal))
  exact h.congr_deriv (by simp only [speed]; ring)
theorem speed_hasDerivAt (diagonal : Bool) (φ : ℝ) :
    HasDerivAt (speed diagonal) (height diagonal φ-1) φ := by
  have h := ((Real.hasDerivAt_sin φ).const_mul (AA diagonal)).add
    ((Real.hasDerivAt_cos φ).const_mul (BB diagonal))
  exact h.congr_deriv (by simp only [height]; ring)
theorem speed_circle (diagonal : Bool) (φ : ℝ) :
    (speed diagonal φ)^2+(height diagonal φ-1)^2=K diagonal := by
  dsimp [speed,height,K]
  linear_combination (AA diagonal^2+BB diagonal^2)*(Real.sin_sq_add_cos_sq φ)
theorem H_hasDerivAt (r : Row) (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    HasDerivAt (H r diagonal) (Hd r diagonal φ) φ := by
  have h := (((hasDerivAt_id' φ).add_const (ocC r)).add
    ((M_hasDerivAt r (height_domain diagonal hφ)).comp φ
      ((height_hasDerivAt diagonal φ).sub_const (1/2)))).add_const (ocG r*bC diagonal)
  exact h.congr_deriv (by simp only [Hd]; ring)
theorem Hd_hasDerivAt (r : Row) (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    HasDerivAt (Hd r diagonal) (Hdd r diagonal φ) φ := by
  have h := (((M1_hasDerivAt r (height_domain diagonal hφ)).comp φ
    ((height_hasDerivAt diagonal φ).sub_const (1/2))).mul
      (speed_hasDerivAt diagonal φ)).const_sub 1
  exact h.congr_deriv (by simp only [Hdd,Function.comp]; ring)

theorem second_identity (r : Row) (diagonal : Bool) {φ : ℝ} (hφ : φ∈earlyAngles) :
    Hdd r diagonal φ*(v (height diagonal φ))^3=
      ocQ r*(Q0*(K diagonal-(height diagonal φ-1)^2)-
        height diagonal φ*(height diagonal φ-1)*(Q0-(height diagonal φ)^2))-
          ocP r*(height diagonal φ-1)*(v (height diagonal φ))^3 := by
  have hp := source_v_positive (height_domain diagonal hφ)
  have he := source_v_square (height_domain diagonal hφ)
  simp only [sub_add_cancel] at hp he
  have hs : (speed diagonal φ)^2=K diagonal-(height diagonal φ-1)^2 := by
    linarith [speed_circle diagonal φ]
  calc
    _ = ocQ r*Q0*(speed diagonal φ)^2-
        ocP r*(height diagonal φ-1)*(v (height diagonal φ))^3-
          ocQ r*height diagonal φ*(height diagonal φ-1)*(v (height diagonal φ))^2 := by
      dsimp [Hdd,M1,M2]
      simp only [sub_add_cancel]
      field_simp [hp.ne']
      ring
    _ = _ := by rw [hs,he]; ring

theorem curvature (r : Row) (hr : Remaining r) (diagonal : Bool) {φ : ℝ}
    (hφ : φ∈earlyAngles) : (13/20:ℝ)<Hdd r diagonal φ :=
  Curvature.endpoint_second_lower (coefficients r hr).1 (coefficients r hr).2.2.2.2
    (mass_lower diagonal) (height_range diagonal hφ) (second_identity r diagonal hφ)

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Endpoint
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Endpoint
open CommonQuarter Arithmetic StationaryPrimitives Reference

def AABox (diagonal : Bool) : Interval (AA diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal.add (Interval.point (1/2))
def BBBox (diagonal : Bool) : Interval (BB diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal.sub (Interval.point (1/2))
def bCBox (diagonal : Bool) : Interval (bC diagonal) := by
  cases diagonal
  · exact Interval.point _
  · exact coreDiagonal

def heightBox (diagonal : Bool) {φ : ℝ} (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ)) :
    Interval (height diagonal φ) :=
  ((Interval.point 1).add ((AABox diagonal).mul C)).sub ((BBBox diagonal).mul S)
def radicandBox {u : ℝ} (U : Interval u) : Interval (Q0-u^2) :=
  (Interval.point Q0).sub U.square
def radicalBox {u : ℝ} (U : Interval u) (hU : 0≤(radicandBox U).lo) : Interval (v u) :=
  rootSix (radicandBox U) (3/2) (by norm_num) hU
def valueBox (r : Row) (diagonal : Bool) {φ : ℝ} (Phi : Interval φ)
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) :
    Interval (H r diagonal φ) := by
  convert ((((Phi.add (Interval.point (ocC r))).add
    ((Interval.point (ocP r)).mul (U.sub (Interval.point (1/2))))).sub
      ((Interval.point (ocQ r)).mul (V.sub (Interval.point (1/2))))).add
        ((Interval.point (ocG r)).mul (bCBox diagonal))) using 1
  dsimp [H,M]
  simp only [sub_add_cancel]
  ring
def firstBox (r : Row) (diagonal : Bool) {φ : ℝ}
    (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ))
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) (hV : 0<V.lo) :
    Interval (Hd r diagonal φ) := by
  convert (Interval.point 1).sub
    (((Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul U).div V hV)).mul
      (((AABox diagonal).mul S).add ((BBBox diagonal).mul C))) using 1
  dsimp [Hd,M1,speed]
  simp only [sub_add_cancel]

private lemma r83_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r83_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl
private lemma r83_value_eq (r : Row) (diagonal : Bool) (φ : ℝ) :
    H r diagonal φ=φ+ocC r+ocP r*(height diagonal φ-1/2)-ocQ r*(v (height diagonal φ)-1/2)+
      ocG r*bC diagonal := by
  dsimp [H,M]; simp only [sub_add_cancel]; ring
private lemma r83_valueBox_lo (r : Row) (diagonal : Bool) {φ : ℝ} (Phi : Interval φ)
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) :
    (valueBox r diagonal Phi U V).lo=((((Phi.add (Interval.point (ocC r))).add
      ((Interval.point (ocP r)).mul (U.sub (Interval.point (1/2))))).sub
        ((Interval.point (ocQ r)).mul (V.sub (Interval.point (1/2))))).add
          ((Interval.point (ocG r)).mul (bCBox diagonal))).lo :=
  r83_mpr_lo (r83_value_eq r diagonal φ) _ _
private lemma r83_first_eq (r : Row) (diagonal : Bool) (φ : ℝ) :
    Hd r diagonal φ=1-(ocP r+ocQ r*height diagonal φ/v (height diagonal φ))*
      (AA diagonal*Real.sin φ+BB diagonal*Real.cos φ) := by
  dsimp [Hd,M1,speed]; simp only [sub_add_cancel]
private lemma r83_firstBox_lo (r : Row) (diagonal : Bool) {φ : ℝ}
    (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ))
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) (hV : 0<V.lo) :
    (firstBox r diagonal S C U V hV).lo=((Interval.point 1).sub
      (((Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul U).div V hV)).mul
        (((AABox diagonal).mul S).add ((BBBox diagonal).mul C)))).lo :=
  r83_mpr_lo (r83_first_eq r diagonal φ) _ _
private lemma r83_firstBox_hi (r : Row) (diagonal : Bool) {φ : ℝ}
    (S : Interval (Real.sin φ)) (C : Interval (Real.cos φ))
    (U : Interval (height diagonal φ)) (V : Interval (v (height diagonal φ))) (hV : 0<V.lo) :
    (firstBox r diagonal S C U V hV).hi=((Interval.point 1).sub
      (((Interval.point (ocP r)).add (((Interval.point (ocQ r)).mul U).div V hV)).mul
        (((AABox diagonal).mul S).add ((BBBox diagonal).mul C)))).hi :=
  r83_mpr_hi (r83_first_eq r diagonal φ) _ _
private lemma r83_rootStep_lo_pos {x : ℝ} (X : Interval x) (s : ℝ) (hs : 0<s) (hX : 0≤X.lo)
    (h : 0<X.lo) : 0<(SecondWord.OppositeThree.ReferenceAlgebra.rootStep X s hs hX).lo := by
  have hh : 0≤X.hi := hX.trans (X.mem.1.trans X.mem.2)
  dsimp [SecondWord.OppositeThree.ReferenceAlgebra.rootStep]
  positivity
private lemma r83_radicalBox_lo_pos {u : ℝ} (U : Interval u) (hU : 0≤(radicandBox U).lo)
    (h : 0<(radicandBox U).lo) : 0<(radicalBox U hU).lo := by
  unfold radicalBox rootSix SecondWord.OppositeThree.ReferenceAlgebra.rootThree
  exact r83_rootStep_lo_pos _ _ _ _ h

local macro "r83_fixed" : tactic => `(tactic|
  norm_num [r83_valueBox_lo,r83_firstBox_lo,r83_firstBox_hi,
    radicandBox,radicalBox,heightBox,AABox,BBBox,bCBox,AA,BB,bC,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    piBox,halfPi,coreDiagonal,Reference.sine,Reference.cosine,
    rootSix,SecondWord.OppositeThree.ReferenceAlgebra.rootThree,
    SecondWord.OppositeThree.ReferenceAlgebra.rootStep,HighOrderTaylor.S15,HighOrderTaylor.S13,
    HighOrderTaylor.S11,HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8,
    ocC,ocP,ocQ,ocG,Q0])

def reference (r : Row) (diagonal : Bool) : ℝ :=
  if r=0 then (if diagonal then 43/40 else 117/100)
  else if r=4 then (if diagonal then 1047/1000 else 1149/1000)
  else if r=11 then (if diagonal then 481/500 else 1061/1000)
  else if r=23 then (if diagonal then 132/125 else 287/250)
  else 1
theorem reference_positive (r : Row) (diagonal : Bool) : 0≤reference r diagonal := by
  fin_cases r <;> cases diagonal <;> norm_num [reference]
theorem reference_mem (r : Row) (diagonal : Bool) : reference r diagonal∈earlyAngles := by
  fin_cases r <;> cases diagonal <;> norm_num [reference,earlyAngles,lowerAngle] <;>
    linarith [pi_hand_enclosure.1,pi_hand_enclosure.2]
def refS (r : Row) (diagonal : Bool) : Interval (Real.sin (reference r diagonal)) :=
  sine (reference_positive r diagonal)
def refC (r : Row) (diagonal : Bool) : Interval (Real.cos (reference r diagonal)) :=
  cosine (reference_positive r diagonal)
def refU (r : Row) (diagonal : Bool) : Interval (height diagonal (reference r diagonal)) :=
  heightBox diagonal (refS r diagonal) (refC r diagonal)
private lemma r83_radicand_at (diagonal : Bool) {x : ℝ} (hx : 0≤x)
    (hv : (diagonal=true ∧ (x=43/40 ∨ x=1047/1000 ∨ x=481/500 ∨ x=132/125 ∨ x=1)) ∨
      (diagonal=false ∧ (x=117/100 ∨ x=1149/1000 ∨ x=1061/1000 ∨ x=287/250 ∨ x=1))) :
    0<(radicandBox (heightBox diagonal (Reference.sine hx) (Reference.cosine hx))).lo := by
  rcases hv with ⟨rfl,rfl|rfl|rfl|rfl|rfl⟩|⟨rfl,rfl|rfl|rfl|rfl|rfl⟩ <;> r83_fixed
private lemma r83_ref_radicand_pos (r : Row) (diagonal : Bool) :
    0<(radicandBox (refU r diagonal)).lo := by
  refine r83_radicand_at diagonal (reference_positive r diagonal) ?_
  cases diagonal <;> simp only [reference,Bool.false_eq_true,↓reduceIte] <;> split_ifs <;> norm_num
theorem ref_radicand (r : Row) (diagonal : Bool) : 0≤(radicandBox (refU r diagonal)).lo :=
  (r83_ref_radicand_pos r diagonal).le
def refV (r : Row) (diagonal : Bool) : Interval (v (height diagonal (reference r diagonal))) :=
  radicalBox (refU r diagonal) (ref_radicand r diagonal)
theorem refV_positive (r : Row) (diagonal : Bool) : 0<(refV r diagonal).lo :=
  r83_radicalBox_lo_pos _ _ (r83_ref_radicand_pos r diagonal)
def refH (r : Row) (diagonal : Bool) : Interval (H r diagonal (reference r diagonal)) :=
  valueBox r diagonal (Interval.point _) (refU r diagonal) (refV r diagonal)
def refHd (r : Row) (diagonal : Bool) : Interval (Hd r diagonal (reference r diagonal)) :=
  firstBox r diagonal (refS r diagonal) (refC r diagonal) (refU r diagonal) (refV r diagonal)
    (refV_positive r diagonal)
def refQuadratic (r : Row) (diagonal : Bool) :
    Interval (H r diagonal (reference r diagonal)-(Hd r diagonal (reference r diagonal))^2/(13/10)) :=
  (refH r diagonal).sub ((refHd r diagonal).square.div (Interval.point (13/10)) (by norm_num [Interval.point]))

private lemma r83_quad_at (r : Row) (diagonal : Bool) {x : ℝ} (hx : 0≤x)
    (hR : 0≤(radicandBox (heightBox diagonal (Reference.sine hx) (Reference.cosine hx))).lo)
    (hV : 0<(radicalBox (heightBox diagonal (Reference.sine hx) (Reference.cosine hx)) hR).lo)
    (hv : (r=0 ∧ ((diagonal=true ∧ x=43/40) ∨ (diagonal=false ∧ x=117/100))) ∨
      (r=4 ∧ ((diagonal=true ∧ x=1047/1000) ∨ (diagonal=false ∧ x=1149/1000))) ∨
      (r=11 ∧ ((diagonal=true ∧ x=481/500) ∨ (diagonal=false ∧ x=1061/1000))) ∨
      (r=23 ∧ ((diagonal=true ∧ x=132/125) ∨ (diagonal=false ∧ x=287/250)))) :
    (89809/100000:ℝ)<((valueBox r diagonal (Interval.point x)
      (heightBox diagonal (Reference.sine hx) (Reference.cosine hx)) (radicalBox _ hR)).sub
        ((firstBox r diagonal (Reference.sine hx) (Reference.cosine hx)
          (heightBox diagonal (Reference.sine hx) (Reference.cosine hx)) (radicalBox _ hR) hV).square.div
            (Interval.point (13/10)) (by norm_num [Interval.point]))).lo := by
  simp only [Interval.sub,Interval.div,Interval.square,Interval.mul,Interval.inv]
  rw [r83_valueBox_lo,r83_firstBox_lo,r83_firstBox_hi]
  rcases hv with ⟨rfl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩|⟨rfl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩|⟨rfl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩|
    ⟨rfl,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ <;> r83_fixed

theorem reference_reserve (r : Row) (hr : r=0∨r=4∨r=11∨r=23) (diagonal : Bool) :
    (89809/100000:ℝ)<H r diagonal (reference r diagonal)-(Hd r diagonal (reference r diagonal))^2/(13/10) := by
  have hbound : (89809/100000:ℝ)<(refQuadratic r diagonal).lo :=
    r83_quad_at r diagonal (reference_positive r diagonal) (ref_radicand r diagonal)
      (refV_positive r diagonal)
      (by rcases hr with rfl|rfl|rfl|rfl <;> cases diagonal <;> norm_num [reference])
  exact hbound.trans_le (refQuadratic r diagonal).mem.1

def initialPhi : Interval lowerAngle := halfPi.sub (Interval.point (7/10))
def initialS : Interval (Real.sin lowerAngle) := by
  convert cosine (by norm_num : (0:ℝ)≤7/10) using 1
  exact Real.sin_pi_div_two_sub (7/10)
def initialC : Interval (Real.cos lowerAngle) := by
  convert sine (by norm_num : (0:ℝ)≤7/10) using 1
  exact Real.cos_pi_div_two_sub (7/10)
private lemma r83_initialS_lo : initialS.lo=(Reference.cosine (by norm_num : (0:ℝ)≤7/10)).lo :=
  r83_mpr_lo (Real.sin_pi_div_two_sub (7/10)) _ _
private lemma r83_initialS_hi : initialS.hi=(Reference.cosine (by norm_num : (0:ℝ)≤7/10)).hi :=
  r83_mpr_hi (Real.sin_pi_div_two_sub (7/10)) _ _
private lemma r83_initialC_lo : initialC.lo=(Reference.sine (by norm_num : (0:ℝ)≤7/10)).lo :=
  r83_mpr_lo (Real.cos_pi_div_two_sub (7/10)) _ _
private lemma r83_initialC_hi : initialC.hi=(Reference.sine (by norm_num : (0:ℝ)≤7/10)).hi :=
  r83_mpr_hi (Real.cos_pi_div_two_sub (7/10)) _ _
def initialU (diagonal : Bool) : Interval (height diagonal lowerAngle) := heightBox diagonal initialS initialC
private lemma r83_initial_radicand_pos (diagonal : Bool) : 0<(radicandBox (initialU diagonal)).lo := by
  cases diagonal <;>
    simp only [radicandBox,initialU,heightBox,Interval.sub,Interval.add,Interval.square,Interval.mul,
      r83_initialS_lo,r83_initialS_hi,r83_initialC_lo,r83_initialC_hi] <;> r83_fixed
theorem initial_radicand (diagonal : Bool) : 0≤(radicandBox (initialU diagonal)).lo :=
  (r83_initial_radicand_pos diagonal).le
def initialV (diagonal : Bool) : Interval (v (height diagonal lowerAngle)) :=
  radicalBox (initialU diagonal) (initial_radicand diagonal)
theorem initialV_positive (diagonal : Bool) : 0<(initialV diagonal).lo :=
  r83_radicalBox_lo_pos _ _ (r83_initial_radicand_pos diagonal)
def initialH (r : Row) (diagonal : Bool) : Interval (H r diagonal lowerAngle) :=
  valueBox r diagonal initialPhi (initialU diagonal) (initialV diagonal)
def initialHd (r : Row) (diagonal : Bool) : Interval (Hd r diagonal lowerAngle) :=
  firstBox r diagonal initialS initialC (initialU diagonal) (initialV diagonal) (initialV_positive diagonal)

theorem initial_reserve (r : Row) (hr : r=12∨r=19) (diagonal : Bool) :
    (89809/100000:ℝ)<H r diagonal lowerAngle ∧ 0<Hd r diagonal lowerAngle := by
  have hv : (89809/100000:ℝ)<(initialH r diagonal).lo := by
    unfold initialH
    rw [r83_valueBox_lo]
    unfold initialV initialU initialPhi
    simp only [Interval.sub,Interval.add,Interval.mul,heightBox,
      r83_initialS_lo,r83_initialS_hi,r83_initialC_lo,r83_initialC_hi]
    rcases hr with rfl|rfl <;> cases diagonal <;> r83_fixed
  have hd : 0<(initialHd r diagonal).lo := by
    unfold initialHd
    rw [r83_firstBox_lo]
    unfold initialV initialU
    simp only [Interval.sub,Interval.add,Interval.mul,Interval.div,Interval.inv,heightBox,
      r83_initialS_lo,r83_initialS_hi,r83_initialC_lo,r83_initialC_hi]
    rcases hr with rfl|rfl <;> cases diagonal <;> r83_fixed
  exact ⟨hv.trans_le (initialH r diagonal).mem.1,hd.trans_le (initialHd r diagonal).mem.1⟩

theorem lower (r : Row) (hr : Remaining r) (diagonal : Bool) {φ : ℝ}
    (hφ : φ∈earlyAngles) : (89809/100000:ℝ)<H r diagonal φ := by
  by_cases hi : r=12∨r=19
  · have h := curvature_tangent (κ:=(13/20:ℝ)) hφ early_left
      (fun t ht => H_hasDerivAt r diagonal ht)
      (fun t ht => Hd_hasDerivAt r diagonal ht)
      (fun t ht => (curvature r hr diagonal ht).le)
    have hinit := initial_reserve r hi diagonal
    have hp := mul_nonneg hinit.2.le (sub_nonneg.mpr hφ.1)
    nlinarith [sq_nonneg (φ-lowerAngle)]
  · have hrows : r=0∨r=4∨r=11∨r=23 := by
      rcases (remaining_iff r).1 hr with h|h|h|h|h|h <;> simp_all
    have href := reference_reserve r hrows diagonal
    have h := positive_of_curvature (f:=fun t => H r diagonal t-89809/100000)
      (d:=Hd r diagonal) (dd:=Hdd r diagonal) (κ:=(13/20:ℝ)) (by norm_num)
      hφ (reference_mem r diagonal)
      (fun t ht => (H_hasDerivAt r diagonal ht).sub_const (89809/100000))
      (fun t ht => Hd_hasDerivAt r diagonal ht)
      (fun t ht => (curvature r hr diagonal ht).le) (by nlinarith)
    linarith

end SquaresInCircles.Eight.ShortWord.MixedQuarter.OuterNegative.Endpoint
end
end
end
