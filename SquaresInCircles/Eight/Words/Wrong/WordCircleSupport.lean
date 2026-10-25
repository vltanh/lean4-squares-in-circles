module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.CircularNorm
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.Endpoint.RotationPenalty
public import SquaresInCircles.Eight.Owners.SpanNormBounds
public import SquaresInCircles.Eight.Owners.TrigonometricReserves
public import SquaresInCircles.Eight.Words.Common.QuarterState
public import SquaresInCircles.Eight.Words.Common.ZeroEndpoint

/-!
# Eight squares: intrinsic circle-support transitions on a complete zero-quarter half

An affine functional on the actual outer arc is minimized at the axial
end, at the diagonal end, or at its full-circle support point. The two
changes occur at zeros of the actual endpoint derivatives. The norm
envelope is concave between those changes, so endpoint estimates extend
over the entire angle interval without selecting angular cells.

The derivative events are obtained by the intermediate value theorem;
their numerical locations are neither supplied nor used.
-/

section
/-!
## One-variable inequalities for the original wrong-sign capture hull

The negative-angle functions `F` are convex on the whole frame interval for every `0 < b ≤ v`,
with no lower bound on the ratio (`F_convex`); their second derivatives keep the strict reserve
`3v/50` (`F_second_lower`). The two positive exterior functions decrease (`A_antitone`,
`B_antitone`). For the second one, exact homogeneity (`B_normalize`) reduces the estimate to the
uniform derivative bound of the middle stress.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.WrongSignCaptureHull
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeEnvelope

abbrev R : ℝ := EndpointRotationPenalty.R
abbrev p : ℝ := EndpointRotationPenalty.charge

def F (v b u : ℝ) : ℝ :=
  R*pairNorm v b (-u)-v*Real.cos u+p*u

def A (v b u : ℝ) : ℝ :=
  R*pairNorm v b u-v*PositiveAngularEnvelope.phi u-p*u

def B (c b u : ℝ) : ℝ :=
  R*pairNorm c b u-b*PositiveAngularEnvelope.phi u-p*u

def Fd (v b u : ℝ) : ℝ :=
  -R*normD1 v b (-u)+v*Real.sin u+p

def Fdd (v b u : ℝ) : ℝ :=
  R*normD2 v b (-u)+v*Real.cos u

def Ad (v b u : ℝ) : ℝ :=
  R*normD1 v b u-v*(Real.cos u-Real.sin u)-p

/-- The zero-angle curvature bound needs only `0≤r≤1`.  The factorization
is the same sum of squares as in the ordinary coefficient bound. -/
theorem shapeC0q_full {r : ℝ} (hr : r∈Icc 0 1) :
    shapeC0q R r<7/10 := by
  have hr2 : r^2≤1 := by simpa using pow_le_pow_left₀ hr.1 hr.2 2
  have hpos : 0≤(1-r^2)*(1+4*r^2-r^4) :=
    mul_nonneg (by linarith) (by nlinarith [sq_nonneg r])
  have hid : (shape r)^6-8*r^4=(1-r^2)*(1+4*r^2-r^4) := by
    calc
      (shape r)^6-8*r^4=((shape r)^2)^3-8*r^4 := by ring
      _=(1-r^2)*(1+4*r^2-r^4) := by rw [shape_sq]; ring
  have hsos : 8*r^4≤(shape r)^6 := by linarith
  have hs6 := pow_pos (shape_pos r) 6
  have hR2 : R^2=9789/2500 := EndpointRotationPenalty.R_sq
  unfold shapeC0q
  apply quotient_lt_of_square (pow_pos (shape_pos r) 3) (by norm_num)
  have e1 : (R*r^2)^2=R^2*r^4 := by ring
  have e2 : (7/10:ℝ)^2*((shape r)^3)^2=(49/100)*(shape r)^6 := by ring
  rw [e1,e2,hR2]
  linarith

theorem zero_curvature_lt {v b : ℝ} (hb : 0<b) (hbv : b≤v) :
    curvatureZero R v b<(7/10)*v := by
  have hv : 0<v := hb.trans_le hbv
  have hr : b/v∈Icc 0 1 :=
    ⟨div_nonneg hb.le hv.le,(div_le_one hv).2 hbv⟩
  have hswap : curvatureZero R v b=curvatureZero R b v := by
    dsimp [curvatureZero,pairProduct]
    rw [pairNorm_symm v b 0]
    ring
  have hnormal := (curvature_constants_normalize (R := R) hb hv).2.2.1
  rw [hswap,hnormal]
  linarith [mul_lt_mul_of_pos_left (shapeC0q_full hr) hv]

theorem F_hasDerivAt {v b u : ℝ} (hv : 0<v) (hb : 0<b)
    (hu : u∈Icc 0 frameCap) : HasDerivAt (F v b) (Fd v b u) u := by
  have hn := (pairNorm_hasDerivAt hv hb
    (show |-u|≤frameCap by simpa only [abs_neg,abs_of_nonneg hu.1] using hu.2)).comp u
      (hasDerivAt_id u).neg
  have hraw := ((hn.const_mul R).sub ((Real.hasDerivAt_cos u).const_mul v)).add
    ((hasDerivAt_id u).const_mul p)
  convert hraw using 1
  · rfl
  · dsimp [Fd]
    ring

theorem Fd_hasDerivAt {v b u : ℝ} (hv : 0<v) (hb : 0<b)
    (hu : u∈Icc 0 frameCap) : HasDerivAt (Fd v b) (Fdd v b u) u := by
  have hn := (normD1_hasDerivAt hv hb
    (show |-u|≤frameCap by simpa only [abs_neg,abs_of_nonneg hu.1] using hu.2)).comp u
      (hasDerivAt_id u).neg
  have hraw := ((hn.const_mul (-R)).add
    ((Real.hasDerivAt_sin u).const_mul v)).add_const p
  convert hraw using 1
  · rfl
  · dsimp [Fdd]
    ring

/-- The original negative-angle support has strictly positive curvature
with a uniform reserve. -/
theorem F_second_lower {v b u : ℝ} (hb : 0<b) (hbv : b≤v)
    (hu : u∈Icc 0 frameCap) : (3/50)*v<Fdd v b u := by
  have hv : 0<v := hb.trans_le hbv
  have hcurv := curvature_negative_upper EndpointRotationPenalty.R_nonneg hv hb
    (show -u∈Icc (-frameCap) 0 by constructor <;> linarith [hu.1,hu.2])
  have hzero := zero_curvature_lt hb hbv
  have hcos := mul_lt_mul_of_pos_left (transport_trig hu).1 hv
  dsimp [Fdd,curvature] at hcurv ⊢
  nlinarith

theorem F_convex {v b : ℝ} (hb : 0<b) (hbv : b≤v) :
    ConvexOn ℝ (Icc 0 frameCap) (F v b) := by
  have hv : 0<v := hb.trans_le hbv
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 frameCap)
    (fun u hu => (F_hasDerivAt hv hb hu).continuousAt.continuousWithinAt)
    (fun u hu => (F_hasDerivAt hv hb (interior_subset hu)).hasDerivWithinAt)
    (fun u hu => (Fd_hasDerivAt hv hb (interior_subset hu)).hasDerivWithinAt)
    (fun u hu => by
      have hh := F_second_lower hb hbv (interior_subset hu)
      nlinarith)

/-- A uniform slope bound for the positive-angle norm.  The
coefficient inequality follows by squaring at the same original radius. -/
theorem norm_slope_upper {v b u : ℝ} (hv : 0<v) (hb : 0<b) (hbv : b≤v)
    (hu : u∈Icc 0 frameCap) :
    R*normD1 v b u≤(7/5)*v*Real.cos u := by
  have hu' : |u|≤frameCap := by rw [abs_of_nonneg hu.1]; exact hu.2
  have hN := pairNorm_pos hv hb hu'
  have hN2 := pairNorm_sq hv hb hu'
  have hbsq := pow_le_pow_left₀ hb.le hbv 2
  have hs := (transport_trig hu).2.2.1
  have hprod := mul_nonneg (mul_nonneg hv.le hb.le) hs
  have hNlower : 2*b^2≤(pairNorm v b u)^2 := by
    dsimp [pairEnergy,pairProduct] at hN2
    nlinarith
  have hRmul := congrArg (fun z : ℝ => z*b^2) EndpointRotationPenalty.R_sq
  have hcoefficient : R*b≤(7/5)*pairNorm v b u := by
    have hsq : (R*b)^2≤((7/5)*pairNorm v b u)^2 := by
      dsimp [qCap] at hRmul
      nlinarith [sq_nonneg b]
    have hr0 := mul_nonneg EndpointRotationPenalty.R_nonneg hb.le
    have hn0 : 0≤(7/5)*pairNorm v b u := by positivity
    nlinarith
  have hc0 : 0≤Real.cos u := (transport_cos_pos hu').le
  have hm := mul_le_mul_of_nonneg_right hcoefficient (mul_nonneg hv.le hc0)
  calc
    R*normD1 v b u=(R*b*(v*Real.cos u))/pairNorm v b u := by
      dsimp [normD1,pairProduct]
      ring
    _≤(7/5)*v*Real.cos u := by
      apply (div_le_iff₀ hN).2
      nlinarith only [hm]

theorem positive_slope_shape {u : ℝ} (hu : u∈Icc 0 frameCap) :
    (2/5)*Real.cos u+Real.sin u≤1 := by
  have hmono : MonotoneOn (fun z : ℝ => (2/5)*Real.cos z+Real.sin z)
      (Icc 0 frameCap) := by
    apply monoOn_of_hasDeriv_nonneg
      (d := fun z => Real.cos z-(2/5)*Real.sin z)
    · fun_prop
    · intro z _
      convert ((Real.hasDerivAt_cos z).const_mul (2/5)).add
        (Real.hasDerivAt_sin z) using 1
      ring
    · intro z hz
      obtain ⟨hc,_,_,hs,_⟩ := transport_trig (Ioo_subset_Icc_self hz)
      linarith
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := cos_upper_four (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hs := sin_upper_five (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hend : (2/5)*Real.cos frameCap+Real.sin frameCap≤1 := by
    norm_num [frameCap] at hc hs
    linarith
  exact (hmono hu hh hu.2).trans hend

theorem A_hasDerivAt {v b u : ℝ} (hv : 0<v) (hb : 0<b)
    (hu : u∈Icc 0 frameCap) : HasDerivAt (A v b) (Ad v b u) u := by
  have hn := pairNorm_hasDerivAt hv hb
    (show |u|≤frameCap by rw [abs_of_nonneg hu.1]; exact hu.2)
  have hphi := (Real.hasDerivAt_cos u).add (Real.hasDerivAt_sin u)
  have hraw := ((hn.const_mul R).sub (hphi.const_mul v)).sub
    ((hasDerivAt_id u).const_mul p)
  convert hraw using 1
  · rfl
  · dsimp [Ad]
    ring

theorem A_derivative_upper {v b u : ℝ} (hb : 0<b) (hbv : b≤v) (hv1 : v≤1)
    (hu : u∈Icc 0 frameCap) : Ad v b u≤ -(1/49) := by
  have hv : 0<v := hb.trans_le hbv
  have hnorm := norm_slope_upper hv hb hbv hu
  have hshape := mul_le_mul_of_nonneg_left (positive_slope_shape hu) hv.le
  dsimp [Ad,p,EndpointRotationPenalty.charge]
  nlinarith

theorem A_antitone {v b : ℝ} (hb : 0<b) (hbv : b≤v) (hv1 : v≤1) :
    AntitoneOn (A v b) (Icc 0 frameCap) := by
  have hv : 0<v := hb.trans_le hbv
  apply antiOn_of_hasDeriv_nonpos
  · exact fun u hu => (A_hasDerivAt hv hb hu).continuousAt.continuousWithinAt
  · exact fun u hu => A_hasDerivAt hv hb (Ioo_subset_Icc_self hu)
  · intro u hu
    have hh := A_derivative_upper hb hbv hv1 (Ioo_subset_Icc_self hu)
    linarith

/-- Exact homogeneity of the second exterior function.  Its angle
dependence is the negative of the original ordinary positive envelope. -/
theorem B_normalize {c : ℝ} (hc : 0<c) (b u : ℝ) :
    B c b u=c*(-SpanNormBounds.U (b/c) u+
      R*pairNorm (b/c) 1 0-b/c)-p*u := by
  have hb : c*(b/c)=b := by field_simp [hc.ne']
  have hN : pairNorm c b u=c*pairNorm (b/c) 1 u := by
    calc
      pairNorm c b u=pairNorm (c*(b/c)) (c*1) u := by
        rw [hb,mul_one]
        exact pairNorm_symm c b u
      _=c*pairNorm (b/c) 1 u := pairNorm_homogeneous hc.le _ _ _
  rw [B,hN]
  dsimp [SpanNormBounds.U,OrdinaryAngleConcavity.U,SpanNormBounds.R,
    R,EndpointRotationPenalty.R]
  field_simp [hc.ne']
  ring

theorem B_difference_upper {c b x y : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hr : b/c∈Icc (13/20 : ℝ) (23/25))
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    B c b y-B c b x≤ -(368/1225)*(y-x) := by
  have hU := SpanNormBounds.U_growth hr hx hy hxy
  have hm := mul_le_mul_of_nonneg_left hU hc.le
  have hcMul := mul_le_mul_of_nonneg_right hc1 (sub_nonneg.mpr hxy)
  rw [B_normalize hc b y,B_normalize hc b x]
  dsimp [p,EndpointRotationPenalty.charge]
  nlinarith

theorem B_antitone {c b : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hr : b/c∈Icc (13/20 : ℝ) (23/25)) :
    AntitoneOn (B c b) (Icc 0 frameCap) := by
  intro x hx y hy hxy
  have hh := B_difference_upper hc hc1 hr hx hy hxy
  nlinarith

end SquaresInCircles.Eight.WrongSignCaptureHull
end
end
end

section
/-!
## Wrong-sign HG0/GA1 pairs with nonpositive total

The comparison point is on the flat core and strictly inside the same q-circle; the original H
and A states do not move. The final HG slack has a uniform positive reserve, including zero
paired total and `yG = 0` (`replacement_slack`, `wrong_sign_nonpositive_total_transport`).

The scalar statements use the whole intervals. The single auxiliary `F` has negative third
derivative (`dddF_negative`), hence negative second derivative, on `[0,1/3]` (`F_concave`). Only
its two endpoints are evaluated (`F_zero_reserve`, `F_third_reserve`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace WrongSign

abbrev L : ℝ := 447/800
abbrev K : ℝ := 13/12
abbrev κ : ℝ := 847/800
abbrev ℓ : ℝ := 21/200

def width (x : ℝ) : ℝ := (1+Real.cos x+Real.sin x)/2

def wrongTarget (x : ℝ) : ℝ := 2/5-Real.cos x/2+(183/200)*Real.sin x

def wrongTargetDerivative (x : ℝ) : ℝ := Real.sin x/2+(183/200)*Real.cos x

theorem wrongTarget_hasDeriv (x : ℝ) :
    HasDerivAt wrongTarget (wrongTargetDerivative x) x := by
  have h := ((hasDerivAt_const x (2/5 : ℝ)).fun_sub
    ((Real.hasDerivAt_cos x).div_const 2)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (183/200))
  exact h.congr_deriv (by unfold wrongTargetDerivative; ring)

theorem wrongTarget_increasing : StrictMonoOn wrongTarget (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve (k := 1/2)
  · exact fun x _ => (wrongTarget_hasDeriv x).continuousAt.continuousWithinAt
  · intro x hx
    exact wrongTarget_hasDeriv x
  · norm_num
  · intro x hx
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse (Ioo_subset_Icc_self hx)
    unfold wrongTargetDerivative
    nlinarith

theorem wrongTarget_at_cut : wrongTarget ℓ < 0 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := (21/200 : ℝ))
  have hs := sin_upper_five (x := (21/200 : ℝ)) (by norm_num)
  dsimp [wrongTarget,ℓ]
  norm_num at hc hs ⊢
  linarith

/-- A wrong weak G sign forces a positive HG error separated from zero. -/
theorem positive_error_cut {bH aG g v : ℝ}
    (hb : bH<9/10) (ha : aG<283/200) (hg : 0≤g)
    (hv : v∈Icc 0 (7/10 : ℝ))
    (h : width v ≤ bH+aG*Real.sin v-g*Real.cos v) : ℓ<v := by
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hv
  have hprod := mul_nonneg hg (show 0≤Real.cos v by linarith)
  have hA := mul_le_mul_of_nonneg_right ha.le hs0
  have hf : 0<wrongTarget v := by
    dsimp [wrongTarget,width] at h ⊢
    nlinarith
  by_contra! hv'
  have hm := wrongTarget_increasing.monotoneOn hv
    (show ℓ∈Icc 0 (7/10 : ℝ) by norm_num [ℓ]) hv'
  linarith [wrongTarget_at_cut]

def pairExcess (s v : ℝ) : ℝ :=
  width v+width (v+s)-2+L*(Real.sin (v+s)-Real.sin v)

def pairExcessDerivative (s v : ℝ) : ℝ :=
  -(L-1/2)*Real.cos v+κ*Real.cos (v+s)-
    (Real.sin v+Real.sin (v+s))/2

def spanDemand (s : ℝ) : ℝ := κ*Real.sin s-(1-Real.cos s)/2

def spanDemandDerivative (s : ℝ) : ℝ := κ*Real.cos s-Real.sin s/2

theorem pairExcess_hasDeriv (s v : ℝ) :
    HasDerivAt (pairExcess s) (pairExcessDerivative s v) v := by
  have hw : ∀ x : ℝ, HasDerivAt width ((Real.cos x-Real.sin x)/2) x := by
    intro x
    have h := (((Real.hasDerivAt_cos x).const_add 1).fun_add (Real.hasDerivAt_sin x)).div_const 2
    exact h.congr_deriv (by ring)
  have ha : HasDerivAt (fun x => x+s) 1 v := (hasDerivAt_id' v).add_const s
  have hs := (Real.hasDerivAt_sin (v+s)).comp v ha
  have h := (((hw v).fun_add ((hw (v+s)).comp v ha)).sub_const 2).fun_add
    ((hs.fun_sub (Real.hasDerivAt_sin v)).const_mul L)
  exact h.congr_deriv (by unfold pairExcessDerivative L κ; ring)

theorem pairExcessDerivative_pos {s v : ℝ}
    (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10) :
    53341/500000 < pairExcessDerivative s v := by
  obtain ⟨hc,hc1,hsi0,hsi,hsc⟩ := transport_trig ⟨hv,by linarith⟩
  obtain ⟨hC,hC1,hS0,hS,hSC⟩ := transport_trig ⟨by linarith,hvs⟩
  unfold pairExcessDerivative L κ
  nlinarith

theorem pairExcess_lower {s v : ℝ}
    (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10) :
    spanDemand s ≤ pairExcess s v := by
  have hm : MonotoneOn (pairExcess s) (Icc 0 (7/10-s)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x _ => (pairExcess_hasDeriv s x).continuousAt.continuousWithinAt
    · intro x hx
      exact pairExcess_hasDeriv s x
    · intro x hx
      have h := pairExcessDerivative_pos hs hx.1.le (by linarith [hx.2])
      linarith
  have h := hm (show (0:ℝ)∈Icc 0 (7/10-s) by constructor <;> linarith)
    (show v∈Icc 0 (7/10-s) by constructor <;> linarith) hv
  have h0 : pairExcess s 0=spanDemand s := by
    simp only [pairExcess,width,spanDemand,zero_add,Real.cos_zero,Real.sin_zero,L,κ]
    ring
  rw [h0] at h
  exact h

theorem spanDemand_hasDeriv (s : ℝ) :
    HasDerivAt spanDemand (spanDemandDerivative s) s := by
  have h := ((Real.hasDerivAt_sin s).const_mul κ).fun_sub
    (((hasDerivAt_const s (1:ℝ)).fun_sub (Real.hasDerivAt_cos s)).div_const 2)
  exact h.congr_deriv (by unfold spanDemandDerivative; ring)

theorem spanDemand_increasing : StrictMonoOn spanDemand (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve (k := 2/5)
  · exact fun x _ => (spanDemand_hasDeriv x).continuousAt.continuousWithinAt
  · intro x hx
    exact spanDemand_hasDeriv x
  · norm_num
  · intro x hx
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse (Ioo_subset_Icc_self hx)
    unfold spanDemandDerivative κ
    nlinarith

theorem spanDemand_at_third : 63/200 < spanDemand (1/3) := by
  have hs := sin_lower_seven (x := (1/3 : ℝ)) (by norm_num)
  have hc := cos_lower_six (x := (1/3 : ℝ)) (by norm_num)
  unfold spanDemand κ
  norm_num at hs hc ⊢
  linarith

/-- The span cut uses the original two witnesses, before moving G. -/
theorem original_pair_bounds {H G A : SignedPoint} {s v : ℝ}
    (hH : H.y<9/10) (hA : A.a<283/200) (hG : L≤G.a)
    (hg : 0≤G.y) (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10)
    (hHG : width v ≤ H.y+G.a*Real.sin v-G.y*Real.cos v)
    (hGA : width (v+s) ≤ A.a-G.a*Real.sin (v+s)+G.y*Real.cos (v+s)) :
    11/10 < A.a ∧ s<1/3 := by
  have hsine : Real.sin v ≤ Real.sin (v+s) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three]) (by linarith)
  have hcos : Real.cos (v+s) ≤ Real.cos v :=
    Real.cos_le_cos_of_nonneg_of_le_pi hv
      (by linarith [Real.pi_gt_three]) (by linarith)
  have hprodA := mul_nonneg (show 0≤G.a by dsimp [L] at hG; linarith)
    (sub_nonneg.mpr hsine)
  have hprodG := mul_nonneg hg (sub_nonneg.mpr hcos)
  have hWv : 1≤width v := by
    show 1≤(1+Real.cos v+Real.sin v)/2
    rw [← edgeWidth_positive_formula ⟨hv,by linarith⟩]
    exact edgeWidth_ge_one v
  have hWz : 1≤width (v+s) := by
    show 1≤(1+Real.cos (v+s)+Real.sin (v+s))/2
    rw [← edgeWidth_positive_formula ⟨by linarith,hvs⟩]
    exact edgeWidth_ge_one (v+s)
  have hlarge : 11/10<A.a := by nlinarith
  refine ⟨hlarge,?_⟩
  have hprodL := mul_nonneg (sub_nonneg.mpr hG) (sub_nonneg.mpr hsine)
  have hpair : 2+pairExcess s v ≤ H.y+A.a := by
    dsimp [pairExcess]
    nlinarith
  have hspan := pairExcess_lower hs hv hvs
  by_contra! hs'
  have hm := spanDemand_increasing.monotoneOn
    (show (1/3:ℝ)∈Icc 0 (7/10 : ℝ) by norm_num)
    (show s∈Icc 0 (7/10 : ℝ) by constructor <;> linarith) hs'
  linarith [spanDemand_at_third]

def coefficient (z : ℝ) : ℝ := (L-1/2)*Real.cos z+Real.sin z/2-K

def error (z s : ℝ) : ℝ :=
  Real.cos s*(Real.sin z+Real.cos z-1)+coefficient z*Real.sin s

def errorDerivative (z s : ℝ) : ℝ :=
  (Real.cos s+Real.sin s/2)*Real.cos z-
    (Real.cos s+(L-1/2)*Real.sin s)*Real.sin z

theorem error_hasDeriv (z s : ℝ) :
    HasDerivAt (fun x => error x s) (errorDerivative z s) z := by
  have h := ((((Real.hasDerivAt_sin z).fun_add (Real.hasDerivAt_cos z)).sub_const 1).const_mul
    (Real.cos s)).fun_add
      ((((Real.hasDerivAt_cos z).const_mul (L-1/2)).fun_add
        ((Real.hasDerivAt_sin z).div_const 2)).sub_const K |>.mul_const (Real.sin s))
  exact h.congr_deriv (by unfold errorDerivative; ring)

theorem error_increasing {s : ℝ} (hs : s∈Icc 0 (1/3 : ℝ)) :
    StrictMonoOn (fun z => error z s) (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve (k := 1/20)
  · exact fun z _ => (error_hasDeriv z s).continuousAt.continuousWithinAt
  · intro z hz
    exact error_hasDeriv z s
  · norm_num
  · intro z hz
    obtain ⟨hc,hc1,hsi0,hsi,hsc⟩ := transport_trig (Ioo_subset_Icc_self hz)
    obtain ⟨hC,hS0,hS⟩ := transport_trig_coarse
      (show s∈Icc 0 (7/10 : ℝ) by constructor <;> linarith [hs.1,hs.2])
    have hfirst : 3/4 ≤ Real.cos s+(L-1/2)*Real.sin s := by
      dsimp [L]
      nlinarith
    have hgap : 0 ≤ (1-L)*Real.sin s := mul_nonneg (by norm_num [L]) hS0
    have hprod := mul_nonneg
      (show 0≤Real.cos s+(L-1/2)*Real.sin s-3/4 by linarith)
      (show 0≤Real.cos z-Real.sin z by linarith)
    have hprod2 := mul_nonneg hgap (show 0≤Real.cos z by linarith)
    unfold errorDerivative L at *
    nlinarith

def F (s : ℝ) : ℝ :=
  κ/2*Real.sin (2*s+ℓ)+Real.cos (2*s+ℓ)/4+
    3/4*Real.cos ℓ+(2-κ)/2*Real.sin ℓ-Real.cos s-K*Real.sin s

def dF (s : ℝ) : ℝ :=
  κ*Real.cos (2*s+ℓ)-Real.sin (2*s+ℓ)/2+Real.sin s-K*Real.cos s

def ddF (s : ℝ) : ℝ :=
  -2*κ*Real.sin (2*s+ℓ)-Real.cos (2*s+ℓ)+Real.cos s+K*Real.sin s

def dddF (s : ℝ) : ℝ :=
  -4*κ*Real.cos (2*s+ℓ)+2*Real.sin (2*s+ℓ)-Real.sin s+K*Real.cos s

theorem F_error (s : ℝ) : F s=error (s+ℓ) s := by
  simp only [F,error,coefficient,Real.sin_add,Real.cos_add,
    Real.sin_two_mul,Real.cos_two_mul,L,K,κ]
  linear_combination (-(Real.cos ℓ/2-(47/800)*Real.sin ℓ))*Real.sin_sq_add_cos_sq s

theorem F_derivatives (s : ℝ) :
    HasDerivAt F (dF s) s ∧ HasDerivAt dF (ddF s) s ∧
      HasDerivAt ddF (dddF s) s := by
  have ha : HasDerivAt (fun x : ℝ => 2*x+ℓ) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul 2).add_const ℓ
  have hs := (Real.hasDerivAt_sin (2*s+ℓ)).comp s ha
  have hc := (Real.hasDerivAt_cos (2*s+ℓ)).comp s ha
  refine ⟨?_,?_,?_⟩
  · have h := (((((hs.const_mul (κ/2)).fun_add (hc.div_const 4)).add_const
      (3/4*Real.cos ℓ)).add_const ((2-κ)/2*Real.sin ℓ)).fun_sub
      (Real.hasDerivAt_cos s)).fun_sub ((Real.hasDerivAt_sin s).const_mul K)
    exact h.congr_deriv (by unfold dF; ring)
  · have h := (((hc.const_mul κ).fun_sub (hs.div_const 2)).fun_add
      (Real.hasDerivAt_sin s)).fun_sub ((Real.hasDerivAt_cos s).const_mul K)
    exact h.congr_deriv (by unfold ddF; ring)
  · have h := (((hs.const_mul (-2*κ)).fun_sub hc).fun_add (Real.hasDerivAt_cos s)).fun_add
      ((Real.hasDerivAt_sin s).const_mul K)
    exact h.congr_deriv (by unfold dddF; ring)

theorem dddF_negative {s : ℝ} (hs : s∈Icc 0 (1/3 : ℝ)) : dddF s<0 := by
  have hw : 2*s+ℓ ∈ Icc 0 (463/600 : ℝ) := by
    constructor <;> dsimp [ℓ] <;> linarith [hs.1,hs.2]
  have hb := trig_bracket (l := 0) (u := (463/600 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hw
  have hC : 716/1000 < Real.cos (2*s+ℓ) := by
    have := hb.2.2.1
    norm_num at this
    linarith
  have hS : Real.sin (2*s+ℓ)<698/1000 := by
    have := hb.2.1
    norm_num at this
    linarith
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_gt_three])
  have hcos := Real.cos_le_one s
  dsimp [dddF,κ,K]
  nlinarith

theorem ddF_zero_negative : ddF 0<0 := by
  have hs := Real.sin_ge_sub_cube (x := (21/200 : ℝ)) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (21/200 : ℝ))
  norm_num [ddF,ℓ,κ,K] at hs hc ⊢
  linarith

theorem F_concave : ConcaveOn ℝ (Icc 0 (1/3 : ℝ)) F := by
  have hm : AntitoneOn ddF (Icc 0 (1/3 : ℝ)) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun x _ => (F_derivatives x).2.2.continuousAt.continuousWithinAt
    · intro x hx
      exact (F_derivatives x).2.2
    · intro x hx
      exact (dddF_negative (Ioo_subset_Icc_self hx)).le
  apply concave_of_deriv2
    (fun x hx => (F_derivatives x).1)
    (fun x hx => (F_derivatives x).2.1)
  intro x hx
  exact (hm (by norm_num) hx hx.1).trans ddF_zero_negative.le

theorem F_zero_reserve : 1/25 < F 0 := by
  rw [F_error]
  have hs := sin_lower_seven (x := (21/200 : ℝ)) (by norm_num)
  have hc := cos_lower_six (x := (21/200 : ℝ)) (by norm_num)
  norm_num [error,ℓ] at hs hc ⊢
  linarith

theorem F_third_reserve : 1/25 < F (1/3) := by
  rw [F_error]
  have hst := sin_lower_seven (x := (263/600 : ℝ)) (by norm_num)
  have hct := cos_lower_six (x := (263/600 : ℝ)) (by norm_num)
  have hsr := sin_upper_five (x := (1/3 : ℝ)) (by norm_num)
  have hcr := cos_lower_six (x := (1/3 : ℝ)) (by norm_num)
  have ht := transport_trig (x := (263/600 : ℝ)) (by norm_num)
  have hr := transport_trig (x := (1/3 : ℝ)) (by norm_num)
  let B₀ : ℝ := (L-1/2)*
    (1-(263/600 : ℝ)^2/2+(263/600 : ℝ)^4/24-(263/600 : ℝ)^6/720)+
    ((263/600 : ℝ)-(263/600 : ℝ)^3/6+(263/600 : ℝ)^5/120-
      (263/600 : ℝ)^7/5040)/2-K
  let A₀ : ℝ :=
    ((263/600 : ℝ)-(263/600 : ℝ)^3/6+(263/600 : ℝ)^5/120-
      (263/600 : ℝ)^7/5040)+
    (1-(263/600 : ℝ)^2/2+(263/600 : ℝ)^4/24-(263/600 : ℝ)^6/720)-1
  have hA : A₀ ≤ Real.sin (263/600)+Real.cos (263/600)-1 := by
    dsimp [A₀]
    linarith
  have hA0 : 0≤A₀ := by norm_num [A₀]
  have hB : B₀ ≤ coefficient (263/600) := by
    unfold coefficient L K
    dsimp [B₀,L,K]
    linarith
  have hB0 : B₀≤0 := by norm_num [B₀,L,K]
  have hprodA := mul_le_mul hA hcr (by norm_num) (hA0.trans hA)
  have hprodB₁ := mul_le_mul_of_nonneg_right hB hr.2.2.1
  have hprodB₂ := mul_le_mul_of_nonpos_left hsr hB0
  have hnum : 1/25 < A₀*
      (1-(1/3 : ℝ)^2/2+(1/3 : ℝ)^4/24-(1/3 : ℝ)^6/720)+
      B₀*((1/3 : ℝ)-(1/3 : ℝ)^3/6+(1/3 : ℝ)^5/120) := by
    norm_num [A₀,B₀,L,K]
  dsimp [error,ℓ]
  norm_num at hprodA hprodB₁ hprodB₂ ⊢
  nlinarith

theorem F_reserve {s : ℝ} (hs : s∈Icc 0 (1/3 : ℝ)) : 1/25<F s :=
  concave_gt_of_endpoints F_concave hs F_zero_reserve F_third_reserve

/-- The unchanged original witnesses imply the strict transverse reserve
at the aligned comparison point. -/
theorem replacement_slack {H G A : SignedPoint} {s v : ℝ}
    (hH : H.y<9/10) (hA : A.a<283/200) (hG : L≤G.a)
    (hGa : G.a<283/200) (hg : 0≤G.y)
    (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10)
    (hHG : width v ≤ H.y+G.a*Real.sin v-G.y*Real.cos v)
    (hGA : width (v+s) ≤ A.a-G.a*Real.sin (v+s)+G.y*Real.cos (v+s)) :
    1/25 < H.y-(7/12)*Real.sin s+(A.a-1)*Real.cos s-width s := by
  obtain ⟨hlarge,hshort⟩ := original_pair_bounds hH hA hG hg hs hv hvs hHG hGA
  have hvcut := positive_error_cut hH hGa hg ⟨hv,by linarith⟩ hHG
  have hcs := (transport_trig_coarse (x := s) ⟨hs,by linarith⟩).1
  have hss := (transport_trig_coarse (x := s) ⟨hs,by linarith⟩).2.1
  have hcz := (transport_trig_coarse (x := v+s) ⟨by linarith,hvs⟩).1
  have hsz := (transport_trig_coarse (x := v+s) ⟨by linarith,hvs⟩).2.1
  have hw := mul_le_mul_of_nonneg_right hGA (show 0≤Real.cos s by linarith)
  have hsin : Real.sin (v+s)*Real.cos s-Real.sin v=
      Real.cos (v+s)*Real.sin s := by
    rw [Real.sin_add,Real.cos_add]
    linear_combination (Real.sin v)*Real.sin_sq_add_cos_sq s
  have hcos : Real.cos v-Real.cos (v+s)*Real.cos s=
      Real.sin (v+s)*Real.sin s := by
    rw [Real.sin_add,Real.cos_add]
    linear_combination (-Real.cos v)*Real.sin_sq_add_cos_sq s
  have hprodL := mul_nonneg (sub_nonneg.mpr hG) (mul_nonneg (show 0≤Real.cos (v+s) by linarith) hss)
  have hprodG := mul_nonneg hg (mul_nonneg hsz hss)
  have hbound : error (v+s) s ≤
      H.y-(7/12)*Real.sin s+(A.a-1)*Real.cos s-width s := by
    dsimp [error,coefficient,width,L,K] at *
    nlinarith
  have hmono := (error_increasing (s := s) ⟨hs,hshort.le⟩).monotoneOn
    (show s+ℓ∈Icc 0 (7/10 : ℝ) by constructor <;> dsimp [ℓ] <;> linarith)
    (show v+s∈Icc 0 (7/10 : ℝ) by constructor <;> linarith)
    (by linarith : s+ℓ≤v+s)
  have hF := F_reserve ⟨hs,hshort.le⟩
  rw [F_error] at hF
  exact hF.trans_le (hmono.trans hbound)

end WrongSign

/-- The nonpositive-total wrong-sign move of G to the flat point `G'`, stated with signed
coordinates and both original weak physical owners; `G'` takes the frame of A. There is no
opposite-side or E premise. -/
theorem wrong_sign_nonpositive_total_transport
    {q : ℝ} {H G A : SignedPoint} {s v : ℝ}
    (hq : q≤qCap)
    (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHc : H.Contained q) (hGc : G.Contained q) (hAc : A.Contained q)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (_hHy : 0≤H.y) (hGy : 0≤G.y) (hAy : 0≤A.y)
    (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10)
    (hHG : zeroFeasible H G v 0)
    (hGA : quarterFeasible G A (-(v+s)) 1) :
    let G' := SignedPoint.flat (-(A.a-1))
    G'.Sorted ∧ G'.Core ∧ G'.circle<q ∧
      zeroFeasible H G' (-s) 0 ∧
      quarterFeasible G' A 0 0 ∧ quarterFeasible G' A 0 1 ∧
      1/25 < zeroProjection H G' (-s) 0-edgeWidth (-s) := by
  obtain ⟨hHl,hHu,hHb⟩ := H.coordinate_bounds hHs hHcore hHc hq
  obtain ⟨hGl,hGu,hGb⟩ := G.coordinate_bounds hGs hGcore hGc hq
  obtain ⟨hAl,hAu,hAb⟩ := A.coordinate_bounds hAs hAcore hAc hq
  have hHwidth : WrongSign.width v ≤ H.y+G.a*Real.sin v-G.y*Real.cos v := by
    have h := hHG
    unfold zeroFeasible at h
    rw [edgeWidth_positive_formula ⟨hv,by linarith⟩] at h
    simp only [zeroProjection,Matrix.cons_val_zero] at h
    exact h
  have hAwidth : WrongSign.width (v+s) ≤
      A.a-G.a*Real.sin (v+s)+G.y*Real.cos (v+s) := by
    have h := hGA
    unfold quarterFeasible at h
    rw [edgeWidth_negative_formula ⟨by linarith,hvs⟩] at h
    simp only [quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero,Real.sin_neg,
      Real.cos_neg] at h
    unfold WrongSign.width
    linarith
  have hHy' : H.y<9/10 := (le_abs_self _).trans_lt hHb
  obtain ⟨hlarge,hshort⟩ := WrongSign.original_pair_bounds hHy' hAu hGl.le hGy hs hv
    hvs hHwidth hAwidth
  have hy : |-(A.a-1)|≤1/2 := by
    rw [abs_neg,abs_of_nonneg (by linarith : 0≤A.a-1)]
    linarith
  have hsort := SignedPoint.flat_sorted hy
  have hcore := SignedPoint.flat_on_core hy
  have hloss : (SignedPoint.flat (-(A.a-1))).circle<q := by
    have hA := hAc
    simp only [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] at hA
    simp only [SignedPoint.flat,SignedPoint.circle,abs_neg,
      abs_of_nonneg (by linarith : 0≤A.a-1)]
    nlinarith [sq_nonneg A.y]
  have hreserve := WrongSign.replacement_slack hHy' hAu hGl.le hGu hGy hs hv hvs
    hHwidth hAwidth
  have hactual : 1/25 < zeroProjection H (SignedPoint.flat (-(A.a-1))) (-s) 0-
      edgeWidth (-s) := by
    rw [edgeWidth_negative_formula ⟨hs,by linarith⟩]
    simp only [zeroProjection,SignedPoint.flat,Matrix.cons_val_zero,Real.sin_neg,Real.cos_neg]
    unfold WrongSign.width at hreserve
    linarith
  refine ⟨hsort,hcore,hloss,?_,?_,?_,hactual⟩
  · unfold zeroFeasible
    linarith
  · simp [quarterFeasible,quarterProjection,SignedPoint.flat]
  · simp [quarterFeasible,quarterProjection,SignedPoint.flat]

end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.WrongWordCircleSupport

open CommonQuarter

def X (p l x : ℝ) : ℝ := -p-l*Real.sin x
def Y (q l x : ℝ) : ℝ := q-l*Real.cos x
def mass (p q l : ℝ) : ℝ := p^2+q^2+l^2
def N (p q l x : ℝ) : ℝ :=
  CircularNorm.norm (mass p q l) (-2*l*q) (2*l*p) x

def base (c l x : ℝ) : ℝ := x+c+l*(1+Real.sin x+Real.cos x)/2
def axial (c p _q l x : ℝ) : ℝ := base c l x+X p l x*outerAxial
def diagonal (c p q l x : ℝ) : ℝ :=
  base c l x+(X p l x+Y q l x)*outerDiagonal
def full (c p q l x : ℝ) : ℝ :=
  base c l x-(X p l x+Y q l x)/2-CommonQuarter.radius*N p q l x

/-- Endpoint derivatives, with the positive axial denominator cleared. -/
def axialSlope (p q l x : ℝ) : ℝ :=
  (outerAxial+1/2)*Y q l x-X p l x/2
def diagonalSlope (p q l x : ℝ) : ℝ := Y q l x-X p l x

lemma energy_eq (p q l x : ℝ) :
    CircularNorm.energy (mass p q l) (-2*l*q) (2*l*p) x=
      (X p l x)^2+(Y q l x)^2 := by
  dsimp [CircularNorm.energy,mass,X,Y]
  linear_combination -(l^2)*(Real.sin_sq_add_cos_sq x)

lemma coefficient_identity (p q l x : ℝ) :
    p^2+q^2=l^2+(X p l x)^2+(Y q l x)^2+
      2*l*(X p l x*Real.sin x+Y q l x*Real.cos x) := by
  dsimp [X,Y]
  linear_combination (l^2)*(Real.sin_sq_add_cos_sq x)

lemma energy_pos {p q l x : ℝ} (_hl : 0<l) (hpq : p^2+q^2<l^2) :
    0<CircularNorm.energy (mass p q l) (-2*l*q) (2*l*p) x := by
  rw [energy_eq]
  by_contra! hn
  have hx : X p l x=0 := by nlinarith [sq_nonneg (Y q l x)]
  have hy : Y q l x=0 := by nlinarith [sq_nonneg (X p l x)]
  have hh := coefficient_identity p q l x
  rw [hx,hy] at hh
  nlinarith

lemma N_sq {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    (N p q l x)^2=(X p l x)^2+(Y q l x)^2 := by
  exact (CircularNorm.norm_sq (energy_pos hl hpq).le).trans (energy_eq p q l x)

lemma N_pos {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    0<N p q l x := CircularNorm.norm_pos (energy_pos hl hpq)

lemma N_lt_twice {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    N p q l x<2*l := by
  let t := p*Real.sin x-q*Real.cos x
  have hproj : t^2≤p^2+q^2 := by
    have hid : t^2+(p*Real.cos x+q*Real.sin x)^2=p^2+q^2 := by
      dsimp [t]
      linear_combination (p^2+q^2)*(Real.sin_sq_add_cos_sq x)
    nlinarith [sq_nonneg (p*Real.cos x+q*Real.sin x)]
  have ht : t<l := by nlinarith
  have hn := N_sq (x := x) hl hpq
  have hpos := N_pos (x := x) hl hpq
  have he : (X p l x)^2+(Y q l x)^2=p^2+q^2+l^2+2*l*t := by
    dsimp [X,Y,t]
    linear_combination (l^2)*(Real.sin_sq_add_cos_sq x)
  have hm := mul_pos hl (sub_pos.mpr ht)
  nlinarith

lemma full_expression (c p q l x : ℝ) :
    full c p q l x=x+c+(l+p-q)/2+l*(Real.sin x+Real.cos x)-CommonQuarter.radius*N p q l x := by
  dsimp [full,base,X,Y]
  ring

def fullD (p q l x : ℝ) : ℝ := 1+l*(Real.cos x-Real.sin x)-
  CommonQuarter.radius*CircularNorm.d1 (mass p q l) (-2*l*q) (2*l*p) x
def fullDD (p q l x : ℝ) : ℝ := -l*(Real.sin x+Real.cos x)-
  CommonQuarter.radius*CircularNorm.d2 (mass p q l) (-2*l*q) (2*l*p) x

lemma full_hasDerivAt {c p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    HasDerivAt (full c p q l) (fullD p q l x) x := by
  have hn := CircularNorm.norm_hasDerivAt (energy_pos (x := x) hl hpq)
  have hf : full c p q l=fun z => z+c+(l+p-q)/2+l*(Real.sin z+Real.cos z)-CommonQuarter.radius*N p q l z := by
    funext z
    exact full_expression c p q l z
  rw [hf]
  have h := ((((hasDerivAt_id' x).add_const c).add_const ((l+p-q)/2)).fun_add
    (((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul l)).fun_sub
      (hn.const_mul CommonQuarter.radius)
  exact h.congr_deriv (by unfold fullD; ring)

lemma fullD_hasDerivAt {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    HasDerivAt (fullD p q l) (fullDD p q l x) x := by
  have hn := CircularNorm.d1_hasDerivAt (energy_pos (x := x) hl hpq)
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul l).const_add
    1).fun_sub (hn.const_mul CommonQuarter.radius)
  exact h.congr_deriv (by unfold fullDD; ring)

lemma full_concave {c p q l : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    ConcaveOn ℝ (Icc 0 (7/10)) (full c p q l) := by
  apply concave_of_deriv2 (fun x _ => full_hasDerivAt hl hpq)
    (fun x _ => fullD_hasDerivAt hl hpq)
  intro x hx
  have hcoef : (-2*l*q)^2+(2*l*p)^2≤(mass p q l)^2 := by
    dsimp [mass]
    nlinarith [sq_nonneg (p^2+q^2-l^2)]
  have hcurv := CircularNorm.curvature_lower (energy_pos (x := x) hl hpq) hcoef
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hprod := mul_le_mul_of_nonneg_left hcurv hR.le
  have hnorm := mul_lt_mul_of_pos_left (N_lt_twice (x := x) hl hpq) hR
  have hRmass := mul_lt_mul_of_pos_right (show CommonQuarter.radius<2 by linarith [radius_bounds.2]) hl
  have hwidth := mul_le_mul_of_nonneg_left (positive_trig hx).2.2.2.2.2 hl.le
  change CommonQuarter.radius*(-N p q l x/4)≤CommonQuarter.radius*
    CircularNorm.d2 (mass p q l) (-2*l*q) (2*l*p) x at hprod
  dsimp [fullDD]
  nlinarith

/-- The circle support agrees with an endpoint whenever the force points
straight inward there. This is the exact Cauchy equality, not a bound. -/
lemma circle_support_eq {X Y a b : ℝ}
    (hc : (a+1/2)^2+(b+1/2)^2=Q0)
    (hcross : X*(b+1/2)-Y*(a+1/2)=0)
    (hdot : X*(a+1/2)+Y*(b+1/2)≤0) :
    -(X+Y)/2-CommonQuarter.radius*Real.sqrt (X^2+Y^2)=X*a+Y*b := by
  have hn := Real.sqrt_nonneg (X^2+Y^2)
  have hn2 := Real.sq_sqrt (show 0≤X^2+Y^2 by positivity)
  have hR : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  have hprod := mul_nonneg hR hn
  have hsq : (CommonQuarter.radius*Real.sqrt (X^2+Y^2))^2=
      (X*(a+1/2)+Y*(b+1/2))^2 := by
    rw [mul_pow,radius_sq,hn2,← hc]
    have hid : ((a+1/2)^2+(b+1/2)^2)*(X^2+Y^2)-
        (X*(a+1/2)+Y*(b+1/2))^2=(X*(b+1/2)-Y*(a+1/2))^2 := by ring
    rw [hcross] at hid
    nlinarith only [hid]
  have he : CommonQuarter.radius*Real.sqrt (X^2+Y^2)=-(X*(a+1/2)+Y*(b+1/2)) := by
    nlinarith
  linarith

lemma N_eq_sqrt {p q l x : ℝ} (_hl : 0<l) (_hpq : p^2+q^2<l^2) :
    N p q l x=Real.sqrt ((X p l x)^2+(Y q l x)^2) := by
  rw [N,CircularNorm.norm,energy_eq]

lemma coeff_not_both_nonneg {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2)
    (hx : x∈Icc 0 (7/10)) : ¬(0≤X p l x ∧ 0≤Y q l x) := by
  rintro ⟨hX,hY⟩
  have ht := positive_trig hx
  have hm := mul_nonneg hl.le (add_nonneg
    (mul_nonneg hX ht.2.2.1) (mul_nonneg hY (show 0≤Real.cos x by linarith [ht.1])))
  nlinarith [coefficient_identity p q l x,sq_nonneg (X p l x),sq_nonneg (Y q l x)]

lemma full_at_diagonal_event {c p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2)
    (hx : x∈Icc 0 (7/10)) (he : diagonalSlope p q l x=0) :
    full c p q l x=diagonal c p q l x := by
  have hXY : Y q l x=X p l x := by simpa [diagonalSlope,sub_eq_zero] using he
  have hX : X p l x<0 := by
    by_contra! hn
    exact coeff_not_both_nonneg hl hpq hx ⟨hn,by rw [hXY]; exact hn⟩
  have hd : 0≤outerDiagonal+1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  have hs := circle_support_eq (X := X p l x) (Y := Y q l x)
    (a := outerDiagonal) (b := outerDiagonal)
    (by nlinarith [diagonal_circle]) (by rw [hXY]; ring)
    (by rw [hXY]; nlinarith [mul_nonpos_of_nonpos_of_nonneg hX.le hd])
  rw [full,N_eq_sqrt hl hpq,diagonal]
  linarith

lemma full_at_axial_event {c p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2)
    (hx : x∈Icc 0 (7/10)) (he : axialSlope p q l x=0) :
    full c p q l x=axial c p q l x := by
  have hu : 0<outerAxial+1/2 := by linarith [outer_endpoint_bounds.1]
  have he' : (outerAxial+1/2)*Y q l x=X p l x/2 := by
    simpa [axialSlope,sub_eq_zero] using he
  have hX : X p l x<0 := by
    by_contra! hn
    have hY : 0≤Y q l x := by nlinarith
    exact coeff_not_both_nonneg hl hpq hx ⟨hn,hY⟩
  have hY : Y q l x<0 := by nlinarith
  have hs := circle_support_eq (X := X p l x) (Y := Y q l x)
    (a := outerAxial) (b := 0) (by simpa using axial_circle)
    (by nlinarith only [he'])
    (by nlinarith [mul_neg_of_neg_of_pos hX hu])
  rw [full,N_eq_sqrt hl hpq,axial]
  linarith

lemma outer_axial_lower {a b X Y : ℝ} (hc : OuterState a b)
    (hX : X≤0) (hder : 0≤(outerAxial+1/2)*Y-X/2) :
    X*outerAxial≤X*a+Y*b := by
  have hb := hc.1
  have hu : 0<outerAxial+1/2 := by linarith [outer_endpoint_bounds.1]
  have htangent : (outerAxial+1/2)*(a-outerAxial)+b/2≤0 := by
    nlinarith [hc.2.2,axial_circle,sq_nonneg (a-outerAxial),sq_nonneg b]
  have hp := mul_nonneg_of_nonpos_of_nonpos hX htangent
  have hd := mul_nonneg hder hb
  nlinarith

lemma outer_diagonal_lower {a b X Y : ℝ} (hc : OuterState a b)
    (hX : X≤0) (hder : Y-X≤0) : (X+Y)*outerDiagonal≤X*a+Y*b := by
  have hh := outer_bounds hc
  have hp := mul_le_mul_of_nonpos_left hh.2.2.2.2 hX
  have hq := mul_le_mul_of_nonpos_left hh.2.2.2.1 hder
  nlinarith

lemma outer_concave_lower {a b X Y m : ℝ} (hc : OuterState a b)
    (hX : 0≤X) (hA : m≤X*outerAxial) (hD : m≤(X+Y)*outerDiagonal) :
    m≤X*a+Y*b := by
  have hb := outer_bounds hc
  have hl : m≤X*Arithmetic.circleX (-1/2) CommonQuarter.radius 0+Y*0 := by
    rw [outer_branch_endpoints.1]
    linarith
  have hu : m≤X*Arithmetic.circleX (-1/2) CommonQuarter.radius outerDiagonal+Y*outerDiagonal := by
    rw [outer_branch_endpoints.2]
    linarith
  have hh := Arithmetic.circle_endpoints_lower (X := X) (Y := Y)
    hX (fun z hz => outer_radicand_pos hz) ⟨hc.1,hb.2.2.2.1⟩ hl hu
  rw [← outer_branch hc] at hh
  exact hh

/-- On the actual interior-support region, concavity joins the two
intrinsic derivative events. The left event may coincide with angle
zero when its full-circle value already has the required bound. -/
theorem interior_full_lower {c p q l m x : ℝ} (hl : 0<l)
    (hpq : p^2+q^2<l^2) (hx : x∈Icc 0 (7/10))
    (hA : ∀z∈Icc 0 (7/10),m<axial c p q l z)
    (hD : ∀z∈Icc 0 (7/10),m<diagonal c p q l z)
    (hleft : diagonalSlope p q l 0≤0 ∨ m<full c p q l 0)
    (hright : 0≤axialSlope p q l (7/10))
    (hd : 0<diagonalSlope p q l x) (ha : axialSlope p q l x<0) :
    m<full c p q l x := by
  have hAc : Continuous (axialSlope p q l) := by unfold axialSlope X Y; fun_prop
  have hDc : Continuous (diagonalSlope p q l) := by unfold diagonalSlope X Y; fun_prop
  obtain ⟨u,hu,heu⟩ := intermediate_value_Icc hx.2 hAc.continuousOn
    (show (0:ℝ)∈Icc (axialSlope p q l x) (axialSlope p q l (7/10)) from
      ⟨ha.le,hright⟩)
  have hu' : u∈Icc 0 (7/10) := ⟨hx.1.trans hu.1,hu.2⟩
  have hFu : m<full c p q l u := by
    rw [full_at_axial_event hl hpq hu' heu]
    exact hA u hu'
  obtain ⟨v,hv,hFv⟩ : ∃v,v∈Icc 0 x ∧ m<full c p q l v := by
    rcases hleft with hleft | hleft
    · obtain ⟨v,hv,hev⟩ := intermediate_value_Icc hx.1 hDc.continuousOn
        (show (0:ℝ)∈Icc (diagonalSlope p q l 0) (diagonalSlope p q l x) from
          ⟨hleft,hd.le⟩)
      have hv' : v∈Icc 0 (7/10) := ⟨hv.1,hv.2.trans hx.2⟩
      refine ⟨v,hv,?_⟩
      rw [full_at_diagonal_event hl hpq hv' hev]
      exact hD v hv'
    · exact ⟨0,⟨le_rfl,hx.1⟩,hleft⟩
  have hconc := (full_concave (c := c) hl hpq).subset
    (Icc_subset_Icc hv.1 hu.2) (convex_Icc v u)
  exact concave_gt_of_endpoints hconc ⟨hv.2,hu.1⟩ hFv hFu

/-- Complete actual-arc support from its two endpoint families and the
intrinsic norm transition. No angle event is a supplied parameter. -/
theorem actual_arc_lower {c p q l m a b x : ℝ} (hc : OuterState a b)
    (hl : 0<l) (hpq : p^2+q^2<l^2) (hx : x∈Icc 0 (7/10))
    (hA : ∀z∈Icc 0 (7/10),m<axial c p q l z)
    (hD : ∀z∈Icc 0 (7/10),m<diagonal c p q l z)
    (hleft : diagonalSlope p q l 0≤0 ∨ m<full c p q l 0)
    (hright : 0≤axialSlope p q l (7/10)) :
    m<base c l x+X p l x*a+Y q l x*b := by
  by_cases hX : 0≤X p l x
  · have hs := outer_concave_lower (Y := Y q l x)
      (m := min (X p l x*outerAxial) ((X p l x+Y q l x)*outerDiagonal)) hc hX
      (min_le_left _ _) (min_le_right _ _)
    have h1 := hA x hx
    have h2 := hD x hx
    dsimp only [axial] at h1
    dsimp only [diagonal] at h2
    have hmin : m-base c l x < min (X p l x*outerAxial) ((X p l x+Y q l x)*outerDiagonal) :=
      lt_min (by linarith) (by linarith)
    linarith
  have hX' : X p l x≤0 := (lt_of_not_ge hX).le
  by_cases hD' : diagonalSlope p q l x≤0
  · have hs := outer_diagonal_lower hc hX' hD'
    have hh := hD x hx
    dsimp [diagonal] at hh
    linarith
  by_cases hA' : 0≤axialSlope p q l x
  · have hs := outer_axial_lower hc hX' hA'
    have hh := hA x hx
    dsimp [axial] at hh
    linarith
  have hh := interior_full_lower hl hpq hx hA hD hleft hright
    (lt_of_not_ge hD') (lt_of_not_ge hA')
  have hs := outer_circle_lower (X := X p l x) (Y := Y q l x) hc
  rw [full,N_eq_sqrt hl hpq] at hh
  linarith

end SquaresInCircles.Eight.WrongWordCircleSupport
end
end
end
