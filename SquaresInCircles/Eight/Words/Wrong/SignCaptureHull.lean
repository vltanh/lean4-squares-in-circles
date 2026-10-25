module

public import SquaresInCircles.Eight.Owners.Endpoint.RotationPenalty
public import SquaresInCircles.Eight.Owners.SpanNormBounds

/-!
# Eight squares: one-variable inequalities for the original wrong-sign capture hull

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
        (Real.hasDerivAt_sin z) using 1 <;> ring
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
