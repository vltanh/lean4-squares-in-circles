module

public import SquaresInCircles.Eight.TableFree.OneNegativeAnchorCharge
public import SquaresInCircles.Eight.TableFree.PowerTailBounds

/-!
# The whole-interval middle endpoint for one negative BT contact

Uncompiled source draft of equations (28)--(35) in
`HAND_G5_GLOBAL_PRIMARY_ENTRY_ONE_NEGATIVE_BT_ANCHOR_ORDER.md`.
The certificate is the displayed degree-ten rational polynomial, with
one coefficient norm on the whole centered interval `|x|≤41/100`.
Its positive quadratic lower bound is proved by completing a square.
Positive scalar tangents then transfer the certificate directly to the
two original trigonometric norms, retaining their exact common radius.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.OneNegativeAnchorPolynomial
open PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open Polynomial PowerTailBounds

abbrev R : ℝ := EndpointRotationPenalty.R
abbrev p : ℝ := OneNegativeAnchorCharge.p
abbrev S0 : ℝ := EndpointBudgetScalars.S0

def MB (l mu L : ℝ) : ℝ :=
  R*(pairNorm 1 l (-L)+pairNorm mu l 0)-1/2-3*mu/2-2*l-Real.cos L+
    (1-mu)*(39/250)+p*L-S0

def MG (l mu L : ℝ) : ℝ :=
  R*(pairNorm 1 l 0+pairNorm mu l (-L))-3/2-3*mu/2-l-l*Real.cos L+
    (1-mu)*(39/250)+p*L-S0

def Rplus : ℚ := 197878751/100000000
def Sminus : ℚ := 41502562/100000000
def center : ℚ := 29/100
def span : ℚ := 41/100

def z : ℚ[X] := C center+X
def weight : ℚ[X] := C (59/100)+C (1/2)*z
def r0 : ℚ[X] := C (1241058016/1000000000)+
  C (296118308/1000000000)*X+C (65393376/1000000000)*X^2
def r1 : ℚ[X] := C (1058241574/1000000000)-
  C (453379807/1000000000)*X-C (332448780/1000000000)*X^2

def S7 : ℚ[X] := z-C (1/6)*z^3+C (1/120)*z^5-C (1/5040)*z^7
def C6 : ℚ[X] := 1-C (1/2)*z^2+C (1/24)*z^4-C (1/720)*z^6
def radicandNegative : ℚ[X] := 1+weight^2-C 2*weight*S7
def radicandZero : ℚ[X] := 1+weight^2
def target : ℚ[X] :=
  C 2+C 2*weight+C6+C (Sminus+1/250)-C (41/40)*z
def certificate : ℚ[X] :=
  C 2*r0*r1*target-C Rplus*
    (r1*(radicandZero+r0^2)+r0*(radicandNegative+r1^2))

def sine7 (t : ℝ) : ℝ := t-t^3/6+t^5/120-t^7/5040
def cosine6 (t : ℝ) : ℝ := 1-t^2/2+t^4/24-t^6/720

theorem radius_reserves : R<(Rplus:ℝ) ∧ (Sminus:ℝ)<S0 := by
  constructor
  · simpa only [Rplus,Rat.cast_div,Rat.cast_ofNat] using OneNegativeAnchorCharge.radius_upper
  · have hs := Real.sq_sqrt (show 0≤qCap-1 by norm_num [qCap])
    have hn := Real.sqrt_nonneg (qCap-1)
    dsimp [Sminus,S0,EndpointBudgetScalars.S0,qCap] at *
    nlinarith

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem expansion_identity :
    certificate=C (certificate.coeff 0)+C (certificate.coeff 1)*X+
      C (certificate.coeff 2)*X^2+tail certificate 3 8 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem coefficient_reserves :
    (51/100000 : ℚ)<certificate.coeff 0 ∧
      |certificate.coeff 1|<521/1000000 ∧
      (1009/10000 : ℚ)<certificate.coeff 2-
        PowerTailBounds.norm certificate 3 8 span := by decide

/-- One completed square proves the strict degree-ten reserve for every
real point of the centered interval. -/
theorem polynomial_positive {x : ℝ} (hx : |x|≤(span:ℝ)) :
    (509/1000000 : ℝ)<aeval x certificate := by
  have hbound := quadratic_lower expansion_identity
    (show (0:ℚ)≤span by norm_num [span]) hx
  have hc0 : (51/100000 : ℝ)<(certificate.coeff 0:ℝ) := by
    exact_mod_cast coefficient_reserves.1
  have hc1 : |(certificate.coeff 1:ℝ)|<521/1000000 := by
    exact_mod_cast coefficient_reserves.2.1
  have hc2 : (1009/10000 : ℝ)<(certificate.coeff 2:ℝ)-
      (PowerTailBounds.norm certificate 3 8 span:ℝ) := by
    exact_mod_cast coefficient_reserves.2.2
  have hlinear : -(521/1000000)*|x|≤(certificate.coeff 1:ℝ)*x := by
    have hm := mul_le_mul_of_nonneg_right hc1.le (abs_nonneg x)
    rw [← abs_mul] at hm
    exact (abs_le.mp hm).1
  have hquadratic := mul_le_mul_of_nonneg_right hc2.le (sq_nonneg x)
  nlinarith [sq_nonneg (|x|-(521/201800 : ℝ)),sq_abs x]

theorem auxiliary_positive {x : ℝ} (hx : |x|≤(span:ℝ)) :
    (102/125 : ℝ)<aeval x r0 ∧ (102/125 : ℝ)<aeval x r1 := by
  have hx' : -(41/100 : ℝ)≤x ∧ x≤41/100 := by
    simpa only [span,Rat.cast_div,Rat.cast_ofNat] using abs_le.mp hx
  have hx2 : x^2≤(41/100 : ℝ)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg x) hx 2
    simpa only [sq_abs,span,Rat.cast_div,Rat.cast_ofNat] using hh
  simp only [r0,r1,map_add,map_sub,map_mul,map_pow,aeval_C,aeval_X]
  norm_num
  constructor <;> nlinarith [sq_nonneg x,hx'.1,hx'.2]

@[simp] theorem S7_eval (x : ℝ) : aeval x S7=sine7 (aeval x z) := by
  simp [S7,sine7]
  ring

@[simp] theorem C6_eval (x : ℝ) : aeval x C6=cosine6 (aeval x z) := by
  simp [C6,cosine6]
  ring

theorem certificate_eval (x : ℝ) : aeval x certificate=
    2*aeval x r0*aeval x r1*
      (2+2*aeval x weight+cosine6 (aeval x z)+(Sminus:ℝ)+1/250-p*aeval x z)-
    (Rplus:ℝ)*(aeval x r1*(1+(aeval x weight)^2+(aeval x r0)^2)+
      aeval x r0*(1+(aeval x weight)^2-
        2*aeval x weight*sine7 (aeval x z)+(aeval x r1)^2)) := by
  simp [certificate,target,radicandZero,radicandNegative,p,OneNegativeAnchorCharge.p]
  ring

/-- The two positive tangent masses are used algebraically; they need not
approximate either original norm. -/
theorem two_norms {n0 n1 A0 A1 e m0 m1 : ℝ}
    (hn0 : 0≤n0) (hn1 : 0≤n1) (hA0 : n0^2≤A0) (hA1 : n1^2≤A1)
    (hm0 : 0<m0) (hm1 : 0<m1)
    (hcertificate : 0<2*m0*m1*e-(Rplus:ℝ)*
      (m1*(A0+m0^2)+m0*(A1+m1^2))) :
    R*(n0+n1)<e := by
  have hRplus : 0≤(Rplus:ℝ) := by norm_num [Rplus]
  have h0 : 2*m0*n0≤A0+m0^2 := by nlinarith [sq_nonneg (n0-m0)]
  have h1 : 2*m1*n1≤A1+m1^2 := by nlinarith [sq_nonneg (n1-m1)]
  have h0w := mul_le_mul_of_nonneg_left h0 (mul_nonneg hRplus hm1.le)
  have h1w := mul_le_mul_of_nonneg_left h1 (mul_nonneg hRplus hm0.le)
  have hR := mul_le_mul_of_nonneg_right radius_reserves.1.le (add_nonneg hn0 hn1)
  have hscale : 0<2*m0*m1 := by positivity
  have hRw := mul_le_mul_of_nonneg_left hR hscale.le
  apply (mul_lt_mul_left hscale).mp
  nlinarith

theorem negative_norm_upper {l L : ℝ} (hl : 0<l) (hL : L∈Icc 0 frameCap) :
    (pairNorm 1 l (-L))^2≤1+l^2-2*l*sine7 L := by
  have hN := pairNorm_sq (show (0:ℝ)<1 by norm_num) hl
    (show |-L|≤frameCap by rw [abs_neg,abs_of_nonneg hL.1]; exact hL.2)
  have hm := mul_le_mul_of_nonneg_left (sin_lower_seven hL.1)
    (show 0≤2*l by positivity)
  simp only [pairEnergy,pairProduct,Real.sin_neg,one_pow,one_mul] at hN
  dsimp [sine7]
  nlinarith

/-- The exact varying-weight endpoint is below `.004` on the complete
large interval; all Taylor directions and radical comparisons are
proved inside this theorem. -/
theorem large_MB {L : ℝ} (hL : L∈Icc (1/25 : ℝ) frameCap) :
    MB (59/100+L/2) 1 L<(1/250 : ℝ) := by
  let x : ℝ := L-29/100
  let l : ℝ := 59/100+L/2
  have hx : |x|≤(span:ℝ) := by
    rw [abs_le]
    dsimp [x,span,frameCap] at *
    constructor <;> linarith [hL.1,hL.2]
  have hz : aeval x z=L := by simp [z,center,x]
  have hw : aeval x weight=l := by
    simp [weight,hz,l] <;> ring
  have hL' : L∈Icc 0 frameCap := ⟨by linarith [hL.1],hL.2⟩
  have hl : 0<l := by dsimp [l]; linarith [hL.1]
  have hP : 0<aeval x certificate := by linarith [polynomial_positive hx]
  rw [certificate_eval,hz,hw] at hP
  obtain ⟨h0,h1⟩ := auxiliary_positive hx
  have hNZ : (pairNorm 1 l 0)^2=1+l^2 := by
    simpa [pairEnergy,pairProduct] using pairNorm_sq (show (0:ℝ)<1 by norm_num) hl
      (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hNN := negative_norm_upper hl hL'
  have hnorm := two_norms (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hNZ.le hNN (by linarith : 0<aeval x r0) (by linarith : 0<aeval x r1) hP
  have hcos := cos_lower_six hL'.1
  have hS := radius_reserves.2
  change MB l 1 L<(1/250 : ℝ)
  dsimp [MB,cosine6] at hnorm ⊢
  norm_num
  linarith

theorem MG_le_MB {l L : ℝ} (hl : l≤1) : MG l 1 L≤MB l 1 L := by
  have hm := mul_nonneg (sub_nonneg.mpr hl)
    (show 0≤1-Real.cos L by linarith [Real.cos_le_one L])
  dsimp [MG,MB]
  norm_num
  nlinarith

theorem large_endpoints {L : ℝ} (hL : L∈Icc (1/25 : ℝ) frameCap) :
    MB (59/100+L/2) 1 L<(1/250 : ℝ) ∧
      MG (59/100+L/2) 1 L<(1/250 : ℝ) := by
  have hB := large_MB hL
  exact ⟨hB,(MG_le_MB (by dsimp [frameCap] at hL; linarith [hL.2])).trans_lt hB⟩

def negativeSupport (a b c t : ℝ) : ℝ :=
  R*pairNorm a b (-t)-c*Real.cos t

/-- Negative-angle convexity remains valid when the cosine coefficient
is only the smaller norm coefficient.  The strict gap is `.7648-.762`.
This is also the convexity used by the original A-frame concentration. -/
theorem negativeSupport_convex {a b c : ℝ} (ha : 0<a) (hb : 0<b) (hbc : b≤c) :
    ConvexOn ℝ (Icc 0 frameCap) (negativeSupport a b c) := by
  let d (t : ℝ) := -R*normD1 a b (-t)+c*Real.sin t
  let dd (t : ℝ) := R*normD2 a b (-t)+c*Real.cos t
  have hd (t : ℝ) (ht : t∈Icc 0 frameCap) :
      HasDerivAt (negativeSupport a b c) (d t) t := by
    have hn := (pairNorm_hasDerivAt ha hb
      (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t
        (hasDerivAt_id t).neg
    convert (hn.const_mul R).sub ((Real.hasDerivAt_cos t).const_mul c) using 1
    · rfl
    · dsimp [d]
      ring
  have hdd (t : ℝ) (ht : t∈Icc 0 frameCap) : HasDerivAt d (dd t) t := by
    have hn := (normD1_hasDerivAt ha hb
      (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)).comp t
        (hasDerivAt_id t).neg
    convert (hn.const_mul (-R)).add ((Real.hasDerivAt_sin t).const_mul c) using 1
    · rfl
    · dsimp [dd]
      ring
  have hswap : curvatureZero R a b=curvatureZero R b a := by
    dsimp [curvatureZero,pairProduct]
    rw [pairNorm_symm a b 0]
    ring
  have hzero : curvatureZero R a b<(381/500)*b := by
    rw [hswap,(curvature_constants_normalize (R := R) hb ha).1]
    exact mul_lt_mul_of_pos_left
      (shapeC0p_lt EndpointRotationPenalty.R_sq.le) hb
  have hnonneg (t : ℝ) (ht : t∈Icc 0 frameCap) : 0≤dd t := by
    have hcurv := curvature_negative_upper EndpointRotationPenalty.R_nonneg ha hb
      (show -t∈Icc (-frameCap) 0 by constructor <;> linarith [ht.1,ht.2])
    have hc := (transport_trig ht).1
    have hcos := mul_lt_mul_of_pos_left hc hb
    have hcoefficient := mul_le_mul_of_nonneg_right hbc (show 0≤Real.cos t by linarith)
    dsimp [dd,curvature] at hcurv ⊢
    nlinarith
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 frameCap)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => (hdd t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => hnonneg t (interior_subset ht))

theorem add_affine_convex {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Icc 0 frameCap) g) (a b : ℝ) :
    ConvexOn ℝ (Icc 0 frameCap) (fun t => g t+a*t+b) := by
  have ha := (affine_concave (-a) (-b) 0 frameCap).neg
  convert hg.add ha using 1
  funext t
  simp only [Pi.add_apply,Pi.neg_apply]
  ring

theorem MB_convex {l mu : ℝ} (hl : 0<l) (hmu : 0<mu) (hl1 : l≤1) :
    ConvexOn ℝ (Icc 0 frameCap) (MB l mu) := by
  have hc := negativeSupport_convex (show (0:ℝ)<1 by norm_num) hl hl1
  convert add_affine_convex hc p
    (R*pairNorm mu l 0-1/2-3*mu/2-2*l+(1-mu)*(39/250)-S0) using 1
  funext L
  dsimp [MB,negativeSupport]
  ring

theorem MG_convex {l mu : ℝ} (hl : 0<l) (hmu : 0<mu) :
    ConvexOn ℝ (Icc 0 frameCap) (MG l mu) := by
  have hc := negativeSupport_convex hmu hl (show l≤l from le_rfl)
  convert add_affine_convex hc p
    (R*pairNorm 1 l 0-3/2-3*mu/2-l+(1-mu)*(39/250)-S0) using 1
  funext L
  dsimp [MG,negativeSupport]
  ring

theorem small_norm_bounds :
    pairNorm 1 (121/200) 0<(1168770722/1000000000 : ℝ) ∧
      pairNorm (47/50) (121/200) 0<(1117866272/1000000000 : ℝ) ∧
      pairNorm 1 (121/200) (-(1/25))<(1147884100/1000000000 : ℝ) ∧
      pairNorm (47/50) (121/200) (-(1/25))<(1097333647/1000000000 : ℝ) := by
  have hz : |(0:ℝ)|≤frameCap := by norm_num [frameCap]
  have he : |-(1/25 : ℝ)|≤frameCap := by norm_num [frameCap]
  have h1 := pairNorm_sq (show (0:ℝ)<1 by norm_num)
    (show (0:ℝ)<121/200 by norm_num) hz
  have h2 := pairNorm_sq (show (0:ℝ)<47/50 by norm_num)
    (show (0:ℝ)<121/200 by norm_num) hz
  have h3 := pairNorm_sq (show (0:ℝ)<1 by norm_num)
    (show (0:ℝ)<121/200 by norm_num) he
  have h4 := pairNorm_sq (show (0:ℝ)<47/50 by norm_num)
    (show (0:ℝ)<121/200 by norm_num) he
  have hs := sin_lower_seven (show (0:ℝ)≤1/25 by norm_num)
  simp only [pairEnergy,pairProduct,Real.sin_zero,Real.sin_neg] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4 hs
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

theorem small_zero :
    MB (121/200) (47/50) 0< -(8968/10000000 : ℝ) ∧
      MG (121/200) (47/50) 0< -(8968/10000000 : ℝ) := by
  have hnorm : pairNorm 1 (121/200) 0+pairNorm (47/50) (121/200) 0≤
      (1168770722/1000000000 : ℝ)+1117866272/1000000000 := by
    linarith [small_norm_bounds.1,small_norm_bounds.2.1]
  have hm := mul_le_mul_of_nonneg_left hnorm EndpointRotationPenalty.R_nonneg
  have hr := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1168770722/1000000000+1117866272/1000000000 by norm_num)
  have hs := radius_reserves.2
  simp only [MB,MG,neg_zero,Real.cos_zero,mul_zero,add_zero,mul_one]
  norm_num [Rplus,Sminus,p,OneNegativeAnchorCharge.p] at hr hs ⊢
  constructor <;> linarith

theorem small_cap :
    MB (121/200) (47/50) (1/25)< -(4271/10000000 : ℝ) ∧
      MG (121/200) (47/50) (1/25)< -(426/10000000 : ℝ) := by
  have hnormB : pairNorm 1 (121/200) (-(1/25))+pairNorm (47/50) (121/200) 0≤
      (1147884100/1000000000 : ℝ)+1117866272/1000000000 := by
    linarith [small_norm_bounds.2.2.1,small_norm_bounds.2.1]
  have hnormG : pairNorm 1 (121/200) 0+pairNorm (47/50) (121/200) (-(1/25))≤
      (1168770722/1000000000 : ℝ)+1097333647/1000000000 := by
    linarith [small_norm_bounds.1,small_norm_bounds.2.2.2]
  have hmB := mul_le_mul_of_nonneg_left hnormB EndpointRotationPenalty.R_nonneg
  have hmG := mul_le_mul_of_nonneg_left hnormG EndpointRotationPenalty.R_nonneg
  have hrB := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1147884100/1000000000+1117866272/1000000000 by norm_num)
  have hrG := mul_lt_mul_of_pos_right radius_reserves.1
    (show (0:ℝ)<1168770722/1000000000+1097333647/1000000000 by norm_num)
  have hs := radius_reserves.2
  have hc := cos_lower_six (show (0:ℝ)≤1/25 by norm_num)
  dsimp [MB,MG]
  norm_num [Rplus,Sminus,p,OneNegativeAnchorCharge.p] at hrB hrG hs hc ⊢
  constructor <;> linarith

/-- Both constant-family endpoints are strictly negative throughout the
whole short interval, including both weak interval endpoints. -/
theorem small_endpoints {L : ℝ} (hL : L∈Icc 0 (1/25 : ℝ)) :
    MB (121/200) (47/50) L<0 ∧ MG (121/200) (47/50) L<0 := by
  have hB := (MB_convex (show (0:ℝ)<121/200 by norm_num)
    (show (0:ℝ)<47/50 by norm_num) (show (121/200:ℝ)≤1 by norm_num)).neg
  have hG := (MG_convex (show (0:ℝ)<121/200 by norm_num)
    (show (0:ℝ)<47/50 by norm_num)).neg
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hcap : (1/25:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hminB := hB.min_le_of_mem_Icc hzero hcap hL
  have hminG := hG.min_le_of_mem_Icc hzero hcap hL
  have hpB : 0<min (-MB (121/200) (47/50) 0) (-MB (121/200) (47/50) (1/25)) := by
    exact lt_min (by linarith [small_zero.1]) (by linarith [small_cap.1])
  have hpG : 0<min (-MG (121/200) (47/50) 0) (-MG (121/200) (47/50) (1/25)) := by
    exact lt_min (by linarith [small_zero.2]) (by linarith [small_cap.2])
  exact ⟨by linarith [hpB.trans_le hminB],by linarith [hpG.trans_le hminG]⟩

end SquaresInCircles.Eight.TableFree.OneNegativeAnchorPolynomial
