module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2CommonEndpointSlopes
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2AffectedNorm

/-!
# Removing the merged negative total

Uncompiled transcription of Section 6 of the common-gain companion.
The secant term is concave in tan S. The unaffected term has a convex
first derivative and a negative right derivative on the long interval;
on the short interval its ordinary second derivative is negative.
Both arguments retain the complete continuous interval [0,t].
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
open Candidate Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryCurvatureBounds
open OrdinaryAngleConcavity OrdinaryNegativeSlope SecantNormCurvature

def unaffected (k t s : ℝ) : ℝ := F k s+V R k 1 (t-s)
def unaffectedFirst (k t s : ℝ) : ℝ := F1 k s-Vd R k 1 (t-s)
def unaffectedSecond (k t s : ℝ) : ℝ := F2 k s+curvature R k 1 (s-t)-Real.cos (t-s)
def unaffectedThird (k t s : ℝ) : ℝ := F3 k s+curvatureD R k 1 (s-t)-Real.sin (t-s)
def affectedAffine (k t x : ℝ) : ℝ :=
  (K+Real.sin t)*x+Real.cos t-1+R*Real.sqrt (k^2+1)-R*NegativeAPositiveTD.AffectedNorm.norm k t x

theorem unaffected_derivative {k t s : ℝ} (hk : 0<k) (ht : t∈Icc 0 frameCap)
    (hs : s∈Icc 0 t) : HasDerivAt (unaffected k t) (unaffectedFirst k t s) s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have hd : t-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [ht.2,hs.1]⟩
  have hh := (V_hasDerivAt (R:=R) hk (by norm_num : (0:ℝ)<1) hd).comp s
    ((hasDerivAt_id s).const_sub t)
  convert (F_derivative (k:=k) hs').add hh using 1
  · rfl
  · dsimp [unaffectedFirst]
    ring

theorem unaffectedFirst_derivative {k t s : ℝ} (hk : 0<k) (ht : t∈Icc 0 frameCap)
    (hs : s∈Icc 0 t) : HasDerivAt (unaffectedFirst k t) (unaffectedSecond k t s) s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have hd : t-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [ht.2,hs.1]⟩
  have hh := (Vd_hasDerivAt (R:=R) hk (by norm_num : (0:ℝ)<1) hd).comp s
    ((hasDerivAt_id s).const_sub t)
  convert (F1_derivative (k:=k) hs').sub hh using 1
  · rfl
  · simp only [neg_sub,one_mul]
    dsimp [unaffectedSecond]
    ring

theorem unaffectedSecond_derivative {k t s : ℝ} (hk : 0<k) (ht : t∈Icc 0 frameCap)
    (hs : s∈Icc 0 t) : HasDerivAt (unaffectedSecond k t) (unaffectedThird k t s) s := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have harg : |s-t|≤frameCap := abs_le.mpr ⟨by linarith [ht.2,hs.1],by linarith [hs.2,ht.1,ht.2]⟩
  have hc := (curvature_hasDerivAt (R:=R) hk (by norm_num : (0:ℝ)<1) harg).comp s
    ((hasDerivAt_id s).sub_const t)
  have hcos := (Real.hasDerivAt_cos (t-s)).comp s ((hasDerivAt_id s).const_sub t)
  convert ((F2_derivative (k:=k) hs').add hc).sub hcos using 1
  · rfl
  · dsimp [unaffectedThird]
    ring

theorem unaffectedThird_positive {k t s : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000)) (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t) :
    (197/250:ℝ)<unaffectedThird k t s := by
  have hk0 : 0<k := by linarith [hk.1]
  have hk1 : k≤1 := by linarith [hk.2]
  have hratio : (1:ℝ)≤2*k := by linarith [hk.1]
  have harg : s-t∈Icc (-frameCap) frameCap :=
    ⟨by linarith [ht.2,hs.1],by linarith [hs.2,ht.1,ht.2]⟩
  have hz : (0:ℝ)∈Icc (-frameCap) frameCap := by norm_num [frameCap]
  have hc := NegativeAPositiveTD.Curvature.curvatureD_antitone_signed hk0 hk1 hratio
    harg hz (show s-t≤0 by linarith [hs.2])
  rw [curvatureD_zero] at hc
  have hconst := (NegativeAPositiveTD.Curvature.universal_constants hk0 hk1 hratio).2.1
  have hf := third_lower hk ⟨hs.1,hs.2.trans ht.2⟩
  have hy := sine_domain (show t-s∈Icc 0 frameCap by
    exact ⟨by linarith [hs.2],by linarith [ht.2,hs.1]⟩)
  dsimp [unaffectedThird]
  linarith [hy.2]

/-- A convex derivative with a nonpositive right endpoint can only
produce a maximum in the interior. This uses its two-point convexity,
not a root search or an assumed sign-change count. -/
theorem endpoint_min_of_convex_derivative {f g : ℝ→ℝ} {t s : ℝ}
    (ht : 0≤t) (hs : s∈Icc 0 t)
    (hd : ∀x∈Icc 0 t,HasDerivAt f (g x) x)
    (hc : ConcaveOn ℝ (Icc 0 t) (fun x => -g x)) (hgt : g t≤0) :
    min (f 0) (f t)≤f s := by
  by_cases hgs : g s≤0
  · have hanti : AntitoneOn f (Icc s t) := by
      apply antiOn_of_hasDeriv_nonpos
      · intro x hx
        exact (hd x ⟨hs.1.trans hx.1,hx.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact hd x ⟨hs.1.trans hx.1.le,hx.2.le⟩
      · intro x hx
        have hh := hc.min_le_of_mem_Icc hs ⟨ht,le_rfl⟩ (Ioo_subset_Icc_self hx)
        have hm : 0≤ min (-g s) (-g t) := le_min (by linarith) (by linarith)
        linarith
    exact (min_le_right (f 0) (f t)).trans (hanti ⟨le_rfl,hs.2⟩ ⟨hs.2,le_rfl⟩ hs.2)
  · have hpos : 0<g s := lt_of_not_ge hgs
    have hmono : MonotoneOn f (Icc 0 s) := by
      apply monoOn_of_hasDeriv_nonneg
      · intro x hx
        exact (hd x ⟨hx.1,hx.2.trans hs.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        exact hd x ⟨hx.1.le,hx.2.le.trans hs.2⟩
      · intro x hx
        have hx' : x∈Icc 0 t := ⟨hx.1.le,hx.2.le.trans hs.2⟩
        have hh := hc.min_le_of_mem_Icc hx' ⟨ht,le_rfl⟩
          (show s∈Icc x t from ⟨hx.2.le,hs.2⟩)
        have hleft : g s≤g x := by
          by_contra hn
          have hm : -g s< min (-g x) (-g t) := lt_min (by linarith) (by linarith)
          linarith
        linarith
    exact (min_le_left (f 0) (f t)).trans (hmono ⟨le_rfl,hs.1⟩ ⟨hs.1,le_rfl⟩ hs.1)

theorem unaffected_endpoint_long {k t s : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc (3/20:ℝ) frameCap) (hs : s∈Icc 0 t) :
    min (V R k 1 t) (F k t)≤F k s+V R k 1 (t-s) := by
  have hk0 : 0<k := by linarith [hk.1]
  have ht' : t∈Icc 0 frameCap := ⟨by linarith [ht.1],ht.2⟩
  have hc : ConcaveOn ℝ (Icc 0 t) (fun s => -unaffectedFirst k t s) := by
    apply concave_of_deriv2
      (fun x hx => (unaffectedFirst_derivative hk0 ht' hx).neg)
      (fun x hx => (unaffectedSecond_derivative hk0 ht' hx).neg)
    intro x hx
    have hh := unaffectedThird_positive hk ht' hx
    linarith
  have hright : unaffectedFirst k t t≤0 := by
    have hF := first_upper_long hk ht
    have hV := zero_slope_lower hk
    simp only [unaffectedFirst,sub_self]
    linarith
  have hh := endpoint_min_of_convex_derivative ht'.1 hs
    (fun x hx => unaffected_derivative hk0 ht' hx) hc hright
  simpa [unaffected,F_zero] using hh

theorem unaffected_endpoint_short {k t s : ℝ}
    (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc (0:ℝ) (3/20)) (hs : s∈Icc 0 t) :
    min (V R k 1 t) (F k t)≤F k s+V R k 1 (t-s) := by
  have hk0 : 0<k := by linarith [hk.1]
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by norm_num [frameCap]; linarith [ht.2]⟩
  have hc : ConcaveOn ℝ (Icc 0 t) (unaffected k t) := by
    apply concave_of_deriv2 (fun x hx => unaffected_derivative hk0 ht' hx)
      (fun x hx => unaffectedFirst_derivative hk0 ht' hx)
    intro x hx
    have hF := second_negative_short hk ⟨hx.1,hx.2.trans ht.2⟩
    have hV := mixedN_second_lt (Real.sqrt_nonneg qCap) radius_sq.le hk0
      (show k≤1 by linarith [hk.2]) (show (1:ℝ)≤2*k by linarith [hk.1])
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
      (show t-x∈Icc 0 frameCap by exact ⟨by linarith [hx.2],by linarith [ht'.2,hx.1]⟩)
    simp only [zero_sub,neg_sub,one_mul] at hV
    dsimp [unaffectedSecond]
    linarith
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,ht.1⟩ ⟨ht.1,le_rfl⟩ hs
  simpa [unaffected,F_zero] using hh

theorem affected_identity {k t s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t) :
    F k s+V R k (secant s) (t-s)=affectedAffine k t (Real.tan s) := by
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have hc : 0<Real.cos s := by linarith [(transport_trig hs').1]
  have hk0 : 0<k := by linarith [hk.1]
  have hq : 0<secant s := by linarith [(full_secant_domain hs').1]
  have hd : |-(t-s)|≤frameCap := by
    rw [abs_neg,abs_of_nonneg (by linarith [hs.2])]
    linarith [ht.2,hs.1]
  have hn := pairNorm_pos hk0 hq hd
  have hn2 := pairNorm_sq hk0 hq hd
  have hv := NegativeAPositiveTD.AffectedNorm.second_coordinate_pos
    (show k∈Icc (0:ℝ) (71/50) by exact ⟨hk0.le,by linarith [hk.2]⟩) ht
  have hN := NegativeAPositiveTD.AffectedNorm.norm_pos (x:=Real.tan s) hv
  have hN2 := NegativeAPositiveTD.AffectedNorm.norm_sq_expanded k t (Real.tan s)
  have he : (pairNorm k (secant s) (-(t-s)))^2=
      (NegativeAPositiveTD.AffectedNorm.norm k t (Real.tan s))^2 := by
    rw [hn2,hN2]
    dsimp [pairEnergy,pairProduct,secant]
    rw [Real.sin_neg,Real.sin_sub,Real.tan_eq_sin_div_cos]
    field_simp [hc.ne']
    linear_combination -Real.sin_sq_add_cos_sq s
  have hnorm : pairNorm k (secant s) (-(t-s))=
      NegativeAPositiveTD.AffectedNorm.norm k t (Real.tan s) := by nlinarith
  have hzero : pairNorm k (secant s) 0=supportNorm k s := by
    simp [pairNorm,supportNorm]
  have hcos : secant s*Real.cos (t-s)=Real.cos t+Real.sin t*Real.tan s := by
    rw [Real.cos_sub,Real.tan_eq_sin_div_cos]
    dsimp [secant]
    field_simp [hc.ne']
  dsimp [F,normalized,V,affectedAffine]
  rw [hnorm,hzero]
  nlinarith only [hcos]

theorem affected_endpoint {k t s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t) :
    min (V R k 1 t) (F k t)≤F k s+V R k (secant s) (t-s) := by
  have hv := NegativeAPositiveTD.AffectedNorm.second_coordinate_pos
    (show k∈Icc (0:ℝ) (71/50) by exact ⟨by linarith [hk.1],by linarith [hk.2]⟩) ht
  have hf (x : ℝ) : HasDerivAt (affectedAffine k t)
      (K+Real.sin t-R*NegativeAPositiveTD.AffectedNorm.first k t x) x := by
    have hh := (((((hasDerivAt_id' x).const_mul (K+Real.sin t)).add_const (Real.cos t)).sub_const
      1).add_const (R*Real.sqrt (k^2+1))).fun_sub
        ((NegativeAPositiveTD.AffectedNorm.norm_hasDerivAt hv).const_mul R)
    exact hh.congr_deriv (by ring)
  have hf' (x : ℝ) : HasDerivAt
      (fun x => K+Real.sin t-R*NegativeAPositiveTD.AffectedNorm.first k t x)
      (-R*NegativeAPositiveTD.AffectedNorm.second k t x) x := by
    convert ((NegativeAPositiveTD.AffectedNorm.first_hasDerivAt hv).const_mul R).const_sub
      (K+Real.sin t) using 1
    ring
  have hc : ConcaveOn ℝ (Icc 0 (Real.tan t)) (affectedAffine k t) := by
    apply concave_of_deriv2 (fun x _ => hf x) (fun x _ => hf' x)
    intro x hx
    dsimp [NegativeAPositiveTD.AffectedNorm.second]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.sqrt_nonneg qCap))
      (div_nonneg (sq_nonneg _) (pow_nonneg (NegativeAPositiveTD.AffectedNorm.norm_pos hv).le 3))
  have ht0 := NegativeAPositiveTD.SecantCoordinate.tan_nonnegative ht
  have hs' : s∈Icc 0 frameCap := ⟨hs.1,hs.2.trans ht.2⟩
  have hx : Real.tan s∈Icc 0 (Real.tan t) :=
    ⟨NegativeAPositiveTD.SecantCoordinate.tan_nonnegative hs',
      NegativeAPositiveTD.SecantCoordinate.tan_monotone hs' ht hs.2⟩
  have h0 := affected_identity hk ht (show (0:ℝ)∈Icc 0 t from ⟨le_rfl,ht.1⟩)
  have h1 := affected_identity hk ht (show t∈Icc 0 t from ⟨ht.1,le_rfl⟩)
  have hh := hc.min_le_of_mem_Icc ⟨le_rfl,ht0⟩ ⟨ht0,le_rfl⟩ hx
  simp only [Real.tan_zero,F_zero,zero_add,sub_zero,sub_self,V_zero,add_zero,
    secant,Real.cos_zero,div_one] at h0 h1
  rw [←h0,←h1,←affected_identity hk ht hs] at hh
  exact hh

/-- The common-gain endpoint principle. The proof also establishes the
short-interval case for every k in the stated coefficient interval. -/
theorem endpoint {k t s : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 t) :
    min (V R k 1 t) (F k t)≤
      F k s+min (V R k 1 (t-s)) (V R k (secant s) (t-s)) := by
  have hun : min (V R k 1 t) (F k t)≤F k s+V R k 1 (t-s) := by
    by_cases hshort : t≤3/20
    · exact unaffected_endpoint_short hk ⟨ht.1,hshort⟩ hs
    · exact unaffected_endpoint_long hk ⟨le_of_lt (lt_of_not_ge hshort),ht.2⟩ hs
  have haff := affected_endpoint hk ht hs
  by_cases hh : V R k 1 (t-s)≤V R k (secant s) (t-s)
  · rw [min_eq_left hh]
    exact hun
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hh))]
    exact haff

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.CommonGain
