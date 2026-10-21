module

public import SquaresInCircles.Eight.TableFree.WrongSignCaptureWeights
public import SquaresInCircles.Eight.TableFree.MiddleAngularPenalty

/-!
# The complete three-frame hull comparison for wrong signs

Uncompiled source draft.  The weights are selected once at the original
three-frame hull width.  Every exterior frame sector decreases to one
of the two scalar endpoints, and the interior sector is bounded by
convexity on a single segment.  No square is moved in this argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.WrongSignCaptureGeometry
open PositiveAngularEnvelope EndpointRotationPenalty WrongSignCaptureScalars
open WrongSignCaptureWeights

def hullWidth (x s : ℝ) : ℝ := max (-x) (max (-s) (-(x+s)))
def quarterWidth (b c s : ℝ) : ℝ :=
  if 0≤s then c+b*phi s else c*Real.cos s+b
def offset (alpha b : ℝ) : ℝ := -2*alpha/5-3/5-b
def angular (alpha a b c x s : ℝ) : ℝ :=
  R*(pairNorm a b x+pairNorm c b s)-a*(1+psi x)-quarterWidth b c s-
    charge*(x+s)+offset alpha b
def endpointT (alpha a b c rho : ℝ) : ℝ :=
  WrongSignCaptureHull.F a b rho+R*pairNorm c b 0-c-b+offset alpha b
def endpointG (alpha a b c rho : ℝ) : ℝ :=
  R*pairNorm a b 0-a+WrongSignCaptureHull.F c b rho-b+offset alpha b

theorem hull_mem {x s : ℝ} (hx : |x|≤frameCap) (hs : |s|≤frameCap)
    (ht : |x+s|≤frameCap) (hr : x+s≤0) : hullWidth x s∈Icc 0 frameCap := by
  have hlow : -(x+s)≤hullWidth x s :=
    (le_max_right (-s) (-(x+s))).trans (le_max_right (-x) (max (-s) (-(x+s))))
  refine ⟨by linarith,?_⟩
  exact max_le ((neg_le_abs x).trans hx)
    (max_le ((neg_le_abs s).trans hs) ((neg_le_abs (x+s)).trans ht))

theorem hull_below {x s : ℝ} (hs : 0≤s) (hr : x+s≤0) : hullWidth x s= -x := by
  apply le_antisymm
  · exact max_le (le_refl _) (max_le (by linarith) (by linarith))
  · exact le_max_left _ _

theorem hull_above {x s : ℝ} (hx : 0≤x) (hr : x+s≤0) : hullWidth x s= -s := by
  apply le_antisymm
  · exact max_le (by linarith) (max_le (le_refl _) (by linarith))
  · exact (le_max_left _ _).trans (le_max_right _ _)

theorem hull_between {x s : ℝ} (hx : x≤0) (hs : s≤0) :
    hullWidth x s= -(x+s) := by
  apply le_antisymm
  · exact max_le (by linarith) (max_le (by linarith) (le_refl _))
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The exact middle width minimum is multiplied only by a positive
actual stress coefficient. -/
theorem scaled_width {b c d v : ℝ} (hc : 0<c)
    (hr : b/c∈Icc (13/20 : ℝ) (23/25))
    (hd : |d|≤frameCap) (hv : |v|≤frameCap) (hs : |d+v|≤frameCap) :
    quarterWidth b c (d+v)≤b*(1+psi d)+c*(1+psi v) := by
  have hratio : b/c∈Icc (13/20 : ℝ) 1 := ⟨hr.1,by linarith [hr.2]⟩
  have hw := mul_le_mul_of_nonneg_left
    (MiddleAngularPenalty.signed_width hratio hd hv hs) hc.le
  have he : c*(b/c)=b := by field_simp [hc.ne']
  have hed := congrArg (fun z : ℝ => z*psi d) he
  by_cases hs0 : 0≤d+v
  · have hes := congrArg (fun z : ℝ => z*(phi (d+v)-1)) he
    rw [quarterWidth,if_pos hs0]
    rw [MiddleAngularPenalty.endpointWidth,if_pos hs0] at hw
    nlinarith
  · rw [quarterWidth,if_neg hs0]
    rw [MiddleAngularPenalty.endpointWidth,if_neg hs0] at hw
    nlinarith

theorem convex_split {f g : ℝ → ℝ} {u v : ℝ}
    (hf : ConvexOn ℝ (Icc 0 frameCap) f) (hg : ConvexOn ℝ (Icc 0 frameCap) g)
    (hu : 0≤u) (hv : 0≤v) (hspan : u+v≤frameCap) :
    f u+g v≤max (f 0+g (u+v)) (f (u+v)+g 0) := by
  by_cases hzero : u+v=0
  · have hu0 : u=0 := by linarith
    have hv0 : v=0 := by linarith
    simp [hu0,hv0]
  · have hpos : 0<u+v := by linarith
    let a : ℝ := v/(u+v)
    let b : ℝ := u/(u+v)
    have ha : 0≤a := div_nonneg hv hpos.le
    have hb : 0≤b := div_nonneg hu hpos.le
    have hab : a+b=1 := by dsimp [a,b]; field_simp [hzero]; ring
    have hargf : a*0+b*(u+v)=u := by dsimp [a,b]; field_simp [hzero]
    have hargg : b*0+a*(u+v)=v := by dsimp [a,b]; field_simp [hzero]
    have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
    have ht : u+v∈Icc 0 frameCap := ⟨by linarith,hspan⟩
    have hfc := hf.2 hz ht ha hb hab
    have hgc := hg.2 hz ht hb ha (by linarith : b+a=1)
    simp only [smul_eq_mul,hargf] at hfc
    simp only [smul_eq_mul,hargg] at hgc
    have hL := mul_le_mul_of_nonneg_left
      (le_max_left (f 0+g (u+v)) (f (u+v)+g 0)) ha
    have hU := mul_le_mul_of_nonneg_left
      (le_max_right (f 0+g (u+v)) (f (u+v)+g 0)) hb
    have hweight := congrArg
      (fun z : ℝ => z*max (f 0+g (u+v)) (f (u+v)+g 0)) hab
    nlinarith

theorem angular_hull {alpha a b c x s L : ℝ}
    (hb : 0<b) (hba : b≤a) (ha1 : a≤1) (hbc : b≤c) (hc1 : c≤1)
    (hratio : b/c∈Icc (13/20 : ℝ) (23/25))
    (hx : |x|≤frameCap) (hs : |s|≤frameCap) (ht : |x+s|≤frameCap) (hr : x+s≤0)
    (hT : endpointT alpha a b c (hullWidth x s)<L)
    (hG : endpointG alpha a b c (hullWidth x s)<L) :
    angular alpha a b c x s<L := by
  have ha : 0<a := hb.trans_le hba
  have hc : 0<c := hb.trans_le hbc
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  by_cases hs0 : 0≤s
  · have hs' : s∈Icc 0 frameCap := ⟨hs0,(le_abs_self s).trans hs⟩
    have hx' : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hpsi : psi x=Real.cos x-1 := by
      simpa only [neg_neg,Real.cos_neg] using psi_negative hx'
    have hB := (WrongSignCaptureHull.B_antitone hc hc1 hratio) hz hs' hs0
    have hB0 : WrongSignCaptureHull.B c b 0=R*pairNorm c b 0-b := by
      simp [WrongSignCaptureHull.B,WrongSignCaptureHull.R,WrongSignCaptureHull.p]
    have he : angular alpha a b c x s=
        WrongSignCaptureHull.F a b (-x)+WrongSignCaptureHull.B c b s-c+offset alpha b := by
      rw [angular,quarterWidth,if_pos hs0,hpsi]
      simp only [WrongSignCaptureHull.F,WrongSignCaptureHull.B,WrongSignCaptureHull.R,
        WrongSignCaptureHull.p,neg_neg,Real.cos_neg]
      ring
    rw [hull_below hs0 hr] at hT
    rw [hB0] at hB
    rw [he]
    dsimp [endpointT] at hT
    linarith
  · have hsn : s≤0 := by linarith
    have hs' : -s∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs s).trans hs⟩
    by_cases hx0 : 0≤x
    · have hx' : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans hx⟩
      have hA := (WrongSignCaptureHull.A_antitone hb hba ha1) hz hx' hx0
      have hA0 : WrongSignCaptureHull.A a b 0=R*pairNorm a b 0-a := by
        simp [WrongSignCaptureHull.A,WrongSignCaptureHull.R,WrongSignCaptureHull.p]
      have he : angular alpha a b c x s=
          WrongSignCaptureHull.A a b x+WrongSignCaptureHull.F c b (-s)-b+offset alpha b := by
        rw [angular,quarterWidth,if_neg hs0,psi_positive hx']
        simp only [WrongSignCaptureHull.F,WrongSignCaptureHull.A,WrongSignCaptureHull.R,
          WrongSignCaptureHull.p,neg_neg,Real.cos_neg]
        ring
      rw [hull_above hx0 hr] at hG
      rw [hA0] at hA
      rw [he]
      dsimp [endpointG] at hG
      linarith
    · have hx' : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
      have hspan : -x+-s≤frameCap := by
        have hh := (neg_le_abs (x+s)).trans ht
        linarith
      have hsplit := convex_split (WrongSignCaptureHull.F_convex hb hba)
        (WrongSignCaptureHull.F_convex hb hbc) hx'.1 hs'.1 hspan
      have hpsi : psi x=Real.cos x-1 := by
        simpa only [neg_neg,Real.cos_neg] using psi_negative hx'
      have he : angular alpha a b c x s=
          WrongSignCaptureHull.F a b (-x)+WrongSignCaptureHull.F c b (-s)-b+offset alpha b := by
        rw [angular,quarterWidth,if_neg hs0,hpsi]
        simp only [WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p,
          neg_neg,Real.cos_neg]
        ring
      have hρ : hullWidth x s= -x+-s := by
        rw [hull_between (by linarith) hsn]
        ring
      rw [hρ] at hT hG
      have hzeroA : WrongSignCaptureHull.F a b 0=R*pairNorm a b 0-a := by
        simp [WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p]
      have hzeroC : WrongSignCaptureHull.F c b 0=R*pairNorm c b 0-c := by
        simp [WrongSignCaptureHull.F,WrongSignCaptureHull.R,WrongSignCaptureHull.p]
      have hleft : WrongSignCaptureHull.F a b 0+WrongSignCaptureHull.F c b (-x+-s)-b+
          offset alpha b<L := by rw [hzeroA]; exact hG
      have hright : WrongSignCaptureHull.F a b (-x+-s)+WrongSignCaptureHull.F c b 0-b+
          offset alpha b<L := by rw [hzeroC]; dsimp [endpointT] at hT; linarith
      rw [he]
      rcases le_total
          (WrongSignCaptureHull.F a b 0+WrongSignCaptureHull.F c b (-x+-s))
          (WrongSignCaptureHull.F a b (-x+-s)+WrongSignCaptureHull.F c b 0) with h | h
      · rw [max_eq_right h] at hsplit
        linarith
      · rw [max_eq_left h] at hsplit
        linarith

theorem admissible_domains {a b : ℝ} (h : Admissible a b) :
    0<a ∧ 0<b ∧ b≤a ∧ b≤1 ∧ b/a∈Icc (13/20 : ℝ) (23/25) := by
  have ha : 0<a := by linarith [h.1.1]
  have hb : 0<b := by linarith [h.2.1.1]
  refine ⟨ha,hb,by nlinarith [h.2.2],by linarith [h.2.1.2],?_⟩
  constructor
  · apply (le_div_iff₀ ha).2
    linarith [h.1.2,h.2.1.1]
  · exact (div_le_iff₀ ha).2 h.2.2

theorem selected_endpoints (alpha b rho : ℝ) :
    endpointT alpha alpha b 1 rho=U_T rho alpha b ∧
      endpointG alpha alpha b 1 rho=U_G rho alpha b ∧
      endpointT alpha 1 b alpha rho=U_G rho alpha b ∧
      endpointG alpha 1 b alpha rho=U_T rho alpha b := by
  dsimp [endpointT,endpointG,U_T,U_G,offset,WrongSignCaptureHull.F,
    WrongSignCaptureHull.R,WrongSignCaptureHull.p]
  refine ⟨?_,?_,?_,?_⟩ <;> ring

/-- At every actual reversed total, one admissible weight pair controls
both possible wrong signs on the original middle path. -/
theorem angular_bounds {x s : ℝ} (hx : |x|≤frameCap) (hs : |s|≤frameCap)
    (ht : |x+s|≤frameCap) (hr : x+s≤0) :
    ∃ alpha b,Admissible alpha b ∧
      angular alpha alpha b 1 x s<(WrongSignWeightPolynomial.limit:ℝ) ∧
      angular alpha 1 b alpha x s<(WrongSignWeightPolynomial.limit:ℝ) := by
  obtain ⟨alpha,b,hadm,hT,hG⟩ := weights (hull_mem hx hs ht hr)
  obtain ⟨ha,hb,hba,hb1,hratio⟩ := admissible_domains hadm
  have hends := selected_endpoints alpha b (hullWidth x s)
  refine ⟨alpha,b,hadm,?_,?_⟩
  · exact angular_hull hb hba hadm.1.2 hb1 (by norm_num)
      (by simpa using hadm.2.1) hx hs ht hr
      (by rw [hends.1]; exact hT) (by rw [hends.2.1]; exact hG)
  · exact angular_hull hb hb1 (by norm_num) hba hadm.1.2 hratio hx hs ht hr
      (by rw [hends.2.2.1]; exact hG) (by rw [hends.2.2.2]; exact hT)

end SquaresInCircles.Eight.TableFree.WrongSignCaptureGeometry
