module

public import SquaresInCircles.Eight.TableFree.OutsideEEndpoint
public import SquaresInCircles.Eight.TableFree.OutsideDE2ReferenceGap
public import SquaresInCircles.Eight.TableFree.OutsideDContact

/-!
# From the reference gap to original DE2/EH1 contacts

Uncompiled source. The reference point is used only to compare scalar
contact rates. This module varies the actual H primary down to the least
sorted primary at the same q, proves the required monotonicities, and
recovers D's original rotated corner at an actual DE2 contact.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace OutsideDE2Comparison

def u (p P : ℝ) : ℝ := P-Real.sin p
def z (q p P : ℝ) : ℝ := Real.sqrt (q-(u p P)^2)
def x (q p P : ℝ) : ℝ := z q p P*Real.cos p-u p P*Real.sin p
def y (q p P : ℝ) : ℝ := z q p P*Real.sin p+u p P*Real.cos p
def beta (q p P : ℝ) : ℝ := x q p P*(1-Real.cos p/z q p P)

theorem contact_circle {q p P : ℝ} (hz : 0≤q-(u p P)^2) :
    (x q p P)^2+(y q p P)^2=q := by
  have hr := Real.sq_sqrt hz
  have hid (Z U s c : ℝ) : (Z*c-U*s)^2+(Z*s+U*c)^2=(Z^2+U^2)*(s^2+c^2) := by ring
  rw [x,y,hid,Real.sin_sq_add_cos_sq]
  dsimp [z] at hr
  linarith

theorem contact_bounds {q p P : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10))
    (hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) :
    -(123/500 : ℝ)<u p P ∧ u p P<141/500 ∧
      979/500<z q p P ∧ z q p P≤OutsideDE2Reference.radius q ∧
      0<q-(u p P)^2 ∧ 0<x q p P ∧ 0<y q p P ∧ y q p P<7/5 := by
  obtain ⟨hRl,hRu,hPl,hPu⟩ := OutsideDE2Reference.constant_bounds hq
  have ht := trig_bracket (l := (11/50 : ℝ)) (u := (7/10 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hp
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ⟨by linarith [hp.1],hp.2⟩
  have hsinlo : 109/500<Real.sin p := by norm_num at ht; linarith [ht.1]
  have hulo : -(123/500 : ℝ)<u p P := by
    dsimp [u,OutsideDE2Polynomial.Plo] at *
    linarith [hP.1]
  have huhi : u p P<141/500 := by dsimp [u]; linarith [hP.2]
  have hu2 : (u p P)^2<(141/500 : ℝ)^2 := by
    nlinarith [mul_pos (by linarith : 0<u p P+141/500)
      (by linarith : 0<141/500-u p P)]
  have hrad : (979/500 : ℝ)^2<q-(u p P)^2 := by
    have hqL := hq.1
    dsimp [qLow] at hqL
    nlinarith
  have hrad0 : 0<q-(u p P)^2 := (sq_nonneg _).trans_lt hrad
  have hzlo : (979/500 : ℝ)<z q p P := by
    have hh := Real.sq_sqrt hrad0.le
    have hn := Real.sqrt_nonneg (q-(u p P)^2)
    dsimp [z]
    nlinarith
  have hzup : z q p P≤OutsideDE2Reference.radius q :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (u p P)])
  have hc0 : 0<Real.cos p := by linarith
  have hspos : 0<Real.sin p := by linarith
  have hxlo : 0<x q p P := by
    have h1 : (979/500 : ℝ)*(7648/10000)<z q p P*Real.cos p :=
      (mul_lt_mul_of_pos_right hzlo (by norm_num : (0:ℝ)<7648/10000)).trans_le
        (mul_le_mul_of_nonneg_left hc.le (by linarith : 0≤z q p P))
    have h2 := mul_le_mul huhi.le hs.le hs0 (by norm_num : (0:ℝ)≤141/500)
    dsimp [x]
    nlinarith
  have hylo : 0<y q p P := by
    have h1 : (979/500 : ℝ)*(109/500)<z q p P*Real.sin p :=
      (mul_lt_mul_of_pos_right hzlo (by norm_num : (0:ℝ)<109/500)).trans_le
        (mul_le_mul_of_nonneg_left hsinlo.le (by linarith : 0≤z q p P))
    have h2 : -(123/500 : ℝ)≤u p P*Real.cos p := by
      have hh := mul_le_mul_of_nonneg_right hulo.le hc0.le
      nlinarith
    dsimp [y]
    nlinarith
  have hyhi : y q p P<7/5 := by
    have hzR : z q p P<4947/2500 := by
      exact hzup.trans_lt (by simpa [OutsideDE2Polynomial.Rhi] using hRu)
    have h1 := mul_le_mul
      (show z q p P-Real.cos p≤607/500 by linarith)
      hs.le hs0 (by norm_num : (0:ℝ)≤607/500)
    have hP0 : 0≤P := by
      dsimp [OutsideDE2Polynomial.Plo] at hPl
      linarith [hP.1]
    have h2 := mul_le_mul hP.2 hc1 hc0.le (by norm_num : (0:ℝ)≤1/2)
    dsimp [y,u]
    nlinarith
  exact ⟨hulo,huhi,hzlo,hzup,hrad0,hxlo,hylo,hyhi⟩

theorem primary_derivatives {q p P : ℝ}
    (hrad : 0<q-(u p P)^2) :
    HasDerivAt (x q p) (-y q p P/z q p P) P ∧
      HasDerivAt (y q p) (x q p P/z q p P) P := by
  have hu : HasDerivAt (u p) 1 P := by simpa [u] using (hasDerivAt_id P).sub_const (Real.sin p)
  have hz0 : z q p P≠0 := (Real.sqrt_pos.mpr hrad).ne'
  have hz : HasDerivAt (z q p) (-(u p P)/z q p P) P := by
    convert ((hasDerivAt_const P q).sub (hu.pow 2)).sqrt hrad.ne' using 1
    · rfl
    · dsimp [z]
      field_simp [hz0]
      ring
  constructor
  · convert (hz.mul_const (Real.cos p)).sub (hu.mul_const (Real.sin p)) using 1
    · rfl
    · dsimp [y]
      field_simp [hz0]
      ring
  · convert (hz.mul_const (Real.sin p)).add (hu.mul_const (Real.cos p)) using 1
    · rfl
    · dsimp [x]
      field_simp [hz0]
      ring

def betaPrimaryDerivative (q p P : ℝ) : ℝ :=
  -(y q p P*z q p P*(z q p P-Real.cos p)+
    x q p P*u p P*Real.cos p)/(z q p P)^3

theorem beta_primary_derivative {q p P : ℝ}
    (hrad : 0<q-(u p P)^2) :
    HasDerivAt (beta q p) (betaPrimaryDerivative q p P) P := by
  have hu : HasDerivAt (u p) 1 P := by simpa [u] using (hasDerivAt_id P).sub_const (Real.sin p)
  have hz0 : z q p P≠0 := (Real.sqrt_pos.mpr hrad).ne'
  have hz : HasDerivAt (z q p) (-(u p P)/z q p P) P := by
    convert ((hasDerivAt_const P q).sub (hu.pow 2)).sqrt hrad.ne' using 1
    · rfl
    · dsimp [z]
      field_simp [hz0]
      ring
  convert (primary_derivatives hrad).1.mul
    ((((hasDerivAt_const P (Real.cos p)).div hz hz0).const_sub 1)) using 1
  · rfl
  · dsimp [betaPrimaryDerivative]
    field_simp [hz0]
    ring

theorem y_primary_mono {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    MonotoneOn (y q p) (Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact (by dsimp [y,z,u]; fun_prop : Continuous (y q p)).continuousOn
  · intro P hP
    exact (primary_derivatives (contact_bounds hq hp (Ioo_subset_Icc_self hP)).2.2.2.2.1).2
  · intro P hP
    have hb := contact_bounds hq hp (Ioo_subset_Icc_self hP)
    exact div_nonneg hb.2.2.2.2.2.1.le (by linarith [hb.2.2.1])

theorem y_gt_half {q p P : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10))
    (hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) :
    1/2<y q p P := by
  have hmono := y_primary_mono hq hp
  have hleft : OutsideDE2Reference.leastPrimary q∈
      Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ) := ⟨le_rfl,hP.1.trans hP.2⟩
  have hh := hmono hleft hP hP.1
  have heq : y q p (OutsideDE2Reference.leastPrimary q)=OutsideDE2Reference.y q p := rfl
  rw [heq] at hh
  exact (OutsideDE2Reference.y_gt_half hq hp).trans_le hh

theorem beta_primary_negative {q p P : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10))
    (hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) :
    betaPrimaryDerivative q p P<0 := by
  obtain ⟨huL,huU,hzL,hzU,hrad,hx,hy,hyU⟩ := contact_bounds hq hp hP
  have hyhalf := y_gt_half hq hp hP
  have hnorm := contact_circle hrad.le
  have hxU : x q p P<383/200 := by
    have hqU := hq.2
    dsimp [qCap] at hqU
    nlinarith
  have hc : 0<Real.cos p := transport_cos_pos (by
    rw [abs_of_nonneg (by linarith [hp.1] : 0≤p)]
    exact hp.2)
  have hzc : 479/500<z q p P-Real.cos p := by linarith [Real.cos_le_one p]
  have hyz : (979/1000 : ℝ)<y q p P*z q p P := by
    nlinarith [mul_pos (sub_pos.mpr hyhalf) (by linarith [hzL] : 0<z q p P)]
  have hmain : (9/10 : ℝ)<y q p P*z q p P*(z q p P-Real.cos p) := by
    have hm : (979/1000 : ℝ)*(479/500)<
        y q p P*z q p P*(z q p P-Real.cos p) :=
      (mul_lt_mul_of_pos_right hyz (by norm_num : (0:ℝ)<479/500)).trans_le
        (mul_le_mul_of_nonneg_left hzc.le (by positivity : 0≤y q p P*z q p P))
    norm_num at hm
    linarith
  have hpositive : 0<y q p P*z q p P*(z q p P-Real.cos p)+
      x q p P*u p P*Real.cos p := by
    by_cases hu0 : 0≤u p P
    · exact add_pos_of_pos_of_nonneg (by linarith)
        (mul_nonneg (mul_nonneg hx.le hu0) hc.le)
    · have huneg : 0< -u p P := by linarith
      have hprod : x q p P*(-u p P)<(383/200 : ℝ)*(123/500) := by
        exact (mul_lt_mul_of_pos_right hxU huneg).trans
          (mul_lt_mul_of_pos_left (by linarith : -u p P<123/500)
            (by norm_num : (0:ℝ)<383/200))
      have hcprod := mul_le_mul_of_nonneg_left (Real.cos_le_one p)
        (mul_nonneg hx.le huneg.le)
      nlinarith
  unfold betaPrimaryDerivative
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hpositive) (pow_pos (by linarith) 3)

theorem beta_primary_anti {q p : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) :
    AntitoneOn (beta q p) (Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) := by
  have hc : ContinuousOn (beta q p)
      (Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) := by
    apply ContinuousOn.mul (by dsimp [x,z,u]; fun_prop)
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div continuousOn_const (by dsimp [z,u]; fun_prop)
    intro P hP
    exact (show 0<z q p P by linarith [(contact_bounds hq hp hP).2.2.1]).ne'
  have hm : MonotoneOn (fun P => -beta q p P)
      (Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg hc.neg
    · intro P hP
      exact (beta_primary_derivative (contact_bounds hq hp
        (Ioo_subset_Icc_self hP)).2.2.2.2.1).neg
    · intro P hP
      exact (neg_pos.mpr (beta_primary_negative hq hp (Ioo_subset_Icc_self hP))).le
  intro P₁ hP₁ P₂ hP₂ hle
  have hh := hm hP₁ hP₂ hle
  linarith

theorem comparison_to_reference {q p P : ℝ} (hq : qLow≤q∧q≤qCap)
    (hp : p∈Icc (11/50 : ℝ) (7/10))
    (hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ)) :
    OutsideDE2Reference.y q p≤y q p P ∧
      beta q p P≤OutsideDE2Reference.beta q p := by
  have hl : OutsideDE2Reference.leastPrimary q∈
      Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ) := ⟨le_rfl,hP.1.trans hP.2⟩
  exact ⟨y_primary_mono hq hp hl hP hP.1,beta_primary_anti hq hp hl hP hP.1⟩

/-- The scalar contact formula recovers the actual original shifted E
corner, rather than replacing it with the reference corner. -/
theorem recover_contact {q p P X Y : ℝ}
    (hp : p∈Icc 0 (7/10 : ℝ)) (hX : 0<X) (hY : 0<Y)
    (hcircle : X^2+Y^2=q) (hcontact : Y*Real.cos p-(X-1)*Real.sin p=P) :
    x q p P=X ∧ y q p P=Y ∧
      OutsideE.contactSpeed (X-1/2) (Y-1/2) (Y/X) p=beta q p P := by
  let Z := X*Real.cos p+Y*Real.sin p
  have ht := transport_trig hp
  have hc : 0<Real.cos p := by linarith [ht.1]
  have hs : 0≤Real.sin p := ht.2.2.1
  have hZ : 0<Z := add_pos_of_pos_of_nonneg (mul_pos hX hc) (mul_nonneg hY.le hs)
  have hU : u p P=Y*Real.cos p-X*Real.sin p := by dsimp [u]; linarith
  have hnorm : Z^2+(u p P)^2=q := by
    rw [hU]
    have hid : Z^2+(Y*Real.cos p-X*Real.sin p)^2=
        (X^2+Y^2)*(Real.sin p^2+Real.cos p^2) := by dsimp [Z]; ring
    rw [hid,Real.sin_sq_add_cos_sq,hcircle]
    ring
  have hroot : z q p P=Z := by
    unfold z
    rw [show q-(u p P)^2=Z^2 by linarith,Real.sqrt_sq_eq_abs,abs_of_pos hZ]
  have hx : x q p P=X := by
    rw [x,hroot,hU]
    calc
      _=X*(Real.sin p^2+Real.cos p^2) := by dsimp [Z]; ring
      _=X := by rw [Real.sin_sq_add_cos_sq]; ring
  have hy : y q p P=Y := by
    rw [y,hroot,hU]
    calc
      _=Y*(Real.sin p^2+Real.cos p^2) := by dsimp [Z]; ring
      _=Y := by rw [Real.sin_sq_add_cos_sq]; ring
  have hden : 0<Real.cos p+(Y/X)*Real.sin p :=
    add_pos_of_pos_of_nonneg hc (mul_nonneg (div_nonneg hY.le hX.le) hs)
  refine ⟨hx,hy,?_⟩
  unfold beta OutsideE.contactSpeed
  rw [hx,hroot]
  dsimp [Z] at hZ ⊢
  field_simp [hX.ne',hZ.ne',hden.ne']
  ring

theorem outer_contact_speed_lt {q p n a b : ℝ} {D H : SignedPoint}
    (hq : qLow≤q∧q≤qCap)
    (hHs : H.Sorted) (hHo : H.Outer q) (hHa : H.a<1)
    (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (ha : 0<a) (hb : 0≤b) (hsort : b≤a)
    (hcircle : (a+1/2)^2+(b+1/2)^2=q)
    (hp : p∈Icc (11/50 : ℝ) (7/10)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hEH : H.a-1/2+(a-1/2)*Real.sin p-(b+1/2)*Real.cos p=0)
    (hDE : (D.a-1/2)*Real.cos n+(D.y-1/2)*Real.sin n+b-1/2=0) :
    OutsideE.contactSpeed a b ((b+1/2)/(a+1/2)) p<
      (D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  let P := H.a-1/2
  have hP : P∈Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ) := by
    have hdiag := (SignedPoint.outer_bounds hHs hHo).1
    dsimp [OutsideDE2Reference.leastPrimary,diagonalCoordinate,P] at *
    constructor <;> linarith
  have hrecover := recover_contact ⟨by linarith [hp.1],hp.2⟩
    (show 0<a+1/2 by linarith) (show 0<b+1/2 by linarith) hcircle
    (show (b+1/2)*Real.cos p-((a+1/2)-1)*Real.sin p=P by dsimp [P]; linarith)
  have hcompare := comparison_to_reference hq hp hP
  have hactual := contact_bounds hq hp hP
  have href := contact_bounds hq hp
    (show OutsideDE2Reference.leastPrimary q∈
      Icc (OutsideDE2Reference.leastPrimary q) (1/2 : ℝ) from ⟨le_rfl,hP.1.trans hP.2⟩)
  have hYref : OutsideDE2Reference.y q p∈Icc (1/2 : ℝ) (7/5) :=
    ⟨(OutsideDE2Reference.y_gt_half hq hp).le,href.2.2.2.2.2.2.2.le⟩
  have hYactual : b+1/2∈Icc (1/2 : ℝ) (7/5) := by
    rw [← hrecover.2.1]
    exact ⟨(y_gt_half hq hp hP).le,hactual.2.2.2.2.2.2.2.le⟩
  have hmono := OutsideDContact.gain_mono_tangent hq.1 hYref hYactual
    (show (7/10 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)
    (by simpa only [hrecover.2.1] using hcompare.1)
  have hreference : OutsideDE2Reference.beta q p<
      OutsideDContact.gain q (OutsideDE2Reference.y q p) (7/10) := by
    simpa [OutsideDContact.gain,OutsideDContact.root,OutsideDContact.ell,
      OutsideDE2Reference.root,OutsideDE2Reference.ell] using
      OutsideDE2Reference.reference_gap hq hp
  have hDcap := OutsideDContact.gain_ge_cap hq.1 hYactual hn
  have hDactual := OutsideDContact.actual_contact_gain hDs hDy hDo hn hDE
  have hspeed : OutsideE.contactSpeed a b ((b+1/2)/(a+1/2)) p=beta q p P := by
    simpa using hrecover.2.2
  rw [hspeed,hDactual]
  exact hcompare.2.trans_lt (hreference.trans_le (hmono.trans hDcap))

theorem flat_contact_speed_lt {q p n b : ℝ} {D : SignedPoint}
    (hq : qLow≤q) (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (hb : b∈Ico 0 (9/40 : ℝ))
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hDE : (D.a-1/2)*Real.cos n+(D.y-1/2)*Real.sin n+b-1/2=0) :
    OutsideE.contactSpeed (7/12) b 0 p<
      (D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hp
  have hc0 : 0<Real.cos p := by linarith
  have hratio : Real.sin p/Real.cos p<843/1000 := by
    apply (div_lt_iff₀ hc0).2
    nlinarith
  have hratio0 := div_nonneg hs0 hc0.le
  have hspeed : OutsideE.contactSpeed (7/12) b 0 p<139/200 := by
    have hid : OutsideE.contactSpeed (7/12) b 0 p=
        1/12+(b+1/2)*(Real.sin p/Real.cos p) := by
      dsimp [OutsideE.contactSpeed]
      field_simp [hc0.ne']
      ring
    rw [hid]
    have hm := mul_le_mul (show b+1/2≤29/40 by linarith [hb.2]) hratio.le
      hratio0 (by norm_num : (0:ℝ)≤29/40)
    nlinarith
  have hgain := OutsideDContact.gain_gt_core_speed hq
    (show b+1/2∈Icc (1/2 : ℝ) (7/5) by constructor <;> linarith [hb.1,hb.2]) hn
  rw [OutsideDContact.actual_contact_gain hDs hDy hDo hn hDE]
  linarith

end OutsideDE2Comparison

namespace OutsideE

theorem ArcSource.de2_contact_speed_lt {q b p n : ℝ} {E D H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hq : qLow≤q∧q≤qCap)
    (hHs : H.Sorted) (hHo : H.Outer q) (hHa : H.a<1)
    (hDs : D.Sorted) (hDy : D.y≤0) (hDo : D.Outer q)
    (hb : b∈Icc 0 (-E.y))
    (hp : p∈Icc (11/50 : ℝ) (7/10)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hEH : ehSlack kind q H p b=0)
    (hDE : (D.a-1/2)*Real.cos n+(D.y-1/2)*Real.sin n+b-1/2=0) :
    contactSpeed (kind.primary q b) b (kind.slope q b) p<
      (D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  cases kind with
  | flatCore =>
    exact OutsideDE2Comparison.flat_contact_speed_lt hq.1 hDs hDy hDo
      ⟨hb.1,hb.2.trans_lt (I.flat rfl).2⟩
      ⟨by linarith [hp.1],hp.2⟩ hn hDE
  | outerCircle =>
    have hg := I.geometry hq.1 hb
    have hroot : 0<Real.sqrt (q-(b+1/2)^2) := by
      have hh := hg.2.2.2.2.2.1
      dsimp [ArcKind.primary] at hh
      linarith
    have hrad := Real.sqrt_pos.mp hroot
    have hcircle : (ArcKind.outerCircle.primary q b+1/2)^2+(b+1/2)^2=q := by
      dsimp [ArcKind.primary]
      nlinarith [Real.sq_sqrt hrad.le]
    have hslope : ArcKind.outerCircle.slope q b=
        (b+1/2)/(ArcKind.outerCircle.primary q b+1/2) := by
      simp [ArcKind.slope,ArcKind.primary]
    rw [hslope]
    exact OutsideDE2Comparison.outer_contact_speed_lt hq hHs hHo hHa hDs hDy hDo
      (by linarith [hg.2.2.2.2.2.1]) hb.1 hg.2.2.2.2.2.2 hcircle hp hn hEH hDE

end OutsideE
end SquaresInCircles.Eight.TableFree

end OutsideDE2Comparison
end SquaresInCircles.Eight.TableFree
