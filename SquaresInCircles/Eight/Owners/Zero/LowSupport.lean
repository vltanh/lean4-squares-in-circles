module

public import SquaresInCircles.Eight.Owners.Zero.LowDomain

/-!
# Eight squares: the original two-edge support inequality for zero--low sign propagation

Both exact stress identities retain the common intermediate point.
The secondary uses its one actual endpoint disk; the positive primary
uses the actual intermediate disk as well.  The comparison-vector
theorem supplies the secondary in the remaining negative primary case.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalZeroLow

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign GlobalOuterAnchor
open GlobalQuarterNegativePrimary

def charge (s t : State) (v x : ℝ) : ℝ :=
  Real.pi/2+v+x-unsigned s-unsigned t

def baseReserve : ℝ :=
  Real.pi/2+eta*(a0+1/2)-19/10+lam-kap-acoef

theorem baseReserve_positive : 0<baseReserve := by
  have ha := FrameLowArc.a0_bounds.1
  have hpi := Arithmetic.pi_hand_enclosure.1
  dsimp [baseReserve,eta,lam,kap,acoef]
  linarith

/-- Young's quadratic support is applied to the same shifted disk.
It is valid for arbitrary signed force components. -/
theorem quadratic_support (s : State) (f g : ℝ) :
    f*s.a+g*s.b≤(9/20)*Q0+(5/9)*(f^2+g^2)-(f+g)/2 := by
  have hc := state_circle s
  have h1 := sq_nonneg ((9/10)*(s.a+1/2)-f)
  have h2 := sq_nonneg ((9/10)*(s.b+1/2)-g)
  nlinarith

def secondaryLower (v x : ℝ) : ℝ :=
  Real.cos v*(Real.pi/2+v+x+eta*a0)+
    lam*(GlobalOuterAnchor.width v+GlobalOuterAnchor.width x-(283/200)*Real.sin v)-
    ((9/20)*Q0+(5/9)*((lam*Real.cos x+eta*Real.cos v)^2+
      (lam*Real.sin x+lam*Real.cos v)^2)-
      (lam*Real.cos x+eta*Real.cos v+lam*Real.sin x+lam*Real.cos v)/2)

theorem secondary_identity {v x : ℝ} (hv : v∈Icc 0 frameCap) :
    secondaryLower v x-Real.cos v*(19/10)=
      base v+secondaryError v x+Real.cos v*baseReserve := by
  have hsin := (transport_trig hv).2.2.1
  have hunit := Real.sin_sq_add_cos_sq x
  have hcusp : |Real.sin x|+Real.sin x=2*max (Real.sin x) 0 := by
    by_cases hs : 0≤Real.sin x
    · rw [abs_of_nonneg hs,max_eq_left hs]; ring
    · rw [abs_of_neg (lt_of_not_ge hs),max_eq_right (le_of_not_ge hs)]; ring
  dsimp [secondaryLower,GlobalOuterAnchor.width,base,secondaryError,baseReserve]
  rw [abs_of_nonneg hsin]
  dsimp [lam,eta,kap,nu,rho,gam,bcoef,kcoef,acoef,Q0]
  nlinarith only [hunit,hcusp]

theorem secondary_dual (s c t : State) {v x : ℝ}
    (hv : |v|≤frameCap) (hx : |x|≤frameCap)
    (hs : transverse s≤0) (hc : transverse c≤0) (ht : 0≤transverse t)
    (hzero : s.Feasible c 2 v)
    (hquarter : c.Feasible t 0 (Real.pi/2+x)) :
    base v+secondaryError v x<Real.cos v*(charge s t v x-19/10) := by
  obtain ⟨hv',_,hmarkerS⟩ := zero_domain s c hv hs hc hzero
  have hvframe : v∈Icc 0 frameCap := ⟨hv'.1.le,hv'.2⟩
  have tv := transport_trig hvframe
  have hcos : 0<Real.cos v := by linarith [tv.1]
  have houter := secondary_target_outer c t hx hc ht hquarter
  have hmarkerT := (outer_marker_bounds t houter).2
  have hmZ := (zero_margin s c hv hs hc).1 hzero
  have hmQ := (low_zero_margin c t hx hc ht).1 hquarter
  have hsupport := quadratic_support t
    (lam*Real.cos x+eta*Real.cos v) (lam*Real.sin x+lam*Real.cos v)
  have hsm := mul_le_mul_of_nonneg_left hmarkerS hcos.le
  have htm := mul_le_mul_of_nonneg_left hmarkerT hcos.le
  have hsource := mul_le_mul_of_nonneg_right (coordinates s).2.1.le tv.2.2.1
  have hcontacts := mul_le_mul_of_nonneg_left (add_le_add hmZ hmQ)
    (by norm_num [lam] : 0≤lam)
  have hlower : secondaryLower v x≤Real.cos v*charge s t v x := by
    dsimp [secondaryLower,charge,lam,eta] at *
    nlinarith only [hsm,htm,hsource,hcontacts,hsupport]
  have hid := secondary_identity (x:=x) hvframe
  have hreserve := mul_pos hcos baseReserve_positive
  nlinarith

def primaryLower (v x : ℝ) : ℝ :=
  Real.cos v*(Real.pi/2+v+x+eta*a0)+
    lam*(GlobalOuterAnchor.width v+Real.cos x*GlobalOuterAnchor.width x-(283/200)*Real.sin v)-
    (lam*Real.sin x*radiusUpper-lam*Real.sin x*(Real.cos x+Real.sin x)/2)-
    ((9/20)*Q0+(5/9)*((lam*Real.cos x+eta*Real.cos v)^2+
      (lam*Real.cos v)^2)-(lam*Real.cos x+eta*Real.cos v+lam*Real.cos v)/2)

theorem primary_identity {v x : ℝ} (hv : v∈Icc 0 frameCap)
    (hx : x∈Icc 0 frameCap) :
    primaryLower v x-Real.cos v*(19/10)=
      scalar v x+Real.cos v*baseReserve := by
  have hsv := (transport_trig hv).2.2.1
  have hsx := (transport_trig hx).2.2.1
  have hunit := Real.sin_sq_add_cos_sq x
  dsimp [primaryLower,GlobalOuterAnchor.width,scalar,base,baseReserve]
  rw [abs_of_nonneg hsv,abs_of_nonneg hsx]
  dsimp [lam,eta,kap,nu,rho,gam,bcoef,kcoef,acoef,Q0,radiusUpper]
  nlinarith only [hunit]

theorem primary_dual (s c t : State) {v x : ℝ}
    (hv : |v|≤frameCap) (hx : x∈Icc 0 frameCap) (hspan : v+x≤frameCap)
    (hs : transverse s≤0) (hc : transverse c≤0)
    (hzero : s.Feasible c 2 v)
    (hquarter : c.Feasible t 1 (Real.pi/2+x)) :
    scalar v x<Real.cos v*(charge s t v x-19/10) := by
  obtain ⟨hv',_,hmarkerS⟩ := zero_domain s c hv hs hc hzero
  have hvframe : v∈Icc 0 frameCap := ⟨hv'.1.le,hv'.2⟩
  have tv := transport_trig hvframe
  have tx := transport_trig hx
  have hcosv : 0<Real.cos v := by linarith [tv.1]
  have hcosx : 0≤Real.cos x := by linarith [tx.1]
  have houter := primary_target_outer s c t hv hx hspan hs hc hzero hquarter
  have hmarkerT := (outer_marker_bounds t houter).2
  have hmZ := (zero_margin s c hv hs hc).1 hzero
  have hmQ := (low_one_margin c t (by rw [abs_of_nonneg hx.1]; exact hx.2) hc).1 hquarter
  have hmQweighted := mul_le_mul_of_nonneg_left hmQ hcosx
  have hcontacts := mul_le_mul_of_nonneg_left (add_le_add hmZ hmQweighted)
    (by norm_num [lam] : 0≤lam)
  have hsupportT := quadratic_support t (lam*Real.cos x+eta*Real.cos v) (lam*Real.cos v)
  have hsupportC := state_support c (Real.cos x) (Real.sin x)
  rw [add_comm ((Real.cos x)^2) ((Real.sin x)^2),Real.sin_sq_add_cos_sq,
    Real.sqrt_one,mul_one] at hsupportC
  have hlamsin : 0≤lam*Real.sin x := mul_nonneg (by norm_num [lam]) tx.2.2.1
  have hsupportCweighted := mul_le_mul_of_nonneg_left hsupportC hlamsin
  have hR := mul_le_mul_of_nonneg_left CommonQuarter.radius_bounds.2.le hlamsin
  have hsm := mul_le_mul_of_nonneg_left hmarkerS hcosv.le
  have htm := mul_le_mul_of_nonneg_left hmarkerT hcosv.le
  have hsource := mul_le_mul_of_nonneg_right (coordinates s).2.1.le tv.2.2.1
  have hunitC := congrArg (fun r : ℝ => lam*c.b*r) (Real.sin_sq_add_cos_sq x)
  have hlower : primaryLower v x≤Real.cos v*charge s t v x := by
    dsimp [primaryLower,charge,lam,eta,radiusUpper] at *
    linarith only [hsm,htm,hsource,hcontacts,hsupportT,hsupportCweighted,hR,hunitC]
  have hid := primary_identity hvframe hx
  have hreserve := mul_pos hcosv baseReserve_positive
  linarith

/-- The full two-edge contradiction charge, with either original low
quarter owner and all original error signs. -/
theorem path_charge (s c t : State) {v x : ℝ}
    (hv : |v|≤frameCap) (hx : |x|≤frameCap) (hspan : |v+x|≤frameCap)
    (hs : transverse s≤0) (hc : transverse c≤0) (ht : 0≤transverse t)
    (hzero : s.Feasible c 2 v) (j : Fin 4) (hj : j=0 ∨ j=1)
    (hquarter : c.Feasible t j (Real.pi/2+x)) :
    19/10<charge s t v x := by
  have hdomain := zero_domain s c hv hs hc hzero
  have hvframe : v∈Icc 0 frameCap := ⟨hdomain.1.1.le,hdomain.1.2⟩
  have hcos : 0<Real.cos v := by linarith [(transport_trig hvframe).1]
  have hsecondary (hm : c.Feasible t 0 (Real.pi/2+x)) : 19/10<charge s t v x := by
    have hd := secondary_dual s c t hv hx hs hc ht hzero hm
    have he : 0≤ secondaryError v x := by
      by_cases hxp : 0≤x
      · exact secondaryError_nonnegative hvframe ⟨hxp,(le_abs_self x).trans hx⟩
      · have hz : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
        have hcut := secondary_negative_cut s c t hv hz hs hc ht hzero (by simpa using hm)
        simpa using secondaryError_negative_nonnegative hvframe ⟨hz.1,hcut.le⟩
    have hb := base_positive hvframe
    have hp : 0<Real.cos v*(charge s t v x-19/10) := by linarith
    have hh := (mul_pos_iff_of_pos_left hcos).1 hp
    linarith
  rcases hj with rfl | rfl
  · exact hsecondary hquarter
  · by_cases hxp : 0≤x
    · have hxframe : x∈Icc 0 frameCap := ⟨hxp,(le_abs_self x).trans hx⟩
      have hsum : v+x≤frameCap := (le_abs_self (v+x)).trans hspan
      have hd := primary_dual s c t hv hxframe hsum hs hc hzero hquarter
      have hl := scalar_lower hvframe.1 hxp hsum
      have hp : 0<Real.cos v*(charge s t v x-19/10) := by linarith
      have hh := (mul_pos_iff_of_pos_left hcos).1 hp
      linarith
    · have hz : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
      have hactual := secondary_of_large_source c t hz hc ht hdomain.2.1 (by simpa using hquarter)
      exact hsecondary (by simpa using hactual)

end SquaresInCircles.Eight.GlobalZeroLow
