module

public import SquaresInCircles.Eight.TableFree.OutsideERates

/-!
# The actual zero-tangent endpoints of the outside-E transport

Uncompiled source. A flat-core EH1 contact supplies the actual EH0 axis
using H's original outer circle. An outer-E contact at long EH error is
incompatible with the high sorted H tangent. These discharge the radial
boundary of compact endpoint attainment.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace OutsideE

theorem flat_zero_contact_eh0 {q p : ℝ} {H : SignedPoint}
    (hq : qLow≤q) (hHs : H.Sorted) (hHy : 0≤H.y) (hHo : H.Outer q)
    (hp : p∈Ioc 0 (7/10 : ℝ))
    (hcontact : ehSlack .flatCore q H p 0=0) :
    quarterFeasible (ArcKind.flatCore.point q 0) H p 0 := by
  let X := H.a+1/2
  let Y := H.y+1/2
  let Z := 1+(1/12 : ℝ)*Real.cos p+(1/2 : ℝ)*Real.sin p
  have ht := transport_trig ⟨hp.1.le,hp.2⟩
  have hs0 : 0≤Real.sin p := ht.2.2.1
  have hc0 : 0<Real.cos p := by linarith [ht.1]
  have hspos : 0<Real.sin p := Real.sin_pos_of_pos_of_lt_pi hp.1
    (by linarith [hp.2,Real.pi_gt_three])
  have hX : X=1+Real.cos p/2-Real.sin p/12 := by
    dsimp [ehSlack,ArcKind.primary] at hcontact
    dsimp [X]
    linarith
  have hlinear : (7/6 : ℝ)*Real.cos p+(5/6 : ℝ)*Real.sin p<3/2 := by
    have hrot : ((7/6 : ℝ)*Real.cos p+(5/6 : ℝ)*Real.sin p)^2+
        ((7/6 : ℝ)*Real.sin p-(5/6 : ℝ)*Real.cos p)^2=74/36 := by
      nlinarith [Real.sin_sq_add_cos_sq p]
    nlinarith [sq_nonneg ((7/6 : ℝ)*Real.sin p-(5/6 : ℝ)*Real.cos p)]
  have hnorm : X^2+Z^2<541/144 := by
    rw [hX]
    dsimp [Z]
    nlinarith [Real.sin_sq_add_cos_sq p]
  have hHcircle : X^2+Y^2=q := by
    simpa [X,Y,SignedPoint.Outer,SignedPoint.circle,abs_of_nonneg hHy] using hHo
  have hYZ : Z<Y := by
    have hY : 0<Y := by dsimp [Y]; linarith
    have hZ : 0<Z := by dsimp [Z]; positivity
    dsimp [qLow] at hq
    nlinarith
  have hid : quarterProjection (ArcKind.flatCore.point q 0) H p 0-edgeWidth p=
      Real.sin p*(Y-Z) := by
    rw [edgeWidth_positive_formula ⟨hp.1.le,hp.2⟩]
    have hHa : H.a=1/2+Real.cos p/2-Real.sin p/12 := by dsimp [X] at hX; linarith
    rw [hHa]
    simp [quarterProjection,ArcKind.point,ArcKind.primary,Y,Z]
    nlinarith [Real.sin_sq_add_cos_sq p]
  apply sub_nonneg.mp
  rw [hid]
  exact (mul_pos hspos (sub_pos.mpr hYZ)).le

theorem outer_zero_long_contact_false {q p : ℝ} {H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 211/250<H.y)
    (hp : p∈Icc (11/50 : ℝ) (7/10 : ℝ))
    (hcontact : ehSlack .outerCircle q H p 0=0) : False := by
  have hha : 211/250<H.a := hHy.trans_le ((le_abs_self _).trans hHs.2)
  have hroot := (uniform_circle_reserves hqL hqU).2.2.1
  have ha : 7/5<ArcKind.outerCircle.primary q 0 := by
    simpa [ArcKind.primary] using (show 7/5<Real.sqrt (q-1/4)-1/2 by linarith)
  have hp0 : 0≤p := by linarith [hp.1]
  have hsin : 1/5<Real.sin p := by
    have hpoly := Real.sin_ge_sub_cube hp0
    have hp2 : p^2≤(7/10 : ℝ)^2 := by nlinarith [hp.2]
    have hp3 : p^3≤(7/10 : ℝ)^2*p := by
      have hh := mul_nonneg hp0 (sub_nonneg.mpr hp2)
      nlinarith
    nlinarith [hp.1]
  have hs0 : 0≤Real.sin p := by linarith
  have hmul := mul_lt_mul_of_pos_right
    (show (9/10 : ℝ)<ArcKind.outerCircle.primary q 0-1/2 by linarith)
    (show 0<Real.sin p by linarith)
  dsimp [ehSlack] at hcontact
  nlinarith [Real.cos_le_one p]

/-- The only zero-tangent first contact supplies the advertised EH0 stop.
No core, circle, or tangent-floor alternative is left implicit. -/
theorem ArcSource.zero_contact_eh0 {q p : ℝ} {E H : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHy : 211/250<H.y) (hHo : H.Outer q)
    (hp : p∈Icc (11/50 : ℝ) (7/10 : ℝ))
    (hcontact : ehSlack kind q H p 0=0) :
    quarterFeasible (kind.point q 0) H p 0 := by
  cases kind with
  | flatCore =>
    exact flat_zero_contact_eh0 hqL hHs (by linarith) hHo
      ⟨by linarith [hp.1],hp.2⟩ hcontact
  | outerCircle =>
    exact (outer_zero_long_contact_false hqL hqU hHs hHy hp hcontact).elim

end OutsideE
end SquaresInCircles.Eight.TableFree
