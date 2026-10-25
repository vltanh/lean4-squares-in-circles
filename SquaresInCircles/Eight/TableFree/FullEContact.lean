module

public import SquaresInCircles.Eight.TableFree.FullEArc

/-!
# Full E-contact rates for arbitrary H

Uncompiled source. These rates use only H's actual sorted contained state.
The low owner itself forces a core E contact onto the flat arc; the high
owner allows the entire curved core. All four DE/EH combinations retain
their original physical normals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace FullE
open OutsideE (contactSpeed contactSpeed_positive)
open DirectNegativeE (lowSlack lowAngularRate lowSpeed)

def highSlack (kind : ArcKind) (q : ℝ) (H : SignedPoint) (p b : ℝ) : ℝ :=
  H.a-1/2+(kind.primary q b-1/2)*Real.sin p-(b+1/2)*Real.cos p

def mixedSlack (kind : ArcKind) (q : ℝ) (H : SignedPoint) (j : Fin 4)
    (p b : ℝ) : ℝ :=
  if j=0 then lowSlack H p b else highSlack kind q H p b

def mixedRate (kind : ArcKind) (q : ℝ) (H : SignedPoint) (j : Fin 4)
    (p b β : ℝ) : ℝ :=
  if j=0 then β-lowAngularRate H p else
    β*(Real.cos p+kind.slope q b*Real.sin p)-
      ((kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p)

def de3Slack (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (p b : ℝ) : ℝ :=
  D.a-1/2-(kind.primary q b+1/2)*Real.sin (p-α)+(b-1/2)*Real.cos (p-α)

def deSlack (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (j : Fin 4)
    (p b : ℝ) : ℝ :=
  if j=2 then OutsideE.de2Slack D α p b else de3Slack kind q α D p b

def deRate (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (j : Fin 4)
    (p b β : ℝ) : ℝ :=
  if j=2 then (D.a-1/2)*Real.sin (p-α)+(1/2-D.y)*Real.cos (p-α)-β else
    (kind.primary q b+1/2-β)*Real.cos (p-α)+
      (b-1/2-kind.slope q b*β)*Real.sin (p-α)

theorem mixedSlack_actual (kind : ArcKind) (q : ℝ) (H : SignedPoint) (b : ℝ)
    {p : ℝ} {j : Fin 4} (hj : j=0 ∨ j=1) (hp : p∈Icc 0 (7/10 : ℝ)) :
    mixedSlack kind q H j p b=
      quarterProjection (kind.point q b) H p j-edgeWidth p := by
  rw [edgeWidth_positive_formula hp]
  rcases hj with rfl | rfl <;>
    simp [mixedSlack,highSlack,lowSlack,quarterProjection,ArcKind.point] <;> ring

theorem deSlack_actual (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (b : ℝ)
    {p : ℝ} {j : Fin 4} (hj : j=2 ∨ j=3) (hn : p-α∈Icc 0 (7/10 : ℝ)) :
    deSlack kind q α D j p b=
      quarterProjection D (kind.point q b) (-(p-α)) j-edgeWidth (-(p-α)) := by
  rw [edgeWidth_negative_formula hn]
  rcases hj with rfl | rfl <;>
    simp only [quarterProjection,Real.cos_neg,Real.sin_neg] <;>
    simp [deSlack,OutsideE.de2Slack,de3Slack,ArcKind.point] <;> ring

/-- H's low-owner angular demand is below .4 even when H is far from its
diagonal and its shifted tangent is negative. -/
theorem lowSpeed_bounds {q p : ℝ} {H : SignedPoint}
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q)
    (hqU : q≤qCap) (hp : p∈Icc 0 (7/10 : ℝ)) :
    0≤lowSpeed H p ∧ lowAngularRate H p≤lowSpeed H p ∧ lowSpeed H p<2/5 := by
  have hHa := SignedPoint.primary_gt_half hHs hHcore
  have hHy : H.y<9/10 := (le_abs_self _).trans_lt
    (SignedPoint.coordinate_bounds hHs hHcore hHc hqU).2.2
  have ht := transport_trig hp
  have hsin := mul_nonneg (show 0≤H.a-1/2 by linarith) ht.2.2.1
  have hrate : lowAngularRate H p<2/5 := by
    by_cases hy : 1/2≤H.y
    · have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one p)
        (show 0≤H.y-1/2 by linarith)
      dsimp [lowAngularRate]
      linarith
    · have hc := mul_nonpos_of_nonpos_of_nonneg
        (show H.y-1/2≤0 by linarith) (show 0≤Real.cos p by linarith [ht.1])
      dsimp [lowAngularRate]
      linarith
  exact ⟨le_max_right _ _,le_max_left _ _,max_lt_iff.mpr ⟨hrate,by norm_num⟩⟩

/-- At a weak EH0 contact, the actual unshifted H projection is below
1.415. The corner-circle inequality, not a near-diagonal assumption,
therefore forces E's tangent magnitude below .415. -/
theorem low_contact_tangent_bound {q p b : ℝ} {H : SignedPoint} {kind : ArcKind}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHc : H.Contained q) (hqU : q≤qCap)
    (hp : p∈Icc 0 (7/10 : ℝ))
    (hf : quarterFeasible (kind.point q b) H p 0) : b<83/200 := by
  let P := H.a*Real.cos p+H.y*Real.sin p
  have ht := transport_trig hp
  have hsum : P≤H.a+H.y := by
    have ha := mul_le_mul_of_nonneg_left (Real.cos_le_one p) hHs.1.le
    have hy := mul_le_mul_of_nonneg_left (Real.sin_le_one p) hHy
    dsimp [P]
    linarith
  have hrot : P^2+(H.a*Real.sin p-H.y*Real.cos p)^2=H.a^2+H.y^2 := by
    calc
      _=(H.a^2+H.y^2)*(Real.sin p^2+Real.cos p^2) := by dsimp [P]; ring
      _=_ := by rw [Real.sin_sq_add_cos_sq]; ring
  have hq : (H.a+1/2)^2+(H.y+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hHy] using hHc.trans hqU
  have hP : P<283/200 := by
    by_contra! hbad
    dsimp [qCap] at hq
    nlinarith [sq_nonneg (H.a*Real.sin p-H.y*Real.cos p)]
  have hproj : edgeWidth p≤P-b := by
    simpa [quarterFeasible,quarterProjection,ArcKind.point,P,sub_eq_add_neg,add_comm,
      add_left_comm,add_assoc] using hf
  have hw := edgeWidth_ge_one p
  linarith

theorem core_speed_bound {a b v p : ℝ}
    (ha : 1/2<a) (haU : a≤7/12) (hb : 0≤b ∧ b≤a) (hv : 0≤v)
    (hp : p∈Icc 0 (7/10 : ℝ)) : contactSpeed a b v p<997/1000 := by
  have ht := transport_trig hp
  have hc : 0<Real.cos p := by linarith [ht.1]
  have htan : Real.sin p<(843/1000 : ℝ)*Real.cos p := by
    nlinarith [ht.1,ht.2.2.2.1]
  have hden := (contactSpeed_positive ha hb.1 hv hp).1
  have hfirst := mul_le_mul_of_nonneg_right (show a-1/2≤1/12 by linarith) hc.le
  have hsecond := mul_le_mul_of_nonneg_right (show b+1/2≤13/12 by linarith [hb.2])
    ht.2.2.1
  have hextra := mul_nonneg hv ht.2.2.1
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem ArcSource.high_speed_bound {q b p : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10 : ℝ)) :
    contactSpeed (kind.primary q b) b (kind.slope q b) p<47/40 := by
  have hg := I.geometry hqL hb
  have hv := (I.derivative hqL hb).2
  cases kind with
  | trueCore =>
    have hcore : (ArcKind.trueCore.point q b).Core :=
      (TrueCoreE.Source.mk I.sorted I.nonpos (I.core rfl)).geometry hb |>.2.1
    have ha := SignedPoint.core_primary_le hg.1 hcore
    have hh := core_speed_bound hg.2.2.2.2.2.1 ha ⟨hb.1,hg.2.2.2.2.2.2⟩ hv.1 hp
    exact hh.trans (by norm_num : (997/1000 : ℝ)<47/40)
  | outerCircle =>
    have hcircle : (ArcKind.outerCircle.primary q b+1/2)^2+(b+1/2)^2≤qCap := by
      simpa [SignedPoint.Contained,SignedPoint.circle,ArcKind.point,abs_neg,
        abs_of_nonneg hb.1] using hg.2.1.trans hqU
    have hvform : ArcKind.outerCircle.slope q b=
        (b+1/2)/(ArcKind.outerCircle.primary q b+1/2) := by
      simp [ArcKind.slope,ArcKind.primary,OutsideE.ArcKind.slope,OutsideE.ArcKind.primary]
    rw [hvform]
    exact DirectNegativeE.outer_speed_bound hg.2.2.2.2.2.1 hb.1 hcircle hp

/-- The curved-core identity supplies the third radial case in the exact
two-contact determinant. Both angle orders remain allowed. -/
theorem de3_contact_rate_positive {a b v p n : ℝ}
    (hb : 0≤b) (hv : 0≤v ∧ v≤1)
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hr : (v=0 ∧ b≤1/2) ∨ b-v*a=(1-v)/2 ∨ b-v*a= -(1-v)/2) :
    0<(a+1/2-contactSpeed a b v p)*Real.cos n+
      (b-1/2-v*contactSpeed a b v p)*Real.sin n := by
  rcases hr with hflat | hcurve | houter
  · exact OutsideE.de3_contact_rate_positive hb hv hp hn (Or.inl hflat)
  · have htP := transport_trig hp
    have htN := transport_trig hn
    have hcP : 0<Real.cos p := by linarith [htP.1]
    have hcN : 0<Real.cos n := by linarith [htN.1]
    have hden : 0<Real.cos p+v*Real.sin p :=
      add_pos_of_pos_of_nonneg hcP (mul_nonneg hv.1 htP.2.2.1)
    have hS : contactSpeed a b v p*(Real.cos p+v*Real.sin p)=
        (a-1/2)*Real.cos p+(b+1/2)*Real.sin p :=
      div_mul_cancel₀ _ hden.ne'
    have heq : ((a+1/2-contactSpeed a b v p)*Real.cos n+
        (b-1/2-v*contactSpeed a b v p)*Real.sin n)*(Real.cos p+v*Real.sin p)=
        Real.cos n*(Real.cos p-Real.sin p)+
          v*Real.sin p*(Real.cos n-Real.sin n) := by
      linear_combination (-(Real.cos n)-v*Real.sin n)*hS+
        (Real.sin n*Real.cos p-Real.cos n*Real.sin p)*hcurve
    have hpos : 0<((a+1/2-contactSpeed a b v p)*Real.cos n+
        (b-1/2-v*contactSpeed a b v p)*Real.sin n)*(Real.cos p+v*Real.sin p) := by
      rw [heq]
      exact add_pos_of_pos_of_nonneg (mul_pos hcN (sub_pos.mpr htP.2.2.2.2))
        (mul_nonneg (mul_nonneg hv.1 htP.2.2.1)
          (sub_nonneg.mpr htN.2.2.2.2.le))
    exact (mul_pos_iff_of_pos_right hden).1 hpos
  · exact OutsideE.de3_contact_rate_positive hb hv hp hn (Or.inr houter)

theorem ArcSource.low_de3_rate {q b p n : ℝ} {E H : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hb : b∈Icc 0 (-E.y)) (hHs : H.Sorted) (hHcore : H.AvoidsCore)
    (hHc : H.Contained q) (hHy : 0≤H.y)
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hf : quarterFeasible (kind.point q b) H p 0) :
    0<(kind.primary q b+1/2-lowSpeed H p)*Real.cos n+
      (b-1/2-kind.slope q b*lowSpeed H p)*Real.sin n := by
  have hβ := lowSpeed_bounds hHs hHcore hHc hqU hp
  have ht := transport_trig hn
  have hc : 0<Real.cos n := by linarith [ht.1]
  have hv := (I.derivative hqL hb).2
  cases kind with
  | trueCore =>
    have hbsmall := low_contact_tangent_bound hHs hHy hHc hqU hp hf
    have haflat : ArcKind.trueCore.primary q b=7/12 :=
      TrueCoreE.primary_flat (by linarith)
    have hvflat : ArcKind.trueCore.slope q b=0 := TrueCoreE.slope_flat (by linarith)
    rw [haflat,hvflat]
    have hmain := mul_lt_mul_of_pos_right (show (41/60 : ℝ)<13/12-lowSpeed H p by
      linarith [hβ.2.2]) hc
    have htan := mul_nonneg hb.1 ht.2.2.1
    nlinarith [ht.1,ht.2.2.2.1]
  | outerCircle =>
    have hg := I.geometry hqL hb
    have ho : (ArcKind.outerCircle.point q b).Outer q := by
      have hroot := hg.2.2.2.2.2.1
      change 1/2<Real.sqrt (q-(b+1/2)^2)-1/2 at hroot
      have hrad : 0<q-(b+1/2)^2 := Real.sqrt_pos.mp (by linarith)
      simp only [SignedPoint.Outer,SignedPoint.circle,ArcKind.point,ArcKind.primary,
        OutsideE.ArcKind.primary,abs_neg,abs_of_nonneg hb.1]
      nlinarith [Real.sq_sqrt hrad.le]
    have ha := (SignedPoint.outer_bounds hg.1 ho).1
    have hdiag := (uniform_circle_reserves hqL hqU).1
    have hmain := mul_lt_mul_of_pos_right
      (show (999/1000 : ℝ)<ArcKind.outerCircle.primary q b+1/2-lowSpeed H p by
        change diagonalCoordinate q≤ArcKind.outerCircle.primary q b at ha
        linarith [hβ.2.2]) hc
    have hvβ := mul_le_mul_of_nonneg_right hv.2 hβ.1
    have htan := mul_le_mul_of_nonneg_right
      (show -(9/10 : ℝ)≤b-1/2-ArcKind.outerCircle.slope q b*lowSpeed H p by
        linarith [hb.1,hβ.2.2]) ht.2.2.1
    nlinarith [ht.1,ht.2.2.2.1]

end FullE
end SquaresInCircles.Eight.TableFree
