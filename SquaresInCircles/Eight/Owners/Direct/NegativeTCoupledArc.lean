module

public import SquaresInCircles.Eight.Owners.Negative.ContactGeometry
public import SquaresInCircles.Eight.Words.Aligned.NegativeEH1Arc
public import SquaresInCircles.Eight.Words.Outside.EEndpoint

/-!
# Eight squares: the aligned D/T/E arc on the original circles of D and E

Along the coupled arc E has tangent `coupledTangent = 1 - a_D` and follows its own radial arc
(`coupledPoint`). The contact speed stays below `199/200` on the whole short positive EH interval
(`coupled_speed_bound`), while the primary of D gains faster than that as long as BT2 is
unavailable, so either EH normal gains the uniform strict reserve `1/250`
(`Source.coupled_derivative_negative`).
-/

section
/-!
## Improvement rates for a nonpositive E outside its frame

When H and D satisfy the cuts of a negative primary, `211/250 < H.y < 9/10` and
`211/250 < -D.y`, either owner of EH and either negative owner of DE improve strictly in a common
direction along the radial arc of E (`ArcSource.improving_below_speed`): the contact speed stays
below `47/40` (`outer_speed_bound`, `ArcSource.high_speed_bound`), while D gains at a rate above
`1249/1000` (`high_D_rate`). E keeps its nonpositive sign, and H and D need only be contained at
`q`: their circles are never enlarged.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeE
open OutsideE

def lowSlack (H : SignedPoint) (p b : ℝ) : ℝ :=
  (H.a-1/2)*Real.cos p+(H.y-1/2)*Real.sin p-b-1/2

def lowAngularRate (H : SignedPoint) (p : ℝ) : ℝ :=
  (H.y-1/2)*Real.cos p-(H.a-1/2)*Real.sin p

def lowSpeed (H : SignedPoint) (p : ℝ) : ℝ := max (lowAngularRate H p) 0

def mixedSlack (kind : ArcKind) (q : ℝ) (H : SignedPoint) (j : Fin 4)
    (p b : ℝ) : ℝ :=
  if j=0 then lowSlack H p b else ehSlack kind q H p b

def mixedRate (kind : ArcKind) (q : ℝ) (H : SignedPoint) (j : Fin 4)
    (p b β : ℝ) : ℝ :=
  if j=0 then β-lowAngularRate H p else
    β*(Real.cos p+kind.slope q b*Real.sin p)-
      ((kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p)

def deSlack (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (j : Fin 4)
    (p b : ℝ) : ℝ :=
  if j=2 then de2Slack D α p b else de3Slack kind q α D p b

def deRate (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (j : Fin 4)
    (p b β : ℝ) : ℝ :=
  if j=2 then (D.a-1/2)*Real.sin (p-α)+(1/2-D.y)*Real.cos (p-α)-β else
    (kind.primary q b+1/2-β)*Real.cos (p-α)+
      (b-1/2-kind.slope q b*β)*Real.sin (p-α)

theorem lowSlack_actual (kind : ArcKind) (q : ℝ) (H : SignedPoint) (b : ℝ)
    {p : ℝ} (hp : p∈Icc 0 (7/10 : ℝ)) :
    lowSlack H p b=quarterProjection (kind.point q b) H p 0-edgeWidth p := by
  rw [edgeWidth_positive_formula hp]
  simp [lowSlack,quarterProjection,ArcKind.point]
  ring

theorem mixedSlack_actual (kind : ArcKind) (q : ℝ) (H : SignedPoint) (b : ℝ)
    {p : ℝ} {j : Fin 4} (hj : j=0 ∨ j=1) (hp : p∈Icc 0 (7/10 : ℝ)) :
    mixedSlack kind q H j p b=
      quarterProjection (kind.point q b) H p j-edgeWidth p := by
  rcases hj with rfl | rfl
  · simpa [mixedSlack] using lowSlack_actual kind q H b hp
  · simpa [mixedSlack] using ehSlack_actual kind q H b hp

theorem deSlack_actual (kind : ArcKind) (q α : ℝ) (D : SignedPoint) (b : ℝ)
    {p : ℝ} {j : Fin 4} (hj : j=2 ∨ j=3) (hn : p-α∈Icc 0 (7/10 : ℝ)) :
    deSlack kind q α D j p b=
      quarterProjection D (kind.point q b) (-(p-α)) j-edgeWidth (-(p-α)) := by
  rcases hj with rfl | rfl
  · simpa [deSlack] using de2Slack_actual kind q α D b hn
  · simpa [deSlack] using de3Slack_actual kind q α D b hn

theorem core_eh0_flat {H E : SignedPoint} {p : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEc : E.Core)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted) (hHa : H.a<1)
    (hp : p∈Icc 0 (7/10 : ℝ)) (hf : quarterFeasible E H p 0) :
    E.a=7/12 ∧ -E.y<141/1000 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hp
  have hHya : H.y≤H.a := by
    simpa [abs_of_pos (show 0<H.y by linarith [hHy.1])] using hHs.2
  have hfeas : -E.y+1/2≤(H.a-1/2)*Real.cos p+(H.y-1/2)*Real.sin p := by
    have hh := hf
    rw [quarterFeasible,edgeWidth_positive_formula hp] at hh
    simp only [quarterProjection,Matrix.cons_val_zero] at hh
    linarith
  have hnorm : ((H.a-1/2)*Real.cos p+(H.y-1/2)*Real.sin p)^2+
      ((H.a-1/2)*Real.sin p-(H.y-1/2)*Real.cos p)^2=
      (H.a-1/2)^2+(H.y-1/2)^2 := by
    calc
      _=((H.a-1/2)^2+(H.y-1/2)^2)*(Real.sin p^2+Real.cos p^2) := by ring
      _=_ := by rw [Real.sin_sq_add_cos_sq]; ring
  have hb : -E.y<141/1000 := by
    by_contra! hbad
    have hsq := pow_le_pow_left₀ (show 0≤ -E.y+1/2 by linarith) hfeas 2
    nlinarith [sq_nonneg ((H.a-1/2)*Real.sin p-(H.y-1/2)*Real.cos p)]
  have hbhalf : |E.y|≤1/2 := by rw [abs_of_nonpos hEy]; linarith
  exact ⟨(SignedPoint.flat_core_iff hEs hbhalf).1 hEc,hb⟩

theorem arcSource_of_owner {q p : ℝ} {H E : SignedPoint} {j : Fin 4}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted) (hHa : H.a<1)
    (hj : j=0 ∨ j=1) (hp : p∈Icc 0 (7/10 : ℝ))
    (hf : quarterFeasible E H p j) : ∃ kind, ArcSource q E kind := by
  rcases hj with rfl | rfl
  · rcases hEr with ho | hc
    · exact ⟨.outerCircle,⟨hEs,hEy,(by intro h; cases h),fun _ => ho⟩⟩
    · obtain ⟨ha,hb⟩ := core_eh0_flat hEs hEy hc hHy hHs hHa hp hf
      exact ⟨.flatCore,⟨hEs,hEy,fun _ => ⟨ha,by linarith⟩,(by intro h; cases h)⟩⟩
  · exact OutsideE.arcSource_of_boundary hEs hEy hEr hHa hp hf

/-- A sorted D with `211/250 < -D.y` gains at a rate above `1249/1000` at every angle of
`[0, 7/10]`; only the signed tangent of D and sorting enter. -/
theorem high_D_rate {D : SignedPoint} {n : ℝ}
    (hDs : D.Sorted) (hDy : 211/250< -D.y) (hn : n∈Icc 0 (7/10 : ℝ)) :
    1249/1000<(D.a-1/2)*Real.sin n+(1/2-D.y)*Real.cos n := by
  have hDya : -D.y≤D.a := by
    simpa [abs_of_neg (show D.y<0 by linarith)] using hDs.2
  have hs7 := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  have hc7 := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hbase : (1249/1000 : ℝ)<(43/125)*Real.sin n+(168/125)*Real.cos n := by
    have hh := trig_concave_gt (α := 0) (A := 43/125) (B := 168/125)
      (m := 1249/1000) (l := 0) (u := 7/10) (x := n)
      (by norm_num) (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three]) hn (by norm_num)
      (by norm_num at hs7 hc7; norm_num; linarith)
    simpa using hh
  have ht := transport_trig hn
  have hsin := mul_le_mul_of_nonneg_right
    (show (43/125 : ℝ)≤D.a-1/2 by linarith) ht.2.2.1
  have hcos := mul_le_mul_of_nonneg_right
    (show (168/125 : ℝ)≤1/2-D.y by linarith) (by linarith [ht.1] : 0≤Real.cos n)
  linarith

theorem lowSpeed_bounds {H : SignedPoint} {p : ℝ}
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted)
    (hp : p∈Icc 0 (7/10 : ℝ)) :
    0≤lowSpeed H p ∧ lowAngularRate H p≤lowSpeed H p ∧ lowSpeed H p<2/5 := by
  have ht := transport_trig hp
  have hHya : H.y≤H.a := by
    simpa [abs_of_pos (show 0<H.y by linarith [hHy.1])] using hHs.2
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one p)
    (show 0≤H.y-1/2 by linarith [hHy.1])
  have hsin := mul_nonneg (show 0≤H.a-1/2 by linarith [hHy.1]) ht.2.2.1
  exact ⟨le_max_right _ _,le_max_left _ _,max_lt_iff.mpr ⟨by
    dsimp [lowAngularRate]; linarith [hHy.2],by norm_num⟩⟩

theorem flat_speed_bound {b p : ℝ}
    (hb : b∈Ico 0 (9/40 : ℝ)) (hp : p∈Icc 0 (7/10 : ℝ)) :
    contactSpeed (7/12) b 0 p<139/200 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hp
  have hc0 : 0<Real.cos p := by linarith
  have hr : Real.sin p/Real.cos p<843/1000 := by
    apply (div_lt_iff₀ hc0).2
    nlinarith
  have hr0 := div_nonneg hs0 hc0.le
  have heq : contactSpeed (7/12) b 0 p=1/12+(b+1/2)*(Real.sin p/Real.cos p) := by
    dsimp [contactSpeed]
    field_simp [hc0.ne']
    ring
  rw [heq]
  have hm := mul_le_mul (show b+1/2≤29/40 by linarith [hb.2]) hr.le hr0
    (by norm_num : (0:ℝ)≤29/40)
  nlinarith

/-- On the outer arc of E the contact speed is below `47/40`. The bound keeps the norm of the
shifted circle of E and needs neither a contact at H nor an outer equality for H or D. -/
theorem outer_speed_bound {a b p : ℝ}
    (ha : 1/2<a) (hb : 0≤b)
    (hq : (a+1/2)^2+(b+1/2)^2≤qCap) (hp : p∈Icc 0 (7/10 : ℝ)) :
    contactSpeed a b ((b+1/2)/(a+1/2)) p<47/40 := by
  let X := a+1/2
  let Y := b+1/2
  let Z := X*Real.cos p+Y*Real.sin p
  have ht := transport_trig hp
  have hc : 0<Real.cos p := by linarith only [ht.1]
  have hX : 0<X := by dsimp only [X]; linarith only [ha]
  have hY : 1/2≤Y := by dsimp only [Y]; linarith only [hb]
  have hZ : 0<Z := add_pos_of_pos_of_nonneg (mul_pos hX hc)
    (mul_nonneg (by linarith only [hY]) ht.2.2.1)
  have hnorm : Z^2+(Y*Real.cos p-X*Real.sin p)^2=X^2+Y^2 := by
    calc
      _=(X^2+Y^2)*(Real.sin p^2+Real.cos p^2) := by dsimp [Z]; ring
      _=_ := by rw [Real.sin_sq_add_cos_sq]; ring
  have hnormq : X^2+Y^2≤9789/2500 := hq
  have hXup : X<383/200 := by
    have hY2 : 1/4≤Y^2 := by nlinarith only [hY]
    have hsq : X^2<(383/200)^2 := by norm_num; linarith only [hnormq,hY2]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hZup : Z<4947/2500 := by
    have hsq : Z^2<(4947/2500)^2 := by
      norm_num
      linarith only [hnorm,hnormq,sq_nonneg (Y*Real.cos p-X*Real.sin p)]
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have hratio : (1912/4947 : ℝ)<Real.cos p/Z := by
    apply (lt_div_iff₀ hZ).2
    linarith only [hZup,ht.1]
  have hformula : contactSpeed a b (Y/X) p=X*(1-Real.cos p/Z) := by
    have hden : Real.cos p+(Y/X)*Real.sin p=Z/X := by
      dsimp only [Z]
      field_simp
    have hN : (a-1/2)*Real.cos p+(b+1/2)*Real.sin p=Z-Real.cos p := by
      simp only [Z,X,Y]; ring
    unfold contactSpeed
    rw [hden,hN]
    field_simp
  rw [show (b+1/2)/(a+1/2)=Y/X by rfl,hformula]
  have hm := mul_lt_mul_of_pos_left
    (show 1-Real.cos p/Z<3035/4947 by linarith only [hratio]) hX
  have hm2 := mul_lt_mul_of_pos_right hXup (by norm_num : (0:ℝ)<3035/4947)
  linarith only [hm,hm2]

theorem ArcSource.high_speed_bound {q b p : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10 : ℝ)) :
    contactSpeed (kind.primary q b) b (kind.slope q b) p<47/40 := by
  cases kind with
  | flatCore =>
    have hh := flat_speed_bound ⟨hb.1,hb.2.trans_lt (I.flat rfl).2⟩ hp
    simpa [ArcKind.primary,ArcKind.slope] using hh.trans (by norm_num : (139/200 : ℝ)<47/40)
  | outerCircle =>
    have hg := I.geometry hqL hb
    have hc : (ArcKind.outerCircle.primary q b+1/2)^2+(b+1/2)^2≤qCap := by
      have hh := hg.2.1.trans hqU
      simpa [SignedPoint.Contained,SignedPoint.circle,ArcKind.point,
        abs_neg,abs_of_nonneg hb.1] using hh
    have hslope : ArcKind.outerCircle.slope q b=
        (b+1/2)/(ArcKind.outerCircle.primary q b+1/2) := by
      simp [ArcKind.slope,ArcKind.primary]
    rw [hslope]
    exact outer_speed_bound hg.2.2.2.2.2.1 hb.1 hc hp

theorem ArcSource.low_de3_rate {q b p n : ℝ} {E H : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hb : b∈Icc 0 (-E.y)) (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted)
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    0<(kind.primary q b+1/2-lowSpeed H p)*Real.cos n+
      (b-1/2-kind.slope q b*lowSpeed H p)*Real.sin n := by
  have hβ := lowSpeed_bounds hHy hHs hp
  have ht := transport_trig hn
  have hc : 0<Real.cos n := by linarith [ht.1]
  have hv := (I.derivative hqL hb).2
  cases kind with
  | flatCore =>
    have hmain := mul_lt_mul_of_pos_right (show (41/60 : ℝ)<13/12-lowSpeed H p by
      linarith [hβ.2.2]) hc
    have htan := mul_nonneg hb.1 ht.2.2.1
    dsimp [ArcKind.primary,ArcKind.slope]
    linarith [ht.1,ht.2.2.2.1]
  | outerCircle =>
    have hg := I.geometry hqL hb
    have ho : (ArcKind.outerCircle.point q b).Outer q := by
      have heq := (I.outer rfl)
      have hroot := hg.2.2.2.2.2.1
      dsimp [ArcKind.primary] at hroot
      have hrad : 0<q-(b+1/2)^2 := Real.sqrt_pos.mp (by linarith)
      simp only [SignedPoint.Outer,SignedPoint.circle,ArcKind.point,ArcKind.primary,
        abs_neg,abs_of_nonneg hb.1]
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
    linarith [ht.1,ht.2.2.2.1]

theorem low_direction_derivative (H : SignedPoint) (p b β : ℝ) :
    HasDerivAt (fun τ => lowSlack H (p-τ) (b-β*τ)) (β-lowAngularRate H p) 0 := by
  have hp : HasDerivAt (fun τ : ℝ => p-τ) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub p
  have hb : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hc := (Real.hasDerivAt_cos (p-0)).comp 0 hp
  have hs := (Real.hasDerivAt_sin (p-0)).comp 0 hp
  convert (((hc.const_mul (H.a-1/2)).add (hs.const_mul (H.y-1/2))).sub hb).sub_const
    (1/2) using 1 <;> simp [lowSlack,lowAngularRate]
  ring

theorem ArcSource.mixed_direction_derivative {q b p β : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (j : Fin 4)
    (hqL : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => mixedSlack kind q H j (p-τ) (b-β*τ))
      (mixedRate kind q H j p b β) 0 := by
  by_cases hj : j=0
  · simpa [mixedSlack,mixedRate,hj] using low_direction_derivative H p b β
  · simpa [mixedSlack,mixedRate,hj] using I.eh_direction_derivative
      (H := H) (p := p) (β := β) hqL hb

theorem ArcSource.de_direction_derivative {q α b p β : ℝ} {E D : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (j : Fin 4)
    (hqL : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => deSlack kind q α D j (p-τ) (b-β*τ))
      (deRate kind q α D j p b β) 0 := by
  by_cases hj : j=2
  · simpa [deSlack,deRate,hj] using de2_direction_derivative D α b p β
  · simpa [deSlack,deRate,hj] using I.de3_direction_derivative
      (D := D) (α := α) (p := p) (β := β) hqL hb

/-- For each of the four combinations of an owner of DE in `{2, 3}` and an owner of EH in
`{0, 1}`, some direction `β > 0` makes both the mixed rate and the DE rate positive. -/
theorem ArcSource.improving_below_speed {q α b p : ℝ} {E D H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted)
    (hDs : D.Sorted) (hDy : 211/250< -D.y)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10 : ℝ))
    (hn : p-α∈Icc 0 (7/10 : ℝ))
    (jDE jEH : Fin 4) (hDE : jDE=2 ∨ jDE=3) (hEH : jEH=0 ∨ jEH=1) :
    ∃ β, 0<β ∧ 0< mixedRate kind q H jEH p b β ∧
      0<deRate kind q α D jDE p b β := by
  let V := (D.a-1/2)*Real.sin (p-α)+(1/2-D.y)*Real.cos (p-α)
  have hV : 1249/1000<V := high_D_rate hDs hDy hn
  have hg := I.geometry hqL hb
  have hv := (I.derivative hqL hb).2
  rcases hEH with rfl | rfl
  · let β₀ := lowSpeed H p
    have hβ := lowSpeed_bounds hHy hHs hp
    rcases hDE with rfl | rfl
    · refine ⟨(β₀+V)/2,by dsimp only [β₀]; linarith only [hβ.1,hV],?_,?_⟩
      · simp only [mixedRate,ite_true]
        dsimp only [β₀]
        linarith only [hβ.1,hβ.2.1,hβ.2.2,hV]
      · simp only [deRate,ite_true]
        show 0<V-(β₀+V)/2
        linarith only [hV,hβ.2.2]
    · let c := Real.cos (p-α)+kind.slope q b*Real.sin (p-α)
      let W := (kind.primary q b+1/2-β₀)*Real.cos (p-α)+
        (b-1/2-kind.slope q b*β₀)*Real.sin (p-α)
      have hW : 0<W := ArcSource.low_de3_rate I hqL hqU hb hHy hHs hp hn
      have hc : 0<c := by
        have ht := transport_trig hn
        exact add_pos_of_pos_of_nonneg (by linarith only [ht.1])
          (mul_nonneg hv.1 ht.2.2.1)
      let η := W/(2*c)
      have hη : 0<η := div_pos hW (mul_pos (by norm_num) hc)
      have hηc : η*c=W/2 := by dsimp [η]; field_simp [hc.ne']
      refine ⟨β₀+η,by dsimp only [β₀]; linarith only [hβ.1,hη],?_,?_⟩
      · simp only [mixedRate,ite_true]
        dsimp only [β₀]
        linarith only [hβ.2.1,hη]
      · norm_num only [deRate,show (3:Fin 4)≠2 by decide,ite_false]
        have heq : (kind.primary q b+1/2-(β₀+η))*Real.cos (p-α)+
            (b-1/2-kind.slope q b*(β₀+η))*Real.sin (p-α)=W-η*c := by
          dsimp [W,c]; ring
        rw [heq,hηc]
        linarith only [hW]
  · rcases hDE with rfl | rfl
    · let β₀ := contactSpeed (kind.primary q b) b (kind.slope q b) p
      let den := Real.cos p+kind.slope q b*Real.sin p
      let U := (kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p
      have hβ := contactSpeed_positive hg.2.2.2.2.2.1 hb.1 hv.1 hp
      have hβup : β₀<47/40 := ArcSource.high_speed_bound I hqL hqU hb hp
      have hid : β₀*den=U := by
        dsimp only [β₀,den,U]; unfold contactSpeed; exact div_mul_cancel₀ _ hβ.1.ne'
      have hgap : β₀<V := by linarith only [hβup,hV]
      have hprod := mul_pos (show 0<(β₀+V)/2-β₀ by linarith only [hgap]) hβ.1
      refine ⟨(β₀+V)/2,by linarith only [hβ.2,hV,hgap],?_,?_⟩
      · norm_num only [mixedRate,show (1:Fin 4)≠0 by decide,ite_false]
        change 0<(β₀+V)/2*den-U
        linarith only [hid,hprod]
      · simp only [deRate,ite_true]
        change 0<V-(β₀+V)/2
        linarith only [hgap]
    · obtain ⟨β,hβ,hEH,hDE⟩ := I.de3_improving_speed hqL hb hp hn
      exact ⟨β,hβ,by simpa [mixedRate] using hEH,by simpa [deRate] using hDE⟩

end DirectNegativeE
end SquaresInCircles.Eight
end
end
end

section
/-!
## Actual DE alignment with the original EH and DE normals

A compact minimum on E's actual radial arc attains DE
alignment. The four simultaneous rate estimates exclude every interior
minimum, while the original inequalities exclude both zero tangent and
zero EH error. In particular H>D is proved at the endpoint rather than
assumed at the beginning. No H or D outer equality is used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeE
open OutsideE

theorem zero_tangent_impossible {q n : ℝ} {D : SignedPoint} {kind : ArcKind}
    (hDa : D.a<1) (hDs : D.Sorted) (hDy : D.y≤0)
    (ha : 0<kind.primary q 0) (hn : n∈Icc 0 (7/10 : ℝ))
    (j : Fin 4) (hj : j=2 ∨ j=3) :
    ¬quarterFeasible D (kind.point q 0) (-n) j := by
  intro hf
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  have hw := edgeWidth_ge_one n
  rcases hj with rfl | rfl
  · have hcos := mul_le_mul_of_nonneg_left hc1 hDs.1.le
    have hsin := mul_nonpos_of_nonpos_of_nonneg hDy hs0
    simp [quarterFeasible,quarterProjection,ArcKind.point] at hf
    linarith
  · have hsin := mul_nonneg ha.le hs0
    simp [quarterFeasible,quarterProjection,ArcKind.point] at hf
    linarith

theorem zero_error_impossible {q b : ℝ} {H : SignedPoint} {kind : ArcKind}
    (hHa : H.a<1) (hb : 0≤b) (j : Fin 4) (hj : j=0 ∨ j=1) :
    ¬quarterFeasible (kind.point q b) H 0 j := by
  intro hf
  rcases hj with rfl | rfl <;>
    simp [quarterFeasible,quarterProjection,ArcKind.point,edgeWidth_zero] at hf <;>
    linarith

structure AlignmentEndpoint (q : ℝ) (D E H : SignedPoint) (n p : ℝ)
    (jDE jEH : Fin 4) where
  point : SignedPoint
  positive_span : 0<p-n
  sorted : point.Sorted
  contained : point.Contained q
  core : point.AvoidsCore
  radial : point.Boundary q
  nonpos : point.y≤0
  tangent_nonincrease : |point.y|≤|E.y|
  circle_nonincrease : point.circle≤E.circle
  DE : quarterFeasible D point 0 jDE
  EH : quarterFeasible point H (p-n) jEH

/-- Both original weak owners survive all the way to actual DE alignment.
The source's H--D span may have either sign; positivity is a conclusion. -/
theorem alignment_endpoint {q n p : ℝ} {D E H : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted) (hHa : H.a<1)
    (hDy : 211/250< -D.y) (hDs : D.Sorted) (hDa : D.a<1)
    (hEs : E.Sorted) (hEy : E.y≤0) (hEr : E.Boundary q)
    (hn : n∈Ioc 0 (7/10 : ℝ)) (hp : p∈Ioc 0 (7/10 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E (-n) jDE) (hEH : quarterFeasible E H p jEH) :
    Nonempty (AlignmentEndpoint q D E H n p jDE jEH) := by
  obtain ⟨kind,I⟩ := arcSource_of_owner hEs hEy hEr hHy hHs hHa hjEH
    ⟨hp.1.le,hp.2⟩ hEH
  let α := p-n
  let l := max 0 α
  let f := mixedSlack kind q H jEH
  let g := deSlack kind q α D jDE
  have hlp : l<p := max_lt_iff.mpr ⟨hp.1,by dsimp [α]; linarith [hn.1]⟩
  have hlzero : 0≤l := le_max_left _ _
  have hlα : α≤l := le_max_right _ _
  have hparams {x : ℝ} (hx : x∈Icc l p) :
      x∈Icc 0 (7/10 : ℝ) ∧ x-α∈Icc 0 (7/10 : ℝ) := by
    constructor
    · exact ⟨hlzero.trans hx.1,hx.2.trans hp.2⟩
    · constructor
      · linarith [hx.1]
      · dsimp [α]; linarith [hx.2,hn.2]
  have hprim := kind.continuous_primary q
  have hcf : Continuous (fun z : ℝ×ℝ => f z.1 z.2) := by
    dsimp [f,mixedSlack,lowSlack,ehSlack]
    split_ifs <;> fun_prop
  have hcg : Continuous (fun z : ℝ×ℝ => g z.1 z.2) := by
    dsimp [g,deSlack,de2Slack,de3Slack]
    split_ifs <;> fun_prop
  let S : Set (ℝ×ℝ) :=
    ((Icc l p ×ˢ Icc 0 (-E.y)) ∩ {z | 0≤f z.1 z.2}) ∩ {z | 0≤g z.1 z.2}
  have hcompact : IsCompact S :=
    ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hcf)).inter_right
      (isClosed_le continuous_const hcg)
  have hstart : (p,-E.y)∈S := by
    refine ⟨⟨⟨⟨hlp.le,le_rfl⟩,⟨neg_nonneg.mpr hEy,le_rfl⟩⟩,?_⟩,?_⟩
    · dsimp [f]
      rw [mixedSlack_actual kind q H (-E.y) hjEH ⟨hp.1.le,hp.2⟩,I.initial]
      exact sub_nonneg.mpr hEH
    · dsimp [g]
      rw [deSlack_actual kind q α D (-E.y) hjDE
        (by dsimp [α]; simpa using ⟨hn.1.le,hn.2⟩),I.initial]
      simpa [α] using sub_nonneg.mpr hDE
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn ⟨(p,-E.y),hstart⟩
    continuous_fst.continuousOn
  let m := z.1
  let b := z.2
  have hm : m∈Icc l p := hz.1.1.1
  have hb : b∈Icc 0 (-E.y) := hz.1.1.2
  have hf : 0≤f m b := hz.1.2
  have hg : 0≤g m b := hz.2
  have hangles := hparams hm
  have hgeometry := I.geometry hqL hb
  have hEHfinal : quarterFeasible (kind.point q b) H m jEH := by
    have hh := hf
    dsimp [f] at hh
    rw [mixedSlack_actual kind q H b hjEH hangles.1] at hh
    exact sub_nonneg.mp hh
  have hDEfinal : quarterFeasible D (kind.point q b) (-(m-α)) jDE := by
    have hh := hg
    dsimp [g] at hh
    rw [deSlack_actual kind q α D b hjDE hangles.2] at hh
    exact sub_nonneg.mp hh
  have hbpos : 0<b := by
    apply lt_of_le_of_ne hb.1
    intro hzero
    have ha : 0<kind.primary q 0 := by
      have hh := hgeometry.2.2.2.2.2.1
      rw [← hzero] at hh
      linarith
    exact zero_tangent_impossible hDa hDs (by linarith) ha hangles.2 jDE hjDE
      (by simpa [← hzero] using hDEfinal)
  have hmleft : m=l := by
    apply le_antisymm _ hm.1
    by_contra! hlm
    obtain ⟨β,hβ,hfder,hgder⟩ := ArcSource.improving_below_speed I hqL hqU hHy hHs hDs hDy
      hb hangles.1 hangles.2 jDE jEH hjDE hjEH
    obtain ⟨z',hz'p,hz'b,hz'f,hz'g,hz'lt⟩ := feasible_shift_left
      (f := f) (g := g) ⟨hlm,hm.2⟩ hb hβ.le (Or.inr hbpos)
      (ArcSource.mixed_direction_derivative I (H := H) (p := m) (β := β) jEH hqL hb)
      (ArcSource.de_direction_derivative I (D := D) (α := α) (p := m) (β := β) jDE hqL hb)
      hf hg (Or.inr hfder) (Or.inr hgder)
    have hz'S : z'∈S := ⟨⟨⟨hz'p,hz'b⟩,hz'f⟩,hz'g⟩
    have hh : m≤z'.1 := hmin hz'S
    linarith
  have hmpos : 0<m := by
    apply lt_of_le_of_ne hangles.1.1
    intro hmzero
    exact zero_error_impossible hHa hb.1 jEH hjEH (by simpa [← hmzero] using hEHfinal)
  have hmα : m=α := by
    have hαpos : 0<α := by
      by_contra! hbad
      have hlEq : l=0 := max_eq_left hbad
      linarith
    exact hmleft.trans (max_eq_right hαpos.le)
  exact ⟨{
    point := kind.point q b
    positive_span := by dsimp [α] at hmα; linarith
    sorted := hgeometry.1
    contained := hgeometry.2.1
    core := hgeometry.2.2.1
    radial := hgeometry.2.2.2.1
    nonpos := by dsimp [ArcKind.point]; linarith [hb.1]
    tangent_nonincrease := by
      simp only [ArcKind.point,abs_neg,abs_of_nonneg hb.1,abs_of_nonpos hEy]
      exact hb.2
    circle_nonincrease := hgeometry.2.2.2.2.1
    DE := by simpa [hmα] using hDEfinal
    EH := by simpa [hmα,α] using hEHfinal }⟩

end DirectNegativeE
end SquaresInCircles.Eight
end
end
end

section
/-!
## Advancing the negative D/T contact while E is above D

Reflection is used only for the D/T/B contact formulas, which do not involve E. The mixed
inequalities are the DE2 and DE3 projections onto the original nonpositive E. A compactness
argument reaches BT2 or DE alignment, and the positive frame movement buys strict slack in the DE
witness while D stays on its circle (`PositiveDEStop`, `Source.positive_de_stop`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap

abbrev Source (q t : ℝ) (D T B : SignedPoint) : Prop :=
  AlignedNegative.Source q t D.reflect T.reflect B.reflect

def Dpath (qD P x : ℝ) : SignedPoint := (movingAnchor qD P x).reflect
def Tpath (P x : ℝ) : SignedPoint := (point P x).reflect

def positiveDESlack (qD P e : ℝ) (E : SignedPoint) (j : Fin 4) (x : ℝ) : ℝ :=
  if j=2 then lowMixedSlack qD P e E.reflect x else highMixedSlack qD P e E.reflect x

def positiveDEDerivative (qD P e : ℝ) (E : SignedPoint) (j : Fin 4) (x : ℝ) : ℝ :=
  if j=2 then lowMixedDerivative qD P e x else highMixedDerivative qD P e E.reflect x

theorem short_original_e_rate {a b d : ℝ}
    (ha : a<283/200) (hb : 0≤b) (hd : d∈Icc 0 (21/100 : ℝ)) :
    (a-1/2)*Real.cos d+(1/2-b)*Real.sin d<1249/1250 := by
  let f : ℝ → ℝ := fun x => (183/200)*Real.cos x+(1/2)*Real.sin x
  have hfder (x : ℝ) : HasDerivAt f (-(183/200)*Real.sin x+(1/2)*Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul (183/200)).add
      ((Real.hasDerivAt_sin x).const_mul (1/2)) using 1
    simp []
  have hmono : MonotoneOn f (Icc 0 (21/100 : ℝ)) := by
    apply monoOn_of_hasDeriv_nonneg (by dsimp [f]; fun_prop)
      (fun x _ => hfder x)
    intro x hx
    have hs : Real.sin x≤21/100 :=
      ((le_abs_self _).trans (Real.abs_sin_le_abs.trans_eq (abs_of_pos hx.1))).trans hx.2.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    have hx2 := pow_le_pow_left₀ hx.1.le hx.2.le 2
    nlinarith
  have hendpoint : f (21/100)<1249/1250 := by
    have hc := cos_upper_four (show (0:ℝ)≤21/100 by norm_num)
    have hs := sin_upper_five (show (0:ℝ)≤21/100 by norm_num)
    dsimp [f]
    norm_num at hc hs
    linarith
  have hfd := hmono hd ⟨by norm_num,le_rfl⟩ hd.2
  have ht := transport_trig (show d∈Icc 0 (7/10 : ℝ) from ⟨hd.1,by linarith [hd.2]⟩)
  have hprim := mul_lt_mul_of_pos_right (show a-1/2<183/200 by linarith)
    (show 0<Real.cos d by linarith [ht.1])
  have htan := mul_le_mul_of_nonneg_right (show 1/2-b≤(1/2:ℝ) by linarith) ht.2.2.1
  dsimp [f] at hfd hendpoint
  linarith

theorem Source.primary_gain {q t x : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (hq : q≤qCap) (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0) :
    1<primaryGain D.circle (B.a-1/2) x := by
  let J := I.atAngle hq hx hnot
  have hcuts := J.cuts hq
  have hgeom := I.path_geometry hq ⟨hx.1.le,hx.2⟩
  have hD := I.path_cap hq ⟨hx.1.le,hx.2⟩
  have hR : intrinsic (value (B.a-1/2) x) x<qCap := by
    simpa [point,SignedPoint.reflect] using hcuts.2.2.2.2.2.2.1.trans_le hq
  have h := circle_primary_gain ⟨hD.1,hD.2.1.le⟩ ⟨hx.1.le,hx.2.trans I.tilt_cap⟩ hR
    (I.H_contained.trans hq) hgeom.2.2.2.2.2.2
  rw [SignedPoint.reflect_circle] at h
  exact h

theorem positiveDESlack_actual {qD P e x : ℝ} (E : SignedPoint)
    (j : Fin 4) (hj : j=2 ∨ j=3) (he : e+x∈Icc 0 (7/10 : ℝ)) :
    positiveDESlack qD P e E j x=
      quarterProjection (Dpath qD P x) E (e+x) j-edgeWidth (e+x) := by
  rcases hj with rfl | rfl
  · have hp := quarterProjection_reflect (Dpath qD P x) E (e+x) 2
    have heq : quarterProjection E.reflect (movingAnchor qD P x) (e+x) 0=
        quarterProjection (Dpath qD P x) E (e+x) 2 := by
      simpa [Dpath,reflectedOwner] using hp
    simpa [positiveDESlack,heq] using lowMixedSlack_actual (qH := qD) (P := P) E.reflect he
  · have hp := quarterProjection_reflect (Dpath qD P x) E (e+x) 3
    have heq : quarterProjection E.reflect (movingAnchor qD P x) (e+x) 1=
        quarterProjection (Dpath qD P x) E (e+x) 3 := by
      simpa [Dpath,reflectedOwner] using hp
    simpa [positiveDESlack,heq] using highMixedSlack_actual (qH := qD) (P := P) E.reflect he

theorem positiveDESlack_hasDerivAt {qD P e x : ℝ} (E : SignedPoint) (j : Fin 4)
    (hc : Real.cos x≠0) (hrad : 0<qD-(2-value P x)^2) :
    HasDerivAt (positiveDESlack qD P e E j) (positiveDEDerivative qD P e E j x) x := by
  by_cases hj : j=2
  · have hfun : positiveDESlack qD P e E j=lowMixedSlack qD P e E.reflect := by
      funext z; simp [positiveDESlack,hj]
    rw [hfun]
    simpa [positiveDEDerivative,hj] using
      lowMixedSlack_hasDerivAt (e := e) E.reflect hc hrad
  · have hfun : positiveDESlack qD P e E j=highMixedSlack qD P e E.reflect := by
      funext z; simp [positiveDESlack,hj]
    rw [hfun]
    simpa [positiveDEDerivative,hj] using
      highMixedSlack_hasDerivAt (e := e) E.reflect hc hrad

theorem Source.positive_de_derivative {q t e x : ℝ} {D T B E : SignedPoint}
    (I : Source q t D T B) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore) (hEy : E.y≤0)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0)
    (he : e+x∈Icc 0 (21/100 : ℝ)) (j : Fin 4) (hj : j=2 ∨ j=3) :
    positiveDEDerivative D.circle (B.a-1/2) e E j x< -(1/1250) := by
  rcases hj with rfl | rfl
  · have hh := I.lowMixedDerivative_negative hq hx hnot
      (show e+x∈Icc 0 (7/10 : ℝ) from ⟨he.1,by linarith [he.2]⟩)
    rw [SignedPoint.reflect_circle] at hh
    rw [positiveDEDerivative,ite_eq_left rfl]
    exact hh.trans (by norm_num)
  · have hgain := I.primary_gain hq hx hnot
    have ha := (SignedPoint.coordinate_bounds hEs hEcore hEc hq).2.1
    have hrate := short_original_e_rate ha (neg_nonneg.mpr hEy) he
    simp only [positiveDEDerivative,show (3:Fin 4)≠2 by decide,ite_false,
      highMixedDerivative,SignedPoint.reflect]
    linarith

private theorem exists_left_improvement {f : ℝ → ℝ} {l m d : ℝ}
    (hd : HasDerivAt f d m) (hneg : d<0) (hlm : l< m) :
    ∃ x, x∈Ioo l m ∧ f m<f x := by
  have hf : HasDerivAt f d (-(-m)) := by simpa using hd
  have hg : HasDerivAt (fun z => f (-z)) (-d) (-m) :=
    (hf.comp (-m) (hasDerivAt_id (-m)).neg).congr_deriv (by ring)
  have hbetter := NegativeContact.eventually_right_gt hg (neg_pos.mpr hneg)
  have hbound : ∀ᶠ z in 𝓝[>] (-m), z< -l :=
    (eventually_lt_nhds (show -m< -l by linarith)).filter_mono nhdsWithin_le_nhds
  obtain ⟨z,hz,hbound,hbetter⟩ :=
    (eventually_mem_nhdsWithin.and (hbound.and hbetter)).exists
  have hz' : -m<z := hz
  exact ⟨-z,⟨by linarith,by linarith⟩,by simpa using hbetter⟩

structure PositiveDEStop {q t : ℝ} {D T B : SignedPoint}
    (I : Source q t D T B) (E : SignedPoint) (e : ℝ) (j : Fin 4) where
  angle : ℝ
  angle_mem : angle∈Ico 0 t
  error_mem : e+angle∈Icc 0 (7/10 : ℝ)
  mixed_strict : 0<positiveDESlack D.circle (B.a-1/2) e E j angle
  terminal : quarterFeasible (point (B.a-1/2) angle) B.reflect (-angle) 0 ∨ e+angle=0

/-- The positive movement stops at an available BT2 axis or at DE alignment, with strict slack in
the DE witness in both cases. -/
theorem Source.positive_de_stop {q t e : ℝ} {D T B E : SignedPoint}
    (I : Source q t D T B) (hq : q≤qCap)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore) (hEy : E.y≤0)
    (he : e+t∈Ioc 0 (21/100 : ℝ)) (j : Fin 4) (hj : j=2 ∨ j=3)
    (hf : quarterFeasible D E (e+t) j) : Nonempty (PositiveDEStop I E e j) := by
  let P := B.a-1/2
  let L : ℝ → ℝ := positiveDESlack D.circle P e E j
  let l := max 0 (-e)
  let k : ℝ := 1/2500
  let F : ℝ → ℝ := fun x => L x-L t-k*(t-x)
  have hlt : l<t := max_lt_iff.mpr ⟨I.tilt_pos,by linarith [he.1]⟩
  have hl0 : 0≤l := le_max_left _ _
  have hlE : -e≤l := le_max_right _ _
  have hewide : |e+t|≤7/10 := by
    rw [abs_of_pos he.1]
    linarith [he.2]
  have hLstart : 0≤L t := by
    have hraw := (quarterFeasible_reflect D E (e+t) j).2 hf
    have hj' : reflectedOwner j=0 ∨ reflectedOwner j=1 := by
      rcases hj with rfl | rfl <;> norm_num [reflectedOwner]
    have hnormalized := (I.normalize hq).retains_mixed hq hewide hj' hraw
    rw [(I.normalize hq).H_eq,SignedPoint.reflect_circle] at hnormalized
    have hback : quarterFeasible (Dpath D.circle P t) E (e+t) j := by
      apply (quarterFeasible_reflect (Dpath D.circle P t) E (e+t) j).1
      rw [Dpath,SignedPoint.reflect_reflect]
      exact hnormalized
    dsimp [L]
    rw [positiveDESlack_actual E j hj ⟨he.1.le,by linarith [he.2]⟩]
    exact sub_nonneg.mpr hback
  let clamp : ℝ → ℝ := fun x => max l (min t x)
  have hclamp (x : ℝ) : clamp x∈Icc l t :=
    ⟨le_max_left _ _,max_le hlt.le (min_le_left _ _)⟩
  have hclamp_eq {x : ℝ} (hx : x∈Icc l t) : clamp x=x := by
    simp [clamp,min_eq_right hx.2,max_eq_right hx.1]
  have hcclamp : Continuous clamp := by dsimp [clamp]; fun_prop
  have hcosclamp (x : ℝ) : Real.cos (clamp x)≠0 := by
    apply (transport_cos_pos (x := clamp x) ?_).ne'
    rw [abs_of_nonneg (hl0.trans (hclamp x).1)]
    exact (hclamp x).2.trans I.tilt_cap
  have hvalue : Continuous (fun x => value P (clamp x)) := by
    unfold value
    exact (continuous_const.sub (continuous_const.mul
      (Real.continuous_sin.comp hcclamp))).div
      (Real.continuous_cos.comp hcclamp) hcosclamp
  have hcF : Continuous (fun x => F (clamp x)) := by
    dsimp [F,L,positiveDESlack,lowMixedSlack,highMixedSlack,movingAnchor,anchorAt]
    split_ifs <;> fun_prop
  let S : Set ℝ := Icc l t ∩ {x | 0≤F (clamp x)}
  have hcompact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hcF)
  have htS : t∈S := by
    refine ⟨⟨hlt.le,le_rfl⟩,?_⟩
    show 0≤F (clamp t)
    rw [hclamp_eq ⟨hlt.le,le_rfl⟩]
    simp [F]
  obtain ⟨m,hm,hmin⟩ := hcompact.exists_isMinOn ⟨t,htS⟩ continuous_id.continuousOn
  have hmint : m∈Icc l t := hm.1
  have hm0 : 0≤m := hl0.trans hmint.1
  have hFm : 0≤F m := by
    have h2 : 0≤F (clamp m) := hm.2
    rwa [hclamp_eq hmint] at h2
  have hem : e+m∈Icc 0 (21/100 : ℝ) := by constructor <;> linarith [hmint.1,hmint.2,he.2]
  have hstop : quarterFeasible (point P m) B.reflect (-m) 0 ∨ e+m=0 := by
    by_cases hhard : quarterFeasible (point P m) B.reflect (-m) 0
    · exact Or.inl hhard
    right
    by_contra hne
    have hmpos : 0<m := by
      apply lt_of_le_of_ne hm0
      intro hzero
      have hprimary : quarterFeasible (point P 0) B.reflect 0 1 := by
        have h := (actual_primary_contact
          (show B.reflect.a=P+1/2 by dsimp [P,SignedPoint.reflect]; ring)
          (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
        rw [neg_zero] at h
        exact h
      apply hhard
      rw [← hzero,neg_zero]
      exact (quarter_low_tie (point P 0) B.reflect).2 hprimary
    have hlm : l<m := by
      apply max_lt_iff.mpr
      exact ⟨hmpos,by have hh := lt_of_le_of_ne hem.1 (Ne.symm hne); linarith⟩
    have hgeom := I.path_geometry hq ⟨hm0,hmint.2⟩
    have hc : Real.cos m≠0 := (transport_cos_pos (by
      rw [abs_of_nonneg hm0]; exact hmint.2.trans I.tilt_cap)).ne'
    have hdL := positiveDESlack_hasDerivAt (qD := D.circle) (P := P) (e := e) E j hc
      (by have h := hgeom.2.2.2.2.2.2; rw [SignedPoint.reflect_circle] at h; exact h)
    have hdF : HasDerivAt F (positiveDEDerivative D.circle P e E j m+k) m :=
      ((hdL.sub_const (L t)).sub
        (((hasDerivAt_id m).const_sub t).const_mul k)).congr_deriv (by ring)
    have hneg : positiveDEDerivative D.circle P e E j m+k<0 := by
      have hh := I.positive_de_derivative hq hEs hEc hEcore hEy
        ⟨hmpos,hmint.2⟩ hhard hem j hj
      dsimp [P,k]
      linarith
    obtain ⟨x,hx,hbetter⟩ := exists_left_improvement hdF hneg hlm
    have hxt : x∈Icc l t := ⟨hx.1.le,hx.2.le.trans hmint.2⟩
    have hxS : x∈S := by
      refine ⟨hxt,?_⟩
      show 0≤F (clamp x)
      rw [hclamp_eq hxt]
      exact hFm.trans hbetter.le
    have hh : m≤x := hmin hxS
    linarith [hx.2]
  have hmt : m<t := by
    apply lt_of_le_of_ne hmint.2
    intro hmeq
    rcases hstop with hhard | hzero
    · have hn := (I.normalize hq).source.no_hard
      rw [(I.normalize hq).G_eq] at hn
      rw [hmeq] at hhard
      exact hn hhard
    · linarith [he.1]
  have hstrict : 0<L m := by
    have hgrowth := mul_pos (show 0<k by norm_num [k]) (sub_pos.mpr hmt)
    dsimp [F] at hFm
    linarith
  exact ⟨⟨m,⟨hm0,hmt⟩,⟨hem.1,by linarith [hem.2]⟩,hstrict,hstop⟩⟩

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap OutsideE DirectNegativeE

def coupledTangent (qD P x : ℝ) : ℝ := 1-(movingAnchor qD P x).a

def coupledPoint (kind : ArcKind) (q qD P x : ℝ) : SignedPoint :=
  kind.point q (coupledTangent qD P x)

def coupledSlack (kind : ArcKind) (q qD P e : ℝ) (H : SignedPoint)
    (j : Fin 4) (x : ℝ) : ℝ :=
  mixedSlack kind q H j (e+x) (coupledTangent qD P x)

def coupledDerivative (kind : ArcKind) (q qD P e : ℝ) (H : SignedPoint)
    (j : Fin 4) (x : ℝ) : ℝ :=
  -mixedRate kind q H j (e+x) (coupledTangent qD P x) (primaryGain qD P x)

theorem short_tan_bound {p : ℝ} (hp : p∈Icc 0 (21/100 : ℝ)) :
    0≤Real.sin p/Real.cos p ∧ Real.sin p/Real.cos p<28/125 := by
  have ht := transport_trig (show p∈Icc 0 (7/10 : ℝ) from ⟨hp.1,by linarith [hp.2]⟩)
  have hc : 0<Real.cos p := by linarith [ht.1]
  have hs : Real.sin p≤21/100 :=
    ((le_abs_self _).trans (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg hp.1))).trans hp.2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := p)
  have hp2 := pow_le_pow_left₀ hp.1 hp.2 2
  refine ⟨div_nonneg ht.2.2.1 hc.le,(div_lt_iff₀ hc).2 ?_⟩
  nlinarith

/-- With the small tangent `b < 39/250` of the DE contact, the contact speed of either radial kind
is below `199/200`; this is what improves on the outer speed bound `47/40`. -/
theorem coupled_speed_bound (kind : ArcKind) {q b p : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap) (hb : b∈Ico 0 (39/250 : ℝ))
    (hp : p∈Icc 0 (21/100 : ℝ)) :
    contactSpeed (kind.primary q b) b (kind.slope q b) p<199/200 := by
  have ht := short_tan_bound hp
  have hc : 0<Real.cos p := transport_cos_pos (by
    rw [abs_of_nonneg hp.1]; linarith [hp.2])
  cases kind with
  | flatCore =>
    have heq : contactSpeed (7/12) b 0 p=1/12+(b+1/2)*(Real.sin p/Real.cos p) := by
      dsimp [contactSpeed]
      field_simp [hc.ne']
      ring
    have hm := mul_le_mul (show b+1/2≤82/125 by linarith [hb.2]) ht.2.le ht.1
      (by norm_num : (0:ℝ)≤82/125)
    simpa only [ArcKind.primary,ArcKind.slope,heq] using
      (show 1/12+(b+1/2)*(Real.sin p/Real.cos p)<199/200 by linarith only [hm])
  | outerCircle =>
    let X := Real.sqrt (q-(b+1/2)^2)
    let Y := b+1/2
    let v := Y/X
    let z := Real.sin p/Real.cos p
    have hY : 1/2≤Y ∧ Y<82/125 := by
      dsimp only [Y]; constructor <;> linarith only [hb.1,hb.2]
    have hY2 : Y^2<(82/125)^2 := pow_lt_pow_left₀ hY.2 (by linarith only [hY.1]) two_ne_zero
    have hY2' : (1/2)^2≤Y^2 := pow_le_pow_left₀ (by norm_num) hY.1 2
    have hqL' : 19577/5000≤q := hqL
    have hqU' : q≤9789/2500 := hqU
    have hrad : (933/500 : ℝ)^2<q-Y^2 := by
      norm_num at hY2 ⊢
      linarith only [hY2,hqL']
    have hrad0 : 0<q-Y^2 := by linarith only [hrad]
    have hX0 : 0<X := Real.sqrt_pos.mpr hrad0
    have hX2 : X^2=q-Y^2 := Real.sq_sqrt hrad0.le
    have hXL : 933/500<X := lt_of_pow_lt_pow_left₀ 2 hX0.le (by rw [hX2]; exact hrad)
    have hXU : X<383/200 := by
      apply lt_of_pow_lt_pow_left₀ 2 (by norm_num)
      rw [hX2]
      norm_num at hY2' ⊢
      linarith only [hY2',hqU']
    have hv : 0≤v ∧ v<44/125 := by
      refine ⟨div_nonneg (by linarith only [hY.1]) hX0.le,(div_lt_iff₀ hX0).2 ?_⟩
      linarith only [hY.2,hXL]
    have hz : 0≤z ∧ z<28/125 := ht
    have hvz : 0≤v*z := mul_nonneg hv.1 hz.1
    have hden : 0<1+v*z := by linarith only [hvz]
    have hfrac : v*z/(1+v*z)≤v*z := div_le_self hvz (by linarith only [hvz])
    have heq : contactSpeed (X-1/2) b v p=X-1+v*z/(1+v*z) := by
      have hYeq : b+1/2=v*X := by dsimp only [v,Y]; field_simp
      have hcs : Real.cos p+v*Real.sin p=Real.cos p*(1+v*z) := by
        dsimp only [z]
        field_simp
      have hzc : z*Real.cos p=Real.sin p := div_mul_cancel₀ _ hc.ne'
      have hfr : v*z/(1+v*z)*(1+v*z)=v*z := div_mul_cancel₀ _ hden.ne'
      unfold contactSpeed
      rw [hYeq,hcs,div_eq_iff (mul_pos hc hden).ne']
      linear_combination (-v*X)*hzc-(Real.cos p)*hfr
    have hproduct := mul_le_mul hv.2.le hz.2.le hz.1 (by norm_num : (0:ℝ)≤44/125)
    change contactSpeed (X-1/2) b v p<199/200
    rw [heq]
    linarith only [hXU,hfrac,hproduct]

theorem ArcSource.primary_antitone {q : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hqL : qLow≤q) :
    AntitoneOn (kind.primary q) (Icc 0 (-E.y)) := by
  apply antiOn_of_hasDeriv_nonpos (kind.continuous_primary q).continuousOn
  · intro b hb
    exact (I.derivative hqL (Ioo_subset_Icc_self hb)).1
  · intro b hb
    exact neg_nonpos.mpr (I.derivative hqL (Ioo_subset_Icc_self hb)).2.1

theorem ArcSource.mixed_projection_mono {q b p : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hqL : qLow≤q)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10 : ℝ))
    (j : Fin 4) (hj : j=0 ∨ j=1) :
    quarterProjection E H p j≤quarterProjection (kind.point q b) H p j := by
  have hEa : E.a≤kind.primary q b := by
    have hh := ArcSource.primary_antitone I hqL hb
      (show -E.y∈Icc 0 (-E.y) from ⟨neg_nonneg.mpr I.nonpos,le_rfl⟩) hb.2
    have heq : kind.primary q (-E.y)=E.a := congrArg SignedPoint.a I.initial
    rwa [heq] at hh
  have ht := transport_trig hp
  rcases hj with rfl | rfl
  · simp [quarterProjection,ArcKind.point]
    linarith [hb.2]
  · have hprim := mul_nonneg (sub_nonneg.mpr hEa) ht.2.2.1
    have htan := mul_nonneg (show 0≤ -E.y-b by linarith [hb.2])
      (show 0≤Real.cos p by linarith [ht.1])
    simp [quarterProjection,ArcKind.point]
    linarith

theorem coupledSlack_actual (kind : ArcKind) {q qD P e x : ℝ} (H : SignedPoint)
    (j : Fin 4) (hj : j=0 ∨ j=1) (hp : e+x∈Icc 0 (7/10 : ℝ)) :
    coupledSlack kind q qD P e H j x=
      quarterProjection (coupledPoint kind q qD P x) H (e+x) j-edgeWidth (e+x) :=
  mixedSlack_actual kind q H (coupledTangent qD P x) hj hp

theorem ArcSource.coupled_hasDerivAt {q qD P e x : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hqL : qLow≤q)
    (hb : coupledTangent qD P x∈Icc 0 (-E.y))
    (hc : Real.cos x≠0) (hrad : 0<qD-(2-value P x)^2) (j : Fin 4) :
    HasDerivAt (coupledSlack kind q qD P e H j)
      (coupledDerivative kind q qD P e H j x) x := by
  have hD := (movingAnchor_derivatives hc hrad).1
  have hbder : HasDerivAt (coupledTangent qD P) (primaryGain qD P x) x :=
    (hD.const_sub 1).congr_deriv (neg_neg _)
  have hpder : HasDerivAt (fun z : ℝ => e+z) 1 x := by
    simpa using (hasDerivAt_id x).const_add e
  have hcder := (Real.hasDerivAt_cos (e+x)).comp x hpder
  have hsder := (Real.hasDerivAt_sin (e+x)).comp x hpder
  by_cases hj : j=0
  · have hfun : coupledSlack kind q qD P e H j=fun z =>
        (H.a-1/2)*Real.cos (e+z)+(H.y-1/2)*Real.sin (e+z)-coupledTangent qD P z-1/2 := by
      funext z
      simp [coupledSlack,mixedSlack,lowSlack,hj]
    rw [hfun]
    exact ((((hcder.const_mul (H.a-1/2)).fun_add (hsder.const_mul (H.y-1/2))).fun_sub
      hbder).sub_const (1/2)).congr_deriv (by
        simp only [coupledDerivative,mixedRate,hj,lowAngularRate,ite_true]; ring)
  · have ha := (I.derivative hqL hb).1.comp x hbder
    have hfun : coupledSlack kind q qD P e H j=fun z =>
        H.a-1/2+(kind.primary q (coupledTangent qD P z)-1/2)*Real.sin (e+z)-
          (coupledTangent qD P z+1/2)*Real.cos (e+z) := by
      funext z
      simp [coupledSlack,mixedSlack,ehSlack,hj]
    rw [hfun]
    exact (((hasDerivAt_const x (H.a-1/2)).fun_add
      ((ha.sub_const (1/2)).fun_mul hsder)).fun_sub
        ((hbder.add_const (1/2)).fun_mul hcder)).congr_deriv (by
          simp only [coupledDerivative,mixedRate,hj,ite_false,Function.comp_apply]; ring)

theorem Source.coupled_derivative_negative {q t e x : ℝ} {D T B E H : SignedPoint}
    {kind : ArcKind} (I : Source q t D T B) (J : ArcSource q E kind)
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted)
    (hx : x∈Ioc 0 t)
    (hnot : ¬quarterFeasible (point (B.a-1/2) x) B.reflect (-x) 0)
    (hb : coupledTangent D.circle (B.a-1/2) x∈Icc 0 (-E.y))
    (hp : e+x∈Icc 0 (21/100 : ℝ)) (j : Fin 4) (hj : j=0 ∨ j=1) :
    coupledDerivative kind q D.circle (B.a-1/2) e H j x< -(1/250) := by
  let a := primaryGain D.circle (B.a-1/2) x
  let b := coupledTangent D.circle (B.a-1/2) x
  have ha : 1<a := I.primary_gain hqU hx hnot
  let K := I.atAngle hqU hx hnot
  have hc := K.cuts hqU
  have hDa : 211/250<(movingAnchor D.circle (B.a-1/2) x).a := by
    have hsort := K.H_sorted.2
    rw [abs_of_nonneg K.H_nonneg] at hsort
    have h := hc.2.2.2.1.trans_le hsort
    rw [SignedPoint.reflect_circle] at h
    exact h
  have hbsmall : b<39/250 := by dsimp only [b,coupledTangent]; linarith only [hDa]
  have hpwide : e+x∈Icc 0 (7/10 : ℝ) := ⟨hp.1,by linarith only [hp.2]⟩
  rcases hj with rfl | rfl
  · have hrate := lowSpeed_bounds hHy hHs hpwide
    have hh : lowAngularRate H (e+x)<2/5 := hrate.2.1.trans_lt hrate.2.2
    simp only [coupledDerivative,mixedRate,ite_true]
    dsimp only [a] at ha
    linarith only [ha,hh]
  · let den := Real.cos (e+x)+kind.slope q b*Real.sin (e+x)
    let U := (kind.primary q b-1/2)*Real.cos (e+x)+(b+1/2)*Real.sin (e+x)
    let β := contactSpeed (kind.primary q b) b (kind.slope q b) (e+x)
    have hgeom := J.geometry hqL hb
    have hv := (J.derivative hqL hb).2
    have hdenβ := contactSpeed_positive hgeom.2.2.2.2.2.1 hb.1 hv.1 hpwide
    have hβ : β<199/200 := coupled_speed_bound kind hqL hqU ⟨hb.1,hbsmall⟩ hp
    have hcos : 97/100<Real.cos (e+x) := by
      have hh := Real.one_sub_sq_div_two_le_cos (x := e+x)
      have hs := pow_le_pow_left₀ hp.1 hp.2 2
      norm_num at hs
      linarith only [hh,hs]
    have hden : 97/100<den := by
      have hprod := mul_nonneg hv.1 (transport_trig hpwide).2.2.1
      dsimp only [den]
      linarith only [hprod,hcos]
    have hid : β*den=U := by
      dsimp only [β,den,U]; unfold contactSpeed; exact div_mul_cancel₀ _ hdenβ.1.ne'
    have hgap := mul_pos (show 0<a-β-1/200 by linarith only [ha,hβ]) hdenβ.1
    have hreserve : 1/250<a*den-U := by linarith only [hgap,hden,hid]
    norm_num only [coupledDerivative,mixedRate,show (1:Fin 4)≠0 by decide,ite_false]
    change -(a*den-U)< -(1/250)
    linarith only [hreserve]

end DirectNegativeT
end SquaresInCircles.Eight
end
end
end
