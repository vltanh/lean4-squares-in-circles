module

public import SquaresInCircles.Eight.Words.Outside.ERates

/-!
# Eight squares: improvement rates for a nonpositive E outside its frame

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
    (1/2) using 1 <;> simp [lowSlack,lowAngularRate] <;> ring

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
