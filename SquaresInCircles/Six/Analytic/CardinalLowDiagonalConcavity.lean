import SquaresInCircles.Six.Analytic.CardinalLowDiagonalFormula

/-!
# The sign/order geometry of the cardinal-W low-D domain

For w<=0 the domain is its original rectangle. For w>=0 it is the quadrilateral
0<=w<=2/5, w<=d<=1/2. Coordinate concavity and the actual diagonal edge d=w
reduce these regions to six distinct original vertices. The D-sourced radical
need not be concave by itself: its curvature is compensated by the pair-width
terms before the endpoint reduction.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

lemma cardLowSmooth_concave_w (ds positive : Bool) {d l u : ℝ}
    (hl : -2/5≤l) (hu : u≤2/5) (hpos : positive=true → 0≤l)
    (hmap : ∀ x∈Set.Icc l u,0≤d-x ∧ d-x≤9/10) :
    ConcaveOn ℝ (Set.Icc l u) (fun w => cardLowSmooth ds positive w d) := by
  have hF := cardLowF_concave ds positive hl hu hpos
  have hH := concave_affine_argument (cardLowH_concave ds)
    (a := -1) (b := d) (by intro x hx; simpa only [neg_one_mul,neg_add_eq_sub,Set.mem_Icc] using hmap x hx)
  have hC := concave_constant (cardLowC ds+cardLowG ds d) l u
  have h := (hC.add hF).add hH
  apply h.congr
  intro x _
  dsimp [cardLowSmooth]
  have he : -1*x+d=d-x := by ring
  rw [he]
  ring

lemma cardLowSmooth_concave_d (ds positive : Bool) {w l u : ℝ}
    (hl : 0≤l) (hu : u≤1/2)
    (hmap : ∀ x∈Set.Icc l u,0≤x-w ∧ x-w≤9/10) :
    ConcaveOn ℝ (Set.Icc l u) (cardLowSmooth ds positive w) := by
  cases ds
  · have hG := cardLowG_false_concave hl hu
    have hH := concave_affine_argument (cardLowH_concave false)
      (a := 1) (b := -w) (by intro x hx; simpa only [one_mul,sub_eq_add_neg,Set.mem_Icc] using hmap x hx)
    have hC := concave_constant (cardLowC false+cardLowF false positive w) l u
    have h := (hC.add hG).add hH
    apply h.congr
    intro x _
    simp only [cardLowSmooth,one_mul,sub_eq_add_neg,Pi.add_apply]
  · have h := rotating_trig_concave
      (C := cardLowC true+cardLowF true positive w)
      (A := (43:ℝ)/100*(387/1000)) (B := (43:ℝ)/100*(387/1000))
      (G := (27:ℝ)/100) (H := (27:ℝ)/100) (c := -w)
      (R := (1689:ℝ)/1000) (p := (30:ℝ)/100) (q := (27:ℝ)/100) (L := (1:ℝ)/4)
      (l := l) (u := u)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun x hx => by
        have hbase := cardLow_trig (x := x) ⟨hl.trans hx.1,by linarith [hx.2]⟩
        have hpair := (cardLow_trig (hmap x hx)).2.2
        change 1/4≤(43/100*(387/1000))*Real.cos x+(43/100*(387/1000))*Real.sin x+
          (27/100)*Real.cos (x-w)+(27/100)*Real.sin (x-w)
        linarith [hbase.1,hbase.2.1])
    apply h.congr
    intro x _
    dsimp [cardLowSmooth,cardLowG,cardLowH,cardLowAlpha,cardLowMu]
    have he : x+-w=x-w := by ring
    rw [he]
    ring

lemma cardLowSmooth_diagonal_concave (ds : Bool) :
    ConcaveOn ℝ (Set.Icc 0 (2/5)) (fun x => cardLowSmooth ds true x x) := by
  cases ds
  · have hF := cardLowF_concave false true (l := 0) (u := (2:ℝ)/5)
      (by norm_num) le_rfl (by intro _; norm_num)
    have hG := cardLowG_false_concave (l := 0) (u := (2:ℝ)/5) (by norm_num) (by norm_num)
    have hC := concave_constant (cardLowC false+cardLowH false 0) 0 (2/5)
    have h := hC.add (hF.add hG)
    apply h.congr
    intro x _
    simp only [cardLowSmooth,sub_self,Pi.add_apply]
    ring
  · have h := rotating_trig_concave
      (C := cardLowC true+cardLowH true 0)
      (A := (30:ℝ)/100+(43/100)*(387/1000))
      (B := (30:ℝ)/100+(43/100)*(387/1000)) (G := 0) (H := 0) (c := 0)
      (R := (1689:ℝ)/1000) (p := (30:ℝ)/100) (q := (27:ℝ)/100) (L := (1:ℝ)/4)
      (l := 0) (u := 2/5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun x hx => by
        have ht := (cardLow_trig (x := x) ⟨hx.1,by linarith [hx.2]⟩).2.2
        nlinarith)
    apply h.congr
    intro x _
    dsimp [cardLowSmooth,cardLowF,cardLowG,cardLowH,cardLowAlpha,cardLowBeta,cardLowMu]
    rw [sub_self]
    ring

/-- Six exact geometric endpoint proofs suffice for either source. -/
theorem cardLow_positive_of_vertices (ds : Bool) {w d : ℝ}
    (hw : -2/5≤w ∧ w≤2/5) (hd : 0≤d ∧ d≤1/2) (hwd : w≤d)
    (hL0 : 0<cardLowSmooth ds false (-2/5) 0)
    (hLD : 0<cardLowSmooth ds false (-2/5) (1/2))
    (h00 : 0<cardLowSmooth ds false 0 0)
    (h0D : 0<cardLowSmooth ds false 0 (1/2))
    (hUU : 0<cardLowSmooth ds true (2/5) (2/5))
    (hUD : 0<cardLowSmooth ds true (2/5) (1/2)) : 0<cardLowGap ds w d := by
  unfold cardLowGap
  split_ifs with hpos
  · have hdiag := positive_on_concave_interval (cardLowSmooth_diagonal_concave ds)
      ⟨hpos,hw.2⟩
      (by simpa only [cardLowSmooth_zero_sign] using h00) hUU
    have htop := positive_on_concave_interval
      (cardLowSmooth_concave_w ds true (d := (1:ℝ)/2) (l := 0) (u := (2:ℝ)/5)
        (by norm_num) le_rfl (by intro _; norm_num)
        (by intro x hx; constructor <;> linarith [hx.1,hx.2]))
      ⟨hpos,hw.2⟩ (by simpa only [cardLowSmooth_zero_sign] using h0D) hUD
    exact positive_on_concave_interval
      (cardLowSmooth_concave_d ds true (w := w) (l := w) (u := (1:ℝ)/2) hpos le_rfl
        (by intro x hx; constructor <;> linarith [hx.1,hx.2]))
      ⟨hwd,hd.2⟩ hdiag htop
  · have hwn : w≤0 := (lt_of_not_ge hpos).le
    exact positive_on_separately_concave_rectangle ⟨hw.1,hwn⟩ hd
      (fun y hy => cardLowSmooth_concave_w ds false (d := y) (l := -(2:ℝ)/5) (u := 0)
        le_rfl (by norm_num) (by intro h; cases h)
        (by intro x hx; constructor <;> linarith [hy.1,hy.2,hx.1,hx.2]))
      (cardLowSmooth_concave_d ds false (w := -(2:ℝ)/5) (l := 0) (u := (1:ℝ)/2)
        (by norm_num) le_rfl (by intro x hx; constructor <;> linarith [hx.1,hx.2]))
      (cardLowSmooth_concave_d ds false (w := 0) (l := 0) (u := (1:ℝ)/2)
        (by norm_num) le_rfl (by intro x hx; constructor <;> linarith [hx.1,hx.2]))
      hL0 hLD h00 h0D

end SquaresInCircles.Six.Analytic
