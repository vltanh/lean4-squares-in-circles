import SquaresInCircles.Six.Analytic.MixedCardinalWest.Concavity

/-!
# Cardinal W, missing south wing: the scalar bound

With the weights `4, 3, 3` on the edges C–W, W–D and D–S, the force on D has
length `6 sin ((d-w)/2)`. When D and S are separated along the secondary axis
of D, their phase gap `π/2 + s - d` is at least `π/4`, and then for
`s ≤ 12/25` the term `cos (d-s) + sin (d-s)` of S is at least its value at
`s = 12/25`, since `cos x + sin x` increases on `[0, π/4]`. What remains is a
function `gap w d` of the angles of W and D, concave in `d`, and concave in
`w` on each side of `w = 0`. Taylor bounds of `sin` and `cos` and rational
bounds of the radicals make it positive at the six points with
`w ∈ {-2/5, 0, 2/5}` and `d ∈ {1/2, π/4}`, and so on all of
`[-2/5, 2/5] × [1/2, π/4]`.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.MixedCardinalSouth
open Normalization

def westTerm (w : ℝ) : ℝ := MixedCardinalWest.southTerm (-w)
def chordTerm (q : ℝ) : ℝ := 3*Real.sin q-6*R0*Real.sin (q/2)
def widthTerm (d : ℝ) : ℝ := 3*(Real.cos (d-12/25)+Real.sin (d-12/25))
def gap (w d : ℝ) : ℝ := 8-4*c0-3*R0+westTerm w+chordTerm (d-w)+widthTerm d

private lemma offset {w d : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 2/5) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) :
    0 ≤ d-w ∧ d-w ≤ 6/5 := by
  constructor <;> linarith [hw.1,hw.2,hd.1,hd.2,Real.pi_lt_d2]

lemma chordTerm_concave : ConcaveOn ℝ (Set.Icc 0 (6/5)) chordTerm := by
  let f' : ℝ → ℝ := fun q => 3*Real.cos q-3*R0*Real.cos (q/2)
  let f'' : ℝ → ℝ := fun q => -3*Real.sin q+(3*R0/2)*Real.sin (q/2)
  have hf (q : ℝ) : HasDerivAt chordTerm (f' q) q := by
    have hh := (((hasDerivAt_id q).div_const 2).sin).const_mul (6*R0)
    convert ((Real.hasDerivAt_sin q).const_mul 3).sub hh using 1
    · funext y
      simp only [chordTerm,Pi.sub_apply,id]
    · simp only [f',id]
      ring
  have hff (q : ℝ) : HasDerivAt f' (f'' q) q := by
    have hh := (((hasDerivAt_id q).div_const 2).cos).const_mul (3*R0)
    convert ((Real.hasDerivAt_cos q).const_mul 3).sub hh using 1
    · funext y
      simp only [f',Pi.sub_apply,id]
    · simp only [f'',id]
      ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (6/5))
    (f := chordTerm) (f' := f') (f'' := f'')
    (fun q _ => (hf q).continuousAt.continuousWithinAt)
  · intro q _; exact (hf q).hasDerivWithinAt
  · intro q _; exact (hff q).hasDerivWithinAt
  · intro q hq
    have h := interior_subset hq
    have hsq := mul_nonneg (show 0 ≤ 3/5-q/2 by linarith [h.2])
      (show 0 ≤ 3/5+q/2 by linarith [h.1])
    have hc : 41/50 ≤ Real.cos (q/2) := by
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := q/2)]
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ q/2 by linarith [h.1]) (show q/2 ≤ Real.pi by linarith [h.2,Real.pi_gt_d2])
    have hp := mul_nonpos_of_nonpos_of_nonneg
      (show -6*Real.cos (q/2)+3*R0/2 ≤ 0 by linarith [R0_lt_1689_1000]) hs
    have hid : Real.sin q=2*Real.sin (q/2)*Real.cos (q/2) := by
      simpa only [show 2*(q/2)=q by ring] using Real.sin_two_mul (q/2)
    dsimp [f'']
    nlinarith only [hp,hid]

lemma widthTerm_concave :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) widthTerm := by
  have hc : ConcaveOn ℝ (Set.Icc 0 (2/5)) (radicalTrig 3 3 1 0 0) := by
    apply radicalTrig_concave (by norm_num) (by norm_num)
    · intro _ _; norm_num
    · intro x hx
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
        (by linarith [hx.2,Real.pi_gt_d2])
      have hc := Real.cos_nonneg_of_mem_Icc
        (show x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
          constructor <;> linarith [hx.1,hx.2,Real.pi_gt_d2])
      nlinarith
  have h := concave_affine_argument (a := 1) (b := -(12/25)) hc
    (l := 1/2) (u := Real.pi/4) (fun d hd => by
      constructor <;> linarith [hd.1,hd.2,Real.pi_lt_d2])
  convert h using 1
  funext d
  dsimp [radicalTrig,widthTerm]
  ring_nf

lemma westTerm_negative_concave : ConcaveOn ℝ (Set.Icc (-(2/5)) 0) westTerm := by
  have h := concave_affine_argument (a := -1) (b := 0)
    MixedCardinalWest.southTerm_positive_concave
    (l := -(2/5)) (u := 0) (fun w hw => by constructor <;> linarith [hw.1,hw.2])
  convert h using 1
  funext w
  simp [westTerm]

lemma westTerm_positive_concave : ConcaveOn ℝ (Set.Icc 0 (2/5)) westTerm := by
  have h := concave_affine_argument (a := -1) (b := 0)
    MixedCardinalWest.southTerm_negative_concave
    (l := 0) (u := 2/5) (fun w hw => by constructor <;> linarith [hw.1,hw.2])
  convert h using 1
  funext w
  simp [westTerm]

lemma gap_diagonal_concave {w : ℝ} (hw : -(2/5) ≤ w ∧ w ≤ 2/5) :
    ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (fun d => gap w d) := by
  have hq0 := concave_affine_argument (a := 1) (b := -w) chordTerm_concave
    (l := 1/2) (u := Real.pi/4) (fun d hd => by simpa [sub_eq_add_neg] using offset hw hd)
  have hq : ConcaveOn ℝ (Set.Icc (1/2) (Real.pi/4)) (fun d => chordTerm (d-w)) := by
    convert hq0 using 1
    funext d
    congr 1
    ring
  exact ((concave_constant (8-4*c0-3*R0+westTerm w) (1/2) (Real.pi/4)).add hq).add
    widthTerm_concave

lemma gap_west_concave {d l u : ℝ} (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4)
    (hl : -(2/5) ≤ l) (hu : u ≤ 2/5)
    (hw : ConcaveOn ℝ (Set.Icc l u) westTerm) :
    ConcaveOn ℝ (Set.Icc l u) (fun w => gap w d) := by
  have hq0 := concave_affine_argument (a := -1) (b := d) chordTerm_concave
    (l := l) (u := u) (fun w hmem => by
      have h := offset ⟨hl.trans hmem.1,hmem.2.trans hu⟩ hd
      constructor <;> linarith [h.1,h.2])
  have hq : ConcaveOn ℝ (Set.Icc l u) (fun w => chordTerm (d-w)) := by
    convert hq0 using 1
    funext w
    congr 1
    ring
  have h := ((concave_constant (8-4*c0-3*R0) l u).add hw).add hq
  exact h.add (concave_constant (widthTerm d) l u)

private lemma sin_half_root {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 6/5) :
    6*Real.sin (q/2)=Real.sqrt (18-18*Real.cos q) := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ q/2 by linarith [hq.1]) (show q/2 ≤ Real.pi by linarith [hq.2,Real.pi_gt_d2])
  have hc : Real.cos q=1-2*Real.sin (q/2)^2 := by
    have h := Real.cos_two_mul (q/2)
    rw [show 2*(q/2)=q by ring] at h
    nlinarith only [h,Real.sin_sq_add_cos_sq (q/2)]
  rw [show 18-18*Real.cos q=(6*Real.sin (q/2))^2 by nlinarith only [hc],
    Real.sqrt_sq (by positivity)]

private lemma sqrt_upper {x U : ℝ} (hU : 0 ≤ U) (hx : x ≤ U^2) : Real.sqrt x ≤ U := by
  have h := Real.sqrt_le_sqrt hx
  simpa only [Real.sqrt_sq hU] using h

private lemma small_trig :
    921/1000 ≤ Real.cos ((2:ℝ)/5) ∧
    389/1000 ≤ Real.sin ((2:ℝ)/5) ∧ Real.sin ((2:ℝ)/5) ≤ 39/100 ∧
    877/1000 ≤ Real.cos ((1:ℝ)/2) ∧ 479/1000 ≤ Real.sin ((1:ℝ)/2) ∧
    621/1000 ≤ Real.cos ((9:ℝ)/10) ∧ 783/1000 ≤ Real.sin ((9:ℝ)/10) ∧
    199/200 ≤ Real.cos ((1:ℝ)/10) ∧ 99/1000 ≤ Real.sin ((1:ℝ)/10) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [Seven.cos_lower_six (x := (2:ℝ)/5) (by norm_num)]
  · nlinarith only [Seven.sin_lower_seven (x := (2:ℝ)/5) (by norm_num)]
  · nlinarith only [Seven.sin_upper_five (x := (2:ℝ)/5) (by norm_num)]
  · nlinarith only [Seven.cos_lower_six (x := (1:ℝ)/2) (by norm_num)]
  · nlinarith only [Seven.sin_lower_seven (x := (1:ℝ)/2) (by norm_num)]
  · nlinarith only [Seven.cos_lower_six (x := (9:ℝ)/10) (by norm_num)]
  · nlinarith only [Seven.sin_lower_seven (x := (9:ℝ)/10) (by norm_num)]
  · nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/10)]
  · nlinarith only [Seven.sin_lower_seven (x := (1:ℝ)/10) (by norm_num)]

private lemma shifted_trig :
    375417/1000000 ≤ Real.cos (Real.pi/4+2/5) ∧
    92617/100000 ≤ Real.sin (Real.pi/4+2/5) ∧
    92617/100000 ≤ Real.cos (Real.pi/4-2/5) ∧
    375417/1000000 ≤ Real.sin (Real.pi/4-2/5) ∧
    707/1000 ≤ Real.cos (Real.pi/4) ∧ 707/1000 ≤ Real.sin (Real.pi/4) := by
  have hr : (707:ℝ)/1000 ≤ Real.sqrt 2/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have ht := small_trig
  have hm := mul_le_mul hr
    (show (531:ℝ)/1000 ≤ Real.cos (2/5)-Real.sin (2/5) by linarith [ht.1,ht.2.2.1])
    (by norm_num : (0:ℝ) ≤ 531/1000) (by positivity : 0 ≤ Real.sqrt 2/2)
  have hp := mul_le_mul hr
    (show (131:ℝ)/100 ≤ Real.cos (2/5)+Real.sin (2/5) by linarith [ht.1,ht.2.1])
    (by norm_num : (0:ℝ) ≤ 131/100) (by positivity : 0 ≤ Real.sqrt 2/2)
  rw [Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,
    Real.cos_pi_div_four,Real.sin_pi_div_four]
  refine ⟨?_,?_,?_,?_,hr,hr⟩ <;> nlinarith only [hm,hp]

private lemma width_endpoints :
    101979/100000 ≤ Real.cos ((1:ℝ)/50)+Real.sin ((1:ℝ)/50) ∧
    627/500 ≤ Real.cos (Real.pi/4-12/25)+Real.sin (Real.pi/4-12/25) := by
  constructor
  · nlinarith only [Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/50),
      Real.sin_ge_sub_cube (x := (1:ℝ)/50) (by norm_num)]
  · have hr : (707:ℝ)/500 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
    have hc : (8869:ℝ)/10000 ≤ Real.cos (12/25) := by
      nlinarith only [Seven.cos_lower_six (x := (12:ℝ)/25) (by norm_num)]
    have hp := mul_le_mul hr hc (by norm_num : (0:ℝ) ≤ 8869/10000) (Real.sqrt_nonneg (2:ℝ))
    rw [Real.cos_sub,Real.sin_sub,Real.cos_pi_div_four,Real.sin_pi_div_four]
    nlinarith only [hp]

def westEnd : Fin 3 → ℝ := ![-2/5,0,2/5]
def diagonalEnd : Fin 2 → ℝ := ![1/2,Real.pi/4]
private def cosBound : Fin 3 → ℝ := ![921/1000,1,921/1000]
private def positiveSinBound : Fin 3 → ℝ := ![0,0,389/1000]
private def westRootBound : Fin 3 → ℝ := ![1979/500,5,2931/500]
private def gapSinBound : Fin 3 → Fin 2 → ℝ :=
  ![![783/1000,92617/100000],![479/1000,707/1000],![99/1000,375417/1000000]]
private def gapRootBound : Fin 3 → Fin 2 → ℝ :=
  ![![653/250,3353/1000],![186/125,2297/1000],![3/10,1153/1000]]
private def gapCosBound : Fin 3 → Fin 2 → ℝ :=
  ![![621/1000,375417/1000000],![877/1000,707/1000],![199/200,92617/100000]]
private def widthBound : Fin 2 → ℝ := ![101979/100000,627/500]

private lemma endpoint_bounds (i : Fin 3) (j : Fin 2) :
    cosBound i ≤ Real.cos (westEnd i) ∧
    positiveSinBound i ≤ max (Real.sin (westEnd i)) 0 ∧
    Real.sqrt (25+24*Real.sin (westEnd i)) ≤ westRootBound i ∧
    gapSinBound i j ≤ Real.sin (diagonalEnd j-westEnd i) ∧
    Real.sqrt (18-18*Real.cos (diagonalEnd j-westEnd i)) ≤ gapRootBound i j ∧
    widthBound j ≤ Real.cos (diagonalEnd j-12/25)+Real.sin (diagonalEnd j-12/25) := by
  obtain ⟨hc4,hs4,hs4u,hc5,hs5,hc9,hs9,hc1,hs1⟩ := small_trig
  obtain ⟨hqcp,hqsp,hqcm,hqsm,hcq,hsq⟩ := shifted_trig
  have hcos : gapCosBound i j ≤ Real.cos (diagonalEnd j-westEnd i) := by
    fin_cases i <;> fin_cases j <;>
      norm_num [gapCosBound,diagonalEnd,westEnd] at * <;> linarith
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · fin_cases i <;> norm_num [cosBound,westEnd] <;> linarith
  · fin_cases i
    · exact le_max_right _ _
    · simp [positiveSinBound,westEnd]
    · simpa [positiveSinBound,westEnd] using hs4.trans (le_max_left _ _)
  · apply sqrt_upper
    · fin_cases i <;> norm_num [westRootBound]
    · fin_cases i <;> norm_num [westEnd,westRootBound] at * <;> nlinarith
  · fin_cases i <;> fin_cases j <;>
      norm_num [gapSinBound,diagonalEnd,westEnd] at * <;> linarith
  · apply sqrt_upper
    · fin_cases i <;> fin_cases j <;> norm_num [gapRootBound]
    · fin_cases i <;> fin_cases j <;>
        norm_num [gapCosBound,gapRootBound] at * <;> nlinarith only [hcos]
  · have hh := width_endpoints
    fin_cases j <;> norm_num [diagonalEnd,widthBound] at * <;> linarith

private def reserve (i : Fin 3) (j : Fin 2) : ℝ :=
  8-4*(113/1000)-3*(1689/1000)+4*cosBound i+4*positiveSinBound i-
    (1689/1000)*westRootBound i+3*gapSinBound i j-
    (1689/1000)*gapRootBound i j+3*widthBound j

private lemma reserve_positive (i : Fin 3) (j : Fin 2) : (9569:ℝ)/500000 ≤ reserve i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [reserve,cosBound,positiveSinBound,westRootBound,gapSinBound,gapRootBound,widthBound]

lemma endpoint_positive (i : Fin 3) (j : Fin 2) : 0 < gap (westEnd i) (diagonalEnd j) := by
  obtain ⟨hc,hs,hrW,hq,hrD,hwidth⟩ := endpoint_bounds i j
  have hw : -(2/5) ≤ westEnd i ∧ westEnd i ≤ 2/5 := by
    fin_cases i <;> norm_num [westEnd]
  have hd : 1/2 ≤ diagonalEnd j ∧ diagonalEnd j ≤ Real.pi/4 := by
    fin_cases j <;> norm_num [diagonalEnd] <;> linarith [Real.pi_gt_d2]
  have hroot := sin_half_root (offset hw hd)
  have hmul := mul_le_mul_of_nonneg_left
    (show 3+Real.sqrt (25+24*Real.sin (westEnd i))+
      Real.sqrt (18-18*Real.cos (diagonalEnd j-westEnd i)) ≤
      3+westRootBound i+gapRootBound i j by linarith) R0_nonneg
  have hr := mul_le_mul_of_nonneg_right R0_lt_1689_1000.le
    (show 0 ≤ 3+westRootBound i+gapRootBound i j by
      fin_cases i <;> fin_cases j <;> norm_num [westRootBound,gapRootBound])
  have hC : c0 ≤ 113/1000 := by dsimp [c0]; linarith [rho0_upper]
  have hp := reserve_positive i j
  dsimp [reserve] at hp
  have hroot' : 6*R0*Real.sin ((diagonalEnd j-westEnd i)/2)=
      R0*Real.sqrt (18-18*Real.cos (diagonalEnd j-westEnd i)) := by
    rw [← hroot]
    ring
  dsimp [gap,westTerm,MixedCardinalWest.southTerm,chordTerm,widthTerm]
  rw [Real.cos_neg,Real.sin_neg,neg_neg,mul_neg,sub_neg_eq_add]
  linarith only [hc,hs,hq,hwidth,hmul,hr,hC,hp,hroot']

/-- `gap w d` is positive on `[-2/5, 2/5] × [1/2, π/4]`. -/
theorem positive {w d : ℝ}
    (hw : -(2/5) ≤ w ∧ w ≤ 2/5) (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) : 0 < gap w d := by
  have he (i : Fin 3) : 0 < gap (westEnd i) d := by
    have hwi : -(2/5) ≤ westEnd i ∧ westEnd i ≤ 2/5 := by
      fin_cases i <;> norm_num [westEnd]
    exact positive_on_concave_interval (gap_diagonal_concave hwi) hd
      (endpoint_positive i 0) (endpoint_positive i 1)
  have h0 : 0 < gap (-(2/5)) d := by
    have h := he 0
    rwa [show westEnd 0 = -(2/5) by norm_num [westEnd]] at h
  by_cases hw0 : w ≤ 0
  · exact positive_on_concave_interval (f := fun w => gap w d)
      (gap_west_concave hd le_rfl (by norm_num) westTerm_negative_concave)
      ⟨hw.1,hw0⟩ h0 (he 1)
  · exact positive_on_concave_interval (f := fun w => gap w d)
      (gap_west_concave hd (by norm_num) le_rfl westTerm_positive_concave)
      ⟨le_of_not_ge hw0,hw.2⟩ (he 1) (he 2)

/-- For `s ≤ 12/25` and a phase gap `π/2 + s - d ≥ π/4`, the term
`cos (d-s) + sin (d-s)` is at least its value at `s = 12/25`. -/
lemma south_width_lower {s d : ℝ}
    (hd : 1/2 ≤ d ∧ d ≤ Real.pi/4) (hs : s ≤ 12/25)
    (hgap : Real.pi/4 ≤ Real.pi/2+s-d) :
    Real.cos (d-12/25)+Real.sin (d-12/25) ≤
      Real.cos (d-s)+Real.sin (d-s) := by
  apply cos_add_sin_mono
  · linarith [hd.1]
  · linarith
  · linarith

/-- `√(18 - 18 cos q) = 6 sin (q/2)` for `0 ≤ q ≤ 6/5`. -/
lemma chord_norm {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 6/5) :
    Real.sqrt (18-18*Real.cos q)=6*Real.sin (q/2) := (sin_half_root hq).symm

end SquaresInCircles.Six.Analytic.MixedCardinalSouth
