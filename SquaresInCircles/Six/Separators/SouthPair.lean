import SquaresInCircles.Six.Separators.Axes
import SquaresInCircles.Six.Separators.Profiles

/-!
# Six squares: D and S along a secondary axis

In every normalized packing D and S are separated along the secondary axis of D
or along that of S. For `s ≤ d` this is the dominance of the secondary axes
(`south_secondary_choice_of_angle`). If `s > d`, then S is separated from C
along its own axis, since otherwise `s < 2/5 < d`, and `r = s - d` lies in
`[0, 1/6]`. Multiplying the separating inequalities of D and S from C by
`sin s` and `cos d` and adding them cancels the first coordinate of the centre
of C, and leaves a reserve that is concave in `d` and in `s` on the triangle
`1/2 ≤ d ≤ s ≤ 2/3`: so `a_D + a_S > 2.17 + r/3`. Then the projections of
the difference of the centres on the two secondary axes sum to more than twice
the threshold `(1 + cos r + sin r)/2`, and one of the two axes separates.
-/

noncomputable section
namespace SquaresInCircles.Six
open Normalization

/-- The trigonometric part of the bound on `a_D + a_S` for D and S on their own
axes, with `1/2 - c_y ≥ 0.387`, `a_S ≤ 1.113` and `0.557 = 2.17 - 1.113 - 1/2`. -/
def coupledOwnReserve (d s : ℝ) : ℝ :=
  0.387*Real.cos (s-d)+Real.sin s*Real.cos d-
    0.613*Real.cos d-(0.557+(s-d)/3)*Real.sin s

private def coupledA (s : ℝ) : ℝ := 0.387*Real.cos s+Real.sin s-0.613
private def coupledB (s : ℝ) : ℝ := 0.387*Real.sin s

private lemma coupled_formula (d s : ℝ) :
    coupledOwnReserve d s=coupledA s*Real.cos d+coupledB s*Real.sin d+
      (Real.sin s/3)*d-(0.557+s/3)*Real.sin s := by
  dsimp [coupledOwnReserve,coupledA,coupledB]
  rw [Real.cos_sub]
  ring

private lemma coupled_trig {x : ℝ} (hx : 1/2≤x ∧ x≤2/3) :
    7/9≤Real.cos x ∧ 9/20≤Real.sin x := by
  obtain ⟨hs,-,hc,-⟩ := trig_bracket (by norm_num) (by linarith [Real.pi_gt_d2]) hx
  norm_num at hs hc
  exact ⟨by linarith,by linarith⟩

private lemma coupled_concave_d {s : ℝ} (hs : 1/2≤ s ∧ s≤2/3) :
    ConcaveOn ℝ (Set.Icc (1/2) s) (fun d => coupledOwnReserve d s) := by
  have ht := coupled_trig hs
  have hA : 0≤coupledA s := by dsimp [coupledA]; linarith [ht.1,ht.2]
  have hB : 0≤coupledB s := by dsimp [coupledB]; linarith [ht.2]
  have htrig := harmonic_concave (A := coupledA s) (B := coupledB s) (l := 1/2) (u := s)
    fun x hx => harmonic_nonneg hA hB ⟨by linarith [hx.1],by linarith [hx.2,hs.2,Real.pi_gt_d2]⟩
  have hlinear := affine_concave (Real.sin s/3)
    (-(0.557+s/3)*Real.sin s) (1/2) s
  apply (htrig.add hlinear).congr
  intro d _
  simp only [Pi.add_apply,harmonic]
  rw [coupled_formula]
  ring

private def coupledLeft (s : ℝ) : ℝ :=
  (0.387*Real.cos (1/2))*Real.cos s+
    (0.387*Real.sin (1/2)+Real.cos (1/2)-0.557)*Real.sin s-
    0.613*Real.cos (1/2)-((s-1/2)/3)*Real.sin s

private lemma coupled_left_formula (s : ℝ) : coupledOwnReserve (1/2) s=coupledLeft s := by
  dsimp [coupledOwnReserve,coupledLeft]
  rw [Real.cos_sub]
  ring

private lemma coupled_left_concave : ConcaveOn ℝ (Set.Icc (1/2) (2/3)) coupledLeft := by
  let A := 0.387*Real.cos (1/2)
  let B := 0.387*Real.sin (1/2)+Real.cos (1/2)-0.557
  let f' : ℝ→ℝ := fun s => -A*Real.sin s+B*Real.cos s-
    Real.sin s/3-((s-1/2)/3)*Real.cos s
  let f'' : ℝ→ℝ := fun s => -A*Real.cos s-B*Real.sin s-
    (2/3)*Real.cos s+((s-1/2)/3)*Real.sin s
  have hA : 0≤A := by dsimp [A]; linarith [trig_bracket_half.1]
  have hB : 0≤B := by dsimp [B]; linarith [trig_bracket_half.1,trig_bracket_half.2.2.1]
  have hu (s : ℝ) : HasDerivAt (fun x : ℝ => (x-1/2)/3) (1/3) s :=
    ((hasDerivAt_id' s).sub_const (1/2)).div_const 3
  have hf (s : ℝ) : HasDerivAt coupledLeft (f' s) s := by
    have h := ((((Real.hasDerivAt_cos s).const_mul A).fun_add
      ((Real.hasDerivAt_sin s).const_mul B)).sub_const
      (0.613*Real.cos (1/2))).fun_sub ((hu s).fun_mul (Real.hasDerivAt_sin s))
    refine h.congr_deriv ?_
    simp only [f']
    ring
  have hff (s : ℝ) : HasDerivAt f' (f'' s) s := by
    have h := ((((Real.hasDerivAt_sin s).const_mul (-A)).fun_add
      ((Real.hasDerivAt_cos s).const_mul B)).fun_sub
      ((Real.hasDerivAt_sin s).div_const 3)).fun_sub ((hu s).fun_mul (Real.hasDerivAt_cos s))
    refine h.congr_deriv ?_
    simp only [f'']
    ring
  refine concave_of_deriv2 (fun s _ => hf s) (fun s _ => hff s) (fun s hsc => ?_)
  have ht := coupled_trig hsc
  have hAc := mul_nonneg hA (show 0≤Real.cos s by linarith [ht.1])
  have hBs := mul_nonneg hB (show 0≤Real.sin s by linarith [ht.2])
  have hupper := mul_le_mul (show (s-1/2)/3≤(1:ℝ)/18 by linarith [hsc.2])
    (Real.sin_le_one s) (show 0≤Real.sin s by linarith [ht.2]) (by norm_num : (0:ℝ)≤1/18)
  dsimp [f'']
  nlinarith only [hAc,hBs,hupper,ht.1]

private def coupledDiagonal (s : ℝ) : ℝ :=
  0.387+Real.sin (2*s)/2-0.613*Real.cos s-0.557*Real.sin s

private lemma coupled_diagonal_formula (s : ℝ) : coupledOwnReserve s s=coupledDiagonal s := by
  simp only [coupledOwnReserve,coupledDiagonal,sub_self,Real.cos_zero,Real.sin_two_mul]
  ring

private lemma coupled_diagonal_concave :
    ConcaveOn ℝ (Set.Icc (1/2) (2/3)) coupledDiagonal := by
  let f' : ℝ→ℝ := fun s => Real.cos (2*s)+0.613*Real.sin s-0.557*Real.cos s
  let f'' : ℝ→ℝ := fun s => -2*Real.sin (2*s)+0.613*Real.cos s+0.557*Real.sin s
  have hu (s : ℝ) : HasDerivAt (fun x : ℝ => 2*x) 2 s := by
    simpa using (hasDerivAt_id s).const_mul 2
  have hf (s : ℝ) : HasDerivAt coupledDiagonal (f' s) s := by
    have h := (((((hu s).sin).div_const 2).const_add 0.387).fun_sub
      ((Real.hasDerivAt_cos s).const_mul 0.613)).fun_sub
      ((Real.hasDerivAt_sin s).const_mul 0.557)
    refine h.congr_deriv ?_
    simp only [f']
    ring
  have hff (s : ℝ) : HasDerivAt f' (f'' s) s := by
    have h := (((hu s).cos).fun_add ((Real.hasDerivAt_sin s).const_mul 0.613)).fun_sub
      ((Real.hasDerivAt_cos s).const_mul 0.557)
    refine h.congr_deriv ?_
    simp only [f'']
    ring
  refine concave_of_deriv2 (fun s _ => hf s) (fun s _ => hff s) (fun s hsc => ?_)
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2)≤(1:ℝ) by linarith [Real.pi_pos])
    (show 2*s≤Real.pi/2 by linarith [hsc.2,Real.pi_gt_d2])
    (show 1≤2*s by linarith [hsc.1])
  have hp := Real.sin_ge_sub_cube (x := (1:ℝ)) (by norm_num)
  norm_num at hp
  dsimp [f'']
  linarith [Real.cos_le_one s,Real.sin_le_one s]

private lemma coupled_vertices :
    0<coupledOwnReserve (1/2) (1/2) ∧
    0<coupledOwnReserve (1/2) (2/3) ∧
    0<coupledOwnReserve (2/3) (2/3) := by
  obtain ⟨hc5l,hc5u,hs5l,hs5u⟩ := trig_bracket_half
  obtain ⟨hc6l,hc6u,hs6l,hs6u⟩ := trig_bracket_two_thirds
  have hprod5 := mul_le_mul hs5l hc5l (by norm_num)
    (show 0≤Real.sin (1/2) by linarith)
  have hprod6 := mul_le_mul hs6l hc6l (by norm_num)
    (show 0≤Real.sin (2/3) by linarith)
  have hprod56 := mul_le_mul hs6l hc5l (by norm_num)
    (show 0≤Real.sin (2/3) by linarith)
  have hcr := Real.one_sub_sq_div_two_le_cos (x := (1:ℝ)/6)
  refine ⟨?_,?_,?_⟩
  · norm_num [coupledOwnReserve]
    linarith
  · norm_num [coupledOwnReserve]
    linarith
  · norm_num [coupledOwnReserve]
    linarith

/-- The reserve is positive on the triangle `1/2 ≤ d ≤ s ≤ 2/3`. -/
theorem coupled_own_reserve_positive {d s : ℝ}
    (hd : 1/2≤d) (hds : d≤ s) (hs : s≤2/3) : 0<coupledOwnReserve d s := by
  have hleft : 0<coupledOwnReserve (1/2) s := by
    rw [coupled_left_formula]
    exact concave_gt_of_endpoints coupled_left_concave ⟨hd.trans hds,hs⟩
      (by rw [← coupled_left_formula]; exact coupled_vertices.1)
      (by rw [← coupled_left_formula]; exact coupled_vertices.2.1)
  have hdiag : 0<coupledOwnReserve s s := by
    rw [coupled_diagonal_formula]
    exact concave_gt_of_endpoints coupled_diagonal_concave ⟨hd.trans hds,hs⟩
      (by rw [← coupled_diagonal_formula]; exact coupled_vertices.1)
      (by rw [← coupled_diagonal_formula]; exact coupled_vertices.2.2)
  have h := concave_gt_of_endpoints (coupled_concave_d ⟨hd.trans hds,hs⟩)
    ⟨hd,hds⟩ hleft hdiag
  exact h

/-- A square in the disk has `3a + |b| < 3.34`, by Cauchy–Schwarz:
`3(a + 1/2) + (|b| + 1/2) ≤ √(10 Q0) < 5.34`. -/
lemma chart_three_radial_support {a b : ℝ} (hc : ContainedChart a |b|) :
    3*a+|b|<3.34 := by
  have hsq := sq_nonneg ((a+1/2)-3*(|b|+1/2))
  have hC := hc.containment
  have hpos : 0≤3*(a+1/2)+(|b|+1/2) := by linarith [hc.half_le,abs_nonneg b]
  have hbound : (3*(a+1/2)+(|b|+1/2))^2≤10*Q0 := by nlinarith only [hC,hsq]
  by_contra! h
  have hp := mul_nonneg
    (show 0≤3*(a+1/2)+(|b|+1/2)-5.34 by linarith)
    (show 0≤3*(a+1/2)+(|b|+1/2)+5.34 by linarith)
  norm_num [Q0] at hbound
  nlinarith

/-- D and S separated from C along their own axes at `1/2 ≤ d ≤ s ≤ 2/3` have
`a_D + a_S > 2.17 + (s - d)/3`. -/
lemma coupled_own_radial_sum {a b A B cx cy d s : ℝ}
    (hS : ContainedChart A |B|)
    (hy : cy≤c0) (hd : 1/2≤d) (hds : d≤ s) (hs : s≤2/3)
    (hCD : 0≤centralMargin .own (Real.pi+d) a b cx cy)
    (hCS : 0≤centralMargin .own (3*Real.pi/2+s) A B cx cy) :
    2.17+(s-d)/3<a+A := by
  have hcd := Real.cos_nonneg_of_mem_Icc
    (show d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd,hds,hs,Real.pi_gt_d2])
  have hsd := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤d by linarith) (by linarith [Real.pi_gt_d2])
  have hcs := Real.cos_nonneg_of_mem_Icc
    (show s∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd,hds,hs,Real.pi_gt_d2])
  have hss := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0≤s by linarith) (by linarith [Real.pi_gt_d2])
  have hcr := Real.cos_nonneg_of_mem_Icc
    (show s-d∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hd,hds,hs,Real.pi_gt_d2])
  have hDgap : 0≤a-1/2-(1/2-cx)*Real.cos d-(1/2-cy)*Real.sin d := by
    have e1 : Real.cos (Real.pi+d)=-Real.cos d := by rw [add_comm]; exact Real.cos_add_pi d
    have e2 : Real.sin (Real.pi+d)=-Real.sin d := by rw [add_comm]; exact Real.sin_add_pi d
    simp only [centralMargin,centralNormal,angularWidth,e1,e2,
      abs_neg,abs_of_nonneg hcd,abs_of_nonneg hsd] at hCD
    nlinarith only [hCD]
  have hSgap : 0≤A-1/2-(1/2-cy)*Real.cos s-(1/2+cx)*Real.sin s := by
    simp only [centralMargin,centralNormal,angularWidth,Real.cos_add,Real.sin_add,
      south_cos,south_sin,zero_mul,neg_one_mul,zero_sub,neg_neg,add_zero,abs_neg,
      abs_of_nonneg hcs,abs_of_nonneg hss] at hCS
    nlinarith only [hCS]
  have hDp := mul_nonneg hDgap hss
  have hSp := mul_nonneg hSgap hcd
  have hcy : 0.387≤1/2-cy := by dsimp [c0] at hy; linarith [rho0_bounds.2]
  have hcyprod := mul_nonneg (sub_nonneg.mpr hcy) hcr
  rw [Real.cos_sub] at hcyprod
  have hcombined : (Real.cos d+Real.sin s)/2+Real.sin s*Real.cos d+
      0.387*Real.cos (s-d)≤a*Real.sin s+A*Real.cos d := by
    rw [Real.cos_sub]
    linarith only [hDp,hSp,hcyprod]
  have hcoslower : 7/9≤Real.cos d := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := d)
    nlinarith only [hc,mul_nonneg (show 0≤2/3-d by linarith) (show 0≤2/3+d by linarith)]
  have hsinupper := Real.sin_le (show 0≤ s by linarith)
  have hdiff : 0≤Real.cos d-Real.sin s := by linarith
  have hAupper : A≤1.113 := by linarith [hS.a_le_rho0,rho0_bounds.2]
  have hAp := mul_le_mul_of_nonneg_right hAupper hdiff
  have hreserve := coupled_own_reserve_positive hd hds hs
  by_contra! hsum
  have hsumprod := mul_le_mul_of_nonneg_right hsum hss
  dsimp [coupledOwnReserve] at hreserve
  nlinarith only [hcombined,hAp,hsumprod,hreserve]

/-- For `r ∈ [0, 1/6]` and `a + A > 2.17 + r/3`, the separations of D and S
along their secondary axes sum to more than twice their threshold. -/
lemma overtaking_secondary_sum {a b A B r : ℝ}
    (hD : ContainedChart a |b|) (hS : ContainedChart A |B|)
    (hr : 0≤r ∧ r≤1/6) (hsum : 2.17+r/3<a+A) :
    1+Real.cos r+Real.sin r<
      (A*Real.cos r-B*Real.sin r-b)+(B+a*Real.cos r+b*Real.sin r) := by
  let T := a+A
  let U := |b|+|B|
  let delta := T-U-2
  have hTlo : 2.17<T := by dsimp [T]; linarith [hr.1]
  have hThi : T≤9/4 := by
    dsimp [T]
    linarith [hD.a_le_rho0,hS.a_le_rho0,rho0_bounds.2]
  have hdelta : (4/3)*r<delta := by
    have h1 := chart_three_radial_support hD
    have h2 := chart_three_radial_support hS
    dsimp [delta,T,U]
    linarith
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (by linarith [hr.2,Real.pi_gt_d2])
  have hs1 := Real.sin_le hr.1
  have hc1 := Real.cos_le_one r
  have hcp := mul_nonneg (sub_nonneg.mpr hThi) (sub_nonneg.mpr hc1)
  have hcLower := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := r))
    (by norm_num : (0:ℝ)≤5/4)
  have hsp := mul_nonneg (show 0≤T-2.17 by linarith) hs0
  have hdp := mul_pos (sub_pos.mpr hdelta) (show 0<1-Real.sin r by linarith [hr.2])
  have hrem := mul_nonneg hr.1 (sub_nonneg.mpr hs1)
  have hdiff : -U≤B-b := by
    dsimp [U]
    linarith [neg_le_abs B,le_abs_self b]
  have hdiffprod := mul_nonneg (sub_nonneg.mpr hdiff)
    (show 0≤1-Real.sin r by linarith [hr.2])
  have hpolynomial := mul_nonneg hr.1 (show 0≤1/2-2*r by linarith [hr.2])
  have he :
      T*Real.cos r-U*(1-Real.sin r)-(1+Real.cos r+Real.sin r)=
      (T-1)*(Real.cos r-1)+(T-3)*Real.sin r+delta*(1-Real.sin r) := by
    dsimp [delta]
    ring
  have hstrict : 0<T*Real.cos r-U*(1-Real.sin r)-(1+Real.cos r+Real.sin r) := by
    nlinarith only [hcp,hcLower,hsp,hdp,hrem,hpolynomial,he,hs1]
  dsimp [T] at hstrict
  nlinarith only [hstrict,hdiffprod]

/-- For S on its own axis and `s ≥ d`, D and S are separated along a secondary
axis. -/
lemma overtaking_own_secondary_choice {R : ℝ} (P : NormalizedPacking R)
    (hown : P.ownAxis 4=true) (horder : P.diagonalAngle≤P.deviation 4) :
    SouthSecondaryChoice P := by
  let r := P.deviation 4-P.diagonalAngle
  have hd : 1/2≤P.diagonalAngle := (normalized_diagonal_gt_half P).le
  have hs : P.deviation 4≤2/3 := P.deviation_windows.2.2.2.2.le
  have hr : 0≤r ∧ r≤1/6 := by dsimp [r]; constructor <;> linarith
  have hDphase : P.phase 3=Real.pi+P.diagonalAngle := by
    dsimp [NormalizedPacking.diagonalAngle]
    ring
  have hSphase : P.phase 4=3*Real.pi/2+P.deviation 4 := P.phase_from_deviation 4
  have hsum := coupled_own_radial_sum (P.contained 4) P.box.2.2 hd horder hs
    (by simpa only [hDphase] using P.own_separator 3 P.diagonal_own)
    (by simpa only [hSphase] using P.own_separator 4 hown)
  have hwork := overtaking_secondary_sum (r := r) (P.contained 3) (P.contained 4) hr hsum
  have hcos := Real.cos_nonneg_of_mem_Icc
    (show r∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hr.1,hr.2,Real.pi_gt_d2])
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hr.1
    (by linarith [hr.2,Real.pi_gt_d2])
  have hq : P.phase 4-P.phase 3=Real.pi/2+r := by
    rw [hDphase,hSphase]
    dsimp [r]
    ring
  have hthreshold : SAT.threshold (P.square 3) (P.square 4)=
      (1+Real.cos r+Real.sin r)/2 := by
    rw [P.square_def 3,P.square_def 4,oriented_pair_threshold,hq,angularWidth]
    simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_sub,add_zero,abs_neg,
      abs_of_nonneg hsin,abs_of_nonneg hcos]
    ring
  have hDwork : dot (normalY (P.square 3)) (sub (P.square 4).center (P.square 3).center)=
      P.radial 4*Real.cos r-P.transverse 4*Real.sin r-P.transverse 3 := by
    change frameY (P.square 3) (sub (P.square 4).center (P.square 3).center)=_
    rw [P.square_def 3,P.square_def 4,pair_frameY_left,hq]
    simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_sub,add_zero]
    ring
  have hSwork : dot (normalY (P.square 4)) (sub (P.square 4).center (P.square 3).center)=
      P.transverse 4+P.radial 3*Real.cos r+P.transverse 3*Real.sin r := by
    change frameY (P.square 4) (sub (P.square 4).center (P.square 3).center)=_
    rw [P.square_def 3,P.square_def 4,pair_frameY_right,hq]
    simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
      zero_mul,one_mul,zero_sub,add_zero]
    ring
  unfold SouthSecondaryChoice
  rw [hthreshold,hDwork,hSwork]
  by_cases h : (1+Real.cos r+Real.sin r)/2≤
      P.radial 4*Real.cos r-P.transverse 4*Real.sin r-P.transverse 3
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- In a normalized packing D and S are separated along a secondary axis. -/
theorem south_secondary_choice {R : ℝ} (P : NormalizedPacking R) : SouthSecondaryChoice P := by
  by_cases h : P.deviation 4≤P.diagonalAngle
  · exact south_secondary_choice_of_angle P h
  · have hown : P.ownAxis 4=true := by
      cases hbit : P.ownAxis 4
      · have hs := (abs_lt.mp (P.cardinal_angle 4 hbit)).2
        have hd := normalized_diagonal_gt_half P
        exfalso
        linarith
      · rfl
    exact overtaking_own_secondary_choice P hown (le_of_not_ge h)

end SquaresInCircles.Six
