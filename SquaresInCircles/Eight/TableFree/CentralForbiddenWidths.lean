module

public import SquaresInCircles.Eight.TableFree.CentralScalarArithmetic

/-!
# Continuous forbidden widths: no rectangle rows

Uncompiled draft of HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT, §§4–6.
The partitions are intrinsic branch changes of the exact geometric endpoint.
One monotone polynomial controls the unique middle-branch minimum. There is
no rational subdivision, list of test rectangles, or table of witnesses.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CentralForbidden

def lowerTransition : ℝ := 1-L
def middleWidth (d : ℝ) : ℝ := 2*Real.arctan (d/L)+E (1-d)
def lowerWidth (d : ℝ) : ℝ := 2*Real.arctan (d/L)+verticalAngle (1-d)

theorem middleWidth_hasDeriv {d : ℝ} (hd : lowerTransition≤d ∧ d≤c) :
    HasDerivAt middleWidth
      (2*L/(L^2+d^2)-1/Real.sqrt (radiusSq-(1-d)^2)) d := by
  have he := E_hasDeriv (y := 1-d) (by
    have hpos : 0≤1-d := by dsimp [c] at hd; linarith
    rw [abs_of_nonneg hpos]
    have hL : 1-d≤L := by dsimp [lowerTransition] at hd; linarith
    exact hL.trans_lt r_bounds.1)
  convert (atan_side_hasDeriv d).add
    (he.comp d ((hasDerivAt_const d 1).sub (hasDerivAt_id d))) using 1
  · rfl
  · ring

theorem middle_derivative_nonpositive {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤c) (hP : 0≤widthPolynomial d) :
    2*L/(L^2+d^2)-1/Real.sqrt (radiusSq-(1-d)^2)≤0 := by
  have hd0 : 0≤d := by norm_num [lowerTransition,L] at hd; linarith
  have hother : 0≤1-d ∧ 1-d≤L := by dsimp [lowerTransition,L,c] at hd ⊢; constructor <;> linarith
  have hrad : 0<radiusSq-(1-d)^2 := by
    linarith [pow_le_pow_left₀ hother.1 hother.2 2,r_sq,r_sq_radiusSq,pow_pos c_pos 2]
  let M := Real.sqrt (radiusSq-(1-d)^2)
  have hM : 0<M := Real.sqrt_pos.mpr hrad
  have hM₂ : M^2=radiusSq-(1-d)^2 := Real.sq_sqrt hrad.le
  have hden : 0<L^2+d^2 := add_pos_of_pos_of_nonneg (pow_pos L_pos 2) (sq_nonneg d)
  have hid : (L^2+d^2)^2-(2*L*M)^2=widthPolynomial d := by
    unfold widthPolynomial
    linear_combination (-4*L^2)*hM₂+4*L^2*r_sq_radiusSq-4*L^2*r_sq
  have hcomparison : 2*L*M≤L^2+d^2 :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq (by linarith) hden.le)
  apply sub_nonpos.mpr
  apply (div_le_div_iff₀ hden hM).mpr
  simpa [M] using hcomparison

theorem middle_derivative_nonnegative {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤c) (hP : widthPolynomial d≤0) :
    0≤2*L/(L^2+d^2)-1/Real.sqrt (radiusSq-(1-d)^2) := by
  have hother : 0≤1-d ∧ 1-d≤L := by dsimp [lowerTransition,L,c] at hd ⊢; constructor <;> linarith
  have hrad : 0<radiusSq-(1-d)^2 := by
    linarith [pow_le_pow_left₀ hother.1 hother.2 2,r_sq,r_sq_radiusSq,pow_pos c_pos 2]
  let M := Real.sqrt (radiusSq-(1-d)^2)
  have hM : 0<M := Real.sqrt_pos.mpr hrad
  have hM₂ : M^2=radiusSq-(1-d)^2 := Real.sq_sqrt hrad.le
  have hden : 0<L^2+d^2 := add_pos_of_pos_of_nonneg (pow_pos L_pos 2) (sq_nonneg d)
  have hid : (L^2+d^2)^2-(2*L*M)^2=widthPolynomial d := by
    unfold widthPolynomial
    linear_combination (-4*L^2)*hM₂+4*L^2*r_sq_radiusSq-4*L^2*r_sq
  have hcomparison : L^2+d^2≤2*L*M :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq (by linarith) (mul_pos (mul_pos two_pos L_pos) hM).le)
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ hM hden).mpr
  simpa [M] using hcomparison

/-- The single sign-changing polynomial traps the minimum, not a mesh. -/
theorem middleWidth_lower {d : ℝ} (hd : lowerTransition≤d ∧ d≤c) :
    347/200<middleWidth d := by
  obtain ⟨a,ha_def⟩ : ∃ a : ℝ, a=1379/10000 := ⟨_,rfl⟩
  obtain ⟨b,hb_def⟩ : ∃ b : ℝ, b=69/500 := ⟨_,rfl⟩
  have ha : lowerTransition≤a ∧ a≤c := by rw [ha_def]; norm_num [lowerTransition,L,c]
  have hb : lowerTransition≤b ∧ b≤c := by rw [hb_def]; norm_num [lowerTransition,L,c]
  have hab : a≤b := by rw [ha_def,hb_def]; norm_num
  have hlt0 : 0<lowerTransition := by norm_num [lowerTransition,L]
  have hleft : AntitoneOn middleWidth (Icc lowerTransition a) := by
    apply antiOn_of_hasDeriv_nonpos (by unfold middleWidth E; fun_prop)
      (fun x hx => middleWidth_hasDeriv ⟨hx.1.le,hx.2.le.trans ha.2⟩)
    intro x hx
    apply middle_derivative_nonpositive ⟨hx.1.le,hx.2.le.trans ha.2⟩
    have hP := widthPolynomial_antitone
      ⟨by linarith [hx.1],hx.2.le.trans ha.2⟩
      ⟨by linarith [ha.1],ha.2⟩ hx.2.le
    rw [ha_def] at hP
    exact widthPolynomial_signs.1.le.trans hP
  have hright : MonotoneOn middleWidth (Icc b c) := by
    apply monoOn_of_hasDeriv_nonneg (by unfold middleWidth E; fun_prop)
      (fun x hx => middleWidth_hasDeriv ⟨hb.1.trans hx.1.le,hx.2.le⟩)
    intro x hx
    apply middle_derivative_nonnegative ⟨hb.1.trans hx.1.le,hx.2.le⟩
    have hP := widthPolynomial_antitone ⟨by linarith [hb.1],hb.2⟩
      ⟨by linarith [hx.1,hb.1],hx.2.le⟩ hx.1.le
    rw [hb_def] at hP
    exact hP.trans widthPolynomial_signs.2.le
  have hbase : 347/200<2*Real.arctan (a/L)+E (1-b) := by
    have h₁ := atan_endpoint_bounds.1
    have h₂ := E_endpoint_bounds.1
    have hid : (1:ℝ)-b=431/500 := by rw [hb_def]; norm_num
    rw [hid,ha_def]
    linarith
  have hwindow (x : ℝ) (hx : a≤x ∧ x≤b) :
      2*Real.arctan (a/L)+E (1-b)≤middleWidth x := by
    have h₁ := Real.arctan_mono (div_le_div_of_nonneg_right hx.1 L_pos.le)
    have h₂ := E_mono (show 1-b≤1-x by linarith)
    dsimp [middleWidth]
    linarith
  by_cases hda : d≤a
  · exact hbase.trans_le ((hwindow a ⟨le_rfl,hab⟩).trans
      (hleft ⟨hd.1,hda⟩ ⟨ha.1,le_rfl⟩ hda))
  by_cases hbd : b≤d
  · exact hbase.trans_le ((hwindow b ⟨hab,le_rfl⟩).trans
      (hright ⟨le_rfl,hb.2⟩ ⟨hbd,hd.2⟩ hbd))
  · exact hbase.trans_le (hwindow d ⟨(lt_of_not_ge hda).le,(lt_of_not_ge hbd).le⟩)

theorem lowerWidth_hasDeriv {d : ℝ}
    (hd : 1-r<d ∧ d<lowerTransition) :
    HasDerivAt lowerWidth
      (2*L/(L^2+d^2)-L/((1-d)*Real.sqrt ((1-d)^2-L^2))) d := by
  have hy : L<1-d := by dsimp [lowerTransition] at hd; linarith
  convert (atan_side_hasDeriv d).add
    ((vertical_hasDeriv hy).comp d
      ((hasDerivAt_const d 1).sub (hasDerivAt_id d))) using 1
  · rfl
  · ring

theorem lowerWidth_antitone : AntitoneOn lowerWidth (Icc (1-r) lowerTransition) := by
  apply antiOn_of_hasDeriv_nonpos
    (by
      unfold lowerWidth verticalAngle
      apply ContinuousOn.add
      · fun_prop
      · apply continuous_const.continuousOn.add
        apply Real.continuous_arccos.comp_continuousOn
        apply continuous_const.continuousOn.div
          (by fun_prop)
        intro d hd
        have hpos : L≤1-d := by have h := hd.2; dsimp [lowerTransition] at h; linarith
        exact ne_of_gt (L_pos.trans_le hpos))
    (fun d hd => lowerWidth_hasDeriv hd)
  intro d hd
  have hyL : L<1-d := by have h := hd.2; dsimp [lowerTransition] at h; linarith
  have hyr : 1-d<r := by linarith [hd.1]
  have hy0 := L_pos.trans hyL
  have hrad : 0<(1-d)^2-L^2 := by nlinarith [L_pos]
  have hm := Real.sqrt_pos.mpr hrad
  have hmc : Real.sqrt ((1-d)^2-L^2)≤c := by
    have hsq := pow_le_pow_left₀ hy0.le hyr.le 2
    calc Real.sqrt ((1-d)^2-L^2)≤Real.sqrt (c^2) :=
          Real.sqrt_le_sqrt (by linarith [r_sq])
      _=c := Real.sqrt_sq c_pos.le
  have hprod : (1-d)*Real.sqrt ((1-d)^2-L^2)≤r*c := by
    exact mul_le_mul hyr.le hmc hm.le r_pos.le
  have hsecond : L/(r*c)≤L/((1-d)*Real.sqrt ((1-d)^2-L^2)) :=
    div_le_div_of_nonneg_left L_pos.le (mul_pos hy0 hm) hprod
  have hfirst : 2*L/(L^2+d^2)≤2/L := by
    apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos L_pos 2) (sq_nonneg d)) L_pos).mpr
    nlinarith [sq_nonneg d]
  linarith [steep_vertical_reserve]

theorem first_width_lower {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    347/200<F L d+F L (1-d) := by
  have hLr := r_bounds.1
  by_cases hsmall : d≤lowerTransition
  · have hdcore : d≤k L := by rw [k_L]; dsimp [lowerTransition,L,c] at hsmall ⊢; linarith
    rw [F_eq_side hdcore,sideAngle_L d hd.1]
    by_cases hfar : r≤1-d
    · rw [F_eq_constant le_rfl hLr hfar]
      have hatan : 0≤Real.arctan (d/L) := Real.arctan_nonneg.mpr (div_nonneg hd.1 L_pos.le)
      linarith [Real.pi_gt_d2,φ_bounds.1]
    · have hyL : L≤1-d := by dsimp [lowerTransition] at hsmall; linarith
      rw [F_eq_vertical le_rfl hLr hyL (le_of_not_ge hfar)]
      have hmono := lowerWidth_antitone
        ⟨by linarith,hsmall⟩ ⟨by linarith [r_bounds.1],le_rfl⟩ hsmall
      have hend : lowerWidth lowerTransition=2*Real.arctan (1/11)+Real.pi/2 := by
        have hrat : lowerTransition/L=(1/11:ℝ) := by norm_num [lowerTransition,L]
        have hid : 1-lowerTransition=L := by unfold lowerTransition; ring
        rw [lowerWidth,hrat,hid,verticalAngle_L]
      rw [hend] at hmono
      change 347/200<lowerWidth d
      linarith [atan_endpoint_bounds.2,Real.pi_gt_d2]
  by_cases hmiddle : d≤c
  · have hdcore : d≤k L := by simpa using hmiddle
    have hyk : k L≤1-d := by rw [k_L]; dsimp [c] at hmiddle ⊢; linarith
    have hyL : 1-d≤L := by dsimp [lowerTransition] at hsmall; linarith
    rw [F_eq_side hdcore,sideAngle_L d hd.1,F_eq_E le_rfl hLr hyk hyL]
    exact middleWidth_lower ⟨(le_of_not_ge hsmall),hmiddle⟩
  · have hdk : k L≤d := by rw [k_L]; exact le_of_not_ge hmiddle
    have hdL : d≤L := by dsimp [L]; linarith
    have hotherk : k L≤1-d := by rw [k_L]; dsimp [c]; linarith
    have hotherL : 1-d≤L := by dsimp [c,L] at hmiddle ⊢; linarith
    rw [F_eq_E le_rfl hLr hdk hdL,F_eq_E le_rfl hLr hotherk hotherL]
    have hc := E_symmetric_minimum ⟨hd.1,by linarith⟩ hdL hotherL
    linarith [E_endpoint_bounds.2.1]

abbrev strongerA : ℝ := 19/20

theorem stronger_k_bounds :
    L<strongerA ∧ strongerA<r ∧ lowerTransition<k strongerA ∧ k strongerA<1/4 := by
  have hAr : strongerA<r := by
    have hr := r_sq_radiusSq
    have hp := r_pos
    dsimp [strongerA,radiusSq] at *
    nlinarith
  have hA : L<strongerA := by norm_num [L,strongerA]
  have hk := k_spec hA.le hAr
  refine ⟨hA,hAr,?_,?_⟩ <;>
    dsimp [lowerTransition,L,strongerA,radiusSq] at * <;> nlinarith

/-- A derivative bound on the entire short-side branch. -/
theorem stronger_side_derivative {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤k strongerA) :
    (5/4:ℝ)<(strongerA+L*d/Real.sqrt (strongerA^2+d^2-L^2))/(strongerA^2+d^2) := by
  have hl : (1/12:ℝ)≤d := by have h := hd.1; norm_num [lowerTransition,L] at h; linarith
  have hd0 : 0<d := by linarith
  have hrad : 0<strongerA^2+d^2-L^2 := by
    norm_num [strongerA,L]
    nlinarith [sq_nonneg d]
  have hM : 0<Real.sqrt (strongerA^2+d^2-L^2) := Real.sqrt_pos.mpr hrad
  have hM₂ : Real.sqrt (strongerA^2+d^2-L^2)^2=strongerA^2+d^2-L^2 := Real.sq_sqrt hrad.le
  have hk := k_spec stronger_k_bounds.1.le stronger_k_bounds.2.1
  have hden : 0<strongerA^2+d^2 := by positivity
  have hdenU : strongerA^2+d^2≤radiusSq := by
    have := pow_le_pow_left₀ hd0.le hd.2 2
    linarith [hk.2.1]
  generalize Real.sqrt (strongerA^2+d^2-L^2)=M at hM hM₂ ⊢
  have hratio : (5/16:ℝ)<d/M := by
    apply (lt_div_iff₀ hM).mpr
    have hd2 : (1/12:ℝ)^2≤d^2 := pow_le_pow_left₀ (by norm_num) hl 2
    have hsq : (5/16*M)^2<d^2 := by
      norm_num [strongerA,L] at hM₂
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hd0.le hsq
  apply (lt_div_iff₀ hden).mpr
  have hmul : L*(5/16)<L*d/M := by
    rw [mul_div_assoc]
    exact mul_lt_mul_of_pos_left hratio L_pos
  have hreserve : (5/4:ℝ)*radiusSq<19/20+5*L/16 := by norm_num [radiusSq,L]
  simp only [strongerA] at hdenU ⊢
  linarith

theorem stronger_side_tangent {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤k strongerA) :
    sideAngle strongerA lowerTransition+(5/4)*(d-lowerTransition)≤sideAngle strongerA d := by
  let g : ℝ → ℝ := fun x => sideAngle strongerA x-(5/4)*x
  have hgd (x : ℝ) : HasDerivAt g
      ((strongerA+L*x/Real.sqrt (strongerA^2+x^2-L^2))/(strongerA^2+x^2)-5/4) x := by
    have h1 := sideAngle_hasDeriv (y := x) stronger_k_bounds.1
    have h2 : HasDerivAt (fun x : ℝ => (5/4:ℝ)*x) (5/4) x := by
      convert (hasDerivAt_id' x).const_mul (5/4:ℝ) using 1
      ring
    exact h1.sub h2
  have hm : MonotoneOn g (Icc lowerTransition (k strongerA)) :=
    monoOn_of_hasDeriv_nonneg (fun x _ => (hgd x).continuousAt.continuousWithinAt)
      (fun x _ => hgd x)
      (fun x hx => sub_nonneg.mpr (stronger_side_derivative ⟨hx.1.le,hx.2.le⟩).le)
  have hh := hm ⟨le_rfl,stronger_k_bounds.2.2.1.le⟩ hd hd.1
  dsimp only [g] at hh
  linarith

def strongerComparison (d : ℝ) : ℝ :=
  9/25+(5/4)*(d-lowerTransition)+E (1-d)

theorem strongerComparison_antitone :
    AntitoneOn strongerComparison (Icc lowerTransition (1/4)) := by
  apply antiOn_of_hasDeriv_nonpos (by unfold strongerComparison E; fun_prop)
    (d := fun d => 5/4-1/Real.sqrt (radiusSq-(1-d)^2))
  · intro d hd
    have hh := E_hasDeriv (y := 1-d) (by
      rw [abs_of_nonneg (by linarith [hd.2] : 0≤1-d)]
      have hL : 1-d≤L := by have h := hd.1; dsimp [lowerTransition] at h; linarith
      exact hL.trans_lt r_bounds.1)
    convert (((hasDerivAt_id d).sub_const lowerTransition).const_mul (5/4)).const_add (9/25)
      |>.add (hh.comp d ((hasDerivAt_const d 1).sub (hasDerivAt_id d))) using 1
    · rfl
    · ring
  · intro d hd
    have hroot : Real.sqrt (radiusSq-(1-d)^2)<4/5 := by
      apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<4/5)).mpr
      have h := hd.2
      dsimp [radiusSq]
      nlinarith
    have hrad : 0<radiusSq-(1-d)^2 := by
      have hyL : 1-d≤L := by have h := hd.1; dsimp [lowerTransition] at h; linarith
      have hy0 : 0≤1-d := by linarith [hd.2]
      nlinarith [r_bounds.1,r_sq_radiusSq,r_pos]
    have hroot0 := Real.sqrt_pos.mpr hrad
    have hrec : (5/4:ℝ)<1/Real.sqrt (radiusSq-(1-d)^2) := by
      apply (lt_div_iff₀ hroot0).mpr
      nlinarith
    linarith

theorem stronger_width_lower {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    899/500<F strongerA d+F strongerA (1-d) := by
  have hA := stronger_k_bounds.1.le
  have hAr := stronger_k_bounds.2.1
  by_cases hsmall : d≤lowerTransition
  · have hfirst := F_ge_initial_side hA hAr hd.1
    have hsecond := F_ge_half_pi hA hAr (show L≤1-d by dsimp [lowerTransition] at hsmall; linarith)
    have hside : (1/4:ℝ)<sideAngle strongerA 0 := stronger_side_endpoint.1
    linarith [Real.pi_gt_d2]
  by_cases hmiddle : d≤k strongerA
  · have hdk : lowerTransition≤d := le_of_not_ge hsmall
    have hotherk : k strongerA≤1-d := by linarith [stronger_k_bounds.2.2.2]
    have hotherL : 1-d≤L := by dsimp [lowerTransition] at hdk; linarith
    rw [F_eq_side hmiddle,F_eq_E hA hAr hotherk hotherL]
    have hside := stronger_side_tangent ⟨hdk,hmiddle⟩
    have hstart : 9/25<sideAngle strongerA lowerTransition := by
      have hlt : lowerTransition=1/12 := by norm_num [lowerTransition,L]
      rw [hlt]
      exact stronger_side_endpoint.2
    have hcomp := strongerComparison_antitone
      ⟨hdk,hmiddle.trans stronger_k_bounds.2.2.2.le⟩
      ⟨by norm_num [lowerTransition,L],le_rfl⟩
      (hmiddle.trans stronger_k_bounds.2.2.2.le)
    have hend : 899/500<strongerComparison (1/4) := by
      dsimp [strongerComparison,lowerTransition,L]
      norm_num
      linarith [E_endpoint_bounds.2.2]
    have hcd : strongerComparison d=9/25+(5/4)*(d-lowerTransition)+E (1-d) := rfl
    linarith
  · have hdk : k strongerA≤d := le_of_not_ge hmiddle
    have hdL : d≤L := by dsimp [L]; linarith
    have hotherk : k strongerA≤1-d := by linarith [stronger_k_bounds.2.2.2]
    have hotherL : 1-d≤L := by
      have hdk' := stronger_k_bounds.2.2.1.trans_le hdk
      dsimp [lowerTransition] at hdk'
      linarith
    rw [F_eq_E hA hAr hdk hdL,F_eq_E hA hAr hotherk hotherL]
    have hm := E_symmetric_minimum ⟨hd.1,by linarith⟩ hdL hotherL
    linarith [E_endpoint_bounds.2.1]

/-- The entire interval is forbidden, including all weak rectangle endpoints. -/
theorem bandA_forbidden {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    ∃ l u : ℝ, l≤0 ∧ 0≤u ∧ (347/200)<u-l ∧ u-l≤4 ∧
      ∀ β, l≤β ∧ β≤u → ∃ v, |v|≤c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0≤p.1 ∧ p.1≤(11/12) ∧ -d≤p.2 ∧ p.2≤1-d := by
  exact centered_rectangle_forbidden le_rfl r_bounds.1 hd (first_width_lower hd)

theorem bandB_forbidden {d : ℝ} (hd : 0≤d ∧ d≤1/2) :
    ∃ l u : ℝ, l≤0 ∧ 0≤u ∧ (899/500)<u-l ∧ u-l≤4 ∧
      ∀ β, l≤β ∧ β≤u → ∃ v, |v|≤c ∧
        let p := pointInDirection (0,0) (β : Direction) L v
        0≤p.1 ∧ p.1≤(19/20) ∧ -d≤p.2 ∧ p.2≤1-d := by
  exact centered_rectangle_forbidden stronger_k_bounds.1.le stronger_k_bounds.2.1 hd
    (stronger_width_lower hd)

end SquaresInCircles.Eight.CentralForbidden