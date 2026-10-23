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
    nlinarith [r_sq_radiusSq,r_pos,r_bounds.1]
  let M := Real.sqrt (radiusSq-(1-d)^2)
  have hM : 0<M := Real.sqrt_pos.mpr hrad
  have hM₂ : M^2=radiusSq-(1-d)^2 := Real.sq_sqrt hrad.le
  have hden : 0<L^2+d^2 := by nlinarith [L_pos,sq_nonneg d]
  have hid : (L^2+d^2)^2-(2*L*M)^2=widthPolynomial d := by
    dsimp [widthPolynomial]
    have hr := r_sq
    have hr' := r_sq_radiusSq
    nlinarith [hM₂]
  have hcomparison : 2*L*M≤L^2+d^2 := by
    nlinarith [mul_pos L_pos hM,sq_nonneg (L^2+d^2+2*L*M)]
  apply sub_nonpos.mpr
  apply (div_le_div_iff₀ hden hM).mpr
  simpa [M] using hcomparison

theorem middle_derivative_nonnegative {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤c) (hP : widthPolynomial d≤0) :
    0≤2*L/(L^2+d^2)-1/Real.sqrt (radiusSq-(1-d)^2) := by
  have hother : 0≤1-d ∧ 1-d≤L := by dsimp [lowerTransition,L,c] at hd ⊢; constructor <;> linarith
  have hrad : 0<radiusSq-(1-d)^2 := by
    nlinarith [r_sq_radiusSq,r_pos,r_bounds.1]
  let M := Real.sqrt (radiusSq-(1-d)^2)
  have hM : 0<M := Real.sqrt_pos.mpr hrad
  have hM₂ : M^2=radiusSq-(1-d)^2 := Real.sq_sqrt hrad.le
  have hden : 0<L^2+d^2 := by nlinarith [L_pos,sq_nonneg d]
  have hid : (L^2+d^2)^2-(2*L*M)^2=widthPolynomial d := by
    dsimp [widthPolynomial]
    nlinarith [r_sq,r_sq_radiusSq,hM₂]
  have hcomparison : L^2+d^2≤2*L*M := by
    nlinarith [mul_pos L_pos hM,sq_nonneg (L^2+d^2+2*L*M)]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ hM hden).mpr
  simpa [M] using hcomparison

/-- The single sign-changing polynomial traps the minimum, not a mesh. -/
theorem middleWidth_lower {d : ℝ} (hd : lowerTransition≤d ∧ d≤c) :
    347/200<middleWidth d := by
  let a : ℝ := 1379/10000
  let b : ℝ := 69/500
  have ha : lowerTransition≤a ∧ a≤c := by norm_num [a,lowerTransition,L,c]
  have hb : lowerTransition≤b ∧ b≤c := by norm_num [b,lowerTransition,L,c]
  have hab : a≤b := by norm_num [a,b]
  have hleft : AntitoneOn middleWidth (Icc lowerTransition a) := by
    apply antiOn_of_hasDeriv_nonpos (by unfold middleWidth E; fun_prop)
      (fun x hx => middleWidth_hasDeriv ⟨hx.1.le,hx.2.le.trans ha.2⟩)
    intro x hx
    apply middle_derivative_nonpositive ⟨hx.1.le,hx.2.le.trans ha.2⟩
    have hP := widthPolynomial_antitone
      ⟨by dsimp [lowerTransition,L] at hx; linarith,hx.2.le.trans ha.2⟩
      ⟨by norm_num [a],ha.2⟩ hx.2.le
    exact widthPolynomial_signs.1.le.trans hP
  have hright : MonotoneOn middleWidth (Icc b c) := by
    apply monoOn_of_hasDeriv_nonneg (by unfold middleWidth E; fun_prop)
      (fun x hx => middleWidth_hasDeriv ⟨hb.1.trans hx.1.le,hx.2.le⟩)
    intro x hx
    apply middle_derivative_nonnegative ⟨hb.1.trans hx.1.le,hx.2.le⟩
    have hP := widthPolynomial_antitone ⟨by norm_num [b],hb.2⟩
      ⟨by dsimp [b] at hx; linarith,hx.2.le⟩ hx.1.le
    exact hP.trans widthPolynomial_signs.2.le
  have hbase : 347/200<2*Real.arctan (a/L)+E (1-b) := by
    have h₁ := atan_endpoint_bounds.1
    have h₂ := E_endpoint_bounds.1
    have hid : (1:ℝ)-b=431/500 := by norm_num [b]
    rw [hid]
    dsimp [a]
    linarith
  have hwindow (x : ℝ) (hx : a≤x ∧ x≤b) :
      2*Real.arctan (a/L)+E (1-b)≤middleWidth x := by
    have h₁ := Real.strictMono_arctan.monotone
      (div_le_div_of_nonneg_right hx.1 L_pos.le)
    have h₂ := E_mono (show 1-b≤1-x by linarith)
    dsimp [middleWidth]
    linarith
  by_cases hda : d≤a
  · exact hbase.trans_le ((hwindow a ⟨le_rfl,hab⟩).trans
      (hleft hd hda))
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
        have hpos : L≤1-d := by dsimp [lowerTransition] at hd; linarith
        exact ne_of_gt (L_pos.trans_le hpos))
    (fun d hd => lowerWidth_hasDeriv hd)
  intro d hd
  have hyL : L<1-d := by dsimp [lowerTransition] at hd; linarith
  have hyr : 1-d<r := by linarith
  have hy0 := L_pos.trans hyL
  have hrad : 0<(1-d)^2-L^2 := by nlinarith [L_pos]
  have hm := Real.sqrt_pos.mpr hrad
  have hm2 := Real.sq_sqrt hrad.le
  have hmc : Real.sqrt ((1-d)^2-L^2)≤c := by
    nlinarith [r_sq,c_pos]
  have hprod : (1-d)*Real.sqrt ((1-d)^2-L^2)≤r*c := by
    exact mul_le_mul hyr.le hmc hm.le r_pos.le
  have hsecond : L/(r*c)≤L/((1-d)*Real.sqrt ((1-d)^2-L^2)) :=
    div_le_div_of_nonneg_left L_pos.le (mul_pos hy0 hm) hprod
  have hfirst : 2*L/(L^2+d^2)≤2/L := by
    apply (div_le_div_iff₀ (by nlinarith [L_pos,sq_nonneg d] : 0<L^2+d^2) L_pos).mpr
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
  have hd0 : 0<d := by norm_num [lowerTransition,L] at hd; linarith
  have hrad : 0<strongerA^2+d^2-L^2 := by
    dsimp [strongerA,L]
    nlinarith [sq_nonneg d]
  let M := Real.sqrt (strongerA^2+d^2-L^2)
  have hM : 0<M := Real.sqrt_pos.mpr hrad
  have hM₂ : M^2=strongerA^2+d^2-L^2 := Real.sq_sqrt hrad.le
  have hratio : (5/16:ℝ)<d/M := by
    apply (lt_div_iff₀ hM).mpr
    have hd2 : (1/12:ℝ)^2≤d^2 := by
      have hl : (1/12:ℝ)≤d := by simpa [lowerTransition,L] using hd.1
      exact pow_le_pow_left₀ (by norm_num) hl 2
    dsimp [strongerA,L] at hM₂
    nlinarith [sq_nonneg (d+5/16*M)]
  have hk := k_spec stronger_k_bounds.1.le stronger_k_bounds.2.1
  have hden : 0<strongerA^2+d^2 := by dsimp [strongerA]; nlinarith [sq_nonneg d]
  have hdenU : strongerA^2+d^2≤radiusSq := by nlinarith [hk.2.1,hk.1]
  apply (lt_div_iff₀ hden).mpr
  have hmul := mul_lt_mul_of_pos_left hratio L_pos
  have hreserve : (5/4:ℝ)*radiusSq<strongerA+5*L/16 := by norm_num [radiusSq,strongerA,L]
  dsimp [M] at hmul
  nlinarith

theorem stronger_side_tangent {d : ℝ}
    (hd : lowerTransition≤d ∧ d≤k strongerA) :
    sideAngle strongerA lowerTransition+(5/4)*(d-lowerTransition)≤sideAngle strongerA d := by
  let g : ℝ → ℝ := fun x => sideAngle strongerA x-(5/4)*x
  have hm : MonotoneOn g (Icc lowerTransition (k strongerA)) := by
    apply monoOn_of_hasDeriv_nonneg (by unfold g sideAngle; fun_prop)
      (d := fun x => (strongerA+L*x/Real.sqrt (strongerA^2+x^2-L^2))/(strongerA^2+x^2)-5/4)
    · intro x hx
      exact (sideAngle_hasDeriv stronger_k_bounds.1).sub ((hasDerivAt_id x).const_mul (5/4))
    · intro x hx
      exact sub_nonneg.mpr (stronger_side_derivative ⟨hx.1.le,hx.2.le⟩).le
  have hh := hm ⟨le_rfl,stronger_k_bounds.2.2.1.le⟩ hd hd.1
  dsimp [g] at hh
  linarith

def strongerComparison (d : ℝ) : ℝ :=
  9/25+(5/4)*(d-lowerTransition)+E (1-d)

theorem strongerComparison_antitone :
    AntitoneOn strongerComparison (Icc lowerTransition (1/4)) := by
  apply antiOn_of_hasDeriv_nonpos (by unfold strongerComparison E; fun_prop)
    (d := fun d => 5/4-1/Real.sqrt (radiusSq-(1-d)^2))
  · intro d hd
    have hh := E_hasDeriv (y := 1-d) (by
      rw [abs_of_nonneg (by linarith : 0≤1-d)]
      have hL : 1-d≤L := by dsimp [lowerTransition] at hd; linarith
      exact hL.trans_lt r_bounds.1)
    convert (((hasDerivAt_id d).sub_const lowerTransition).const_mul (5/4)).const_add (9/25)
      |>.add (hh.comp d ((hasDerivAt_const d 1).sub (hasDerivAt_id d))) using 1
    · rfl
    · ring
  · intro d hd
    have hroot : Real.sqrt (radiusSq-(1-d)^2)<4/5 := by
      apply (Real.sqrt_lt (by norm_num : (0:ℝ)≤4/5)).mpr
      dsimp [radiusSq]
      nlinarith
    have hrad : 0<radiusSq-(1-d)^2 := by
      have hyL : 1-d≤L := by dsimp [lowerTransition] at hd; linarith
      have hy0 : 0≤1-d := by linarith
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
    linarith [stronger_side_endpoint.1,Real.pi_gt_d2]
  by_cases hmiddle : d≤k strongerA
  · have hdk : lowerTransition≤d := le_of_not_ge hsmall
    have hotherk : k strongerA≤1-d := by linarith [stronger_k_bounds.2.2.2]
    have hotherL : 1-d≤L := by dsimp [lowerTransition] at hdk; linarith
    rw [F_eq_side hmiddle,F_eq_E hA hAr hotherk hotherL]
    have hside := stronger_side_tangent ⟨hdk,hmiddle⟩
    have hstart : 9/25<sideAngle strongerA lowerTransition := by
      simpa [lowerTransition,L] using stronger_side_endpoint.2
    have hcomp := strongerComparison_antitone
      ⟨hdk,hmiddle.trans stronger_k_bounds.2.2.2.le⟩
      ⟨by norm_num [lowerTransition,L],le_rfl⟩
      (hmiddle.trans stronger_k_bounds.2.2.2.le)
    have hend : 899/500<strongerComparison (1/4) := by
      dsimp [strongerComparison,lowerTransition,L]
      norm_num
      linarith [E_endpoint_bounds.2.2]
    dsimp [strongerComparison] at hcomp
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