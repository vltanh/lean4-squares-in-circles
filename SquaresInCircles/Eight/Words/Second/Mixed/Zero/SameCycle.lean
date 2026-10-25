module

public import SquaresInCircles.Eight.Words.Second.Outer.JBounds
public import SquaresInCircles.Eight.Words.Second.Outer.VBounds
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositiveCore
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroSameOwners
public import SquaresInCircles.Eight.Words.Wrong.ZeroOriginalOwners

/-!
# Eight squares: every original same-sign mixed zero edge of the second wrong word

The independent cyclic owner theorem fixes
the source-secondary owner for positive signs and the target-secondary
owner for negative signs.  The latter is an exact reflected expression
of one of the two positive radial orders.  All original axes are tested
before this reduction, including axes tied at a weak physical contact.
-/

section
/-!
## The exact mixed zero-quarter labels of the second wrong word

The bounds in this module hold on the whole physical outer arc (`target_affine_upper`,
`source_affine_lower`). The two core pieces share the same affine labels (`same_core_literal`,
`same_outer_literal`), and no core point is moved.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

abbrev SameRow := Fin 2

def coreC : SameRow → ℝ := ![125/100000,4970/100000]
def coreG : SameRow → ℝ := ![103981/100000,94831/100000]
def targetLabel : SameRow → RoleLabel := ![JLabel,KLabel]
def outerC : SameRow → ℝ := ![19555/100000,16823/100000]
def outerG : SameRow → ℝ := ![63132/100000,62312/100000]
def sourceLabel : SameRow → RoleLabel := ![PLabel,LLabel]
def sourceSlope : SameRow → ℝ := ![7/10,311/500]

lemma core_coefficients (r : SameRow) :
    (94831/100000:ℝ)≤coreG r ∧ coreG r≤103981/100000 := by
  fin_cases r <;> norm_num [coreG]

lemma outer_coefficients (r : SameRow) :
    0≤outerG r ∧ outerG r<(191/250:ℝ) ∧
      0≤ sourceSlope r ∧ sourceSlope r≤1 := by
  fin_cases r <;> norm_num [outerG,sourceSlope]

lemma target_slope_upper (r : SameRow) {B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) : (targetLabel r).d1 B<(11/10:ℝ) := by
  fin_cases r
  · simpa [targetLabel] using (J_first_bounds hB).2.trans (by norm_num : (541/500:ℝ)<11/10)
  · simpa [targetLabel] using (K_first_bounds hB).2.trans (by norm_num : (116/125:ℝ)<11/10)

lemma target_zero_negative (r : SameRow) : (targetLabel r).outer 0<0 := by
  fin_cases r
  · change J 0<0
    rw [J_zero]
    nlinarith [outer_endpoint_bounds.1]
  · change K 0<0
    linarith [K_zero_bounds.2]

lemma target_affine_upper (r : SameRow) {B : ℝ}
    (hB : B∈Icc 0 outerDiagonal) : (targetLabel r).outer B≤(11/10)*B := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun t => (11/10)*t-(targetLabel r).outer t) (11/10-(targetLabel r).d1 t) t := by
    have h := ((hasDerivAt_id' t).const_mul (11/10:ℝ)).sub
      ((targetLabel r).outer_hasDerivAt (outer_domain ht))
    exact h.congr_deriv (by ring)
  have hm : MonotoneOn (fun t => (11/10)*t-(targetLabel r).outer t) (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by linarith [target_slope_upper r (Ioo_subset_Icc_self ht)])
  have hh := hm outer_zero_mem hB hB.1
  simp only at hh
  linarith [target_zero_negative r]

lemma source_slope_lower (r : SameRow) {b : ℝ}
    (hb : b∈Icc 0 outerDiagonal) : sourceSlope r<(sourceLabel r).d1 b := by
  fin_cases r
  · norm_num [sourceSlope,sourceLabel]
    linarith [(P_first_bounds hb).1]
  · simpa [sourceSlope,sourceLabel] using L_first_lower hb

lemma source_affine_lower (r : SameRow) {b : ℝ}
    (hb : b∈Icc 0 outerDiagonal) :
    (sourceLabel r).outer 0+sourceSlope r*b≤(sourceLabel r).outer b := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun t => (sourceLabel r).outer t-sourceSlope r*t)
        ((sourceLabel r).d1 t-sourceSlope r) t := by
    have h := ((sourceLabel r).outer_hasDerivAt (outer_domain ht)).sub
      ((hasDerivAt_id' t).const_mul (sourceSlope r))
    exact h.congr_deriv (by ring)
  have hm : MonotoneOn (fun t => (sourceLabel r).outer t-sourceSlope r*t)
      (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by linarith [source_slope_lower r (Ioo_subset_Icc_self ht)])
  have hh := hm outer_zero_mem hb hb.1
  simp only [mul_zero,sub_zero] at hh
  linarith

lemma source_zero (r : SameRow) :
    (sourceLabel r).outer 0=![2478/100000,3965/100000] r := by
  fin_cases r <;> norm_num [sourceLabel,RoleLabel.outer,RoleLabel.eval,PLabel,LLabel]

lemma same_core_literal (r : SameRow) (kind : RadialKind) (hk : kind≠.outer)
    {a b A B x : ℝ} (ht : OuterState A B) :
    cost (![0,4] r) kind .outer true true a b A B x=
      x+coreC r+coreG r*b-(targetLabel r).outer B := by
  rw [(targetLabel r).outer_actual ht]
  revert hk
  fin_cases r <;> cases kind <;>
    norm_num [cost,label,wrongValue,WordProblems.secondCoefficients,
      WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
      next,coreC,coreG,targetLabel,JLabel,KLabel,RoleLabel.eval] <;> ring

lemma same_outer_literal (r : SameRow) (kind : RadialKind) (hk : kind≠.outer)
    {a b A B x : ℝ} (hs : OuterState a b) :
    cost (![0,4] r) .outer kind true true a b A B x=
      x+(sourceLabel r).outer b-outerC r-outerG r*B := by
  rw [(sourceLabel r).outer_actual hs]
  revert hk
  fin_cases r <;> cases kind <;>
    norm_num [cost,label,wrongValue,WordProblems.secondCoefficients,
      WordProblems.radialIndex,WordProblems.signIndex,WordProblems.sign,
      next,outerC,outerG,sourceLabel,PLabel,LLabel,RoleLabel.eval] <;> ring

end SquaresInCircles.Eight.SecondWord.MixedZero
end
end
end

section
/-!
## Both positive-core/positive-outer zero rows

A single circle support applies throughout
the original frame interval.  Its rotating-vector speed is at most the
core slope, so the fixed initial lower bound pays the entire possible
angle loss.  Every source point on both closed core pieces is included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.SameCore
open CommonQuarter CorePairGeometry Arithmetic

def N (r : SameRow) (x : ℝ) : ℝ :=
  CircularNorm.norm ((coreG r)^2+(11/10)^2) (-2*coreG r*(11/10)) 0 x
def Nd (r : SameRow) (x : ℝ) : ℝ := coreG r*(11/10)*Real.sin x/N r x
def F (r : SameRow) (x : ℝ) : ℝ :=
  x+coreC r+(coreG r+11/10)/2+coreG r*Real.sin x-CommonQuarter.radius*N r x
def Fd (r : SameRow) (x : ℝ) : ℝ := 1+coreG r*Real.cos x-CommonQuarter.radius*Nd r x

lemma energy_positive (r : SameRow) (x : ℝ) :
    0<CircularNorm.energy ((coreG r)^2+(11/10)^2)
      (-2*coreG r*(11/10)) 0 x := by
  fin_cases r <;> norm_num [coreG,CircularNorm.energy] <;>
    nlinarith [Real.cos_le_one x]

lemma N_positive (r : SameRow) (x : ℝ) : 0<N r x :=
  CircularNorm.norm_pos (energy_positive r x)

lemma N_square (r : SameRow) (x : ℝ) :
    (N r x)^2=(coreG r)^2+(11/10)^2-2*coreG r*(11/10)*Real.cos x := by
  have hh := CircularNorm.norm_sq (energy_positive r x).le
  simp only [N]
  rw [hh]
  simp only [CircularNorm.energy]
  ring

lemma N_hasDerivAt (r : SameRow) (x : ℝ) : HasDerivAt (N r) (Nd r x) x := by
  have hn : CircularNorm.norm ((coreG r)^2+(11/10)^2)
      (-2*coreG r*(11/10)) 0 x≠0 := (N_positive r x).ne'
  convert CircularNorm.norm_hasDerivAt (energy_positive r x) using 1
  · rfl
  · dsimp [Nd,N,CircularNorm.d1,CircularNorm.slope]
    field_simp [hn]
    ring

lemma speed_upper (r : SameRow) (x : ℝ) : Nd r x≤coreG r := by
  have hn := N_square r x
  have hid : ((11/10)*Real.sin x)^2+
      (coreG r-(11/10)*Real.cos x)^2=(N r x)^2 := by
    linear_combination (121/100:ℝ)*(Real.sin_sq_add_cos_sq x)-hn
  have hs : (11/10)*Real.sin x≤N r x := by
    nlinarith [sq_nonneg (coreG r-(11/10)*Real.cos x),N_positive r x]
  have hg : 0≤coreG r := by linarith [(core_coefficients r).1]
  apply (div_le_iff₀ (N_positive r x)).2
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hg

lemma F_hasDerivAt (r : SameRow) (x : ℝ) : HasDerivAt (F r) (Fd r x) x := by
  have h := (((((hasDerivAt_id' x).add_const (coreC r)).add_const
    ((coreG r+11/10)/2)).add ((Real.hasDerivAt_sin x).const_mul (coreG r))).sub
      ((N_hasDerivAt r x).const_mul CommonQuarter.radius))
  exact h.congr_deriv (by simp only [Fd])

lemma derivative_lower (r : SameRow) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    -(27/100:ℝ)<Fd r x := by
  have hr := radius_bounds
  have hg : 0<coreG r := by linarith [(core_coefficients r).1]
  have hR : 0<CommonQuarter.radius := by linarith [hr.1]
  have hs := mul_le_mul_of_nonneg_left (speed_upper r x) hR.le
  have hc := mul_lt_mul_of_pos_left
    (ShortMixedZero.PositiveCore.angle_trig hx).2 hg
  have hu := mul_lt_mul_of_pos_right hr.2 hg
  dsimp [Fd]
  fin_cases r <;> norm_num [coreG] at hs hc hu ⊢ <;> linarith

lemma initial_norm (r : SameRow) : N r (2/5)<(217/500:ℝ) := by
  have hh := N_square r (2/5)
  have hp := N_positive r (2/5)
  have hc := mul_lt_mul_of_pos_left ShortMixedZero.PositiveCore.initial_trig.2.2
    (show 0<2*coreG r*(11/10) by linarith [(core_coefficients r).1])
  generalize N r (2/5) = n at hh hp ⊢
  fin_cases r <;> norm_num [coreG] at hh hc ⊢ <;> nlinarith

lemma initial_value (r : SameRow) : (49/50:ℝ)<F r (2/5) := by
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hn := mul_lt_mul_of_pos_left (initial_norm r) hR
  have hr := mul_lt_mul_of_pos_right radius_bounds.2
    (by norm_num : (0:ℝ)<217/500)
  have hs := mul_lt_mul_of_pos_left ShortMixedZero.PositiveCore.initial_trig.1
    (show 0<coreG r by linarith [(core_coefficients r).1])
  dsimp only [F]
  generalize N r (2/5) = n at hn ⊢
  fin_cases r <;> norm_num [coreC,coreG] at hs ⊢ <;> linarith

lemma support_lower (r : SameRow) {x : ℝ} (hx : x∈Icc (2/5) (7/10)) :
    (17953/20000:ℝ)<F r x := by
  have hd (t : ℝ) : HasDerivAt (fun t => F r t+(27/100)*t) (Fd r t+27/100) t :=
    ((F_hasDerivAt r t).add ((hasDerivAt_id' t).const_mul (27/100:ℝ))).congr_deriv (by ring)
  have hm : MonotoneOn (fun t => F r t+(27/100)*t) (Icc (2/5) (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => hd t)
      (fun t ht => by linarith [derivative_lower r (Ioo_subset_Icc_self ht)])
  have hh := hm (by norm_num) hx hx.1
  simp only at hh
  linarith [initial_value r,hx.2]

theorem original (r : SameRow) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (17953/20000:ℝ)<x+coreC r+coreG r*b-(targetLabel r).outer B := by
  have hangle : x∈Icc (2/5) (7/10) :=
    ⟨(ShortMixedZero.PositiveCore.original_angle hs ht hx hm).le,(abs_le.mp hx).2⟩
  have tr := positive_trig
    (show x∈Icc 0 (7/10) from ⟨by linarith [hangle.1],hangle.2⟩)
  have hw : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hx,abs_of_nonneg tr.2.2.1]
    ring
  have hmargin := mul_nonneg
    (show 0≤coreG r by linarith [(core_coefficients r).1]) hm
  norm_num [Eight.forwardMargin] at hmargin
  rw [hw] at hmargin
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have htarget := target_affine_upper r hB
  have hsupp := outer_circle_lower (X := -coreG r*Real.sin x)
    (Y := coreG r*Real.cos x-11/10) ht
  have he : (-coreG r*Real.sin x)^2+(coreG r*Real.cos x-11/10)^2=
      (coreG r)^2+(11/10)^2-2*coreG r*(11/10)*Real.cos x := by
    linear_combination (coreG r)^2*(Real.sin_sq_add_cos_sq x)
  have hn : N r x=Real.sqrt ((-coreG r*Real.sin x)^2+
      (coreG r*Real.cos x-11/10)^2) := by
    rw [he]
    simp only [N,CircularNorm.norm,CircularNorm.energy]
    congr 1
    ring
  rw [←hn] at hsupp
  have hl := support_lower r hangle
  dsimp [F] at hl
  nlinarith only [hmargin,hsupp,htarget,hl]

end SquaresInCircles.Eight.SecondWord.MixedZero.SameCore
end
end
end

section
/-!
## Both positive-outer/positive-core zero rows

The original source-secondary separator
forces the angle above `.46`.  A whole-arc lower affine bound for the
outer label then leaves one elementary quadratic in the frame angle.
This includes both core pieces, the arc endpoints and all weak contacts.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.SameOuter
open CommonQuarter CorePairGeometry Arithmetic

lemma original_angle {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) : (23/50:ℝ)<x := by
  have hcut := ShortMixedZero.PositiveOuter.original_cuts hs ht hx hm
  have hp : x∈Icc 0 (7/10) := ⟨by linarith [hcut.1],(abs_le.mp hx).2⟩
  have tr := positive_trig hp
  have hw : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hx,abs_of_nonneg tr.2.2.1]
    ring
  have hm' := hm
  norm_num [Eight.forwardMargin] at hm'
  rw [hw,hcut.2.1] at hm'
  have hBc := mul_nonneg (CoreAngleEndpoint.state_bounds ht).2.2.1
    (show 0≤Real.cos x by linarith [tr.1])
  have hb : b<(9/10:ℝ) :=
    (outer_bounds hs).2.2.2.1.trans_lt outer_endpoint_bounds.2.2.2
  by_contra! hn
  have hsine := Real.sin_le hp.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsquare := pow_le_pow_left₀ hp.1 hn 2
  nlinarith

theorem original (r : SameRow) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (17953/20000:ℝ)<x+(sourceLabel r).outer b-outerC r-outerG r*B := by
  have hangle := original_angle hs ht hx hm
  have hp : x∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hx).2⟩
  have tr := positive_trig hp
  have hw : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hx,abs_of_nonneg tr.2.2.1]
    ring
  have hm' := hm
  norm_num [Eight.forwardMargin] at hm'
  rw [hw] at hm'
  have hc := CoreAngleEndpoint.state_bounds ht
  have hA := mul_le_mul_of_nonneg_right hc.2.1 tr.2.2.1
  have hg := outer_coefficients r
  have hB := mul_nonneg hc.2.2.1
    (show 0≤Real.cos x-outerG r by linarith [hg.2.1,tr.1])
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hline := source_affine_lower r hb
  have hloss := mul_le_mul_of_nonneg_left
    (show b≤(9/10:ℝ) from hb.2.trans outer_endpoint_bounds.2.2.2.le)
    (show 0≤1-sourceSlope r by linarith [hg.2.2.2])
  have hsine := Real.sin_le hp.1
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hquad : (11/12:ℝ)*(23/50)-(23/50:ℝ)^2/4≤(11/12)*x-x^2/4 := by
    have hprod := mul_nonneg (show 0≤x-23/50 by linarith)
      (show 0≤11/12-(x+23/50)/4 by linarith [hp.2])
    nlinarith
  rw [source_zero] at hline
  generalize outerG r = G at hB ⊢
  fin_cases r <;> norm_num [sourceSlope,outerC] at hline hloss hquad ⊢ <;>
    nlinarith only [hm',hA,hB,hline,hloss,hsine,hcos,hquad]

end SquaresInCircles.Eight.SecondWord.MixedZero.SameOuter
end
end
end

section
@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Same
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

def Mixed (source target : RadialKind) : Prop :=
  (source=.outer ∧ target≠.outer) ∨ (source≠.outer ∧ target=.outer)

lemma mixed_swap {source target : RadialKind} (hm : Mixed source target) :
    Mixed target source := by
  rcases hm with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact Or.inr ⟨ht,hs⟩
  · exact Or.inl ⟨ht,hs⟩

lemma positive_roles (i : Vertex) (hi : WordProblems.wrongWord .second i=0)
    (ha : WordProblems.allowed .second i true true) : i=0 ∨ i=4 := by
  revert hi ha
  fin_cases i <;> norm_num [WordProblems.wrongWord,WordProblems.allowed,next]

lemma negative_roles (i : Vertex) (hi : WordProblems.wrongWord .second i=0)
    (ha : WordProblems.allowed .second i false false) : i=1 ∨ i=4 := by
  revert hi ha
  fin_cases i <;> norm_num [WordProblems.wrongWord,WordProblems.allowed,next]

theorem original_row (r : SameRow) {source target : RadialKind}
    (hmixed : Mixed source target) {a b A B x : ℝ}
    (hs : State source a b) (ht : State target A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    (17953/20000:ℝ)<cost (![0,4] r) source target true true a b A B x := by
  rcases hmixed with ⟨rfl,hcore⟩ | ⟨hcore,rfl⟩
  · have ho : OuterState a b := by simpa [State] using hs
    have hc : CoreState A B := by simpa [State,hcore] using ht
    rw [same_outer_literal r target hcore ho]
    exact SameOuter.original r ho hc hx hm
  · have hc : CoreState a b := by simpa [State,hcore] using hs
    have ho : OuterState A B := by simpa [State] using ht
    rw [same_core_literal r source hcore ho]
    exact SameCore.original r hc ho hx hm

theorem original_positive {i : Vertex} (hi : i=0 ∨ i=4)
    {source target : RadialKind} (hmixed : Mixed source target)
    {a b A B x : ℝ} (hs : State source a b) (ht : State target A B)
    (hx : |x|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 x) :
    threshold i<cost i source target true true a b A B x := by
  rw [threshold_value]
  rcases hi with rfl | rfl
  · simpa using original_row (0:SameRow) hmixed hs ht hx hm
  · simpa using original_row (1:SameRow) hmixed hs ht hx hm

theorem original_negative {i : Vertex} (hi : i=1 ∨ i=4)
    {source target : RadialKind} (hmixed : Mixed source target)
    {a b A B x : ℝ} (hs : State source a b) (ht : State target A B)
    (hx : |x|≤7/10) (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) x) :
    threshold i<cost i source target false false a b A B x := by
  have hrev : 0≤Eight.forwardMargin 0 A B a b 1 1 x := by
    have h2 : Eight.forwardMargin 2 a b A B (-1) (-1) x=
        a*Real.sin x+(-1)*b*Real.cos x-(-1)*B-pairWidth x := rfl
    have h0 : Eight.forwardMargin 0 A B a b 1 1 x=
        1*B+a*Real.sin x-1*b*Real.cos x-pairWidth x := rfl
    rw [h0]
    rw [h2] at hm
    linarith
  have hir : reverseEdge i=0 ∨ reverseEdge i=4 := by
    rcases hi with rfl | rfl <;> norm_num [reverseEdge]
  have hh := original_positive hir (mixed_swap hmixed) ht hs hx hrev
  have he := cost_reflection i source target false false a b A B x
  norm_num at he
  rw [he,threshold_value] at hh
  simpa only [threshold_value] using hh

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Mixed (C.kind i) (C.kind (next i)))
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  have hx : |phaseValue F hgap i|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hword : WordProblems.wrongWord .second i=0 := by simpa [hw] using hi
  have ha := actual_allowed C F hgap .second hw i
  have hm := original_margin C F hgap i j howner
  have hh : threshold i<cost i (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i))
      (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (phaseValue F hgap i) := by
    rcases WrongZeroOriginalOwners.original C F hgap i hi j howner with
      ⟨rfl,hpos⟩ | ⟨rfl,hneg⟩
    · have htpos : positiveOf C (next i)=true := hsg.symm.trans hpos
      rw [hpos,htpos] at ha ⊢
      exact original_positive (positive_roles i hword ha) hmixed
        (actual_state C i) (actual_state C (next i)) hx
        (by simpa [hpos,htpos,WordProblems.sign] using hm)
    · have hsneg : positiveOf C i=false := hsg.trans hneg
      rw [hsneg,hneg] at ha ⊢
      exact original_negative (negative_roles i hword ha) hmixed
        (actual_state C i) (actual_state C (next i)) hx
        (by simpa [hsneg,hneg,WordProblems.sign] using hm)
  simpa only [cost,label,wrongMarker] using hh

theorem actual (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .second)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=0)
    (hmixed : Mixed (C.kind i) (C.kind (next i)))
    (hsg : positiveOf C i=positiveOf C (next i)) :
    threshold i<phaseValue F hgap i+wrongMarker C .second i-
      wrongMarker C .second (next i) := by
  obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
  have howner : (forwardAxis j).Feasible (C.square i) (C.square (next i)) := by
    simpa only [←hj] using C.feasible i
  exact actual_owner C F hgap hw i hi hmixed hsg j howner

end SquaresInCircles.Eight.SecondWord.MixedZero.Same
end
end
end
