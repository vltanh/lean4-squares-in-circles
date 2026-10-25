module

public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroCoreNegative
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroOuter
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroPositiveCore

/-!
# Eight squares: same-sign mixed zero edges with their original role labels

The finite steps below identify only the exact role coefficients and the two secondary-axis
presentations (`positive_zero_roles`, `negative_zero_roles`). Their analytic estimates are
whole-interval theorems on the original core and outer states (`same_outer_source`,
`same_core_source`, `same_outer_target`, `same_core_target`).
-/

section
/-!
## Four negative-core contact costs on their complete geometric interval

The exact rotated coordinates make all four contact costs strictly
concave: both terms of their second derivative have the required sign.
The possible diagonal competitor increases. Strict rational comparisons
at the geometric interval's two endpoints complete the scalar proof.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.NegativeContact

open CommonQuarter CorePairGeometry

abbrev Row := Fin 4
def c : Row → ℝ := ![-11418/100000,7943/100000,-25648/100000,-94615/100000]
def p : Row → ℝ := ![9133/100000,19335/100000,0,-51554/100000]
def q : Row → ℝ := ![88074/100000,76744/100000,94766/100000,119909/100000]
def g : Row → ℝ := ![62095/100000,62750/100000,62095/100000,58829/100000]
def H (r : Row) (x : ℝ) : ℝ := x+c r-p r*(U x-1/2)+q r*(V x-1/2)
def Hd (r : Row) (x : ℝ) : ℝ := 1-speed x*(p r*V x+q r*U x)
def Hdd (r : Row) (x : ℝ) : ℝ :=
  -speedD x*(p r*V x+q r*U x)+(speed x)^2*(p r*U x-q r*V x)
def G (r : Row) (x : ℝ) : ℝ := x+c r+(q r-p r)*outerDiagonal-g r*cut x
def Gd (r : Row) (x : ℝ) : ℝ := 1-g r*(outerDiagonal-1/2)*n x

lemma coefficient_bounds (r : Row) : 0<g r ∧ g r<1 ∧ 0<q r := by
  fin_cases r <;> norm_num [g,q]

lemma H_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt (H r) (Hd r x) x := by
  have hh : HasDerivAt (fun y => y+c r-p r*(U y-1/2)+q r*(V y-1/2))
      (1-p r*(V x*speed x)+q r*(-U x*speed x)) x :=
    (((hasDerivAt_id' x).add_const (c r)).sub
      (((U_hasDerivAt hx).sub_const (1/2)).const_mul (p r))).add
        (((V_hasDerivAt hx).sub_const (1/2)).const_mul (q r))
  exact hh.congr_deriv (by dsimp [Hd]; ring)

lemma Hd_hasDerivAt (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) :
    HasDerivAt (Hd r) (Hdd r x) x := by
  have hh : HasDerivAt (fun y => 1-speed y*(p r*V y+q r*U y))
      (-(speedD x*(p r*V x+q r*U x)+speed x*(p r*(-U x*speed x)+q r*(V x*speed x)))) x :=
    ((speed_hasDerivAt hx).mul
      (((V_hasDerivAt hx).const_mul (p r)).add
        ((U_hasDerivAt hx).const_mul (q r)))).const_sub 1
  exact hh.congr_deriv (by dsimp [Hdd]; ring)

lemma contact_coefficients (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) :
    0<p r*V x+q r*U x ∧ p r*U x-q r*V x<0 := by
  have hc := coordinates hx
  fin_cases r <;> norm_num [p,q] <;>
    constructor <;> nlinarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

lemma Hdd_neg (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) : Hdd r x<0 := by
  have hh := contact_coefficients r hx
  have hp := mul_pos (speedD_pos hx) hh.1
  have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (speed x)) hh.2.le
  dsimp [Hdd]
  linarith

lemma H_concave (r : Row) : ConcaveOn ℝ (Icc start (7/10)) (H r) :=
  concave_of_deriv2 (fun _ hx => H_hasDerivAt r hx)
    (fun _ hx => Hd_hasDerivAt r hx) (fun _ hx => (Hdd_neg r hx).le)

lemma H_endpoints (r : Row) : (449/500:ℝ)<H r start ∧ (449/500:ℝ)<H r (7/10) := by
  have he := endpoint_coordinates
  have hend : (7/10:ℝ)∈Icc start (7/10) := by norm_num [start]
  have hc := coordinates hend
  have hst : start=30243/100000 := rfl
  constructor
  · fin_cases r <;> norm_num [H,c,p,q] <;>
      linarith only [he.1,he.2.1,he.2.2.1,he.2.2.2.1,hst]
  · fin_cases r <;> norm_num [H,c,p,q] <;>
      linarith only [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem H_lower (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) : (449/500:ℝ)<H r x :=
  concave_gt_of_endpoints (H_concave r) hx (H_endpoints r).1 (H_endpoints r).2

lemma G_hasDerivAt (r : Row) (x : ℝ) : HasDerivAt (G r) (Gd r x) x := by
  have hh : HasDerivAt (fun y => y+c r+(q r-p r)*outerDiagonal-
      g r*((outerDiagonal-1/2)*m y-1/2))
      (1-g r*((outerDiagonal-1/2)*n x)) x :=
    (((hasDerivAt_id' x).add_const (c r)).add_const ((q r-p r)*outerDiagonal)).sub
      ((((m_hasDerivAt x).const_mul (outerDiagonal-1/2)).sub_const (1/2)).const_mul (g r))
  exact hh.congr_deriv (by dsimp [Gd]; ring)

lemma Gd_pos (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) : 0<Gd r x := by
  have hx' : x∈Icc 0 (7/10) := ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩
  have tr := positive_trig hx'
  have hn : n x≤1 := by dsimp [n]; linarith [tr.2.1,tr.2.2.1]
  have hcoef : 0≤g r*(outerDiagonal-1/2) :=
    mul_nonneg (coefficient_bounds r).1.le (by linarith [fine_diagonal_bounds.1])
  have hp := mul_le_mul_of_nonneg_left hn hcoef
  have hd := mul_lt_mul_of_pos_left (show outerDiagonal-1/2<(2/5:ℝ) by
    linarith [outer_endpoint_bounds.2.2.2]) (coefficient_bounds r).1
  dsimp [Gd]
  nlinarith [(coefficient_bounds r).2.1]

lemma G_initial (r : Row) : (449/500:ℝ)<G r start := by
  have hd := fine_diagonal_bounds
  have hp := mul_neg_of_pos_of_neg (coefficient_bounds r).1 cut_start_neg
  dsimp [G]
  fin_cases r <;> norm_num [start,c,p,q,g] at hp ⊢ <;> linarith [hd.1,hd.2]

theorem G_lower (r : Row) {x : ℝ} (hx : x∈Icc start (7/10)) : (449/500:ℝ)<G r x := by
  have hm : MonotoneOn (G r) (Icc start (7/10)) :=
    monoOn_of_hasDeriv_nonneg (fun z _ => (G_hasDerivAt r z).continuousAt.continuousWithinAt)
      (fun z _ => G_hasDerivAt r z) (fun z hz => (Gd_pos r (Ioo_subset_Icc_self hz)).le)
  exact (G_initial r).trans_le (hm (by norm_num [start]) hx hx.1)

end SquaresInCircles.Eight.ShortMixedZero.NegativeContact
end
end
end

section
/-!
## Four complete negative-core to negative-outer families

The original weak owner pays the negative source label. The resulting
outer functional increases from the actual zero-source contact in three
families; the fourth is concave and has only that contact and the
diagonal as possible minimizers. Both values have already been bounded
on their complete geometric interval.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.NegativeContact

open CommonQuarter CorePairGeometry

def coeffX (r : Row) (x : ℝ) : ℝ := -p r-g r*Real.sin x
def coeffY (r : Row) (x : ℝ) : ℝ := q r-g r*Real.cos x
def base (r : Row) (x : ℝ) : ℝ := x+c r+g r*(1+Real.sin x+Real.cos x)/2

lemma contact_value (r : Row) (x : ℝ) :
    H r x=base r x+coeffX r x*(U x-1/2)+coeffY r x*(V x-1/2) := by
  have hh := congrArg (fun z : ℝ => g r*z) (contact_equation x)
  dsimp [H,base,coeffX,coeffY]
  nlinarith only [hh]

lemma diagonal_value (r : Row) (x : ℝ) :
    G r x=base r x+(coeffX r x+coeffY r x)*outerDiagonal := by
  dsimp [G,base,coeffX,coeffY,cut,m]
  ring

lemma original_support (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc start (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤-b+A*Real.sin x+B*Real.cos x) :
    min (H r x) (G r x)≤base r x+coeffX r x*A+coeffY r x*B := by
  obtain ⟨hc,hB⟩ := original_contact hs ht hx hm
  have tr := positive_trig (show x∈Icc 0 (7/10) from
    ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩)
  have hHv := (min_le_left (H r x) (G r x)).trans_eq (contact_value r x)
  have hGv := (min_le_right (H r x) (G r x)).trans_eq (diagonal_value r x)
  by_cases h3 : r=3
  · subst r
    have hX : 0≤coeffX 3 x := by norm_num [coeffX,p,g]; linarith [tr.2.2.2.1]
    have hh := CoreContact.outer_subarc_lower hc ht hB hX
      (m := min (H 3 x) (G 3 x)-base 3 x) (Y := coeffY 3 x)
      (by linarith) (by linarith)
    linarith
  · have hX : coeffX r x≤0 := by
      fin_cases r <;> first
        | exact absurd rfl h3
        | (norm_num [coeffX,p,g]; nlinarith [tr.2.2.1])
    have hY : 0≤coeffY r x := by
      fin_cases r <;> first
        | exact absurd rfl h3
        | (norm_num [coeffY,q,g]; linarith [tr.2.1])
    have hA := CoreContact.outer_primary_order hc ht hB
    have hp := mul_le_mul_of_nonpos_left hA hX
    have hq := mul_le_mul_of_nonneg_left hB hY
    linarith

/-- All four original negative-core/negative-outer source-secondary
families, including the full corner, side and weak contact cases. -/
theorem original_cost (r : Row) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) :
    (449/500:ℝ)<φ+c r-g r*b-p r*A+q r*B := by
  have hx : φ∈Icc start (7/10) :=
    ⟨(original_angle hs ht hφ hm).le,(abs_le.mp hφ).2⟩
  have tr := positive_trig (show φ∈Icc 0 (7/10) from
    ⟨by linarith [hx.1,(show (0:ℝ)<start by norm_num [start])],hx.2⟩)
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  have hm' : (1+Real.sin φ+Real.cos φ)/2≤-b+A*Real.sin φ+B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    rw [hw] at hm
    linarith
  have hsupport := original_support r hs ht hx hm'
  have hmargin := mul_le_mul_of_nonneg_left hm' (coefficient_bounds r).1.le
  have hcost : min (H r φ) (G r φ)≤φ+c r-g r*b-p r*A+q r*B := by
    dsimp [base,coeffX,coeffY] at hsupport
    nlinarith only [hsupport,hmargin]
  exact (lt_min (H_lower r hx) (G_lower r hx)).trans_le hcost

end SquaresInCircles.Eight.ShortMixedZero.NegativeContact
end
end
end

section
/-!
## Positive outer source and positive core target, original zero owner

The original separator forces the target onto its core side, the angle
above `.4`, and the original outer secondary coordinate above
`.828+.764 B`. A single sloping line supports the remaining outer arc.
These geometric inequalities pay all four exact label families directly;
no angle partition or target-contact minimizer is needed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.ShortMixedZero.PositiveOuter

open CommonQuarter CorePairGeometry

abbrev Row := Fin 4
def c : Row → ℝ := ![-25648/100000,-11418/100000,-94615/100000,7943/100000]
def p : Row → ℝ := ![0,-9133/100000,51554/100000,-19335/100000]
def q : Row → ℝ := ![94766/100000,88074/100000,119909/100000,76744/100000]
def g : Row → ℝ := ![62095/100000,62095/100000,58829/100000,62750/100000]

/-- The positivity half of `CommonQuarter.zero_positive_secondary_angle` (not imported here):
the original weak separator forces a positive angle. -/
private lemma zero_positive_angle_pos {source target : RadialKind}
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) : 0<φ := by
  have hs' := state_bounds hs
  have ht' := state_bounds ht
  have hc : 0<Real.cos φ := by linarith [(signed_cos hφ).1]
  have hw : 1≤pairWidth φ := by
    have h := one_le_abs_cos_add_abs_sin φ
    dsimp [pairWidth]
    linarith
  by_contra! hn
  have hsin : Real.sin φ≤0 := by
    have hp := positive_trig (x := -φ) ⟨by linarith,by linarith [(abs_le.mp hφ).1]⟩
    simpa only [Real.sin_neg,neg_nonneg] using hp.2.2.1
  have hAs := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤A by linarith [ht'.1]) hsin
  have hBc := mul_nonneg ht'.2.2.1 hc.le
  norm_num [forwardMargin] at hm
  nlinarith [hs'.2.2.2.2]

lemma original_cuts {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ|≤7/10) (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (2/5:ℝ)<φ ∧ A=7/12 ∧ (207/250:ℝ)+(191/250)*B<b := by
  have hp := zero_positive_angle_pos (source := .outer) (target := .coreSide)
    (by simpa [State] using hs) (by simpa [State] using ht) hφ hm
  have hx : φ∈Icc 0 (7/10) := ⟨by linarith,(abs_le.mp hφ).2⟩
  have tr := positive_trig hx
  have ho := outer_bounds hs
  have hcore := CoreAngleEndpoint.state_bounds ht
  have hw : pairWidth φ=(1+Real.sin φ+Real.cos φ)/2 := by
    rw [signed_width hφ,abs_of_nonneg tr.2.2.1]
    ring
  have hm' : (1+Real.sin φ+Real.cos φ)/2≤b+A*Real.sin φ-B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    rw [hw] at hm
    linarith
  have hAs := mul_le_mul_of_nonneg_right hcore.2.1 tr.2.2.1
  have hc0 : 0≤Real.cos φ := (lt_trans (by norm_num) tr.1).le
  have hsmall : B<1/2 := by
    by_contra! hlarge
    have hBc := mul_le_mul_of_nonneg_right hlarge hc0
    linarith [ho.2.2.2.1,outer_endpoint_bounds.2.2.2,tr.1,tr.2.2.2.1]
  obtain ⟨hA,_⟩ := core_small_side ht hsmall
  rw [hA] at hm'
  have hBc := mul_nonneg hcore.2.2.1 hc0
  have hangle : (2/5:ℝ)<φ := by
    by_contra! hn
    have hco := Real.one_sub_sq_div_two_le_cos (x := φ)
    have hsi := Real.sin_le hx.1
    have hs2 := pow_le_pow_left₀ hx.1 hn 2
    linarith [ho.2.2.2.1,outer_endpoint_bounds.2.2.2]
  have hBc' := mul_le_mul_of_nonneg_right
    (le_trans (by norm_num : (191/250:ℝ)≤19121/25000) tr.1.le) hcore.2.2.1
  exact ⟨hangle,hA,by linarith [tr.1,tr.2.2.2.1]⟩

/-- One circle calculation gives a supporting line on the entire arc
selected by the original owner. The reference point is strictly outside
the containing circle, providing a uniform reserve. -/
lemma original_sloping_line {a b : ℝ} (hs : OuterState a b) (hb : (207/250:ℝ)≤b) :
    a+(9/10)*b<(1072/625:ℝ) := by
  have hbu : b<9/10 := (outer_bounds hs).2.2.2.1.trans_lt outer_endpoint_bounds.2.2.2
  by_contra! hn
  have hl : 0≤(97/100:ℝ)-(9/10)*(b-207/250)+1/2 := by linarith
  have hsqa := pow_le_pow_left₀ hl
    (show (97/100:ℝ)-(9/10)*(b-207/250)+1/2≤a+1/2 by linarith) 2
  have hc := hs.2.2
  norm_num [Q0] at hc
  nlinarith [sq_nonneg (b-207/250)]

lemma role_comparisons (r : Row) (hr : r≠2) :
    p r≤0 ∧ 0≤q r-(9/10)*p r ∧
      0≤(191/250)*(q r-(9/10)*p r)-g r ∧
        (449/500:ℝ)<2/5+c r+(97/100)*p r+(207/250)*q r := by
  fin_cases r
  · norm_num [c,p,q,g]
  · norm_num [c,p,q,g]
  · exact absurd rfl hr
  · norm_num [c,p,q,g]

/-- The four complete positive-outer/positive-core families with their
original weak source-secondary axis and complete core state. -/
theorem original_cost (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B 1 1 φ) :
    (449/500:ℝ)<φ+c r+p r*a+q r*b-g r*B := by
  obtain ⟨hangle,hA,hb⟩ := original_cuts hs ht hφ hm
  have hB := (CoreAngleEndpoint.state_bounds ht).2.2.1
  have hb0 : (207/250:ℝ)≤b := by linarith
  by_cases hr : r=2
  · subst r
    have ha : (899/1000:ℝ)<a :=
      (by linarith [fine_diagonal_bounds.1] : (899/1000:ℝ)<outerDiagonal).trans_le
        (outer_bounds hs).1
    norm_num [c,p,q,g]
    nlinarith
  · have hline := original_sloping_line hs hb0
    have hh := role_comparisons r hr
    have hp := mul_le_mul_of_nonpos_left hline.le hh.1
    have hq := mul_le_mul_of_nonneg_left hb.le hh.2.1
    have hrem := mul_nonneg hh.2.2.1 hB
    nlinarith only [hangle,hp,hq,hrem,hh.2.2.2]

end SquaresInCircles.Eight.ShortMixedZero.PositiveOuter
end
end
end

section
@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.ShortMixedZero

open CommonQuarter CorePairGeometry WordProblems QuarterWordGeometry

lemma positive_zero_roles (i : Vertex) (hi : wrongWord .short i=0)
    (ha : allowed .short i true true) : i=0 ∨ i=3 := by
  revert hi ha
  fin_cases i <;> decide

lemma negative_zero_roles (i : Vertex) (hi : wrongWord .short i=0)
    (ha : allowed .short i false false) : i=1 ∨ i=3 := by
  revert hi ha
  fin_cases i <;> decide

/-- The case `τ = false` of `CommonQuarter.negative_source_core_target_false`: a negative source
cannot own a core target on the negative secondary axis. -/
private lemma negative_source_core_target_false {a b A B φ : ℝ}
    (hb : 0≤b) (ht : CoreState A B)
    (hm : 0≤forwardMargin 0 a b A B (-1) (-1) φ) : False := by
  have hcore := CorePairGeometry.core_radius_sq ht
  have hw : 1≤pairWidth φ := by
    have h := one_le_abs_cos_add_abs_sin φ
    dsimp [pairWidth]
    linarith
  have hproj : 1≤A*Real.sin φ+B*Real.cos φ := by
    norm_num [forwardMargin] at hm
    linarith
  have hid : (A*Real.sin φ+B*Real.cos φ)^2+
      (A*Real.cos φ-B*Real.sin φ)^2=A^2+B^2 := by
    linear_combination (A^2+B^2)*(Real.sin_sq_add_cos_sq φ)
  nlinarith [sq_nonneg (A*Real.cos φ-B*Real.sin φ),
    sq_nonneg (A*Real.sin φ+B*Real.cos φ-1)]

theorem same_outer_source (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) kind σ A B := by
  cases σ
  · exact (negative_source_core_target_false hs.1 ht (by simpa [sign] using hm)).elim
  · have hm' : 0≤forwardMargin 0 a b A B 1 1 φ := by simpa [sign] using hm
    rcases positive_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveOuter.original_cost 0 hs ht hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveOuter.original_cost 2 hs ht hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith

theorem same_core_source (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 0 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i kind σ a b-
      wrongValue .short (next i) .outer σ A B := by
  cases σ
  · have hm' : 0≤forwardMargin 0 a b A B (-1) (-1) φ := by simpa [sign] using hm
    rcases negative_zero_roles i hi ha with rfl | rfl
    · have hh := NegativeContact.original_cost 0 hs ht hφ hm'
      norm_num [NegativeContact.c,NegativeContact.p,NegativeContact.q,NegativeContact.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := NegativeContact.original_cost 1 hs ht hφ hm'
      norm_num [NegativeContact.c,NegativeContact.p,NegativeContact.q,NegativeContact.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
  · have hm' : 0≤forwardMargin 0 a b A B 1 1 φ := by simpa [sign] using hm
    rcases positive_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveCore.original_cost 0 hs ht hφ hm'
      norm_num [PositiveCore.c,PositiveCore.p,PositiveCore.q,PositiveCore.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveCore.original_cost 3 hs ht hφ hm'
      norm_num [PositiveCore.c,PositiveCore.p,PositiveCore.q,PositiveCore.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith

theorem same_outer_target (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 2 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) kind σ A B := by
  cases σ
  · have hm' : 0≤forwardMargin 0 A B a b 1 1 φ := by
      norm_num [forwardMargin,sign] at hm ⊢
      linarith
    rcases negative_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveCore.original_cost 1 ht hs hφ hm'
      norm_num [PositiveCore.c,PositiveCore.p,PositiveCore.q,PositiveCore.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveCore.original_cost 2 ht hs hφ hm'
      norm_num [PositiveCore.c,PositiveCore.p,PositiveCore.q,PositiveCore.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
  · have hm' : 0≤forwardMargin 0 A B a b (-1) (-1) φ := by
      norm_num [forwardMargin,sign] at hm ⊢
      linarith
    rcases positive_zero_roles i hi ha with rfl | rfl
    · have hh := NegativeContact.original_cost 2 ht hs hφ hm'
      norm_num [NegativeContact.c,NegativeContact.p,NegativeContact.q,NegativeContact.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := NegativeContact.original_cost 3 ht hs hφ hm'
      norm_num [NegativeContact.c,NegativeContact.p,NegativeContact.q,NegativeContact.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith

theorem same_core_target (i : Vertex) (hi : wrongWord .short i=0)
    (kind : RadialKind) (hk : kind≠.outer) (σ : Bool) (ha : allowed .short i σ σ)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ|≤7/10)
    (hm : 0≤forwardMargin 2 a b A B (sign σ) (sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i kind σ a b-
      wrongValue .short (next i) .outer σ A B := by
  cases σ
  · have hm' : 0≤forwardMargin 0 A B a b 1 1 φ := by
      norm_num [forwardMargin,sign] at hm ⊢
      linarith
    rcases negative_zero_roles i hi ha with rfl | rfl
    · have hh := PositiveOuter.original_cost 1 ht hs hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
    · have hh := PositiveOuter.original_cost 3 ht hs hφ hm'
      norm_num [PositiveOuter.c,PositiveOuter.p,PositiveOuter.q,PositiveOuter.g,
        wrongValue,shortCoefficients,radialIndex,hk,signIndex,sign,next] at hh ⊢
      linarith
  · have hm' : 0≤forwardMargin 0 A B a b (-1) (-1) φ := by
      norm_num [forwardMargin,sign] at hm ⊢
      linarith
    exact (negative_source_core_target_false ht.1 hs hm').elim

end SquaresInCircles.Eight.ShortMixedZero
end
end
end
