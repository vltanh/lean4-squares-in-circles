module

public import SquaresInCircles.Eight.Arithmetic.WholeIntervalPolynomial
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Owners.PowerTailBounds
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Stationary.System
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroLReferences
public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.ZeroAsymmetric
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterReferences
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveLowerPrimaryReference
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositePrimaryNegativeGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeSecondary
public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryNegativeFirst
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryNegativeLater
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryPositiveZero

/-!
# Eight squares: uniform curvature along the original lower secondary contact

Both positive circle contributions are kept. The constants `1.915` and `1.457` bound the roots
on every segment from the axial reference to a feasible original contact (`tangent`).
-/

section
/-!
## All positive halves of the three same-sign secondary owners

Compactness is applied to the whole contact strip (`contact_lower`). Its moving zero-source and
diagonal-target boundaries increase from alignment; an interior target minimum has a positive
angular derivative. A separate floor on the whole arc covers all later angles (`original`).
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Positive
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)

lemma diagonal_first_positive (r : Row) {x : ℝ} (hx : x∈Icc 0 strip) :
    0<first r outerDiagonal x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  have hd : Domain outerDiagonal x := ⟨hdiag,hx,(contact_target_diagonal hx).1.le⟩
  have hl := slope_bounds r (source_mem hd)
  have ht := strip_trig hx
  have hf := positive_trig (angle_full hx)
  have he : contactAngle outerDiagonal x=
      -(outerDiagonal-1/2)*(Real.cos x-Real.sin x) := by
    dsimp [contactAngle,D,SecondWord.U,SecondWord.W]
    rw [SameContact.arc_diagonal]
    ring
  have hmu0 : 0≤(outerDiagonal-1/2)*(Real.cos x-Real.sin x) :=
    mul_nonneg (by linarith [outer_endpoint_bounds.2.2.1]) (by linarith [ht.2.2.2])
  have hmu := mul_le_mul
    (show outerDiagonal-1/2≤(2/5:ℝ) by linarith [outer_endpoint_bounds.2.2.2])
    (show Real.cos x-Real.sin x≤1 by linarith [hf.2.1,ht.2.1])
    (by linarith [ht.2.2.2]) (by norm_num)
  have hprod := mul_le_mul hl.2.le hmu hmu0 (by norm_num : (0:ℝ)≤6/5)
  rw [first,he]
  nlinarith

lemma diagonal_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 strip) :
    (8981/10000:ℝ)<cost r outerDiagonal x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  have hdom : ∀y∈Icc 0 strip,Domain outerDiagonal y :=
    fun y hy => ⟨hdiag,hy,(contact_target_diagonal hy).1.le⟩
  have hm : MonotoneOn (cost r outerDiagonal) (Icc 0 strip) := monoOn_of_hasDeriv_nonneg
    (fun y hy => (cost_angle_hasDerivAt r (hdom y hy)).continuousAt.continuousWithinAt)
    (fun y hy => cost_angle_hasDerivAt r (hdom y (Ioo_subset_Icc_self hy)))
    (fun y hy => (diagonal_first_positive r (Ioo_subset_Icc_self hy)).le)
  have h0 : (0:ℝ)∈Icc 0 strip := by norm_num [strip]
  exact (initial_lower r (hdom 0 h0)).trans_le (hm h0 hx hx.1)

lemma interior_not_minimum (r : Row) {B x : ℝ} (hd : Domain B x)
    (hx : 0<x) (hB : B<outerDiagonal) (hb : 0<contact B x)
    (hmin : ∀C y,Domain C y→cost r B x≤cost r C y) : False := by
  let T : Set ℝ := Ioo 0 outerDiagonal ∩ (fun C => contact C x) ⁻¹' Ioi 0
  have hcontactT : Continuous (fun C => contact C x) := by dsimp [contact,arc]; fun_prop
  have hT : IsOpen T := isOpen_Ioo.inter (isOpen_Ioi.preimage hcontactT)
  have hmemT : B∈T := ⟨⟨target_positive hd,hB⟩,hb⟩
  have hlocalT : IsLocalMin (fun C => cost r C x) B := by
    filter_upwards [hT.mem_nhds hmemT] with C hC
    exact hmin C x ⟨Ioo_subset_Icc_self hC.1,hd.2.1,hC.2.le⟩
  have hstat : targetFirst r B x=0 :=
    hlocalT.hasDerivAt_eq_zero (cost_target_hasDerivAt r hd)
  have hfirst : (33/100:ℝ)<first r B x := by
    rw [stationary_first r hd hstat]
    exact transport_lower r hd.1 hd.2.1
  let O : Set ℝ := Ioi 0 ∩ (contact B) ⁻¹' Ioi 0
  have hcontactO : Continuous (contact B) := by
    show Continuous (fun y => 1/2+(1/2-arc B)*Real.cos y+(1/2-B)*Real.sin y); fun_prop
  have hO : IsOpen O := isOpen_Ioi.inter (isOpen_Ioi.preimage hcontactO)
  have hmemO : x∈O := ⟨hx,hb⟩
  obtain ⟨ε,hε,hsub⟩ := exists_closed_interval_in_open hO hmemO
  have hdom {y : ℝ} (hy : y∈Icc (x-ε) x) : Domain B y := by
    have hh := hsub (show y∈Icc (x-ε) (x+ε) from ⟨hy.1,by linarith [hy.2]⟩)
    exact ⟨hd.1,⟨hh.1.le,hy.2.trans hd.2.1.2⟩,hh.2.le⟩
  have hn := ContactMinimumDerivatives.right_endpoint (show x-ε<x by linarith)
    (first_continuousAt r hd) (fun y hy => cost_angle_hasDerivAt r (hdom hy))
    (fun y hy => hmin B y (hdom hy))
  linarith

lemma minimum_lower (r : Row) {B x : ℝ} (hd : Domain B x)
    (hmin : ∀C y,Domain C y→cost r B x≤cost r C y) :
    (8981/10000:ℝ)<cost r B x := by
  by_cases hx : x=0
  · subst x
    exact initial_lower r hd
  by_cases hb : contact B x=0
  · exact Zero.original_lower r hd hb
  by_cases hB : B=outerDiagonal
  · subst B
    exact diagonal_lower r hd.2.1
  exact (interior_not_minimum r hd (lt_of_le_of_ne hd.2.1.1 (Ne.symm hx))
    (lt_of_le_of_ne hd.1.2 hB) (lt_of_le_of_ne hd.2.2 (Ne.symm hb)) hmin).elim

theorem contact_lower (r : Row) {B x : ℝ} (hd : Domain B x) :
    (8981/10000:ℝ)<cost r B x := by
  let guard : ℝ×ℝ→ℝ := fun z => contact z.1 z.2
  let objective : ℝ×ℝ→ℝ := fun z => cost r z.1 z.2
  have hg : Continuous guard := by dsimp [guard,contact,arc]; fun_prop
  have hf : Continuous objective := by dsimp [objective,cost,target,targetCost,contact,arc]; fun_prop
  obtain ⟨z,hz,hbetter,hmin⟩ := contact_region_minimum hg hf
    (p₀ := (B,x)) ⟨hd.1,hd.2.1,hd.2.2⟩
  have hzd : Domain z.1 z.2 := ⟨hz.1,hz.2.1,hz.2.2⟩
  have hh := minimum_lower r hzd (fun C y hCy => hmin (C,y) hCy.1 hCy.2.1 hCy.2.2)
  exact hh.trans_le hbetter

lemma original_strip (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 strip)
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x) :
    (8981/10000:ℝ)<Real.pi/2+x+c r-P r*a+t r*b+p r*A-q r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hc : contact B x≤b := by
    dsimp [contact]
    rw [(SameContact.actual_arc ht).1]
    linarith
  have hcost : Real.pi/2+x+c r+target r b+targetCost r B=
      Real.pi/2+x+c r-P r*a+t r*b+p r*A-q r*B := by
    have hh := original_cost r hs ht
    linarith
  rw [←hcost]
  by_cases hactive : 0≤contact B x
  · have hd : Domain B x := ⟨hB,hx,hactive⟩
    have hsource := target_monotone r (source_mem hd) hb hc
    have hh := contact_lower r hd
    dsimp [cost] at hh
    linarith
  · have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
      ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
    have hcont : Continuous (fun D => contact D x) := by dsimp [contact,arc]; fun_prop
    obtain ⟨D,hD,he⟩ := intermediate_value_Icc hB.2 hcont.continuousOn
      (show (0:ℝ)∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨by linarith,(contact_target_diagonal hx).1.le⟩)
    have hDouter : D∈Icc 0 outerDiagonal := ⟨hB.1.trans hD.1,hD.2⟩
    have htarget := targetCost_antitone r hB hDouter hD.1
    have hsource := target_monotone r
      (show (0:ℝ)∈Icc 0 outerDiagonal from ⟨le_rfl,hdiag.1⟩) hb hb.1
    have hh := contact_lower r (show Domain D x from ⟨hDouter,hx,he.ge⟩)
    dsimp [cost] at hh
    rw [show contact D x=0 from he] at hh
    linarith

theorem original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x) :
    (449/500:ℝ)<Real.pi/2+x+c r-P r*a+t r*b+p r*A-q r*B := by
  by_cases hstrip : x≤ strip
  · linarith [original_strip r hs ht ⟨hx.1,hstrip⟩ hm]
  · have hh := independent_lower (x := x) r hs ht
    dsimp [strip] at hstrip
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Positive
end
end
end

section
/-!
## Both complete halves of the three same-sign secondary owners

The first two original owners are restored by the literal reflection
and reversal of the adjacent states. The third is already in the
normalized orientation. All original weak owner ties remain included.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry

theorem negative_original (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (449/500:ℝ)<Real.pi/2-x+c r-P r*a+t r*b+p r*A-q r*B := by
  by_cases hr : r=0
  · subst r
    exact Negative.FirstStrip.original hs ht hx hm
  · have hrows : r=1 ∨ r=2 := by fin_cases r <;> simp_all
    linarith [Negative.Later.original r hrows hs ht hx hm]

theorem normalized (r : Row) {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) :
    (449/500:ℝ)<φ+c r-P r*a+t r*b+p r*A-q r*B := by
  obtain ⟨high,x,hx,rfl⟩ := Unit.angle_cover hφ
  have hh := RoleFour.primary_margin high hx hm
  cases high
  · have hh' : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x := by
      simp only [Unit.direction,Bool.false_eq_true,↓reduceIte] at hh
      linarith
    have hv := negative_original r hs ht hx hh'
    simp only [Unit.angle,Unit.direction,Bool.false_eq_true,↓reduceIte]
    linarith
  · have hh' : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x+B*Real.sin x := by
      simp only [Unit.direction,↓reduceIte] at hh
      linarith
    have hv := Positive.original r hs ht hx hh'
    simp only [Unit.angle,Unit.direction,↓reduceIte]
    linarith

def OriginalOwner (i : Vertex) (σ : Bool) (j : Fin 4) : Prop :=
  ((i=2 ∨ i=4) ∧ σ=false ∧ j=2) ∨ (i=6 ∧ σ=true ∧ j=0)

theorem original_owner (i : Vertex) (σ : Bool) (j : Fin 4) (hrole : OriginalOwner i σ j)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10)
    (hm : 0≤Eight.forwardMargin j a b A B (WordProblems.sign σ) (WordProblems.sign σ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) .outer σ A B := by
  rcases hrole with ⟨hi,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · have hm' : 0≤Eight.forwardMargin 0 A B a b 1 1 φ := by
      simp [WordProblems.sign,Eight.forwardMargin] at hm ⊢
      linarith
    rcases hi with rfl | rfl
    · have hh := normalized 0 ht hs hφ hm'
      norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
        WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
      linarith
    · have hh := normalized 1 ht hs hφ hm'
      norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
        WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
      linarith
  · have hh := normalized 2 hs ht hφ (by simpa [WordProblems.sign] using hm)
    norm_num [wrongValue,WordProblems.shortCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,next,c,p,q,P,t] at *
    linarith

theorem actual_owner (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i)
    (_hw : F.word hgap pi_lt_22_over_7=WordProblems.wrongWord .short)
    (i : Vertex) (hi : F.word hgap pi_lt_22_over_7 i=1)
    (hs : C.kind i=.outer) (ht : C.kind (next i)=.outer)
    (hsg : positiveOf C i=positiveOf C (next i)) (j : Fin 4)
    (hrole : OriginalOwner i (positiveOf C i) j)
    (howner : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    WordProblems.wrongGamma .short i<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by
  have hφ : |phaseValue F hgap i-Real.pi/2|≤7/10 := by
    simpa [phaseValue,hi] using (difference_small F i).le
  have hm := original_margin C F hgap i j howner
  have hsource : OuterState (C.a i) (C.b i) := by
    simpa only [State,hs,↓reduceIte] using actual_state C i
  have htarget : OuterState (C.a (next i)) (C.b (next i)) := by
    simpa only [State,ht,↓reduceIte] using actual_state C (next i)
  have hh := original_owner i (positiveOf C i) j hrole
    hsource htarget hφ (by simpa [←hsg] using hm)
  have hh' : (449/500:ℝ)<phaseValue F hgap i+wrongMarker C .short i-
      wrongMarker C .short (next i) := by simpa only [wrongMarker,hs,ht,←hsg] using hh
  exact (ShortWord.Zero.threshold_le i).trans_lt hh'

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary
end
end
end

section
/-!
## The actual lower secondary contact and its forced angle interval

The source is moved monotonically to its original weak separator.
Its contact remains strictly below the diagonal. The original target
circle determines the positive radical and the unique rotated point.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
open CommonQuarter CorePairGeometry Arithmetic StationaryPrimitives
open ShortWord.MixedQuarter.Reference

def cap : ℝ := 571/1000
def feasibility (u : ℝ) : ℝ := (2*outerAxial-1)*Real.cos u-Real.sin u
def source (r : Bool) (b : ℝ) : ℝ := p r*SameContact.arc b-q r*b
def sourceD (r : Bool) (b : ℝ) : ℝ := -p r*SameContact.ratio b-q r
def contact (A B u : ℝ) : ℝ := A*Real.cos u-B*Real.sin u-width u
def Z (v u : ℝ) : ℝ := v+Real.cos u
def T (v u : ℝ) : ℝ := root (Z v u)
def cost (r : Bool) (v u : ℝ) : ℝ := Real.pi/2-u+cShift r+p r*root v-
  (q r+D r u)*v-D r u*Real.cos u-E r u*T v u
def first (r : Bool) (v u : ℝ) : ℝ := p r*rootD v-(q r+D r u)-E r u*rootD (Z v u)
def second (r : Bool) (v u : ℝ) : ℝ := p r*rootDD v-E r u*rootDD (Z v u)
def Domain (v u : ℝ) : Prop := u∈Icc 0 cap ∧ RootDomain v ∧ RootDomain (Z v u)

lemma small_angle {u : ℝ} (hu : u∈Icc 0 cap) : u∈Icc 0 (7/10) :=
  ⟨hu.1,hu.2.trans (by norm_num [cap])⟩

lemma feasible {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10))
    (hm : width u≤-b+A*Real.cos u-B*Real.sin u) : 1≤feasibility u := by
  have hb := outer_bounds hs
  have hB := outer_bounds ht
  have htr := positive_trig hu
  have hA := mul_le_mul_of_nonneg_right hB.2.1 (by linarith [htr.1] : 0≤Real.cos u)
  have hBs := mul_nonneg hB.2.2.1 htr.2.2.1
  dsimp [width] at hm
  dsimp [feasibility]
  nlinarith

lemma feasibility_hasDerivAt (u : ℝ) : HasDerivAt feasibility
    (-(2*outerAxial-1)*Real.sin u-Real.cos u) u := by
  have hh := ((Real.hasDerivAt_cos u).const_mul (2*outerAxial-1)).fun_sub (Real.hasDerivAt_sin u)
  exact hh.congr_deriv (by ring)

lemma feasibility_antitone : AntitoneOn feasibility (Icc 0 (7/10)) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (feasibility_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => feasibility_hasDerivAt u)
    (fun u hu => by
      have ht := positive_trig (Ioo_subset_Icc_self hu)
      have hp := mul_nonneg (show 0≤2*outerAxial-1 by linarith [outer_endpoint_bounds.1]) ht.2.2.1
      linarith [ht.1])

lemma cap_infeasible : feasibility cap<1 := by
  let V := (((ShortWord.MixedQuarter.Reference.axial.mul (Interval.point 2)).sub
    (Interval.point 1)).mul
    (ShortWord.MixedQuarter.Reference.cosine (by norm_num [cap] : (0:ℝ)≤cap))).sub
      (ShortWord.MixedQuarter.Reference.sine (by norm_num [cap] : (0:ℝ)≤cap))
  have hh : V.hi<1 := by dsimp [V,cap]; mixed_fixed
  have hv : feasibility cap≤V.hi := by
    have h2 := V.mem.2
    dsimp [feasibility]
    linarith
  exact hv.trans_lt hh

lemma forced_cap {u : ℝ} (hu : u∈Icc 0 (7/10)) (hf : 1≤feasibility u) : u<cap := by
  by_contra! hcap
  have hh := feasibility_antitone (by norm_num [cap] : cap∈Icc 0 (7/10)) hu hcap
  linarith [cap_infeasible]

lemma forced_half_cap {u : ℝ} (hu : u∈Icc 0 (7/10)) (hf : 1≤feasibility u) :
    half u<halfCap := by
  have hx := half_bounds hu
  have htr := half_trig hu
  have hd : 0<1+(half u)^2 := by positivity
  have he : feasibility u-1=
      (2*outerAxial*(1-(half u)^2)-2-2*half u)/(1+(half u)^2) := by
    dsimp [feasibility]
    rw [htr.1,htr.2]
    field_simp [hd.ne']
    ring
  have hn : 0≤2*outerAxial*(1-(half u)^2)-2-2*half u := by
    have h0 : 0≤(2*outerAxial*(1-(half u)^2)-2-2*half u)/(1+(half u)^2) := by
      rw [←he]
      linarith
    have h1 := mul_nonneg h0 hd.le
    rwa [div_mul_cancel₀ _ hd.ne'] at h1
  by_contra! hcap
  have hx2 : (halfCap)^2≤(half u)^2 := by
    have hp := mul_nonneg (show 0≤half u-halfCap by linarith) (show 0≤half u+halfCap by dsimp [halfCap]; linarith)
    nlinarith only [hp]
  have hfactor : 0≤2*(1-(half u)^2) := by nlinarith [hx.1,hx.2]
  have ha := mul_le_mul_of_nonneg_right ShortOuterZero.fine_axial_bounds.2.le hfactor
  dsimp [halfCap] at *
  nlinarith only [hn,ha,hx2,hcap]

lemma cap_trig : (21/25:ℝ)<Real.cos cap ∧ (27/50:ℝ)<Real.sin cap := by
  have hc : (21/25:ℝ)<(ShortWord.MixedQuarter.Reference.cosine
      (by norm_num [cap] : (0:ℝ)≤cap)).lo := by dsimp [cap]; mixed_fixed
  have hs : (27/50:ℝ)<(ShortWord.MixedQuarter.Reference.sine
      (by norm_num [cap] : (0:ℝ)≤cap)).lo := by dsimp [cap]; mixed_fixed
  exact ⟨hc.trans_le (ShortWord.MixedQuarter.Reference.cosine (by norm_num [cap])).mem.1,
    hs.trans_le (ShortWord.MixedQuarter.Reference.sine (by norm_num [cap])).mem.1⟩

lemma small_trig {u : ℝ} (hu : u∈Icc 0 cap) :
    (21/25:ℝ)<Real.cos u ∧ Real.cos u≤1 ∧ 0≤Real.sin u ∧ Real.sin u<13/20 := by
  have ht := positive_trig (small_angle hu)
  have hk := cos_anti (small_angle hu) (by norm_num [cap] : cap∈Icc 0 (7/10)) hu.2
  exact ⟨cap_trig.1.trans_le hk,ht.2.1,ht.2.2.1,by linarith [ht.2.2.2.1]⟩

lemma E_hasDerivAt (r : Bool) (u : ℝ) : HasDerivAt (E r) (D r u) u := by
  have hh := ((Real.hasDerivAt_sin u).const_mul (P r)).fun_add
    ((Real.hasDerivAt_cos u).const_mul (t r))
  exact hh.congr_deriv (by simp only [D]; ring)
lemma D_hasDerivAt (r : Bool) (u : ℝ) : HasDerivAt (D r) (-E r u) u := by
  have hh := ((Real.hasDerivAt_cos u).const_mul (P r)).fun_sub
    ((Real.hasDerivAt_sin u).const_mul (t r))
  exact hh.congr_deriv (by simp only [E]; ring)

lemma E_lower (r : Bool) {u : ℝ} (hu : u∈Icc 0 cap) : (81/100:ℝ)<E r u := by
  have hc : ConcaveOn ℝ (Icc 0 cap) (E r) := concave_of_deriv2
    (fun x _ => E_hasDerivAt r x) (fun x _ => D_hasDerivAt r x)
    (fun x hx => by linarith [E_positive r (small_angle hx)])
  apply concave_gt_of_endpoints hc hu
  · cases r <;> norm_num [E,P,t,PQ,tQ]
  · have hs := mul_lt_mul_of_pos_left cap_trig.2
      (show 0<P r by linarith [(coefficient_bounds r).2.2.2.2.1])
    have hk := mul_lt_mul_of_pos_left cap_trig.1
      (show 0<t r by linarith [(coefficient_bounds r).2.2.2.2.2.2.1])
    cases r <;> norm_num [E,P,t,PQ,tQ] at hs hk ⊢ <;> linarith

lemma source_hasDerivAt (r : Bool) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (source r) (sourceD r b) b := by
  have hh := ((SameContact.arc_hasDerivAt (SameContact.outer_domain hb)).const_mul (p r)).fun_sub
    ((hasDerivAt_id' b).const_mul (q r))
  exact hh.congr_deriv (by simp only [sourceD]; ring)
lemma sourceD_negative (r : Bool) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : sourceD r b<0 := by
  have hratio := SecondWord.outer_ratio_bounds hb
  have hh := mul_le_mul_of_nonneg_left hratio.2.1
    (show 0≤-p r by linarith [(coefficient_bounds r).2.1])
  have hcoeff := coefficient_bounds r
  dsimp [sourceD]
  linarith
lemma source_antitone (r : Bool) : AntitoneOn (source r) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hb => (source_hasDerivAt r hb).continuousAt.continuousWithinAt)
    (fun _ hb => source_hasDerivAt r (Ioo_subset_Icc_self hb))
    (fun _ hb => (sourceD_negative r (Ioo_subset_Icc_self hb)).le)

lemma contact_bounds {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    b≤contact A B u ∧ contact A B u∈Icc 0 outerDiagonal := by
  have hb := outer_bounds hs
  have hB := outer_bounds ht
  have htr := positive_trig hu
  have hAs := mul_le_mul_of_nonneg_left htr.2.1 (show 0≤A by linarith [hB.1,outer_endpoint_bounds.2.2.1])
  have hBs := mul_nonneg hB.2.2.1 htr.2.2.1
  have hmax : contact A B u≤outerAxial-1 := by
    dsimp [contact]
    linarith [width_ge_one hu,hB.2.1]
  have hbc : b≤contact A B u := by dsimp [contact]; linarith
  exact ⟨hbc,⟨hb.2.2.1.trans hbc,by linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.1,
    ShortOuterZero.fine_axial_bounds.2]⟩⟩

lemma contact_domain {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    Domain (contact A B u+1/2) u := by
  have hb := (contact_bounds hs ht hu hm).2
  have hB := outer_bounds ht
  have htr := positive_trig hu
  have hv : RootDomain (contact A B u+1/2) := by
    apply root_domain_iff.2
    simpa using SameContact.outer_domain hb
  have he : Z (contact A B u+1/2) u=
      (A+1/2)*Real.cos u-(B+1/2)*Real.sin u := by dsimp [Z,contact,width]; ring
  have hAk := mul_le_mul_of_nonneg_left htr.2.1
    (show 0≤A+1/2 by linarith [hB.1,outer_endpoint_bounds.2.2.1])
  have hBs := mul_nonneg (show 0≤B+1/2 by linarith [hB.2.2.1]) htr.2.2.1
  have hz : RootDomain (Z (contact A B u+1/2) u) := by
    constructor
    · dsimp [Z]
      linarith [hv.1,htr.1]
    · rw [he,X0_eq]
      linarith [hB.2.1]
  exact ⟨⟨hu.1,(forced_cap hu (feasible hs ht hu hm)).le⟩,hv,hz⟩

lemma interval_domain {v u w : ℝ} (hd : Domain v u) (hw : w∈Icc (1/2) v) : Domain w u := by
  refine ⟨hd.1,⟨hw.1,hw.2.trans hd.2.1.2⟩,?_⟩
  have ht := small_trig hd.1
  have hZ : Z v u≤X0 := hd.2.2.2
  constructor
  · dsimp [Z]
    linarith [hw.1,ht.1]
  · dsimp [Z] at hZ ⊢
    linarith [hw.2]

lemma contact_target_radical {a b A B u : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    T (contact A B u+1/2) u=(A+1/2)*Real.sin u+(B+1/2)*Real.cos u := by
  have hd := contact_domain hs ht hu hm
  have hB := outer_bounds ht
  have htr := positive_trig hu
  have he : Z (contact A B u+1/2) u=
      (A+1/2)*Real.cos u-(B+1/2)*Real.sin u := by dsimp [Z,contact,width]; ring
  have hp : 0<(A+1/2)*Real.sin u+(B+1/2)*Real.cos u := by
    have h1 := mul_nonneg (show 0≤A+1/2 by linarith [hB.1,outer_endpoint_bounds.2.2.1]) htr.2.2.1
    have h2 := mul_pos (show 0<B+1/2 by linarith [hB.2.2.1]) (show 0<Real.cos u by linarith [htr.1])
    linarith
  have heq : ((A+1/2)*Real.sin u+(B+1/2)*Real.cos u)^2=
      Q0-(Z (contact A B u+1/2) u)^2 := by
    rw [he]
    linear_combination ht.2.2+((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq u)
  have hroot := root_sq hd.2.2
  have hroot0 := root_positive hd.2.2
  change (root (Z (contact A B u+1/2) u))^2=_ at hroot
  dsimp [T]
  nlinarith

lemma contact_identity {a b A B u : ℝ} (r : Bool) (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    cost r (contact A B u+1/2) u=
      Real.pi/2-u+c+source r (contact A B u)-P r*A-t r*B := by
  have hT := contact_target_radical hs ht hu hm
  have hroot : root (contact A B u+1/2)=SameContact.arc (contact A B u)+1/2 := by
    rw [root_eq_arc]
    congr 2
    ring
  have he : Z (contact A B u+1/2) u=(A+1/2)*Real.cos u-(B+1/2)*Real.sin u := by
    dsimp [Z,contact,width]
    ring
  have hcircle := Real.sin_sq_add_cos_sq u
  dsimp [cost]
  rw [hT,hroot]
  dsimp [cShift,source,D,E]
  dsimp [Z] at he
  linear_combination (-P r*Real.cos u+t r*Real.sin u)*he-
    (P r*(A+1/2)+t r*(B+1/2))*hcircle

lemma original_to_contact {a b A B u : ℝ} (r : Bool) (hs : OuterState a b) (ht : OuterState A B)
    (hu : u∈Icc 0 (7/10)) (hm : width u≤-b+A*Real.cos u-B*Real.sin u) :
    cost r (contact A B u+1/2) u≤Real.pi/2-u+c+p r*a-q r*b-P r*A-t r*B := by
  have hb := contact_bounds hs ht hu hm
  have hsrc := source_antitone r ⟨(outer_bounds hs).2.2.1,(outer_bounds hs).2.2.2.1⟩ hb.2 hb.1
  rw [contact_identity r hs ht hu hm]
  dsimp only [source] at hsrc ⊢
  rw [(SameContact.actual_arc hs).1] at hsrc
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
open CommonQuarter CorePairGeometry Arithmetic

lemma cost_hasDerivAt (r : Bool) {v u : ℝ} (hd : Domain v u) :
    HasDerivAt (fun w => cost r w u) (first r v u) v := by
  have hT0 := (root_hasDerivAt hd.2.2).comp v ((hasDerivAt_id' v).add_const (Real.cos u))
  have hT : HasDerivAt (fun w => root (w+Real.cos u)) (rootD (Z v u)*1) v := hT0
  have hh := (((((root_hasDerivAt hd.2.1).const_mul (p r)).const_add
    (Real.pi/2-u+cShift r)).fun_sub ((hasDerivAt_id' v).const_mul (q r+D r u))).sub_const
      (D r u*Real.cos u)).fun_sub (hT.const_mul (E r u))
  exact hh.congr_deriv (by simp only [first]; ring)

lemma first_hasDerivAt (r : Bool) {v u : ℝ} (hd : Domain v u) :
    HasDerivAt (fun w => first r w u) (second r v u) v := by
  have hT0 := (rootD_hasDerivAt hd.2.2).comp v ((hasDerivAt_id' v).add_const (Real.cos u))
  have hT : HasDerivAt (fun w => rootD (w+Real.cos u)) (rootDD (Z v u)*1) v := hT0
  have hh := (((rootD_hasDerivAt hd.2.1).const_mul (p r)).sub_const (q r+D r u)).fun_sub
    (hT.const_mul (E r u))
  exact hh.congr_deriv (by simp only [second]; ring)

lemma second_formula (r : Bool) (v u : ℝ) : second r v u=
    (-p r)*Q0/(root v)^3+E r u*Q0/(T v u)^3 := by
  dsimp [second,rootDD,T]
  ring

lemma roots_upper {v u : ℝ} (hd : Domain v u) :
    root v<(383/200:ℝ) ∧ T v u<(1457/1000:ℝ) := by
  have hs : root v<(383/200:ℝ) := (root_le_X0 hd.2.1).trans_lt (by linarith [X0_bounds.2])
  have hz : (67/50:ℝ)<Z v u := by dsimp [Z]; linarith [hd.2.1.1,(small_trig hd.1).1]
  have ht := root_sq hd.2.2
  have hp := root_positive hd.2.2
  have ht' : T v u<(1457/1000:ℝ) := by
    dsimp [T]
    norm_num [Q0] at ht
    nlinarith
  exact ⟨hs,ht'⟩

lemma second_lower (r : Bool) {v u : ℝ} (hd : Domain v u) : (57/50:ℝ)<second r v u := by
  have hS := root_positive hd.2.1
  have hT := root_positive hd.2.2
  have hS3 : 0<(root v)^3 := pow_pos hS _
  have hT3 : 0<(T v u)^3 := pow_pos hT _
  have hSmax : (root v)^3<(383/200:ℝ)^3 := by
    gcongr
    exact (roots_upper hd).1
  have hTmax : (T v u)^3<(1457/1000:ℝ)^3 := by
    gcongr
    exact (roots_upper hd).2
  have hp : (20967/100000:ℝ)≤-p r := by linarith [(coefficient_bounds r).2.1]
  have hE := E_lower r hd.1
  have hsrc : ((20967/100000:ℝ)*Q0)/(383/200:ℝ)^3<(-p r)*Q0/(root v)^3 := by
    apply (lt_div_iff₀ hS3).2
    have hnum := mul_le_mul_of_nonneg_right hp (by norm_num [Q0] : 0≤Q0)
    norm_num [Q0] at hSmax hnum ⊢
    nlinarith
  have htgt : ((81/100:ℝ)*Q0)/(1457/1000:ℝ)^3<E r u*Q0/(T v u)^3 := by
    apply (lt_div_iff₀ hT3).2
    have hnum := mul_lt_mul_of_pos_right hE (by norm_num [Q0] : 0<Q0)
    norm_num [Q0] at hTmax hnum ⊢
    nlinarith
  rw [second_formula]
  norm_num [Q0] at hsrc htgt ⊢
  linarith

lemma axial_identity (r : Bool) (u : ℝ) : cost r (1/2) u=axial r u := by
  dsimp [cost,T,Z]
  rw [root_half,X0_eq]
  dsimp [axial,cShift,axialZ,axialT]
  ring

theorem tangent (r : Bool) {v u : ℝ} (hd : Domain v u) :
    axial r u+first r (1/2) u*(v-1/2)+(57/100:ℝ)*(v-1/2)^2≤cost r v u := by
  have hh := CenteredMonomialBounds.second_derivative_tangent_lower
    (f:=fun w => cost r w u) (df:=fun w => first r w u) (ddf:=fun w => second r w u)
    (l:=1/2) (h:=v) (x₀:=1/2) (x:=v) (κ:=57/50)
    (fun w hw => cost_hasDerivAt r (interval_domain hd hw))
    (fun w hw => first_hasDerivAt r (interval_domain hd hw))
    (fun w hw => (second_lower r (interval_domain hd hw)).le)
    (left_mem_Icc.2 hd.2.1.1) (right_mem_Icc.2 hd.2.1.1)
  have h0 : cost r (1/2) u+first r (1/2) u*(v-1/2)+(57/50)/2*(v-1/2)^2≤cost r v u := hh
  rw [axial_identity] at h0
  linarith

end SquaresInCircles.Eight.ShortOuterOne.OppositeFive.LowerSecondary
end
end
end
