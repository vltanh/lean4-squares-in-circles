module

public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Words.Second.Outer.Same.ZeroPJDiagonalGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePositiveGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.One.UnitScalars
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameEvent

/-!
# Eight squares: the axial reference curve and its whole-interval derivatives

Every estimate
holds on the entire interval ending at the intrinsic diagonal event.
-/

section
/-!
## Literal data for the six original opposite primary owners

The row order is (edge 2, axis 2), (edge 2, axis 4), then the same two
axes on edges 4 and 6. Axis 2 is reflected and reversed exactly once;
the resulting source-primary separator has signs (-,+). No original
owner is reselected.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

abbrev Row := Fin 6
def c : Row→ℝ := ![6618/10000,6618/10000,-25931/100000,-25931/100000,-1866/10000,-1866/10000]
def p : Row→ℝ := ![-51554/100000,9133/100000,0,19335/100000,0,18602/100000]
def q : Row→ℝ := ![119909/100000,88074/100000,86884/100000,76744/100000,94766/100000,80996/100000]
def P : Row→ℝ := ![-9133/100000,51554/100000,-19335/100000,0,-18602/100000,0]
def t : Row→ℝ := ![88074/100000,119909/100000,76744/100000,86884/100000,80996/100000,94766/100000]
def threshold (r : Row) : ℝ := if r<2 then 359/400 else 17953/20000
def rho : ℝ := 1/(2*(outerAxial+1/2))
def width (x : ℝ) : ℝ := (1+Real.cos x+Real.sin x)/2
def cost (r : Row) (high : Bool) (a b A B x : ℝ) : ℝ :=
  Unit.angle high x+c r+p r*a-q r*b-P r*A-t r*B
def source (r : Row) (a : ℝ) : ℝ := p r*a-q r*arc a
def sourceD (r : Row) (a : ℝ) : ℝ := p r+q r*ratio a
def sourceDD (r : Row) (a : ℝ) : ℝ := q r*ratioD a
def target (r : Row) (B : ℝ) : ℝ := -P r*arc B-t r*B
def targetD (r : Row) (B : ℝ) : ℝ := P r*ratio B-t r

theorem coefficients (r : Row) :
    (76744/100000:ℝ)≤q r ∧ q r≤119909/100000 ∧
      (68355/100000:ℝ)≤p r+q r ∧
      -(19335/100000:ℝ)≤P r ∧ P r≤51554/100000 ∧ 0<t r ∧ P r<t r := by
  fin_cases r <;> norm_num [p,q,P,t]

theorem rho_bounds : (5223/20000:ℝ)<rho ∧ rho<131/500 := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hh : 0<2*(outerAxial+1/2) := by linarith [ha.1]
  constructor
  · apply (lt_div_iff₀ hh).2
    linarith [ha.2]
  · apply (div_lt_iff₀ hh).2
    linarith [ha.1]

theorem rho_identity : (outerAxial+1/2)*rho=1/2 := by
  have h : outerAxial+1/2≠0 := (by linarith [outer_endpoint_bounds.1] : (0:ℝ)<outerAxial+1/2).ne'
  rw [rho,mul_one_div,mul_comm 2,div_mul_eq_div_div,div_self h]

theorem ratio_zero : ratio 0=rho := by
  rw [ratio,SameContact.arc_zero,rho,zero_add,div_div]

theorem ratio_diagonal : ratio outerDiagonal=1 := by
  rw [ratio,SameContact.arc_diagonal]
  exact div_self (by linarith [outer_endpoint_bounds.2.2.1])

theorem target_ratio {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : rho≤ratio B ∧ ratio B≤1 := by
  have hlo := SameContact.ratio_monotone
    (show (0:ℝ)∈Icc 0 outerAxial from ⟨le_rfl,by linarith [outer_endpoint_bounds.1]⟩)
    (SameContact.outer_domain hB) hB.1
  rw [ratio_zero] at hlo
  have hs := SameContact.arc_state hB
  have hp := SameContact.shifted_positive (SameContact.outer_domain hB)
  exact ⟨hlo,(div_le_one hp).2 (by linarith [hs.2.1])⟩

theorem source_hasDerivAt (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (source r) (sourceD r a) a := by
  have hh := ((hasDerivAt_id' a).const_mul (p r)).fun_sub
    ((SameContact.arc_hasDerivAt (Same.primary_domain ha)).const_mul (q r))
  exact hh.congr_deriv (by simp only [sourceD]; ring)
theorem sourceD_hasDerivAt (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    HasDerivAt (sourceD r) (sourceDD r a) a :=
  ((SameContact.ratio_hasDerivAt (Same.primary_domain ha)).const_mul (q r)).const_add (p r)
theorem sourceD_lower (r : Row) {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) : p r+q r≤ sourceD r a := by
  have hh := mul_le_mul_of_nonneg_left (Same.primary_ratio_lower ha)
    (show 0≤q r by linarith [(coefficients r).1])
  dsimp [sourceD]
  linarith
theorem source_monotone (r : Row) : MonotoneOn (source r) (Icc outerDiagonal outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun a ha => (source_hasDerivAt r ha).continuousAt.continuousWithinAt)
    (fun a ha => source_hasDerivAt r (Ioo_subset_Icc_self ha))
    (fun a ha => by linarith [sourceD_lower r (Ioo_subset_Icc_self ha),(coefficients r).2.2.1])
theorem source_identity (r : Row) {a b : ℝ} (hs : OuterState a b) : source r a=p r*a-q r*b := by
  rw [source,(SameContact.actual_arc hs).2]

theorem target_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (target r) (targetD r B) B := by
  have hh := ((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).const_mul (-P r)).fun_sub
    ((hasDerivAt_id' B).const_mul (t r))
  exact hh.congr_deriv (by simp only [targetD]; ring)
theorem targetD_negative (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : targetD r B<0 := by
  have hrat := target_ratio hB
  have hpos : 0≤ratio B := by linarith [hrat.1,rho_bounds.1]
  by_cases hP : P r≤0
  · have hh := mul_nonpos_of_nonpos_of_nonneg hP hpos
    dsimp [targetD]
    linarith [(coefficients r).2.2.2.2.2.1]
  · have hh := mul_le_mul_of_nonneg_left hrat.2 (lt_of_not_ge hP).le
    dsimp [targetD]
    linarith [(coefficients r).2.2.2.2.2.2]
theorem target_antitone (r : Row) : AntitoneOn (target r) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (target_hasDerivAt r hB).continuousAt.continuousWithinAt)
    (fun _ hB => target_hasDerivAt r (Ioo_subset_Icc_self hB))
    (fun _ hB => (targetD_negative r (Ioo_subset_Icc_self hB)).le)

theorem normalized_margin (high : Bool) {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) 1 (Unit.angle high x)) :
    width x≤a+Unit.direction high*A*Real.sin x-B*Real.cos x := by
  have hw := quarter_width (x:=Unit.direction high*x)
    (by cases high <;> simpa [Unit.direction,abs_of_nonneg hx.1,abs_neg] using hx.2)
  have hs := (positive_trig hx).2.2.1
  cases high <;>
    norm_num [width,Unit.angle,Unit.direction,Eight.forwardMargin,Real.sin_add,Real.cos_add,
      Real.sin_neg,Real.cos_neg,abs_of_nonneg hs,abs_neg] at hm hw ⊢ <;> linarith

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary
end
end
end

section
/-!
## The coupled upper primary contact and its intrinsic lower end

The circle chart, its rotation and the unique axial/diagonal event (`exists_event`) are the
same-circle formulas. The source coordinate runs along its primary arc, and every original point
reduces by monotonicity to a physical contact with no larger cost (`original_to_contact`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

abbrev contact := SecondWord.SameZero.b
abbrev angleSpeed := SecondWord.SameZero.v
abbrev stateSpeed := SecondWord.SameZero.k
abbrev IsEvent := ShortOuterZero.Same.Event.IsEvent
abbrev T := SecondWord.SameZero.PJ.Diagonal.Y
abbrev z := SecondWord.SameZero.PJ.Diagonal.Z
abbrev z0 := SecondWord.SameZero.PJ.Diagonal.z₀
abbrev U := SecondWord.SameZero.PJ.Diagonal.horizontal
abbrev V := SecondWord.SameZero.PJ.Diagonal.vertical
abbrev diagonalB := SecondWord.SameZero.PJ.Diagonal.height
abbrev omega := SecondWord.SameZero.PJ.Diagonal.factor
abbrev omegaD := SecondWord.SameZero.PJ.Diagonal.factorD
abbrev diagonalSpeed := SecondWord.SameZero.PJ.Diagonal.speed
abbrev DiagonalDomain := SecondWord.SameZero.PJ.Diagonal.Domain

def Domain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ contact B x∈Icc outerDiagonal outerAxial
def value (r : Row) (B x : ℝ) : ℝ := Real.pi/2+x+c r+source r (contact B x)+target r B
def first (r : Row) (B x : ℝ) : ℝ := sourceD r (contact B x)*stateSpeed B x+P r*ratio B-t r
def second (r : Row) (B x : ℝ) : ℝ := sourceDD r (contact B x)*(stateSpeed B x)^2+
  ratioD B*(sourceD r (contact B x)*Real.sin x+P r)
def angleFirst (r : Row) (B x : ℝ) : ℝ := 1-sourceD r (contact B x)*angleSpeed B x

theorem zero_mem : (0:ℝ)∈Icc 0 outerDiagonal :=
  ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩
theorem diagonal_mem : outerDiagonal∈Icc 0 outerDiagonal :=
  ⟨zero_mem.2,le_rfl⟩
theorem diagonal_primary_mem : outerDiagonal∈Icc outerDiagonal outerAxial :=
  ⟨le_rfl,SameContact.diagonal_le_axial⟩

theorem stateSpeed_lower {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    Real.cos x≤ stateSpeed B x := by
  have hh := mul_nonneg (SameContact.ratio_pos (SameContact.outer_domain hB)).le
    (positive_trig hx).2.2.1
  dsimp [stateSpeed,SecondWord.SameZero.k]
  linarith

theorem contact_strictMono {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    StrictMonoOn (fun B => contact B x) (Icc 0 outerDiagonal) := by
  have hint : interior (Icc 0 outerDiagonal) = Ioo 0 outerDiagonal := interior_Icc
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 outerDiagonal)
    (f' := fun B => SecondWord.SameZero.k B x)
  · exact fun B hB => (SecondWord.SameZero.b_target_hasDerivAt hB x).continuousAt.continuousWithinAt
  · intro B hB
    rw [hint] at hB ⊢
    exact (SecondWord.SameZero.b_target_hasDerivAt (Ioo_subset_Icc_self hB) x).hasDerivWithinAt
  · intro B hB
    rw [hint] at hB
    exact SecondWord.SameZero.k_positive (Ioo_subset_Icc_self hB) hx

theorem target_diagonal_above {x : ℝ} (hx : x∈Icc 0 (7/10)) : outerDiagonal<contact outerDiagonal x := by
  have tr := positive_trig hx
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hfirst := mul_lt_mul''
    (show (1399/1000:ℝ)<outerDiagonal+1/2 by linarith) tr.1 (by norm_num) (by norm_num)
  have hsecond := mul_le_mul
    (show outerDiagonal-1/2≤(2/5:ℝ) by linarith) tr.2.2.2.1.le tr.2.2.1 (by norm_num)
  dsimp [contact,SecondWord.SameZero.b]
  rw [SameContact.arc_diagonal]
  linarith [hd.2]

theorem value_target_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun B => value r B x) (first r B x) B := by
  have h1 := (source_hasDerivAt r hd.2.2).comp B (SecondWord.SameZero.b_target_hasDerivAt hd.1 x)
  have h2 := (h1.const_add (Real.pi/2+x+c r)).fun_add (target_hasDerivAt r hd.1)
  convert h2 using 1
  · funext y
    dsimp only [value,Function.comp_apply]
  · dsimp only [first,targetD]
    ring

theorem first_target_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun B => first r B x) (second r B x) B := by
  have hk := ((SameContact.ratio_hasDerivAt (SameContact.outer_domain hd.1)).mul_const (Real.sin x)).const_add (Real.cos x)
  have hh := (((sourceD_hasDerivAt r hd.2.2).comp B
    (SecondWord.SameZero.b_target_hasDerivAt hd.1 x)).mul hk).add
      ((SameContact.ratio_hasDerivAt (SameContact.outer_domain hd.1)).const_mul (P r))
  convert hh.sub_const (t r) using 1 <;> dsimp [first,second,stateSpeed,SecondWord.SameZero.k]
  ring

theorem value_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (value r B) (angleFirst r B x) x := by
  have h1 : HasDerivAt (fun y => source r (contact B y))
      (sourceD r (contact B x)*(-SecondWord.SameZero.v B x)) x :=
    (source_hasDerivAt r hd.2.2).comp x (SecondWord.SameZero.b_angle_hasDerivAt B x)
  have h2 := (((hasDerivAt_id' x).const_add (Real.pi/2+c r)).fun_add h1).add_const (target r B)
  convert h2 using 1
  · funext y
    dsimp only [value]
    ring
  · dsimp only [angleFirst]
    ring

theorem between_domain {B D y x : ℝ} (hB : Domain B x) (hD : Domain D x) (hy : y∈Icc B D) :
    Domain y x := by
  have hy' : y∈Icc 0 outerDiagonal := ⟨hB.1.1.trans hy.1,hy.2.trans hD.1.2⟩
  have hlo := (contact_strictMono hB.2.1).monotoneOn hB.1 hy' hy.1
  have hhi := (contact_strictMono hB.2.1).monotoneOn hy' hD.1 hy.2
  exact ⟨hy',hB.2.1,⟨hB.2.2.1.trans hlo,hhi.trans hD.2.2.2⟩⟩

theorem event_bounds {e : ℝ} (he : IsEvent e) :
    (134/1250:ℝ)<e ∧ e<1073/10000 ∧ e∈Icc 0 (7/10) := by
  have hh := he.1
  norm_num [ShortOuterZero.Same.Event.lo,ShortOuterZero.Same.Event.hi] at hh
  exact ⟨by linarith [hh.1],by linarith [hh.2],ShortOuterZero.Same.Event.angle_mem he⟩
theorem exists_event : ∃e,IsEvent e := ShortOuterZero.Same.Event.exists_event

theorem before_domain {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) : Domain 0 x := by
  have hx' : x∈Icc 0 (7/10) := ⟨hx.1,hx.2.trans (event_bounds he).2.2.2⟩
  have hlo := SecondWord.SameZero.b_angle_antitone zero_mem hx' (event_bounds he).2.2 hx.2
  have he2 : SecondWord.SameZero.b 0 e=outerDiagonal := he.2
  rw [he2] at hlo
  have hhi := SecondWord.SameZero.b_angle_antitone zero_mem
    (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hx' hx.1
  have h00 : SecondWord.SameZero.b 0 0=1 := by norm_num [SecondWord.SameZero.b]
  rw [h00] at hhi
  exact ⟨zero_mem,hx',hlo,by linarith [outer_endpoint_bounds.1]⟩

theorem diagonal_at_event {e : ℝ} (he : IsEvent e) : DiagonalDomain e ∧ diagonalB e=0 := by
  have he2 : SecondWord.SameZero.b 0 e=outerDiagonal := he.2
  exact SecondWord.SameZero.PJ.Diagonal.original_coordinates
    (show SecondWord.SameZero.Domain 0 e from
      ⟨zero_mem,(event_bounds he).2.2,by rw [he2]; exact ⟨zero_mem.2,le_rfl⟩⟩) he2

theorem after_diagonal_domain {e x : ℝ} (he : IsEvent e) (hx : x∈Icc e (7/10)) : DiagonalDomain x := by
  have heD := diagonal_at_event he
  have hx' : x∈Icc SecondWord.SameZero.PJ.Diagonal.start (7/10) :=
    ⟨heD.1.1.1.trans hx.1,hx.2⟩
  have hm := SecondWord.SameZero.PJ.Diagonal.height_monotone heD.1.1 hx' hx.1
  have h0 : SecondWord.SameZero.PJ.Diagonal.height e=0 := heD.2
  rw [h0] at hm
  exact ⟨hx',hm⟩

theorem diagonal_target_arc {x : ℝ} (hx : DiagonalDomain x) : arc (diagonalB x)=U x-1/2 := by
  have hh := (SecondWord.SameZero.PJ.Diagonal.actual_coordinates hx).1
  dsimp [SecondWord.U] at hh
  linarith
theorem diagonal_contact_domain {x : ℝ} (hx : DiagonalDomain x) : Domain (diagonalB x) x := by
  refine ⟨SecondWord.SameZero.PJ.Diagonal.target_mem hx,
    SecondWord.SameZero.PJ.Diagonal.angle_mem hx.1,?_⟩
  have hc : contact (diagonalB x) x=outerDiagonal := SecondWord.SameZero.PJ.Diagonal.contact hx
  rw [hc]
  exact diagonal_primary_mem

theorem diagonal_lower_target {B x : ℝ} (hd : Domain B x) (hx : DiagonalDomain x) : diagonalB x≤B := by
  by_contra! hbad
  have hh := contact_strictMono hd.2.1 hd.1
    (SecondWord.SameZero.PJ.Diagonal.target_mem hx) hbad
  have hc : contact (diagonalB x) x=outerDiagonal := SecondWord.SameZero.PJ.Diagonal.contact hx
  simp only at hh
  rw [hc] at hh
  linarith [hd.2.2.1]

/-- The original coordinates move only along the contact; the source-diagonal slack portion ends
at its first circle contact. -/
theorem original_to_contact (r : Row) {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : width x≤a+A*Real.sin x-B*Real.cos x) :
    ∃D,Domain D x ∧ value r D x≤cost r true a b A B x := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have ha : a∈Icc outerDiagonal outerAxial := ⟨(outer_bounds hs).1,(outer_bounds hs).2.1⟩
  have hcontact : contact B x≤a := by
    dsimp [contact,SecondWord.SameZero.b,width] at *
    rw [(SameContact.actual_arc ht).1]
    linarith
  have he : cost r true a b A B x=Real.pi/2+x+c r+source r a+target r B := by
    rw [source_identity r hs,target,(SameContact.actual_arc ht).1]
    dsimp [cost,Unit.angle,Unit.direction]
    ring
  rw [he]
  by_cases hactive : outerDiagonal≤contact B x
  · have hd : Domain B x := ⟨hB,hx,hactive,hcontact.trans ha.2⟩
    refine ⟨B,hd,?_⟩
    have hh := source_monotone r hd.2.2 ha hcontact
    dsimp [value]
    linarith
  · have hc : Continuous (fun D => contact D x) := by
      dsimp [contact,SecondWord.SameZero.b,arc]; fun_prop
    obtain ⟨D,hD,hDe⟩ := intermediate_value_Icc hB.2 hc.continuousOn
      (show outerDiagonal∈Icc (contact B x) (contact outerDiagonal x) from
        ⟨(lt_of_not_ge hactive).le,(target_diagonal_above hx).le⟩)
    simp only at hDe
    have hD' : D∈Icc 0 outerDiagonal := ⟨hB.1.trans hD.1,hD.2⟩
    have hd : Domain D x := ⟨hD',hx,by rw [hDe]; exact diagonal_primary_mem⟩
    refine ⟨D,hd,?_⟩
    have hsource := source_monotone r diagonal_primary_mem ha ha.1
    have htarget := target_antitone r hB hD' hD.1
    dsimp [value]
    rw [hDe]
    linarith

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
end
end
end

section
/-!
## Uniform curvature of the six primary contacts

The source and target radicals are bounded on the coupled contact (`source_root_bounds`,
`target_root_bounds`), which gives a uniform curvature (`curvature`). The quadratic remainder is
kept for the two owners whose minimum can be in the interior of that contact
(`contact_remainder`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

def curvatureFloor : Row→ℝ := ![86/100,1,44/100,6/10,52/100,67/100]
def targetDenom (r : Row) : ℝ := if P r<0 then 1399/1000 else 383/200

theorem source_root_bounds {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    0<arc a+1/2 ∧ arc a+1/2<(7/5:ℝ) := by
  have hb := SameContact.primary_secondary_mem ha
  exact ⟨SameContact.shifted_positive (Same.primary_domain ha),
    by linarith [hb.2,ShortMixedZero.fine_diagonal_bounds.2]⟩

theorem target_root_bounds {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (1399/1000:ℝ)<arc B+1/2 ∧ arc B+1/2<(383/200:ℝ) := by
  have hb := outer_bounds (SameContact.arc_state hB)
  exact ⟨by linarith [hb.1,ShortMixedZero.fine_diagonal_bounds.1],
    by linarith [hb.2.1,ShortOuterZero.fine_axial_bounds.2]⟩

theorem source_ratioD_lower {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    Q0/(7/5:ℝ)^3≤ratioD a := by
  have hr := source_root_bounds ha
  have hp := pow_le_pow_left₀ hr.1.le hr.2.le 3
  dsimp [ratioD]
  apply (le_div_iff₀ (pow_pos hr.1 3)).2
  norm_num [Q0] at *
  nlinarith

theorem target_ratioD_bounds {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    Q0/(383/200:ℝ)^3≤ratioD B ∧ ratioD B≤Q0/(1399/1000:ℝ)^3 := by
  have hr := target_root_bounds hB
  have hp0 : 0<arc B+1/2 := by linarith
  have hlo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hr.1.le 3
  have hhi := pow_le_pow_left₀ hp0.le hr.2.le 3
  constructor
  · dsimp [ratioD]
    apply (le_div_iff₀ (pow_pos hp0 3)).2
    norm_num [Q0] at *
    nlinarith
  · dsimp [ratioD]
    apply (div_le_iff₀ (pow_pos hp0 3)).2
    norm_num [Q0] at *
    nlinarith

theorem signed_target_curvature (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    P r*Q0/(targetDenom r)^3≤P r*ratioD B := by
  have hr := target_ratioD_bounds hB
  by_cases hP : P r<0
  · have hh := mul_le_mul_of_nonpos_left hr.2 hP.le
    simpa [targetDenom,hP,mul_div_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_left hr.1 (le_of_not_gt hP)
    simpa [targetDenom,hP,mul_div_assoc] using hh

theorem curvature_of_cos (r : Row) {B x k : ℝ} (hd : Domain B x)
    (hk : 0<k) (hcos : k<Real.cos x) :
    q r*Q0*k^2/(7/5:ℝ)^3+P r*Q0/(targetDenom r)^3<second r B x := by
  have hq : 0<q r := by linarith [(coefficients r).1]
  have hL : 0<sourceD r (contact B x) := by
    linarith [sourceD_lower r hd.2.2,(coefficients r).2.2.1]
  have hk' : k<stateSpeed B x := hcos.trans_le (stateSpeed_lower hd.1 hd.2.1)
  have hsquare : k^2<(stateSpeed B x)^2 := by nlinarith
  have hr := source_ratioD_lower hd.2.2
  have hfirst := mul_lt_mul_of_pos_left hsquare
    (mul_pos hq (show 0<Q0/(7/5:ℝ)^3 by norm_num [Q0]))
  have hfirst' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr hq.le) (sq_nonneg (stateSpeed B x))
  have hsecond := signed_target_curvature r hd.1
  have hdrop := mul_nonneg
    (SameContact.ratioD_pos (SameContact.outer_domain hd.1)).le
    (mul_nonneg hL.le (positive_trig hd.2.1).2.2.1)
  have e1 : second r B x=q r*ratioD (contact B x)*(stateSpeed B x)^2+
      ratioD B*(sourceD r (contact B x)*Real.sin x)+P r*ratioD B := by
    dsimp only [second,sourceDD]
    ring
  have e2 : q r*Q0*k^2/(7/5:ℝ)^3=q r*(Q0/(7/5:ℝ)^3)*k^2 := by ring
  rw [e1,e2]
  linarith

theorem curvature_positive (r : Row) : 0<curvatureFloor r := by
  fin_cases r <;> norm_num [curvatureFloor]

theorem curvature (r : Row) {B x : ℝ} (hd : Domain B x) :
    curvatureFloor r<second r B x := by
  have hh := curvature_of_cos r hd (by norm_num : (0:ℝ)<191/250)
    (lt_trans (by norm_num) (positive_trig hd.2.1).1)
  fin_cases r <;> norm_num [curvatureFloor,targetDenom,p,q,P,Q0] at * <;> linarith

theorem early_cos {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (99417/100000:ℝ)<Real.cos x := by
  have hnum : (99417/100000:ℝ)<HighOrderTaylor.C14 (27/250) := by
    norm_num [HighOrderTaylor.C14,HighOrderTaylor.C12,cos10,cos8]
  have ht := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤27/250 by norm_num)
  have hm := cos_anti (before_domain he hx).2.1
    (by norm_num : (27/250:ℝ)∈Icc 0 (7/10))
    (show x≤27/250 by linarith [(event_bounds he).2.1,hx.2])
  exact hnum.trans_le (ht.trans hm)

theorem early_curvature_zero {B e x : ℝ} (he : IsEvent e) (hd : Domain B x)
    (hx : x≤e) : (39/25:ℝ)<second 0 B x := by
  have hh := curvature_of_cos 0 hd (by norm_num : (0:ℝ)<99417/100000)
    (early_cos he ⟨hd.2.1.1,hx⟩)
  norm_num [targetDenom,q,P,Q0] at hh
  linarith

theorem early_curvature_one {B e x : ℝ} (he : IsEvent e) (hd : Domain B x)
    (hx : x≤e) : (38/25:ℝ)<second 1 B x := by
  have hh := curvature_of_cos 1 hd (by norm_num : (0:ℝ)<99417/100000)
    (early_cos he ⟨hd.2.1.1,hx⟩)
  norm_num [targetDenom,q,P,Q0] at hh
  linarith

theorem contact_tangent (r : Row) {D B x κ : ℝ}
    (hD : Domain D x) (hB : Domain B x) (hDB : D≤B)
    (hκ : ∀E∈Icc D B,κ≤ second r E x) :
    value r D x+first r D x*(B-D)+κ/2*(B-D)^2≤value r B x := by
  exact CenteredMonomialBounds.second_derivative_tangent_lower
    (fun E hE => value_target_hasDerivAt r (between_domain hD hB hE))
    (fun E hE => first_target_hasDerivAt r (between_domain hD hB hE)) hκ
    (show D∈Icc D B from ⟨le_rfl,hDB⟩)
    (show B∈Icc D B from ⟨hDB,le_rfl⟩)

theorem endpoint_minimum (r : Row) {D B x : ℝ}
    (hD : Domain D x) (hB : Domain B x) (hDB : D≤B) (hfirst : 0≤first r D x) :
    value r D x≤value r B x := by
  have hh := contact_tangent r hD hB hDB
    (fun E hE => (curvature r (between_domain hD hB hE)).le)
  have hp := mul_nonneg hfirst (sub_nonneg.mpr hDB)
  have hq := mul_nonneg (div_nonneg (curvature_positive r).le (by norm_num : (0:ℝ)≤2))
    (sq_nonneg (B-D))
  linarith

theorem contact_remainder (r : Row) {D B x κ h : ℝ}
    (hD : Domain D x) (hB : Domain B x) (hDB : D≤B)
    (hκ0 : 0<κ) (_hh0 : 0≤h) (hfirst : -h≤first r D x)
    (hκ : ∀E∈Icc D B,κ≤ second r E x) :
    value r D x-h^2/(2*κ)≤value r B x := by
  have ht := contact_tangent r hD hB hDB hκ
  have hp := mul_le_mul_of_nonneg_right hfirst (sub_nonneg.mpr hDB)
  have hs := sq_nonneg (κ*(B-D)-h)
  have hdiv : h^2/(2*κ)*(2*κ)=h^2 := by
    field_simp [ne_of_gt hκ0]
  nlinarith

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)

def K (x : ℝ) : ℝ := contact 0 x+1/2
def v (x : ℝ) : ℝ := arc (contact 0 x)+1/2
def h (x : ℝ) : ℝ := angleSpeed 0 x
def projection (x : ℝ) : ℝ := Real.cos x+rho*Real.sin x
def projectionD (x : ℝ) : ℝ := -Real.sin x+rho*Real.cos x
def F (r : Row) (x : ℝ) : ℝ := value r 0 x
def F1 (r : Row) (x : ℝ) : ℝ := angleFirst r 0 x
def F2 (r : Row) (x : ℝ) : ℝ :=
  sourceDD r (contact 0 x)*(h x)^2-sourceD r (contact 0 x)*(K x-1)
def H (r : Row) (x : ℝ) : ℝ := first r 0 x
def H1 (r : Row) (x : ℝ) : ℝ :=
  -sourceDD r (contact 0 x)*h x*projection x+sourceD r (contact 0 x)*projectionD x

theorem K_formula (x : ℝ) : K x=1+Real.cos x/2-(outerAxial-1/2)*Real.sin x := by
  dsimp [K,contact,SecondWord.SameZero.b]
  rw [SameContact.arc_zero]
  ring
theorem v_formula (x : ℝ) : v x=Real.sqrt (Q0-(K x)^2) := by
  dsimp [v,K,arc]
  ring
theorem h_formula (x : ℝ) : h x=Real.sin x/2+(outerAxial-1/2)*Real.cos x := by
  dsimp [h,angleSpeed,SecondWord.SameZero.v]
  rw [SameContact.arc_zero]
  ring
theorem F_formula (r : Row) (x : ℝ) :
    F r x=Real.pi/2+x+c r+p r*(K x-1/2)-q r*(v x-1/2)-P r*outerAxial := by
  dsimp [F,value,source,target,K,v]
  rw [SameContact.arc_zero]
  ring
theorem F1_formula (r : Row) (x : ℝ) : F1 r x=1-(p r+q r*K x/v x)*h x := by
  dsimp [F1,angleFirst,sourceD,ratio,K,v,h]
  ring
theorem H_formula (r : Row) (x : ℝ) :
    H r x=(p r+q r*K x/v x)*projection x+P r*rho-t r := by
  dsimp [H,first,sourceD,stateSpeed,SecondWord.SameZero.k]
  rw [ratio_zero]
  dsimp [ratio,K,v,projection]
  ring

theorem h_hasDerivAt (x : ℝ) : HasDerivAt h (K x-1) x :=
  (SecondWord.SameZero.v_angle_hasDerivAt 0 x).congr_deriv (by simp only [K]; ring)
theorem projection_hasDerivAt (x : ℝ) : HasDerivAt projection (projectionD x) x :=
  (Real.hasDerivAt_cos x).fun_add ((Real.hasDerivAt_sin x).const_mul rho)
theorem F_hasDerivAt (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (F r) (F1 r x) x := value_angle_hasDerivAt r (before_domain he hx)
theorem F1_hasDerivAt (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (F1 r) (F2 r x) x := by
  have hh := (((sourceD_hasDerivAt r (before_domain he hx).2.2).comp x
    (SecondWord.SameZero.b_angle_hasDerivAt 0 x)).fun_mul (h_hasDerivAt x)).const_sub 1
  exact hh.congr_deriv (by simp only [F2,h,angleSpeed,contact,Function.comp_apply]; ring)
theorem H_hasDerivAt (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    HasDerivAt (H r) (H1 r x) x := by
  have hh := (((sourceD_hasDerivAt r (before_domain he hx).2.2).comp x
    (SecondWord.SameZero.b_angle_hasDerivAt 0 x)).mul (projection_hasDerivAt x)).add_const (P r*rho-t r)
  convert hh using 1
  · ext y
    dsimp [H,first,stateSpeed,SecondWord.SameZero.k,projection]
    rw [ratio_zero]
    ring
  · dsimp [H1,h]
    ring

theorem axial_primary_range {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    contact 0 x∈Icc outerDiagonal 1 := by
  have hd := before_domain he hx
  have hm := SecondWord.SameZero.b_angle_antitone zero_mem
    (by norm_num : (0:ℝ)∈Icc 0 (7/10)) hd.2.1 hx.1
  have h00 : SecondWord.SameZero.b 0 0=1 := by norm_num [SecondWord.SameZero.b]
  rw [h00] at hm
  exact ⟨hd.2.2.1,hm⟩

theorem axial_bounds {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (1399/1000:ℝ)<K x ∧ K x≤3/2 ∧ (129/100:ℝ)<v x ∧ v x<(7/5:ℝ) ∧
      (914575671/1000000000:ℝ)<h x ∧ h x<(121072/125000:ℝ) ∧
      0≤Real.sin x ∧ Real.sin x<(27/250:ℝ) := by
  have ha := axial_primary_range he hx
  have hv := Same.Positive.source_root ha
  have hs : Real.sin x<(27/250:ℝ) :=
    (Real.sin_le hx.1).trans_lt (by linarith [hx.2,(event_bounds he).2.1])
  have ht := positive_trig (before_domain he hx).2.1
  have hm : MonotoneOn h (Icc 0 e) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun y _ => (h_hasDerivAt y).continuousAt.continuousWithinAt)
      (fun y _ => h_hasDerivAt y)
    intro y hy
    have hh := (axial_primary_range he (Ioo_subset_Icc_self hy)).1
    dsimp [K]
    linarith [ShortMixedZero.fine_diagonal_bounds.1]
  have hlo := hm (show (0:ℝ)∈Icc 0 e from ⟨le_rfl,by linarith [(event_bounds he).1]⟩) hx hx.1
  rw [h_formula,h_formula] at hlo
  norm_num at hlo
  have hh := mul_le_mul_of_nonneg_left ht.2.1
    (show 0≤outerAxial-1/2 by linarith [ShortOuterZero.fine_axial_bounds.1])
  refine ⟨?_,?_,hv.1,hv.2,?_,?_,ht.2.2.1,hs⟩
  · dsimp [K]
    linarith [ha.1,ShortMixedZero.fine_diagonal_bounds.1]
  · dsimp [K]
    linarith [ha.2]
  · rw [h_formula]
    linarith [ShortOuterZero.fine_axial_bounds.1]
  · rw [h_formula]
    linarith [ShortOuterZero.fine_axial_bounds.2]

theorem projection_early {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    1≤projection x ∧ projection x<(128537/125000:ℝ) ∧
      (5223/20000)*(99417/100000)-27/250<projectionD x ∧ projectionD x<131/500 := by
  have hb := axial_bounds he hx
  have hc := early_cos he hx
  have ht := positive_trig (before_domain he hx).2.1
  have hlow := mul_lt_mul'' rho_bounds.1 hc (by norm_num) (by norm_num)
  have hhi := mul_le_mul_of_nonneg_left ht.2.1 (by linarith [rho_bounds.1] : 0≤rho)
  have hpd : (5223/20000)*(99417/100000)-27/250<projectionD x := by
    dsimp [projectionD]
    linarith [hb.2.2.2.2.2.2.2]
  have hm : MonotoneOn projection (Icc 0 e) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun y _ => (projection_hasDerivAt y).continuousAt.continuousWithinAt)
      (fun y _ => projection_hasDerivAt y)
    intro y hy
    have hc' := early_cos he (Ioo_subset_Icc_self hy)
    have hs' := (axial_bounds he (Ioo_subset_Icc_self hy)).2.2.2.2.2.2.2
    have hh := mul_le_mul rho_bounds.1.le hc'.le (by norm_num)
      (by linarith [rho_bounds.1] : 0≤rho)
    dsimp [projectionD]
    linarith
  have hmono := hm ⟨le_rfl,by linarith [(event_bounds he).1]⟩ hx hx.1
  norm_num [projection] at hmono
  have hprod := mul_lt_mul'' rho_bounds.2 hb.2.2.2.2.2.2.2
    (by linarith [rho_bounds.1]) hb.2.2.2.2.2.2.1
  refine ⟨hmono,?_,hpd,?_⟩
  · dsimp [projection]
    linarith [ht.2.1]
  · dsimp [projectionD]
    linarith [rho_bounds.2,hb.2.2.2.2.2.2.1]

theorem axial_sourceD_upper (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    sourceD r (contact 0 x)<p r+q r*(50/43:ℝ) := by
  have hb := axial_bounds he hx
  have hr : K x/v x<(50/43:ℝ) := by
    apply (div_lt_iff₀ (by linarith [hb.2.2.1] : 0<v x)).2
    linarith [hb.2.1]
  have hq : 0<q r := by linarith [(coefficients r).1]
  have hh := mul_lt_mul_of_pos_left hr hq
  dsimp [sourceD,ratio,K,v] at *
  linarith

theorem axial_curvature_bound (r : Row) {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    q r*Q0*(227/250:ℝ)^2/(7/5:ℝ)^3-(p r+q r*(50/43:ℝ))/2<F2 r x := by
  have hb := axial_bounds he hx
  have hq : 0<q r := by linarith [(coefficients r).1]
  have hD := source_ratioD_lower (before_domain he hx).2.2
  have hsquare : (227/250:ℝ)^2<(h x)^2 := by nlinarith [hb.2.2.2.2.1]
  have h1 := mul_lt_mul_of_pos_left hsquare
    (mul_pos hq (show 0<Q0/(7/5:ℝ)^3 by norm_num [Q0]))
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hD hq.le) (sq_nonneg (h x))
  have hL := axial_sourceD_upper r he hx
  have hL0 : 0≤ sourceD r (contact 0 x) := by
    linarith [sourceD_lower r (before_domain he hx).2.2,(coefficients r).2.2.1]
  have h3 := mul_le_mul hL.le (show K x-1≤(1/2:ℝ) by linarith [hb.2.1])
    (by linarith [hb.1] : 0≤K x-1) (by linarith)
  have e : q r*Q0*(227/250:ℝ)^2/(7/5:ℝ)^3=q r*(Q0/(7/5:ℝ)^3)*(227/250)^2 := by ring
  dsimp only [F2,sourceDD]
  rw [e]
  linarith only [h1,h2,h3]

theorem axial_curvature_pair (r : Row) (hr : r=3∨r=4) {e x : ℝ}
    (he : IsEvent e) (hx : x∈Icc 0 e) : (1/4:ℝ)<F2 r x := by
  have hh := axial_curvature_bound r he hx
  rcases hr with rfl | rfl <;> norm_num [p,q,Q0] at hh <;> linarith

theorem axial_curvature_one {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (47/100:ℝ)<F2 1 x := by
  have hh := axial_curvature_bound 1 he hx
  norm_num [p,q,Q0] at hh
  linarith

theorem axial_curvature_zero {e x : ℝ} (he : IsEvent e) (hx : x∈Icc 0 e) :
    (99/100:ℝ)<F2 0 x := by
  have hb := axial_bounds he hx
  have hD := source_ratioD_lower (before_domain he hx).2.2
  have hL : sourceD 0 (contact 0 x)<(879/1000:ℝ) := by
    have hh := axial_sourceD_upper 0 he hx
    norm_num [p,q] at hh
    linarith
  have hL0 : 0≤ sourceD 0 (contact 0 x) := by
    have hh := sourceD_lower 0 (before_domain he hx).2.2
    norm_num [p,q] at hh
    linarith
  have hsquare : (914575671/1000000000:ℝ)^2≤(h x)^2 := by nlinarith [hb.2.2.2.2.1]
  have h1 := mul_le_mul
    (mul_le_mul_of_nonneg_left hD (show 0≤q 0 by norm_num [q])) hsquare
    (by positivity) (mul_nonneg (by norm_num [q])
      (SameContact.ratioD_pos (Same.primary_domain (before_domain he hx).2.2)).le)
  have h2 := mul_le_mul hL.le (show K x-1≤(1/2:ℝ) by linarith [hb.2.1])
    (by linarith [hb.1] : 0≤K x-1) (by norm_num)
  dsimp [F2,sourceDD]
  norm_num [q,Q0] at *
  nlinarith

end SquaresInCircles.Eight.ShortOuterOne.Opposite.Primary.Upper
end
end
end
