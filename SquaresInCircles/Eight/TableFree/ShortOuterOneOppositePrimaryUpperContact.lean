module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneOppositePrimaryData
public import SquaresInCircles.Eight.TableFree.ShortOuterOneSamePositiveGeometry
public import SquaresInCircles.Eight.TableFree.SecondOuterSameZeroPJDiagonalGeometry

/-!
# The actual coupled upper primary contact and its intrinsic lower end

Uncompiled transcription of the common contact reduction in both upper
primary notes. The circle chart, its rotation, and the unique axial/
diagonal event are the already explicit same-circle formulas. The source
coordinate now runs along its primary arc, and every original point
reduces by monotonicity to a physical contact with no larger cost.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
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
  convert hh.sub_const (t r) using 1 <;> dsimp [first,second,stateSpeed,SecondWord.SameZero.k] <;> ring

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

/-- The original coordinates move only along the stipulated contact; the
source-diagonal slack portion ends at its first actual circle contact. -/
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

end SquaresInCircles.Eight.TableFree.ShortOuterOne.Opposite.Primary.Upper
