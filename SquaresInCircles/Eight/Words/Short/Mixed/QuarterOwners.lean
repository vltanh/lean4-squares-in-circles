module

public import SquaresInCircles.Eight.Words.Second.Outer.Opposite.TwoCycle
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterCore
public import SquaresInCircles.Eight.Words.Short.Mixed.QuarterOuter

/-!
# Eight squares: all ninety-six original mixed quarter owners

Only edge indices, signs, radial orders and the four original owners are split
(`original_core_source`, `original_outer_source`, `original`). The target owners are the exact
reflection and reversal of the two source owners (`reverse_margin`). The original angle and the
signed role cost are kept, including both closed core pieces.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortWord.MixedQuarter
open CommonQuarter CorePairGeometry Arithmetic QuarterWordGeometry WordProblems

def directRow (i : Vertex) (σ τ : Bool) : Row :=
  if i=2 then (if τ then 2 else 0)
  else if i=4 then (if σ then (if τ then 10 else 8) else (if τ then 6 else 4))
  else if i=5 then (if σ then (if τ then 18 else 16) else (if τ then 14 else 12))
  else if σ then 22 else 20
def reverseRow (i : Vertex) (σ τ : Bool) : Row := directRow i σ τ+1

theorem direct_data (i : Vertex) (σ τ : Bool) (hq : wrongWord .short i=1)
    (ha : allowed .short i σ τ) :
    reversed (directRow i σ τ)=false ∧ edge (directRow i σ τ)=i ∧
      sourcePositive (directRow i σ τ)=σ ∧ targetPositive (directRow i σ τ)=τ := by
  fin_cases i <;> cases σ <;> cases τ <;>
    simp [wrongWord,allowed,next,directRow,reversed,edge,sourcePositive,targetPositive] at hq ha ⊢
theorem reverse_data (i : Vertex) (σ τ : Bool) (hq : wrongWord .short i=1)
    (ha : allowed .short i σ τ) :
    reversed (reverseRow i σ τ)=true ∧ edge (reverseRow i σ τ)=i ∧
      sourcePositive (reverseRow i σ τ)=(!τ) ∧ targetPositive (reverseRow i σ τ)=(!σ) := by
  fin_cases i <;> cases σ <;> cases τ <;>
    simp [wrongWord,allowed,next,reverseRow,directRow,reversed,edge,sourcePositive,targetPositive] at hq ha ⊢

theorem angle_cover {φ : ℝ} (hφ : |φ-Real.pi/2|≤7/10) :
    ∃upper x,x∈Icc 0 (7/10) ∧ φ=angle upper x := by
  have hb := abs_le.mp hφ
  by_cases h : φ≤Real.pi/2
  · refine ⟨false,Real.pi/2-φ,⟨by linarith,by linarith [hb.1]⟩,?_⟩
    dsimp [angle,direction]; ring
  · refine ⟨true,φ-Real.pi/2,⟨by linarith,by linarith [hb.2]⟩,?_⟩
    dsimp [angle,direction]; ring

theorem core_source_owner (r : Row) {a b A B φ : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (j : Fin 4) (hj : j=0∨j=3)
    (hm : 0≤Eight.forwardMargin j a b A B (sourceSign r) (targetSign r) φ) :
    (449/500:ℝ)<coreOuterCost r a b A B φ := by
  obtain ⟨upper,x,hx,rfl⟩ := angle_cover hφ
  rcases hj with rfl|rfl
  · apply core_secondary r upper hs ht hx
    dsimp [sourceSecondary]
    simpa [Eight.forwardMargin,sub_nonneg] using hm
  · apply core_primary r upper hs ht hx
    dsimp [sourcePrimary]
    simpa [Eight.forwardMargin,sub_nonneg] using hm
theorem outer_source_owner (r : Row) {a b A B φ : ℝ}
    (hs : OuterState a b) (ht : CoreState A B) (hφ : |φ-Real.pi/2|≤7/10)
    (j : Fin 4) (hj : j=0∨j=3)
    (hm : 0≤Eight.forwardMargin j a b A B (sourceSign r) (targetSign r) φ) :
    (449/500:ℝ)<outerCoreCost r a b A B φ := by
  obtain ⟨upper,x,hx,rfl⟩ := angle_cover hφ
  rcases hj with rfl|rfl
  · apply outer_secondary r upper hs ht hx
    dsimp [sourceSecondary]
    simpa [Eight.forwardMargin,sub_nonneg] using hm
  · apply outer_primary r upper hs ht hx
    dsimp [sourcePrimary]
    simpa [Eight.forwardMargin,sub_nonneg] using hm

theorem sign_not (σ : Bool) : (sign (!σ):ℝ)= -(sign σ:ℝ) := by cases σ <;> norm_num [sign]
theorem reverse_margin (j : Fin 4) (a b A B φ : ℝ) (σ τ : Bool) :
    Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b (sign (!τ)) (sign (!σ)) φ=
      Eight.forwardMargin j a b A B (sign σ) (sign τ) φ := by
  rw [sign_not,sign_not]
  exact SecondWord.margin_reflection j a b A B (sign σ) (sign τ) φ

theorem original_core_source (i : Vertex) (σ τ : Bool) (core : RadialKind) (hcore : core≠.outer)
    (hq : wrongWord .short i=1) (ha : allowed .short i σ τ)
    {a b A B φ : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i core σ a b-
      wrongValue .short (next i) .outer τ A B := by
  by_cases hj : j=0∨j=3
  · let r := directRow i σ τ
    have hd := direct_data i σ τ hq ha
    have hm' : 0≤Eight.forwardMargin j a b A B (sourceSign r) (targetSign r) φ := by
      simpa [r,sourceSign,targetSign,hd.2.2.1,hd.2.2.2] using hm
    have hh := core_source_owner r hs ht hφ j hj hm'
    rw [coreOuter_literal r core hcore] at hh
    simpa [r,literalCoreOuter,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2] using hh
  · let r := reverseRow i σ τ
    have hd := reverse_data i σ τ hq ha
    have hj' : SecondWord.reflectedOwner j=0∨SecondWord.reflectedOwner j=3 := by
      fin_cases j <;> simp [SecondWord.reflectedOwner] at hj ⊢
    have hm' : 0≤Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b
        (sourceSign r) (targetSign r) φ := by
      have hh : 0≤Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b (sign (!τ)) (sign (!σ)) φ := by
        rw [reverse_margin]; exact hm
      simpa [r,sourceSign,targetSign,hd.2.2.1,hd.2.2.2] using hh
    have hh := outer_source_owner r ht hs hφ (SecondWord.reflectedOwner j) hj' hm'
    rw [outerCore_literal r core hcore] at hh
    simpa [r,literalOuterCore,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2] using hh

theorem original_outer_source (i : Vertex) (σ τ : Bool) (core : RadialKind) (hcore : core≠.outer)
    (hq : wrongWord .short i=1) (ha : allowed .short i σ τ)
    {a b A B φ : ℝ} (hs : OuterState a b) (ht : CoreState A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i .outer σ a b-
      wrongValue .short (next i) core τ A B := by
  by_cases hj : j=0∨j=3
  · let r := directRow i σ τ
    have hd := direct_data i σ τ hq ha
    have hm' : 0≤Eight.forwardMargin j a b A B (sourceSign r) (targetSign r) φ := by
      simpa [r,sourceSign,targetSign,hd.2.2.1,hd.2.2.2] using hm
    have hh := outer_source_owner r hs ht hφ j hj hm'
    rw [outerCore_literal r core hcore] at hh
    simpa [r,literalOuterCore,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2] using hh
  · let r := reverseRow i σ τ
    have hd := reverse_data i σ τ hq ha
    have hj' : SecondWord.reflectedOwner j=0∨SecondWord.reflectedOwner j=3 := by
      fin_cases j <;> simp [SecondWord.reflectedOwner] at hj ⊢
    have hm' : 0≤Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b
        (sourceSign r) (targetSign r) φ := by
      have hh : 0≤Eight.forwardMargin (SecondWord.reflectedOwner j) A B a b (sign (!τ)) (sign (!σ)) φ := by
        rw [reverse_margin]; exact hm
      simpa [r,sourceSign,targetSign,hd.2.2.1,hd.2.2.2] using hh
    have hh := core_source_owner r ht hs hφ (SecondWord.reflectedOwner j) hj' hm'
    rw [coreOuter_literal r core hcore] at hh
    simpa [r,literalCoreOuter,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2] using hh

def Mixed (source target : RadialKind) : Prop :=
  (source=.outer∧target≠.outer)∨(source≠.outer∧target=.outer)

theorem original {i : Vertex} {source target : RadialKind} {σ τ : Bool}
    (hq : wrongWord .short i=1) (ha : allowed .short i σ τ) (hmixed : Mixed source target)
    {a b A B φ : ℝ} (hs : State source a b) (ht : State target A B)
    (hφ : |φ-Real.pi/2|≤7/10) (j : Fin 4)
    (hm : 0≤Eight.forwardMargin j a b A B (sign σ) (sign τ) φ) :
    (449/500:ℝ)<φ+wrongValue .short i source σ a b-
      wrongValue .short (next i) target τ A B := by
  rcases hmixed with ⟨rfl,hcore⟩|⟨hcore,rfl⟩
  · exact original_outer_source i σ τ target hcore hq ha
      (by simpa [State] using hs) (by simpa [State,hcore] using ht) hφ j hm
  · exact original_core_source i σ τ source hcore hq ha
      (by simpa [State,hcore] using hs) (by simpa [State] using ht) hφ j hm

end SquaresInCircles.Eight.ShortWord.MixedQuarter
