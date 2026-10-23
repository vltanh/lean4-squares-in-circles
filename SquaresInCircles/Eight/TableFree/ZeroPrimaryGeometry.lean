module

public import SquaresInCircles.Eight.TableFree.CommonZero
public import SquaresInCircles.Eight.TableFree.FrameCoreArc

/-!
# What an original zero-quarter primary owner forces

The original physical gap and weak primary inequality force a positive
source tangent, an outer target and a frame deviation greater than `.45`.
The reflection identity retains the same gap for the other primary owner.
No wrong-word conclusion or mismatch assumption is used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ZeroPrimary

open FramePair

def radialKind (s : State) : RadialKind := if s.branch.type=0 then .coreSide else .outer

theorem semantic_state (s : State) : CommonQuarter.State (radialKind s) s.a s.b := by
  by_cases hc : s.branch.type=0
  · simpa [radialKind,hc,CommonQuarter.State] using FrameCoreArc.state_core_chart s hc
  · have hh : CommonQuarter.OuterState s.a s.b := ⟨s.b_nonneg,s.canonical,s.outer_eq hc⟩
    simpa [radialKind,hc,CommonQuarter.State] using hh

theorem sign_eq (p : Bool) : (WordProblems.sign p:ℝ)=FramePair.sign p := by
  cases p <;> norm_num [WordProblems.sign,FramePair.sign]

theorem primary_lower (s : State) : (447/800:ℝ)<s.a := by
  by_cases hc : s.branch.type=0
  · have hh := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart s hc)).1
    linarith [CoreAngleEndpoint.diagonal_bounds.1]
  · have hh := CommonQuarter.outer_bounds
      (show CommonQuarter.OuterState s.a s.b from ⟨s.b_nonneg,s.canonical,s.outer_eq hc⟩)
    linarith [hh.1,CommonQuarter.outer_endpoint_bounds.2.2.1]

theorem coordinates (s : State) :
    (447/800:ℝ)<s.a ∧ s.a<283/200 ∧ 0≤s.b ∧ s.b≤s.a ∧ s.b<9/10 := by
  have hh := CommonQuarter.state_bounds (semantic_state s)
  exact ⟨primary_lower s,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩

/-- Every original target-primary zero contact lies in the same forced
large positive interval and has a strictly positive source tangent. -/
theorem target_primary_domain (s t : State) {d : ℝ} (hd : |d|≤7/10)
    (hg : (19/25:ℝ)<s.gap t d) (hm : s.Feasible t 1 d) :
    d∈Ioc (9/20) (7/10) ∧ s.positive=true ∧ 0<s.b ∧ 1<t.a ∧ t.branch.type≠0 := by
  have hs := semantic_state s
  have ht := semantic_state t
  have hsc := coordinates s
  have htc := coordinates t
  have hm₀ : 0≤forwardMargin 1 s.a s.b t.a t.b
      (WordProblems.sign s.positive) (WordProblems.sign t.positive) d := by
    simpa [State.Feasible,sign_eq] using hm
  have hg₀ : (19/25:ℝ)<d+(WordProblems.sign s.positive:ℝ)*Real.arctan (s.b/s.a)-
      (WordProblems.sign t.positive:ℝ)*Real.arctan (t.b/t.a) := by
    simpa [State.gap,State.offset,sign_eq] using hg
  have hmr : 0≤forwardMargin 3 t.a t.b s.a s.b
      (WordProblems.sign (!t.positive)) (WordProblems.sign (!s.positive)) d := by
    rw [← CommonQuarter.margin_reverse 1 s.positive t.positive s.a s.b t.a t.b d] at hm₀
    simpa using hm₀
  have hgr : (19/25:ℝ)<d+(WordProblems.sign (!t.positive):ℝ)*Real.arctan (t.b/t.a)-
      (WordProblems.sign (!s.positive):ℝ)*Real.arctan (s.b/s.a) := by
    rwa [CommonQuarter.gap_reverse]
  have hpositive : s.positive=true := by
    cases hp : s.positive
    · have hmf : 0≤forwardMargin 3 t.a t.b s.a s.b
          (WordProblems.sign (!t.positive)) 1 d := by
        simpa [hp,WordProblems.sign] using hmr
      have hgf : (19/25:ℝ)<d+(WordProblems.sign (!t.positive):ℝ)*Real.arctan (t.b/t.a)-
          Real.arctan (s.b/s.a) := by simpa [hp,WordProblems.sign] using hgr
      exact (CommonQuarter.zero_primary_positive_target_false ht hs (!t.positive) hd hgf hmf).elim
    · rfl
  have hmr' : 0≤forwardMargin 3 t.a t.b s.a s.b
      (WordProblems.sign (!t.positive)) (-1) d := by
    simpa [hpositive,WordProblems.sign] using hmr
  have hp : 0<d := CommonQuarter.zero_primary_negative_angle ht hs (!t.positive) hd hmr'
  have hdi : d∈Icc 0 (7/10) := ⟨hp.le,(abs_le.mp hd).2⟩
  have tr := CommonQuarter.positive_trig hdi
  have hsin : 0<Real.sin d := by
    linarith [(CommonQuarter.positive_taylor_reserves hdi).1]
  have hcos : 0<Real.cos d := by linarith [tr.1]
  have hdiff : 0<Real.cos d-Real.sin d := by linarith [tr.1,tr.2.2.2.1]
  have hbase : t.a-s.a*Real.cos d<1 := by
    have hh := mul_lt_mul_of_pos_right hsc.1 hcos
    nlinarith [htc.2.1,tr.1]
  have hm' : 0≤t.a-s.a*Real.cos d+s.b*Real.sin d-pairWidth d := by
    simpa [State.Feasible,forwardMargin,hpositive,FramePair.sign] using hm
  have hw := CommonQuarter.width_ge_one d
  have hb : 0<s.b := by
    by_contra! hn
    have hh := mul_nonpos_of_nonpos_of_nonneg hn hsin.le
    linarith
  have hbs := mul_le_mul_of_nonneg_right s.canonical hsin.le
  have hapos : 0<s.a*(Real.cos d-Real.sin d) := mul_pos s.a_pos hdiff
  have htarget : 1<t.a := by nlinarith
  have hlarge : (9/20:ℝ)<d := by
    by_contra! hsmall
    have hA := mul_le_mul_of_nonneg_right hsc.1.le hdiff.le
    have hc := cos_lower_two hp.le
    have hsine := Real.sin_le hp.le
    have hd2 := pow_le_pow_left₀ hp.le hsmall 2
    rw [CommonQuarter.signed_width hd,abs_of_nonneg hsin.le] at hm'
    nlinarith [htc.2.1]
  have houter : t.branch.type≠0 := by
    intro hc
    have hh := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart t hc)).2.1
    linarith
  exact ⟨⟨hlarge,hdi.2⟩,hpositive,hb,htarget,houter⟩

/-- Source-primary data are transported by exact reflection/reversal. -/
theorem source_primary_domain (s t : State) {d : ℝ} (hd : |d|≤7/10)
    (hg : (19/25:ℝ)<s.gap t d) (hm : s.Feasible t 3 d) :
    d∈Ioc (9/20) (7/10) ∧ t.positive=false ∧ 0<t.b ∧ 1<s.a ∧ s.branch.type≠0 := by
  have hrev : t.flip.Feasible s.flip 1 d := by
    simpa [State.Feasible,State.flip,forwardMargin,FramePair.sign_not,
      sub_eq_add_neg,mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hm
  have hh := target_primary_domain t.flip s.flip hd (by simpa using hg) hrev
  have hsign : t.positive=false := by
    cases hp : t.positive <;> simpa [State.flip,hp] using hh.2.1
  exact ⟨hh.1,hsign,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩

end SquaresInCircles.Eight.TableFree.ZeroPrimary
