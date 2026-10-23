module

public import SquaresInCircles.Eight.TableFree.PrimaryPairClassification

/-!
# Actual primary preprocessing with its original-source obstruction

Uncompiled reconstruction from the retained local transports.  A source
which already has its hard primary is left literally unchanged.  If a
missing hard primary becomes feasible, the output retains either the
positive original anchor total or a strict actual neighboring zero axis.
The implication tests actual output feasibility, not its selected owner.
No equality conclusion or hard-class endpoint is assumed here.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate

structure GPairSourceOutput (q : ℝ) (H G A : SignedPoint) (θH θG θA : ℝ) where
  output : GPairOutput q H A θH θG θA
  fixed_if_hard : quarterFeasible G A (θA-θG) 0 →
    output.point=G ∧ output.theta=θG
  source_obstruction : (¬quarterFeasible G A (θA-θG) 0) →
    quarterFeasible output.point A (θA-output.theta) 0 →
    0<θA-θH ∨
      edgeWidth (output.theta-θH)<
        zeroProjection H output.point (output.theta-θH) output.hgOwner

namespace GPairSourceOutput

def original_hard {q θH θG θA : ℝ} {H G A : SignedPoint}
    (I : GPairInput q H G A θH θG θA)
    (hhard : quarterFeasible G A (θA-θG) 0) :
    GPairSourceOutput q H G A θH θG θA where
  output := GPairOutput.original_hard I hhard
  fixed_if_hard := fun _ => ⟨rfl,rfl⟩
  source_obstruction := fun h _ => False.elim (h hhard)

/-- An already aligned negative primary remains its literal source.
Moving it again would discard the required source-contact provenance. -/
def original_negative {q θH θG θA : ℝ} {H G A : SignedPoint}
    (I : GPairInput q H G A θH θG θA)
    (hnot : ¬quarterFeasible G A (θA-θG) 0)
    (hn : θA-θG<0) (hy : G.y<0) (ha : θG=θH) :
    GPairSourceOutput q H G A θH θG θA where
  output := {
    point := G
    theta := θG
    hgOwner := I.owner
    gaOwner := 1
    hg_allowed := I.owner_allowed
    ga_allowed := Or.inr rfl
    sorted := I.G_sorted
    contained := I.G_contained
    avoids := I.G_core
    boundary := I.G_boundary
    HG := I.HG
    GA := I.GA
    canceling_normal := I.canceling_normal
    frame_range := Or.inl rfl
    terminal := Or.inr (Or.inr (Or.inl ⟨rfl,ha,hn,hy⟩)) }
  fixed_if_hard := fun h => False.elim (hnot h)
  source_obstruction := fun _ h => False.elim (hnot h)

/-- For an unaligned negative source, an actual hard output keeps the
strict owner supplied by the concrete negative transport.  If the hard
axis remains absent, the endpoint is classified with its aligned tie. -/
theorem of_negative {q θH θG θA : ℝ} {H G A : SignedPoint}
    (hnot : ¬quarterFeasible G A (θA-θG) 0)
    (hne : θG≠θH) (O : NegativeGEndpoint q H A θH θA θG) :
    Nonempty (GPairSourceOutput q H G A θH θG θA) := by
  have hframe : O.theta∈Icc (min θH θA) (max θH θA) := by
    rcases O.endpoint with h | h
    · rw [h]; exact ⟨min_le_right _ _,le_max_right _ _⟩
    · rw [h]; exact ⟨min_le_left _ _,le_max_left _ _⟩
  by_cases hhard : quarterFeasible O.point A (θA-O.theta) 0
  · exact ⟨{
      output := {
        point := O.point
        theta := O.theta
        hgOwner := O.owner
        gaOwner := 0
        hg_allowed := O.owner_allowed
        ga_allowed := Or.inl rfl
        sorted := O.sorted
        contained := O.circle_lt.le
        avoids := O.avoids
        boundary := Or.inr O.core
        HG := O.HG
        GA := hhard
        canceling_normal := fun _ => O.normal
        frame_range := Or.inr hframe
        terminal := Or.inl rfl }
      fixed_if_hard := fun h => False.elim (hnot h)
      source_obstruction := fun _ _ => Or.inr (O.strict_if_unaligned hne) }⟩
  have hH : O.theta=θH := by
    rcases O.endpoint with h | h
    · exact False.elim (hhard (O.hard_at_A h))
    · exact h
  have hzero : zeroFeasible H O.point 0 2 := by
    have hh := O.HG
    rw [hH,sub_self] at hh
    rcases O.owner_allowed with h | h
    · exact (zero_owner_tie _ _).1 (by simpa [h] using hh)
    · simpa [h] using hh
  have hnonzero : θA-O.theta≠0 := by
    intro h
    apply hhard
    rw [h]
    exact (quarter_low_tie _ _).2 (by simpa [h] using O.GA)
  have hterminal :
      (1 : Fin 4)=0 ∨
        ((1 : Fin 4)=1 ∧ (2 : Fin 4)=2 ∧ 0<θA-O.theta) ∨
        ((1 : Fin 4)=1 ∧ O.theta=θH ∧ θA-O.theta<0 ∧ O.point.y<0) ∨
        O.point.y= -O.point.a := by
    rcases lt_or_gt_of_ne hnonzero with hn | hp
    · exact Or.inr (Or.inr (Or.inl ⟨rfl,hH,hn,O.normal⟩))
    · exact Or.inr (Or.inl ⟨rfl,rfl,hp⟩)
  exact ⟨{
    output := {
      point := O.point
      theta := O.theta
      hgOwner := 2
      gaOwner := 1
      hg_allowed := Or.inr rfl
      ga_allowed := Or.inr rfl
      sorted := O.sorted
      contained := O.circle_lt.le
      avoids := O.avoids
      boundary := Or.inr O.core
      HG := by simpa [hH] using hzero
      GA := O.GA
      canceling_normal := fun _ => O.normal
      frame_range := Or.inr hframe
      terminal := hterminal }
    fixed_if_hard := fun h => False.elim (hnot h)
    source_obstruction := fun _ h => False.elim (hhard h) }⟩

end GPairSourceOutput

/-- Every original source row has an actual same-radius output together
with the strict source information needed by the later equality pullback. -/
theorem preprocess_G_pair_with_source {q θH θG θA : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (I : GPairInput q H G A θH θG θA) :
    Nonempty (GPairSourceOutput q H G A θH θG θA) := by
  by_cases hhard : quarterFeasible G A (θA-θG) 0
  · exact ⟨GPairSourceOutput.original_hard I hhard⟩
  have hnonzero : θA-θG≠0 := by
    intro h
    apply hhard
    rw [h]
    exact (quarter_low_tie _ _).2 (by simpa [h] using I.GA)
  have hHbound : H.y<9/10 := (le_abs_self H.y).trans_lt
    (H.coordinate_bounds I.H_sorted I.H_core I.H_contained hqU).2.2
  have negative_endpoint (hn : θA-θG<0) (hy : G.y≤0) :
      Nonempty (GPairSourceOutput q H G A θH θG θA) := by
    by_cases ha : θG=θH
    · have hzero : zeroFeasible H G 0 0 := by
        have hh := I.HG
        rw [ha,sub_self] at hh
        rcases I.owner_allowed with hj | hj
        · simpa [hj] using hh
        · exact (zero_owner_tie _ _).2 (by simpa [hj] using hh)
      have hylt := hg0_nonpositive_error_normal hHbound I.G_sorted.1
        (by norm_num : |(0 : ℝ)|≤7/10) (by norm_num : (0 : ℝ)≤0) hzero
      exact ⟨GPairSourceOutput.original_negative I hhard hn hylt ha⟩
    · obtain ⟨O⟩ := negative_GA_pair_endpoint hqU
        I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
        I.H_core I.G_core I.A_core I.G_boundary I.H_normal hy I.A_normal
        hn I.GA_error (by simpa [abs_sub_comm] using I.HA_error) I.HG_error
        I.owner_allowed I.HG I.GA hhard
      exact GPairSourceOutput.of_negative hhard ha O
  rcases I.owner_allowed with hj | hj
  · have hHG : zeroFeasible H G (θG-θH) 0 := by simpa [hj] using I.HG
    by_cases htotal : 0<θA-θH
    · obtain ⟨O⟩ := positive_GA_HG_pair hqL hqU
        I.H_sorted I.A_sorted I.G_sorted I.H_normal I.H_contained I.A_outer
        I.G_contained I.G_core hHG I.GA I.GA_error I.HG_error
        ⟨htotal,(abs_le.mp I.HA_error).2⟩
      obtain ⟨P⟩ := GPairOutput.of_positive_endpoint O hHbound htotal
      exact ⟨{
        output := P
        fixed_if_hard := fun h => False.elim (hhard h)
        source_obstruction := fun _ _ => Or.inl htotal }⟩
    · have htotal0 : θA≤θH := by linarith
      rcases lt_or_gt_of_ne hnonzero with hn | hp
      · by_cases hy : G.y≤0
        · exact negative_endpoint hn hy
        · have hy0 : 0≤G.y := (lt_of_not_ge hy).le
          have hHGpos : 0<θG-θH := by
            by_contra! hd
            exact (not_le_of_gt
              (hg0_nonpositive_error_normal hHbound I.G_sorted.1 I.HG_error hd hHG)) hy0
          let s := θH-θA
          let v := θG-θH
          have hs : 0≤s := by dsimp [s]; linarith
          have hv : 0≤v := hHGpos.le
          have hsum : v+s=θG-θA := by dsimp [v,s]; ring
          have hsumBound : v+s≤7/10 := by
            rw [hsum]
            linarith [(abs_le.mp I.GA_error).1]
          have hprimary : quarterFeasible G A (-(v+s)) 1 := by
            convert I.GA using 1 <;> dsimp [v,s] <;> ring
          obtain ⟨hs',hc',hcircle,hHG',hGA',hGA1',hstrict⟩ :=
            wrong_sign_nonpositive_total_transport hqU
              I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
              I.H_core I.G_core I.A_core I.H_normal hy0 I.A_normal hs hv hsumBound
              hHG hprimary
          have he : θA-θH= -s := by dsimp [s]; ring
          have htransverse : zeroFeasible H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0 := by
            rw [he]
            exact hHG'
          refine ⟨{
            output := GPairOutput.flat_hard hs' hc' hcircle htransverse hGA'
            fixed_if_hard := fun h => False.elim (hhard h)
            source_obstruction := ?_ }⟩
          intro _ _
          right
          change edgeWidth (θA-θH)<
            zeroProjection H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0
          rw [he]
          linarith
      · have hHGneg : θG-θH≤0 := by linarith
        have hy := (hg0_nonpositive_error_normal hHbound I.G_sorted.1
          I.HG_error hHGneg hHG).le
        let s := θH-θA
        let x := θA-θG
        have hs : 0≤s := by dsimp [s]; linarith
        have hx : 0<x := hp
        have hsum : s+x=θH-θG := by dsimp [s,x]; ring
        have hsumBound : s+x≤7/10 := by
          rw [hsum]
          linarith [(abs_le.mp I.HG_error).1]
        have htransverse : zeroFeasible H G (-(s+x)) 0 := by
          convert hHG using 1 <;> dsimp [s,x] <;> ring
        obtain ⟨hs',hc',havoid,hcircle,hGA',hGA1',hstrict⟩ :=
          positive_ga1_nonpositive_total_transport hqU
            I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
            I.H_core I.G_core I.A_core I.H_normal hy I.A_normal hx hs hsumBound
            htransverse I.GA
        have he : θA-θH= -s := by dsimp [s]; ring
        have hHG' : zeroFeasible H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0 := by
          rw [he]
          exact hstrict.le
        refine ⟨{
          output := GPairOutput.flat_hard hs' hc' hcircle hHG' hGA'
          fixed_if_hard := fun h => False.elim (hhard h)
          source_obstruction := ?_ }⟩
        intro _ _
        right
        change edgeWidth (θA-θH)<
          zeroProjection H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0
        rw [he]
        exact hstrict
  · rcases lt_or_gt_of_ne hnonzero with hn | hp
    · exact negative_endpoint hn (I.canceling_normal hj).le
    · exact ⟨{
        output := GPairOutput.original_positive I hj hp
        fixed_if_hard := fun h => False.elim (hhard h)
        source_obstruction := fun _ h => False.elim (hhard h) }⟩

structure TPairSourceOutput (q : ℝ) (B T D : SignedPoint) (θB θT θD : ℝ) where
  output : TPairOutput q B D θB θT θD
  fixed_if_hard : quarterFeasible B T (θT-θB) 2 →
    output.point=T ∧ output.theta=θT
  source_obstruction : (¬quarterFeasible B T (θT-θB) 2) →
    quarterFeasible B output.point (output.theta-θB) 2 →
    0<θD-θB ∨
      edgeWidth (θD-output.theta)<
        zeroProjection output.point D (θD-output.theta) output.tdOwner

/-- Local reflection preserves the actual source and target hard-axis tests.
The original E point and its signed tangent do not occur in this operation. -/
def GPairSourceOutput.reflectToT {q θB θT θD : ℝ} {B T D : SignedPoint}
    (S : GPairSourceOutput q D.reflect T.reflect B.reflect (-θD) (-θT) (-θB)) :
    TPairSourceOutput q B T D θB θT θD where
  output := S.output.reflectToT
  fixed_if_hard := by
    intro h
    have hh : quarterFeasible T.reflect B.reflect (-θB-(-θT)) 0 := by
      simpa [neg_sub_neg,reflectedOwner] using
        (quarterFeasible_reflect B T (θT-θB) 2).2 h
    obtain ⟨hp,ht⟩ := S.fixed_if_hard hh
    change S.output.point.reflect=T ∧ -S.output.theta=θT
    constructor
    · rw [hp]; simp
    · linarith
  source_obstruction := by
    intro hnot hout
    have hnot' : ¬quarterFeasible T.reflect B.reflect (-θB-(-θT)) 0 := by
      intro h
      apply hnot
      apply (quarterFeasible_reflect B T (θT-θB) 2).1
      simpa [neg_sub_neg,reflectedOwner] using h
    have hout' : quarterFeasible B S.output.point.reflect (-θB-S.output.theta) 2 := by
      simpa [GPairOutput.reflectToT,sub_eq_add_neg,add_comm] using hout
    have hhard : quarterFeasible S.output.point B.reflect (-θB-S.output.theta) 0 :=
      (quarterFeasible_reflect S.output.point B.reflect (-θB-S.output.theta) 0).1
        (by simpa [reflectedOwner] using hout')
    rcases S.source_obstruction hnot' hhard with htotal | hstrict
    · left
      simpa only [neg_sub_neg] using htotal
    · right
      have hid := zeroProjection_reflect D.reflect S.output.point
        (S.output.theta-(-θD)) S.output.hgOwner
      rw [←hid] at hstrict
      simpa [GPairOutput.reflectToT,sub_eq_add_neg,add_comm] using hstrict

theorem preprocess_T_pair_with_source {q θB θT θD : ℝ} {B T D : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (I : TPairInput q B T D θB θT θD) :
    Nonempty (TPairSourceOutput q B T D θB θT θD) := by
  obtain ⟨S⟩ := preprocess_G_pair_with_source hqL hqU I
  exact ⟨S.reflectToT⟩

end SquaresInCircles.Eight.TableFree
