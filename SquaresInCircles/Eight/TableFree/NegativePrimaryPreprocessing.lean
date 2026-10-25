module

public import SquaresInCircles.Eight.TableFree.NecessaryCycle
public import SquaresInCircles.Eight.TableFree.FlatCoreCancelingPrimary

/-!
# Actual same-radius preprocessing of either negative primary

Uncompiled source. A genuinely negative primary with its normal intermediate
sign is forced onto the flat core before either transverse-owner transport
is applied. This module joins those two transports, includes their aligned
weak ties, and reflects the resulting physical statement to the T side.

The cycle adapters preserve all seven selected neighboring inequalities,
all five anchor records, the opposite intermediate, the true core, the
actual circle ceiling, and both signed variations. They do not assert that
local algebraic feasibility alone supplies the cyclic-order or nearest-axis
classification needed by later boundary arguments.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
open Candidate

/-- The unchanged H and A have their original frames. Only G is replaced. -/
structure NegativeGEndpoint (q : ℝ) (H A : SignedPoint) (θH θA θG : ℝ) where
  point : SignedPoint
  theta : ℝ
  owner : Fin 4
  owner_allowed : owner=0 ∨ owner=2
  endpoint : theta=θA ∨ theta=θH
  sorted : point.Sorted
  core : point.Core
  avoids : point.AvoidsCore
  circle_lt : point.circle<q
  normal : point.y<0
  HG : zeroFeasible H point (theta-θH) owner
  GA : quarterFeasible point A (θA-theta) 1
  hard_at_A : theta=θA → quarterFeasible point A (θA-theta) 0
  strict_if_unaligned : θG≠θH →
    edgeWidth (theta-θH)<zeroProjection H point (theta-θH) owner

/-- Both original HG owners are covered, including an exact original HG tie.
The strict failure of the hard GA axis is tested on the original G. -/
theorem negative_GA_pair_endpoint
    {q θH θG θA : ℝ} {H G A : SignedPoint} {j : Fin 4}
    (hq : q≤qCap)
    (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHc : H.Contained q) (hGc : G.Contained q) (hAc : A.Contained q)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (hGb : G.Boundary q) (hHy : 0≤H.y) (hGy : G.y≤0) (hAy : 0≤A.y)
    (hnegative : θA-θG<0)
    (hGAerror : |θA-θG|≤7/10)
    (hHAerror : |θH-θA|≤7/10)
    (hHGerror : |θG-θH|≤7/10)
    (hj : j=0 ∨ j=2)
    (hHG : zeroFeasible H G (θG-θH) j)
    (hGA : quarterFeasible G A (θA-θG) 1)
    (hnot : ¬quarterFeasible G A (θA-θG) 0) :
    Nonempty (NegativeGEndpoint q H A θH θA θG) := by
  let z := θG-θA
  let Θ := θH-θA
  have hz : 0<z ∧ z≤7/10 := by
    dsimp [z]
    rw [abs_of_neg hnegative] at hGAerror
    constructor <;> linarith
  have hΘ : |Θ|≤(7/10 : ℝ) := hHAerror
  have heGA : -z=θA-θG := by dsimp [z]; ring
  have heHG : z-Θ=θG-θH := by dsimp [z,Θ]; ring
  have hgap : |z-Θ|≤(7/10 : ℝ) := by rwa [heHG]
  have htransport : ∃ (G' : SignedPoint) (x : ℝ) (k : Fin 4),
      (k=0 ∨ k=2) ∧ (x=0 ∨ x=Θ) ∧ G'.Sorted ∧ G'.Core ∧
      G'.AvoidsCore ∧ G'.circle<q ∧ G'.y<0 ∧
      zeroFeasible H G' (x-Θ) k ∧ quarterFeasible G' A (-x) 1 ∧
      (x=0 → quarterFeasible G' A (-x) 0) ∧
      (z≠Θ → edgeWidth (x-Θ)<zeroProjection H G' (x-Θ) k) := by
    rcases hj with rfl | rfl
    · obtain ⟨hflat,hsmall,hcore,hvector⟩ := negative_primary_flat_entry
        hGs hAs hGb hAc hq hGy hAy hz
        (heGA.symm ▸ hGA) (heGA.symm ▸ hnot)
      obtain ⟨G',x,ha,hend,hframe,hs,hc,havoid,hcircle,hHG',hGA',hhard,hstrict,hyn⟩ :=
        flat_core_negative_ga1_hg0_transport hq hHs hGs hAs hHc hGc hAc
          hHcore hGcore hAcore hflat hGy hz hΘ hgap
          (heHG.symm ▸ hHG) (heGA.symm ▸ hGA)
      exact ⟨G',x,0,Or.inl rfl,hend,hs,hc,havoid,hcircle,hyn,
        hHG',hGA',hhard,hstrict⟩
    · obtain ⟨G',x,k,hk,ha,hend,hframe,hs,hc,havoid,hcircle,hHG',hGA',hhard,hstrict,hyn⟩ :=
        flat_core_negative_ga1_hg2_transport hq hHs hGs hAs hHc hGc hAc
          hHcore hGcore hAcore hGb hHy hGy hAy hz hΘ hgap
          (heHG.symm ▸ hHG) (heGA.symm ▸ hGA) (heGA.symm ▸ hnot)
      exact ⟨G',x,k,hk,hend,hs,hc,havoid,hcircle,hyn,hHG',hGA',hhard,hstrict⟩
  obtain ⟨G',x,k,hk,hend,hs,hcore,havoid,hcircle,hyn,hHG',hGA',hhard,hstrict⟩ := htransport
  let θ' := θA+x
  have he₁ : θ'-θH=x-Θ := by dsimp [θ',Θ]; ring
  have he₂ : θA-θ'= -x := by dsimp [θ']; ring
  refine ⟨{
    point := G'
    theta := θ'
    owner := k
    owner_allowed := hk
    endpoint := ?_
    sorted := hs
    core := hcore
    avoids := havoid
    circle_lt := hcircle
    normal := hyn
    HG := he₁.symm ▸ hHG'
    GA := he₂.symm ▸ hGA'
    hard_at_A := ?_
    strict_if_unaligned := ?_ }⟩
  · rcases hend with hx0 | hxΘ
    · left; dsimp [θ']; linarith
    · right; dsimp [θ',Θ] at *; linarith
  · intro he
    have hx0 : x=0 := by dsimp [θ'] at he; linarith
    rw [he₂]
    exact hhard hx0
  · intro hne
    have hzne : z≠Θ := by
      intro he
      apply hne
      dsimp [z,Θ] at he
      linarith
    rw [he₁]
    exact hstrict hzne

/-- The exact reflected output uses the original B and D, and changes T only. -/
structure NegativeTEndpoint (q : ℝ) (B D : SignedPoint) (θB θD θT : ℝ) where
  point : SignedPoint
  theta : ℝ
  owner : Fin 4
  owner_allowed : owner=0 ∨ owner=2
  endpoint : theta=θB ∨ theta=θD
  sorted : point.Sorted
  core : point.Core
  avoids : point.AvoidsCore
  circle_lt : point.circle<q
  normal : 0<point.y
  BT : quarterFeasible B point (theta-θB) 3
  TD : zeroFeasible point D (θD-theta) owner
  hard_at_B : theta=θB → quarterFeasible B point (theta-θB) 2
  strict_if_unaligned : θT≠θD →
    edgeWidth (θD-theta)<zeroProjection point D (θD-theta) owner

/-- Reflection is local to the triple. There is no E-sign hypothesis. -/
theorem negative_BT_pair_endpoint
    {q θB θT θD : ℝ} {B T D : SignedPoint} {j : Fin 4}
    (hq : q≤qCap)
    (hBs : B.Sorted) (hTs : T.Sorted) (hDs : D.Sorted)
    (hBc : B.Contained q) (hTc : T.Contained q) (hDc : D.Contained q)
    (hBcore : B.AvoidsCore) (hTcore : T.AvoidsCore) (hDcore : D.AvoidsCore)
    (hTb : T.Boundary q) (hBy : B.y≤0) (hTy : 0≤T.y) (hDy : D.y≤0)
    (hnegative : θT-θB<0)
    (hBTerror : |θT-θB|≤7/10)
    (hBDerror : |θD-θB|≤7/10)
    (hTDerror : |θD-θT|≤7/10)
    (hj : j=0 ∨ j=2)
    (hBT : quarterFeasible B T (θT-θB) 3)
    (hTD : zeroFeasible T D (θD-θT) j)
    (hnot : ¬quarterFeasible B T (θT-θB) 2) :
    Nonempty (NegativeTEndpoint q B D θB θD θT) := by
  have hk : reflectedOwner j=0 ∨ reflectedOwner j=2 := by
    rcases hj with rfl | rfl <;> simp [reflectedOwner]
  have hTD' := (zeroFeasible_reflect T D (θD-θT) j).2 hTD
  have hBT' := (quarterFeasible_reflect B T (θT-θB) 3).2 hBT
  have hnot' : ¬quarterFeasible T.reflect B.reflect (θT-θB) 0 := by
    intro h
    exact hnot ((quarterFeasible_reflect B T (θT-θB) 2).1 (by simpa [reflectedOwner] using h))
  obtain ⟨O⟩ := negative_GA_pair_endpoint
    (q := q) (θH := -θD) (θG := -θT) (θA := -θB)
    (H := D.reflect) (G := T.reflect) (A := B.reflect)
    (j := reflectedOwner j) hq
    (by simpa using hDs) (by simpa using hTs) (by simpa using hBs)
    (by simpa using hDc) (by simpa using hTc) (by simpa using hBc)
    (by simpa using hDcore) (by simpa using hTcore) (by simpa using hBcore)
    (by simpa using hTb)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa [SignedPoint.reflect] using neg_nonpos.mpr hTy)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    (by simpa only [neg_sub_neg] using hnegative)
    (by simpa only [neg_sub_neg] using hBTerror)
    (by rw [neg_sub_neg,abs_sub_comm]; exact hBDerror)
    (by simpa only [neg_sub_neg] using hTDerror) hk
    (by simpa only [neg_sub_neg] using hTD')
    (by rw [neg_sub_neg]; exact hBT')
    (by simpa only [neg_sub_neg] using hnot')
  refine ⟨{
    point := O.point.reflect
    theta := -O.theta
    owner := reflectedOwner O.owner
    owner_allowed := ?_
    endpoint := ?_
    sorted := by simpa using O.sorted
    core := by simpa using O.core
    avoids := by simpa using O.avoids
    circle_lt := by simpa using O.circle_lt
    normal := by simpa [SignedPoint.reflect] using neg_pos.mpr O.normal
    BT := ?_
    TD := ?_
    hard_at_B := ?_
    strict_if_unaligned := ?_ }⟩
  · rcases O.owner_allowed with he | he <;> simp [he,reflectedOwner]
  · rcases O.endpoint with he | he
    · left; linarith
    · right; linarith
  · have h := (quarterFeasible_reflect O.point B.reflect (-θB-O.theta) 1).2 O.GA
    simpa [reflectedOwner,sub_eq_add_neg,add_comm] using h
  · have h := (zeroFeasible_reflect D.reflect O.point (O.theta-(-θD)) O.owner).2 O.HG
    simpa [sub_eq_add_neg,add_comm] using h
  · intro he
    have hO : O.theta= -θB := by linarith
    have h := (quarterFeasible_reflect O.point B.reflect (-θB-O.theta) 0).2
      (O.hard_at_A hO)
    simpa [reflectedOwner,sub_eq_add_neg,add_comm] using h
  · intro hne
    have hO : -θT≠ -θD := fun h => hne (neg_inj.mp h)
    have h := O.strict_if_unaligned hO
    have hid := zeroProjection_reflect D.reflect O.point (O.theta-(-θD)) O.owner
    rw [← hid] at h
    simpa [sub_eq_add_neg,add_comm] using h


namespace SignedCycle

/-- Endpoint frame replacement preserves every pairwise spread estimate. -/
theorem spread_replace_endpoint {C : SignedCycle} {v a b : Vertex}
    {p : SignedPoint} {t : ℝ} (h : C.Spread)
    (ht : t=C.theta a ∨ t=C.theta b) :
    (replacePoint C v p t).Spread := by
  intro i j
  rcases ht with ht | ht
  · by_cases hi : i=v <;> by_cases hj : j=v <;>
      simpa [replacePoint,ht,hi,hj] using
        h (if i=v then a else i) (if j=v then a else j)
  · by_cases hi : i=v <;> by_cases hj : j=v <;>
      simpa [replacePoint,ht,hi,hj] using
        h (if i=v then b else i) (if j=v then b else j)

/-- The full strict real-frame bound is preserved by the same exact endpoint. -/
theorem strictSpread_replace_endpoint {C : SignedCycle} {v a b : Vertex}
    {p : SignedPoint} {t : ℝ} (h : C.StrictSpread)
    (ht : t=C.theta a ∨ t=C.theta b) :
    (replacePoint C v p t).StrictSpread := by
  intro i j
  rcases ht with ht | ht
  · by_cases hi : i=v <;> by_cases hj : j=v <;>
      simpa [replacePoint,ht,hi,hj] using
        h (if i=v then a else i) (if j=v then a else j)
  · by_cases hi : i=v <;> by_cases hj : j=v <;>
      simpa [replacePoint,ht,hi,hj] using
        h (if i=v then b else i) (if j=v then b else j)

private lemma r28_replaceG_HG (C : SignedCycle) (P : SignedPoint) (t : ℝ) (j : Fin 4) :
    (replacePoint C G P t).Feasible H j ↔ zeroFeasible (C.point H) P (t-C.theta H) j := by
  simp [replacePoint,Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg]

private lemma r28_replaceG_GA (C : SignedCycle) (P : SignedPoint) (t : ℝ) (j : Fin 4) :
    (replacePoint C G P t).Feasible G j ↔ quarterFeasible P (C.point A) (C.theta A-t) j := by
  simp [replacePoint,Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg]

/-- All original nonincident witnesses are left verbatim in the owner vector. -/
def negativeGWitnesses {C : SignedCycle} {q : ℝ} (w : C.Witnesses)
    (O : NegativeGEndpoint q (C.point H) (C.point A)
      (C.theta H) (C.theta A) (C.theta G)) :
    (replacePoint C G O.point O.theta).Witnesses where
  owner := Function.update (Function.update w.owner H O.owner) G 1
  feasible i := by
    have hHG : H ≠ G := by decide
    fin_cases i
    · show (replacePoint C G O.point O.theta).Feasible H
        (Function.update (Function.update w.owner H O.owner) G 1 H)
      rw [Function.update_of_ne hHG,Function.update_self]
      exact (r28_replaceG_HG C O.point O.theta O.owner).2 O.HG
    · show (replacePoint C G O.point O.theta).Feasible G
        (Function.update (Function.update w.owner H O.owner) G 1 G)
      rw [Function.update_self]
      exact (r28_replaceG_GA C O.point O.theta 1).2 O.GA
    all_goals
      rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide)]
      exact (replacePoint_other_feasible (by decide) (by decide)).2 (w.feasible _)
  allowed i := by
    fin_cases i
    · rcases O.owner_allowed with he | he <;> simp [he,normalOwners,H,G]
    · simp [normalOwners,H,G]
    all_goals simpa [H,G] using w.allowed _

/-- The replacement never consumes the opposite-side sign implication. -/
theorem negativeG_zero_signs {C : SignedCycle} {q : ℝ} (w : C.Witnesses)
    (h : C.ZeroSignImplications w)
    (O : NegativeGEndpoint q (C.point H) (C.point A)
      (C.theta H) (C.theta A) (C.theta G)) :
    (replacePoint C G O.point O.theta).ZeroSignImplications
      (negativeGWitnesses w O) := by
  constructor
  · intro _
    simpa [replacePoint,G] using O.normal
  · intro hj
    have hTD : w.owner T=0 := by simpa [negativeGWitnesses,H,G,T] using hj
    simpa [replacePoint,G,T] using h.TD_canceling hTD

/-- Necessary actual-coordinate data survive on every vertex. -/
theorem negativeG_necessary {C : SignedCycle} {q : ℝ}
    (h : C.Necessary q)
    (O : NegativeGEndpoint q (C.point H) (C.point A)
      (C.theta H) (C.theta A) (C.theta G)) :
    (replacePoint C G O.point O.theta).Necessary q := {
  sorted i := by
    by_cases hi : i=G
    · simpa [replacePoint,hi] using O.sorted
    · simpa [replacePoint,hi] using h.sorted i
  contained i := by
    by_cases hi : i=G
    · simpa [replacePoint,hi,SignedPoint.Contained] using O.circle_lt.le
    · simpa [replacePoint,hi] using h.contained i
  core i := by
    by_cases hi : i=G
    · simpa [replacePoint,hi] using O.avoids
    · simpa [replacePoint,hi] using h.core i
  spread := spread_replace_endpoint h.spread O.endpoint }

/-- Every original radial label except G stays unchanged; the new G is an
actual true-core state, with strict interiority in the same input disk. -/
theorem negativeG_radial {C : SignedCycle} {q : ℝ}
    (h : ∀ i, (C.point i).Boundary q)
    (O : NegativeGEndpoint q (C.point H) (C.point A)
      (C.theta H) (C.theta A) (C.theta G)) :
    ∀ i, ((replacePoint C G O.point O.theta).point i).Boundary q := by
  intro i
  by_cases hi : i=G
  · subst hi
    have hb : O.point.Boundary q := by unfold SignedPoint.Boundary; exact Or.inr O.core
    simpa [replacePoint] using hb
  · simpa [replacePoint,hi] using h i

/-- Both retained incident axes are actual; no equality endpoint is used as
an original-square claim. At HG alignment either zero owner may be selected. -/
theorem negativeG_terminal {C : SignedCycle} {q : ℝ}
    (O : NegativeGEndpoint q (C.point H) (C.point A)
      (C.theta H) (C.theta A) (C.theta G)) :
    let D := replacePoint C G O.point O.theta
    D.Feasible G 0 ∨
      (delta D.theta H=0 ∧ D.Feasible H 0 ∧ D.Feasible H 2 ∧
        D.Feasible G 1 ∧ (D.point G).y<0) := by
  dsimp only
  rcases O.endpoint with hA | hH
  · left
    have hh := O.hard_at_A hA
    simpa [Feasible,slack,edge,replacePoint,word,delta,next,G,A,
      quarterFeasible] using sub_nonneg.mpr hh
  · right
    have hzero : zeroFeasible (C.point H) O.point 0 0 := by
      have hh := O.HG
      rw [hH,sub_self] at hh
      rcases O.owner_allowed with he | he
      · simpa [he] using hh
      · exact (zero_owner_tie _ _).2 (by simpa [he] using hh)
    have hzero2 := (zero_owner_tie _ _).1 hzero
    refine ⟨?_,?_,?_,?_,?_⟩
    · simp [replacePoint,delta,next,H,G,hH]
    · simpa [Feasible,slack,edge,replacePoint,word,delta,next,H,G,hH,
        zeroFeasible] using sub_nonneg.mpr hzero
    · simpa [Feasible,slack,edge,replacePoint,word,delta,next,H,G,hH,
        zeroFeasible] using sub_nonneg.mpr hzero2
    · simpa [Feasible,slack,edge,replacePoint,word,delta,next,G,A,
        quarterFeasible] using sub_nonneg.mpr O.GA
    · simpa [replacePoint,G] using O.normal

/-- The strict original transverse slack is retained on the actual descendant.
A later opposite-intermediate move cannot remove it. -/
theorem negativeG_strict_source_slack {C : SignedCycle} {q : ℝ}
    (O : NegativeGEndpoint q (C.point H) (C.point A)
      (C.theta H) (C.theta A) (C.theta G))
    (hne : C.theta G≠C.theta H) :
    0<(replacePoint C G O.point O.theta).slack H O.owner := by
  have hh := O.strict_if_unaligned hne
  simpa [slack,edge,replacePoint,word,delta,next,H,G]
    using sub_pos.mpr hh

end SignedCycle
end SquaresInCircles.Eight.TableFree
