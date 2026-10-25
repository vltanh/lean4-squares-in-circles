module

public import SquaresInCircles.Eight.Owners.Flat.CoreCancelingPrimary

/-!
# Eight squares: preprocessing a negative primary at the same radius

A negative GA primary, with GA1 weak and GA0 failing at G, is forced onto the flat core before the
transport of either transverse owner of HG applies. For both owners `0` and `2` of HG, exact ties
included, the two transports are joined into one endpoint (`negative_GA_pair_endpoint`): G moves
to a core point strictly inside the circle, at the frame of A or of H, with the HG witness, GA1,
the hard GA0 at the frame of A, and strict HG slack when HG was not aligned (`NegativeGEndpoint`).
H and A keep their points and frames.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate

/-- The endpoint of a negative G primary: G is replaced by a core point at the frame of A or of H,
while H and A keep their points and frames. -/
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

/-- A negative GA1 primary with GA0 failing at G reaches a `NegativeGEndpoint`, for both owners `0`
and `2` of HG, an exact HG tie included. -/
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

namespace SignedCycle

end SignedCycle
end SquaresInCircles.Eight
