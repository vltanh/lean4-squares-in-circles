module

public import SquaresInCircles.Eight.Candidate.GeometricCoreMarker

/-!
# Coarse affine coverage with a direct core/core cost proof

Each vertex keeps the label selected by the original closed state cover.
When both selected arcs are core, center separation and the marker theorem
supply the charged inequality. Every remaining feasible domain has an
outer endpoint and uses the original row claim and closed angle chain.

The endpoint-label checks and seven scalar budgets are explicit in
`NumericValid`. There is no computed replacement list for the core pairs.
This source and its finite obligations remain uncompiled.
-/

@[expose] public section
open scoped BigOperators
namespace SquaresInCircles.Eight.Candidate.GeometricCoreCoverage
open Arithmetic

def AngleValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  ∀ s t : Fin M.arcs.length,
    (arcAt M t).role=(arcAt M s).role+1 →
    ∀ axis : ForwardAxis, axis∈M.allowedAxes (arcAt M s).role →
      ¬ GeometricAffine.Excluded M s t axis →
      ((arcAt M s).outer=true ∨ (arcAt M t).outer=true) → ∀ r : Bool,
      Every (fun k => k<rows.length ∧
        (rows.getD k default).source=s.val ∧ (rows.getD k default).target=t.val ∧
        (rows.getD k default).edge=(arcAt M s).role ∧ (rows.getD k default).axis=axis ∧
        (rows.getD k default).quarter=M.word (arcAt M s).role ∧
        (rows.getD k default).positiveHalf=r ∧
        M.target (arcAt M s).role≤(rows.getD k default).lowerTarget)
        (K.angleRows s t axis r) ∧
      ClosedChain (K.required M s t r).lo (K.required M s t r).hi
        ((K.angleRows s t axis r).map (fun k => (rows.getD k default).angle))

def NumericValid (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) : Prop :=
  K.EndpointsValid M ∧ K.states.NumericValid M ∧
    GeometricCoreMarker.MarkersValid K M ∧ GeometricCoreMarker.BudgetsValid M ∧
    AngleValid K M rows

instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (AngleValid K M rows) := by unfold AngleValid; infer_instance

instance (K : AffineCover) (M : AffineTableMeta) (rows : List AffineTableRow) :
    Decidable (NumericValid K M rows) := by unfold NumericValid; infer_instance

theorem row_cover {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : AngleValid K M rows) {s t : Fin M.arcs.length}
    (hst : (arcAt M t).role=(arcAt M s).role+1)
    {axis : ForwardAxis} (haxis : axis∈M.allowedAxes (arcAt M s).role)
    (hkeep : ¬ GeometricAffine.Excluded M s t axis)
    (houter : (arcAt M s).outer=true ∨ (arcAt M t).outer=true)
    {r : Bool} {u : ℝ} (hu : (K.required M s t r).Mem u) :
    ∃ row ∈ rows,
      row.source=s.val ∧ row.target=t.val ∧ row.edge=(arcAt M s).role ∧
      row.axis=axis ∧ row.quarter=M.word (arcAt M s).role ∧
      row.positiveHalf=r ∧ row.angle.Mem u ∧ M.target (arcAt M s).role≤row.lowerTarget := by
  have hh := hK s t hst axis haxis hkeep houter r
  obtain ⟨I,hI,hIu⟩ := hh.2.covers hu
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hI
  have hp := hh.1.of_mem hk
  exact ⟨rows.getD k default,list_getD_mem hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,
    hp.2.2.2.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,hIu,hp.2.2.2.2.2.2.2⟩

/-- One shared state/label selection precedes the geometric split. The
outer-endpoint branch keeps the original continuous row application. -/
noncomputable def chargedBound {K : AffineCover} {M : AffineTableMeta} {rows : List AffineTableRow}
    (hK : NumericValid K M rows) (hrows : ∀ r∈rows, r.Claim M)
    (C : BoundaryCycle (M.radius:ℝ)) (F : Frame C) (β : ℝ)
    (hword : ∀ i, (M.word i:ℝ)=(Candidate.word i:ℝ))
    (hcharge : ∀ i, (M.charge i:ℝ)=Candidate.charge β i)
    (hcuts : ∀ i, (M.cuts i).Mem (C.tangent i))
    (hdiff : ∀ i, (M.differenceRange i).Mem (Candidate.delta F.theta i))
    (haxes : ∀ i j, (forwardAxis j).Feasible (C.square i) (C.square (next i)) →
      ForwardAxis.ofIndex j∈M.allowedAxes i) :
    ChargedBound C F β (fun i => (M.target i:ℝ)) := by
  choose selected hrole hcontains hproducts using fun i => K.states.covers hK.2.1 C hcuts i
  refine {label:=fun i => (arcAt M (selected i)).label.eval (C.a i) (C.b i),pair_bound:=?_}
  intro i j hj
  by_cases hcore : (arcAt M (selected i)).outer=false ∧
      (arcAt M (selected (next i))).outer=false
  · have hp := GeometricCoreMarker.pair_bound hK.1 hK.2.2.1 hK.2.2.2.1 C F
      (hrole i) (hrole (next i)) (hcontains i) (hcontains (next i))
      (hproducts i) (hproducts (next i)) hcore.1 hcore.2 j hj
    simpa [chargedCost,frameCharge,Candidate.h,hcharge,
      sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hp
  · have houter : (arcAt M (selected i)).outer=true ∨
        (arcAt M (selected (next i))).outer=true := by
      cases hs : (arcAt M (selected i)).outer <;>
        cases ht : (arcAt M (selected (next i))).outer <;> simp_all
    let axis := ForwardAxis.ofIndex j
    let d := Candidate.delta F.theta i
    let r : Bool := decide (0≤d)
    let u := |d|
    have hdu : Candidate.delta F.theta i=(AnglePolynomial.signQ r:ℝ)*u := by
      dsimp [r,u,d]
      by_cases hd : 0≤Candidate.delta F.theta i <;>
        simp [hd,AnglePolynomial.signQ,abs_of_nonneg,abs_of_neg]
    have hu := K.required_mem hK.1 C F hword hdiff (hrole i) (hcontains i)
      (hcontains (next i)) (hproducts i) (hproducts (next i)) (r:=r) (u:=u) rfl hdu
    have hallowed : axis∈M.allowedAxes (arcAt M (selected i)).role := by
      simpa [axis,hrole] using haxes i j hj
    have hkeep : ¬ GeometricAffine.Excluded M (selected i) (selected (next i)) axis :=
      GeometricAffine.feasible_not_excluded C F (hrole i) (hcontains i) (hcontains (next i))
        (hproducts i) (hproducts (next i)) j hj
    obtain ⟨row,hrow,hs,ht,he,ha,hk,hr,hru,hγ⟩ := row_cover hK.2.2.2.2
      (by rw [hrole,hrole]; rfl) hallowed hkeep houter hu
    have hsdata : row.sourceArc M=arcAt M (selected i) := by
      simp [AffineTableRow.sourceArc,arcAt,hs]
    have htdata : row.targetArc M=arcAt M (selected (next i)) := by
      simp [AffineTableRow.targetArc,arcAt,ht]
    have he' : row.edge=i := he.trans (hrole i)
    have hphi : row.phi u=Candidate.phi F.theta i := by
      rw [AffineTableRow.phi,hk,hrole]
      rw [show row.sign=(AnglePolynomial.signQ r:ℝ) by
        cases r <;> simp [AffineTableRow.sign,hr,AnglePolynomial.signQ]]
      rw [← hdu,hword]
      rfl
    have hdom : row.Domain M (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) u :=
      ⟨by simpa [hsdata] using hcontains i,by simpa [htdata] using hcontains (next i),hru⟩
    have hactual := (F.margin_nonneg_iff i j).mp hj
    have horiginal : 0≤Arithmetic.forwardMargin axis (C.sigma i) (C.sigma (next i))
        (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (Candidate.phi F.theta i) := by
      simpa [forwardMargin_actual,axis,Candidate.margin] using hactual
    have hselected : 0≤Arithmetic.forwardMargin row.axis (row.sourceArc M).sign (row.targetArc M).sign
        (C.a i) (C.b i) (C.a (next i)) (C.b (next i)) (row.phi u) := by
      rw [ha,hsdata,htdata,hphi,
        forwardMargin_congr_products axis (hproducts i) (hproducts (next i))]
      exact horiginal
    have hp := hrows row hrow _ _ _ _ _ hdom hselected
    have htarget : (M.target i:ℝ)≤row.lowerTarget := by
      simpa [hrole] using
        (show (M.target (arcAt M (selected i)).role:ℝ)≤row.lowerTarget by exact_mod_cast hγ)
    have hh := htarget.trans_lt hp
    simpa [chargedCost,frameCharge,Candidate.h,hsdata,htdata,he',hphi,hcharge,
      sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using hh

end SquaresInCircles.Eight.Candidate.GeometricCoreCoverage
