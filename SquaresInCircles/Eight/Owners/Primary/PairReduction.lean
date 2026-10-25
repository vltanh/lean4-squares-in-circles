module

public import SquaresInCircles.Eight.Owners.Positive.PairEndpoints
public import SquaresInCircles.Eight.Owners.Negative.ContactGeometry

/-!
# Eight squares: same-radius positive-total primary-pair reduction, with all error signs

The scalar endpoint theorem combines nonnegative errors
with both signed-cancellation orders. The G and T adapters retain actual
signed tangent coordinates and both original projected inequalities.

The sole local alternative not an alignment is an actual nearest-axis tie.
It is returned explicitly, rather than discarded by a local bound. Its
exclusion belongs to the global quarter-word argument.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate
namespace PairedPrimary

theorem positive_total_endpoint {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (hD : 0≤D ∧ D≤diagonalCoordinate q)
    (hu : |u|≤7/10) (hv : |v|≤7/10)
    (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hs : p.Sorted) (hcore : p.AvoidsCore) (hc : p.Contained q)
    (h₁ : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (h₂ : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    Nonempty (Endpoint q B D (u+v)) := by
  by_cases hu0 : 0≤u
  · by_cases hv0 : 0≤v
    · exact nonnegative_pair_endpoint hqL hqU hB hD.2 hu0 hv0 ht0 ht hs hc h₁ h₂
    · have hvneg : v<0 := lt_of_not_ge hv0
      have huPos : 0<u := by linarith
      have hDa : D≤axisCoordinate q := by
        have hdiag : diagonalCoordinate q≤axisCoordinate q := by
          have hp := SignedPoint.outerAt_spec hqL
            (show |(0:ℝ)|≤diagonalCoordinate q by
              have h := (uniform_circle_reserves hqL hqU).1
              norm_num; linarith)
          exact (SignedPoint.outer_bounds hp.1 hp.2.1).1.trans
            (SignedPoint.outer_bounds hp.1 hp.2.1).2.2
        exact hD.2.trans hdiag
      obtain ⟨p',hps,hpo,hpc,hsecond,hfirst⟩ := NegativeContact.second_negative_alignment
        hqL hqU ⟨hD.1,hDa⟩ ⟨huPos,(abs_le.mp hu).2⟩
        ⟨by linarith [(abs_le.mp hv).1],hvneg⟩ ht0 hs hcore hc h₁ h₂
      refine ⟨⟨p',u+v,⟨ht0.le,le_rfl⟩,hps,hpo,hpc,hfirst,?_,Or.inr (Or.inl rfl)⟩⟩
      simpa using hsecond.ge
  · have huneg : u<0 := lt_of_not_ge hu0
    have hvpos : 0<v := by linarith
    have hB0 : 0≤B := by
      have hdiag := (uniform_circle_reserves hqL hqU).1
      linarith [hB.1]
    obtain ⟨p',hps,hpo,hpc,hfirst,hsecond⟩ := NegativeContact.first_negative_alignment
      hqL hqU ⟨hB0,hB.2⟩ ⟨by linarith [(abs_le.mp hu).1],huneg⟩
      ⟨hvpos,(abs_le.mp hv).2⟩ ht0 hs hcore hc h₁ h₂
    refine ⟨⟨p',0,⟨le_rfl,ht0.le⟩,hps,hpo,hpc,?_,?_,Or.inl rfl⟩⟩
    · simpa using hfirst.ge
    · simpa using hsecond

end PairedPrimary

/-- G-only positive-total output, stated on its actual neighboring squares. -/
structure GPositiveEndpoint (q : ℝ) (H A : SignedPoint) (θH θA : ℝ) where
  G : SignedPoint
  theta : ℝ
  theta_mem : θH≤theta ∧ theta≤θA
  sorted : G.Sorted
  outer : G.Outer q
  core : G.AvoidsCore
  HG : zeroFeasible H G (theta-θH) 0
  GA : quarterFeasible G A (θA-theta) 1
  endpoint : theta=θA ∨ theta=θH ∨ G.y= -G.a

theorem positive_GA_HG_pair {q θH θG θA : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hH : H.Sorted) (hA : A.Sorted) (hG : G.Sorted)
    (hHnormal : 0≤H.y) (hHcircle : H.Contained q) (hAouter : A.Outer q)
    (hGcircle : G.Contained q) (hGcore : G.AvoidsCore)
    (hHG : zeroFeasible H G (θG-θH) 0)
    (hGA : quarterFeasible G A (θA-θG) 1)
    (hfirst : |θA-θG|≤7/10) (hsecond : |θG-θH|≤7/10)
    (ht : 0<θA-θH ∧ θA-θH≤7/10) :
    Nonempty (GPositiveEndpoint q H A θH θA) := by
  have hAs := SignedPoint.outer_bounds hA hAouter
  have hHs := SignedPoint.contained_minor_le_diagonal hH hHcircle
  have hsum : (θA-θG)+(θG-θH)=θA-θH := by ring
  obtain ⟨E⟩ := PairedPrimary.positive_total_endpoint
    (p := G.reflect) (B := A.a) (D := H.y)
    hqL hqU ⟨hAs.1,hAs.2.2⟩
    ⟨hHnormal,by simpa [abs_of_nonneg hHnormal] using hHs⟩
    hfirst hsecond (by rw [hsum]; exact ht.1) (by rw [hsum]; exact ht.2)
    ((SignedPoint.reflect_sorted G).mpr hG)
    ((SignedPoint.reflect_avoidsCore G).mpr hGcore)
    ((SignedPoint.reflect_contained G q).mpr hGcircle)
    (by
      have h : edgeWidth (θA-θG)≤A.a+G.a*Real.sin (θA-θG)+G.y*Real.cos (θA-θG) := hGA
      show edgeWidth (θA-θG)≤A.a+G.reflect.a*Real.sin (θA-θG)-G.reflect.y*Real.cos (θA-θG)
      simp only [SignedPoint.reflect]
      linarith)
    (by
      have h : edgeWidth (θG-θH)≤H.y+G.a*Real.sin (θG-θH)-G.y*Real.cos (θG-θH) := hHG
      show edgeWidth (θG-θH)≤G.reflect.a*Real.sin (θG-θH)+G.reflect.y*Real.cos (θG-θH)+H.y
      simp only [SignedPoint.reflect]
      linarith)
  have E' : PairedPrimary.Endpoint q A.a H.y (θA-θH) := hsum ▸ E
  have hm := E'.first_mem
  refine ⟨⟨E'.point.reflect,θA-E'.firstError,⟨by linarith [hm.2],by linarith [hm.1]⟩,
    (SignedPoint.reflect_sorted E'.point).mpr E'.sorted,
    (SignedPoint.reflect_outer E'.point q).mpr E'.outer,
    (SignedPoint.reflect_avoidsCore E'.point).mpr E'.avoids_core,?_,?_,?_⟩⟩
  · have h := E'.second_feasible
    rw [show θA-E'.firstError-θH=θA-θH-E'.firstError by ring]
    show edgeWidth (θA-θH-E'.firstError)≤H.y+E'.point.reflect.a*Real.sin (θA-θH-E'.firstError)-
      E'.point.reflect.y*Real.cos (θA-θH-E'.firstError)
    simp only [SignedPoint.reflect]
    linarith
  · have h := E'.first_feasible
    rw [show θA-(θA-E'.firstError)=E'.firstError by ring]
    show edgeWidth E'.firstError≤A.a+E'.point.reflect.a*Real.sin E'.firstError+
      E'.point.reflect.y*Real.cos E'.firstError
    simp only [SignedPoint.reflect]
    linarith
  · rcases E'.endpoint with he | he | he
    · left
      linarith
    · right
      left
      linarith
    · right
      right
      simp only [SignedPoint.reflect]
      linarith

end SquaresInCircles.Eight