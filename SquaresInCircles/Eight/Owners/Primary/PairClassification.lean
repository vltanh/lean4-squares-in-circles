module

public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.Negative.ContactGeometry
public import SquaresInCircles.Eight.Owners.Negative.PrimaryPreprocessing
public import SquaresInCircles.Eight.Owners.Positive.SplitCalculus
public import SquaresInCircles.Eight.Words.Wrong.WordCircleSupport

/-!
# Eight squares: local classification of the G primary pair

Every local G pair (`GPairInput`), for all signed totals, signs of the errors and tangents, radial
kinds and weak ties, has an output at the same `q` (`preprocess_G_pair`): a point with its two
feasible projections on HG and GA (`GPairOutput`). Its four alternatives are the hard owner GA0, a
positive canceling primary, an aligned negative primary, and the nearest-axis diagonal. The
diagonal is excluded by the global quarter-word argument, not by the two local inequalities. The
same holds on the side of T after reversal (`TPairInput`, `GPairOutput.reflectToT`,
`preprocess_T_pair`).
-/

section
/-!
## Same-radius positive-total primary-pair reduction, with all error signs

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate

/-- The local data of a G pair: H, G, A sorted, contained and off the core, G on the boundary and A
on the circle, the normal signs of H and A, errors at most `frameCap`, a zero owner of HG with its
sign implication, and GA1. Nothing about E or the opposite side enters. -/
structure GPairInput (q : ℝ) (H G A : SignedPoint) (θH θG θA : ℝ) where
  H_sorted : H.Sorted
  G_sorted : G.Sorted
  A_sorted : A.Sorted
  H_contained : H.Contained q
  G_contained : G.Contained q
  A_contained : A.Contained q
  H_core : H.AvoidsCore
  G_core : G.AvoidsCore
  A_core : A.AvoidsCore
  G_boundary : G.Boundary q
  A_outer : A.Outer q
  H_normal : 0≤H.y
  A_normal : 0≤A.y
  HG_error : |θG-θH|≤frameCap
  GA_error : |θA-θG|≤frameCap
  HA_error : |θA-θH|≤frameCap
  owner : Fin 4
  owner_allowed : owner=0 ∨ owner=2
  HG : zeroFeasible H G (θG-θH) owner
  GA : quarterFeasible G A (θA-θG) 1
  canceling_normal : owner=2 → G.y<0

/-- The output of a G pair: a point at the same `q` with feasible owners of HG and GA, its frame at
the original one or between those of H and A, and one of the four terminal alternatives. -/
structure GPairOutput (q : ℝ) (H A : SignedPoint) (θH θG θA : ℝ) where
  point : SignedPoint
  theta : ℝ
  hgOwner : Fin 4
  gaOwner : Fin 4
  hg_allowed : hgOwner=0 ∨ hgOwner=2
  ga_allowed : gaOwner=0 ∨ gaOwner=1
  sorted : point.Sorted
  contained : point.Contained q
  avoids : point.AvoidsCore
  boundary : point.Boundary q
  HG : zeroFeasible H point (theta-θH) hgOwner
  GA : quarterFeasible point A (θA-theta) gaOwner
  canceling_normal : hgOwner=2 → point.y<0
  frame_range : theta=θG ∨ theta∈Icc (min θH θA) (max θH θA)
  terminal : gaOwner=0 ∨
    (gaOwner=1 ∧ hgOwner=2 ∧ 0<θA-theta) ∨
    (gaOwner=1 ∧ theta=θH ∧ θA-theta<0 ∧ point.y<0) ∨
    point.y= -point.a

namespace GPairOutput

def original_hard {q θH θG θA : ℝ} {H G A : SignedPoint}
    (I : GPairInput q H G A θH θG θA)
    (h : quarterFeasible G A (θA-θG) 0) :
    GPairOutput q H A θH θG θA where
  point := G
  theta := θG
  hgOwner := I.owner
  gaOwner := 0
  hg_allowed := I.owner_allowed
  ga_allowed := Or.inl rfl
  sorted := I.G_sorted
  contained := I.G_contained
  avoids := I.G_core
  boundary := I.G_boundary
  HG := I.HG
  GA := h
  canceling_normal := I.canceling_normal
  frame_range := Or.inl rfl
  terminal := Or.inl rfl

def original_positive {q θH θG θA : ℝ} {H G A : SignedPoint}
    (I : GPairInput q H G A θH θG θA)
    (hj : I.owner=2) (hpositive : 0<θA-θG) :
    GPairOutput q H A θH θG θA where
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
  terminal := Or.inr (Or.inl ⟨rfl,hj,hpositive⟩)

/-- An output from a negative endpoint: the two alignments of the negative entry are classified by
their error, zero error being a hard tie, and the transverse owner may be selected again. -/
theorem of_negative {q θH θG θA : ℝ} {H A : SignedPoint}
    (O : NegativeGEndpoint q H A θH θA θG) :
    Nonempty (GPairOutput q H A θH θG θA) := by
  have hframe : O.theta∈Icc (min θH θA) (max θH θA) := by
    rcases O.endpoint with he | he
    · rw [he]; exact ⟨min_le_right _ _,le_max_right _ _⟩
    · rw [he]; exact ⟨min_le_left _ _,le_max_left _ _⟩
  by_cases hhard : quarterFeasible O.point A (θA-O.theta) 0
  · exact ⟨{
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
      terminal := Or.inl rfl }⟩
  have hH : O.theta=θH := by
    rcases O.endpoint with he | he
    · exact (hhard (O.hard_at_A he)).elim
    · exact he
  have hzero : zeroFeasible H O.point 0 2 := by
    have hh := O.HG
    rw [hH,sub_self] at hh
    rcases O.owner_allowed with he | he
    · exact (zero_owner_tie _ _).1 (by simpa [he] using hh)
    · simpa [he] using hh
  have hne : θA-O.theta≠0 := by
    intro he
    apply hhard
    rw [he]
    exact (quarter_low_tie _ _).2 (by simpa [he] using O.GA)
  refine ⟨{
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
    terminal := ?_ }⟩
  rcases lt_or_gt_of_ne hne with hn | hp
  · exact Or.inr (Or.inr (Or.inl ⟨rfl,hH,hn,O.normal⟩))
  · exact Or.inr (Or.inl ⟨rfl,rfl,hp⟩)

/-- At positive total the two frame alignments are hard or positive-terminal; the diagonal stays
the fourth alternative. -/
theorem of_positive_endpoint {q θH θG θA : ℝ} {H A : SignedPoint}
    (O : GPositiveEndpoint q H A θH θA)
    (hH : H.y<9/10) (ht : 0<θA-θH) :
    Nonempty (GPairOutput q H A θH θG θA) := by
  have hframe : O.theta∈Icc (min θH θA) (max θH θA) := by
    exact ⟨(min_le_left _ _).trans O.theta_mem.1,
      O.theta_mem.2.trans (le_max_right _ _)⟩
  rcases O.endpoint with hA | hHalign | hdiag
  · have hhard : quarterFeasible O.G A (θA-O.theta) 0 := by
      rw [hA,sub_self]
      exact (quarter_low_tie _ _).2 (by simpa [hA] using O.GA)
    exact ⟨{
      point := O.G
      theta := O.theta
      hgOwner := 0
      gaOwner := 0
      hg_allowed := Or.inl rfl
      ga_allowed := Or.inl rfl
      sorted := O.sorted
      contained := O.outer.le
      avoids := O.core
      boundary := Or.inl O.outer
      HG := O.HG
      GA := hhard
      canceling_normal := by intro h; norm_num at h
      frame_range := Or.inr hframe
      terminal := Or.inl rfl }⟩
  · have hHG0 : zeroFeasible H O.G 0 0 := by simpa [hHalign] using O.HG
    have hHG2 : zeroFeasible H O.G (O.theta-θH) 2 := by
      simpa [hHalign] using (zero_owner_tie _ _).1 hHG0
    have hy : O.G.y<0 := by
      have hh : 1≤H.y-O.G.y := by simpa [zeroFeasible,zeroProjection] using hHG0
      linarith
    exact ⟨{
      point := O.G
      theta := O.theta
      hgOwner := 2
      gaOwner := 1
      hg_allowed := Or.inr rfl
      ga_allowed := Or.inr rfl
      sorted := O.sorted
      contained := O.outer.le
      avoids := O.core
      boundary := Or.inl O.outer
      HG := hHG2
      GA := O.GA
      canceling_normal := fun _ => hy
      frame_range := Or.inr hframe
      terminal := Or.inr (Or.inl ⟨rfl,rfl,by rwa [hHalign]⟩) }⟩
  · exact ⟨{
      point := O.G
      theta := O.theta
      hgOwner := 0
      gaOwner := 1
      hg_allowed := Or.inl rfl
      ga_allowed := Or.inr rfl
      sorted := O.sorted
      contained := O.outer.le
      avoids := O.core
      boundary := Or.inl O.outer
      HG := O.HG
      GA := O.GA
      canceling_normal := by intro h; norm_num at h
      frame_range := Or.inr hframe
      terminal := Or.inr (Or.inr (Or.inr hdiag)) }⟩

/-- The hard endpoint on the flat core, which serves both signs of a nonpositive total. -/
def flat_hard {q θH θG θA : ℝ} {H A p : SignedPoint}
    (hs : p.Sorted) (hc : p.Core) (hcircle : p.circle<q)
    (hHG : zeroFeasible H p (θA-θH) 0)
    (hGA : quarterFeasible p A 0 0) :
    GPairOutput q H A θH θG θA where
  point := p
  theta := θA
  hgOwner := 0
  gaOwner := 0
  hg_allowed := Or.inl rfl
  ga_allowed := Or.inl rfl
  sorted := hs
  contained := hcircle.le
  avoids := hc.ge
  boundary := Or.inr hc
  HG := hHG
  GA := by simpa using hGA
  canceling_normal := by intro h; norm_num at h
  frame_range := Or.inr ⟨min_le_right _ _,le_max_right _ _⟩
  terminal := Or.inl rfl

end GPairOutput

/-- An HG0 witness at nonpositive error forces the normal sign `G.y < 0`, from the width and the
bound `H.y < 9/10`. -/
theorem hg0_nonpositive_error_normal {H G : SignedPoint} {d : ℝ}
    (hH : H.y<9/10) (hG : 0<G.a) (hd : |d|≤7/10) (hd0 : d≤0)
    (hHG : zeroFeasible H G d 0) : G.y<0 := by
  have hc := transport_cos_pos hd
  have hsin : Real.sin d≤0 := by
    have hs := (transport_trig_coarse
      (show -d∈Icc 0 (7/10 : ℝ) by
        constructor <;> linarith [(abs_le.mp hd).1])).2.1
    rw [Real.sin_neg] at hs
    linarith
  by_contra! hy
  have hfirst := mul_nonpos_of_nonneg_of_nonpos hG.le hsin
  have hsecond := mul_nonneg hy hc.le
  have hp : edgeWidth d≤H.y+G.a*Real.sin d-G.y*Real.cos d := hHG
  linarith [edgeWidth_ge_one d]

/-- Every local G pair has an output at the same `q`. -/
theorem preprocess_G_pair {q θH θG θA : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (I : GPairInput q H G A θH θG θA) :
    Nonempty (GPairOutput q H A θH θG θA) := by
  by_cases hhard : quarterFeasible G A (θA-θG) 0
  · exact ⟨GPairOutput.original_hard I hhard⟩
  have hnonzero : θA-θG≠0 := by
    intro he
    apply hhard
    rw [he]
    exact (quarter_low_tie _ _).2 (by simpa [he] using I.GA)
  have hHbound : H.y<9/10 := (le_abs_self H.y).trans_lt
    (H.coordinate_bounds I.H_sorted I.H_core I.H_contained hqU).2.2
  have negative_endpoint (hn : θA-θG<0) (hy : G.y≤0) :
      Nonempty (GPairOutput q H A θH θG θA) := by
    obtain ⟨O⟩ := negative_GA_pair_endpoint hqU
      I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
      I.H_core I.G_core I.A_core I.G_boundary I.H_normal hy I.A_normal
      hn I.GA_error (by simpa [abs_sub_comm] using I.HA_error) I.HG_error
      I.owner_allowed I.HG I.GA hhard
    exact GPairOutput.of_negative O
  rcases I.owner_allowed with hj | hj
  · have hHG : zeroFeasible H G (θG-θH) 0 := by simpa [hj] using I.HG
    by_cases htotal : 0<θA-θH
    · obtain ⟨O⟩ := positive_GA_HG_pair hqL hqU
        I.H_sorted I.A_sorted I.G_sorted I.H_normal I.H_contained I.A_outer
        I.G_contained I.G_core hHG I.GA I.GA_error I.HG_error
        ⟨htotal,(abs_le.mp I.HA_error).2⟩
      exact GPairOutput.of_positive_endpoint O hHbound htotal
    · have htotal0 : θA≤θH := by linarith
      rcases lt_or_gt_of_ne hnonzero with hnegative | hpositive
      · by_cases hy : G.y≤0
        · exact negative_endpoint hnegative hy
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
            have h1 := (abs_le.mp I.GA_error).1
            simp only [frameCap] at h1
            linarith
          have hprimary : quarterFeasible G A (-(v+s)) 1 := by
            convert I.GA using 1
            dsimp [v,s]
            ring
          obtain ⟨hs',hc',hcircle,hHG',hGA',hGA1',hstrict⟩ :=
            wrong_sign_nonpositive_total_transport hqU
              I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
              I.H_core I.G_core I.A_core I.H_normal hy0 I.A_normal hs hv hsumBound
              hHG hprimary
          have htransverse : zeroFeasible H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0 := by
            convert hHG' using 1
            dsimp [s]
            ring
          exact ⟨GPairOutput.flat_hard hs' hc' hcircle htransverse hGA'⟩
      · have hHGneg : θG-θH≤0 := by linarith
        have hy := (hg0_nonpositive_error_normal hHbound I.G_sorted.1
          I.HG_error hHGneg hHG).le
        let s := θH-θA
        let x := θA-θG
        have hs : 0≤s := by dsimp [s]; linarith
        have hx : 0<x := hpositive
        have hsum : s+x=θH-θG := by dsimp [s,x]; ring
        have hsumBound : s+x≤7/10 := by
          rw [hsum]
          have h1 := (abs_le.mp I.HG_error).1
          simp only [frameCap] at h1
          linarith
        have htransverse : zeroFeasible H G (-(s+x)) 0 := by
          convert hHG using 1
          dsimp [s,x]
          ring
        obtain ⟨hs',hc',havoid,hcircle,hGA',hGA1',hstrict⟩ :=
          positive_ga1_nonpositive_total_transport hqU
            I.H_sorted I.G_sorted I.A_sorted I.H_contained I.G_contained I.A_contained
            I.H_core I.G_core I.A_core I.H_normal hy I.A_normal hx hs hsumBound
            htransverse I.GA
        have hHG' : zeroFeasible H (SignedPoint.flat (-(A.a-1))) (θA-θH) 0 := by
          have hh : zeroFeasible H (SignedPoint.flat (-(A.a-1))) (-s) 0 := hstrict.le
          convert hh using 1
          dsimp [s]
          ring
        exact ⟨GPairOutput.flat_hard hs' hc' hcircle hHG' hGA'⟩
  · rcases lt_or_gt_of_ne hnonzero with hn | hp
    · exact negative_endpoint hn (I.canceling_normal hj).le
    · exact ⟨GPairOutput.original_positive I hj hp⟩

/-- The local G pair of a boundary input with a GA1 witness. -/
def SignedCycle.BoundaryInput.gPair {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hGA : I.cycle.Feasible G 1) :
    GPairInput q (I.cycle.point H) (I.cycle.point G) (I.cycle.point A)
      (I.cycle.theta H) (I.cycle.theta G) (I.cycle.theta A) where
  H_sorted := I.necessary.sorted H
  G_sorted := I.necessary.sorted G
  A_sorted := I.necessary.sorted A
  H_contained := I.necessary.contained H
  G_contained := I.necessary.contained G
  A_contained := I.necessary.contained A
  H_core := I.necessary.core H
  G_core := I.necessary.core G
  A_core := I.necessary.core A
  G_boundary := I.radial G
  A_outer := I.anchors_outer A (by simp [H,A,B,D])
  H_normal := I.anchors_normal.H_nonneg
  A_normal := I.anchors_normal.A_nonneg
  HG_error := I.necessary.spread G H
  GA_error := I.necessary.spread A G
  HA_error := I.necessary.spread A H
  owner := I.witnesses.owner H
  owner_allowed := by simpa [SignedCycle.normalOwners,H] using I.witnesses.allowed H
  HG := by
    have h := I.witnesses.feasible H
    change 0≤I.cycle.slack H (I.witnesses.owner H) at h
    simpa [SignedCycle.slack,SignedCycle.edge,word,delta,next,H,G,zeroFeasible]
      using sub_nonneg.mp h
  GA := by
    change 0≤I.cycle.slack G 1 at hGA
    simpa [SignedCycle.slack,SignedCycle.edge,word,delta,next,G,A,quarterFeasible]
      using sub_nonneg.mp hGA
  canceling_normal := I.zero_signs.HG_canceling

/-- The local data of a T pair: the same problem after reversal, with the signs of its two errors;
E does not enter. -/
abbrev TPairInput (q : ℝ) (B T D : SignedPoint) (θB θT θD : ℝ) :=
  GPairInput q D.reflect T.reflect B.reflect (-θD) (-θT) (-θB)

structure TPairOutput (q : ℝ) (B D : SignedPoint) (θB θT θD : ℝ) where
  point : SignedPoint
  theta : ℝ
  btOwner : Fin 4
  tdOwner : Fin 4
  bt_allowed : btOwner=2 ∨ btOwner=3
  td_allowed : tdOwner=0 ∨ tdOwner=2
  sorted : point.Sorted
  contained : point.Contained q
  avoids : point.AvoidsCore
  boundary : point.Boundary q
  BT : quarterFeasible B point (theta-θB) btOwner
  TD : zeroFeasible point D (θD-theta) tdOwner
  canceling_normal : tdOwner=0 → 0<point.y
  frame_range : theta=θT ∨ theta∈Icc (min θB θD) (max θB θD)
  terminal : btOwner=2 ∨
    (btOwner=3 ∧ tdOwner=0 ∧ 0<theta-θB) ∨
    (btOwner=3 ∧ theta=θD ∧ theta-θB<0 ∧ 0<point.y) ∨
    point.y=point.a

/-- The output of a T pair from the reflected G pair: the weak owners and the terminal case carry
over, the transverse sign implication included. -/
def GPairOutput.reflectToT {q θB θT θD : ℝ} {B D : SignedPoint}
    (O : GPairOutput q D.reflect B.reflect (-θD) (-θT) (-θB)) :
    TPairOutput q B D θB θT θD where
  point := O.point.reflect
  theta := -O.theta
  btOwner := reflectedOwner O.gaOwner
  tdOwner := reflectedOwner O.hgOwner
  bt_allowed := by rcases O.ga_allowed with h | h <;> simp [h,reflectedOwner]
  td_allowed := by rcases O.hg_allowed with h | h <;> simp [h,reflectedOwner]
  sorted := by simpa using O.sorted
  contained := by simpa using O.contained
  avoids := by simpa using O.avoids
  boundary := by simpa using O.boundary
  BT := by
    have h := (quarterFeasible_reflect O.point B.reflect (-θB-O.theta) O.gaOwner).2 O.GA
    simpa [sub_eq_add_neg,add_comm] using h
  TD := by
    have h := (zeroFeasible_reflect D.reflect O.point (O.theta-(-θD)) O.hgOwner).2 O.HG
    simpa [sub_eq_add_neg,add_comm] using h
  canceling_normal := by
    intro h
    have hj : O.hgOwner=2 := by
      rcases O.hg_allowed with hj | hj
      · simp [hj,reflectedOwner] at h
      · exact hj
    simpa [SignedPoint.reflect] using neg_pos.mpr (O.canceling_normal hj)
  frame_range := by
    rcases O.frame_range with h | h
    · left; linarith
    · right
      rcases le_total θB θD with hord | hord
      · simp only [min_eq_left hord,max_eq_right hord]
        have hneg : -θD≤ -θB := by linarith
        simp only [min_eq_left hneg,max_eq_right hneg,mem_Icc] at h
        constructor <;> linarith
      · simp only [min_eq_right hord,max_eq_left hord]
        have hneg : -θB≤ -θD := by linarith
        simp only [min_eq_right hneg,max_eq_left hneg,mem_Icc] at h
        constructor <;> linarith
  terminal := by
    rcases O.terminal with h | ⟨hg,hh,hpos⟩ | ⟨hg,he,hneg,hy⟩ | hdiag
    · left; simp [h,reflectedOwner]
    · right; left
      exact ⟨by simp [hg,reflectedOwner],by simp [hh,reflectedOwner],by linarith⟩
    · right; right; left
      exact ⟨by simp [hg,reflectedOwner],by linarith,by linarith,
        by simpa [SignedPoint.reflect] using neg_pos.mpr hy⟩
    · right; right; right
      dsimp [SignedPoint.reflect]
      linarith

theorem preprocess_T_pair {q θB θT θD : ℝ} {B T D : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (I : TPairInput q B T D θB θT θD) :
    Nonempty (TPairOutput q B D θB θT θD) := by
  obtain ⟨O⟩ := preprocess_G_pair hqL hqU I
  exact ⟨O.reflectToT⟩

/-- The local T pair of a boundary input with a BT3 witness; no sign of E is involved. -/
def SignedCycle.BoundaryInput.tPair {q : ℝ} (I : SignedCycle.BoundaryInput q)
    (hBT : I.cycle.Feasible B 3) :
    TPairInput q (I.cycle.point B) (I.cycle.point T) (I.cycle.point D)
      (I.cycle.theta B) (I.cycle.theta T) (I.cycle.theta D) where
  H_sorted := by simpa using I.necessary.sorted D
  G_sorted := by simpa using I.necessary.sorted T
  A_sorted := by simpa using I.necessary.sorted B
  H_contained := by simpa using I.necessary.contained D
  G_contained := by simpa using I.necessary.contained T
  A_contained := by simpa using I.necessary.contained B
  H_core := by simpa using I.necessary.core D
  G_core := by simpa using I.necessary.core T
  A_core := by simpa using I.necessary.core B
  G_boundary := by simpa using I.radial T
  A_outer := by simpa using I.anchors_outer B (by simp [H,A,B,D])
  H_normal := by
    simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.D_nonpos
  A_normal := by
    simpa [SignedPoint.reflect] using neg_nonneg.mpr I.anchors_normal.B_nonpos
  HG_error := by simpa only [neg_sub_neg] using I.necessary.spread D T
  GA_error := by simpa only [neg_sub_neg] using I.necessary.spread T B
  HA_error := by simpa only [neg_sub_neg] using I.necessary.spread D B
  owner := reflectedOwner (I.witnesses.owner T)
  owner_allowed := by
    have h : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
      simpa [SignedCycle.normalOwners,T] using I.witnesses.allowed T
    rcases h with h | h <;> simp [h,reflectedOwner]
  HG := by
    have h : zeroFeasible (I.cycle.point T) (I.cycle.point D)
        (I.cycle.theta D-I.cycle.theta T) (I.witnesses.owner T) := by
      have hh := I.witnesses.feasible T
      change 0≤I.cycle.slack T (I.witnesses.owner T) at hh
      simpa [SignedCycle.slack,SignedCycle.edge,word,delta,next,T,D,zeroFeasible]
        using sub_nonneg.mp hh
    simpa only [neg_sub_neg] using (zeroFeasible_reflect _ _ _ _).2 h
  GA := by
    have h : quarterFeasible (I.cycle.point B) (I.cycle.point T)
        (I.cycle.theta T-I.cycle.theta B) 3 := by
      change 0≤I.cycle.slack B 3 at hBT
      simpa [SignedCycle.slack,SignedCycle.edge,word,delta,next,B,T,quarterFeasible]
        using sub_nonneg.mp hBT
    have h' := (quarterFeasible_reflect _ _ _ 3).2 h
    simp only [reflectedOwner] at h'
    convert h' using 1
    · ring
    · rfl
  canceling_normal := by
    intro h
    have hj : I.witnesses.owner T=0 := by
      have hallowed : I.witnesses.owner T=0 ∨ I.witnesses.owner T=2 := by
        simpa [SignedCycle.normalOwners,T] using I.witnesses.allowed T
      rcases hallowed with hj | hj
      · exact hj
      · simp [hj,reflectedOwner] at h
    simpa [SignedPoint.reflect] using neg_neg_of_pos (I.zero_signs.TD_canceling hj)

end SquaresInCircles.Eight
end
end
end
