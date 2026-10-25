module

public import SquaresInCircles.Eight.Owners.All.HighBridgeTransfer
public import SquaresInCircles.Eight.Owners.All.HighCycleComponents
public import SquaresInCircles.Eight.Owners.All.HighNegativeOuter
public import SquaresInCircles.Eight.Owners.BT.ReturnScalar
public import SquaresInCircles.Eight.Owners.BT.CoreDE3Polynomial
public import SquaresInCircles.Eight.Owners.BT.ErrorComparisons
public import SquaresInCircles.Eight.Owners.Zero.SourceOuter

/-!
# Eight squares: the core endpoint and the two prefix circles

The marker of a core E pays its DE3 endpoint term exactly (`core_endpoint_marker`). The support
forces of T and D then bound the tail by the concentrated scalar `reduced`, for either owner of TD
and with no sign restriction on the forces (`support`).
-/

section
/-!
## Concentrating the two core-E prefix placements

The tail of the core-E negative-DE3 path is at least the smaller of its two saturated placements
`first` and `last` (`concentrated_lower`). For owner `0` of TD the tail is the split `split`,
concave by the concavity of the norm for arbitrary positive coefficients (`split_concave`); owner
`2` uses the weighted cosine comparison. The prefix multiplier stays fixed in each comparison.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open FrameCircleArc

def tail (second : Bool) (e c r s t : ℝ) : ℝ :=
  Real.pi-(r+s)-t+(3/2)*kappa+c+e+kappa*Real.cos r+c*Real.cos s+
    (e/2)*Real.cos t+e*(13/12)*Real.sin t-
      R*(if second then tailNorm kappa c (r+s)+tailNorm e c 0
        else tailNorm kappa c r+tailNorm e c s)

def split (e c r s t : ℝ) : ℝ :=
  Real.pi-(r+s)-t+(3/2)*kappa+c+e+(e/2)*Real.cos t+e*(13/12)*Real.sin t+
    normCos kappa c r+normCos c e s

theorem split_concave {e c p t : ℝ} (he : 0<e) (hc : 0<c)
    (hp : p∈Icc 0 frameCap) : ConcaveOn ℝ (Icc 0 p) (fun r => split e c r (p-r) t) := by
  have hfirst := (normCos_concave (a := kappa) (by norm_num [kappa]) hc).subset (Icc_subset_Icc le_rfl hp.2) (convex_Icc 0 p)
  have hlast := concave_affine_argument (normCos_concave hc he)
    (a := -1) (b := p) (l := 0) (u := p)
    (fun r hr => ⟨by linarith [hr.2],by linarith [hp.2,hr.1]⟩)
  have hconstant := affine_concave 0
    (Real.pi-p-t+(3/2)*kappa+c+e+(e/2)*Real.cos t+e*(13/12)*Real.sin t) 0 p
  convert (hconstant.add hfirst).add hlast using 1
  funext r
  dsimp [split]
  rw [show (-1:ℝ)*r+p=p-r by ring]
  ring

theorem split_zero (p t e : ℝ) : split e (weight p) 0 p t=last p t e := by
  dsimp [split,last,normCos]
  rw [tailNorm_comm (weight p) e p]
  simp only [Real.cos_zero,mul_one]
  ring

theorem split_last (p t e : ℝ) : split e (weight p) p 0 t=first p t e := by
  dsimp [split,first,normCos]
  rw [tailNorm_comm (weight p) e 0]
  simp only [Real.cos_zero,mul_one]
  ring

theorem tail_false_split (e c r s t : ℝ) : tail false e c r s t=split e c r s t := by
  dsimp [tail,split,normCos]
  rw [tailNorm_comm c e s]
  ring

theorem concentrated_lower (second : Bool) {r s t e : ℝ}
    (hr : 0≤r) (hs : 0≤ s) (hcap : r+s≤frameCap) (he : 0<e) :
    min (first (r+s) t e) (last (r+s) t e)≤tail second e (weight (r+s)) r s t := by
  have hp : r+s∈Icc 0 frameCap := ⟨add_nonneg hr hs,hcap⟩
  have hc := weight_pos hp
  cases second with
  | false =>
      have hconc := split_concave (t := t) he hc hp
      have hm := hconc.min_le_of_mem_Icc
        (show (0:ℝ)∈Icc 0 (r+s) from ⟨le_rfl,add_nonneg hr hs⟩)
        (show r+s∈Icc 0 (r+s) from ⟨add_nonneg hr hs,le_rfl⟩)
        (show r∈Icc 0 (r+s) from ⟨hr,by linarith⟩)
      simp only [sub_zero,sub_self] at hm
      rw [split_zero,split_last,min_comm] at hm
      rw [tail_false_split]
      simpa only [show r+s-r=s by ring] using hm
  | true =>
      have hcos := cosine_concentration hc.le (weight_bounds hp).2.2
        (show s∈Icc 0 frameCap from ⟨hs,by linarith⟩)
        (show r∈Icc 0 frameCap from ⟨hr,by linarith⟩)
      rw [add_comm s r] at hcos
      have hfirst : first (r+s) t e≤tail true e (weight (r+s)) r s t := by
        dsimp [first,tail]
        linarith only [hcos]
      exact (min_le_left _ _).trans hfirst

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end

section
/-!
## Keeping the negative tail errors

Positive errors are removed inside the dual expressions only: the dual terms at an error `d` are
at least their values at `retainedNegative d = -max (-d) 0` (`retain_zero`, `retain_BT0`,
`retain_DE2`, `retain_DE3`). A negative DE3 projection onto an outer target is dominated by the
DE2 projection on the same states (`negative_DE3_projection`); no frame or state is changed.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def quarterDual (s t : State) (j : Fin 4) (d lambda : ℝ) : ℝ :=
  d+lambda*(GlobalOuterAnchor.width d-projection true s t d j)

theorem negative_part_range {d : ℝ} (hd : |d|≤frameCap) :
    max (-d) 0∈Icc 0 frameCap := by
  exact ⟨le_max_right _ _,max_le ((neg_le_abs d).trans hd) (by norm_num [frameCap])⟩

theorem retained_of_nonnegative {d : ℝ} (hd : 0≤d) : retainedNegative d=0 := by
  simp [retainedNegative,max_eq_right (by linarith : -d≤0)]

theorem retained_of_nonpositive {d : ℝ} (hd : d≤0) : retainedNegative d=d := by
  simp [retainedNegative,max_eq_left (by linarith : 0≤-d)]

theorem zeroDual_zero (s t : State) (primary : Bool) (lambda : ℝ) :
    zeroDual primary s t 0 lambda=lambda*(1-transverse s+transverse t) := by
  have hw : GlobalOuterAnchor.width 0=1 := by norm_num [GlobalOuterAnchor.width]
  have hp : projection false s t 0 (leftOwner primary)=transverse s-transverse t := by
    cases primary <;> simp [projection,leftOwner]
  rw [zeroDual,hw,hp]
  ring

theorem quarterDual_zero (s t : State) (j : Fin 4) (lambda : ℝ) :
    quarterDual s t j 0 lambda=lambda*(1-projection true s t 0 j) := by
  simp [quarterDual,GlobalOuterAnchor.width]

theorem retain_zero (s t : State) (primary : Bool) {d lambda : ℝ}
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa) :
    zeroDual primary s t (retainedNegative d) lambda≤zeroDual primary s t d lambda := by
  rcases le_total 0 d with hp | hn
  · rw [retained_of_nonnegative hp,zeroDual_zero]
    exact positive_zero_delete s t primary hl hlu ⟨hp,(le_abs_self d).trans hd⟩
  · rw [retained_of_nonpositive hn]

theorem retain_BT0 (s t : State) {d lambda : ℝ}
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa) :
    quarterDual s t 0 (retainedNegative d) lambda≤quarterDual s t 0 d lambda := by
  rcases le_total 0 d with hp | hn
  · rw [retained_of_nonnegative hp,quarterDual_zero]
    exact positive_BT0_delete s t hl hlu ⟨hp,(le_abs_self d).trans hd⟩
  · rw [retained_of_nonpositive hn]

theorem retain_DE2 (s t : State) {d lambda : ℝ}
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa) :
    quarterDual s t 2 (retainedNegative d) lambda≤quarterDual s t 2 d lambda := by
  rcases le_total 0 d with hp | hn
  · rw [retained_of_nonnegative hp,quarterDual_zero]
    exact positive_DE2_delete s t hl hlu ⟨hp,(le_abs_self d).trans hd⟩
  · rw [retained_of_nonpositive hn]

theorem negative_DE3_projection (s t : State)
    (hs : transverse s≤0) (ht : transverse t≤0) (htOuter : t.branch.type≠0)
    {z : ℝ} (hz : z∈Icc 0 frameCap) :
    projection true s t (-z) 3≤projection true s t (-z) 2 := by
  have hh := GlobalAllHigh.negative_outer_projection_comparison s t htOuter hz
  have hsy : transverse s= -s.b := transverse_nonpos_eq s hs
  have hty : transverse t= -t.b := transverse_nonpos_eq t ht
  dsimp [projection]
  rw [hsy,hty]
  simp only [Real.cos_neg,Real.sin_neg]
  linarith only [hh]

theorem retain_DE3 (s t : State) {d lambda : ℝ}
    (hs : transverse s≤0) (ht : transverse t≤0)
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa)
    (hordinary : 0≤d ∨ t.branch.type≠0) :
    quarterDual s t 2 (retainedNegative d) lambda≤quarterDual s t 3 d lambda := by
  rcases le_total 0 d with hp | hn
  · rw [retained_of_nonnegative hp,quarterDual_zero]
    exact positive_DE3_delete s t hl hlu ⟨hp,(le_abs_self d).trans hd⟩
  · by_cases hz : d=0
    · subst d
      simp [retainedNegative,quarterDual,projection,GlobalOuterAnchor.width]
    · have htOuter : t.branch.type≠0 := by
        rcases hordinary with hp | ho
        · exact False.elim (hz (le_antisymm hn hp))
        · exact ho
      have hp := negative_DE3_projection s t hs ht htOuter
        (show -d∈Icc 0 frameCap from ⟨by linarith,(neg_le_abs d).trans hd⟩)
      simp only [neg_neg] at hp
      have hm := mul_le_mul_of_nonneg_left hp hl
      rw [retained_of_nonpositive hn]
      dsimp [quarterDual]
      linarith

/-- For an owner `j ∈ {2, 3}` of DE, the dual term at `d` is at least the DE2 term at
`retainedNegative d`, unless `j = 3`, `d < 0` and the target is on the core, which is the case of
the core-E tail. This includes both owners at zero error and every DE2 witness. -/
theorem retain_DE (s t : State) (j : Fin 4) {d lambda : ℝ}
    (hs : transverse s≤0) (ht : transverse t≤0) (hj : j=2 ∨ j=3)
    (hd : |d|≤frameCap) (hl : 0≤lambda) (hlu : lambda≤kappa)
    (hordinary : j=2 ∨ 0≤d ∨ t.branch.type≠0) :
    quarterDual s t 2 (retainedNegative d) lambda≤quarterDual s t j d lambda := by
  rcases hj with rfl | rfl
  · exact retain_DE2 s t hd hl hlu
  · apply retain_DE3 s t hs ht hd hl hlu
    rcases hordinary with hh | hh
    · norm_num at hh
    · exact hh

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## The two original circles in the DE2 tail

The exact signed projections cancel B and the linear A charge.  The
remaining T and D forces have the two radicals already bounded by the
continuous tail theorem.  Their components may have either sign.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

def tailChart : Fin 4→Fin 3 := ![0,0,1,2]

theorem tailChart_weight (i : Fin 4) : (TailPolynomial.e (tailChart i):ℝ)=tailWeight i := by
  fin_cases i <;> norm_num [tailChart,TailPolynomial.e,tailWeight]

theorem tailChart_margin (i : Fin 4) : (TailPolynomial.m (tailChart i):ℝ)=tailMargin i := by
  fin_cases i <;> norm_num [tailChart,TailPolynomial.m,tailMargin]

theorem tailChart_marker (s : State) :
    (TailPolynomial.m (tailChart s.branch.type):ℝ)+
      (TailPolynomial.e (tailChart s.branch.type):ℝ)*s.b≤ZeroPrimary.unsigned s := by
  rw [tailChart_weight,tailChart_margin]
  exact tail_marker s

theorem tailChart_weight_bounds (i : Fin 3) :
    0<(TailPolynomial.e i:ℝ) ∧ (TailPolynomial.e i:ℝ)≤kappa := by
  fin_cases i <;> norm_num [TailPolynomial.e,kappa]

theorem mixed_force_norm (a c r s : ℝ) :
    Real.sqrt ((a*Real.cos r-c*Real.sin s)^2+(c*Real.cos s-a*Real.sin r)^2)=
      tailNorm a c (r+s) := by
  unfold tailNorm
  congr 1
  rw [Real.sin_add]
  linear_combination a^2*(Real.sin_sq_add_cos_sq r)+c^2*(Real.sin_sq_add_cos_sq s)

theorem mixed_state_support (t : State) (a c r s : ℝ) :
    (a*Real.cos r-c*Real.sin s)*t.a+(c*Real.cos s-a*Real.sin r)*t.b≤
      R*tailNorm a c (r+s)-
        ((a*Real.cos r-c*Real.sin s)+(c*Real.cos s-a*Real.sin r))/2 := by
  have hh := state_support t (a*Real.cos r-c*Real.sin s) (c*Real.cos s-a*Real.sin r)
  rw [mixed_force_norm] at hh
  exact hh

def reducedDE2Tail (b t d e : State) (second : Bool)
    (c eWeight r s u : ℝ) : ℝ :=
  Real.pi+kappa*(1+transverse b)+quarterDual b t 0 (-r) kappa+
    zeroDual second t d (-s) c+quarterDual d e 2 (-u) eWeight+ZeroPrimary.unsigned e

/-- A support inequality on the unchanged states, with the original
T and D circles and both original TD owners. -/
theorem de2_support (b t d e : State) (second : Bool) {c eWeight margin r s u : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap)
    (hmarker : margin+eWeight*e.b≤ZeroPrimary.unsigned e) :
    de2Tail second eWeight margin c r s u≤reducedDE2Tail b t d e second c eWeight r s u := by
  have hty := transverse_of_nonneg t ht
  have hdy : transverse d=-d.b := transverse_nonpos_eq d hd
  have hey : transverse e=-e.b := transverse_nonpos_eq e he
  cases second with
  | false =>
      have hT := mixed_state_support t kappa c r 0
      have hD := mixed_state_support d eWeight c u s
      rw [add_comm u s] at hD
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hT
      dsimp [de2Tail,reducedDE2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hr,width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg]
      linarith only [hT,hD,hmarker]
  | true =>
      have hT := mixed_state_support t kappa c r s
      have hD := mixed_state_support d eWeight c u 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [de2Tail,reducedDE2Tail,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hr,width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg]
      linarith only [hT,hD,hmarker]

theorem reduced_de2_strict (b t d e : State) (second : Bool) {r s u : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hr : 0≤r) (hs : 0≤ s) (hu : 0≤u) (hcap : r+s+u≤frameCap) :
    pathThreshold<reducedDE2Tail b t d e second
      (strengthenedWeight (tailChart e.branch.type) (r+s+u))
      (TailPolynomial.e (tailChart e.branch.type):ℝ) r s u := by
  have htail := strengthened_de2Tail (tailChart e.branch.type) second hr hs hu hcap
  have hsupport := de2_support b t d e second
    (c := strengthenedWeight (tailChart e.branch.type) (r+s+u)) ht hd he
    (show r∈Icc 0 frameCap from ⟨hr,by linarith⟩)
    (show s∈Icc 0 frameCap from ⟨hs,by linarith⟩)
    (show u∈Icc 0 frameCap from ⟨hu,by linarith⟩) (tailChart_marker e)
  exact htail.trans_le hsupport

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## The three-edge return bound

On a boundary cycle with `C.tangent E ≤ 0` and `0 ≤ C.tangent A`, the return charge of the three
edges from E back to A exceeds `returnThreshold = 103/40` (`frame_return`): the pair bounds of the
three edges, the sum of their projections and the marker scalar give the strict reserve. Every
owner of EH and GA and both transverse owners of HG are allowed, and only the signs of the two
endpoints enter, with no sign or radial kind of H and G. The four-edge tail from A to E then has
charge below `pathThreshold` (`frame_tail_cap`).
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT

open Candidate FramePair GlobalOuterAnchor GlobalQuarterSign

def returnCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) : ℝ :=
  Real.pi+delta theta E+delta theta H+delta theta G-
    kappa*(stateOf C A).b-ZeroPrimary.unsigned (stateOf C E)
def tailCharge (C : BoundaryCycle Q0) (theta : Vertex→ℝ) : ℝ :=
  Real.pi+delta theta A+delta theta B+delta theta T+delta theta D+
    kappa*(stateOf C A).b+ZeroPrimary.unsigned (stateOf C E)

theorem return_tail_sum (C : BoundaryCycle Q0) (theta : Vertex→ℝ) :
    returnCharge C theta+tailCharge C theta=2*Real.pi := by
  simp only [returnCharge,tailCharge,delta,show next E=H by decide,show next H=G by decide,
    show next G=A by decide,show next A=B by decide,show next B=T by decide,
    show next T=D by decide,show next D=E by decide]
  ring

theorem three_frameCost_lower {r v t : ℝ}
    (hr : |r|≤frameCap) (hv : |v|≤frameCap) (ht : |t|≤frameCap) :
    frameCost (min (|r|+|v|+|t|) (3/10))≤
      frameCost |r|+frameCost |v|+frameCost |t| := by
  have hdom {x : ℝ} (hx : |x|≤frameCap) : |x|∈Icc 0 (Real.pi/4) := by
    refine ⟨abs_nonneg _,?_⟩
    dsimp [frameCap] at hx
    linarith [Real.pi_gt_three]
  have hw : min (|r|+|v|) (3/10)∈Icc 0 (Real.pi/4) := by
    refine ⟨le_min (add_nonneg (abs_nonneg r) (abs_nonneg v)) (by norm_num),?_⟩
    linarith [min_le_right (|r|+|v|) (3/10:ℝ),Real.pi_gt_three]
  have hk : min (|r|+|v|+|t|) (3/10)∈Icc 0 (Real.pi/4) := by
    refine ⟨le_min (by positivity) (by norm_num),?_⟩
    linarith [min_le_right (|r|+|v|+|t|) (3/10:ℝ),Real.pi_gt_three]
  have hfirst := frameCost_triangle (hdom hr) (hdom hv) hw (min_le_left _ _)
  have htriangle : min (|r|+|v|+|t|) (3/10)≤ min (|r|+|v|) (3/10)+|t| := by
    by_cases hshort : |r|+|v|≤(3/10:ℝ)
    · rw [min_eq_left hshort]
      exact min_le_left _ _
    · rw [min_eq_right (le_of_not_ge hshort)]
      linarith [min_le_right (|r|+|v|+|t|) (3/10:ℝ),abs_nonneg t]
  have hsecond := frameCost_triangle hw (hdom ht) hk htriangle
  linarith

theorem frame_return {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0) (hA : 0≤C.tangent A) :
    returnThreshold<returnCharge C F.theta := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have he : transverse (stateOf C E)≤0 := by
    rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (C.a_pos E).le hE
  have ha : 0≤transverse (stateOf C A) := by
    rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonneg (C.a_pos A).le hA
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose owner hf using hex
  have hHGowner : owner H=0 ∨ owner H=2 := by
    rcases GlobalZeroSign.of_frame F hq H (by norm_num [word,H]) (owner H) (hf H) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hEH : (stateOf C E).Feasible (stateOf C H) (owner E)
      (Real.pi/2+delta F.theta E) := by
    simpa [Candidate.phi,word,E,H,next] using
      GlobalAllHigh.frame_state_feasible F E (owner E) (hf E)
  have hHG : (stateOf C H).Feasible (stateOf C G) (owner H) (delta F.theta H) := by
    simpa [Candidate.phi,word,H,G,next] using
      GlobalAllHigh.frame_state_feasible F H (owner H) (hf H)
  have hGA : (stateOf C G).Feasible (stateOf C A) (owner G)
      (Real.pi/2+delta F.theta G) := by
    simpa [Candidate.phi,word,G,A,next] using
      GlobalAllHigh.frame_state_feasible F G (owner G) (hf G)
  let R : ℝ := |delta F.theta E|+|delta F.theta H|+|delta F.theta G|
  let gain : ℝ := frameCost |delta F.theta E|+frameCost |delta F.theta H|+
    frameCost |delta F.theta G|
  have hsmall : R≤3/10 → (stateOf C A).b≤4*c0-3+R := by
    intro hshort
    exact short_return_endpoint (stateOf C E) (stateOf C H) (stateOf C G) (stateOf C A)
      (owner E) (owner H) (owner G) he ha hHGowner hshort hEH hHG hGA
  have hg : frameCost (min R (3/10))≤gain :=
    three_frameCost_lower (by simpa only [frameCap] using (F.delta_small E).le)
      (by simpa only [frameCap] using (F.delta_small H).le)
      (by simpa only [frameCap] using (F.delta_small G).le)
  have hs := return_marker_reserve (stateOf C A) (by dsimp [R]; positivity) hg hsmall
  have hp (i : Vertex) : (8833/10000:ℝ)+(9/50)*frameCost |delta F.theta i|<
      GlobalAllHigh.Bridge.markerCharge C F.theta i := by
    have hg := ZeroPrimary.handGamma_lower (stateOf C i).branch.type
      (stateOf C (next i)).branch.type
    have hh := GlobalAllHigh.Bridge.frame_pair_bound F i
    linarith
  have heLabel := signed_of_nonpos (stateOf C E) he
  have haLabel := signed_of_nonneg (stateOf C A) ha
  have hsum : GlobalAllHigh.Bridge.markerCharge C F.theta E+
      GlobalAllHigh.Bridge.markerCharge C F.theta H+
      GlobalAllHigh.Bridge.markerCharge C F.theta G=
      Real.pi+delta F.theta E+delta F.theta H+delta F.theta G-
        ZeroPrimary.unsigned (stateOf C E)-ZeroPrimary.unsigned (stateOf C A) := by
    simp only [GlobalAllHigh.Bridge.markerCharge,
      show next E=H by decide,show next H=G by decide,show next G=A by decide,
      heLabel,haLabel,Candidate.phi,show word E=1 by decide,show word H=0 by decide,
      show word G=1 by decide,Int.cast_one,Int.cast_zero,zero_mul,one_mul]
    ring
  have hpE := hp E
  have hpH := hp H
  have hpG := hp G
  dsimp [returnCharge,gain] at hs ⊢
  linarith

/-- When `C.tangent E ≤ 0` and `0 ≤ C.tangent A`, the charge of the four-edge tail is below
`pathThreshold`, the cap that the BT0 and BT1 dual bounds contradict. -/
theorem frame_tail_cap {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0) (hA : 0≤C.tangent A) :
    tailCharge C F.theta<pathThreshold := by
  have hr := frame_return F hE hA
  have hs := return_tail_sum C F.theta
  have ht := thresholds_sum
  linarith [Arithmetic.two_pi_lt_710_over_113]

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
/-!
## The complete ordinary BT0 tail on actual source states

The four actual weak separating inequalities pay the explicit dual
multipliers.  All signed AB errors and both TD owners are included.
The sole remaining tail is core E with a strictly negative DE3 error.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

namespace SquaresInCircles.Eight.GlobalBT

open Candidate FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem zeroDual_le_error (s t : State) (primary : Bool) {v lambda : ℝ}
    (hl : 0≤lambda) (hp : GlobalOuterAnchor.width v≤projection false s t v (leftOwner primary)) :
    zeroDual primary s t v lambda≤v := by
  have hm := mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos.mpr hp)
  dsimp [zeroDual]
  linarith

theorem quarterDual_le_error (s t : State) (j : Fin 4) {v lambda : ℝ}
    (hl : 0≤lambda) (hp : GlobalOuterAnchor.width v≤projection true s t v j) :
    quarterDual s t j v lambda≤v := by
  have hm := mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos.mpr hp)
  dsimp [quarterDual]
  linarith

theorem ordinary_path (a b t d e : State) (ab td : Bool) (jD : Fin 4)
    {v x w y : ℝ}
    (ha : 0≤transverse a) (ht : 0≤transverse t)
    (hd : transverse d≤0) (he : transverse e≤0)
    (hv : |v|≤frameCap) (hx : |x|≤frameCap) (hw : |w|≤frameCap) (hy : |y|≤frameCap)
    (hcap : max (-x) 0+max (-w) 0+max (-y) 0≤frameCap)
    (hjD : jD=2 ∨ jD=3) (hordinary : jD=2 ∨ 0≤y ∨ e.branch.type≠0)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v (leftOwner ab))
    (hBT : GlobalOuterAnchor.width x≤projection true b t x 0)
    (hTD : GlobalOuterAnchor.width w≤projection false t d w (leftOwner td))
    (hDE : GlobalOuterAnchor.width y≤projection true d e y jD) :
    pathThreshold<Real.pi+v+x+w+y+kappa*a.b+ZeroPrimary.unsigned e := by
  let i := tailChart e.branch.type
  let z := max (-x) 0+max (-w) 0+max (-y) 0
  let c := strengthenedWeight i z
  let eWeight : ℝ := (TailPolynomial.e i:ℝ)
  have hz : z∈Icc 0 frameCap := ⟨by dsimp [z]; positivity,hcap⟩
  have hcBounds := strengthened_bounds i hz
  have hc : 0≤c := by dsimp [c]; linarith [hcBounds.1]
  have hcu : c≤kappa := hcBounds.2.1
  have heBounds := tailChart_weight_bounds i
  have hABdual := (AB_delete a b ab hv).trans
    (zeroDual_le_error a b ab (ABweight_positive hv).le hAB)
  have hBTdual := (retain_BT0 b t (lambda := kappa) hx (by norm_num [kappa]) le_rfl).trans
    (quarterDual_le_error b t 0 (lambda := kappa) (by norm_num [kappa]) hBT)
  have hTDdual := (retain_zero t d td hw hc hcu).trans
    (zeroDual_le_error t d td hc hTD)
  have hDEdual := (retain_DE d e jD hd he hjD hy heBounds.1.le heBounds.2 hordinary).trans
    (quarterDual_le_error d e jD heBounds.1.le hDE)
  have hstrict := reduced_de2_strict b t d e td ht hd he
    (le_max_right (-x) 0) (le_max_right (-w) 0) (le_max_right (-y) 0) hcap
  have hay := transverse_of_nonneg a ha
  rw [hay] at hABdual
  dsimp [reducedDE2Tail] at hstrict
  dsimp [retainedNegative] at hBTdual hTDdual hDEdual
  dsimp [c,z,i,eWeight] at hTDdual hDEdual
  linarith

theorem frame_tail_negative_budget {q : ℝ} {C : BoundaryCycle q}
    (F : Candidate.Frame C) (hq : q∈Icc (5/2:ℝ) Q0) :
    max (-delta F.theta B) 0+max (-delta F.theta T) 0+
      max (-delta F.theta D) 0<frameCap := by
  have hv := (FramePhysicalTransport.candidate_variations F hq).2
  change negativeVariation F.theta<frameCap at hv
  simp only [negativeVariation,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hv
  have h0 := negativePart_nonneg (delta F.theta H)
  have h1 := negativePart_nonneg (delta F.theta G)
  have h2 := negativePart_nonneg (delta F.theta Candidate.A)
  have h6 := negativePart_nonneg (delta F.theta E)
  dsimp [negativePart,H,G,Candidate.A,B,T,D,E] at hv h0 h1 h2 h6 ⊢
  linarith

theorem ceiling_BT0_ordinary_false {C : BoundaryCycle Q0} (F : Candidate.Frame C)
    (hE : C.tangent E≤0)
    (hBT : (forwardAxis 0).Feasible (C.square B) (C.square T))
    (jD : Fin 4) (hDE : (forwardAxis jD).Feasible (C.square D) (C.square E))
    (hordinary : jD=2 ∨ 0≤delta F.theta D ∨ C.kind E=.outer) : False := by
  have hq : Q0∈Icc (5/2:ℝ) Q0 := by norm_num [Q0]
  have hA := GlobalZeroLow.frame_BT_low_A_positive F hq 0 (Or.inl rfl) hBT
  have hT : 0<C.tangent T := by
    rcases GlobalQuarterSign.of_frame F hq B (by norm_num [word,B]) 0
      (by simpa [B,T,next] using hBT) with ⟨_,hh⟩ | ⟨hh,_⟩
    · simpa [B,T,next] using hh
    · rcases hh with hh | hh <;> norm_num at hh
  have hD := GlobalQuarterSign.frame_DE F hq hE
  have hex (i : Vertex) :
      ∃ k : Fin 4,(forwardAxis k).Feasible (C.square i) (C.square (next i)) := by
    obtain ⟨k,hk⟩ := F.forward_complete i (C.selected i) (C.feasible i)
    exact ⟨k,hk ▸ C.feasible i⟩
  choose owner hf using hex
  have hABowner : owner Candidate.A=0 ∨ owner Candidate.A=2 := by
    rcases GlobalZeroSign.of_frame F hq Candidate.A (by norm_num [word,Candidate.A])
      (owner Candidate.A) (hf Candidate.A) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hTDowner : owner T=0 ∨ owner T=2 := by
    rcases GlobalZeroSign.of_frame F hq T (by norm_num [word,T]) (owner T) (hf T) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨ab,hab⟩ : ∃ab : Bool,leftOwner ab=owner Candidate.A := by
    rcases hABowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  obtain ⟨td,htd⟩ : ∃td : Bool,leftOwner td=owner T := by
    rcases hTDowner with hh | hh
    · exact ⟨false,by simpa [leftOwner] using hh.symm⟩
    · exact ⟨true,by simpa [leftOwner] using hh.symm⟩
  have hdelta (i : Vertex) : |delta F.theta i|≤frameCap := by
    simpa only [frameCap] using (F.delta_small i).le
  have hABstate : (stateOf C Candidate.A).Feasible (stateOf C B) (leftOwner ab)
      (0+delta F.theta Candidate.A) := by
    simpa [Candidate.phi,word,Candidate.A,B,next,hab] using
      GlobalAllHigh.frame_state_feasible F Candidate.A (owner Candidate.A) (hf Candidate.A)
  have hBTstate : (stateOf C B).Feasible (stateOf C T) 0
      (Real.pi/2+delta F.theta B) := by
    simpa [Candidate.phi,word,B,T,next] using GlobalAllHigh.frame_state_feasible F B 0
      (by simpa [B,T,next] using hBT)
  have hTDstate : (stateOf C T).Feasible (stateOf C D) (leftOwner td)
      (0+delta F.theta T) := by
    simpa [Candidate.phi,word,T,D,next,htd] using
      GlobalAllHigh.frame_state_feasible F T (owner T) (hf T)
  have hDEstate : (stateOf C D).Feasible (stateOf C E) jD
      (Real.pi/2+delta F.theta D) := by
    simpa [Candidate.phi,word,D,E,next] using GlobalAllHigh.frame_state_feasible F D jD
      (by simpa [D,E,next] using hDE)
  have hey : transverse (stateOf C E)≤0 := by
    rw [GlobalAllHigh.state_transverse_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (C.a_pos E).le hE
  have ho : jD=2 ∨ 0≤delta F.theta D ∨ (stateOf C E).branch.type≠0 := by
    rcases hordinary with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr (GlobalAllHigh.state_outer_of_kind C E hh))
  have hpath := ordinary_path (stateOf C Candidate.A) (stateOf C B) (stateOf C T)
    (stateOf C D) (stateOf C E) ab td jD
    (GlobalAllHigh.state_positive_of_tangent C Candidate.A hA).le
    (GlobalAllHigh.state_positive_of_tangent C T hT).le
    (GlobalAllHigh.state_negative_of_tangent C D hD.1).le hey
    (hdelta Candidate.A) (hdelta B) (hdelta T) (hdelta D)
    (frame_tail_negative_budget F hq).le (hD.2 jD hDE) ho
    ((projection_feasible false _ _ _ (hdelta Candidate.A)).1 hABstate)
    ((projection_feasible true _ _ _ (hdelta B)).1 hBTstate)
    ((projection_feasible false _ _ _ (hdelta T)).1 hTDstate)
    ((projection_feasible true _ _ _ (hdelta D)).1 hDEstate)
  have hreturn := frame_tail_cap F hE hA.le
  dsimp [tailCharge] at hreturn
  linarith

end SquaresInCircles.Eight.GlobalBT
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.GlobalBT.CoreDE3

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem core_marker_identity (e : State) (he : e.branch.type=0) :
    ZeroPrimary.unsigned e=(7506931/1000000)*(7/12-e.a)+m*e.b := by
  cases hbranch : e.branch <;> simp [hbranch,Branch.type] at he
  all_goals simp [ZeroPrimary.unsigned,hbranch,FramePair.label,m]

theorem core_endpoint_marker (e : State) (he : e.branch.type=0) {t : ℝ}
    (ht : t∈Icc 0 frameCap) :
    endpointWeight t*(7/12)*Real.sin t≤ZeroPrimary.unsigned e+
      endpointWeight t*e.a*Real.sin t-endpointWeight t*e.b*Real.cos t := by
  have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart e he)).2.1
  have hweights := endpointWeight_bounds ht
  have hfirst := mul_nonneg (sub_nonneg.mpr hweights.2.2.2)
    (show 0≤7/12-e.a by linarith)
  have hlast := mul_nonneg (sub_nonneg.mpr hweights.2.2.1) e.b_nonneg
  rw [core_marker_identity e he]
  nlinarith only [hfirst,hlast]

def reduced (b t d e : State) (second : Bool) (c eWeight r s u : ℝ) : ℝ :=
  Real.pi+kappa*(1+transverse b)+quarterDual b t 0 (-r) kappa+
    zeroDual second t d (-s) c+quarterDual d e 3 (-u) eWeight+ZeroPrimary.unsigned e

theorem support (b t d e : State) (second : Bool) {c r s u : ℝ}
    (ht : 0≤transverse t) (hd : transverse d≤0) (he : transverse e≤0)
    (hcore : e.branch.type=0)
    (hr : r∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) :
    tail second (endpointWeight u) c r s u≤
      reduced b t d e second c (endpointWeight u) r s u := by
  have hty := transverse_of_nonneg t ht
  have hdy : transverse d=-d.b := transverse_nonpos_eq d hd
  have hey : transverse e=-e.b := transverse_nonpos_eq e he
  have hmarker := core_endpoint_marker e hcore hu
  cases second with
  | false =>
      have hT := mixed_state_support t kappa c r 0
      have hD := mixed_state_support d (endpointWeight u) c 0 s
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero,zero_add] at hT hD
      dsimp [tail,reduced,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hr,width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg]
      linarith only [hT,hD,hmarker]
  | true =>
      have hT := mixed_state_support t kappa c r s
      have hD := mixed_state_support d (endpointWeight u) c 0 0
      simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,sub_zero,add_zero] at hD
      dsimp [tail,reduced,quarterDual,zeroDual,leftOwner,projection]
      rw [width_negative hr,width_negative hs,width_negative hu,hty,hdy,hey]
      simp only [Real.cos_neg,Real.sin_neg]
      linarith only [hT,hD,hmarker]

end SquaresInCircles.Eight.GlobalBT.CoreDE3
end
end
end
