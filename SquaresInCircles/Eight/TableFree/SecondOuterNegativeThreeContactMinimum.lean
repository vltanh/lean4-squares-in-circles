module

public import SquaresInCircles.Eight.TableFree.SecondOuterNegativeThreeContactBoundary
public import SquaresInCircles.Eight.TableFree.ContactArcMinimum

/-!
# The compact original contact minimum and the last weak owner

The actual contact region is the closed source-angle rectangle cut by
both original target-coordinate bounds.  Every interior minimizer is
angularly stationary.  A negative angular second derivative contradicts
minimality on an actual feasible angular interval; otherwise the proved
positive source derivative contradicts source stationarity.  The six
remaining boundary pieces are already bounded strictly.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Contact

open CommonQuarter CorePairGeometry Arithmetic
open NegativeTwo

lemma target_continuous : Continuous (fun p : ℝ×ℝ => TargetContact.B p.1 p.2) := by
  dsimp [TargetContact.B,ShortOuterOne.SameContact.arc]
  fun_prop

lemma cost_continuous : Continuous (fun p : ℝ×ℝ => cost p.1 p.2) := by
  dsimp [cost,value,T,K,RoleLabel.outer,RoleLabel.eval,TLabel,KLabel,
    TargetContact.B,ShortOuterOne.SameContact.arc]
  fun_prop

lemma angleSecond_continuousAt {b x : ℝ} (hd : TargetContact.Domain b x) :
    ContinuousAt (angleSecond b) x := by
  have hB := (TargetContact.B_angle_hasDerivAt b x).continuousAt
  have hK := (KLabel.d1_hasDerivAt (outer_domain hd.2.2)).continuousAt.comp x hB
  have hK2 := (KLabel.d2_hasDerivAt (outer_domain hd.2.2)).continuousAt.comp x hB
  have hv := (TargetContact.v_angle_hasDerivAt b x).continuousAt
  exact (hK2.mul (hv.pow 2)).sub (hK.mul (hB.sub continuousAt_const))

theorem interior_not_minimum {b x : ℝ}
    (hb : b∈Ioo 0 outerDiagonal) (hx : x∈Ioo 0 (7/10))
    (hB : TargetContact.B b x∈Ioo 0 outerDiagonal)
    (hmin : ∀ u v, TargetContact.Domain u v → cost b x≤cost u v) : False := by
  have hd : TargetContact.Domain b x :=
    ⟨Ioo_subset_Icc_self hb,Ioo_subset_Icc_self hx,Ioo_subset_Icc_self hB⟩
  let O : Set ℝ := {t | t∈Ioo (0:ℝ) (7/10) ∧ TargetContact.B b t∈Ioo 0 outerDiagonal}
  have hcB : Continuous (TargetContact.B b) := by
    dsimp [TargetContact.B]
    fun_prop
  have hO : IsOpen O := isOpen_Ioo.inter (isOpen_Ioo.preimage hcB)
  have hxO : x∈O := ⟨hx,hB⟩
  have hdom {t : ℝ} (ht : t∈O) : TargetContact.Domain b t :=
    ⟨hd.1,Ioo_subset_Icc_self ht.1,Ioo_subset_Icc_self ht.2⟩
  have hlocal : IsLocalMin (cost b) x := by
    filter_upwards [hO.mem_nhds hxO] with t ht
    exact hmin b t (hdom ht)
  have hstationary : angleFirst b x=0 :=
    hlocal.hasDerivAt_eq_zero (cost_angle_hasDerivAt hd)
  rcases stationary_alternatives hd hstationary with hnegative | hpositive
  · let κ : ℝ := -angleSecond b x/2
    have hk : 0<κ := by dsimp [κ]; linarith
    have hcurv : ∀ᶠ t in 𝓝 x, angleSecond b t<angleSecond b x/2 :=
      (angleSecond_continuousAt hd).tendsto.eventually
        (gt_mem_nhds (by linarith : angleSecond b x<angleSecond b x/2))
    have hneighborhood : {t | t∈O ∧ angleSecond b t<angleSecond b x/2}∈𝓝 x :=
      inter_mem (hO.mem_nhds hxO) hcurv
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hneighborhood
    apply not_minimum_on_strictly_concave_curve
      (s := {q : ℝ×ℝ | TargetContact.Domain q.1 q.2})
      (cost := fun q : ℝ×ℝ => cost q.1 q.2)
      (p := (b,x)) (fun q hq => hmin q.1 q.2 hq)
      (curve := fun t : ℝ => (b,t)) (value := cost b)
      (dvalue := angleFirst b) (ddvalue := angleSecond b)
      (O := Metric.ball x r) Metric.isOpen_ball
      (show x∈Metric.ball x r by simpa using hr) hk
    · rfl
    · intro t ht
      exact hdom (hsub ht).1
    · intros
      rfl
    · intro t ht
      exact cost_angle_hasDerivAt (hdom (hsub ht).1)
    · intro t ht
      exact angleFirst_hasDerivAt (hdom (hsub ht).1)
    · intro t ht
      have hh := (hsub ht).2
      dsimp [κ]
      linarith
  · let P : Set ℝ := {t | t∈Ioo (0:ℝ) outerDiagonal ∧ TargetContact.B t x∈Ioo 0 outerDiagonal}
    have hc : Continuous (fun t => TargetContact.B t x) := by
      dsimp [TargetContact.B,ShortOuterOne.SameContact.arc]
      fun_prop
    have hP : IsOpen P := isOpen_Ioo.inter (isOpen_Ioo.preimage hc)
    have hbP : b∈P := ⟨hb,hB⟩
    have hsourceLocal : IsLocalMin (fun t => cost t x) b := by
      filter_upwards [hP.mem_nhds hbP] with t ht
      exact hmin t x ⟨Ioo_subset_Icc_self ht.1,hd.2.1,Ioo_subset_Icc_self ht.2⟩
    have he := hsourceLocal.hasDerivAt_eq_zero (cost_source_hasDerivAt hd)
    linarith

theorem contact_lower {b x : ℝ} (hd : TargetContact.Domain b x) :
    (89777/100000:ℝ)<cost b x := by
  let guard : ℝ×ℝ→ℝ := fun p =>
    min (TargetContact.B p.1 p.2) (outerDiagonal-TargetContact.B p.1 p.2)
  have hg : Continuous guard := target_continuous.min (continuous_const.sub target_continuous)
  have hguard : 0≤guard (b,x) := by
    exact le_min hd.2.2.1 (sub_nonneg.mpr hd.2.2.2)
  obtain ⟨p,hp,hbetter,hmin⟩ := contact_region_minimum hg cost_continuous
    (p₀ := (b,x)) ⟨hd.1,hd.2.1,hguard⟩
  have hpguard := le_min_iff.mp hp.2.2
  have hpd : TargetContact.Domain p.1 p.2 :=
    ⟨hp.1,hp.2.1,⟨hpguard.1,by linarith [hpguard.2]⟩⟩
  have hpboundary : Boundary p.1 p.2 := by
    by_contra hn
    simp only [Boundary,not_or] at hn
    rcases hn with ⟨hb0,hbd,hx0,hxc,hB0,hBd⟩
    have hbi : p.1∈Ioo 0 outerDiagonal :=
      ⟨lt_of_le_of_ne hpd.1.1 (Ne.symm hb0),lt_of_le_of_ne hpd.1.2 hbd⟩
    have hxi : p.2∈Ioo 0 (7/10) :=
      ⟨lt_of_le_of_ne hpd.2.1.1 (Ne.symm hx0),lt_of_le_of_ne hpd.2.1.2 hxc⟩
    have hBi : TargetContact.B p.1 p.2∈Ioo 0 outerDiagonal :=
      ⟨lt_of_le_of_ne hpd.2.2.1 (Ne.symm hB0),lt_of_le_of_ne hpd.2.2.2 hBd⟩
    exact interior_not_minimum hbi hxi hBi (fun u v huv =>
      hmin (u,v) huv.1 huv.2.1 (le_min huv.2.2.1 (sub_nonneg.mpr huv.2.2.2)))
  exact (boundary_lower hpd hpboundary).trans_le hbetter

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree.Contact

namespace SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree

open CommonQuarter CorePairGeometry Arithmetic

theorem original_lower_target_secondary {a b A B x : ℝ}
    (hs : OuterState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    (89777/100000:ℝ)<value b B (Real.pi/2-x) := by
  obtain ⟨b',B',hb',hB',hc,hbetter⟩ := Contact.original_lower_contact hs ht hx hm
  have hd : NegativeTwo.TargetContact.Domain b' x :=
    ⟨hb',hx,by rw [hc]; exact hB'⟩
  have hh := Contact.contact_lower hd
  dsimp [Contact.cost] at hh
  rw [hc] at hh
  exact hh.trans_le hbetter

end SquaresInCircles.Eight.TableFree.SecondWord.NegativeThree
