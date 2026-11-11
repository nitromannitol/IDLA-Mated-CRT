import MatedCRT.Steps.Sec4.ObstacleSpecialization
import MatedCRT.Proofs.Sec4.ObstacleSpecialization.GreenMarkov
import MatedCRT.Proofs.WalkPotential.MaximumPrinciple

/-!
# Section 4: Lemmas 4.3-4.5 without connectivity of `V^ε(B_ρ) \ V^ε(∂B_ρ)`

Appendix A assumes that `V` is connected (line 3339; field `IsObstacleSetting.connected`), and the reduction of
lines 3400-3411 applies it to `V = V^ε(B_ρ) \ V^ε(∂B_ρ)`, which need not be connected. We apply Appendix A to the
connected component `V'` of the origin in `V` (`vComponent`) instead, and glue.

* No edge joins `V \ V'` to `V'` (`not_mem_vComponent_of_adj`); hence `∂V' ∩ V = ∅` and `cl(V') ⊆ cl(V)`. The
  component `V'` is connected (`isVConnected_vComponent`).
* `Δφ = 0` on `V \ V'` (the pole `0` lies in `V'`) and the outer neighbours of `V \ V'` lie outside `V`, where `φ = 0`.
  Every finite vertex set of the mated-CRT map has an outgoing edge (`a ∼ a + 1`, `escape_of_adjacent_succ`), so the
  maximum principle `nonpos_of_lapSum_nonneg` gives `φ = 0` on `V \ V'` (`eq_zero_of_mem_sdiff_vComponent`).
* The least supersolution of the problem posed on `V ⊇ V'` is the Appendix A solution on `cl(V')`, extended by `0`
  (`dls_eq_gluedW_of_subset`), and `Δw = 0` on `V \ V'` (`mLaplacian_gluedW_eq_zero`).

Lemmas 4.3-4.5 at fixed `t, ε` follow from Lemmas A.2-A.4 for the data `(V', 0, deg⁻¹, φ, ε⁻¹ t deg(0)⁻¹)`
(`matedBasicProperties_of_regular`, `matedLaplacianBound_of_regular`, `matedConservationOfMass_of_regular`), under
the deterministic properties `IsRegularMatedMap` of the map at scale `ε`.
-/

namespace MatedCRT

open Set Metric Filter Topology

/-! ## The connected component of the origin in `V` -/

section Component

variable {α : Type*} {m : α → α → ℕ} {V : Set α} {o a b : α}

/-- A step between two adjacent vertices of `V`. -/
abbrev vStep (m : α → α → ℕ) (V : Set α) (x y : α) : Prop :=
  x ∈ V ∧ y ∈ V ∧ m x y ≠ 0

/-- The *connected component* of `o` in the subgraph induced by `V`: the vertices joined to `o` by a path in `V`. -/
def vComponent (m : α → α → ℕ) (V : Set α) (o : α) : Set α :=
  {a | Relation.ReflTransGen (vStep m V) o a}

theorem self_mem_vComponent : o ∈ vComponent m V o :=
  Relation.ReflTransGen.refl

theorem vComponent_subset (ho : o ∈ V) : vComponent m V o ⊆ V := by
  intro a (ha : Relation.ReflTransGen (vStep m V) o a)
  induction ha with
  | refl => exact ho
  | tail _ hxy _ => exact hxy.2.1

theorem mem_vComponent_of_adj (ha : a ∈ vComponent m V o) (haV : a ∈ V) (hbV : b ∈ V) (hab : m a b ≠ 0) :
    b ∈ vComponent m V o := by
  have h : Relation.ReflTransGen (vStep m V) o a := ha
  exact h.tail ⟨haV, hbV, hab⟩

/-- No edge joins a vertex of `V \ V'` to the component `V'`. -/
theorem not_mem_vComponent_of_adj (hsymm : ∀ a b, m a b = m b a) (ho : o ∈ V) (haV : a ∈ V)
    (ha : a ∉ vComponent m V o) (hab : m a b ≠ 0) : b ∉ vComponent m V o := fun hb =>
  ha (mem_vComponent_of_adj hb (vComponent_subset ho hb) haV (by rwa [hsymm]))

/-- `∂V' ∩ V = ∅`. -/
theorem not_mem_of_mem_vBoundary_vComponent (ho : o ∈ V) (hb : b ∈ vBoundary m (vComponent m V o)) : b ∉ V := by
  obtain ⟨hbC, a, ha, hab⟩ := hb
  exact fun hbV => hbC (mem_vComponent_of_adj ha (vComponent_subset ho ha) hbV hab)

theorem vClosure_vComponent_subset (ho : o ∈ V) : vClosure m (vComponent m V o) ⊆ vClosure m V := by
  rintro b (hb | hb)
  · exact Or.inl (vComponent_subset ho hb)
  · have hbV := not_mem_of_mem_vBoundary_vComponent ho hb
    obtain ⟨-, a, ha, hab⟩ := hb
    exact Or.inr ⟨hbV, a, vComponent_subset ho ha, hab⟩

/-- The component `V'` is connected. -/
theorem isVConnected_vComponent (hsymm : ∀ a b, m a b = m b a) : IsVConnected m (vComponent m V o) := by
  have key : ∀ (a : α) (h : Relation.ReflTransGen (vStep m V) o a),
      ((adjGraph m).induce (vComponent m V o)).Reachable ⟨o, self_mem_vComponent⟩ ⟨a, h⟩ := by
    intro a h
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c hob hbc ih =>
      by_cases hbc' : b = c
      · subst hbc'
        exact ih
      · refine ih.trans (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.induce_adj, adjGraph_adj_iff hsymm]
        exact ⟨hbc', hbc.2.2⟩
  show ((adjGraph m).induce (vComponent m V o)).Connected
  exact { preconnected := fun x y => (key x.1 x.2).symm.trans (key y.1 y.2),
          nonempty := ⟨⟨o, self_mem_vComponent⟩⟩ }

/-- **Vanishing off the component.** Let an edge leave every nonempty subset of the finite set `V`. If `φ ≤ 0` on `V`,
`φ = 0` off `V` and `Δφ = 0` on `V \ V'`, then `φ = 0` on `V \ V'`: the maximum principle applies to `-φ` on `V \ V'`,
whose outer neighbours lie outside `V`. -/
theorem eq_zero_of_mem_sdiff_vComponent (hlf : IsLocallyFiniteMult m) (hsymm : ∀ a b, m a b = m b a)
    (ho : o ∈ V) (hV : V.Finite) (hesc : ∀ S ⊆ V, S.Nonempty → ∃ a ∈ S, ∃ b ∉ S, m a b ≠ 0) {φ : α → ℝ}
    (hφ : ∀ a ∈ V, φ a ≤ 0) (hφ0 : ∀ b ∉ V, φ b = 0)
    (hlap : ∀ a ∈ V, a ∉ vComponent m V o → mLaplacian m φ a = 0) (haV : a ∈ V) (ha : a ∉ vComponent m V o) :
    φ a = 0 := by
  have hsub : ∀ b ∈ V \ vComponent m V o, 0 ≤ lapSum hlf (fun c => -φ c) b := by
    intro b hb
    have h1 : lapSum hlf φ b = 0 := by
      rw [← mLaplacian_mul_mdeg hlf, hlap b hb.1 hb.2, zero_mul]
    have h2 : lapSum hlf (fun c => -φ c) b = -lapSum hlf φ b := by
      simp only [lapSum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [h2, h1, neg_zero]
  have hbd : ∀ b ∈ V \ vComponent m V o, ∀ c, m b c ≠ 0 → c ∉ V \ vComponent m V o → -φ c ≤ 0 := by
    intro b hb c hbc hc
    have hcC : c ∉ vComponent m V o := not_mem_vComponent_of_adj hsymm ho hb.1 hb.2 hbc
    have hcV : c ∉ V := fun hcV => hc ⟨hcV, hcC⟩
    rw [hφ0 c hcV, neg_zero]
  have hle : -φ a ≤ 0 := nonpos_of_lapSum_nonneg hlf (U := V \ vComponent m V o) (hV.subset Set.sdiff_subset)
    (fun S hS hne => hesc S (hS.trans Set.sdiff_subset) hne) hsub hbd a ⟨haV, ha⟩
  exact le_antisymm (hφ a haV) (by linarith)

end Component

/-! ## The obstacle problem posed on `V ⊇ V'` -/

section Glue

variable {α : Type*} {m : α → α → ℕ} {V V' W : Set α} {o : α} {𝔯 φ : α → ℝ} {𝔱 : ℝ}

theorem gluedW_of_mem {a : α} (ha : a ∈ vClosure m V') :
    gluedW m V' 𝔯 φ a = discreteLeastSupersolution m V' (vClosure m V') 𝔯 φ a := by
  simp [gluedW, ha]

theorem gluedW_of_not_mem {a : α} (ha : a ∉ vClosure m V') : gluedW m V' 𝔯 φ a = 0 := by
  simp [gluedW, ha]

/-- The Appendix A solution on `cl(V')` extended by `0` vanishes off `V'` (it vanishes on `∂V'`). -/
theorem gluedW_eq_zero (hS : IsObstacleSetting m V' o 𝔯 φ 𝔱) {a : α} (ha : a ∉ V') : gluedW m V' 𝔯 φ a = 0 := by
  by_cases hac : a ∈ vClosure m V'
  · rw [gluedW_of_mem hac]
    rcases hac with h | h
    · exact absurd h ha
    · exact (hS.w_boundary a h).1
  · exact gluedW_of_not_mem hac

theorem mLaplacian_gluedW_of_mem {a : α} (ha : a ∈ V') :
    mLaplacian m (gluedW m V' 𝔯 φ) a = mLaplacian m (discreteLeastSupersolution m V' (vClosure m V') 𝔯 φ) a :=
  mLaplacian_congr_nbhd (gluedW_of_mem (show a ∈ vClosure m V' from Or.inl ha)) fun _ hb =>
    gluedW_of_mem (nbr_mem_vClosure ha hb)

/-- `Δw = 0` on `V \ V'` when no edge joins `V \ V'` to `V'`. -/
theorem mLaplacian_gluedW_eq_zero (hS : IsObstacleSetting m V' o 𝔯 φ 𝔱)
    (hsep : ∀ a ∈ V, a ∉ V' → ∀ b, m a b ≠ 0 → b ∉ V') {a : α} (ha : a ∈ V) (ha' : a ∉ V') :
    mLaplacian m (gluedW m V' 𝔯 φ) a = 0 := by
  rw [mLaplacian_congr_nbhd (u := gluedW m V' 𝔯 φ) (v := fun _ => (0 : ℝ)) (gluedW_eq_zero hS ha') fun b hb =>
    gluedW_eq_zero hS (hsep a ha ha' b hb)]
  simp [mLaplacian]

/-- The Appendix A solution on `V'` extended by `0` is admissible for the obstacle problem posed on `V ⊇ V'`. -/
theorem gluedW_mem_of_subset (hS : IsObstacleSetting m V' o 𝔯 φ 𝔱)
    (hsep : ∀ a ∈ V, a ∉ V' → ∀ b, m a b ≠ 0 → b ∉ V') (h𝔯 : ∀ a ∈ V, 0 ≤ 𝔯 a)
    (hφ : ∀ b ∈ W, b ∉ vClosure m V' → φ b = 0) : gluedW m V' 𝔯 φ ∈ obstacleAdmissible m V W 𝔯 φ := by
  refine ⟨fun b hb => ?_, (gluedW_mem hS hφ).2⟩
  by_cases hb' : b ∈ V'
  · exact (gluedW_mem hS hφ).1 b hb'
  · rw [mLaplacian_gluedW_eq_zero hS hsep hb hb']
    exact h𝔯 b hb

/-- The obstacle problem posed on `V ⊇ V'` (no edge between `V \ V'` and `V'`, `φ = 0` on `W \ cl(V')`) is solved on
`W ⊇ cl(V')` by the Appendix A solution on `V'` extended by `0`. -/
theorem dls_eq_gluedW_of_subset (hS : IsObstacleSetting m V' o 𝔯 φ 𝔱) (hV : V' ⊆ V)
    (hsep : ∀ a ∈ V, a ∉ V' → ∀ b, m a b ≠ 0 → b ∉ V') (h𝔯 : ∀ a ∈ V, 0 ≤ 𝔯 a) (hW : vClosure m V' ⊆ W)
    (hφ : ∀ b ∈ W, b ∉ vClosure m V' → φ b = 0) {a : α} (ha : a ∈ W) :
    discreteLeastSupersolution m V W 𝔯 φ a = gluedW m V' 𝔯 φ a := by
  have hmem := gluedW_mem_of_subset hS hsep h𝔯 hφ
  rw [discreteLeastSupersolution_eq]
  apply le_antisymm
  · refine csInf_le ⟨φ a, ?_⟩ ⟨_, hmem, rfl⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hu.2 a ha
  · refine le_csInf ⟨_, ⟨_, hmem, rfl⟩⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    by_cases hac : a ∈ vClosure m V'
    · rw [gluedW_of_mem hac]
      exact IsObstacleSetting.w_le (V := V') u ⟨fun b hb => hu.1 b (hV hb), fun b hb => hu.2 b (hW hb)⟩ a hac
    · rw [gluedW_of_not_mem hac, ← hφ a ha hac]
      exact hu.2 a ha

theorem mLaplacian_dls_eq_gluedW (hS : IsObstacleSetting m V' o 𝔯 φ 𝔱) (hV : V' ⊆ V)
    (hsep : ∀ a ∈ V, a ∉ V' → ∀ b, m a b ≠ 0 → b ∉ V') (h𝔯 : ∀ a ∈ V, 0 ≤ 𝔯 a) (hW : vClosure m V' ⊆ W)
    (hφ : ∀ b ∈ W, b ∉ vClosure m V' → φ b = 0) (hVW : vClosure m V ⊆ W) {a : α} (ha : a ∈ V) :
    mLaplacian m (discreteLeastSupersolution m V W 𝔯 φ) a = mLaplacian m (gluedW m V' 𝔯 φ) a :=
  mLaplacian_congr_nbhd (dls_eq_gluedW_of_subset hS hV hsep h𝔯 hW hφ (hVW (Or.inl ha))) fun _ hb =>
    dls_eq_gluedW_of_subset hS hV hsep h𝔯 hW hφ (hVW (nbr_mem_vClosure ha hb))

/-- The cluster `{a ∈ U : w(a) > φ(a)}`, `V' ⊆ U ⊆ W`, of a function `w` equal to the glued solution on `W` is the
Appendix A cluster of `V'`. -/
theorem discreteCluster_eq_of_gluedW (hS : IsObstacleSetting m V' o 𝔯 φ 𝔱) {w : α → ℝ}
    (hw : ∀ a ∈ W, w a = gluedW m V' 𝔯 φ a) (hφ : ∀ b ∈ W, b ∉ vClosure m V' → φ b = 0) {U : Set α}
    (hVU : V' ⊆ U) (hUW : U ⊆ W) :
    discreteCluster U w φ =
      discreteCluster (vClosure m V') (discreteLeastSupersolution m V' (vClosure m V') 𝔯 φ) φ := by
  ext a
  constructor
  · rintro ⟨haU, hlt⟩
    rw [hw a (hUW haU)] at hlt
    by_cases hac : a ∈ vClosure m V'
    · exact ⟨hac, by rwa [gluedW_of_mem hac] at hlt⟩
    · rw [gluedW_of_not_mem hac, hφ a (hUW haU) hac] at hlt
      exact absurd hlt (lt_irrefl 0)
  · rintro ⟨hac, hlt⟩
    have haV : a ∈ V' := hS.cluster_subset ⟨hac, hlt⟩
    refine ⟨hVU haV, ?_⟩
    rw [hw a (hUW (hVU haV)), gluedW_of_mem hac]
    exact hlt

end Glue

theorem tsum_subtype_eq_toFinset_sum {s : Set ℤ} (hs : s.Finite) (f : ℤ → ℝ) :
    ∑' a : s, f a = ∑ a ∈ hs.toFinset, f a := by
  rw [tsum_subtype s f, tsum_eq_finsum (hs.subset Set.support_indicator_subset), ← finsum_mem_def,
    finsum_mem_eq_finite_toFinset_sum _ hs]

/-! ## The mated-CRT map at a fixed scale -/

section Proper

variable {ε : ℝ} {η : ℝ → ℂ} {ρ : ℝ}

/-- For a continuous curve with `η(s) → ∞` as `|s| → ∞`, finitely many cells meet a bounded set. -/
theorem cellVertices_finite_of_proper (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) {K : Set ℂ} (hK : Bornology.IsBounded K) : (cellVertices ε η K).Finite := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  have hc : IsCompact (η ⁻¹' closedBall 0 R) :=
    (isProperMap_iff_tendsto_cocompact.2 ⟨hη, hp⟩).isCompact_preimage (isCompact_closedBall 0 R)
  obtain ⟨T, hT⟩ := hc.isBounded.subset_closedBall 0
  refine (Set.finite_Icc (-⌈T / ε + 1⌉) ⌈T / ε + 1⌉).subset ?_
  intro k hk
  obtain ⟨z, ⟨s, hs, rfl⟩, hzK⟩ : ∃ z, z ∈ η '' Icc (ε * (k - 1)) (ε * k) ∧ z ∈ K := hk
  have hsT : |s| ≤ T := by simpa [Real.dist_eq] using hT (hR hzK)
  have h1 : ε * (k - 1) ≤ T := hs.1.trans ((le_abs_self s).trans hsT)
  have h2 : -T ≤ ε * k := ((neg_le_neg hsT).trans (neg_abs_le s)).trans hs.2
  have hk1 : (k : ℝ) ≤ T / ε + 1 := by
    have : (k : ℝ) - 1 ≤ T / ε := (le_div_iff₀ hε).2 (by rw [mul_comm]; exact h1)
    linarith
  have hk2 : -(T / ε + 1) ≤ (k : ℝ) := by
    have h3 : -T / ε ≤ (k : ℝ) := (div_le_iff₀ hε).2 (by rw [mul_comm]; exact h2)
    rw [neg_div] at h3
    linarith
  have hc1 := Int.le_ceil (T / ε + 1)
  constructor
  · have : ((-⌈T / ε + 1⌉ : ℤ) : ℝ) ≤ k := by push_cast; linarith
    exact_mod_cast this
  · exact_mod_cast hk1.trans hc1

/-- A map whose adjacent vertices have intersecting cells is locally finite (continuous proper curve). -/
theorem locallyFinite_of_cellsMeet_of_proper {m : ℤ → ℤ → ℕ} (hη : Continuous η)
    (hp : Tendsto η (cocompact ℝ) (cocompact ℂ)) (hε : 0 < ε)
    (hcell : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty) : IsLocallyFiniteMult m := fun a => by
  have hK : Bornology.IsBounded (cell ε η a) := (isCompact_Icc.image hη).isBounded
  refine (cellVertices_finite_of_proper hη hp hε hK).subset fun b hb => ?_
  obtain ⟨z, hza, hzb⟩ := hcell a b hb
  exact ⟨z, hzb, hza⟩

/-- `V^ε(B_ρ) \ V^ε(∂B_ρ)` is finite (continuous proper curve). -/
theorem ballInterior_finite_of_proper (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hε : 0 < ε) : (ballInterior ε η ρ).Finite :=
  (cellVertices_finite_of_proper hη hp hε isBounded_ball).subset ballInterior_subset_cellVertices_ball

end Proper

/-- The deterministic properties of the mated-CRT map at scale `ε` used in Lemmas 4.3-4.5: `η` is continuous and
`η(s) → ∞` as `|s| → ∞`, the edge multiplicity is symmetric and loopless, consecutive vertices are adjacent
(`εk ∼ ε(k+1)`, Definition 1.1) and adjacent vertices have intersecting cells. They hold almost surely for all `ε > 0`
(MatedCRT/Proofs/Sec4/ObstacleSpecialization/Statements.lean). -/
structure IsRegularMatedMap (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) : Prop where
  continuous : Continuous η
  proper : Tendsto η (cocompact ℝ) (cocompact ℂ)
  pos : 0 < ε
  symm : ∀ a b, m a b = m b a
  loopless : ∀ a, m a a = 0
  succ : ∀ k, m k (k + 1) ≠ 0
  cells_meet : ∀ j k, m j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty

namespace IsRegularMatedMap

variable {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ} (hd : IsRegularMatedMap m ε η)
include hd

theorem locallyFinite : IsLocallyFiniteMult m :=
  locallyFinite_of_cellsMeet_of_proper hd.continuous hd.proper hd.pos hd.cells_meet

theorem finite_ballInterior : (ballInterior ε η ρ).Finite :=
  ballInterior_finite_of_proper hd.continuous hd.proper hd.pos

theorem sep (h0 : (0 : ℤ) ∈ ballInterior ε η ρ) :
    ∀ a ∈ ballInterior ε η ρ, a ∉ vComponent m (ballInterior ε η ρ) 0 → ∀ b, m a b ≠ 0 →
      b ∉ vComponent m (ballInterior ε η ρ) 0 :=
  fun _ ha haC _ hab => not_mem_vComponent_of_adj hd.symm h0 ha haC hab

/-- The Section 4 data restricted to the component `V'` of the origin in `V^ε(B_ρ) \ V^ε(∂B_ρ)` satisfy the hypotheses
of Appendix A (lines 3400-3411, with `V'` in place of `V`). -/
theorem isObstacleSetting (ht : 0 < t) (h0 : (0 : ℤ) ∈ ballInterior ε η ρ) :
    IsObstacleSetting m (vComponent m (ballInterior ε η ρ) 0) 0 (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹)
      (matedObstacle m ε η ρ t) (t / ε * ((matedDeg m 0 : ℕ) : ℝ)⁻¹) where
  symm := hd.symm
  loopless := hd.loopless
  locallyFinite := hd.locallyFinite
  infinite := inferInstance
  finite := hd.finite_ballInterior.subset (vComponent_subset h0)
  connected := isVConnected_vComponent hd.symm
  origin_mem := self_mem_vComponent
  threshold_pos := fun a _ => inv_pos.2 (Nat.cast_pos.2 (mdeg_pos_of_ne_zero hd.locallyFinite (hd.succ a)))
  obstacle_nonpos := fun a _ => matedObstacle_nonpos ht.le hd.pos.le a
  obstacle_laplacian := fun a ha => by
    rw [matedObstacle_laplacian (greenKernelLaplacianStep m _ hd.symm hd.locallyFinite hd.succ
      hd.finite_ballInterior 0 h0) (vComponent_subset h0 ha)]
    by_cases h : a = 0 <;> simp [h]
  obstacle_boundary := fun _ ha => matedObstacle_eq_zero_of_not_mem (not_mem_of_mem_vBoundary_vComponent h0 ha)
  mass_pos := mul_pos (div_pos ht hd.pos) (inv_pos.2 (Nat.cast_pos.2 (mdeg_pos_of_ne_zero hd.locallyFinite (hd.succ 0))))

/-- The obstacle `φ = -(t ε⁻¹) g^ε_{B_ρ}(0, ·)` vanishes off `cl(V')`. -/
theorem obstacle_eq_zero_off (ht : 0 < t) (h0 : (0 : ℤ) ∈ ballInterior ε η ρ) {b : ℤ}
    (hb : b ∉ vClosure m (vComponent m (ballInterior ε η ρ) 0)) : matedObstacle m ε η ρ t b = 0 := by
  by_cases hbV : b ∈ ballInterior ε η ρ
  · refine eq_zero_of_mem_sdiff_vComponent (φ := matedObstacle m ε η ρ t) hd.locallyFinite hd.symm h0
      hd.finite_ballInterior (escape_of_adjacent_succ hd.succ hd.finite_ballInterior)
      (fun a _ => matedObstacle_nonpos ht.le hd.pos.le a) (fun c hc => matedObstacle_eq_zero_of_not_mem hc)
      (fun a ha haC => ?_) hbV fun h => hb (Or.inl h)
    have ha0 : a ≠ 0 := fun h => haC (by rw [h]; exact self_mem_vComponent)
    rw [matedObstacle_laplacian (greenKernelLaplacianStep m _ hd.symm hd.locallyFinite hd.succ
      hd.finite_ballInterior 0 h0) ha]
    simp [ha0]
  · exact matedObstacle_eq_zero_of_not_mem hbV

/-- `w̃^ε_t` is the Appendix A solution on `cl(V')` extended by `0`. -/
theorem w_eq_gluedW (ht : 0 < t) (h0 : (0 : ℤ) ∈ ballInterior ε η ρ) {a : ℤ}
    (ha : a ∈ cellVertices ε η (closedBall 0 ρ)) :
    matedLeastSupersolution m ε η ρ t a = gluedW m (vComponent m (ballInterior ε η ρ) 0)
      (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹) (matedObstacle m ε η ρ t) a :=
  dls_eq_gluedW_of_subset (hd.isObstacleSetting ht h0) (vComponent_subset h0) (hd.sep h0)
    (fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
    ((vClosure_vComponent_subset h0).trans (vClosure_ballInterior_subset hd.continuous hd.cells_meet))
    (fun _ _ hb => hd.obstacle_eq_zero_off ht h0 hb) ha

theorem lap_w_eq (ht : 0 < t) (h0 : (0 : ℤ) ∈ ballInterior ε η ρ) {a : ℤ} (ha : a ∈ ballInterior ε η ρ) :
    matedLaplacian m (matedLeastSupersolution m ε η ρ t) a = mLaplacian m (gluedW m
      (vComponent m (ballInterior ε η ρ) 0) (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹) (matedObstacle m ε η ρ t)) a :=
  mLaplacian_dls_eq_gluedW (hd.isObstacleSetting ht h0) (vComponent_subset h0) (hd.sep h0)
    (fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
    ((vClosure_vComponent_subset h0).trans (vClosure_ballInterior_subset hd.continuous hd.cells_meet))
    (fun _ _ hb => hd.obstacle_eq_zero_off ht h0 hb) (vClosure_ballInterior_subset hd.continuous hd.cells_meet) ha

/-- `Λ^ε_t` is the Appendix A cluster of `V'`. -/
theorem cluster_eq (ht : 0 < t) (h0 : (0 : ℤ) ∈ ballInterior ε η ρ) :
    matedDiscreteCluster m ε η ρ t =
      discreteCluster (vClosure m (vComponent m (ballInterior ε η ρ) 0))
        (discreteLeastSupersolution m (vComponent m (ballInterior ε η ρ) 0)
          (vClosure m (vComponent m (ballInterior ε η ρ) 0)) (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹)
          (matedObstacle m ε η ρ t)) (matedObstacle m ε η ρ t) :=
  discreteCluster_eq_of_gluedW (hd.isObstacleSetting ht h0) (fun _ ha => hd.w_eq_gluedW ht h0 ha)
    (fun _ _ hb => hd.obstacle_eq_zero_off ht h0 hb)
    ((vComponent_subset h0).trans ballInterior_subset_cellVertices_ball) cellVertices_ball_subset_closedBall

end IsRegularMatedMap

section Fixed

variable {m : ℤ → ℤ → ℕ} {ε : ℝ} {η : ℝ → ℂ} {ρ t : ℝ}

/-- **Lemma 4.3** for fixed `t, ε`, without connectivity of `V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
theorem matedBasicProperties_of_regular (hd : IsRegularMatedMap m ε η) (ht : 0 < t) :
    (∀ a ∈ cellVertices ε η (closedBall 0 ρ),
      max (-normExitTime m (ballInterior ε η ρ) a) (matedObstacle m ε η ρ t a) ≤
        matedLeastSupersolution m ε η ρ t a ∧ matedLeastSupersolution m ε η ρ t a ≤ 0) ∧
    ∀ a ∈ ballInterior ε η ρ,
      matedLaplacian m (matedLeastSupersolution m ε η ρ t) a ≤ ((matedDeg m a : ℕ) : ℝ)⁻¹ := by
  by_cases h0 : (0 : ℤ) ∈ ballInterior ε η ρ
  · have hS := hd.isObstacleSetting ht h0
    have hq : ∀ a ∈ vComponent m (ballInterior ε η ρ) 0,
        mLaplacian m (fun b => -normExitTime m (ballInterior ε η ρ) b) a = ((matedDeg m a : ℕ) : ℝ)⁻¹ := by
      intro a ha
      have : (fun b => -normExitTime m (ballInterior ε η ρ) b) =
          fun b => (-1) * normExitTime m (ballInterior ε η ρ) b := funext fun _ => by ring
      rw [this, mLaplacian_const_mul, normExitTimeLaplacianStep m _ hd.symm hd.locallyFinite hd.succ
        hd.finite_ballInterior a (vComponent_subset h0 ha),
        show ((matedDeg m a : ℕ) : ℝ) = (mdeg m a : ℝ) from rfl]
      ring
    have hqb : ∀ a ∈ vBoundary m (vComponent m (ballInterior ε η ρ) 0),
        -normExitTime m (ballInterior ε η ρ) a = 0 := fun a ha => by
      rw [normExitTime_eq_zero_of_not_mem _ (not_mem_of_mem_vBoundary_vComponent h0 ha), neg_zero]
    have hA := discreteBasicPropertiesGeneral ℤ _ _ _ _ _ _ hS _ hq hqb
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · rw [hd.w_eq_gluedW ht h0 ha]
      by_cases hac : a ∈ vClosure m (vComponent m (ballInterior ε η ρ) 0)
      · rw [gluedW_of_mem hac]
        exact hA.1 a hac
      · rw [gluedW_of_not_mem hac, hd.obstacle_eq_zero_off ht h0 hac]
        exact ⟨max_le (neg_nonpos.2 (normExitTime_nonneg _ _ _)) le_rfl, le_rfl⟩
    · rw [hd.lap_w_eq ht h0 ha]
      by_cases haC : a ∈ vComponent m (ballInterior ε η ρ) 0
      · rw [mLaplacian_gluedW_of_mem haC]
        exact hA.2 a haC
      · rw [mLaplacian_gluedW_eq_zero hS (hd.sep h0) ha haC]
        exact inv_nonneg.2 (Nat.cast_nonneg _)
  · exact matedBasicProperties_fixed hd.continuous hd.cells_meet (fun h => absurd h h0) fun h => absurd h h0

/-- **Lemma 4.4** for fixed `t, ε` (origin claim under `0 ∈ V`), without connectivity of `V`. -/
theorem matedLaplacianBound_of_regular (hd : IsRegularMatedMap m ε η) (ht : 0 < t) :
    (∀ a ∈ matedDiscreteCluster m ε η ρ t,
      matedLaplacian m (matedLeastSupersolution m ε η ρ t) a = ((matedDeg m a : ℕ) : ℝ)⁻¹) ∧
    (∀ a ∈ ballInterior ε η ρ,
      0 ≤ matedLaplacian m (matedLeastSupersolution m ε η ρ t) a ∧
      matedLaplacian m (matedLeastSupersolution m ε η ρ t) a ≤ ((matedDeg m a : ℕ) : ℝ)⁻¹) ∧
    IsVPreconnected m (matedDiscreteCluster m ε η ρ t) ∧
    (1 < t / ε → (0 : ℤ) ∈ ballInterior ε η ρ → (0 : ℤ) ∈ matedDiscreteCluster m ε η ρ t) := by
  by_cases h0 : (0 : ℤ) ∈ ballInterior ε η ρ
  · have hS := hd.isObstacleSetting ht h0
    have hA := discreteLaplacianBoundGeneral ℤ _ _ _ _ _ _ hS
    refine ⟨fun a ha => ?_, fun a ha => ?_, ?_, fun h1 _ => ?_⟩
    · rw [hd.cluster_eq ht h0] at ha
      have haC := hS.cluster_subset ha
      rw [hd.lap_w_eq ht h0 (vComponent_subset h0 haC), mLaplacian_gluedW_of_mem haC]
      exact hA.1 a ha
    · rw [hd.lap_w_eq ht h0 ha]
      by_cases haC : a ∈ vComponent m (ballInterior ε η ρ) 0
      · rw [mLaplacian_gluedW_of_mem haC]
        exact hA.2.1 a haC
      · rw [mLaplacian_gluedW_eq_zero hS (hd.sep h0) ha haC]
        exact ⟨le_rfl, inv_nonneg.2 (Nat.cast_nonneg _)⟩
    · rw [hd.cluster_eq ht h0]
      exact hA.2.2.1
    · rw [hd.cluster_eq ht h0]
      refine hA.2.2.2 ?_
      show ((matedDeg m 0 : ℕ) : ℝ)⁻¹ < t / ε * ((matedDeg m 0 : ℕ) : ℝ)⁻¹
      exact lt_mul_of_one_lt_left (inv_pos.2 (Nat.cast_pos.2 (IsObstacleSetting.mdeg_origin_pos hS))) h1
  · exact matedLaplacianBound_fixed hd.continuous hd.cells_meet fun h => absurd h h0

/-- **Lemma 4.5** for fixed `t, ε` (mass identity under `0 ∈ V`), without connectivity of `V`. -/
theorem matedConservationOfMass_of_regular (hd : IsRegularMatedMap m ε η) (ht : 0 < t) :
    (matedDiscreteCluster m ε η ρ t).Finite ∧
    ((matedDiscreteCluster m ε η ρ t).ncard : ℝ) ≤ t / ε ∧
    ((0 : ℤ) ∈ ballInterior ε η ρ →
      matedDiscreteCluster m ε η ρ t ⊆ vInterior m (ballInterior ε η ρ) →
      ∑' a : ballInterior ε η ρ,
        matedLaplacian m (matedLeastSupersolution m ε η ρ t) a * (matedDeg m a : ℝ) = t / ε) := by
  by_cases h0 : (0 : ℤ) ∈ ballInterior ε η ρ
  · have hS := hd.isObstacleSetting ht h0
    have hA := discreteConservationOfMassGeneral ℤ _ _ _ _ _ _ hS fun _ _ => rfl
    have hd0 : ((mdeg m 0 : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (IsObstacleSetting.mdeg_origin_pos hS).ne'
    have h𝔱 : t / ε * ((matedDeg m 0 : ℕ) : ℝ)⁻¹ * (mdeg m 0 : ℝ) = t / ε :=
      inv_mul_cancel_right₀ hd0 _
    have hCfin := hS.finite
    have hfin : (ballInterior ε η ρ).Finite := hd.finite_ballInterior
    rw [hd.cluster_eq ht h0]
    refine ⟨IsObstacleSetting.cluster_finite hS, hA.1.trans_eq h𝔱, fun _ hint => ?_⟩
    have hint' : discreteCluster (vClosure m (vComponent m (ballInterior ε η ρ) 0))
        (discreteLeastSupersolution m (vComponent m (ballInterior ε η ρ) 0)
          (vClosure m (vComponent m (ballInterior ε η ρ) 0)) (fun b => ((matedDeg m b : ℕ) : ℝ)⁻¹)
          (matedObstacle m ε η ρ t)) (matedObstacle m ε η ρ t) ⊆
          vInterior m (vComponent m (ballInterior ε η ρ) 0) := fun a ha =>
      ⟨hS.cluster_subset ha, fun b hab =>
        mem_vComponent_of_adj (hS.cluster_subset ha) (hint ha).1 ((hint ha).2 b hab) hab⟩
    have hmass := hA.2 hint'
    rw [finsum_mem_eq_finite_toFinset_sum _ hCfin] at hmass
    have hsub : hCfin.toFinset ⊆ hfin.toFinset := fun a ha =>
      hfin.mem_toFinset.2 (vComponent_subset h0 (hCfin.mem_toFinset.1 ha))
    rw [tsum_subtype_eq_toFinset_sum hfin
        (fun a => matedLaplacian m (matedLeastSupersolution m ε η ρ t) a * (matedDeg m a : ℝ)),
      ← Finset.sum_subset hsub ?_, ← h𝔱, ← hmass]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have haC := hCfin.mem_toFinset.1 ha
      rw [hd.lap_w_eq ht h0 (vComponent_subset h0 haC), mLaplacian_gluedW_of_mem haC]
      rfl
    · intro a haV haC
      have haV' := hfin.mem_toFinset.1 haV
      rw [hd.lap_w_eq ht h0 haV', mLaplacian_gluedW_eq_zero hS (hd.sep h0) haV'
        fun h => haC (hCfin.mem_toFinset.2 h), zero_mul]
  · exact matedConservationOfMass_fixed hd.continuous hd.cells_meet ht hd.pos fun h => absurd h h0

end Fixed

end MatedCRT
