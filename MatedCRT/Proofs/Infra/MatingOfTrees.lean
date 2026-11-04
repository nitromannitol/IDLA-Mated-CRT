import MatedCRT.Defs.Setting

/-!
# The map of Definition 1.1 under the mating-of-trees coupling

Uses Leonardo Bonanno's mating-of-trees bundle as ported to Lattice-Probability (adapted from Leonardo Bonanno's
lean-formalizations, MatedCRTHarmonic, commit 31e7483): `MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling`
(module `LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling`), fields `spaceFilling` and `areaParam`.

* `bmEdgeCount_self`, `bmEdgeCount_symm`: no loops, undirected (deterministic).
* `bmAdjacent_succ`, `bmEdgeCount_succ_ne_zero`: for continuous paths, consecutive vertices are adjacent
  (Definition 1.1: the point `a` lies in both windows; Leo's `sideCond_succ`).
* `MatedCRTEnv.mult_self`, `MatedCRTEnv.mult_symm`, `MatedCRTEnv.mult_succ_ne_zero`: the same for the map of the
  environment, for every `ω` (the pair `bm ω` is continuous).
* `MatedCRTEnv.IsValid.ae_tendsto_cocompact`: almost surely `η(t) → ∞` as `|t| → ∞` (bundle: `ηL` is transient,
  `spaceFilling`, and `η` is an increasing reparametrization of `ηL`, `areaParam`).

These replace the former literature input `SpaceFillingSLEPathInput` (MatedCRT/External/SLE.lean, commit 12219de).
-/

namespace MatedCRT

open MeasureTheory Filter Topology Set

/-- Definition 1.1 has no loops. -/
theorem bmEdgeCount_self (ε : ℝ) (L R : ℝ → ℝ) (k : ℤ) : bmEdgeCount ε L R k k = 0 := by
  simp [bmEdgeCount]

/-- The map of Definition 1.1 is undirected. -/
theorem bmEdgeCount_symm (ε : ℝ) (L R : ℝ → ℝ) (j k : ℤ) : bmEdgeCount ε L R j k = bmEdgeCount ε L R k j := by
  rcases eq_or_ne j k with rfl | h
  · rfl
  · simp only [bmEdgeCount, h, h.symm, ↓reduceIte]
    rw [min_comm k j, max_comm k j]

/-- For a continuous path, consecutive vertices satisfy the adjacency condition (eq:edge-map, line 172): the point
`εk` lies in both windows `[εk - ε, εk]`, `[εk, εk + ε]`, and the middle interval is `{εk}`. -/
theorem bmAdjacent_succ {ε : ℝ} (hε : 0 ≤ ε) {X : ℝ → ℝ} (hX : Continuous X) (k : ℤ) :
    bmAdjacent ε X k (k + 1) := by
  have e1 : ε * ((k + 1 : ℤ) : ℝ) = ε * k + ε := by push_cast; ring
  unfold bmAdjacent
  rw [e1, add_sub_cancel_right, Icc_self, image_singleton, csInf_singleton]
  have hb : ∀ a b : ℝ, BddBelow (X '' Icc a b) := fun a b => (isCompact_Icc.image hX).bddBelow
  exact max_le (csInf_le (hb _ _) ⟨ε * k, ⟨by linarith, le_rfl⟩, rfl⟩)
    (csInf_le (hb _ _) ⟨ε * k, ⟨le_rfl, by linarith⟩, rfl⟩)

/-- For continuous paths, consecutive vertices of the map of Definition 1.1 are joined by an edge. -/
theorem bmEdgeCount_succ_ne_zero {ε : ℝ} (hε : 0 ≤ ε) {L : ℝ → ℝ} (hL : Continuous L) (R : ℝ → ℝ) (k : ℤ) :
    bmEdgeCount ε L R k (k + 1) ≠ 0 := by
  have hmin : min k (k + 1) = k := min_eq_left (by omega)
  have hmax : max k (k + 1) = k + 1 := max_eq_right (by omega)
  have hadj : bmAdjacent ε L (min k (k + 1)) (max k (k + 1)) := by
    rw [hmin, hmax]
    exact bmAdjacent_succ hε hL k
  simp only [bmEdgeCount]
  split_ifs with h1 h2 h3
  all_goals first | omega | exact absurd (Or.inl hadj) h2

namespace MatedCRTEnv

variable {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)

theorem mult_self (ε : ℝ) (ω : Ω) (k : ℤ) : S.mult ε ω k k = 0 :=
  bmEdgeCount_self _ _ _ k

theorem mult_symm (ε : ℝ) (ω : Ω) (j k : ℤ) : S.mult ε ω j k = S.mult ε ω k j :=
  bmEdgeCount_symm _ _ _ j k

/-- Consecutive vertices are adjacent in `𝒢^ε`, for every `ω` and `ε ≥ 0`. -/
theorem mult_succ_ne_zero {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω) (k : ℤ) : S.mult ε ω k (k + 1) ≠ 0 :=
  bmEdgeCount_succ_ne_zero hε (S.bm ω).continuous.fst _ k

variable {S}

/-- Almost surely `η(t) → ∞` as `|t| → ∞`: under the mating-of-trees coupling, `η = ηL ∘ φ` for an increasing
homeomorphism `φ` of `ℝ` (`areaParam`) and the whole-plane space-filling SLE `ηL` is transient (`spaceFilling`). -/
theorem IsValid.ae_tendsto_cocompact {𝒮 : SpaceFillingSLEModel} {γ : ℝ} (hS : S.IsValid 𝒮 γ) :
    ∀ᵐ ω ∂S.P, Tendsto (S.η ω) (cocompact ℝ) (cocompact ℂ) := by
  obtain ⟨X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η', η₀, hC, htie⟩ := hS.matingOfTrees
  filter_upwards [hC.spaceFilling, hC.areaParam, htie] with ω hsf hap hω
  obtain ⟨⟨φ, -, hφ⟩, -⟩ := hap
  have hη : S.η ω = ηL ω ∘ φ := by
    rw [← hω.1]
    funext t
    exact hφ t
  rw [hη]
  exact hsf.2.1.comp φ.toHomeomorph.map_cocompact.le

end MatedCRTEnv

end MatedCRT
