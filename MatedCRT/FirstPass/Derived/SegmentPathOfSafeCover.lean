import MatedCRT.FirstPass.Derived.SegmentReachOfCoupling
import MatedCRT.FirstPass.Derived.GreenCellSumFromBalls
import MatedCRT.FirstPass.S3t.CellGeometry

/-!
# The segment paths of the Green kernel upper bound

Step 1 of the proof of the Green kernel upper bound (Berestycki-Gwynne arXiv:2003.10320, Lemma 5.3) bounds an
effective resistance by the method of random paths: from a vertex `b ∈ V^ε(B_ρ(0)) \ V^ε(∂B_ρ(0))`, follow a
uniformly random segment `[η(εb), η(εb) + ℓ e^{iθ}]` and choose, among the cells it meets, a self-avoiding path of
`𝒢^ε` from `b` to a vertex of `V^ε(∂B_ρ(0))` through cells meeting `B_ρ(0)`. The path must depend on `θ` only through
the finite set of cells met by the segment (`LatticeProb.segmentPath`).

For a valid environment such paths exist almost surely, for every mesh and every direction: by the safe cell cover
connectivity (`MatedCRTEnv.IsValid.ae_reachable_in_safe_cell_cover`) the cells met by the initial piece of the
segment up to its exit from `B_ρ(0)` are connected inside the vertices hit by the segment and meeting `B_ρ(0)`
(`segmentReach_of_safeCover_from`), and a path of the induced subgraph can be shortened to a self-avoiding one.
Hence the segment path input `hpath` of `greenKernelUpperBoundStmt_of_ring_single` holds for every model, and the
Green kernel upper bound (Lemma 5.4) follows from the cell size estimate, the ring events and the single-ball
estimate alone.

## Main results

* `exists_nodup_isChain_of_reachable_induce`: reachability in an induced subgraph gives a self-avoiding chain of
  edges inside the vertex set.
* `exists_segmentPath_of_safeCover`: the deterministic segment paths from a vertex point.
* `segmentPathInput_holds`: the segment path input, with polynomially high probability (in fact almost surely).
* `greenKernelUpperBoundStmt_of_ring_single_cellSize`: Lemma 5.4 without the segment path input.
-/

open Set Metric MeasureTheory Filter Topology HarmonicBalls LatticeProb

namespace MatedCRT

/-- **Self-avoiding paths in an induced subgraph.** If `k` is reachable from `j` in the subgraph of `adjGraph m`
induced by `U`, with `m` symmetric, there is a list `j :: p` without repetitions, whose consecutive entries are
joined by an edge, which ends at `k` and lies in `U`. -/
theorem exists_nodup_isChain_of_reachable_induce {m : ℤ → ℤ → ℕ} (hm : ∀ a b, m a b = m b a)
    {U : Set ℤ} {j k : ℤ} {hj : j ∈ U} {hk : k ∈ U}
    (h : ((adjGraph m).induce U).Reachable ⟨j, hj⟩ ⟨k, hk⟩) :
    ∃ p : List ℤ, (j :: p).Nodup ∧ (j :: p).IsChain (fun a c => m a c ≠ 0) ∧
      (j :: p).getLast (List.cons_ne_nil j p) = k ∧ ∀ v ∈ j :: p, v ∈ U := by
  obtain ⟨w⟩ := h
  have hs : w.bypass.support.map Subtype.val = j :: w.bypass.support.tail.map Subtype.val := by
    conv_lhs => rw [← w.bypass.cons_tail_support]
    rfl
  refine ⟨w.bypass.support.tail.map Subtype.val, ?_, ?_, ?_, ?_⟩
  · rw [← hs]
    exact w.bypass_isPath.support_nodup.map Subtype.val_injective
  · rw [← hs, List.isChain_map]
    refine w.bypass.isChain_adj_support.imp fun a c hac => ?_
    simp only [SimpleGraph.induce_adj, adjGraph, SimpleGraph.fromRel_adj] at hac
    rcases hac.2 with h1 | h1
    · exact h1
    · rwa [hm]
  · have key : ∀ (l₁ l₂ : List ℤ) (_ : l₁ = l₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []),
        l₁.getLast h₁ = l₂.getLast h₂ := by
      rintro l₁ _ rfl _ _
      rfl
    rw [← key _ _ hs (by rw [hs]; exact List.cons_ne_nil _ _) (List.cons_ne_nil _ _), List.getLast_map,
      SimpleGraph.Walk.getLast_support]
  · intro v hv
    rw [← hs, List.mem_map] at hv
    obtain ⟨a, _, rfl⟩ := hv
    exact a.2

/-- **The segment paths from a vertex point** (Berestycki-Gwynne 2020, Lemma 5.3, Step 1). Let `η` be continuous,
proper and onto, `m` symmetric, and assume the safe cell cover connectivity. For every
`b ∈ V^ε(B_ρ(0)) \ V^ε(∂B_ρ(0))` there are a length `ℓ`, a finite set `Y` and a rule `F` choosing from every finite
set of vertices a list in it such that, for every direction `θ`, the path `segmentPath (η(εb)) ℓ H Y F θ` is
self-avoiding, consecutive vertices are joined by an edge, it starts at `b`, its vertices have cells meeting
`B_ρ(0)`, and it ends outside `V^ε(B_ρ(0)) \ V^ε(∂B_ρ(0))`. -/
theorem exists_segmentPath_of_safeCover {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {η : ℝ → ℂ} (hη : Continuous η) (hp : Tendsto η (cocompact ℝ) (cocompact ℂ))
    (hsurj : Function.Surjective η) {m : ℤ → ℤ → ℕ} (hm : ∀ a b, m a b = m b a)
    (hcover : ∀ K : Set ℂ, IsPreconnected K → IsCompact K → ∀ U : Set ℤ,
      ∀ (hsafe : ∀ j, (K ∩ cell ε η j).Nonempty → j ∈ U), ∀ j k : ℤ,
      ∀ (hj : (K ∩ cell ε η j).Nonempty) (hk : (K ∩ cell ε η k).Nonempty),
      ((adjGraph m).induce U).Reachable ⟨j, hsafe j hj⟩ ⟨k, hsafe k hk⟩)
    {b : ℤ} (hb : b ∈ interiorCellVertices ε η (ball 0 ρ)) :
    ∃ (ℓ : ℝ) (Y : Finset ℤ) (F : Finset ℤ → List ℤ), (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
      ∀ θ : ℝ, (segmentPath (vertexPoint ε η b) ℓ (cell ε η) Y F θ).Nodup ∧
        (segmentPath (vertexPoint ε η b) ℓ (cell ε η) Y F θ).IsChain (fun a c => m a c ≠ 0) ∧
        ∃ p, segmentPath (vertexPoint ε η b) ℓ (cell ε η) Y F θ = b :: p ∧
          (∀ v ∈ b :: p, v ∈ cellVertices ε η (ball 0 ρ)) ∧
          (b :: p).getLast (List.cons_ne_nil b p) ∉ interiorCellVertices ε η (ball 0 ρ) := by
  classical
  have hbz : vertexPoint ε η b ∈ cell ε η b := vertexPoint_mem_cell hε.le η b
  have hconn : IsConnected (cell ε η b) :=
    (isConnected_Icc (by nlinarith)).image η hη.continuousOn
  have hzb : vertexPoint ε η b ∈ ball (0 : ℂ) ρ :=
    TruncatedLaws.cell_subset_of_mem_interiorCellVertices isOpen_ball hb hconn hbz
  obtain ⟨Y, hY⟩ := segmentReach_of_safeCover_from hε hρ hρ1 hη hp hsurj hcover hbz hzb
  let P : Finset ℤ → List ℤ → Prop := fun T l => l.Nodup ∧ l.IsChain (fun a c => m a c ≠ 0) ∧
    (∃ p, l = b :: p ∧ (∀ v ∈ b :: p, v ∈ cellVertices ε η (ball 0 ρ)) ∧
      (b :: p).getLast (List.cons_ne_nil b p) ∉ interiorCellVertices ε η (ball 0 ρ)) ∧ ∀ a ∈ l, a ∈ T
  let F : Finset ℤ → List ℤ := fun T => if h : ∃ l, P T l then h.choose else []
  have hF : ∀ T, (∃ l, P T l) → P T (F T) := by
    intro T h
    simp only [F]
    split_ifs
    exact h.choose_spec
  refine ⟨2, Y, F, fun T a ha => ?_, fun θ => ?_⟩
  · simp only [F] at ha
    split_ifs at ha with h
    · exact h.choose_spec.2.2.2 a ha
    · simp at ha
  · have hex : ∃ l, P (hitFinset Y (fun y => segmentDirections (vertexPoint ε η b) 2 (cell ε η y)) θ) l := by
      obtain ⟨_, c, hc, _, _, hreach⟩ := hY θ
      obtain ⟨p, hnd, hch, hlast, hmem⟩ := exists_nodup_isChain_of_reachable_induce hm hreach
      refine ⟨b :: p, hnd, hch, ⟨p, rfl, fun v hv => (hmem v hv).2, ?_⟩, fun v hv => (hmem v hv).1⟩
      rw [hlast]
      exact hc
    obtain ⟨h1, h2, h3, -⟩ := hF _ hex
    exact ⟨h1, h2, h3⟩

/-- An event family holding almost surely for every positive mesh holds with polynomially high probability. -/
theorem polyHighProb_of_ae_forall_pos {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'}
    {E : ℝ → Set Ω'} (h : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ω ∈ E ε) : PolyHighProb P E := by
  refine ⟨1, one_pos, 0, 1, one_pos, fun r hr _ => ?_⟩
  have h0 : P (E r)ᶜ = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro ω hω hall
    exact hω (hall r hr)
  simp [h0]

/-- **The segment path input of Lemma 5.4 holds** for every model: for a valid environment, almost surely, for
every mesh `ε > 0` and every `b ∈ V^ε(B_{(1+ρ)/2}(0)) \ V^ε(∂B_{(1+ρ)/2}(0))`, the segment paths of
`exists_segmentPath_of_safeCover` exist; in particular they exist with polynomially high probability. -/
theorem segmentPathInput_holds (𝒮 : SpaceFillingSLEModel) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      PolyHighProb S.P fun ε => {ω | ∀ b ∈ interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)),
        ∃ (ℓ : ℝ) (Y : Finset ℤ) (F : Finset ℤ → List ℤ), (∀ T : Finset ℤ, ∀ a ∈ F T, a ∈ T) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).Nodup) ∧
        (∀ᵐ θ ∂uniformDirection,
          (segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ).IsChain
            fun a c => S.mult ε ω a c ≠ 0) ∧
        (∀ᵐ θ ∂uniformDirection, ∃ p,
          segmentPath (vertexPoint ε (S.η ω) b) ℓ (cell ε (S.η ω)) Y F θ = b :: p ∧
          (∀ v ∈ b :: p, v ∈ cellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2))) ∧
          (b :: p).getLast (List.cons_ne_nil b p) ∉
            interiorCellVertices ε (S.η ω) (ball 0 ((1 + ρ) / 2)))} := by
  intro γ _ _ ρ hρ hρ1 Ω _ S hS
  have hρ' : 0 < (1 + ρ) / 2 := by linarith
  have hρ1' : (1 + ρ) / 2 < 1 := by linarith
  refine polyHighProb_of_ae_forall_pos ?_
  filter_upwards [hS.ae_reachable_in_safe_cell_cover, hS.ae_tendsto_cocompact,
    hS.isAreaParametrized] with ω hcov hp harea
  intro ε hε b hb
  obtain ⟨ℓ, Y, F, hF, hθ⟩ := exists_segmentPath_of_safeCover hε hρ' hρ1' harea.1 hp harea.2.2.1
    (S.mult_symm ε ω) (hcov ε hε) hb
  exact ⟨ℓ, Y, F, hF, .of_forall fun θ => (hθ θ).1, .of_forall fun θ => (hθ θ).2.1,
    .of_forall fun θ => (hθ θ).2.2⟩

/-- **The Green kernel upper bound** (Berestycki-Gwynne 2020, Lemma 5.4) from the cell size estimate, the ring
events of Lemma 3.10 (`hRing`) and the single-ball estimate of Gwynne-Miller-Sheffield (2019), Proposition 2.9
(`hsingle`): the segment path input of `greenKernelUpperBoundStmt_of_ring_single` is `segmentPathInput_holds`. -/
theorem greenKernelUpperBoundStmt_of_ring_single_cellSize {𝒮 : SpaceFillingSLEModel}
    (hsize : CellSizeEstimateStmt 𝒮)
    (hRing : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ z' : ℂ, ‖z'‖ < ρ' → ∀ s' : ℝ, ε ^ β₀ ≤ s' →
        2 * s' ≤ ρ' - ‖z'‖ →
        S.P {ω | ¬ RingSeparates (S.mult ε ω) ε (S.η ω) p z' s'} ≤ ENNReal.ofReal (C * ε ^ α₀))
    (hsingle : ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ β₀ α₀ : ℝ, 0 < β₀ ∧ 0 < α₀ ∧ ∀ ρ' : ℝ, 0 < ρ' → ρ' < 1 →
      ∃ A : ℝ, 0 < A ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
        ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (z : ℂ) (r : ℝ), ε ^ β₀ ≤ r → ball z r ⊆ ball 0 ρ' →
          S.P {ω | ¬ ∀ T : Finset ℤ, (∀ k ∈ T, k ∈ cellVertices ε (S.η ω) (ball z r)) →
            ∑ k ∈ T, (mdeg (S.mult ε ω) k : ℝ) * diam (cell ε (S.η ω) k) ^ 2 ≤ A * r ^ 2} ≤
              ENNReal.ofReal (C * ε ^ α₀)) :
    GreenKernelUpperBoundStmt 𝒮 :=
  greenKernelUpperBoundStmt_of_ring_single hsize hRing hsingle (segmentPathInput_holds 𝒮)

end MatedCRT
