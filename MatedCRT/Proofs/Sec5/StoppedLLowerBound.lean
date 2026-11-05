import MatedCRT.Proofs.Sec5.LLowerBound.OfInputs
import MatedCRT.Proofs.Sec5.IDLALowerBound.Stopped

/-!
# Lemma 5.4 on `V^ε(Λ_t)` (E-c1-5)

The proof of Lemma 5.4 (corrected.tex, proof of Lemma 5.4; formalized by x1 as `lLowerBound_of_adjacentCellsMeet`,
Proofs/Sec5/LLowerBound) uses only three properties of the domain `A = Λ^ε_t`: `A` is a finite subset of
`V^ε(B_ρ) \ V^ε(∂B_ρ)`, it lies in `V^ε(B_ρ)`, and the marked points `η(a)`, `a ∈ A`, lie in `B_ρ`. On the event
`{t < T}` the vertex set `V^ε(Λ_t)` of the cells meeting the harmonic ball has the same three properties as soon as
the cells meeting `B_ρ` have diameter at most `ρ/4`, because `Λ_t ⊆ B_{ρ/3}`. Hence the same argument (Green kernel
lower bound, Lemma 2.16; counting measure convergence, Lemma 2.9; crude Green bound, Lemma 2.15; reversibility and
domain monotonicity of the Green function) gives Lemma 5.4 on `V^ε(Λ_t)`, with `q = 1/4`.

* `stoppedLLowerBound_of_inputs : StoppedLLowerBoundStep 𝒮` from Lemmas 2.9, 2.15 and 2.16.
-/

namespace MatedCRT

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace StoppedLLowerBound

/-- A cell meeting `L ⊆ B_r` lies in `B_ρ` when the cells meeting `B_ρ` have diameter at most `d` and
`r + d ≤ ρ`. -/
theorem cell_subset_ball_of_mem_cellVertices {ε : ℝ} {η : ℝ → ℂ} (hη : Continuous η) {L : Set ℂ}
    {r ρ d : ℝ} (hL : L ⊆ ball 0 r) (hd : 0 ≤ d) (hrd : r + d ≤ ρ)
    (hsmall : ∀ k ∈ cellVertices ε η (ball 0 ρ), diam (cell ε η k) ≤ d)
    {a : ℤ} (ha : a ∈ cellVertices ε η L) : cell ε η a ⊆ ball 0 ρ := by
  obtain ⟨y, hyc, hyL⟩ := ha
  have hy : dist y 0 < r := hL hyL
  have haρ : a ∈ cellVertices ε η (ball 0 ρ) := ⟨y, hyc, show dist y 0 < ρ by linarith⟩
  intro x hx
  have hxy := ConstantOrderDiv.dist_le_of_mem_cell hη (hsmall a haρ) hx hyc
  show dist x 0 < ρ
  linarith [dist_triangle x y 0]

/-- A vertex with a nonempty cell contained in `B_ρ` is an interior vertex `a ∈ V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
theorem mem_ballInterior_of_cell_subset {ε : ℝ} {η : ℝ → ℂ} {ρ : ℝ} {a : ℤ}
    (hne : (cell ε η a).Nonempty) (hsub : cell ε η a ⊆ ball 0 ρ) : a ∈ ballInterior ε η ρ := by
  show a ∈ cellVertices ε η (ball 0 ρ) \ cellVertices ε η (frontier (ball 0 ρ))
  refine ⟨⟨_, hne.some_mem, hsub hne.some_mem⟩, ?_⟩
  rintro ⟨x, hx, hfront⟩
  rw [isOpen_ball.frontier_eq] at hfront
  exact hfront.2 (hsub hx)

end StoppedLLowerBound

open StoppedLLowerBound in
/-- **Lemma 5.4 on `V^ε(Λ_t)`** (`StoppedLLowerBoundStep`, E-c1-5) from the cited Lemmas 2.9, 2.15 and 2.16, with
`q = 1/4`: the proof of Lemma 5.4 applied to the domain `V^ε(Λ_t) ⊆ V^ε(B_ρ) \ V^ε(∂B_ρ)`. -/
theorem stoppedLLowerBound_of_inputs (𝒮 : SpaceFillingSLEModel)
    (h215 : GreenFunctionCrudeBoundStmt 𝒮) (h216 : GreenKernelLowerBoundStmt 𝒮)
    (h29 : CountingMeasureConvergenceStmt 𝒮) : StoppedLLowerBoundStep 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro Ω _ S hS Λ hΛ δ t hδ hδρ ht
  have hcell := adjacentCellsMeetAeStep 𝒮
  let ρ' : ℝ := (1 + ρ) / 2
  have hρ'0 : 0 < ρ' := by dsimp [ρ']; linarith
  have hρ'1 : ρ' < 1 := by dsimp [ρ']; linarith
  have hρρ' : ρ < ρ' := by dsimp [ρ']; linarith
  obtain ⟨ω, hω, h216a⟩ := h216 γ hγ hγ2
  obtain ⟨C, hC, h216b⟩ := h216a ρ' hρ'0 hρ'1
  obtain ⟨α, β, hα, hβ, h29a⟩ := h29 γ hγ hγ2
  obtain ⟨R, r, d, hR0, hr0, hd0, hRδ, hRρ, hrR, hgap, hdδ, hscale⟩ :=
    exists_green_lower_radii (C := C) hδ hρ1
  have hsep : ρ + R ≤ ρ' := by dsimp [ρ']; linarith
  have hgood : ∀ᵐ ξ ∂S.P, (IsAreaParametrized (S.μ ξ) (S.η ξ) ∧
      Tendsto (S.η ξ) (cocompact ℝ) (cocompact ℂ) ∧
      ∀ ε : ℝ, 0 < ε → IsLocallyFiniteMult (S.mult ε ξ)) ∧ MonotoneOn (Λ ξ) (Ioi 0) := by
    filter_upwards [hS.isAreaParametrized, hS.ae_tendsto_cocompact,
      hS.ae_isLocallyFiniteMult hγ hγ2 hcell, hΛ] with ξ h1 h2 h3 h4
    exact ⟨⟨h1, h2, h3⟩, h4.2.1.monotoneOn⟩
  have hall := ((((((probTendsToOne_of_ae hgood).inter
    (HarmonicBalls.PolyHighProb.probTendsToOne (h216b Ω S hS))).inter
    (HarmonicBalls.PolyHighProb.probTendsToOne (h29a ρ' hρ'0 hρ'1 Ω S hS))).inter
    (hS.probTendsToOne_small_cells (ρ + δ / 2) d hd0)).inter
    (hS.probTendsToOne_ball_mass_rpow ρ r α (1 / 2) hr0 hα (by norm_num))).inter
    (hS.probTendsToOne_ball_mass_rpow ρ r (1 / 4) (1 / 4) hr0 (by norm_num) (by norm_num))).inter
    (HarmonicBalls.PolyHighProb.probTendsToOne
      (h215 γ hγ hγ2 ρ (1 / 2) hρ hρ1 (by norm_num) (by norm_num) Ω S hS))
  have hfull : ProbTendsToOne S.P fun ε => {ξ | t < clusterExitTime (Λ ξ) ρ →
      ∀ a ∈ cellVertices ε (S.η ξ) (Λ ξ t),
        δ < infDist (vertexPoint ε (S.η ξ) a)
          (frontier (fillCells ε (S.η ξ) (cellVertices ε (S.η ξ) (Λ ξ t)))) →
        ε ^ (-(1 / 4 : ℝ)) ≤ (∑' b : cellVertices ε (S.η ξ) (Λ ξ t),
            greenFn (S.mult ε ξ) (cellVertices ε (S.η ξ) (Λ ξ t)) b a) /
          greenFn (S.mult ε ξ) (cellVertices ε (S.η ξ) (Λ ξ t)) a a} := by
    refine hall.mono_ev ?_
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ),
      (tendsto_rpow_nhdsGT_zero hω).eventually (Iio_mem_nhds (lt_min hR0 (sub_pos.mpr hρρ'))),
      Ioo_mem_nhdsGT (Real.exp_pos (-(3 / 2) * C))] with ε hε hε1 hpow hexp ξ hξ
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hη, hp, hlf⟩, hmono⟩, hg⟩, hc⟩, hsmall⟩, hmass1⟩, hmass2⟩, hcrude⟩ := hξ
    intro hT
    have hinv : Real.exp (3 / 2 * C) ≤ ε⁻¹ := by
      have h := inv_anti₀ hε hexp.2.le
      rwa [← Real.exp_neg, show -(-(3 / 2) * C) = 3 / 2 * C by ring] at h
    have hpowR : ε ^ ω ≤ R := (lt_of_lt_of_le hpow (min_le_left _ _)).le
    have hpowρ : ρ ≤ ρ' - ε ^ ω := by
      have := lt_of_lt_of_le hpow (min_le_right _ _)
      linarith
    have hlfε := hlf ε hε
    have hcons := S.mult_succ_ne_zero hε.le ξ
    have hΛt : Λ ξ t ⊆ ball 0 (ρ / 3) :=
      IDLALowerBound.subset_ball_div_three_of_lt_clusterExitTime hmono ht hT
    have hsmallρ : ∀ k ∈ cellVertices ε (S.η ξ) (ball 0 ρ), diam (cell ε (S.η ξ) k) ≤ d :=
      fun k hk => hsmall k (ConstantOrderDiv.cellVertices_mono' (ball_subset_ball (by linarith)) hk)
    have hcellsub : ∀ a ∈ cellVertices ε (S.η ξ) (Λ ξ t), cell ε (S.η ξ) a ⊆ ball 0 ρ :=
      fun a ha => cell_subset_ball_of_mem_cellVertices hη.1 hΛt hd0.le (by linarith) hsmallρ ha
    have hAB : cellVertices ε (S.η ξ) (Λ ξ t) ⊆ ballInterior ε (S.η ξ) ρ := by
      intro a ha
      refine mem_ballInterior_of_cell_subset ?_ (hcellsub a ha)
      obtain ⟨y, hy⟩ := ha
      exact ⟨y, hy.1⟩
    have hB : (ballInterior ε (S.η ξ) ρ).Finite := ballInterior_finite hη.1 hp hε
    have hA : (cellVertices ε (S.η ξ) (Λ ξ t)).Finite := hB.subset hAB
    have hAcell : cellVertices ε (S.η ξ) (Λ ξ t) ⊆ cellVertices ε (S.η ξ) (ball 0 ρ) :=
      hAB.trans ballInterior_subset_cellVertices_ball
    have hfirstA := greenFn_laplacian_fst hlfε hcons hA
    have hfirstB := greenFn_laplacian_fst hlfε hcons hB
    intro a ha hdist
    have hpoint : vertexPoint ε (S.η ξ) a ∈ ball 0 ρ :=
      hcellsub a ha (ConstantOrderDiv.vertexPoint_mem_cell hε.le _ _)
    obtain ⟨D, Cset, α', M, hCfin, hDC, hCA, hkernel, hcount, herr, hsm⟩ :=
      localData_of_green_counting hη hε hε1.2.le hδ hβ hA ha hdist hpoint
        hρ'0.le hsep hpowρ hpowR hRδ hrR hR0.le hgap hdδ hC hinv hscale hg hc hsmall
        (by simpa [div_eq_mul_inv, mul_comm] using hmass1 _ hpoint)
        (by simpa [div_eq_mul_inv, mul_comm] using hmass2 _ hpoint)
    have hN := greenSum_lower_of_count (S.mult_symm ε ξ) hlfε hcons hA hCfin hDC hCA hε
      hkernel hcount herr hsm
    have hD : 0 < greenFn (S.mult ε ξ) (cellVertices ε (S.η ξ) (Λ ξ t)) a a :=
      greenFn_diag_pos_of_firstStep ha hfirstA
    have hupper : greenFn (S.mult ε ξ) (cellVertices ε (S.η ξ) (Λ ξ t)) a a ≤ ε ^ (-(1 / 2 : ℝ)) :=
      (greenFn_mono_of_firstStep hlfε hcons hA hAB hfirstA hfirstB a a).trans
        (hcrude a (hAcell ha) a (hAcell ha))
    apply (le_div_iff₀ hD).2
    calc
      ε ^ (-(1 / 4 : ℝ)) * greenFn (S.mult ε ξ) (cellVertices ε (S.η ξ) (Λ ξ t)) a a
        ≤ ε ^ (-(1 / 4 : ℝ)) * ε ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hupper (Real.rpow_nonneg hε.le _)
      _ = ε ^ (-(3 / 4 : ℝ)) := by
          rw [← Real.rpow_add hε]
          congr 1
          norm_num
      _ ≤ _ := hN
  unfold TendsToOneOn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfull
    (fun _ => zero_le) fun ε => measure_mono fun ξ hξ h => hξ.2 (h hξ.1)

end MatedCRT
