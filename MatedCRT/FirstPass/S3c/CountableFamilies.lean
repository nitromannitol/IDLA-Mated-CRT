import MatedCRT.FirstPass.S3c.PointwiseSelection
import MatedCRT.FirstPass.S3c.Thinning
import MatedCRT.FirstPass.Frozen.S3S4

/-!
# Lemma 3.1 (corrected), countable families: the diagonal subsequence

The corrected Lemma 3.1 (paper/idla_mated_crt-corrected.tex, lemma:discrete-potential-tightness, last sentence): "The
subsequence can be chosen simultaneously for any countable collection of such function families and domains indexed by
the same `𝓔`." Audit notes/fp-gaps/CHATGPT-idla-3-1-audit.md §1.4: diagonalize.

Stage `j` applies `tightness_selection_pointwise` to the family `j`, pulled back along the current random subsequence
`R_j` (`E' ω n = E ω (R_j ω n)`); `R_{j+1} = R_j ∘ ψ_j`; the diagonal is `Φ ω k = R_{k+1} ω k`. For `k ≥ j` the terms
`Φ ω k` lie in the range of `R_{j+1} ω`, which gives the convergence of every family along `Φ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal NNReal

namespace MatedCRT.S3c

/-- Measurability of `ω ↦ f ω (k ω)` for a measurable random index `k` and a family `f ω m` measurable in `ω` for each
index `m` (the index set `ℕ` is countable). -/
theorem measurable_eval_comp {Ω γ : Type*} (mΩ : MeasurableSpace Ω) [MeasurableSpace γ] (f : Ω → ℕ → γ)
    (hf : ∀ m, Measurable[mΩ] fun ω => f ω m) {k : Ω → ℕ} (hk : Measurable[mΩ] k) :
    Measurable[mΩ] fun ω => f ω (k ω) := by
  let _inst : MeasurableSpace Ω := mΩ
  have h : Measurable fun p : Ω × ℕ => f p.1 p.2 :=
    measurable_from_prod_countable_left fun m => hf m
  exact h.comp (measurable_id.prodMk hk)

/-- The rescaled function `ū^ε` at the sample `ω` and the scale index `n` (write-up eq:discrete-scaling). -/
noncomputable def rsc {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω) (E : Ω → ℕ → ℝ) (u : Ω → ℕ → ℤ → ℝ) (ω : Ω) (n : ℕ) :
    ℂ → ℝ :=
  rescale (S.mε (E ω n)) (E ω n) (S.η ω) (u ω n)

/-- Pulling the samplewise admissibility back along a strictly increasing `R ω` (at the sample `ω`). -/
theorem pw_pull {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {D : Set ℂ} {e : ℕ → ℝ} {E : Ω → ℕ → ℝ}
    {u : Ω → ℕ → ℤ → ℝ} {C : Ω → ℝ} {ω : Ω} {R : Ω → ℕ → ℕ} (hR : StrictMono (R ω))
    (h : PointwiseTightnessData S D e E u C ω) :
    PointwiseTightnessData S D e (fun ω' n => E ω' (R ω' n)) (fun ω' n => u ω' (R ω' n)) C ω := by
  obtain ⟨hEe, hEt, hCp, hlap, hbd⟩ := h
  have hR' : Tendsto (R ω) atTop atTop := tendsto_atTop_mono (fun n => hR.id_le n) tendsto_id
  exact ⟨fun n => hEe (R ω n), hEt.comp hR', hCp, fun n a ha => hlap (R ω n) a ha,
    fun n a ha => hbd (R ω n) a ha⟩

/-- The "moreover" hypotheses are inherited by a pulled-back family (every index of the pulled family is an index of
the original). -/
theorem holder_pull {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω} {D : Set ℂ} {E : Ω → ℕ → ℝ}
    {u : Ω → ℕ → ℤ → ℝ} {ω : Ω} (R : Ω → ℕ → ℕ) (h : HasHolderBoundaryData S D E u ω) :
    HasHolderBoundaryData S D (fun ω' n => E ω' (R ω' n)) (fun ω' n => u ω' (R ω' n)) ω := by
  obtain ⟨hs, hharm, χ, C', hχ, hχ1, hC', hdat⟩ := h
  exact ⟨hs, fun n a ha => hharm (R ω n) a ha, χ, C', hχ, hχ1, hC', fun n hn a ha b hb => hdat (R ω n) hn a ha b hb⟩

/-- A uniform convergence along `R'` transfers to a subsequence `Φ` whose tail lies in the range of `R'`. -/
theorem tendstoUniformlyOn_diag {R' Φ : ℕ → ℕ} (hR' : StrictMono R') (hΦ : StrictMono Φ) (j : ℕ)
    (hrange : ∀ k, j ≤ k → ∃ p, Φ k = R' p) {F : ℕ → ℂ → ℝ} {f : ℂ → ℝ} {O : Set ℂ}
    (h : TendstoUniformlyOn (fun m => F (R' m)) f atTop O) :
    TendstoUniformlyOn (fun k => F (Φ k)) f atTop O := by
  rw [tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 (h ε hε)
  refine eventually_atTop.2 ⟨max j (R' M), fun k hk => ?_⟩
  obtain ⟨p, hp⟩ := hrange k (le_of_max_le_left hk)
  have h1 : R' M ≤ Φ k := le_trans (le_of_max_le_right hk) (hΦ.id_le k)
  have h2 : M ≤ p := hR'.le_iff_le.1 (hp ▸ h1)
  intro x hx
  rw [hp]
  exact hM p h2 x hx

/-- **Lemma 3.1, corrected, countable families** (`DiscretePotentialTightnessCountableStmt`; [C11] and the last sentence
of the corrected Lemma 3.1): one probability-one event `Ω₀` and one measurable subsequence `Φ`, for every countable family
of domains and data indexed by the same scales `E`. At every `ω ∈ Ω₀` at which all the families are admissible
(`PointwiseTightnessData`), `Φ ω` is strictly increasing and every family converges along `Φ ω` (uniformly on compacts of
its domain, and on the closure under the "moreover" hypotheses). -/
def DiscretePotentialTightnessCountableStmt (𝒮 : SpaceFillingSLEModel) : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : MatedCRTEnv Ω), S.IsValid 𝒮 γ →
  ∀ σ₀ : ℕ → ℝ, (∀ n, 0 < σ₀ n) → Tendsto σ₀ atTop (𝓝 0) →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω₀ : Set Ω, (∀ᵐ ω ∂S.P, ω ∈ Ω₀) ∧
  ∀ D : ℕ → Set ℂ, (∀ j, D j ⊆ ball 0 ρ ∧ IsOpen (D j) ∧ IsConnected (D j)) →
  ∀ (E : Ω → ℕ → ℝ) (u : ℕ → Ω → ℕ → ℤ → ℝ) (C : ℕ → Ω → ℝ),
    (∀ n, Measurable[S.envSigma] fun ω => E ω n) → (∀ j n a, Measurable[S.envSigma] fun ω => u j ω n a) →
    (∀ j, Measurable[S.envSigma] (C j)) →
  ∃ Φ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => Φ ω k) ∧
    ∀ ω ∈ Ω₀, (∀ j, PointwiseTightnessData S (D j) (fun k => σ₀ (φ k)) E (u j) (C j) ω) →
      StrictMono (Φ ω) ∧ ∀ j, ∃ ubar : ℂ → ℝ, ContinuousOn ubar (D j) ∧
        (∀ O : Set ℂ, IsCompact O → closure O ⊆ D j →
          TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u j ω (Φ ω k)))
            ubar atTop O) ∧
        (HasHolderBoundaryData S (D j) E (u j) ω →
          TendstoUniformlyOn (fun k => rescale (S.mε (E ω (Φ ω k))) (E ω (Φ ω k)) (S.η ω) (u j ω (Φ ω k)))
            ubar atTop (closure (D j)))

/-- **Lemma 3.1, corrected, countable faithful form** (`DiscretePotentialTightnessCountableStmt`), by diagonalization of
the single-family samplewise selection `tightness_selection_pointwise`. -/
theorem firstPass_3_1_countable {𝒮 : SpaceFillingSLEModel} (hm : MepsScalingInput 𝒮) (h27 : VolumeGrowthStmt)
    (h218 : ExitTimeUpperBoundStmt 𝒮) (h32 : FrozenDiscreteHolderContinuityCorrected 𝒮) :
    DiscretePotentialTightnessCountableStmt 𝒮 := by
  intro γ hγ hγ2 ρ hρ hρ1 Ω _ S hS σ₀ hpos hlim
  obtain ⟨φ, hφ, hpoly⟩ := exists_polySummable_thinning hpos hlim
  obtain ⟨Ω₀, hΩ₀, hsel⟩ := tightness_selection_pointwise hm (boundedExitTimeRV_of_steps h27) h218 h32
    (adjacentCellsMeetAeStep 𝒮) γ hγ hγ2 ρ hρ hρ1 Ω S hS (fun k => σ₀ (φ k)) hpoly
  refine ⟨φ, hφ, Ω₀, hΩ₀, fun D hD E u C hEm hum hCm => ?_⟩
  -- one stage: family `j` pulled back along a measurable random subsequence `R`
  have stage : ∀ (j : ℕ) (R : Ω → ℕ → ℕ), (∀ m, Measurable[S.envSigma] fun ω => R ω m) →
      ∃ ψ : Ω → ℕ → ℕ, (∀ k, Measurable[S.envSigma] fun ω => ψ ω k) ∧
        ∀ ω ∈ Ω₀, PointwiseTightnessData S (D j) (fun k => σ₀ (φ k)) E (u j) (C j) ω → StrictMono (R ω) →
          StrictMono (ψ ω) ∧ ∃ ubar : ℂ → ℝ, ContinuousOn ubar (D j) ∧
          (∀ O : Set ℂ, IsCompact O → closure O ⊆ D j →
            TendstoUniformlyOn (fun m => rsc S E (u j) ω (R ω (ψ ω m))) ubar atTop O) ∧
          (HasHolderBoundaryData S (D j) E (u j) ω →
            TendstoUniformlyOn (fun m => rsc S E (u j) ω (R ω (ψ ω m))) ubar atTop (closure (D j))) := by
    intro j R hR
    obtain ⟨ψ, hψm, hψ⟩ := hsel (D j) (hD j).1 (hD j).2.1 (hD j).2.2
      (fun ω n => E ω (R ω n)) (fun ω n a => u j ω (R ω n) a) (C j)
      (fun n => measurable_eval_comp S.envSigma (fun ω m => E ω m) hEm (hR n))
      (fun n a => measurable_eval_comp S.envSigma (fun ω m => u j ω m a) (fun m => hum j m a) (hR n))
      (hCm j)
    refine ⟨ψ, hψm, fun ω hω hPW hRω => ?_⟩
    obtain ⟨hmono, ubar, hC, hO, hHol⟩ := hψ ω hω (pw_pull (R := R) hRω hPW)
    exact ⟨hmono, ubar, hC, hO, fun hH => hHol (holder_pull R hH)⟩
  choose ψf hψfm hψf using stage
  -- the random subsequences `R_j`, with `R_0 = id` and `R_{j+1} = R_j ∘ ψ_j`
  obtain ⟨Rs, hRs0, hRsS⟩ : ∃ Rs : ℕ → {R : Ω → ℕ → ℕ // ∀ m, Measurable[S.envSigma] fun ω => R ω m},
      (∀ ω n, (Rs 0).1 ω n = n) ∧
      ∀ j ω n, (Rs (j + 1)).1 ω n = (Rs j).1 ω (ψf j (Rs j).1 (Rs j).2 ω n) :=
    ⟨fun j => Nat.rec (motive := fun _ => {R : Ω → ℕ → ℕ // ∀ m, Measurable[S.envSigma] fun ω => R ω m})
      ⟨fun _ n => n, fun _ => measurable_const⟩
      (fun j Rj => ⟨fun ω n => Rj.1 ω (ψf j Rj.1 Rj.2 ω n),
        fun m => measurable_eval_comp S.envSigma Rj.1 Rj.2 (hψfm j Rj.1 Rj.2 m)⟩) j,
      fun ω n => rfl, fun j ω n => rfl⟩
  -- the invariant: at the admissible samples every `R_j ω` is strictly increasing
  have hmono : ∀ ω ∈ Ω₀, (∀ j, PointwiseTightnessData S (D j) (fun k => σ₀ (φ k)) E (u j) (C j) ω) →
      ∀ j, StrictMono ((Rs j).1 ω) := by
    intro ω hω hPW j
    induction j with
    | zero =>
      have h0 : (Rs 0).1 ω = id := funext (hRs0 ω)
      rw [h0]
      exact strictMono_id
    | succ j ih =>
      have h1 : (Rs (j + 1)).1 ω = (Rs j).1 ω ∘ ψf j (Rs j).1 (Rs j).2 ω := funext fun n => hRsS j ω n
      rw [h1]
      exact ih.comp (hψf j (Rs j).1 (Rs j).2 ω hω (hPW j) ih).1
  -- ranges: the tail of the diagonal lies in the range of each `R_{s}`
  have hrange : ∀ s t, s ≤ t → ∀ ω n, ∃ p, (Rs t).1 ω n = (Rs s).1 ω p := by
    intro s t hst
    induction t, hst using Nat.le_induction with
    | base => intro ω n; exact ⟨n, rfl⟩
    | succ t hst ih =>
      intro ω n
      obtain ⟨p, hp⟩ := ih ω (ψf t (Rs t).1 (Rs t).2 ω n)
      exact ⟨p, by rw [hRsS, hp]⟩
  -- the diagonal `Φ ω k = R_{k+1} ω k` is strictly increasing at the admissible samples
  have hΦmono : ∀ ω ∈ Ω₀, (∀ j, PointwiseTightnessData S (D j) (fun k => σ₀ (φ k)) E (u j) (C j) ω) →
      StrictMono (fun k => (Rs (k + 1)).1 ω k) := by
    intro ω hω hPW
    refine strictMono_nat_of_lt_succ fun k => ?_
    have hk1 := hmono ω hω hPW (k + 1)
    have hψk := (hψf (k + 1) (Rs (k + 1)).1 (Rs (k + 1)).2 ω hω (hPW (k + 1)) hk1).1
    have h1 : (Rs (k + 1)).1 ω k < (Rs (k + 1)).1 ω (k + 1) := hk1 (Nat.lt_succ_self k)
    have h2 : (Rs (k + 1)).1 ω (k + 1) ≤ (Rs (k + 1)).1 ω (ψf (k + 1) (Rs (k + 1)).1 (Rs (k + 1)).2 ω (k + 1)) :=
      hk1.monotone (hψk.id_le (k + 1))
    show (Rs (k + 1)).1 ω k < (Rs (k + 1 + 1)).1 ω (k + 1)
    rw [hRsS (k + 1) ω (k + 1)]
    exact h1.trans_le h2
  refine ⟨fun ω k => (Rs (k + 1)).1 ω k, fun k => (Rs (k + 1)).2 k, fun ω hω hPW =>
    ⟨hΦmono ω hω hPW, fun j => ?_⟩⟩
  obtain ⟨-, ubar, hCt, hO, hHol⟩ := hψf j (Rs j).1 (Rs j).2 ω hω (hPW j) (hmono ω hω hPW j)
  -- the stage-`j` convergence is along `R_{j+1}`: the reindexing `R_{j+1} = R_j ∘ ψ_j`
  have hfun : (fun m => rsc S E (u j) ω ((Rs j).1 ω (ψf j (Rs j).1 (Rs j).2 ω m))) =
      (fun m => rsc S E (u j) ω ((Rs (j + 1)).1 ω m)) := by
    funext m
    rw [hRsS]
  have hrng : ∀ k, j ≤ k → ∃ p, (fun ω k => (Rs (k + 1)).1 ω k) ω k = (Rs (j + 1)).1 ω p :=
    fun k hk => hrange (j + 1) (k + 1) (by omega) ω k
  refine ⟨ubar, hCt, fun O hO' hcl => ?_, fun hH => ?_⟩
  · have hc : TendstoUniformlyOn (fun m => rsc S E (u j) ω ((Rs (j + 1)).1 ω m)) ubar atTop O := by
      rw [← hfun]
      exact hO O hO' hcl
    exact tendstoUniformlyOn_diag (F := rsc S E (u j) ω) (hmono ω hω hPW (j + 1)) (hΦmono ω hω hPW) j hrng hc
  · have hc : TendstoUniformlyOn (fun m => rsc S E (u j) ω ((Rs (j + 1)).1 ω m)) ubar atTop (closure (D j)) := by
      rw [← hfun]
      exact hHol hH
    exact tendstoUniformlyOn_diag (F := rsc S E (u j) ω) (hmono ω hω hPW (j + 1)) (hΦmono ω hω hPW) j hrng hc

end MatedCRT.S3c
