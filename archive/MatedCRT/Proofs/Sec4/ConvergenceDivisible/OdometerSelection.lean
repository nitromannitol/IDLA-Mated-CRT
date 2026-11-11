import MatedCRT.Steps.Sec4.SubsequentialConvergence
import MatedCRT.Proofs.MatingOfTrees.AdjacentCells
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.OdometerSelectionProxy
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.OdometerSelectionDetStage
import MatedCRT.Proofs.Sec4.ConvergenceDivisible.OdometerSelectionDetLimit

/-! # `OdometerMeasurableSelectionStep` (Lemma 4.6, measurable choice of a convergent subsequence)

Theorem. For each fixed time `t > 0` and deterministic mesh sequence `εs → 0`, if almost surely some subsequence
of `rescaledMatedLeastSupersolution S ρ t (εs ·) ω` converges uniformly on `closedBall 0 ρ` to a Hölder continuous
limit, then a subsequence `Φ ω` can be chosen with `Φ ω k` measurable in `ω` for the envSigma σ-algebra, such that
almost surely `Φ ω` is strictly increasing and the selected subsequence converges uniformly to a Hölder
continuous limit on the closed ball.

Route (GAPS `OdometerMeasurableSelectionStep`, clarification 2026-11-06, position-indexed pigeonhole):
the dense Hölder classes `(m, j)` (`OdometerSelectionHolder`); envSigma proxies for the uniform-distance
events (`OdometerSelectionProxy`); the least-index recursion and its measurability (`OdometerSelectionRecursion`);
the deterministic stage argument (`OdometerSelectionDetStage`) and the limit (`OdometerSelectionDetLimit`). -/

namespace MatedCRT

open MeasureTheory Filter Topology Set Metric

theorem odometerMeasurableSelection_holds (𝒮 : SpaceFillingSLEModel) :
    OdometerMeasurableSelectionStep 𝒮 := by
  intro γ hγ hγ' ρ hρ hρ' Ω _ S hS t ht εs hε _ hpath
  set K : Set ℂ := closedBall (0 : ℂ) ρ with hKdef
  have hK : IsCompact K := isCompact_closedBall (0 : ℂ) ρ
  -- countable dense families and finite nets of the Hölder classes `(m, j)`
  choose cenMJ hcenMJ hdenMJ using fun m j : ℕ => exists_dense_seq_holderClass hK m j
  choose NetMJ hNetMJ using fun m j k : ℕ => exists_net_holderClass hK m j (cenMJ m j) (hdenMJ m j) k
  have hdec : ∀ m j : ℕ, (Nat.unpair (Nat.pair m j)).1 = m ∧ (Nat.unpair (Nat.pair m j)).2 = j :=
    fun m j => by rw [Nat.unpair_pair]; exact ⟨rfl, rfl⟩
  let cen : ℕ → ℕ → ℂ → ℝ := fun p i => cenMJ (Nat.unpair p).1 (Nat.unpair p).2 i
  let NetN : ℕ → ℕ → Finset ℕ := fun p k => NetMJ (Nat.unpair p).1 (Nat.unpair p).2 k
  let cls : ℕ → (ℂ → ℝ) → Prop := fun p h =>
    HolderClassOn K ((Nat.unpair p).1 : ℝ) (holderExp (Nat.unpair p).2) h
  have hcont : ∀ p i, ContinuousOn (cen p i) K := fun p i => (hcenMJ _ _ i).1
  have hcls : ∀ p i, cls p (cen p i) := fun p i => (hcenMJ _ _ i).2
  have hnet : ∀ p k h, cls p h → ∃ i ∈ NetN p k, ∀ x ∈ K, |h x - cen p i x| < (1 / 2 : ℝ) ^ k :=
    fun p k h hh => hNetMJ _ _ k h hh
  -- envSigma proxies for the uniform-distance events
  obtain ⟨G, hG, hGae⟩ := exists_selection_proxies hS hγ hγ' (adjacentCellsMeetAeStep 𝒮) ρ t ht εs hε
    K hK cen hcont
  set Pst : Ω → ℕ := selPair G with hPstdef
  have hPst : Measurable[S.envSigma] Pst := measurable_selPair hG
  -- the criterion of the chosen pair holds almost surely
  have hcritAe : ∀ᵐ ω ∂S.P, ∃ p, ω ∈ critSet G p := by
    filter_upwards [hpath, hGae] with ω hω hag
    obtain ⟨φ, hφ, w, hwc, hwh, hwu⟩ := hω
    obtain ⟨m, j, hwcls⟩ := exists_holderClass_of_isHolder hK hwc hwh
    refine ⟨Nat.pair m j, ?_⟩
    have hcen_eq : ∀ i, cen (Nat.pair m j) i = cenMJ m j i := fun i => by
      simp only [cen, (hdec m j).1, (hdec m j).2]
    simp only [critSet, Set.mem_iInter, Set.mem_iUnion]
    intro q N
    obtain ⟨i, hi⟩ := hdenMJ m j w hwcls ((1 / 2 : ℝ) ^ (q + 1)) (by positivity)
    have hev := (Metric.tendstoUniformlyOn_iff.1 hwu) ((1 / 2 : ℝ) ^ (q + 1)) (by positivity)
    obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hev
    refine ⟨φ (max k0 N), ?_, i, ?_⟩
    · exact (le_max_right k0 N).trans (hφ.id_le _)
    · refine (hag (Nat.pair m j) i (φ (max k0 N)) q).2 fun x hx => ?_
      have h1 := hk0 (max k0 N) (le_max_left _ _) x hx
      have h2 := hi x hx
      rw [hcen_eq i]
      have h1' : |w x - rescaledMatedLeastSupersolution S ρ t (εs (φ (max k0 N))) ω x| <
          (1 / 2 : ℝ) ^ (q + 1) := by
        rw [← Real.dist_eq]
        exact h1
      have h3 := abs_sub_le (rescaledMatedLeastSupersolution S ρ t (εs (φ (max k0 N))) ω x) (w x)
        (cenMJ m j i x)
      have h4 : |w x - cenMJ m j i x| = |cenMJ m j i x - w x| := abs_sub_comm _ _
      have h5 : |cenMJ m j i x - w x| < (1 / 2 : ℝ) ^ (q + 1) := by
        rw [← h4]
        exact h2
      have h6 : |rescaledMatedLeastSupersolution S ρ t (εs (φ (max k0 N))) ω x - w x| =
          |w x - rescaledMatedLeastSupersolution S ρ t (εs (φ (max k0 N))) ω x| := abs_sub_comm _ _
      have hpow : (1 / 2 : ℝ) ^ (q + 1) + (1 / 2 : ℝ) ^ (q + 1) = (1 / 2 : ℝ) ^ q := by ring
      have h7 : |rescaledMatedLeastSupersolution S ρ t (εs (φ (max k0 N))) ω x - cenMJ m j i x| ≤
          |rescaledMatedLeastSupersolution S ρ t (εs (φ (max k0 N))) ω x - w x| +
            |w x - cenMJ m j i x| := abs_sub_le _ _ _
      linarith
  -- the deterministic data at a sample point
  let D : SelStatic Ω := ⟨K, cls, cen, NetN, G, Pst, hcls, hnet⟩
  let F : ℕ → Ω → ℂ → ℝ := fun n ω x => rescaledMatedLeastSupersolution S ρ t (εs n) ω x
  refine ⟨fun ω k => selSeq G Pst NetN k ω, fun k => measurable_selSeq hPst hG k, ?_⟩
  filter_upwards [hcritAe, hGae] with ω hex hag
  have hcrit : ω ∈ critSet G (Pst ω) := (leastOr_spec (fun ω' p => ω' ∈ critSet G p) ω hex).1
  have hagF : ∀ p i n q, ω ∈ D.G p i n q ↔ ∀ x ∈ D.K, |F n ω x - D.cen p i x| ≤ (1 / 2 : ℝ) ^ q :=
    fun p i n q => hag p i n q
  refine ⟨SelStatic.selSeq_strictMono D F hagF hcrit, ?_⟩
  obtain ⟨w, hwc, hwh, hwu⟩ := holder_limit_of_centers
    (m := (Nat.unpair (Pst ω)).1) (j := (Nat.unpair (Pst ω)).2)
    (u := fun ℓ x => F (selSeq G Pst NetN ℓ ω) ω x)
    (c := fun k x => D.cen (Pst ω) (idxSel G Pst NetN (inTSet G Pst NetN k) k ω) x)
    (fun k ℓ ℓ' hℓ hℓ' x hx => SelStatic.selSeq_cauchy D F hagF hcrit k ℓ ℓ' hℓ hℓ' hx)
    (fun k x hx => SelStatic.inT_succ_truth D F hagF k _
      (SelStatic.stage_mem D F hagF hcrit (k + 1)) x hx)
    (fun k => hcls (Pst ω) (idxSel G Pst NetN (inTSet G Pst NetN k) k ω))
  exact ⟨w, hwc, hwh, hwu⟩

end MatedCRT
