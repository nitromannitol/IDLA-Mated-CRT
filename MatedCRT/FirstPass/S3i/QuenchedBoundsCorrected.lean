import MatedCRT.FirstPass.S3i.QuenchedBounds
import MatedCRT.FirstPass.S3i.LensBEClosed
import MatedCRT.FirstPass.S3i.LensStep
import MatedCRT.FirstPass.S3i.ExitAlmostSure

/-!
# Plan Lemma 7 with the corrected exit input

`S3i/QuenchedBounds.lean` (commit 6b13afa) takes the finite-domain package `FP36LemmaOne` as a binder `L1`.
Its conjunct 1, `srwLaw m a {x | UsesEdges m a x ∧ vExitTime A x < ⊤} = 1`, is false as typed, so that theorem
is vacuous. This file restates Lemma 7 with `L1` replaced by the almost-sure exit statement alone:

* `hexit : ∀ {m} {A'}, FiniteExitData m A' → ∀ a ∈ A', srwLaw m a {x | vExitTime A' x < ⊤} = 1`
  (part (a): true as typed; `srwLaw_vExitTime_lt_top_fp36` of `S3i/ExitAlmostSure.lean`, supplies it).
* Lemma 6 is used in its closed form `lensProb_le_fp36_closed` (`S3i/LensBEClosed.lean`), which takes no exit input.
* The far-exit clause replaces the all-time event `UsesEdges` by the almost-sure step property
  `H2.ae_step_adjacent` (Lemma 2). Steps that stay put are allowed by that property and are harmless in the pathwise
  core (`farExit_pathwise_step_fp36`).

Terminology: quenched law `srwLaw` and exit time (Armstrong-Kuusi-Mourrat); same-walk coupling and the one-sided
boundary estimate (Gwynne-Miller-Sheffield, arXiv:1807.07511); Lawler-Limic for the strong Markov property; finite
exit sets and exit-hitting probabilities as in Armitage-Gardiner.
-/

namespace MatedCRT
namespace FirstPass36

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

/-! ## Clause 1: the walk is good a.s., with the direct application of the exit input -/

/-- **Plan Lemma 7, clause 1, with the almost-sure exit input `hexit`.** Almost surely the walk from the selected
start vertex is a same-walk good path. The exit input is applied directly (no projection from `UsesEdges`). -/
theorem quenchedStart_null_of_exit_fp36
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω}
    (hexit : ∀ {m : ℤ → ℤ → ℕ} {A' : Set ℤ}, FiniteExitData m A' →
      ∀ a ∈ A', srwLaw m a {x | vExitTime A' x < ⊤} = 1)
    (hε : 0 < ε) (hmpos : 0 < S.mε ε)
    (houter : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω) :
    srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y) {x | ¬ SameWalkGood S r z ε ω x} = 0 := by
  obtain ⟨hA, -, -, hfin, hvin, -⟩ := hgood
  have hη : Continuous (S.η ω) := hA.1
  set a := vertexOf ε (S.η ω) y with ha
  set V := cellVertices ε (S.η ω) (ball z (r + 4 * ε ^ b)) with hV
  have hδ : 0 ≤ ε ^ b := Real.rpow_nonneg hε.le b
  have hball : ball z r ⊆ ball z (r + 4 * ε ^ b) := ball_subset_ball (by linarith)
  have haV : a ∈ V := by
    obtain ⟨c, hc1, hc2⟩ := hvin.1
    exact ⟨c, hc1, hball hc2⟩
  have hfinV : FiniteExitData (S.mult ε ω) V := (hfin _ houter).1
  have hE' : srwLaw (S.mult ε ω) a {x | vExitTime V x < ⊤} = 1 := hexit hfinV a haV
  have hnull2 : srwLaw (S.mult ε ω) a {x | vExitTime V x < ⊤}ᶜ = 0 :=
    (prob_compl_eq_zero_iff (measurableSet_vExitTime_lt_top_fp36 V)).2 hE'
  have hnull1 : srwLaw (S.mult ε ω) a {x | x 0 ≠ a} = 0 := by
    have h := ae_iff.1 (srwLaw_ae_start (S.mult ε ω) a)
    simpa [ne_eq] using h
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hnull1 hnull2)
  by_contra hxn
  simp only [mem_union, Set.mem_ofPred_eq, mem_compl_iff, not_or, not_not] at hxn hx
  obtain ⟨h0, hT⟩ := hxn
  apply hx
  unfold SameWalkGood
  refine ⟨?_, ?_⟩
  · rw [interpolatedWalk_zero_fp36, h0]
    exact vertexPoint_mem_ball_of_interior_fp36 hε.le hη hvin
  · exact pathExitTime_lt_top_of_vertex_not_mem_fp36 hmpos
      (fun h => vertexPoint_not_mem_of_not_mem_cellVertices_fp36 hε.le
        (vExitTime_toNat_not_mem_fp36 hT) (hball h))

/-! ## Clause 2, helper: the far-exit core under the almost-sure step property -/

/-- The pathwise far-exit core (`farExit_pathwise_fp36`) under the almost-sure step property
`x (n+1) = x n ∨ M (x n) (x (n+1)) ≠ 0` (Lemma 2, `H2.ae_step_adjacent`). A step that stays put is harmless: the
cell of a vertex meets itself. The core is applied to the multiplicity `j, k ↦ if j = k then 1 else M j k`,
which is nonzero along every step of `x`; the core uses its multiplicity only through `hedge` and `hadj`. -/
lemma farExit_pathwise_step_fp36 {ε mε δ s r : ℝ} {η : ℝ → ℂ} {M : ℤ → ℤ → ℕ} {x : ℕ → ℤ} {z P : ℂ} {N : ℕ}
    (hε : 0 < ε) (hη : Continuous η) (hm : 0 < mε) (hr : 0 < r) (hδ : 0 < δ)
    (hscale : 64 * δ ≤ s) (hN0 : 0 < N)
    (hN1 : ∀ k < N, x k ∈ interiorCellVertices ε η (ball z r))
    (hN2 : x N ∉ interiorCellVertices ε η (ball z r))
    (hedge : ∀ n, x (n + 1) = x n ∨ M (x n) (x (n + 1)) ≠ 0)
    (hadj : ∀ j k, M j k ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty)
    (hdiam : ∀ k, (cell ε η k ∩ ball z (r + 4 * δ)).Nonempty → diam (cell ε η k) ≤ δ)
    (hq : dist (vertexPoint ε η (x N)) P ≤ δ)
    (hent : dist (vertexPoint ε η (x (N - 1))) P ≤ 3 * δ)
    (hvU : x N ∈ interiorCellVertices ε η (fp36LensDomain z r δ P s))
    (hT : HarmonicBalls.pathExitTime (ball z r) (interpolatedWalk ε η mε x) < ⊤)
    (hfar : s / 2 < dist (pathExitPosition (ball z r) (interpolatedWalk ε η mε x)) P) :
    vExitTime (interiorCellVertices ε η (fp36LensDomain z r δ P s)) (shiftedPath N x) < ⊤ ∧
      vExitPosition (interiorCellVertices ε η (fp36LensDomain z r δ P s)) (shiftedPath N x) ∈
        fp36LensFarCells ε η P s := by
  have hadj' : ∀ j k, (if j = k then 1 else M j k) ≠ 0 → (cell ε η j ∩ cell ε η k).Nonempty := by
    intro j k hjk
    split_ifs at hjk with hjk'
    · subst hjk'
      exact ⟨vertexPoint ε η j, vertexPoint_mem_cell_fp36 hε.le η j, vertexPoint_mem_cell_fp36 hε.le η j⟩
    · exact hadj j k hjk
  have hedge' : ∀ n, (if x n = x (n + 1) then 1 else M (x n) (x (n + 1))) ≠ 0 := by
    intro n
    split_ifs with heq
    · exact one_ne_zero
    · rcases hedge n with h | h
      · exact absurd h.symm heq
      · exact h
  exact farExit_pathwise_fp36 (M := fun j k => if j = k then 1 else M j k) hε hη hm hr hδ hscale hN0 hN1 hN2
    hedge' hadj' hdiam hq hent hvU hT hfar

/-! ## Clause 2 and the theorem: Lemma 7 with the corrected exit input -/

/-- **Plan Lemma 7 (`quenchedBoundsOnGood_fp36`) with the corrected exit input.** On a good environment, clause 1: the
quenched law from the selected start vertex gives a.s. a same-walk good path; clause 2: the probability of the far-exit
event is at most `A 96^ν ε^{νb/2}`, uniformly over the boundary vertices of Lemma 2, by the closed lens estimate
`lensProb_le_fp36_closed`. The only exit input is `hexit` (almost-sure exit from a finite exit set). -/
theorem quenchedBoundsOnGood_fp36_of_exit
    {Ω : Type} [MeasurableSpace Ω] {S : MatedCRTEnv Ω}
    {ρ₀ ρ₁ b ν A r ε : ℝ} {z y : ℂ} {ω : Ω}
    (hexit : ∀ {m : ℤ → ℤ → ℕ} {A' : Set ℤ}, FiniteExitData m A' →
      ∀ a ∈ A', srwLaw m a {x | vExitTime A' x < ⊤} = 1)
    (hε : 0 < ε) (hb : 0 < b) (hν : 0 < ν)
    (hA : 0 < A) (hr : 0 < r) (hρ : ρ₀ < ρ₁)
    (hmpos : 0 < S.mε ε)
    (hscale : 64 * ε ^ b ≤ ε ^ (b / 2))
    (houter : closure (ball z (r + 4 * ε ^ b)) ⊆ ball 0 ρ₀)
    (hgood : FP36GoodEnv S ρ₀ ρ₁ b ν A r z y ε ω) :
    let μ := srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
    μ {x | ¬ SameWalkGood S r z ε ω x} = 0 ∧
    μ {x | SameWalkGood S r z ε ω x ∧
      ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
      ≤ ENNReal.ofReal (A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2)) := by
  refine ⟨quenchedStart_null_of_exit_fp36 hexit hε hmpos houter hgood, ?_⟩
  show srwLaw (S.mult ε ω) (vertexOf ε (S.η ω) y)
      {x | SameWalkGood S r z ε ω x ∧
        ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)}
      ≤ ENNReal.ofReal (A * (96 : ℝ) ^ ν * ε ^ (ν * b / 2))
  obtain ⟨hA', hadj, hdiam3, hfin, hvin, -⟩ := id hgood
  have hη : Continuous (S.η ω) := hA'.1
  have hδ : 0 < ε ^ b := Real.rpow_pos_of_pos hε b
  have hsub1 : ball z (r + 4 * ε ^ b) ⊆ ball 0 ρ₁ :=
    (subset_closure.trans houter).trans (ball_subset_ball hρ.le)
  have hball : ball z r ⊆ ball 0 ρ₁ := (ball_subset_ball (by linarith)).trans hsub1
  have hdiam : ∀ k : ℤ, (cell ε (S.η ω) k ∩ ball z (r + 4 * ε ^ b)).Nonempty →
      diam (cell ε (S.η ω) k) ≤ ε ^ b :=
    fun k ⟨c, hc1, hc2⟩ => hdiam3 k ⟨c, hc1, hsub1 hc2⟩
  have hfinI : FiniteExitData (S.mult ε ω) (interiorCellVertices ε (S.η ω) (ball z r)) :=
    (hfin (ball z r) ((closure_mono (ball_subset_ball (by linarith))).trans houter)).2
  set a := vertexOf ε (S.η ω) y with ha
  set I := interiorCellVertices ε (S.η ω) (ball z r) with hI
  -- almost surely: the walk starts at `a`, every step is trivial or an edge of positive multiplicity
  -- (`H2.ae_step_adjacent`), and the walk exits the finite set `I` in finite time (`hexit`)
  have hs0 : ∀ᵐ x ∂srwLaw (S.mult ε ω) a, x 0 = a := srwLaw_ae_start (S.mult ε ω) a
  have hsteps : ∀ᵐ x ∂srwLaw (S.mult ε ω) a,
      ∀ n : ℕ, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0 :=
    H2.ae_step_adjacent (S.mult ε ω) a
  have hfinE : ∀ᵐ x ∂srwLaw (S.mult ε ω) a, vExitTime I x < ⊤ :=
    ae_iff.2 ((prob_compl_eq_zero_iff (measurableSet_vExitTime_lt_top_fp36 I)).2 (hexit hfinI a hvin))
  have hAE := hs0.and (hsteps.and hfinE)
  have hnull : srwLaw (S.mult ε ω) a
      {x : ℕ → ℤ | ¬ (x 0 = a ∧ (∀ n : ℕ, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0) ∧
        vExitTime I x < ⊤)} = 0 :=
    ae_iff.1 hAE
  have hcontain : {x : ℕ → ℤ | SameWalkGood S r z ε ω x ∧
      ε ^ (b / 2) / 2 < dist (sameWalkExitPoint S r z ε ω x) (sameWalkProjected S r z ε ω x)} ⊆
      {x : ℕ → ℤ | vExitTime I x < ⊤ ∧
        (let n := (vExitTime I x).toNat
         let v := vExitPosition I x
         vExitTime (interiorCellVertices ε (S.η ω)
            (fp36LensDomain z r (ε ^ b) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2))))
           (shiftedPath n x) < ⊤ ∧
         vExitPosition (interiorCellVertices ε (S.η ω)
            (fp36LensDomain z r (ε ^ b) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2))))
           (shiftedPath n x) ∈ fp36LensFarCells ε (S.η ω) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2)))} ∪
      {x : ℕ → ℤ | ¬ (x 0 = a ∧ (∀ n : ℕ, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0) ∧
        vExitTime I x < ⊤)} := by
    intro x hx
    by_cases hxP : x 0 = a ∧ (∀ n : ℕ, x (n + 1) = x n ∨ S.mult ε ω (x n) (x (n + 1)) ≠ 0) ∧
        vExitTime I x < ⊤
    · left
      obtain ⟨hx0eq, hedgeAll, hfinx⟩ := hxP
      obtain ⟨hxG, hxfar⟩ := hx
      obtain ⟨-, hTfin⟩ := hxG
      have hNe : vExitTime I x = ((vExitTime I x).toNat : ℕ∞) :=
        (ENat.natCast_toNat hfinx.ne).symm
      have hN1 : ∀ k < (vExitTime I x).toNat, x k ∈ I :=
        fun k hk => mem_of_lt_vExitTime_fp36 hNe hk
      have hN2 : x (vExitTime I x).toNat ∉ I :=
        vExitTime_toNat_not_mem_fp36 hfinx
      have hN0 : 0 < (vExitTime I x).toNat :=
        Nat.pos_of_ne_zero (fun h0 => hN2 (by rw [h0, hx0eq]; exact hvin))
      -- the exit step is an edge: a trivial step would keep the walk inside `I`
      have hedgeN : S.mult ε ω (x ((vExitTime I x).toNat - 1)) (x (vExitTime I x).toNat) ≠ 0 := by
        have h := hedgeAll ((vExitTime I x).toNat - 1)
        rw [Nat.sub_add_cancel hN0] at h
        rcases h with h | h
        · exfalso
          apply hN2
          rw [h]
          exact hN1 _ (by omega)
        · exact h
      have hvb : x (vExitTime I x).toNat ∈ vBoundary (S.mult ε ω) I :=
        ⟨hN2, _, hN1 _ (by omega), hedgeN⟩
      obtain ⟨-, -, hq, hent4⟩ := H4.boundaryVertexGeometry_fp36_of_ball hε hr hball hgood hvb
      have hent := hent4 _ (hN1 _ (by omega)) hedgeN
      have hvU := (H5.lensGeometry_fp36 hε hb hr hρ hscale houter hgood hvb).1
      refine ⟨hfinx, ?_⟩
      exact farExit_pathwise_step_fp36 (M := S.mult ε ω) (N := (vExitTime I x).toNat)
        hε hη hmpos hr hδ hscale hN0 hN1 hN2
        hedgeAll hadj hdiam hq hent hvU hTfin hxfar
    · right
      exact hxP
  refine (measure_mono hcontain).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, add_zero]
  refine (H2.srwLaw_strongMarkov_vExitTime hfinI hvin
    (fun v => interiorCellVertices ε (S.η ω)
      (fp36LensDomain z r (ε ^ b) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2))))
    (fun v => fp36LensFarCells ε (S.η ω) (ballRetraction z r (vertexPoint ε (S.η ω) v)) (ε ^ (b / 2)))).trans ?_
  exact iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal
    (lensProb_le_fp36_closed hε hb hν hA hr hρ hscale houter hgood hv)

/-! ## The consumer `QuenchedBoundsOnGoodStmt` (`S3i/LensStep.lean`) from the exit input -/

/-- `QuenchedBoundsOnGoodStmt` (the input `hQB` of `firstPass_3_6_annealed_closed`), proved from the almost-sure
exit input `hexit` alone. -/
theorem quenchedBoundsOnGoodStmt_of_exit
    (hexit : ∀ {m : ℤ → ℤ → ℕ} {A' : Set ℤ}, FiniteExitData m A' →
      ∀ a ∈ A', srwLaw m a {x | vExitTime A' x < ⊤} = 1) :
    QuenchedBoundsOnGoodStmt := by
  intro Ω _ S ρ₀ ρ₁ b ν A r ε z y ω hε hb hν hA hr hρ hmpos hscale houter hgood
  exact quenchedBoundsOnGood_fp36_of_exit hexit hε hb hν hA hr hρ hmpos hscale houter hgood

/-! ## The unconditional consumer: the exit input is the theorem `srwLaw_vExitTime_lt_top_fp36` -/

/-- **`QuenchedBoundsOnGoodStmt` with no binder.** The almost-sure exit input is `srwLaw_vExitTime_lt_top_fp36`
(`S3i/ExitAlmostSure.lean`, almost-sure exit from a finite exit set, Lemma 1 conjunct 1 as corrected). -/
theorem quenchedBoundsOnGoodStmt_closed : QuenchedBoundsOnGoodStmt :=
  quenchedBoundsOnGoodStmt_of_exit srwLaw_vExitTime_lt_top_fp36

#print axioms MatedCRT.FirstPass36.quenchedStart_null_of_exit_fp36
#print axioms MatedCRT.FirstPass36.farExit_pathwise_step_fp36
#print axioms MatedCRT.FirstPass36.quenchedBoundsOnGood_fp36_of_exit
#print axioms MatedCRT.FirstPass36.quenchedBoundsOnGoodStmt_of_exit
#print axioms MatedCRT.FirstPass36.quenchedBoundsOnGoodStmt_closed

end FirstPass36
end MatedCRT
