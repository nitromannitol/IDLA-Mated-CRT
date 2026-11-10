import MatedCRT.FirstPass.S5c.FixedIndexGap

/-!
# FIRST PASS, Lemma 5.3 (three-inputs (b), pathwise core): a countable-infimum margin

Deterministic, for one outcome. Let `Λ` be a cluster `Λ_t` (a harmonic ball of mass `t` at `0`), `A x = w_t x - 2 w_{t/2} x`
the margin, `δ > 0`, and `K_δ = B̄_ρ ∩ {x | δ/2 ≤ d(x, Λᶜ)}`. Let `D` be a dense set of `ℂ` (countable in the use).
Put

* `marginIndex Λ ρ δ` (`I`): the points `q` with `|q| < ρ` such that a closed ball `B̄(q, r)` of rational radius `r > δ/4`
  lies in `Λ`; then `d(q, Λᶜ) ≥ r > δ/4`, so `I ⊆ marginCore Λ ρ δ = B̄_ρ ∩ {x | δ/4 ≤ d(x, Λᶜ)}`, a compact subset of `Λ`;
* `marginInf D I A = ⨅ q ∈ D, (if q ∈ I then A q else 1)`, a countable infimum.

Then `min 1 β ≤ marginInf D I A` when `A ≥ β` on the compact core (the uniform positive margin of the fixed-index gap), and
`marginInf D I A ≤ A x` for every `x ∈ K_δ` (approximate `x` by points of `D ∩ I`, continuity of `A` on `B̄_ρ`).
This is the pathwise inequality (4.1) of the three-inputs note, with the dyadic selection B2 replaced by the countable
infimum; the measurability of `marginInf` is a separate step (see the notes).

Terminology: Duplantier-Sheffield and Berestycki-Powell (the cluster `Λ_t` as a harmonic ball), Armitage-Gardiner (majorant).
-/

namespace MatedCRT.S5c

open MeasureTheory Filter Topology Set Metric Laplacian
open Classical

/-- The index set `I` of the margin: points `q` with `|q| < ρ` such that a closed ball `B̄(q, r)` of rational
radius `r > δ/4` lies in `Λ`. -/
def marginIndex (Λ : Set ℂ) (ρ δ : ℝ) : Set ℂ :=
  {q | ‖q‖ < ρ ∧ ∃ r : ℚ, δ / 4 < (r : ℝ) ∧ closedBall q (r : ℝ) ⊆ Λ}

/-- The compact core `B̄_ρ ∩ {x | δ/4 ≤ d(x, Λᶜ)}` of the margin. -/
def marginCore (Λ : Set ℂ) (ρ δ : ℝ) : Set ℂ :=
  closedBall (0 : ℂ) ρ ∩ {x | δ / 4 ≤ infDist x Λᶜ}

/-- The countable infimum of the margin over `D`, with value `1` off the index set `I`. -/
noncomputable def marginInf (D I : Set ℂ) (A : ℂ → ℝ) : ℝ :=
  ⨅ q : D, if (q : ℂ) ∈ I then A q else 1

theorem marginIndex_subset_closedBall {Λ : Set ℂ} {ρ δ : ℝ} :
    marginIndex Λ ρ δ ⊆ closedBall (0 : ℂ) ρ := fun q hq => by
  rw [mem_closedBall_zero_iff]
  exact hq.1.le

theorem isCompact_marginCore (Λ : Set ℂ) (ρ δ : ℝ) : IsCompact (marginCore Λ ρ δ) :=
  (isCompact_closedBall (0 : ℂ) ρ).inter_right
    (isClosed_le continuous_const (Metric.continuous_infDist_pt (s := Λᶜ)))

theorem marginCore_subset {Λ : Set ℂ} {ρ δ : ℝ} (hδ : 0 < δ) : marginCore Λ ρ δ ⊆ Λ := by
  rintro x ⟨-, hx⟩
  by_contra hxΛ
  have h0 : infDist x Λᶜ = 0 := infDist_zero_of_mem (mem_compl hxΛ)
  have hx' : δ / 4 ≤ infDist x Λᶜ := hx
  linarith

theorem marginIndex_subset_core {Λ : Set ℂ} {ρ δ : ℝ} (hΛne : Λᶜ.Nonempty) :
    marginIndex Λ ρ δ ⊆ marginCore Λ ρ δ := by
  rintro q ⟨hqρ, r, hr, hball⟩
  refine ⟨mem_closedBall_zero_iff.2 hqρ.le, ?_⟩
  show δ / 4 ≤ infDist q Λᶜ
  refine le_trans hr.le ?_
  rw [le_infDist hΛne]
  intro y hy
  by_contra hlt
  rw [not_le] at hlt
  exact hy (hball (mem_closedBall.2 (by rw [dist_comm]; exact hlt.le)))

theorem ball_subset_of_infDist {Λ : Set ℂ} {x : ℂ} {δ : ℝ} (hx : δ / 2 ≤ infDist x Λᶜ) :
    ball x (δ / 2) ⊆ Λ := by
  intro y hy
  by_contra hyΛ
  have h1 : infDist x Λᶜ ≤ dist x y := infDist_le_dist_of_mem (mem_compl hyΛ)
  have h2 : dist x y < δ / 2 := by
    rw [dist_comm]
    exact mem_ball.1 hy
  linarith

/-- Approximation: a point `x ∈ B̄_ρ` with `B(x, δ/2) ⊆ Λ` is the limit of points of `D ∩ I`. -/
theorem exists_marginIndex_near {D : Set ℂ} (hD : Dense D) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    {Λ : Set ℂ} {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) ρ) (hΛ : ball x (δ / 2) ⊆ Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ D, q ∈ marginIndex Λ ρ δ ∧ dist q x < ε := by
  have hxcl : x ∈ closure (ball (0 : ℂ) ρ) := by
    rw [closure_ball (0 : ℂ) hρ.ne']
    exact hx
  have hη : 0 < min ε (δ / 8) := lt_min hε (by linarith)
  obtain ⟨y, hyρ, hyx⟩ := Metric.mem_closure_iff.1 hxcl (min ε (δ / 8)) hη
  obtain ⟨q, hqD, hqU⟩ := hD.exists_mem_open (isOpen_ball.inter isOpen_ball)
    ⟨y, mem_ball.2 (by rw [dist_comm]; exact hyx), hyρ⟩
  obtain ⟨hqx, hq0⟩ := hqU
  have hqx' : dist q x < min ε (δ / 8) := mem_ball.1 hqx
  have hqε : dist q x < ε := lt_of_lt_of_le hqx' (min_le_left _ _)
  have hqδ : dist q x < δ / 8 := lt_of_lt_of_le hqx' (min_le_right _ _)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show δ / 4 < δ / 2 - dist q x by linarith)
  refine ⟨q, hqD, ⟨mem_ball_zero_iff.1 hq0, r, hr1, ?_⟩, hqε⟩
  intro z hz
  apply hΛ
  rw [mem_closedBall] at hz
  rw [mem_ball]
  have := dist_triangle z q x
  linarith

/-- The term of the infimum is at least `min 1 β` when `A ≥ β` on the index set. -/
theorem term_ge_min {D I : Set ℂ} {A : ℂ → ℝ} {β : ℝ} (hβ : ∀ q ∈ D, q ∈ I → β ≤ A q) (q : D) :
    min 1 β ≤ if (q : ℂ) ∈ I then A q else 1 := by
  split_ifs with hq
  · exact (min_le_right _ _).trans (hβ q q.2 hq)
  · exact min_le_left _ _

theorem le_marginInf {D I : Set ℂ} {A : ℂ → ℝ} {β : ℝ} (hDne : D.Nonempty)
    (hβ : ∀ q ∈ D, q ∈ I → β ≤ A q) : min 1 β ≤ marginInf D I A := by
  have : Nonempty D := hDne.to_subtype
  exact le_ciInf (term_ge_min hβ)

/-- Upper bound: `marginInf ≤ A x` when `A` is continuous within `S ⊇ I` at `x` and `x` is a limit of points of `D ∩ I`. -/
theorem marginInf_le_of_approx {D I S : Set ℂ} {A : ℂ → ℝ} {m : ℝ}
    (hlow : ∀ q : D, m ≤ if (q : ℂ) ∈ I then A q else 1) (hIS : I ⊆ S) {x : ℂ}
    (hA : ContinuousWithinAt A S x) (happ : ∀ ε : ℝ, 0 < ε → ∃ q ∈ D, q ∈ I ∧ dist q x < ε) :
    marginInf D I A ≤ A x := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.continuousWithinAt_iff.1 hA η hη
  obtain ⟨q, hqD, hqI, hqd⟩ := happ ε hε
  have hqS : q ∈ S := hIS hqI
  have h1 : marginInf D I A ≤ if (q : ℂ) ∈ I then A q else 1 := by
    unfold marginInf
    exact ciInf_le ⟨m, by rintro _ ⟨p, rfl⟩; exact hlow p⟩ (⟨q, hqD⟩ : D)
  simp only [hqI, ↓reduceIte] at h1
  have h2 := hball hqS hqd
  rw [Real.dist_eq] at h2
  have h3 := (abs_lt.1 h2).2
  linarith

/-- **Pathwise margin** (three-inputs (4.1), countable-infimum form). If `A` is continuous on `B̄_ρ` and `A ≥ β` on the
compact core `marginCore Λ ρ δ`, then the countable infimum is at least `min 1 β` and at most `A x` for every
`x ∈ B̄_ρ` with `d(x, Λᶜ) ≥ δ/2`. -/
theorem marginInf_pathwise {D : Set ℂ} (hD : Dense D) (hDne : D.Nonempty)
    {Λ : Set ℂ} {A : ℂ → ℝ} {ρ δ β : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hΛne : Λᶜ.Nonempty)
    (hA : ContinuousOn A (closedBall (0 : ℂ) ρ)) (hβ : ∀ x ∈ marginCore Λ ρ δ, β ≤ A x) :
    min 1 β ≤ marginInf D (marginIndex Λ ρ δ) A ∧
      ∀ x ∈ closedBall (0 : ℂ) ρ, δ / 2 ≤ infDist x Λᶜ →
        marginInf D (marginIndex Λ ρ δ) A ≤ A x := by
  have hβI : ∀ q ∈ D, q ∈ marginIndex Λ ρ δ → β ≤ A q := fun q _ hq =>
    hβ q (marginIndex_subset_core hΛne hq)
  refine ⟨le_marginInf hDne hβI, fun x hx hxd => ?_⟩
  exact marginInf_le_of_approx (term_ge_min hβI) marginIndex_subset_closedBall
    (hA.continuousWithinAt hx)
    (fun ε hε => exists_marginIndex_near hD hρ hδ hx (ball_subset_of_infDist hxd) hε)

end MatedCRT.S5c
