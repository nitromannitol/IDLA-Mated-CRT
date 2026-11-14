import MatedCRT.FirstPass.Derived.SrwStageDecay
import MatedCRT.FirstPass.Derived.SrwWalkLawBridge
import MatedCRT.FirstPass.Derived.SrwGraphAdjBridge
import MatedCRT.FirstPass.Derived.SrwHitLawSeparation
import MatedCRT.Defs.Setting
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.EpsBMain

/-!
# The stage events of (3.35) for the quenched walk (Berestycki–Gwynne (2020), proof of Lemma 6.13)

On the good event of Lemma 3.11 (`Lemma311GoodReal`), from every vertex whose cell meets `B_r(z)` the walk
disconnects `V(∂B_{r/2}(z))` from `V(∂B_{2r}(z))` before hitting `V(∂B_{2r}(z))` with quenched probability `≥ p`.
Here this is read for `srwLaw` of the edge multiplicity `S.mult ε ω`: the event is `stageEvent` of the outer vertex set
with success sets "the vertices visited so far graph-separate the inner set from the outer set"
(`disconnectSets`).  At the radii `R_i = 4^i R₀` the outer set of stage `i` is the inner set of stage `i + 1`
(`R_{i+1}/2 = 2 R_i`), so the stage decay `srwLaw_stageFail_le` applies: the walk fails at `k` consecutive stages
with probability at most `(1 - p)^k`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRT.FirstPass.Derived

open MatedCRTHarmonic

/-- The vertices visited strictly before time `k` by a history `f`. -/
def histVisited {k : ℕ} (f : Fin (k + 1) → ℤ) : Set ℤ := {y | ∃ i : Fin (k + 1), i.val < k ∧ f i = y}

/-- The success sets of the disconnection stage: the vertices visited before time `k` graph-separate `A` from `B`
in the simple graph of the edge multiplicity `m`. -/
def disconnectSets (m : ℤ → ℤ → ℕ) (A B : Set ℤ) (k : ℕ) : Set (Fin (k + 1) → ℤ) :=
  {f | HarmonicInfinity.GraphSeparates (srwGraph m) (histVisited f) A B}

theorem histVisited_pathHist (k : ℕ) (ξ : ℕ → ℤ) :
    histVisited (pathHist k ξ) = {y | ∃ i < k, ξ i = y} := by
  ext y
  simp only [histVisited, pathHist, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, Nat.lt_succ_of_lt hi⟩, hi, rfl⟩

/-- "The walk disconnects `A` from `B` before hitting `B`" (T15A) is membership in the stage event of `B` with the
disconnection success sets. -/
theorem disconnectsBeforeHit_iff_mem_stageEvent {ε : ℝ} {ω : MatedCRTHarmonic.MatedCRT.Path2}
    (h : MatedCRTHarmonic.MatedCRT.IsLocallyFinite ε ω) (hε : 0 ≤ ε) (A B : Set ℤ) (X : ℕ → ℤ) :
    GMSMain.T15A.DisconnectsBeforeHit (MatedCRTHarmonic.MatedCRT.graph ε ω h) A B X ↔
      X ∈ stageEvent B
        (disconnectSets (bmEdgeCount ε (fun t => (ω t).1) (fun t => (ω t).2)) A B) := by
  constructor
  · rintro ⟨n, hn, hd⟩
    refine ⟨n, by rw [← hitTime_eq_vHitTime]; exact hn, ?_⟩
    show HarmonicInfinity.GraphSeparates _ (histVisited (pathHist n X)) A B
    rw [histVisited_pathHist]
    exact (disconnects_graph_iff_graphSeparates h hε _ A B).1 hd
  · rintro ⟨n, hn, hd⟩
    refine ⟨n, by rw [hitTime_eq_vHitTime]; exact hn, ?_⟩
    have hd' : HarmonicInfinity.GraphSeparates _ (histVisited (pathHist n X)) A B := hd
    rw [histVisited_pathHist] at hd'
    exact (disconnects_graph_iff_graphSeparates h hε _ A B).2 hd'

/-- **One stage on the good event of (3.35).**  On `Lemma311GoodReal`, for `ε^β ≤ r ≤ ρ` and `B_{2r}(z) ⊆ B_ρ(0)`,
from every vertex whose cell meets `B_r(z)` the walk succeeds at the stage `V(∂B_{r/2}(z)) → V(∂B_{2r}(z))` with
`srwLaw` probability at least `p`. -/
theorem srwLaw_stageEvent_ge_of_lemma311GoodReal {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {η' : Ω → C(ℝ, ℂ)} {ω : Ω} {ε ρ β p : ℝ} (hε : 0 ≤ ε)
    (hgood : ω ∈ GMSMain.EpsB.Lemma311GoodReal S.bm η' ε ρ β p)
    (hcellEq : ∀ x : ℤ, cell ε (S.η ω) x = η' ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (z : ℂ) (r : ℝ) (hr1 : ε ^ β ≤ r) (hr2 : r ≤ ρ) (hball : ball z (2 * r) ⊆ ball (0 : ℂ) ρ) :
    ∀ x ∈ cellVertices ε (S.η ω) (ball z r),
      ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) x
        (stageEvent (cellVertices ε (S.η ω) (sphere z (2 * r)))
          (disconnectSets (S.mult ε ω) (cellVertices ε (S.η ω) (sphere z (r / 2)))
            (cellVertices ε (S.η ω) (sphere z (2 * r))))) := by
  obtain ⟨h, H, hcell, h311⟩ := hgood
  have hHc : H.cell = cell ε (S.η ω) := funext fun x => (hcell x).trans (hcellEq x).symm
  have hVM : ∀ E : Set ℂ, verticesMeeting H.cell E = cellVertices ε (S.η ω) E := by
    intro E
    rw [hHc]
    rfl
  intro x hx
  have hx' : x ∈ verticesMeeting H.cell (ball z r) := by rw [hVM]; exact hx
  have h1 := h311 z r hr1 hr2 hball x hx'
  refine h1.trans ?_
  have h2 := walkLaw_vertexPath_preimage_le_srwLaw h hε x
    {X : ℕ → ℤ | GMSMain.T15A.Lemma311Event (MatedCRTHarmonic.MatedCRT.graph ε (S.bm ω) h) H.cell z r X}
  refine h2.trans (le_of_eq ?_)
  congr 1
  ext X
  show GMSMain.T15A.Lemma311Event _ H.cell z r X ↔ _
  unfold GMSMain.T15A.Lemma311Event
  rw [hVM, hVM]
  exact disconnectsBeforeHit_iff_mem_stageEvent h hε _ _ X

/-- A stage event of probability at least `p` fails with probability at most `1 - p`. -/
theorem srwLaw_compl_stageEvent_le {m : ℤ → ℤ → ℕ} {y : ℤ} {B : Set ℤ}
    {F : ∀ k : ℕ, Set (Fin (k + 1) → ℤ)} {p : ℝ} (hp0 : 0 ≤ p)
    (h : ENNReal.ofReal p ≤ srwLaw m y (stageEvent B F)) :
    srwLaw m y (stageEvent B F)ᶜ ≤ ENNReal.ofReal (1 - p) := by
  rw [prob_compl_eq_one_sub (measurableSet_stageEvent B F)]
  calc 1 - srwLaw m y (stageEvent B F) ≤ 1 - ENNReal.ofReal p := tsub_le_tsub_left h 1
    _ = ENNReal.ofReal (1 - p) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp0]

/-- The vertex set of stage `i`: `V(∂B_{R_i/2}(c))` with `R_i = 4^i R₀`. -/
def stageSet (ε : ℝ) (η : ℝ → ℂ) (c : ℂ) (R₀ : ℝ) (i : ℕ) : Set ℤ :=
  cellVertices ε η (sphere c (4 ^ i * R₀ / 2))

/-- The success sets of stage `i`: the visited vertices separate `stageSet i` from `stageSet (i + 1)`. -/
def stageFamily (m : ℤ → ℤ → ℕ) (ε : ℝ) (η : ℝ → ℂ) (c : ℂ) (R₀ : ℝ) :
    ℕ → ℤ → ∀ k : ℕ, Set (Fin (k + 1) → ℤ) :=
  fun i _ k => disconnectSets m (stageSet ε η c R₀ i) (stageSet ε η c R₀ (i + 1)) k

theorem stageSet_succ (ε : ℝ) (η : ℝ → ℂ) (c : ℂ) (R₀ : ℝ) (i : ℕ) :
    stageSet ε η c R₀ (i + 1) = cellVertices ε η (sphere c (2 * (4 ^ i * R₀))) := by
  unfold stageSet
  have : (4 : ℝ) ^ (i + 1) * R₀ / 2 = 2 * (4 ^ i * R₀) := by rw [pow_succ]; ring
  rw [this]

/-- **Per-stage failure bound at the radii `R_i = 4^i R₀`.** -/
theorem stage_failure_le_of_lemma311GoodReal {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {η' : Ω → C(ℝ, ℂ)} {ω : Ω} {ε ρ β p : ℝ} (hε : 0 ≤ ε) (hp0 : 0 ≤ p)
    (hgood : ω ∈ GMSMain.EpsB.Lemma311GoodReal S.bm η' ε ρ β p)
    (hcellEq : ∀ x : ℤ, cell ε (S.η ω) x = η' ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (c : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀) (N : ℕ) (hfloor : ε ^ β ≤ R₀)
    (hρ : ∀ i < N, 4 ^ i * R₀ ≤ ρ) (hball : ∀ i < N, ball c (2 * (4 ^ i * R₀)) ⊆ ball (0 : ℂ) ρ) :
    ∀ i < N, ∀ y ∈ stageSet ε (S.η ω) c R₀ i,
      srwLaw (S.mult ε ω) y
        (stageEvent (stageSet ε (S.η ω) c R₀ (i + 1))
          (stageFamily (S.mult ε ω) ε (S.η ω) c R₀ i y))ᶜ ≤ ENNReal.ofReal (1 - p) := by
  intro i hi y hy
  have hr0 : 0 < 4 ^ i * R₀ := by positivity
  have hyb : y ∈ cellVertices ε (S.η ω) (ball c (4 ^ i * R₀)) := by
    obtain ⟨w, hw1, hw2⟩ := hy
    refine ⟨w, hw1, ?_⟩
    rw [mem_ball]
    have := mem_sphere.1 hw2
    linarith
  have hge : R₀ ≤ 4 ^ i * R₀ := le_mul_of_one_le_left hR₀.le (one_le_pow₀ (by norm_num))
  have key := srwLaw_stageEvent_ge_of_lemma311GoodReal S hε hgood hcellEq c (4 ^ i * R₀)
    (hfloor.trans hge) (hρ i hi) (hball i hi) y hyb
  have key' : ENNReal.ofReal p ≤ srwLaw (S.mult ε ω) y
      (stageEvent (stageSet ε (S.η ω) c R₀ (i + 1))
        (stageFamily (S.mult ε ω) ε (S.η ω) c R₀ i y)) := by
    rw [← stageSet_succ] at key
    exact key
  exact srwLaw_compl_stageEvent_le hp0 key'

/-- **Decay over `k` consecutive stages on the good event of (3.35).**  For `k ≤ N`, from every vertex of the first
stage set the walk fails at `k` consecutive stages with `srwLaw` probability at most `(1 - p)^k`. -/
theorem srwLaw_stageFail_le_of_lemma311GoodReal {Ω : Type} [MeasurableSpace Ω] (S : MatedCRTEnv Ω)
    {η' : Ω → C(ℝ, ℂ)} {ω : Ω} {ε ρ β p : ℝ} (hε : 0 ≤ ε) (hp0 : 0 ≤ p)
    (hgood : ω ∈ GMSMain.EpsB.Lemma311GoodReal S.bm η' ε ρ β p)
    (hcellEq : ∀ x : ℤ, cell ε (S.η ω) x = η' ω '' Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (c : ℂ) (R₀ : ℝ) (hR₀ : 0 < R₀) (N : ℕ) (hfloor : ε ^ β ≤ R₀)
    (hρ : ∀ i < N, 4 ^ i * R₀ ≤ ρ) (hball : ∀ i < N, ball c (2 * (4 ^ i * R₀)) ⊆ ball (0 : ℂ) ρ)
    (k : ℕ) (hk : k ≤ N) (y : ℤ) (hy : y ∈ stageSet ε (S.η ω) c R₀ 0) :
    srwLaw (S.mult ε ω) y
        (stageFail (stageSet ε (S.η ω) c R₀) (stageFamily (S.mult ε ω) ε (S.η ω) c R₀) k 0 y) ≤
      ENNReal.ofReal (1 - p) ^ k :=
  srwLaw_stageFail_le (S.mult ε ω) (stageSet ε (S.η ω) c R₀)
    (stageFamily (S.mult ε ω) ε (S.η ω) c R₀) (ENNReal.ofReal (1 - p)) N
    (stage_failure_le_of_lemma311GoodReal S hε hp0 hgood hcellEq c R₀ hR₀ N hfloor hρ hball) k 0
    (by omega) y hy

end MatedCRT.FirstPass.Derived
