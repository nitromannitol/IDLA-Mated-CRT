import MatedCRT.FirstPass.Derived.GreenCrudePolyHighProb

/-!
# Selection of the segment paths

In the proof of BG20 Lemma 5.6 the segment from a point `u` in a uniformly random direction `θ`
meets a set of cells, and a path of the mated-CRT map from the vertex `x` through these cells to
the boundary of `V^ε(B_ρ)` is "chosen in some measurable manner". The flow bounds of the method of
random segment paths need, for each direction, a path that is a nodup chain of the graph, starts
at `x`, stays in `V^ε(B_ρ)` and ends outside `V^ε(B_ρ) \ V^ε(∂B_ρ)`; the path depends on the
direction only through the finite set of cells met by the segment (`LatticeProb.segmentPath`),
so no measurability is needed beyond that of the hit set.

This file supplies the selection rule. A nodup chain is extracted from any chain by cutting out
loops (`MatedCRT.exists_nodup_isChain_of_reflTransGen`), and the rule `MatedCRT.chainSelect`
chooses one whenever one exists. Hence the segment-path event reduces to the reachability, inside
the cells met by the segment, of a vertex outside `V^ε(B_ρ) \ V^ε(∂B_ρ)` from `x`
(`MatedCRT.MatedCRTEnv.mem_segmentPathEvent_of_reachable`).

## Main statements

* `MatedCRT.exists_nodup_isChain_of_reflTransGen`
* `MatedCRT.chainSelect`, `MatedCRT.exists_chainSelect_eq_cons_of_reflTransGen`
* `MatedCRT.MatedCRTEnv.mem_segmentPathEvent_of_reachable`
-/

open Set Metric LatticeProb

namespace MatedCRT

variable {ι : Type*}

/-- **Loop erasure.** If `b` is reachable from `x` by steps of `r` whose targets lie in `s`, and
`x ∈ s`, then there is a nodup `r`-chain in `s` from `x` to `b`. -/
theorem exists_nodup_isChain_of_reflTransGen {r : ι → ι → Prop} {s : Set ι} {x b : ι}
    (h : Relation.ReflTransGen (fun a c => c ∈ s ∧ r a c) x b) (hx : x ∈ s) :
    ∃ l : List ι, (x :: l).Nodup ∧ (x :: l).IsChain r ∧ (∀ v ∈ x :: l, v ∈ s) ∧
      (x :: l).getLast (List.cons_ne_nil x l) = b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], List.nodup_singleton _, List.isChain_singleton _, by simpa using hx, rfl⟩
  | @head a c hac _ ih =>
    obtain ⟨l, hnd, hch, hs, hl⟩ := ih hac.1
    by_cases ha : a ∈ c :: l
    · obtain ⟨p, q, hpq⟩ := List.append_of_mem ha
      refine ⟨q, ?_, ?_, ?_, ?_⟩
      · rw [hpq] at hnd
        exact hnd.sublist (List.sublist_append_right p (a :: q))
      · rw [hpq] at hch
        exact hch.suffix (List.suffix_append p (a :: q))
      · intro v hv
        exact hs v (hpq ▸ List.mem_append_right p hv)
      · have h1 : (c :: l).getLast? = some b := by
          rw [List.getLast?_eq_some_getLast (List.cons_ne_nil c l), hl]
        rw [hpq, List.getLast?_append] at h1
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a q)] at h1
        simpa using h1
    · refine ⟨c :: l, List.nodup_cons.2 ⟨ha, hnd⟩, List.IsChain.cons_cons hac.2 hch, ?_, ?_⟩
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hx
        · exact hs v hv
      · rw [List.getLast_cons (List.cons_ne_nil c l)]
        exact hl

/-- **The selection rule.** Through the finite set `T`, a nodup `r`-chain from `x` whose vertices
lie in `T` and satisfy `Q` and whose last vertex does not satisfy `P`, if one exists; otherwise
the empty path. -/
noncomputable def chainSelect (r : ι → ι → Prop) (Q P : ι → Prop) (x : ι) (T : Finset ι) :
    List ι := by
  classical
  exact if h : ∃ l : List ι, (x :: l).Nodup ∧ (x :: l).IsChain r ∧ (∀ v ∈ x :: l, v ∈ T ∧ Q v) ∧
      ¬ P ((x :: l).getLast (List.cons_ne_nil x l)) then x :: h.choose else []

variable {r : ι → ι → Prop} {Q P : ι → Prop} {x : ι}

theorem chainSelect_spec (T : Finset ι) :
    (chainSelect r Q P x T).Nodup ∧ (chainSelect r Q P x T).IsChain r ∧
      ∀ v ∈ chainSelect r Q P x T, v ∈ T ∧ Q v := by
  classical
  unfold chainSelect
  split_ifs with h
  · obtain ⟨hnd, hch, hs, -⟩ := h.choose_spec
    exact ⟨hnd, hch, hs⟩
  · exact ⟨List.nodup_nil, List.isChain_nil, fun v hv => absurd hv List.not_mem_nil⟩

theorem mem_of_mem_chainSelect {T : Finset ι} {v : ι} (hv : v ∈ chainSelect r Q P x T) :
    v ∈ T :=
  ((chainSelect_spec T).2.2 v hv).1

theorem nodup_chainSelect (T : Finset ι) : (chainSelect r Q P x T).Nodup :=
  (chainSelect_spec T).1

theorem isChain_chainSelect (T : Finset ι) : (chainSelect r Q P x T).IsChain r :=
  (chainSelect_spec T).2.1

/-- If some vertex outside `P` is reachable from `x ∈ T` by steps of `r` inside `T ∩ Q`, the
selected path starts at `x`, stays in `Q` and ends outside `P`. -/
theorem exists_chainSelect_eq_cons_of_reflTransGen {T : Finset ι} (hxT : x ∈ T) (hxQ : Q x)
    {b : ι} (hb : ¬ P b)
    (hreach : Relation.ReflTransGen (fun a c => (c ∈ T ∧ Q c) ∧ r a c) x b) :
    ∃ l, chainSelect r Q P x T = x :: l ∧ (∀ v ∈ x :: l, Q v) ∧
      ¬ P ((x :: l).getLast (List.cons_ne_nil x l)) := by
  classical
  have hex : ∃ l : List ι, (x :: l).Nodup ∧ (x :: l).IsChain r ∧ (∀ v ∈ x :: l, v ∈ T ∧ Q v) ∧
      ¬ P ((x :: l).getLast (List.cons_ne_nil x l)) := by
    obtain ⟨l, hnd, hch, hs, hl⟩ :=
      exists_nodup_isChain_of_reflTransGen (s := {c | c ∈ T ∧ Q c}) hreach ⟨hxT, hxQ⟩
    exact ⟨l, hnd, hch, hs, hl ▸ hb⟩
  refine ⟨hex.choose, ?_, fun v hv => (hex.choose_spec.2.2.1 v hv).2, hex.choose_spec.2.2.2⟩
  unfold chainSelect
  split_ifs
  rfl

/-- The segment from `u` meets the cell containing `u` in every direction. -/
theorem mem_hitFinset_segmentDirections_of_mem {H : ι → Set ℂ} {Y : Finset ι} {u : ℂ} {ℓ : ℝ}
    (hxY : x ∈ Y) (hu : u ∈ H x) (hℓ : 0 ≤ ℓ) (θ : ℝ) :
    x ∈ hitFinset Y (fun y => segmentDirections u ℓ (H y)) θ :=
  mem_hitFinset.2 ⟨hxY, 0, ⟨le_rfl, hℓ⟩, by simpa using hu⟩

/-- **The segment-path event from reachability.** If for every vertex `x` of
`V^ε(B_ρ) \ V^ε(∂B_ρ)` there are a point `u` with `‖u‖ ≤ U`, a length `ℓ` and a finite set `Y`
of cells such that, in every direction `θ`, the cell of `x` is met by the segment and some vertex
outside `V^ε(B_ρ) \ V^ε(∂B_ρ)` is reachable from `x` in the graph `𝒢^ε` through cells of
`V^ε(B_ρ)` met by the segment, then the segment-path event holds. -/
theorem MatedCRTEnv.mem_segmentPathEvent_of_reachable {Ω : Type} [MeasurableSpace Ω]
    {S : MatedCRTEnv Ω} {ρ U ε : ℝ} {ω : Ω}
    (h : ∀ x ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ), ∃ (u : ℂ) (ℓ : ℝ) (Y : Finset ℤ),
      ‖u‖ ≤ U ∧ ∀ θ : ℝ,
        x ∈ hitFinset Y (fun y => segmentDirections u ℓ (cell ε (S.η ω) y)) θ ∧
        ∃ b ∉ interiorCellVertices ε (S.η ω) (ball 0 ρ), Relation.ReflTransGen
          (fun a c => (c ∈ hitFinset Y (fun y => segmentDirections u ℓ (cell ε (S.η ω) y)) θ ∧
            c ∈ cellVertices ε (S.η ω) (ball 0 ρ)) ∧ S.mult ε ω a c ≠ 0) x b) :
    ω ∈ S.segmentPathEvent ρ U ε := by
  intro x hx
  obtain ⟨u, ℓ, Y, hU, hθ⟩ := h x hx
  refine ⟨u, ℓ, Y, chainSelect (fun a c => S.mult ε ω a c ≠ 0)
    (· ∈ cellVertices ε (S.η ω) (ball 0 ρ)) (· ∈ interiorCellVertices ε (S.η ω) (ball 0 ρ)) x,
    hU, fun T a ha => mem_of_mem_chainSelect ha, fun θ => nodup_chainSelect _,
    fun θ => isChain_chainSelect _, fun θ => ?_⟩
  obtain ⟨hxT, b, hb, hreach⟩ := hθ θ
  exact exists_chainSelect_eq_cons_of_reflTransGen hxT hx.1 hb hreach

end MatedCRT
