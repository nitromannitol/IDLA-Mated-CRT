# Audit of corrections C11–C12

C11 replaces Lemma 3.1's arbitrary random input by deterministic preparation: for each deterministic input sequence a deterministic thinning supplies one almost-sure event, inherited by all measurable random subsequences and countable families. The proof prepares the uniform fixed-mesh estimates by a summable diagonal; its interior, measurable selection, harmonic boundary and zero-boundary ball arguments are in the corrected draft. The C10 factor ε⁻¹ in the boundary modulus is retained. C12 puts fixed t and the deterministic input sequence before the thinning and almost-sure assertion in Lemma 4.6, and gives relative compactness, Hölder limits and measurable selection; Lemma 4.7 has the same corrected sequence order. An event for each fixed input does not imply a common event over all deterministic inputs (see E-x3-2 in GAPS-SEC2567A.md).

The following checks concern the sequence quantifiers; they do not certify independent parts of the proofs. Locations are result labels, stable under line shifts.

| Use | Verdict |
| --- | --- |
| Lemma 3.3, Green-kernel compactness | Prepared deterministic input, rational compact exhaustion away from the pole, then random extraction. Every refinement inherits the estimates. Identification is needed for every limit; the printed proof's m₀/6 instead of c₀/6 remains G4. |
| Lemma 3.4, occupation convergence | No direct 3.1 call. Deterministically thin for cell size, exit estimates and quenched walk convergence; use the subsequence criterion. The separate smaller-domain killing issue remains G4. |
| Lemma 3.5, harmonic and forced Dirichlet pieces | Prepare pointwise data and normalized exit barrier before the random extraction; apply boundary control to normalized harmonic data, and zero-boundary comparison to the forced piece. The printed barrier normalization/PDE is independently incorrect (G4). |
| Lemma 3.6 | No compactness call; its countably many fixed starting points can be prepared by diagonalization. |
| Lemma 3.7, first and second compactness extractions | Prepare rational poles, cutoffs and bump problems first; the random input lies inside the prepared sequence. Countably many truncated families have bounded Laplacian, bounded magnitude and zero boundary data. The printed annulus/test-function and near-pole identifications fail independently (G1 and G2). |
| Lemmas 4.3–4.5 | Fixed-mesh deterministic bounds; no extraction. |
| Lemma 4.7 | Deterministic thinning followed by Borel–Cantelli; the odometer and exit-time bounds are uniform in t. |
| Lemma 4.6 | Prepare the 3.1 event and 4.7 bound together, apply the zero-boundary ball comparison, and extract measurably for fixed t. Relative compactness is inherited by every further subsequence. |
| Lemma 4.8 | For fixed t prepare Green, Dirichlet and exit-time convergences on rational balls and rational polynomial data before choosing a limit. Compactness holds on every further subsequence. **The printed comparison does not establish every-limit identification:** the additive δ boundary margin vanishes on normalization (G3). Thus the sequence-quantifier use is valid conditional on a separate repair of G3, not a complete proof of 4.8. |
| Theorem 4.1 | Every-limit identification plus relative compactness gives convergence on a prepared thinning; the deterministic subsequence criterion yields convergence in probability. This use is conditional on the separate 4.8 comparison and constant issues (G3–G4). |
| Proposition 4.2 | Thin for Theorem 4.1, Green convergence on countably many rational annuli and cell sizes; a random spatial radius is chosen only after those convergences. Conditional on its cited inputs. |
| Lemmas 5.2–5.4 and Proposition 5.1 | Fixed-mesh estimates and in-probability inputs; no new random mesh. Proposition 5.1's stopped-cluster lower-inclusion issue remains separate (C9 audit). |
| Section 6 | Uses fixed-mesh estimates and Proposition 5.1; Borel–Cantelli over dyadic spatial radii is not a random mesh extraction. Conditional on cited results. |
| Section 7 | Theorem 4.1 and Green convergence are used on spatial sets, handled by localization away from the origin; later iteration is at fixed mesh. Conditional on cited results and separate iteration issues. |
| Proposition 8.1 and Theorems 1.4 and 1.6 | Combine fixed-parameter in-probability statements; quantum-area scaling sends ε to ε/b for deterministic b. Random spatial radii are localized; no random mesh selection. Conditional on cited results. |
| Appendix A and introductory references | No probabilistic compactness application. |

Independent audit: fleet `audits/n3/audit/REPORT.md` passes the Lemma 3.1 repair but finds G1–G4 in downstream proofs. Paper-level repair proposals and their status are in `PROOF-REPAIRS-G.md`; they are not incorporated by C11–C12. The use checks above do not assert those gaps are closed.
