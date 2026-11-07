# Lemma 3.6: audit of uses

Author-approved replacement, 2026-11-06. Locations below identify the original
corrected draft before C13–C14, not the preserved arXiv source. The complete
argument and its literature inputs are in `LEMMA36-REPLACEMENT.md`.

- **Direct use, Lemma 3.5, line 1453.** Its harmonic part is the expectation
  of the projected boundary datum after normalization. C13 applies the same
  projection to the statement and decomposition. Pointwise convergence for
  rational points permits a deterministic diagonal extraction; the stronger
  uniform conclusion also suffices. No quantitative rate is used.
- **Lemma 3.7, lines 1565 and 1674.** The Dirichlet problems have zero boundary
  data and a countable prepared family of deterministic smooth sources. The
  corrected harmonic part is zero; C11 supplies deterministic preparation.
- **Odometer compactness, line 1948.** The invocation of the proof's boundary
  barrier requires the lens barrier and bounded-Laplacian control described
  in `PROOF-REPAIRS-G.md`; it is not a consequence of pointwise harmonic
  convergence alone.
- **Lemma 4.8, lines 1981 and 2031.** Rational balls and rational polynomial
  data form a countable prepared family, so an environment-dependent choice
  from it is permitted. Polynomials extend to a collar; their unprojected
  and projected values differ by o(1) uniformly on boundary cells, and the
  maximum principle transfers uniform convergence. C14 changes the printed
  boundary offset to `m_eps (phi^delta + delta)`, as required for domination
  and the displayed limiting boundary value. This implements G3, which had
  been recorded in `PROOF-REPAIRS-G.md` but not yet applied in the TeX.
- **Announcements, lines 339, 1143, 1540 and 1952.** These announce, discuss,
  or describe the Dirichlet result, not additional harmonic convergence uses.

The direct label search finds no other invocation of Lemma 3.6; no downstream
use requires its comparison rate. This audit is limited to these dependencies.
Independent residual normalization issues noted in the full replacement remain:
the inhomogeneous Step 1 display still prints `m_0` instead of C1's `c_0`, and
the normalized exit-time equation in Step 3 prints `-1` rather than `-c_0`.
The zero-boundary lens barrier is independently required as noted above.
