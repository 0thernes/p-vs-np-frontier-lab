<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Errata & Corrections Log (`ERRATA.md`)

This append-only ledger records every mathematical, formalization, documentation, or provenance correction after release (Defensible Independent AI Research Playbook v1.3, item #39).

## `v1.1.0` (2026-11-25)
- **Zero mathematical errata in theorems `C1`–`C14` or white paper PDF.**
- **Provenance & packaging upgrade:** Added isolated `lean/PalomarChallenge.lean`, `lean/PalomarSolution.lean`, and `lean/comparator.json` so all 15 exported targets pass `lake comparator --config comparator.json --paranoid` on Ubuntu CI across all 6 independent kernels; upgraded repository metadata from Build Standard v1.1.0 (6 classes) to v1.2.0 (10 classes) prior to initial public GitHub publication.
- **Withdrawal plan:** Should any fatal defect ever be identified in a published theorem statement or empirical experiment, a dated entry will be appended here, the README and CLAIMS ledger will mark the affected claim `retracted`, and a new versioned tag will be cut without rewriting prior git history.

## 2026-11-26 statement audit

Source: [2026-11-26 statement audit log](https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md), audited commit `a70733fc388c24e3789eef9fb7afc8464f1669fe` (v1.2.0). The Lean build passes and the 25 axiom lines reproduce. No Lean theorem statement is false. The errors below are in how the results are described, in citation records, and in tooling. The entry above for `v1.1.0` ("zero mathematical errata ... white paper PDF") is superseded by this one for the paper.

### Corrected in README.md, CLAIMS.md, LIMITATIONS.md, CITATION.cff and docs/ in this commit

- "14 unconditional complexity-barrier theorems" now reads "14 statements: the Baker–Gill–Solovay theorem, the counting step of natural proofs, and 12 classical supporting lemmas". Only `C2` is a barrier theorem in full.
- "27/27 Live Crossref Verified" is withdrawn; three DOIs are wrong (see below).
- "Live negative Lean kernel rejection" now reads "negative elaboration test".
- "All 6 independent kernels" now reads "six kernel checks (five checker implementations)".
- `C3` is described as the counting lemma behind Razborov–Rudich, without constructivity, circuit class or efficiency bound.
- `C11` is described as a k-NOT compilation without size bound, not as Fischer's polynomial-size theorem.
- `C14` instruction count is $3\cdot 4^{d-1} - 2$, not $3\cdot 4^{d-1}$; the multiplicands are program constants; "conservation law" and "complexity bound" are dropped.
- `C6` is stated for $2k+1$ variables, $k \ge 0$ (previously "$C_{2k+3}$"), and `C6`–`C7` as minimal unsatisfiability.
- `C10` upper bound is stated for $n = 2^k - 1$ only (previously "$\iff n \le 2^k - 1$").
- `C4` is stated in its pigeonhole form.
- `C5` name corrected to `NaturalProofNonvacuousStmt`.
- "Zero sorry" now notes the 15 intentional comparator stubs in `lean/PalomarChallenge.lean`.
- "Four rigorous falsifiers of aggressive P=NP heuristics" now reads "three exact counterexamples and one numerical illustration against four illustrative SAT heuristics".
- Open frontier `O2` (MC of $\mathrm{CLIQUE}_{4,3}$) is marked as open in this artifact only.
- Prior work added: Ben-Or and Cleve (1992, doi:10.1137/0221006) for `C14`; Turan and Peralta (ePrint 2015/848) and Calik, Turan and Peralta (2019, doi:10.1007/s12095-018-0297-2) for E3; Post's lattice for `C9`; Fischer (1975) as a polynomial-size construction for `C11`.

### Errors in the frozen paper (`paper/main.tex`, `dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf`, `dist/arxiv_submission.tar.gz`), not fixed in place

None of these changes a Lean theorem statement; they correct the paper's prose about the statements.

1. **Where:** abstract (main.tex:76) and main.tex:201. **What:** "8,078 lines across 13 `module` files". **Correction:** at v1.2.0 the library has 17 files and 8,266 lines. Theorem statement affected: no.
2. **Where:** abstract (main.tex:76–78). **What:** "fourteen unconditional theorems ... the Baker–Gill–Solovay dual relativization barrier ...", presented as barrier theorems. **Correction:** fourteen statements: the Baker–Gill–Solovay theorem, the counting step of the natural-proofs argument, and twelve classical supporting lemmas. Theorem statement affected: no.
3. **Where:** abstract (main.tex:79) and the natural-proofs theorem (`thm:natproofs`). **What:** "exact cross-multiplied Razborov–Rudich natural-proofs PRF breaker" and a summed hybrid triangle inequality. **Correction:** `C3` is the counting step only (no constructivity, circuit class, pseudorandomness or asymptotics); `C4` in Lean is the pigeonhole corollary $mB < \lvert a_0 - a_m\rvert \Rightarrow \exists i,\ \lvert a_i - a_{i+1}\rvert > B$. Theorem statement affected: no (the paper's statement of `C4` is stronger than the Lean one).
4. **Where:** abstract (main.tex:80–81) and main.tex:405–413. **What:** "maximal parity-sheaf contextuality for all odd cycles $C_{2k+3}$"; "maximal sheaf obstruction ($H^1 \neq 0$ ...)". **Correction:** the Lean notion is minimal unsatisfiability (unsatisfiable, every drop-one subsystem satisfiable); no sheaf or cohomology is formalized; the family is $2k+1$ variables for all $k \ge 0$. Theorem statement affected: no.
5. **Where:** main.tex:162–168. **What:** "we prove constructively in Lean ... that just the two monotone 3-SAT clause relations ... admit no non-projection polymorphisms", without attribution. **Correction:** "we formalize the classical fact" that these are the clones $T_0$ and $T_1$ of Post's lattice, with a reference to Post's lattice. Theorem statement affected: no.
6. **Where:** abstract (main.tex:83–84), section heading main.tex:468, main.tex:470 and the theorem at main.tex:473–481. **What:** "Fischer's universal dual-rail compiler"; "recovers full general circuit power"; "Berkowitz Slices" in a section about `C10`–`C11`. **Correction:** `C11` is a k-NOT compilation (existence, no size bound; the inverter used is exponential-size); Fischer's 1975 theorem is a polynomial-size construction. Berkowitz slice monotonicity is a Python check (E5) only and is not in Lean. The upper bound covers $n = 2^k - 1$ exactly. Theorem statement affected: no.
7. **Where:** abstract (main.tex:86–88) and main.tex:600–610. **What:** "catalytic multilinear multiplication ... in exactly $3\cdot 4^{d-1}$ operations"; "borrowing dirty memory obeys a strict reversible time--space conservation law". **Correction:** the program has $3\cdot 4^{d-1} - 2$ instructions; it adds $\pm$ the product of $d$ integers fixed in the program (a constant) and restores all other registers; no time-space law or catalytic-space bound is proved. Ben-Or and Cleve (SIAM J. Comput. 21, 1992, doi:10.1137/0221006) should be cited as closer prior work. Theorem statement affected: no.
8. **Where:** abstract (main.tex:94–97) and main.tex:621–623. **What:** "falsify four aggressive $\mathrm{P}=\mathrm{NP}$ heuristics"; "four prominent non-standard proposals". **Correction:** three exact counterexamples and one numerical illustration against four illustrative heuristics built for the bench; only Attack A (Ercsey-Ravasz and Toroczkai 2011) has a published source. Theorem statement affected: no.
9. **Where:** main.tex:528–535 and the E3 discussion. **What:** the multiplicative-complexity values are presented without prior work, and "the best known explicit bound remains $3n - o(n)$". **Correction:** the values reproduce Turan and Peralta (ePrint 2015/848) and Calik, Turan and Peralta (Cryptogr. Commun. 11, 2019, doi:10.1007/s12095-018-0297-2). The sentence mixes general-circuit and multiplicative-complexity lower bounds; the two records should be stated separately with citations (the audit's literature search reports a published $3.1n - o(n)$ general-circuit bound for an explicit function, not re-verified here). Theorem statement affected: no.
10. **Where:** bibliography, main.tex:926–929 (`PichSanthanam2023`). **What:** venue given as FOCS 2023. **Correction:** Pich and Santhanam, "Why are Proof Complexity Lower Bounds Hard?", 2019 IEEE 60th FOCS, pp. 1305–1324, doi:10.1109/FOCS.2019.00080. Theorem statement affected: no.
11. **Where:** bibliography. **What:** anchors named in `docs/statement-fidelity.md` (Goldreich–Goldwasser–Micali 1986, Jeavons 1998, Post, Schnorr 1988; the anchor Mermin 1993 is now replaced by the cited Mermin 1990) are not bibitems, and Ben-Or–Cleve 1992 and the multiplicative-complexity classifications above are missing. **Correction:** add these references. Theorem statement affected: no.

### Errors in hashed records (listed in `MANIFEST.sha256`; not edited in this pass)

1. **Where:** `docs/citation-audit.md` lines 14, 20, 30, and `scripts/check_citations.py` lines 24, 30, 40. **What:** `BoyarPeralta2008` is listed as `10.1016/j.tcs.2008.01.021` (Crossref: "Parametric λ-theories"); `Fischer1975` as `10.1007/3-540-07407-4_7` (Crossref: an LR(k) paper by Kopp); `PichSanthanam2023` as `10.1109/FOCS57990.2023.00126` (Crossref: "Sparse Submodular Function Minimization"). The report prints these wrong titles next to "HTTP 200 Crossref", so "27/27 verified" is false. **Correction:** `10.1016/j.tcs.2008.01.030`, `10.1007/3-540-07407-4_9`, `10.1109/FOCS.2019.00080`; regenerate the report only after titles and authors match. The paper's own bibitems give the correct titles without DOIs.
2. **Where:** `lean/formalization.yaml`. **What:** `forbidden_token_hits: 0` (15 intentional `sorry` stubs exist in `lean/PalomarChallenge.lean`); `live_negative_kernel_rejection: true` (the test is elaboration-level); `total_lean_lines: 8275` (8,266 measured at the audited commit); the disclaimer "unconditional complexity barriers"; `C5` named `NaturalProofNonVacuousStmt` (Lean: `NaturalProofNonvacuousStmt`); `C6` title "C_{2k+3}"; `C8` title "Schaefer Tractable Polymorphisms"; `C11` title "Fischer Universal ... Compilation"; `C14` title "3*4^{d-1} Ops" (Lean: $3\cdot 4^{d-1} - 2$). **Correction:** as in `CLAIMS.md`.
3. **Where:** `results/six_kernel_audit.txt` lines 3–13. **What:** generated for v1.0.0 ("13 files, 8,078 total lines"). **Correction:** regenerate from the v1.2.0 tree and CI log.

### Known issues in the formal code (not yet fixed)

These are docstring and naming defects. None makes a theorem statement false.

1. **Where:** `lean/PVsNP/NonVacuity.lean:24–27`. **What:** NV1 is described as the "3-vertex triangle XOR system", but `oddCycleSystem 0` has one variable ($x_0 \oplus x_0 = 1$). **Correction:** use `oddCycleSystem 1` for the triangle, or fix the docstring. Theorem statement affected: no.
2. **Where:** `lean/PVsNP/NonVacuity.lean:14–16`. **What:** the module docstring says every core hypothesis structure (`Oracle`, `InP`, ...) is shown inhabited; the file has no witness for `Oracle`, `InP`, or the hypotheses of `C3` and `C11`. NV2 restates `C7` verbatim. **Correction:** add the witnesses or narrow the docstring. Theorem statement affected: no.
3. **Where:** `lean/Challenge.lean:29–30`. **What:** "computable oracles `A` and `B`"; `Oracle` is `List Bool → Bool` and the statement has no computability content. **Correction:** "explicitly defined oracles". Theorem statement affected: no.
4. **Where:** `lean/Challenge.lean:85` and `lean/PVsNP/CircuitPhaseTransition.lean:369–379`. **What:** `C11` docstring "Fischer (1975) universal reduction"; `FischerReductionStmt` has no size bound and `compileMonotoneAux` recurses twice per variable, giving an exponential-size inverter. **Correction:** rename to "k-NOT compilation (existence; no size bound)" or prove a polynomial bound on `(fischerCompile k gs).length`. Theorem statement affected: no.
5. **Where:** `lean/Challenge.lean:78–83`. **What:** `C10` docstring "exact bounded-negation phase transition"; the upper bound is for $n = 2^k - 1$ only. **Correction:** add a padding lemma or state $n = 2^k - 1$. Theorem statement affected: no.
6. **Where:** `lean/PVsNP/SheafPolymorphism.lean:49–52`. **What:** `IsMaximallyContextual` is minimal unsatisfiability; the name suggests a sheaf-theoretic notion that is not formalized. **Correction:** rename or document. Theorem statement affected: no.
7. **Where:** `lean/PVsNP/CatalyticAlgebra.lean:98–118`. **What:** `catalyticProdProg` takes the multiplicands as program constants (`addVal`), so it computes a constant. **Correction:** document, or read the multiplicands from registers. Theorem statement affected: no.

### Known issues in CI and scripts (not yet fixed)

1. **Where:** `.github/workflows/ci.yml:44–55`. **What:** the "live negative Lean kernel rejection" step is rejected by `decide` during elaboration and passes on any non-zero exit. **Correction:** call it a negative elaboration test and check for the expected error text; for a kernel-level test, give a tampered export to the external checkers.
2. **Where:** `scripts/check_citations.py:84–104`. **What:** any successful Crossref lookup counts as verified; titles are not compared; CI runs `--offline`, which only checks bibliography key parity. **Correction:** fail on title or first-author mismatch.
3. **Where:** CI run 45829725341, log line 997. **What:** nanoda prints `Skipped exported but unpermitted axioms ["sorryAx"]` during `lake check` before accepting. **Correction:** explain the line or make unpermitted axioms a hard error.

## 2026-11-26 Round 3 hardening pass (hashed records & tooling resolved)

The hashed-record and CI/script defects logged in the `2026-11-26` statement audit above have been resolved without altering any Lean theorem statement or overwriting the frozen PDF (`paper/main.tex` / `dist/Donahue_2026_p_vs_np_barrier_anatomy.pdf` errata remain listed above):

1. **Citation DOIs & title/author enforcement (`scripts/check_citations.py`, `docs/citation-audit.md`, `tests/test_all.py`):** Replaced the 3 mismatched DOIs with verified canonical DOIs (`BoyarPeralta2008` -> `10.1016/j.tcs.2008.01.030`, `Fischer1975` -> `10.1007/3-540-07407-4_9`, `PichSanthanam2023` -> `10.1109/FOCS.2019.00080`), upgraded `scripts/check_citations.py` to fail on title-overlap or author-surname mismatch (requiring author verification when Crossref omits a historical title such as `MignonRessayre2004`), regenerated `docs/citation-audit.md` live (`25/25` Crossref DOIs title+author verified, `2` print/tech-report records without DOIs, `0` retractions), and added `test_citation_verifier_rejects_wrong_article_doi` in `tests/test_all.py`.
2. **Formalization ledger & kernel audit (`lean/formalization.yaml`, `results/six_kernel_audit.txt`):** Synchronized line count (`8,266`), `PalomarChallenge.lean` 15 intentional stubs, `negative_elaboration_test`, `C5` symbol `NaturalProofNonvacuousStmt`, and `C6`/`C8`/`C11`/`C14` descriptions with `CLAIMS.md` and `v1.2.0` CI run `45829725341`.
3. **CI negative elaboration check (`.github/workflows/ci.yml`):** Relabeled accurately as a negative elaboration test and asserted the expected `decide` rejection diagnostic instead of accepting arbitrary non-zero exits.
4. **Provenance refresh (`MANIFEST.sha256`, `data/MANIFEST.sha256`, `data/MANIFEST.sha256.tsr`):** Regenerated SHA-256 manifests for the updated hashed records (`docs/citation-audit.md`, `lean/formalization.yaml`, `results/six_kernel_audit.txt`) and re-stamped `data/MANIFEST.sha256.tsr` via DigiCert RFC 3161 TSA; frozen PDF and Lean source hashes are unchanged.
