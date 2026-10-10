# Disclosure

JD Jones directed this project. Claude (Anthropic) in Claude Code was used throughout: the statements, the Lean proofs,
the standard-library replays, the literature and prior-art searches, the checkers and the repository were produced in
that process. A GPT-6 Pro (OpenAI) consult on 2026-10-10 reviewed the repository and contributed the seven statements of
`Crystallographic/Extensions.lean` and `Crystallographic/InvariantForm.lean` with their Lean proofs, the paper proofs of
the determinant `−1` threshold and of the class count of PROOF.md §12 with `scripts/check_minimal_classes.py`, and the
page references to Vaidyanathaswamy's two 1928 notes; Claude re-derived and verified these, proved the determinant `−1`
threshold in Lean, integrated them, and wrote the final documents. The theorem is classical (Vaidyanathaswamy 1928;
Hiller 1985; Kuzmanovich–Pavlichenkov 2002; Bamberg–Cairns–Kilminster 2003); the proofs follow the standard route
through minimal and cyclotomic polynomials and the companion blocks, written for Mathlib. Verification status is stated
in VERIFICATION.md. No independent human review or source-author endorsement is claimed.
