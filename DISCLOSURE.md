# Disclosure

JD Jones directed this project. Claude (Anthropic) in Claude Code was used throughout: the statements, the Lean proofs,
the standard-library replay of the tables, the literature and prior-art searches, the checkers and the repository were
produced in that process. The theorem is classical (Vaidyanathaswamy 1928; Hiller 1985; Kuzmanovich–Pavlichenkov 2002;
Bamberg–Cairns–Kilminster 2003); the proofs here follow the standard route through minimal and cyclotomic polynomials
and the companion blocks, written for Mathlib. Verification status is stated in VERIFICATION.md. No independent human
review or source-author endorsement is claimed.

A pre-submission consult with GPT-6 Astra (OpenAI), using parallel review and proof-development agents,
recovered and read both original Vaidyanathaswamy papers, corrected the source documentation, and added
the formalizations in `Crystallographic/Extensions.lean` and `Crystallographic/InvariantForm.lean`.
The same consult supplied the separately labelled, unformalized derivations in
`MATHEMATICAL-EXTENSIONS.md` and independently replayed the checks described in `VERIFICATION.md`.
The additions formalize classical arguments; no mathematical priority or source-author endorsement
is claimed for them.
