# Exposed points of Lipschitz-free spaces in Lean 4 (test)

> **Important — please read first.**
>
> * This is a **personal test** by an M2 student, nothing more. Its only purpose is to check
>   whether the proofs of a published paper can be written in Lean, and to put online an
>   alternative proof of the finite case proposed by the AI assistant Claude.
> * **The authors of the paper (C. Petitjean, A. Procházka) are not associated with this
>   project in any way.** They did not request, supervise, review or endorse it, and they
>   are not responsible for its content.
> * **All mathematical credit belongs to the authors of the paper.** This repository claims
>   no new mathematical result. The alternative proof of the finite case (an easy case, which
>   the paper itself describes as immediate) was proposed by Claude and is not presented as a
>   research contribution.
> * This is not a Mathlib contribution. Any error in the Lean code is mine.

A Lean 4 / Mathlib formalization around the paper

> C. Petitjean, A. Procházka, *On exposed points of Lipschitz free spaces*, arXiv:1810.12031 (2018).

Main result of the paper: for a complete metric space $M$ and $p \neq q$, the molecule
$m_{pq} = (\delta(p) - \delta(q))/d(p,q)$ is an exposed point of the unit ball of the
Lipschitz-free space $\mathcal F(M)$ if and only if the metric segment $[p,q]$ is $\{p,q\}$.

To our knowledge, Mathlib does not contain Lipschitz-free (Arens–Eells) spaces yet
(checked with Loogle on 11 November 2026).

## Contents

| File | What it does | Status |
|---|---|---|
| `LipschitzFree/FiniteExposed.lean` | **Finite case, fully proved.** For a finite metric space, with $\mathcal F(M)$ modelled by functions $\mu : M \to \mathbb R$ and the unit ball defined by duality with 1-Lipschitz functions: $m_{xy}$ is exposed iff $[x,y]=\{x,y\}$ (`mol_exposed_iff`), and $\lVert m_{xy}\rVert = 1$ (`fnorm_mol`). The proof is a direct one, specific to the finite case (it does not use the paper's "magic function"). | no `sorry`, no extra axiom |
| `LipschitzFree/PetitjeanProchazka2018.lean` | **The proofs written in the paper**, for a complete metric space: Lemma 3, Lemma 4, the remark after Lemma 5, Lemma 6 and Theorem 1. The results the paper *cites* from other works are **assumed**, as explicit hypotheses of the theorems (not as axioms): basic properties of $\mathcal F(M)$ (Godefroy–Kalton), Lemma 2.23 of Fabian et al., Proposition 2 (Aliaga–Pernecká), Lemma 5 (Ivakhno–Kadets–Werner). Theorem 1 is stated with base point $q$, as in the paper's proof. $\mathcal F(M)$ is an abstract Banach space satisfying the assumed properties. | no `sorry`, no extra axiom; cited results are hypotheses |

So Lean checks the implication *"cited results ⇒ Theorem 1, by the paper's proof"*.
Whether each assumed hypothesis faithfully matches its source is **not** something Lean can check;
reviews are welcome.

## Verification

Both files were checked on 12 November 2026 on <https://live.lean-lang.org>
("Latest Mathlib with Lean v4.36.0-rc2"): no errors, and every main theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` (see the `#print axioms` lines at the end of each file).

On the experimental Comparator service (<https://comparator.live.lean-lang.org>), with a challenge
file containing only the definitions and statements, five independent kernels
(Lean paranoid, lean4lean, nanoda, con-leche, con-ron) accepted `PetitjeanProchazka2018.lean`;
the run then stopped without any error message during the last step ("Lean default kernel"),
so we do not claim a complete Comparator validation.

The local build configuration (`lakefile.toml`, `lean-toolchain`) has **not** been tested with
`lake build` yet.

## Notes

* Comments and docstrings are in French.
* The code is not written to Mathlib standards.

## How this was made

The Lean code was produced with the AI assistant Claude (Anthropic), under the direction of the
author, and every proof was checked by the Lean kernel. The author is responsible for the
modelling choices and for any remaining errors.

## Author

Samuel Moatty — M2 student, Mathématiques approfondies (CTU), Université Marie et Louis Pasteur, Besançon.

## License

Apache License 2.0 (the license used by Mathlib).
