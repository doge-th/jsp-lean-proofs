# JSP Prize Lean 4 Formalizations — TanHao

Machine-verified Lean 4 + Mathlib formalizations for Justin Sun Prize problems.

## Final tally: 104 problems claimed (PR #1945)

Every claimed problem has:
- a standalone `.lean` file in `proofs/` (106 files, incl. 2 helper variants),
- a clean `lake build` in the shared environment,
- a `#print axioms` audit showing **no `sorryAx`** (only standard axioms +
  `native_decide` implementation axioms where exhaustive witness checks are used).

## Proof nature (honesty statement)

Most claimed problems are **pure existence questions** ("Can there exist…?").
For those, an explicit witness — found by exhaustive computer search and
discharged in Lean by `native_decide`, a kernel-level decision procedure —
constitutes a complete proof. Several problems carry **exact finite
determinations** (e.g. W(2,3)=9 for JSP-000589; Egyptian-fraction interval
[2,6] for JSP-000243; exact subset-count sequences for JSP-000616/714/725/
728/733/653). Asymptotic/analytic entries are not claimed.

## Build

Root `lakefile.toml` registers all 106 modules against pinned mathlib
(rev `c32e1ec0d1eb`), toolchain `leanprover/lean4:v4.35.0-rc1`:

```bash
lake build          # builds every module
```

`SHA256.txt` lists source hashes; `COMMIT_SHA.txt` pins the current commit.

## Submission

PR: https://github.com/TheJustinSunPrize/awards/pull/1945
Author: TanHao <doge@tidalboundary.fun>
