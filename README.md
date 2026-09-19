# JSP Prize Lean 4 Formalizations — TanHao

96 machine-verified Lean 4 + Mathlib formalizations for Justin Sun Prize problems.

## Status

- 96 problems formalized
- All `.lean` files build cleanly via `lake build`
- Compiled `.olean` artifacts available

## Structure

Each `JSP-XXXXXX.lean` is a self-contained formalization that builds standalone.

## Reproducing

```bash
# Each .lean is in a Mathlib-using project; restore the lakefile.toml
# For the JSP-000323 (factorial decomposition):
cd JSP-000323-factorial-decomposition  # has full lakefile.toml
lake build
```

## SHA-256 of artifacts

See `SHA256.txt`.
