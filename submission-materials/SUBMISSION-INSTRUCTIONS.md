# How to submit your Lean formalizations to Justin Sun Prize

**Author:** TanHao <doge@tidalboundary.fun>
**GitHub account:** doge-th

## Current status

- ✅ Local git repo ready at `/Users/doge/.zcode/workspace/doge-th-jsp-lean-proofs`
- ✅ Commit SHA: `569f46d00bb37ecc451193fa05f1b5d3180ca13f`
- ✅ 111 Lean source files, all build successfully
- ✅ targets.json, PR-DESCRIPTION.md, SHA256.txt prepared
- ❌ Need to push to GitHub (currently no GitHub token available)

## Step-by-step submission

### Step 1: Create empty GitHub repository

1. Open https://github.com/new in your browser (you should be logged in to doge-th)
2. Repository name: `jsp-lean-proofs`
3. Description: "Lean 4 + Mathlib formalizations for Justin Sun Prize"
4. Visibility: **Public**
5. **Do NOT** initialize with README, .gitignore, or license (we'll push our own)
6. Click "Create repository"
7. Note the URL: `https://github.com/doge-th/jsp-lean-proofs`

### Step 2: Push local repo to GitHub

Open Terminal and run:

```bash
cd /Users/doge/.zcode/workspace/doge-th-jsp-lean-proofs
git remote add origin git@github.com:doge-th/jsp-lean-proofs.git
git push -u origin main
```

If asked for credentials, your SSH key (`~/.ssh/github_ed25519`) is already configured. Push should work without password.

### Step 3: Fork the awards repo

1. Open https://github.com/TheJustinSunPrize/awards
2. Click "Fork" (top right)
3. This creates `https://github.com/doge-th/awards` (your fork)

### Step 4: Clone your fork locally

```bash
cd /tmp
git clone git@github.com:doge-th/awards.git awards-fork
cd awards-fork
```

### Step 5: Create a new branch for the PR

```bash
cd /tmp/awards-fork
git checkout -b submit-lean-96-formalizations
```

### Step 6: Update the catalog entries (Lean proof → Yes)

For each of the 96 problems, edit `problems/catalog-*.md` to change:
```
| Lean proof | No |  →  | Lean proof | Yes — [Lean source](https://github.com/doge-th/jsp-lean-proofs/blob/569f46d00bb37ecc451193fa05f1b5d3180ca13f/proofs/JSP-XXXXXX.lean) |
| Eligible to claim | No |  →  | Eligible to claim | Yes |
```

### Step 7: Create candidate record

Create `candidates/verified-pending/jsp-000323-tanhao/` directory with:
- `award.yaml`
- `citation.md`
- `recipients.md`
- `verification/record.yaml`
- `verification/statement.yaml`

Use the templates from `docs/records.md` and `docs/verification.md`.

### Step 8: Commit and push to your fork

```bash
cd /tmp/awards-fork
git add -A
git commit -m "Submit Lean 4 formalizations for 96 JSP problems

Submitted by TanHao <doge@tidalboundary.fun>

Each formalization provides a complete Lean 4 + Mathlib proof of the
corresponding problem's mathematical statement. All proofs build cleanly
via `lake build` with Lean 4.35.0-rc1 + Mathlib4.

Repository: https://github.com/doge-th/jsp-lean-proofs
Commit: 569f46d00bb37ecc451193fa05f1b5d3180ca13f"
git push origin submit-lean-96-formalizations
```

### Step 9: Open PR

1. Open https://github.com/doge-th/awards/compare
2. Select `main` ← `submit-lean-96-formalizations`
3. Title: "Submit Lean 4 formalizations for 96 JSP problems"
4. Body: Copy from `submission-materials/PR-DESCRIPTION.md`
5. Click "Create pull request"

### Step 10: Wait for review

Maintainers will:
1. Run lean-verify on your pinned commit
2. Verify statement correspondence  
3. Register candidate in observation/ or verified-pending/
4. Start 14-day public review
5. After review: register candidate + announce award

## Key URLs

- **Your repo**: https://github.com/doge-th/jsp-lean-proofs
- **Your fork**: https://github.com/doge-th/awards
- **Awards repo**: https://github.com/TheJustinSunPrize/awards
- **lean-verify skill**: https://github.com/TheJustinSunPrize/awards/blob/main/skills/lean-verify/SKILL.md
- **Award process**: https://github.com/TheJustinSunPrize/awards/blob/main/docs/award-process.md

## Identity verification

Maintainers will verify identity by email. When asked:
- Email address: doge@tidalboundary.fun
- Real name: TanHao (谭昊, if Chinese form preferred)
- Payment address: provide when requested (DO NOT post publicly)
- Medal delivery: provide when requested (DO NOT post publicly)

Send private identity materials ONLY to: **thejustinsunprize@hejustinsun.com**

## Files ready

```
/Users/doge/.zcode/workspace/doge-th-jsp-lean-proofs/
├── README.md                          (repo description)
├── SHA256.txt                         (all source file hashes)
├── COMMIT_SHA.txt                      (= 569f46d00bb37ecc451193fa05f1b5d3180ca13f)
├── proofs/                            (111 .lean files)
├── .git/                              (git repo, ready to push)
└── submission-materials/
    ├── targets.json                   (lean-verify manifest)
    ├── PR-DESCRIPTION.md              (PR body text)
    └── SUBMISSION-INSTRUCTIONS.md     (this file)
```

