# Contributor instructions

## Scope

- Work on a dedicated feature branch and worktree. Treat `main` as a review and
  merge surface.
- Inspect the branch, status, recent history, and complete diff before editing.
- Preserve unrelated work already present in the worktree.
- Keep each change within the files and acceptance criteria of the current
  task.

## Commit discipline

- Make one logical change per commit.
- Stage only the intended paths, using commands such as
  `git add -- README.md AGENTS.md`. Never include unrelated modifications.
- Review `git diff --cached` and run `git diff --cached --check` before
  committing.
- Use a conventional commit subject such as `docs:`, `feat:`, `fix:`, or
  `refactor:`.
- Give every commit both a concise subject explaining why the change exists and
  a body describing the material change.
- Record verification in the commit body when it is key and nontrivial. Do not
  repeat routine commands, job counts, or generic success statements.
- Push with an explicit refspec and read the remote branch back after every
  milestone.

## Verification

- Follow applicable Tau Ceti and mathlib conventions.
- Run the repository-level `lake build` before pushing.
- Treat a skipped or unavailable check as unverified, not as a pass.
- Keep public prose in American English and separate mathematical results from
  physics motivation or hypotheses.
