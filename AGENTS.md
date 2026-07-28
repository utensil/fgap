# Contributor instructions

## Scope

- Work on a dedicated feature branch and worktree. Treat `main` as a review and
  merge surface.
- Start independent work from the current `main`. If work depends on pull
  requests with `lgta`, record their numbers and the exact base commit in the
  pull-request body. Use a temporary branch containing only the named
  prerequisites when more than one is needed. Never use `dev` as an implicit
  feature base.
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

## GitHub communication

- AI agents own code and documentation, the `dev` integration branch, issue and
  pull-request titles and bodies, and commit messages.
- Do not post comments or apply `lgth`. Read human comments and address them
  through commits or an updated issue or pull-request body.
- Record review and revision considerations and changes only in commit
  messages.

## Review states

- `lgta` means "looks good to AI agent." After `lgta`, pull-request work may be
  integrated into `dev` in Git history, not through GitHub. `dev` aggregates
  this work for integration and testing; it is not a default feature base and
  is reconstructed from `main` and the remaining `lgta` work after `main`
  changes.
- `lgth` means "looks good to human." Only a human may post the holistic review
  comment and apply `lgth`, which gates a squash merge into `main`.
- Both states apply to a specific head commit. A new commit requires review
  again.

## Verification

- Follow applicable Tau Ceti and mathlib conventions.
- Run the repository-level `lake build` before pushing.
- Treat a skipped or unavailable check as unverified, not as a pass.
- Keep public prose in American English and separate mathematical results from
  physics motivation or hypotheses.
