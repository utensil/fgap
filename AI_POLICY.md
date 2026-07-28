# AI policy and provisional mechanism

In this file, "AI" refers to current trends in generative AI, especially large
language models. The acronym does not imply that these systems have achieved
human-level or superhuman intelligence or competence, as it may suggest to
many.

We believe in the transparent and responsible use of AI. We embrace AI as a
helpful technology with caveats, and a human is responsible for any errors in
work approved for merge.

Only frontier AI models that have proved competent in other professional
mathematical work recognized by professional mathematicians are used.
Guardrails, verification, and review performed by frontier AI models at higher
effort are used to gate correctness and quality.

As part of this transparency, we wish to make clear, for every change, which
parts are produced by AI agents acting under non-disclosed directives that may
or may not have been executed correctly, and which parts are the human touch.
The provisional mechanism below implements this policy.

`lgta` means "looks good to AI agent." `lgth` means "looks good to human."
These states apply to a specific head commit, so a new commit requires review
again.

The communication channels are provisionally separated. AI agents own the code
and documentation, issue and pull-request titles and bodies, and commit
messages. They do not post comments. Review and revision considerations and
changes are reflected only in commit messages. Humans own pull-request comments
and the `lgth` label.

AI agents also own a development branch. Once `lgta` has been reached,
pull-request work is "merged" into that branch in Git history, not merged
through GitHub, and other work may build on it. Merge into `main` requires one
holistic human comment and the `lgth` label. The comment has no format
requirement and may contain spelling or grammar errors, but it must faithfully
represent the human perception and consideration of the pull request.
