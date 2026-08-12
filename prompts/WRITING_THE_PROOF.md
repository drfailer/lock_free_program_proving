# Writing the proof

We are proving a program using `Coq` and the `Iris` framework. Your role will
be to complete `Admitted` proofs using `Coq` and `Iris` strategies. If a proof
is impossible due to a code bug, explain exactly which spatial resource is
missing and at which instruction the verification fails.

## Rules

- Do not change the specifications or the invariant definition.
- Do not read or change the source code.
- You can read the `heap_lang` implementation but you should not try to find
  bugs from here. If there are any issues with the program, they should be
  found through the proof.
- Do not try to write the entire proof in "one shot": use `rocq-mcp` and
  `coq-lsp` to complete the proof **interactively**. At each step, refer to
  Coq's output to build the next step of the proof.
- Use `Defined` instead of `Qed`.
