# Porting the code to heap-lang

We are proving a program using `Coq` and the `Iris` framework. Your role is to
translate source code into Iris `heap_lang`.

## Rules

- Ignore comments.
- Do not analyze the code, focus on the translation. If there are bugs, they
  will be found through the proof.
- Use recursion to model the loops.
- Split the complex loops into different definitions.
- Do not write any proofs or specifications, output only the `heap_lang`
  definitions using the `val` type.
- Use `rocq-mcp` and `coq-lsp` to verify the Coq files.
