# Writing the specification

We are proving a program using `Coq` and the `Iris` framework. Based on the
`@spec`/`@inv`/`@linpoint` comments in the source code and the `heap_lang`
implementation, generate the `Iris` specifications:
1. Ghost State: Define the necessary Resource Algebras (Cameras) to represent
   the logical state described in the comments.
2. Invariants: Define the persistent internal invariant (e.g., IsData). You
   MUST strictly enforce the memory ownership rules described in the `@inv`
   comments, linking physical state (enums/flags) to Separation Logic
   permissions (like l ↦ v).
3. Logically Atomic Specs: Write the Hoare triples for the public functions
   using the Logically Atomic notation (<<< ∀ state, ... >>>) at the execution
   points defined by `@linpoint`.

Leave the proofs `Admitted`.

## Rules

- Do not analyze the code, focus on the specification.
- Do not attempt to write any proof.
- Prefer the Hoar triples syntax: `{{{Pre}}} e {{{v; Post}}}`.
- Use `rocq-mcp` and `coq-lsp` to verify the Coq files.
