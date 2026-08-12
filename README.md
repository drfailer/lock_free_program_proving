# Lock-free program proving using LLMs

The goal of this experiment was to use an LLM to write a lock-free data
structure (based on code skeleton and specifications), and prove its
correctness using `Coq` and `Iris`. Before starting the proving process, the
code was manually poisoned to assert that AI's ability to find bugs through the
proof.

## The data structure

The data structure used as a test case in this project is a custom mostly
lock-free chunked queue. The queue uses monolithic counters for the head and
the tail, and the data is stored in a linked list of chunks (arrays of slots).
The linked list is circular and creates a ring buffer which can grow but not
shrink (nodes are freed at the end). A mutex is used when the queue needs to
grow. The chunks are composed of slots, and each slot stores a data element
and a state which is used to determine the slot ownership (the slot is empty,
being written or being read).

The goal is to have a realistic lock-free algorithm to prove, but this does not
aim to be the most efficient lock-free queue implementation.

The queue implementation is written in [Odin](https://odin-lang.org/) because it's a simple and amazing
language!

## The experiment

### The steps

This experiment was realized in four steps:

1. **Implementation**: provide code skeleton and data structure description to
   the LLM and let it write the implementation. The proved code can also be
   hand-written (yes some people still do that), but the LLM's ability to write
   simple and correct lock-free code was also evaluated here.
2. **Heap-lang**: another agent was asked to port the Odin code to Iris heap-lang.
3. **Specifications**: for this test, it was chosen to keep the prompts generic
   (see `prompts/`), so the specifications where provided through comments in
   the code (we keep the specification close to the implementation). The agent
   was asked to read the `@spec`/`@inv`/`@linpoint` comments, and generate the
   Coq/Iris code. All the theorems/lemmas were left Admitted in this step.
4. **Proof**: in this final step, the AI had to complete the admitted theorems.
   Some additional prompting was done to break complex lemmas into sub-proofs to
   reduce context explosion and facilitate the proving process.

Because of a logic issue that wasn't found through the proof due to a missing
specification, an extra-step was used to fix the code and update the proof.

### The results

#### Implementation

The first version of the code that has been proved presented a logic issue that
was only found later (not through the proof, indicating a hole in the
specifications). The bug was located in the grow logic: in the original
version, block reuse (circular linked list) wasn't implemented, and the push
function was always reallocating new blocks instead of reusing the empty ones
behind the head. Correcting this issue required updating both the code and the
specifications to maintain the correctness of the proof. Note that this logic
issue was not a race bug, and both the push and pop functions were working
(which was proved). However, the block reuse speciation was not written which
explains why this issue wasn't detected when writing the proof. Not being
careful enough when reading the AI output and not writing all the
specifications properly was a mistake. However, this mistake is a good
demonstration that the proving process only demonstrates the program
correctness with respect to the specifications, and it is possible to
successfully prove a wrong program. Note as well that this error had no impact
on the slot ownership bug introduced on purpose to make sure that AI was able
to find bugs through the proof.

For the test part, the agent was simply told to write a test that verifies all
the queues operations. Surprisingly, the AI only wrote a sequential test which
was not able to detect the bug introduced later.

##### The introduced bug

The bug was introduced where the data is written in the push function.

Expected code:

```odin
sync.atomic_store_explicit(&slot.state, .Writing, .Relaxed)
slot.value = data
sync.atomic_store_explicit(&slot.state, .Valid, .Release)
```

Poisoned code:

```odin
sync.atomic_store_explicit(&slot.state, .Writing, .Relaxed)
sync.atomic_store_explicit(&slot.state, .Valid, .Release)
slot.value = data
```

This is an easy one to detect, but its a good first test for this experiment.
Finding such a bug still requires rigorous slot ownership specification, and
this is a bug that can be found early in the proving process (writing the
entire proof took a long time).

#### Heap-lang translation

Translating the code into heap-lang is necessary to make the whole proof using
Iris. This is also the first potential point failure because we must guaranty
that the heap-lang code matches the original Odin code perfectly. Multiple
passes were necessary to complete this step (initial writing + post
verifications). Note that during the first pass, the agent solved the bug while
translating the code which is a big issue because it invalidates the proof.
Focusing and constraining the agent on the translating task is difficult, but
the critique agents were able to find the inconsistencies during the
verification passes.

#### Specification

Here, the complexity is moved to the human side. Translating specification
comments into Coq is a relatively easy task, but writing the specifications
requires time and experience. I'm not experienced enough in the field meaning
that the current specifications could be improved to make the code even more
robust, or make the proof easier. The current specifications were enough to
find the introduced bug. In this step, both the specifications definitions, and
their translation into Coq can benefit from an external critique and
verification passes.

Once the specifications are written in Coq, breaking them down into small and
easy to prove sub-lemmas will improve the proving process in the final step.

#### The proof

This last step is the most expensive and time consuming one. The proving
process is very mechanical, however it remains quite difficult, especially when
proving parallel programs. Concurrency introduces extra complexity and the
resulting proof is very verbose and uses complex mechanisms from Iris. Even
though the LLMs seemed to know the concepts and some of the tactics (showing
that this was part of the training data), it still required a lot of trial and
error to complete the proofs.

As said previously, the introduced bug can be found early in the proof and it
didn't take long to the AI to find and prove the error. Things became more
complicated when the AI moved to the top level proof (showing the linearization
of the push and pop functions), and it took several days to prove those
specifications.

Interestingly, when asked to complete a proof without further instructions,
most LLMs try to solve the entire proof in one-shot. This either results in a
completely wrong output, or no output at all when the LLM get stuck on complex
recursion (the request simply times out). To avoid those issues, the AI must be
told to write the proof interactively. This was done using the MCP server which
was not particularity convenient to use (the AI was often falling back to the
compiler). In my opinion, the MCP server is simply not adapted to this use
case, and it would be much easier to do interactive proving using the compiler
directly (using command line arguments to specify which lemma to compile, and
up to which line in a similar way this can be done in the IDE; the other lemmas
should be considered admitted or cashed to reduce compile time).

The AI was also tempted to change the specifications. Changing the
specification, the heap-lang code and reading or changing the original source
code should be explicitly forbidden in the prompt.

A more experience Coq and Iris user may know how to break the specifications or
rewrite them in a way that makes the proving process easier and faster. A skill
file presenting advanced patterns could also improve the agent performance
during this phase.

## Solving the reuse bug

TODO

## Conclusion

The goal of this work was to try to automate all the proving process of a
concurrent lock-free program using AI. This experiment show an example approach
for the prompting and specification definitions, and demonstrate how AI can be
used in concurrent program proving. There are still many things that can be
improved. For instance, there may be better ways of formulating the constraints
within prompts to prevent the AI to go out of bounds. Specifications could be
improved as well to make the proving process smoother. Finally, better tooling
as well as additional helper context (proper skill) could also improve the
proof writing.
