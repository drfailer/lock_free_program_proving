From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import invariants mono_nat.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import lang proofmode notation.

(* Queue layout: [mutex, head_block, head_idx, tail_block, tail_idx, capacity]
   Block layout: [next, block_id, slot_0_val, slot_0_state, slot_1_val, ...]
   Slot state:   0 = Empty, 1 = Writing, 2 = Valid *)

Definition CHUNKED_QUEUE_BLOCK_SIZE : Z := 64.
Definition BLOCK_ALLOC_SIZE : Z := (2 + 2 * CHUNKED_QUEUE_BLOCK_SIZE)%Z.

Definition acquire : val :=
  rec: "loop" "l" :=
    if: CAS "l" #0 #1 then #() else "loop" "l".

Definition release : val :=
  λ: "l", "l" <- #0.

Definition chunked_queue_init : val :=
  λ: "queue",
    let: "block" := AllocN #BLOCK_ALLOC_SIZE #0 in
    "block" +ₗ #0 <- "block";;
    "block" +ₗ #1 <- #0;;
    "queue" +ₗ #1 <- "block";;
    "queue" +ₗ #2 <- #0;;
    "queue" +ₗ #3 <- "block";;
    "queue" +ₗ #4 <- #0;;
    "queue" +ₗ #5 <- #CHUNKED_QUEUE_BLOCK_SIZE;;
    #().

Definition chunked_queue_push_grow_loop : val :=
  rec: "grow" "queue" "tail" "block_id" :=
    if: !("tail" +ₗ #1) < "block_id"
    then
      let: "new_block" := AllocN #BLOCK_ALLOC_SIZE #0 in
      "new_block" +ₗ #1 <- !("tail" +ₗ #1) + #1;;
      "new_block" +ₗ #0 <- !("tail" +ₗ #0);;
      "tail" +ₗ #0 <- "new_block";;
      "queue" +ₗ #5 <- !("queue" +ₗ #5) + #CHUNKED_QUEUE_BLOCK_SIZE;;
      "grow" "queue" "new_block" "block_id"
    else "tail".

Definition chunked_queue_push_find_block : val :=
  rec: "find" "cursor" "start" "block_id" "slot_idx" "data" :=
    if: !("cursor" +ₗ #1) = "block_id"
    then
      let: "slot" := "cursor" +ₗ (#2 + #2 * "slot_idx") in
      "slot" +ₗ #1 <- #1;;
      "slot" +ₗ #1 <- #2;;
      "slot" <- "data";;
      SOME #()
    else
      let: "next" := !("cursor" +ₗ #0) in
      if: "next" = "start"
      then NONE
      else "find" "next" "start" "block_id" "slot_idx" "data".

Definition chunked_queue_push_find_block_loop : val :=
  rec: "loop" "queue" "block_id" "slot_idx" "data" :=
    let: "cursor" := !("queue" +ₗ #3) in
    let: "res" := chunked_queue_push_find_block "cursor" "cursor" "block_id" "slot_idx" "data" in
    match: "res" with
      NONE => "loop" "queue" "block_id" "slot_idx" "data"
    | SOME <> => #()
    end.

Definition chunked_queue_push : val :=
  λ: "queue" "data",
    let: "pos" := FAA ("queue" +ₗ #4) #1 in
    let: "block_id" := "pos" `quot` #CHUNKED_QUEUE_BLOCK_SIZE in
    let: "slot_idx" := "pos" `rem` #CHUNKED_QUEUE_BLOCK_SIZE in
    (if: ("slot_idx" = #0) && (#0 < "pos")
    then
      acquire ("queue" +ₗ #0);;
      let: "tail" := !("queue" +ₗ #3) in
      let: "new_tail" := chunked_queue_push_grow_loop "queue" "tail" "block_id" in
      "queue" +ₗ #3 <- "new_tail";;
      release ("queue" +ₗ #0)
    else #());;
    chunked_queue_push_find_block_loop "queue" "block_id" "slot_idx" "data".

Definition chunked_queue_pop_cas_loop : val :=
  rec: "loop" "queue" :=
    let: "head" := !("queue" +ₗ #2) in
    let: "tail" := !("queue" +ₗ #4) in
    if: "tail" ≤ "head"
    then InjL #()
    else
      if: CAS ("queue" +ₗ #2) "head" ("head" + #1)
      then InjR "head"
      else "loop" "queue".

Definition chunked_queue_pop_advance_head_loop : val :=
  rec: "loop" "queue" "block_id" :=
    let: "old_head" := !("queue" +ₗ #1) in
    if: "block_id" ≤ !("old_head" +ₗ #1)
    then #()
    else
      let: "next" := !("old_head" +ₗ #0) in
      CAS ("queue" +ₗ #1) "old_head" "next";;
      "loop" "queue" "block_id".

Definition chunked_queue_pop_find_slot : val :=
  rec: "find" "cursor" "start" "block_id" "slot_idx" :=
    if: !("cursor" +ₗ #1) = "block_id"
    then
      let: "slot" := "cursor" +ₗ (#2 + #2 * "slot_idx") in
      (rec: "wait" <> :=
        if: !("slot" +ₗ #1) = #2
        then #()
        else "wait" #()) #();;
      let: "data" := !"slot" in
      "slot" +ₗ #1 <- #0;;
      SOME "data"
    else
      let: "next" := !("cursor" +ₗ #0) in
      if: "next" = "start"
      then NONE
      else "find" "next" "start" "block_id" "slot_idx".

Definition chunked_queue_pop_find_slot_loop : val :=
  rec: "loop" "queue" "block_id" "slot_idx" :=
    let: "cursor" := !("queue" +ₗ #1) in
    let: "res" := chunked_queue_pop_find_slot "cursor" "cursor" "block_id" "slot_idx" in
    match: "res" with
      NONE => "loop" "queue" "block_id" "slot_idx"
    | SOME "data" => "data"
    end.

Definition chunked_queue_pop : val :=
  λ: "queue",
    match: chunked_queue_pop_cas_loop "queue" with
      InjL <> => (InjL #(), #false)
    | InjR "pos" =>
      let: "block_id" := "pos" `quot` #CHUNKED_QUEUE_BLOCK_SIZE in
      let: "slot_idx" := "pos" `rem` #CHUNKED_QUEUE_BLOCK_SIZE in
      (if: ("slot_idx" = #0) && (#0 < "pos")
      then chunked_queue_pop_advance_head_loop "queue" "block_id"
      else #());;
      let: "data" := chunked_queue_pop_find_slot_loop "queue" "block_id" "slot_idx" in
      (InjR "data", #true)
    end.

Definition chunked_queue_destroy_loop : val :=
  rec: "loop" "cursor" "head" :=
    if: "cursor" = "head"
    then #()
    else
      let: "next" := !("cursor" +ₗ #0) in
      Free #BLOCK_ALLOC_SIZE "cursor";;
      "loop" "next" "head".

Definition chunked_queue_destroy : val :=
  λ: "queue",
    let: "head" := !("queue" +ₗ #1) in
    if: "head" = #0
    then #()
    else
      let: "cursor" := !("head" +ₗ #0) in
      chunked_queue_destroy_loop "cursor" "head";;
      Free #BLOCK_ALLOC_SIZE "head";;
      "queue" +ₗ #1 <- #0;;
      "queue" +ₗ #3 <- #0;;
      #().

Definition chunked_queue_size : val :=
  λ: "queue",
    let: "tail" := !("queue" +ₗ #4) in
    let: "head" := !("queue" +ₗ #2) in
    if: "head" < "tail"
    then "tail" - "head"
    else #0.

(* ================================================================ *)
(*                         SPECIFICATION                            *)
(* ================================================================ *)

(** Ghost State:
    - mono_list (leibnizO val): authoritative append-only list L
      representing the logical history of all pushed elements.
    - mono_nat (×2): monotonic counters for head_idx and tail_idx. *)

Class chunked_queueG Σ := ChunkedQueueG {
  cq_mono_listG :: inG Σ (mono_listR (leibnizO val));
  cq_mono_natG :: mono_natG Σ;
}.

Definition chunked_queueΣ : gFunctors :=
  #[ GFunctor (mono_listR (leibnizO val)); mono_natΣ ].

Global Instance subG_chunked_queueΣ {Σ} :
  subG chunked_queueΣ Σ → chunked_queueG Σ.
Proof. solve_inG. Qed.

Record queue_name := QueueName {
  γ_list : gname;
  γ_head : gname;
  γ_tail : gname;
}.

Section spec.
  Context `{!heapGS Σ, !chunked_queueG Σ}.
  Implicit Types (γ : queue_name) (q : loc).

  Let queueN := nroot .@ "chunked_queue".
  Let BS := Z.to_nat CHUNKED_QUEUE_BLOCK_SIZE.

  (* -------------------------------------------------------------- *)
  (*  @inv(Slot Ownership)                                           *)
  (*  Empty (0):   invariant owns state AND value.                   *)
  (*               No thread may read/write value.                   *)
  (*  Writing (1): producer holds exclusive value permission.         *)
  (*               Invariant owns state only.                        *)
  (*  Valid (2):   producer relinquished permission.                  *)
  (*               Invariant owns state AND value ↦ data.            *)
  (*               data matches ghost list at position pos.          *)
  (* -------------------------------------------------------------- *)
  Definition slot_inv (L : list val) (pos : nat) (slot_loc : loc) : iProp Σ :=
    ∃ (state : Z), (slot_loc +ₗ 1) ↦ #state ∗
    ( (⌜state = 0⌝ ∗ slot_loc ↦ #0)
    ∨ (⌜state = 1⌝)
    ∨ (⌜state = 2⌝ ∗ ∃ v, slot_loc ↦ v ∗ ⌜L !! pos = Some v⌝) ).

  (* -------------------------------------------------------------- *)
  (*  Block: [next, block_id, slot_0_val, slot_0_state, ...]         *)
  (* -------------------------------------------------------------- *)
  Definition is_block (L : list val) (b : loc) (bid : Z)
      (next : loc) : iProp Σ :=
    (b +ₗ 0) ↦ #next ∗
    (b +ₗ 1) ↦ #bid ∗
    [∗ list] i ∈ seq 0 BS,
      slot_inv L (Z.to_nat bid * BS + i) (b +ₗ (2 + 2 * Z.of_nat i)).

  (* -------------------------------------------------------------- *)
  (*  Circular block chain                                           *)
  (* -------------------------------------------------------------- *)
  Definition block_next (blocks : list (loc * Z)) (i : nat)
      (first : loc) : loc :=
    match blocks !! (S i) with
    | Some (b, _) => b
    | None => first
    end.

  Definition is_block_chain (L : list val) (blocks : list (loc * Z))
      (first : loc) : iProp Σ :=
    [∗ list] i↦blk ∈ blocks,
      let '(b, bid) := blk in
      is_block L b bid (block_next blocks i first).

  (* -------------------------------------------------------------- *)
  (*  @inv(Queue State)                                              *)
  (*  Ghost state: authoritative append-only list L.                 *)
  (*  tail_idx = |L|, monotonically increasing ticket counter.       *)
  (*  head_idx ≤ tail_idx, monotonically increasing pop counter.     *)
  (* -------------------------------------------------------------- *)
  Definition queue_inv_inner (γ : queue_name) (q : loc) : iProp Σ :=
    ∃ (L : list val) (h t : nat)
      (lock_val : Z) (hb tb : loc) (cap : Z)
      (blocks : list (loc * Z)),
    own γ.(γ_list) (●ML{# (1/2)%Qp} L) ∗
    mono_nat_auth_own γ.(γ_head) (1/2)%Qp h ∗
    mono_nat_auth_own γ.(γ_tail) (1/2)%Qp t ∗
    ⌜t = length L⌝ ∗
    ⌜h ≤ t⌝ ∗
    (q +ₗ 0) ↦ #lock_val ∗ ⌜lock_val = 0 ∨ lock_val = 1⌝ ∗
    (q +ₗ 1) ↦ #hb ∗
    (q +ₗ 2) ↦ #(Z.of_nat h) ∗
    (q +ₗ 3) ↦ #tb ∗
    (q +ₗ 4) ↦ #(Z.of_nat t) ∗
    (q +ₗ 5) ↦ #cap ∗
    ⌜blocks ≠ []⌝ ∗
    ⌜cap = (Z.of_nat (length blocks) * CHUNKED_QUEUE_BLOCK_SIZE)%Z⌝ ∗
    ⌜(Z.of_nat t ≤ cap)%Z⌝ ∗
    ⌜hb ∈ fst <$> blocks⌝ ∗
    ⌜tb ∈ fst <$> blocks⌝ ∗
    match blocks with
    | [] => True
    | (first, _) :: _ => is_block_chain L blocks first
    end.

  Definition is_queue (γ : queue_name) (q : loc) : iProp Σ :=
    inv queueN (queue_inv_inner γ q).

  Global Instance is_queue_persistent γ q : Persistent (is_queue γ q).
  Proof. apply _. Qed.

  (* -------------------------------------------------------------- *)
  (*  Client-facing abstract queue content                           *)
  (* -------------------------------------------------------------- *)
  Definition queue_content (γ : queue_name)
      (L : list val) (h : nat) : iProp Σ :=
    own γ.(γ_list) (●ML{# (1/2)%Qp} L) ∗
    mono_nat_auth_own γ.(γ_head) (1/2)%Qp h ∗
    mono_nat_auth_own γ.(γ_tail) (1/2)%Qp (length L).

  (* -------------------------------------------------------------- *)
  (*  Logically Atomic Specifications                                *)
  (* -------------------------------------------------------------- *)

  Lemma chunked_queue_init_spec (q : loc) :
    {{{ q ↦∗ replicate 6 #0 }}}
      chunked_queue_init #q
    {{{ γ, RET #(); is_queue γ q ∗ queue_content γ [] 0 }}}.
  Proof. Admitted.

  (** @spec: logically atomic push that appends data to L.
      @linpoint: FAA on queue.tail_idx. *)
  Lemma chunked_queue_push_spec γ (q : loc) (v : val) :
    is_queue γ q -∗
    <<{ ∀∀ (L : list val) (h : nat), queue_content γ L h }>>
      chunked_queue_push #q v @ ↑queueN
    <<{ queue_content γ (L ++ [v]) h | RET #() }>>.
  Proof. Admitted.

  (** @spec: logically atomic pop that removes head from L.
      @linpoint: CAS on queue.head_idx. *)
  Lemma chunked_queue_pop_spec γ (q : loc) :
    is_queue γ q -∗
    <<{ ∀∀ (L : list val) (h : nat), queue_content γ L h }>>
      chunked_queue_pop #q @ ↑queueN
    <<{ ∃∃ (w : val) (ok : bool),
        (⌜ok = true⌝ ∗
          ∃ d, ⌜w = InjRV d⌝ ∗ ⌜L !! h = Some d⌝ ∗
               queue_content γ L (S h)) ∨
        (⌜ok = false⌝ ∗
          ⌜w = InjLV #()⌝ ∗ ⌜h = length L⌝ ∗
          queue_content γ L h)
      | RET (w, #ok)%V }>>.
  Proof. Admitted.

End spec.
