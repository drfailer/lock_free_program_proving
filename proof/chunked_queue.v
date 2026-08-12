From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import invariants mono_nat ghost_map ghost_var.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import lang proofmode notation.

(* Queue layout: [mutex, head_block, head_idx, tail_block, tail_idx, capacity]
   Block layout: [next, block_id, empty_count, slot_0_val, slot_0_state, slot_1_val, ...]
   Slot state:   0 = Empty, 1 = Writing, 2 = Valid *)

Definition CHUNKED_QUEUE_BLOCK_SIZE : Z := 64.
Definition BLOCK_ALLOC_SIZE : Z := (3 + 2 * CHUNKED_QUEUE_BLOCK_SIZE)%Z.

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
      let: "next" := !("tail" +ₗ #0) in
      let: "ec" := !("next" +ₗ #2) in
      if: "ec" = #CHUNKED_QUEUE_BLOCK_SIZE
      then
        "next" +ₗ #2 <- #0;;
        "next" +ₗ #1 <- !("tail" +ₗ #1) + #1;;
        "grow" "queue" "next" "block_id"
      else
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
      let: "slot" := "cursor" +ₗ (#3 + #2 * "slot_idx") in
      "slot" +ₗ #1 <- #1;;
      "slot" <- "data";;
      "slot" +ₗ #1 <- #2;;
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
      let: "slot" := "cursor" +ₗ (#3 + #2 * "slot_idx") in
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
  cq_mono_list_locG :: inG Σ (mono_listR (leibnizO loc));
  cq_mono_natG :: mono_natG Σ;
  cq_ghost_mapG :: ghost_mapG Σ nat ();
  cq_ghost_varG :: ghost_varG Σ (nat * loc)%type;
}.

Definition chunked_queueΣ : gFunctors :=
  #[ GFunctor (mono_listR (leibnizO val));
     GFunctor (mono_listR (leibnizO loc));
     mono_natΣ;
     ghost_mapΣ nat ();
     ghost_varΣ (nat * loc)%type ].

Global Instance subG_chunked_queueΣ {Σ} :
  subG chunked_queueΣ Σ → chunked_queueG Σ.
Proof. solve_inG. Qed.

Record queue_name := QueueName {
  γ_list : gname;
  γ_blocks : gname;
  γ_head : gname;
  γ_tail : gname;
  γ_claims : gname;
  γ_writes : gname;
  γ_lock : gname;
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
  Definition slot_inv (γc γw : gname) (L : list val) (pos : nat) (slot_loc : loc) : iProp Σ :=
    ∃ (state : Z), (slot_loc +ₗ 1) ↦ #state ∗
    ( (⌜state = 0⌝ ∗ ∃ w, slot_loc ↦ w)
    ∨ (⌜state = 1⌝ ∗ pos ↪[γw] ())
    ∨ (⌜state = 2⌝ ∗ ∃ v, slot_loc ↦ v ∗ ⌜L !! pos = Some v⌝ ∗ pos ↪[γw] ())
    ∨ (⌜state = 2⌝ ∗ pos ↪[γc] () ∗ pos ↪[γw] ()) ).

  (* -------------------------------------------------------------- *)
  (*  Block: [next, block_id, empty_count, slot_0_val, slot_0_state, ...]  *)
  (* -------------------------------------------------------------- *)
  Definition is_block (γc γw : gname) (L : list val) (b : loc) (bid : Z)
      (next : loc) : iProp Σ :=
    ∃ (ec : Z),
    (b +ₗ 0) ↦ #next ∗
    (b +ₗ 1) ↦ #bid ∗
    (b +ₗ 2) ↦ #ec ∗
    [∗ list] i ∈ seq 0 BS,
      slot_inv γc γw L (Z.to_nat bid * BS + i) (b +ₗ (3 + 2 * Z.of_nat i)).

  (* -------------------------------------------------------------- *)
  (*  Circular block chain                                           *)
  (* -------------------------------------------------------------- *)
  Definition block_next (blocks : list (loc * Z)) (i : nat)
      (first : loc) : loc :=
    match blocks !! (S i) with
    | Some (b, _) => b
    | None => first
    end.

  Definition is_block_chain (γc γw : gname) (L : list val) (blocks : list (loc * Z))
      (first : loc) : iProp Σ :=
    [∗ list] i↦blk ∈ blocks,
      let '(b, bid) := blk in
      is_block γc γw L b bid (block_next blocks i first).

  (* -------------------------------------------------------------- *)
  (*  @inv(Queue State)                                              *)
  (*  Ghost state: authoritative append-only list L.                 *)
  (*  tail_idx = |L|, monotonically increasing ticket counter.       *)
  (*  head_idx ≤ tail_idx, monotonically increasing pop counter.     *)
  (* -------------------------------------------------------------- *)
  Definition queue_inv_inner (γ : queue_name) (q : loc) : iProp Σ :=
    ∃ (L : list val) (h t : nat)
      (lock_val : Z) (hb tb : loc) (cap : Z)
      (blocks : list (loc * Z))
      (hi ti : nat) (C W : gmap nat ()),
    own γ.(γ_list) (●ML{# (1/2)%Qp} L) ∗
    own γ.(γ_blocks) (●ML (blocks.*1)) ∗
    mono_nat_auth_own γ.(γ_head) (1/2)%Qp h ∗
    mono_nat_auth_own γ.(γ_tail) (1/2)%Qp t ∗
    ghost_map_auth γ.(γ_claims) 1 C ∗
    ghost_map_auth γ.(γ_writes) 1 W ∗
    ⌜t = length L⌝ ∗
    ⌜h ≤ t⌝ ∗
    (q +ₗ 0) ↦ #lock_val ∗ ⌜lock_val = 0 ∨ lock_val = 1⌝ ∗
    (q +ₗ 1) ↦ #hb ∗
    (q +ₗ 2) ↦ #(Z.of_nat h) ∗
    (q +ₗ 3) ↦ #tb ∗
    (q +ₗ 4) ↦ #(Z.of_nat t) ∗
    (q +ₗ 5) ↦ #cap ∗
    ⌜blocks ≠ []⌝ ∗
    ⌜blocks !! hi = Some (hb, Z.of_nat hi)⌝ ∗
    ⌜∃ ci, blocks !! ci = Some (tb, Z.of_nat ci)⌝ ∗
    ⌜if decide (lock_val = 0) then blocks !! ti = Some (tb, Z.of_nat ti) else True⌝ ∗
    ⌜if decide (lock_val = 0) then ti = length blocks - 1 else True⌝ ∗
    ⌜∀ i blk, blocks !! i = Some blk → snd blk = Z.of_nat i⌝ ∗
    ⌜∀ k : nat, h ≤ k → C !! k = None⌝ ∗
    ⌜∀ k : nat, t ≤ k → W !! k = None⌝ ∗
    (if decide (lock_val = 0) then ghost_var γ.(γ_lock) (1/2) (length blocks, tb) else True) ∗
    ghost_var γ.(γ_lock) (1/2) (length blocks, tb) ∗
    match blocks with
    | [] => True
    | (first, _) :: _ => is_block_chain γ.(γ_claims) γ.(γ_writes) L blocks first
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
  Proof.
    iIntros (Φ) "Hq HΦ".
    unfold chunked_queue_init. wp_pures.
    iDestruct (array_cons with "Hq") as "[Hq0 Hq]".
    iDestruct (array_cons with "Hq") as "[Hq1 Hq]".
    iDestruct (array_cons with "Hq") as "[Hq2 Hq]".
    iDestruct (array_cons with "Hq") as "[Hq3 Hq]".
    iDestruct (array_cons with "Hq") as "[Hq4 Hq]".
    iDestruct (array_cons with "Hq") as "[Hq5 Hq]".
    iClear "Hq".
    replace (q +ₗ 1 +ₗ 1) with (q +ₗ 2) in * by (rewrite Loc.add_assoc; done).
    replace (q +ₗ 2 +ₗ 1) with (q +ₗ 3) in * by (rewrite Loc.add_assoc; done).
    replace (q +ₗ 3 +ₗ 1) with (q +ₗ 4) in * by (rewrite Loc.add_assoc; done).
    replace (q +ₗ 4 +ₗ 1) with (q +ₗ 5) in * by (rewrite Loc.add_assoc; done).
    wp_alloc block as "Hblock".
    { unfold BLOCK_ALLOC_SIZE, CHUNKED_QUEUE_BLOCK_SIZE. lia. }
    wp_pures.
    change (Z.to_nat BLOCK_ALLOC_SIZE) with 131%nat.
    iDestruct (array_cons with "Hblock") as "[Hb0 Hblock]".
    iDestruct (array_cons with "Hblock") as "[Hb1 Hblock]".
    iDestruct (array_cons with "Hblock") as "[Hb2 Hblock]".
    rewrite Loc.add_0. wp_store. wp_pures.
    wp_store. wp_pures. wp_store. wp_pures. wp_store. wp_pures.
    wp_store. wp_pures. wp_store. wp_pures. wp_store.
    replace (block +ₗ 1 +ₗ 1) with (block +ₗ 2) in * by (rewrite Loc.add_assoc; done).
    replace (block +ₗ 2 +ₗ 1) with (block +ₗ 3) in * by (rewrite Loc.add_assoc; done).
    iMod (own_alloc (●ML{# (1/2)%Qp} ([] : list (leibnizO val)) ⋅ ●ML{# (1/2)%Qp} ([] : list (leibnizO val)))) as (γ_list) "[Hauth1 Hauth2]".
    { rewrite -mono_list_auth_dfrac_op. rewrite dfrac_op_own Qp.half_half. apply mono_list_auth_valid. }
    iMod (own_alloc (●ML{# 1%Qp} ([block] : list (leibnizO loc)))) as (γ_blocks) "Hblk_auth".
    { apply mono_list_auth_valid. }
    iMod (mono_nat_own_alloc 0) as (γ_head) "[Hhead_auth _]".
    iMod (mono_nat_own_alloc 0) as (γ_tail) "[Htail_auth _]".
    iMod (ghost_map_alloc_empty) as (γ_claims) "Hclaims".
    iMod (ghost_map_alloc_empty) as (γ_writes) "Hwrites".
    iMod (ghost_var_alloc (1%nat, block)) as (γ_lk) "Hgv_lk".
    iDestruct "Hgv_lk" as "[Hgv_lk1 Hgv_lk2]".
    iDestruct "Hhead_auth" as "[Hhead1 Hhead2]".
    iDestruct "Htail_auth" as "[Htail1 Htail2]".
    set (γ := QueueName γ_list γ_blocks γ_head γ_tail γ_claims γ_writes γ_lk).
    iApply ("HΦ" $! γ). iSplitR "Hauth2 Hhead2 Htail2".
    2:{ unfold queue_content. simpl. iFrame. iModIntro. done. }
    iApply inv_alloc. iNext. unfold queue_inv_inner.
    iExists [], 0%nat, 0%nat, 0%Z, block, block, CHUNKED_QUEUE_BLOCK_SIZE, [(block, 0%Z)], 0%nat, 0%nat, ∅, ∅.
    simpl. iFrame "Hauth1 Hblk_auth Hhead1 Htail1 Hclaims Hwrites".
    rewrite Loc.add_0. iFrame "Hq0 Hq1 Hq2 Hq3 Hq4 Hq5".
    iSplit; first done.
    iSplit; first (iPureIntro; lia).
    iSplit; first (iPureIntro; left; done).
    iSplit; first done.
    iSplit; first (iPureIntro; reflexivity).
    iSplit; first (iPureIntro; exists 0%nat; reflexivity).
    iSplit; first (iPureIntro; reflexivity).
    iSplit; first (iPureIntro; simpl; lia).
    iSplit; first (iPureIntro; intros i blk Hi; destruct i as [|[|]]; simpl in Hi; [inversion Hi; done|discriminate|discriminate]).
    iSplit; first (iPureIntro; intros k _; apply lookup_empty).
    iSplit; first (iPureIntro; intros k _; apply lookup_empty).
    simpl. iFrame "Hgv_lk1 Hgv_lk2".
    unfold is_block_chain. simpl. rewrite right_id. unfold is_block. rewrite Loc.add_0.
    iExists 0. iFrame "Hb0 Hb1 Hb2".
    change BS with 64%nat. change (Z.to_nat 0) with 0%nat.
    iAssert (∀ (n : nat), ⌜(n ≤ 64)%nat⌝ -∗
      (block +ₗ (3 + 2 * Z.of_nat (64 - n))) ↦∗ replicate (2 * n) #0 -∗
      [∗ list] i ∈ seq (64 - n) n, slot_inv γ_claims γ_writes [] (0 * 64 + i)%nat (block +ₗ (3 + 2 * Z.of_nat i)))%I as "Hind".
    { iIntros (n).
      iInduction n as [|n'] "IH".
      - iIntros "% Hblock". done.
      - iIntros (Hn) "Hblock".
        replace (64 - S n')%nat with (64 - n' - 1)%nat by lia.
        replace (2 * S n')%nat with (2 + 2 * n')%nat by lia.
        rewrite replicate_add.
        iDestruct (array_app with "Hblock") as "[Hpair Hrest]".
        simpl.
        iDestruct (array_cons with "Hpair") as "[Hval Hpair]".
        iDestruct (array_cons with "Hpair") as "[Hstate _]".
        iSplitL "Hval Hstate".
        { unfold slot_inv. iExists 0.
          replace (block +ₗ (3 + 2 * (64 - n' - 1)%nat) +ₗ 1) with (block +ₗ (3 + 2 * Z.of_nat (64 - n' - 1)) +ₗ 1) by (f_equal; lia).
          iFrame "Hstate". iLeft. iSplit; [done|]. iExists #0. iExact "Hval". }
        replace (S (64 - n' - 1)) with (64 - n')%nat by lia.
        iApply ("IH" with "[%] [Hrest]").
        { lia. }
        replace (block +ₗ (3 + 2 * (64 - n' - 1)%nat) +ₗ 2%nat) with (block +ₗ (3 + 2 * Z.of_nat (64 - n'))) by (rewrite Loc.add_assoc; f_equal; lia).
        replace (n' + (n' + 0))%nat with (2 * n')%nat by lia.
        done. }
    iSpecialize ("Hind" $! 64%nat with "[%] [Hblock]").
    { lia. }
    { change (3 + 2 * Z.of_nat (64 - 64))%Z with 3%Z. done. }
    replace (64 - 64)%nat with 0%nat by lia. done.
  Defined.

  (* ---------------------------------------------------------------- *)
  (*  Push helpers                                                     *)
  (* ---------------------------------------------------------------- *)

  Lemma block_next_app_lt blocks new_entry first i :
    S i < length blocks →
    block_next (blocks ++ [new_entry]) i first = block_next blocks i first.
  Proof.
    intros Hlt. unfold block_next.
    rewrite lookup_app_l; [done|lia].
  Qed.

  Lemma block_next_app_last blocks new_blk new_bid first :
    blocks ≠ [] →
    block_next (blocks ++ [(new_blk, new_bid)]) (length blocks - 1) first = new_blk.
  Proof.
    intros Hne. unfold block_next.
    destruct blocks as [|hd tl]; [done|].
    rewrite lookup_app_r; [|simpl; lia].
    replace (S (length (hd :: tl) - 1) - length (hd :: tl))%nat with 0%nat by (simpl; lia).
    simpl. done.
  Qed.

  Lemma block_next_app_new blocks new_entry first :
    block_next (blocks ++ [new_entry]) (length blocks) first = first.
  Proof.
    unfold block_next.
    rewrite lookup_app_r; [|lia].
    replace (S (length blocks) - length blocks)%nat with 1%nat by lia.
    simpl. done.
  Qed.

  Lemma is_block_chain_grow γc γw L blocks (first last_blk new_blk : loc)
      last_bid new_bid :
    blocks ≠ [] →
    last blocks = Some (last_blk, last_bid) →
    is_block_chain γc γw L blocks first -∗
    (last_blk +ₗ 0) ↦ #new_blk -∗
    is_block γc γw L new_blk new_bid first -∗
    is_block_chain γc γw L (blocks ++ [(new_blk, new_bid)]) first.
  Proof.
    iIntros (Hne Hlast) "Hchain Hn_new Hblk_new".
    assert (∃ blocks_init, blocks = blocks_init ++ [(last_blk, last_bid)] ∧
      length blocks_init = length blocks - 1) as [blocks_init [Hblocks_eq Hlen_init]].
    { exists (take (length blocks - 1) blocks). split.
      - rewrite last_lookup in Hlast.
        replace (Init.Nat.pred (length blocks)) with (length blocks - 1)%nat in Hlast by lia.
        pose proof (take_drop_middle blocks (length blocks - 1) (last_blk, last_bid) Hlast) as Hmid.
        assert (drop (S (length blocks - 1)) blocks = []) as Hdrop.
        { apply nil_length_inv. rewrite length_drop.
          destruct blocks; [done|simpl; lia]. }
        rewrite Hdrop in Hmid. symmetry. exact Hmid.
      - rewrite length_take. destruct blocks; [done|simpl; lia]. }
    subst blocks.
    set (old_blocks := blocks_init ++ [(last_blk, last_bid)]).
    set (new_blocks := old_blocks ++ [(new_blk, new_bid)]).
    unfold is_block_chain.
    (* Split old chain using big_sepL_snoc *)
    rewrite /old_blocks big_sepL_snoc.
    iDestruct "Hchain" as "[Hchain_init Hblk_last]".
    simpl.
    iDestruct "Hblk_last" as (ec_last) "(Hn_old & Hbid_last & Hec_last & Hsl_last)".
    (* Build new chain using big_sepL_snoc twice *)
    rewrite /new_blocks big_sepL_snoc.
    iSplitL "Hchain_init Hn_new Hbid_last Hec_last Hsl_last".
    - rewrite /old_blocks big_sepL_snoc.
      iSplitL "Hchain_init".
      + iApply (big_sepL_impl with "Hchain_init").
        iIntros "!>" (k [b bid] Hk) "Hblk".
        assert (k < length blocks_init) as Hk_bound.
        { apply lookup_lt_Some in Hk. done. }
        assert (S k < length old_blocks) as Hsk.
        { rewrite /old_blocks length_app. simpl. lia. }
        rewrite (block_next_app_lt old_blocks); [|exact Hsk].
        done.
      + simpl.
        replace (length blocks_init) with (length old_blocks - 1)%nat
          by (rewrite /old_blocks length_app; simpl; lia).
        rewrite (block_next_app_last old_blocks); [|rewrite /old_blocks; destruct blocks_init; discriminate].
        unfold is_block. iExists ec_last. iFrame.
    - simpl.
      rewrite (block_next_app_new old_blocks).
      done.
  Qed.

  Lemma push_grow_loop_spec γ (q tail tb0 : loc) (block_id : Z)
      (blocks0 : list (loc * Z)) (nblk0 : nat)
      (Htail_in : ∃ ti0, blocks0 !! ti0 = Some (tail, Z.of_nat ti0) ∧ S ti0 = length blocks0)
      (Hnblk0 : nblk0 = length blocks0) :
    {{{ is_queue γ q ∗
        own γ.(γ_blocks) (◯ML (blocks0.*1 : list (leibnizO loc))) ∗
        ghost_var γ.(γ_lock) (1/2) (nblk0, tb0) }}}
      chunked_queue_push_grow_loop #q #tail #block_id
    {{{ (new_tail : loc) (blocks : list (loc * Z)), RET #new_tail;
        own γ.(γ_blocks) (◯ML (blocks.*1 : list (leibnizO loc))) ∗
        ⌜∃ nt, blocks !! nt = Some (new_tail, Z.of_nat nt) ∧ S nt = length blocks⌝ ∗
        ghost_var γ.(γ_lock) (1/2) (length blocks, tb0) }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hlb0 & Hgvtok) HΦ".
    destruct Htail_in as [ti0 [Hti0 Hti0_last]].
    iLöb as "IH" forall (tail blocks0 nblk0 ti0 Hti0 Hti0_last Hnblk0) "Hlb0".
    unfold chunked_queue_push_grow_loop. wp_rec. wp_pures.
    (* Load tail.block_id for comparison *)
    wp_bind (! _)%E.
    iInv "Hinv" as (L1 h1 t1 lv1 hb1 tb1 cap1 blocks1 hi1 ti1 C1 W1)
      ">(Ha1 & Hba1 & Hh1 & Ht1 & Hcl1 & Hwr1 & %Ht1 & %Hht1 & Hlk1 & %Hlv1 &
         Hhb1 & Hhl1 & Htb1 & Htl1 & Hcap1 &
         %Hne1 & %Hhi1 & %Htb_in1 & %Hti1 & %Htilast1 & %Hbids1 & %Hcfresh1 & %Hwfresh1 & Hgvlk1 & Hgv1 & Hch1)".
    iDestruct (own_valid_2 with "Hba1 Hlb0") as %[_ Hpfx1]%mono_list_both_dfrac_valid_L.
    assert (blocks1.*1 !! ti0 = Some tail) as Htail_in1.
    { eapply prefix_lookup_Some; [|exact Hpfx1].
      rewrite list_lookup_fmap. rewrite Hti0. done. }
    assert (∃ bid1, blocks1 !! ti0 = Some (tail, bid1)) as [bid1 Htail_blk1].
    { rewrite list_lookup_fmap in Htail_in1.
      destruct (blocks1 !! ti0) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
    assert (bid1 = Z.of_nat ti0) as -> by (apply (Hbids1 _ _ Htail_blk1)).
    destruct blocks1 as [|[first1 fb1] blocks1']; first done.
    iDestruct (big_sepL_lookup_acc with "Hch1") as "[Hblk1 Hrest1]"; first exact Htail_blk1.
    iDestruct "Hblk1" as (ec1) "(Hn1 & Hbid1 & Hec1 & Hsl1)".
    wp_load.
    iDestruct ("Hrest1" with "[Hn1 Hbid1 Hec1 Hsl1]") as "Hch1"; first (iExists ec1; iFrame).
    iDestruct (own_mono _ _ (◯ML (((first1,fb1)::blocks1').*1 : list (leibnizO loc))) with "Hba1") as "#Hlb1".
    { apply mono_list_included. }
    iDestruct (ghost_var_agree with "Hgvtok Hgv1") as %Hnblk1.
    injection Hnblk1 as Hnblk1 _.
    iModIntro. iSplitR "HΦ Hgvtok".
    { iNext. iExists L1,h1,t1,lv1,hb1,tb1,cap1,((first1,fb1)::blocks1'),hi1,ti1,C1,W1. iFrame. done. }
    wp_pures.
    (* Branch on tail.block_id < block_id *)
    destruct (decide (Z.of_nat ti0 < block_id)%Z) as [Hlt|Hge].
    - (* Need to grow *)
      rewrite bool_decide_eq_true_2; last lia.
      wp_pures.

      (* ====== 2 loads for the reuse/allocate check ====== *)
      (* Load 1: next = !(tail +ₗ 0) *)
      wp_bind (! #(tail +ₗ 0))%E.
      iInv "Hinv" as (La ha ta lva hba tba capa blocksa hia tia Ca Wa)
        ">(Haa & Hbaa & Hha & Hta' & Hcla & Hwra & %Hta & %Hhta & Hlka & %Hlva &
           Hhba & Hhla & Htba & Htla & Hcapa &
           %Hnea & %Hhia & %Htb_ina & %Htia & %Htilasta & %Hbidsa & %Hcfresha & %Hwfresha & Hgvlka & Hgva & Hcha)".
      iDestruct (own_valid_2 with "Hbaa Hlb1") as %[_ Hpfxa]%mono_list_both_dfrac_valid_L.
      assert (blocksa.*1 !! ti0 = Some tail) as Htail_fmapa.
      { eapply prefix_lookup_Some; [|exact Hpfxa].
        rewrite list_lookup_fmap. simpl.
        rewrite (list_lookup_fmap fst ((first1,fb1)::blocks1') ti0) in Htail_in1.
        exact Htail_in1. }
      assert (blocksa !! ti0 = Some (tail, Z.of_nat ti0)) as Htail_blka.
      { rewrite list_lookup_fmap in Htail_fmapa.
        destruct (blocksa !! ti0) as [[? z]|] eqn:Heq; [|done].
        simpl in Htail_fmapa. injection Htail_fmapa as ->.
        assert (z = Z.of_nat ti0) as -> by (apply (Hbidsa _ _ Heq)). done. }
      destruct blocksa as [|[firsta fba] blocksa']; first done.
      iDestruct (big_sepL_lookup_acc with "Hcha") as "[Hblka Hresta]"; first exact Htail_blka.
      iDestruct "Hblka" as (eca) "(Hna & Hbida & Heca & Hsla)".
      wp_load.
      set (tail_next := block_next ((firsta, fba) :: blocksa') ti0 firsta).
      iDestruct ("Hresta" with "[Hna Hbida Heca Hsla]") as "Hcha"; first (iExists eca; iFrame).
      iDestruct (ghost_var_agree with "Hgvtok Hgva") as %Hnblka.
      injection Hnblka as Hnblka_len Hnblka_tb.
      assert (S ti0 = length ((firsta, fba) :: blocksa')) as Hlena.
      { simpl in *. lia. }
      assert (tail_next = firsta) as Htail_next_eq.
      { unfold tail_next, block_next.
        rewrite lookup_ge_None_2; [done|lia]. }
      iDestruct (own_mono _ _ (◯ML (((firsta,fba)::blocksa').*1 : list (leibnizO loc))) with "Hbaa") as "#Hlba".
      { apply mono_list_included. }
      iModIntro. iSplitR "HΦ Hgvtok".
      { iNext. iExists La,ha,ta,lva,hba,tba,capa,((firsta,fba)::blocksa'),hia,tia,Ca,Wa. iFrame. done. }
      wp_pures.

      (* Load 2: ec = !(tail_next +ₗ 2) = !(firsta +ₗ 2) *)
      wp_bind (! #(tail_next +ₗ 2))%E.
      rewrite Htail_next_eq.
      iInv "Hinv" as (Lb hb0 tb0' lvb hbb tbb capb blocksb hib tib Cb Wb)
        ">(Hab & Hbab & Hhb & Htb' & Hclb & Hwrb & %Htb_eq & %Hhtb & Hlkb & %Hlvb &
           Hhbb & Hhlb & Htbb & Htlb & Hcapb &
           %Hneb & %Hhib & %Htb_inb & %Htib & %Htilastb & %Hbidsb & %Hcfreshb & %Hwfreshb & Hgvlkb & Hgvb & Hchb)".
      iDestruct (own_valid_2 with "Hbab Hlba") as %[_ Hpfxb]%mono_list_both_dfrac_valid_L.
      assert (blocksb.*1 !! 0 = Some firsta) as Hfirst_fmapb.
      { eapply prefix_lookup_Some; [|exact Hpfxb]. done. }
      assert (∃ fbb, blocksb !! 0 = Some (firsta, fbb)) as [fbb Hfirst_blkb].
      { rewrite list_lookup_fmap in Hfirst_fmapb.
        destruct (blocksb !! 0) as [[? z]|] eqn:Heq; [|done].
        simpl in Hfirst_fmapb. injection Hfirst_fmapb as ->. eauto. }
      assert (fbb = Z.of_nat 0) as -> by (apply (Hbidsb _ _ Hfirst_blkb)).
      destruct blocksb as [|[firstb fbb'] blocksb']; first done.
      simpl in Hfirst_blkb. injection Hfirst_blkb as -> ->.
      iDestruct (big_sepL_lookup_acc with "Hchb") as "[Hblkb Hrestb]"; first by apply lookup_cons_Some; left.
      iDestruct "Hblkb" as (ecb) "(Hnb & Hbidb & Hecb & Hslb)".
      wp_load.
      iDestruct ("Hrestb" with "[Hnb Hbidb Hecb Hslb]") as "Hchb"; first (iExists ecb; iFrame).
      iModIntro. iSplitR "HΦ Hgvtok".
      { iNext. iExists Lb,hb0,tb0',lvb,hbb,tbb,capb,((firsta,0%Z)::blocksb'),hib,tib,Cb,Wb. iFrame. done. }
      wp_pures.

      (* Clear stale hypotheses *)
      clear Hta Hhta Hlva Hnea Hhia Htb_ina Htia Htilasta Hbidsa Hcfresha Hwfresha
            Htail_fmapa Htail_blka Hnblka_len Hnblka_tb Hlena Hpfxa.
      clear La ha ta lva hba tba capa hia tia Ca Wa.
      clear Htb_eq Hhtb Hlvb Hneb Hhib Htb_inb Htib Htilastb Hbidsb Hcfreshb Hwfreshb Hpfxb Hfirst_fmapb.
      clear Lb hb0 tb0' lvb hbb tbb capb blocksb' hib tib Cb Wb.

      (* Branch: ec = BS? *)
      destruct (decide (ecb = CHUNKED_QUEUE_BLOCK_SIZE)%Z) as [Hec_full|Hec_not_full].
      + (* ec = BS → reuse branch (deferred) *)
        rewrite bool_decide_eq_true_2; last (subst ecb; done).
        wp_pures.
        admit.

      + (* ec ≠ BS → allocate branch *)
        rewrite bool_decide_eq_false_2; last (intro Habs; apply Hec_not_full; injection Habs; lia).
        wp_pures.

        (* AllocN new block *)
        wp_alloc new_block as "Hnew".
        { unfold BLOCK_ALLOC_SIZE, CHUNKED_QUEUE_BLOCK_SIZE. lia. }
        wp_pures.
        change (Z.to_nat BLOCK_ALLOC_SIZE) with 131%nat.
        iDestruct (array_cons with "Hnew") as "[Hnb0 Hnew]".
        iDestruct (array_cons with "Hnew") as "[Hnb1 Hnew]".
        iDestruct (array_cons with "Hnew") as "[Hnb2 Hnew_slots]".
        replace (new_block +ₗ 1 +ₗ 1) with (new_block +ₗ 2) in * by (rewrite Loc.add_assoc; done).
        replace (new_block +ₗ 2 +ₗ 1) with (new_block +ₗ 3) in * by (rewrite Loc.add_assoc; done).
        (* Load tail.block_id for "new_block +ₗ 1 <- !(tail +ₗ 1) + 1" *)
        wp_bind (! _)%E.
        iInv "Hinv" as (L2 h2 t2 lv2 hb2 tb2 cap2 blocks2 hi2 ti2 C2 W2)
          ">(Ha2 & Hba2 & Hh2 & Ht2 & Hcl2 & Hwr2 & %Ht2 & %Hht2 & Hlk2 & %Hlv2 &
             Hhb2 & Hhl2 & Htb2 & Htl2 & Hcap2 &
             %Hne2 & %Hhi2 & %Htb_in2 & %Hti2 & %Htilast2 & %Hbids2 & %Hcfresh2 & %Hwfresh2 & Hgvlk2 & Hgv2 & Hch2)".
        iDestruct (own_valid_2 with "Hba2 Hlb1") as %[_ Hpfx2]%mono_list_both_dfrac_valid_L.
        assert (blocks2.*1 !! ti0 = Some tail) as Htail_fmap2.
        { eapply prefix_lookup_Some; [|exact Hpfx2].
          rewrite list_lookup_fmap. simpl.
          rewrite (list_lookup_fmap fst ((first1,fb1)::blocks1') ti0) in Htail_in1.
          exact Htail_in1. }
        assert (blocks2 !! ti0 = Some (tail, Z.of_nat ti0)) as Htail_blk2.
        { rewrite list_lookup_fmap in Htail_fmap2.
          destruct (blocks2 !! ti0) as [[? z]|] eqn:Heq; [|done].
          simpl in Htail_fmap2. injection Htail_fmap2 as ->.
          assert (z = Z.of_nat ti0) as -> by (apply (Hbids2 _ _ Heq)). done. }
        destruct blocks2 as [|[first2 fb2] blocks2']; first done.
        iDestruct (big_sepL_lookup_acc with "Hch2") as "[Hblk2 Hrest2]"; first exact Htail_blk2.
        iDestruct "Hblk2" as (ec2) "(Hn2 & Hbid2 & Hec2 & Hsl2)".
        wp_load.
        iDestruct ("Hrest2" with "[Hn2 Hbid2 Hec2 Hsl2]") as "Hch2"; first (iExists ec2; iFrame).
        iModIntro. iSplitR "HΦ Hnb0 Hnb1 Hnb2 Hnew_slots Hgvtok".
        { iNext. iExists L2,h2,t2,lv2,hb2,tb2,cap2,((first2,fb2)::blocks2'),hi2,ti2,C2,W2. iFrame. done. }
        wp_pures.
        (* Store new_block.block_id = ti0 + 1 *)
        wp_store. wp_pures.
        (* Load tail.next for "new_block +ₗ 0 <- !(tail +ₗ 0)" *)
        wp_bind (! _)%E.
        iInv "Hinv" as (L3 h3 t3 lv3 hb3 tb3 cap3 blocks3 hi3 ti3 C3 W3)
          ">(Ha3 & Hba3 & Hh3 & Ht3 & Hcl3 & Hwr3 & %Ht3 & %Hht3 & Hlk3 & %Hlv3 &
             Hhb3 & Hhl3 & Htb3 & Htl3 & Hcap3 &
             %Hne3 & %Hhi3 & %Htb_in3 & %Hti3 & %Htilast3 & %Hbids3 & %Hcfresh3 & %Hwfresh3 & Hgvlk3 & Hgv3 & Hch3)".
        iDestruct (own_valid_2 with "Hba3 Hlb1") as %[_ Hpfx3]%mono_list_both_dfrac_valid_L.
        assert (blocks3.*1 !! ti0 = Some tail) as Htail_fmap3.
        { eapply prefix_lookup_Some; [|exact Hpfx3].
          rewrite list_lookup_fmap. simpl.
          rewrite (list_lookup_fmap fst ((first1,fb1)::blocks1') ti0) in Htail_in1.
          exact Htail_in1. }
        assert (blocks3 !! ti0 = Some (tail, Z.of_nat ti0)) as Htail_blk3.
        { rewrite list_lookup_fmap in Htail_fmap3.
          destruct (blocks3 !! ti0) as [[? z]|] eqn:Heq; [|done].
          simpl in Htail_fmap3. injection Htail_fmap3 as ->.
          assert (z = Z.of_nat ti0) as -> by (apply (Hbids3 _ _ Heq)). done. }
        destruct blocks3 as [|[first3 fb3] blocks3']; first done.
        iDestruct (big_sepL_lookup_acc with "Hch3") as "[Hblk3 Hrest3]"; first exact Htail_blk3.
        iDestruct "Hblk3" as (ec3) "(Hn3 & Hbid3 & Hec3 & Hsl3)".
        wp_load.
        set (tail_next2 := block_next ((first3, fb3) :: blocks3') ti0 first3).
        iDestruct ("Hrest3" with "[Hn3 Hbid3 Hec3 Hsl3]") as "Hch3"; first (iExists ec3; iFrame).
        iDestruct (ghost_var_agree with "Hgvtok Hgv3") as %Hnblk3.
        injection Hnblk3 as Hnblk3_len Hnblk3_tb.
        assert (S ti0 = length ((first3, fb3) :: blocks3')) as Hlen3.
        { simpl in *. lia. }
        iModIntro. iSplitR "HΦ Hnb0 Hnb1 Hnb2 Hnew_slots Hgvtok".
        { iNext. iExists L3,h3,t3,lv3,hb3,tb3,cap3,((first3,fb3)::blocks3'),hi3,ti3,C3,W3. iFrame. done. }
        wp_pures.
        (* Store new_block.next = tail_next2 *)
        iAssert ((new_block +ₗ 0) ↦ #0)%I with "[Hnb0]" as "Hnb0".
        { rewrite Loc.add_0. iFrame. }
        wp_store. wp_pures.
        (* Now store tail.next <- new_block: modifies the invariant *)
        wp_bind (_ <- _)%E.
        iInv "Hinv" as (L4 h4 t4 lv4 hb4 tb4 cap4 blocks4 hi4 ti4 C4 W4)
          ">(Ha4 & Hba4 & Hh4 & Ht4 & Hcl4 & Hwr4 & %Ht4 & %Hht4 & Hlk4 & %Hlv4 &
             Hhb4 & Hhl4 & Htb4 & Htl4 & Hcap4 &
             %Hne4 & %Hhi4 & %Htb_in4 & %Hti4 & %Htilast4 & %Hbids4 & %Hcfresh4 & %Hwfresh4 & Hgvlk4 & Hgv4 & Hch4)".
        iDestruct (own_valid_2 with "Hba4 Hlb1") as %[_ Hpfx4]%mono_list_both_dfrac_valid_L.
        assert (blocks4.*1 !! ti0 = Some tail) as Htail_fmap4.
        { eapply prefix_lookup_Some; [|exact Hpfx4].
          rewrite list_lookup_fmap. simpl.
          rewrite (list_lookup_fmap fst ((first1,fb1)::blocks1') ti0) in Htail_in1.
          exact Htail_in1. }
        assert (blocks4 !! ti0 = Some (tail, Z.of_nat ti0)) as Htail_blk4.
        { rewrite list_lookup_fmap in Htail_fmap4.
          destruct (blocks4 !! ti0) as [[? z]|] eqn:Heq; [|done].
          simpl in Htail_fmap4. injection Htail_fmap4 as ->.
          assert (z = Z.of_nat ti0) as -> by (apply (Hbids4 _ _ Heq)). done. }
        destruct blocks4 as [|[first4 fb4] blocks4']; first done.
        iDestruct (ghost_var_agree with "Hgvtok Hgv4") as %Hnblk4.
        injection Hnblk4 as Hnblk4 Htb_eq4.
        assert (ti0 = length blocks4') as Hti0_len.
        { simpl in Hnblk4. lia. }
        assert (∃ blocks_init,
          (first4, fb4) :: blocks4' = blocks_init ++ [(tail, Z.of_nat ti0)] ∧
          length blocks_init = ti0) as [blocks_init [Hblocks_split Hlen_init]].
        { exists (take ti0 ((first4, fb4) :: blocks4')).
          split.
          - pose proof (take_drop_middle ((first4, fb4) :: blocks4') ti0 (tail, Z.of_nat ti0) Htail_blk4) as Hsplit.
            assert (drop (S ti0) ((first4, fb4) :: blocks4') = []) as Hdrop_nil.
            { apply nil_length_inv. rewrite length_drop. simpl. lia. }
            rewrite Hdrop_nil in Hsplit. symmetry. exact Hsplit.
          - rewrite length_take. simpl. lia. }
        rewrite Hblocks_split.
        unfold is_block_chain.
        rewrite big_sepL_app.
        iDestruct "Hch4" as "[Hch_init Hch_last]".
        simpl. rewrite Hlen_init.
        iDestruct "Hch_last" as "[Hblk_tail _]".
        unfold is_block. unfold block_next.
        rewrite lookup_app_r; [|lia].
        replace (S ti0 - length blocks_init)%nat with 1%nat by lia.
        simpl.
        iDestruct "Hblk_tail" as (ec4) "(Hn4 & Hbid4 & Hec4 & Hsl4)".
        wp_store.
        change (Z.to_nat BLOCK_ALLOC_SIZE) with 131%nat.
        iAssert (∀ (n : nat), ⌜(n ≤ BS)%nat⌝ -∗
          (new_block +ₗ (3 + 2 * Z.of_nat (BS - n))) ↦∗ replicate (2 * n) #0 -∗
          [∗ list] i ∈ seq (BS - n) n,
            slot_inv γ.(γ_claims) γ.(γ_writes) L4
              (Z.to_nat (Z.of_nat ti0 + 1) * BS + i)%nat
              (new_block +ₗ (3 + 2 * Z.of_nat i)))%I as "Hslot_ind".
        { iIntros (n).
          iInduction n as [|n'] "IH_sl".
          - iIntros "% _". done.
          - iIntros (Hn) "Hblock".
            replace (BS - S n')%nat with (BS - n' - 1)%nat by lia.
            replace (2 * S n')%nat with (2 + 2 * n')%nat by lia.
            rewrite replicate_add.
            iDestruct (array_app with "Hblock") as "[Hpair Hrest_sl]".
            simpl.
            iDestruct (array_cons with "Hpair") as "[Hval Hpair]".
            iDestruct (array_cons with "Hpair") as "[Hstate _]".
            iSplitL "Hval Hstate".
            { unfold slot_inv. iExists 0.
              replace (new_block +ₗ (3 + 2 * (BS - n' - 1)%nat) +ₗ 1) with
                (new_block +ₗ (3 + 2 * Z.of_nat (BS - n' - 1)) +ₗ 1) by (f_equal; lia).
              iFrame "Hstate". iLeft. iSplit; [done|]. iExists #0. iExact "Hval". }
            replace (S (BS - n' - 1)) with (BS - n')%nat by lia.
            iApply ("IH_sl" with "[%] [Hrest_sl]").
            { lia. }
            replace (new_block +ₗ (3 + 2 * (BS - n' - 1)%nat) +ₗ 2%nat) with
              (new_block +ₗ (3 + 2 * Z.of_nat (BS - n'))) by (rewrite Loc.add_assoc; f_equal; lia).
            replace (n' + (n' + 0))%nat with (2 * n')%nat by lia.
            done. }
        iSpecialize ("Hslot_ind" $! BS with "[%] [Hnew_slots]").
        { lia. }
        { change BS with 64%nat. change (3 + 2 * Z.of_nat (64 - 64))%Z with 3%Z. done. }
        replace (BS - BS)%nat with 0%nat by lia.
        assert (first3 = first1) as Hfirst3.
        { assert (((first3, fb3) :: blocks3').*1 !! 0 = Some first1) as Hf3.
          { eapply prefix_lookup_Some; [|exact Hpfx3]. simpl. done. }
          simpl in Hf3. congruence. }
        assert (first4 = first1) as Hfirst4.
        { assert (((first4, fb4) :: blocks4').*1 !! 0 = Some first1) as Hf4.
          { eapply prefix_lookup_Some; [|exact Hpfx4]. simpl. done. }
          simpl in Hf4. congruence. }
        assert (tail_next2 = first4) as Htail_next2.
        { unfold tail_next2, block_next.
          rewrite lookup_ge_None_2; [|lia]. congruence. }
        set (new_blocks := ((first4,fb4)::blocks4') ++ [(new_block, Z.of_nat (S ti0))]).
        iAssert (is_block_chain γ.(γ_claims) γ.(γ_writes) L4 new_blocks first4)%I
          with "[Hch_init Hn4 Hbid4 Hec4 Hsl4 Hnb0 Hnb1 Hnb2 Hslot_ind]" as "Hch_new".
        { unfold is_block_chain, new_blocks.
          rewrite Hblocks_split big_sepL_app.
          iSplitL "Hch_init Hn4 Hbid4 Hec4 Hsl4".
          - rewrite big_sepL_snoc.
            iSplitL "Hch_init".
            + iApply (big_sepL_impl with "Hch_init").
              iIntros "!>" (k [b bid] Hk) "Hblk".
              apply lookup_lt_Some in Hk.
              unfold block_next.
              rewrite (lookup_app_l (blocks_init ++ [(tail, Z.of_nat ti0)]));
                [|rewrite length_app /=; lia].
              done.
            + simpl. unfold block_next.
              rewrite (lookup_app_r (blocks_init ++ [(tail, Z.of_nat ti0)]));
                [|rewrite length_app /=; lia].
              rewrite length_app /=.
              replace (S (length blocks_init) - (length blocks_init + 1))%nat with 0%nat by lia. simpl.
              unfold is_block. iExists ec4. iFrame.
          - rewrite big_sepL_cons big_sepL_nil.
            rewrite right_id.
            unfold is_block, block_next.
            rewrite lookup_ge_None_2; [|rewrite !length_app /=; lia].
            change BS with 64%nat.
            replace (Z.of_nat ti0 + 1)%Z with (Z.of_nat (S ti0)) by lia.
            replace (Z.to_nat (Z.of_nat (S ti0))) with (S ti0) by lia.
            iEval (rewrite Htail_next2 Hfirst4) in "Hnb0".
            iExists 0. iFrame "Hnb0 Hnb1 Hnb2 Hslot_ind". }
        assert (new_blocks.*1 = ((first4, fb4) :: blocks4').*1 ++ [new_block]) as Hnb_fmap.
        { rewrite /new_blocks fmap_app. simpl. done. }
        assert (((first4, fb4) :: blocks4').*1 `prefix_of` new_blocks.*1) as Hpfx_new.
        { rewrite Hnb_fmap. apply prefix_app_r. done. }
        iMod (own_update _ _ (●ML (new_blocks.*1 : list (leibnizO loc))) with "Hba4") as "Hba4".
        { apply mono_list_update.
          rewrite /new_blocks Hblocks_split !fmap_app /=. apply prefix_app_r. done. }
        iDestruct (own_mono _ _ (◯ML (new_blocks.*1 : list (leibnizO loc))) with "Hba4") as "#Hlb_new".
        { apply mono_list_included. }
        assert (length new_blocks = S (S (length blocks4'))) as Hlen_new.
        { rewrite /new_blocks length_app. simpl. lia. }
        iMod (ghost_var_update_halves (length new_blocks, tb0) with "Hgvtok Hgv4") as "[Hgvtok Hgv4]".
        destruct Hlv4 as [Hlv4_zero|Hlv4_one].
        { subst lv4. simpl.
          iDestruct (ghost_var_agree with "Hgvlk4 Hgv4") as %Habs.
          injection Habs as Habs_len _.
          iExFalso. iPureIntro.
          assert (length (blocks_init ++ [(tail, Z.of_nat ti0)]) = S ti0) as Hlen_old
            by (rewrite length_app /=; lia).
          rewrite Hlen_old in Habs_len.
          rewrite /new_blocks length_app /= in Habs_len. lia. }
        replace lv4 with 1%Z by lia.
        iModIntro.
        iSplitR "HΦ Hgvtok".
        { iNext.
          assert (new_blocks ≠ []) as Hne_new.
          { rewrite /new_blocks. destruct blocks4'; discriminate. }
          assert (∀ i blk, new_blocks !! i = Some blk → snd blk = Z.of_nat i) as Hbids_new.
          { intros i blk. rewrite /new_blocks lookup_app.
            destruct (((first4, fb4) :: blocks4') !! i) eqn:Heq.
            - intros [= <-]. apply (Hbids4 _ _ Heq).
            - apply lookup_ge_None_1 in Heq.
              simpl. destruct (i - S (length blocks4'))%nat as [|[|]] eqn:Heq2; simpl.
              + intros [= <-]. simpl in *. lia.
              + discriminate.
              + discriminate. }
          assert (new_blocks !! hi4 = Some (hb4, Z.of_nat hi4)) as Hhi_lookup.
          { rewrite /new_blocks lookup_app_l; [exact Hhi4|apply lookup_lt_Some in Hhi4; done]. }
          assert (∃ ci, new_blocks !! ci = Some (tb4, Z.of_nat ci)) as Htb_in_new.
          { destruct Htb_in4 as [ci4 Hci4].
            exists ci4. rewrite /new_blocks lookup_app_l; [exact Hci4|apply lookup_lt_Some in Hci4; done]. }
          iExists L4,h4,t4,1%Z,hb4,tb4,cap4,new_blocks,hi4,(S ti0),C4,W4.
          rewrite /new_blocks. simpl.
          iEval (rewrite Htb_eq4) in "Hgv4".
          iFrame "Ha4 Hba4 Hh4 Ht4 Hcl4 Hwr4 Hlk4 Hhb4 Hhl4 Htb4 Htl4 Hcap4 Hgv4 Hch_new".
          repeat iSplit; try (iPureIntro; first [done | lia | right; done | exact Hhi_lookup | exact Htb_in_new | exact Hbids_new]). }
        wp_pures.
        (* Load capacity: !(queue +ₗ 5) *)
        wp_bind (! _)%E.
        iInv "Hinv" as (L5 h5 t5 lv5 hb5 tb5 cap5 blocks5 hi5 ti5 C5 W5)
          ">(Ha5 & Hba5 & Hh5 & Ht5 & Hcl5 & Hwr5 & %Ht5 & %Hht5 & Hlk5 & %Hlv5 &
             Hhb5 & Hhl5 & Htb5 & Htl5 & Hcap5 &
             %Hne5 & %Hhi5 & %Htb_in5 & %Hti5 & %Htilast5 & %Hbids5 & %Hcfresh5 & %Hwfresh5 & Hgvlk5 & Hgv5 & Hch5)".
        wp_load. iModIntro.
        iSplitR "HΦ Hgvtok".
        { iNext. iExists L5,h5,t5,lv5,hb5,tb5,cap5,blocks5,hi5,ti5,C5,W5. iFrame. done. }
        wp_pures.
        (* Store new capacity: queue +ₗ 5 <- cap5 + BLOCK_SIZE *)
        wp_bind (_ <- _)%E.
        iInv "Hinv" as (L6 h6 t6 lv6 hb6 tb6 cap6 blocks6 hi6 ti6 C6 W6)
          ">(Ha6 & Hba6 & Hh6 & Ht6 & Hcl6 & Hwr6 & %Ht6 & %Hht6 & Hlk6 & %Hlv6 &
             Hhb6 & Hhl6 & Htb6 & Htl6 & Hcap6 &
             %Hne6 & %Hhi6 & %Htb_in6 & %Hti6 & %Htilast6 & %Hbids6 & %Hcfresh6 & %Hwfresh6 & Hgvlk6 & Hgv6 & Hch6)".
        wp_store.
        destruct Hlv6 as [Hlv6_zero|Hlv6_one].
        { subst lv6. simpl.
          iDestruct (ghost_var_agree with "Hgvtok Hgv6") as %Hgv6_eq.
          iCombine "Hgv6 Hgvlk6" as "Hgv_full".
          iDestruct (ghost_var_valid_2 with "Hgvtok Hgv_full") as %[Hfrac _].
          exfalso. rewrite Qp.add_comm in Hfrac. by apply Qp.not_add_le_l in Hfrac. }
        replace lv6 with 1%Z by lia.
        iModIntro.
        iSplitR "HΦ Hgvtok".
        { iNext. iExists L6,h6,t6,1%Z,hb6,tb6,(cap5 + CHUNKED_QUEUE_BLOCK_SIZE)%Z,blocks6,hi6,ti6,C6,W6.
          simpl. iFrame. repeat iSplit; try (iPureIntro; first [done | lia]). }
        (* Recurse via IH *)
        change ((rec: "grow" "queue" "tail" "block_id" :=
         if: ! ("tail" +ₗ #1) < "block_id"
         then let: "next" := ! ("tail" +ₗ #0) in
              let: "ec" := ! ("next" +ₗ #2) in
              if: "ec" = #CHUNKED_QUEUE_BLOCK_SIZE
              then "next" +ₗ #2 <- #0;;
                   "next" +ₗ #1 <- ! ("tail" +ₗ #1) + #1;;
                   "grow" "queue" "next" "block_id"
              else let: "new_block" := AllocN #BLOCK_ALLOC_SIZE #0 in
                   "new_block" +ₗ #1 <- ! ("tail" +ₗ #1) + #1;;
                   "new_block" +ₗ #0 <- ! ("tail" +ₗ #0);;
                   "tail" +ₗ #0 <- "new_block";;
                   "queue" +ₗ #5 <- ! ("queue" +ₗ #5) + #CHUNKED_QUEUE_BLOCK_SIZE;;
                   "grow" "queue" "new_block" "block_id"
         else "tail")%V) with chunked_queue_push_grow_loop.
        wp_seq.
        iApply ("IH" $! new_block new_blocks (length new_blocks) (S ti0)
          with "[%] [%] [%] [Hgvtok] HΦ [Hlb_new]").
        * rewrite /new_blocks lookup_app_r; [|simpl; lia].
          rewrite Hti0_len Nat.sub_diag /=. done.
        * rewrite /new_blocks length_app. simpl. lia.
        * done.
        * done.
        * done.

    - (* No growth needed, return tail *)
      rewrite bool_decide_eq_false_2; last lia.
      wp_pures.
      iApply ("HΦ" $! tail ((first1,fb1)::blocks1')).
      rewrite Hnblk0 in Hnblk1.
      assert (length blocks0 = length ((first1, fb1) :: blocks1')) as Hlen_eq1.
      { apply prefix_length in Hpfx1. simpl in *. lia. }
      rewrite -Hlen_eq1 -Hnblk0. iFrame "Hlb1 Hgvtok".
      iPureIntro. exists ti0. split; [exact Htail_blk1|lia].
  Admitted.

  Lemma push_find_block_inner_spec γ (q : loc) (cursor start : loc)
      (pos : nat) (v : val) (L : list val) (blocks : list (loc * Z))
      (Hlookup : L !! pos = Some v)
      (Hcursor_in : ∃ ci, blocks.*1 !! ci = Some cursor) :
    {{{ is_queue γ q ∗
        own γ.(γ_list) (◯ML (L : list (leibnizO val))) ∗
        own γ.(γ_blocks) (◯ML (blocks.*1 : list (leibnizO loc))) ∗
        pos ↪[γ.(γ_writes)] () }}}
      chunked_queue_push_find_block #cursor #start
        #(Z.quot (Z.of_nat pos) CHUNKED_QUEUE_BLOCK_SIZE)
        #(Z.rem (Z.of_nat pos) CHUNKED_QUEUE_BLOCK_SIZE)
        v
    {{{ r, RET r;
        (⌜r = SOMEV #()⌝) ∨
        (⌜r = NONEV⌝ ∗ pos ↪[γ.(γ_writes)] ()) }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hlb_L & #Hlb_blocks & Hwtok) HΦ".
    destruct Hcursor_in as [ci Hci].
    set (block_id := Z.quot (Z.of_nat pos) CHUNKED_QUEUE_BLOCK_SIZE).
    set (slot_idx := Z.rem (Z.of_nat pos) CHUNKED_QUEUE_BLOCK_SIZE).
    unfold chunked_queue_push_find_block.

    assert (Z.to_nat slot_idx < BS) as Hsi_lt.
    { unfold slot_idx, BS, CHUNKED_QUEUE_BLOCK_SIZE.
      apply Z2Nat.inj_lt.
      - apply Z.rem_nonneg; lia.
      - lia.
      - apply Z.rem_bound_pos; lia. }
    assert (∀ c : nat, Z.of_nat c = block_id →
            pos = c * BS + Z.to_nat slot_idx) as Hdecomp_pre.
    { unfold block_id, slot_idx, BS, CHUNKED_QUEUE_BLOCK_SIZE. intros c Heq.
      assert (Hnn: (0 ≤ Z.rem (Z.of_nat pos) 64)%Z) by (apply Z.rem_nonneg; lia).
      assert (Hqr: (Z.of_nat pos = 64 * Z.quot (Z.of_nat pos) 64 + Z.rem (Z.of_nat pos) 64)%Z)
        by (apply Z.quot_rem'; lia).
      rewrite <- Heq in Hqr. lia. }

    iLöb as "IH" forall (cursor ci blocks Hci) "Hlb_blocks".
    wp_rec. wp_pures.
    (* Load cursor.block_id *)
    wp_bind (! _)%E.
    iInv "Hinv" as (Li hi ti lvi hbi tbi capi blocksi hii tii Ci Wi)
      ">(Hai & Hbai & Hhi & Hti & Hclaimsi & Hwritesi & %Hti_eq & %Hhti & Hlki & %Hlvi &
         Hhbi & Hhli & Htbi & Htli & Hcapi &
         %Hnei & %Hhii & %Htb_ini & %Htii & %Htilasti & %Hbidsi & %Hcfreshi & %Hwfreshi & Hgvlki & Hgvi & Hchi)".
    iDestruct (own_valid_2 with "Hbai Hlb_blocks") as %[_ Hpfx]%mono_list_both_dfrac_valid_L.
    assert (blocksi.*1 !! ci = Some cursor) as Hci_cur
      by (eapply prefix_lookup_Some; [exact Hci | exact Hpfx]).
    assert (∃ bid_i, blocksi !! ci = Some (cursor, bid_i)) as [bid_i Hcur_blk].
    { rewrite list_lookup_fmap in Hci_cur.
      destruct (blocksi !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
    assert (bid_i = Z.of_nat ci) as -> by (apply (Hbidsi _ _ Hcur_blk)).
    destruct blocksi as [|[firsti fbi] blocksi']; first done.
    iDestruct (big_sepL_lookup_acc with "Hchi") as "[Hblk Hrest]"; first exact Hcur_blk.
    iDestruct "Hblk" as (eci) "(Hnext & Hbid & Heci & Hslots)". wp_load.
    iDestruct ("Hrest" with "[Hnext Hbid Heci Hslots]") as "Hchi"; first (iExists eci; iFrame).
    iModIntro. iSplitR "Hwtok HΦ".
    { iNext. iExists Li,hi,ti,lvi,hbi,tbi,capi,((firsti,fbi)::blocksi'),hii,tii,Ci,Wi. iFrame. done. }
    wp_pures.
    destruct (decide (Z.of_nat ci = block_id)) as [Heq|Hne].
    - (* Correct block — do the three stores *)
      rewrite bool_decide_eq_true_2; last (subst block_id; rewrite Heq; done).
      wp_pures.
      pose proof (Hdecomp_pre ci Heq) as Hpos_decomp.
      set (si := Z.to_nat slot_idx).
      assert (seq 0 BS !! si = Some si) as Hseq by (apply lookup_seq; lia).
      (* Store 1: state ← 1 (Empty → Writing) *)
      wp_bind (_ <- _)%E.
      iInv "Hinv" as (Lw hw tw lvw hbw tbw capw blocksw hiw tiw Cw Ww)
        ">(Haw & Hbaw & Hhw & Htw & Hclaimsw & Hwritesw & %Htw & %Hhtw & Hlkw & %Hlvw &
           Hhbw & Hhlw & Htbw & Htlw & Hcapw &
           %Hnew & %Hhiw & %Htb_inw & %Htiw & %Htilastw & %Hbidsw & %Hcfw & %Hwfw & Hgvlkw & Hgvw & Hchw)".
      iDestruct (own_valid_2 with "Hbaw Hlb_blocks") as %[_ Hpfxw]%mono_list_both_dfrac_valid_L.
      assert (blocksw.*1 !! ci = Some cursor) as Hciw
        by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxw]).
      assert (∃ bw, blocksw !! ci = Some (cursor, bw)) as [bw Hblkw].
      { rewrite list_lookup_fmap in Hciw.
        destruct (blocksw !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
      assert (bw = Z.of_nat ci) as -> by (apply (Hbidsw _ _ Hblkw)).
      destruct blocksw as [|[fw fbw] blocksw']; first done.
      iDestruct (big_sepL_lookup_acc with "Hchw") as "[Hblk Hrest]"; first exact Hblkw.
      iDestruct "Hblk" as (ecw) "(Hn & Hb & Hecw & Hsl)".
      iDestruct (big_sepL_lookup_acc with "Hsl") as "[Hslot Hsl_rest]"; first exact Hseq.
      replace (Z.of_nat si) with slot_idx
        by (subst si; symmetry; apply Z2Nat.id; unfold slot_idx; apply Z.rem_nonneg; lia).
      assert (Hpos_eq : Z.to_nat (Z.of_nat ci) * BS + si = pos)
        by (rewrite Nat2Z.id; lia).
      iDestruct "Hslot" as (st) "[Hst Hcases]".
      iDestruct "Hcases" as "[H0|[H1|[H2|H3]]]".
      + (* Empty — expected case *)
        iDestruct "H0" as "[% Hv]". subst st. iDestruct "Hv" as (w) "Hv".
        wp_store.
        iDestruct ("Hsl_rest" with "[Hst Hwtok]") as "Hsl".
        { iExists 1. iFrame. iRight. iLeft. iSplit; [done|]. rewrite Hpos_eq. iFrame. }
        iDestruct ("Hrest" with "[Hn Hb Hecw Hsl]") as "Hch"; first (iExists ecw; iFrame).
        iModIntro. iSplitR "Hv HΦ".
        { iNext. iExists Lw,hw,tw,lvw,hbw,tbw,capw,((fw,fbw)::blocksw'),hiw,tiw,Cw,Ww. iFrame. done. }
        wp_pures.
        (* Store 2: slot ← data *)
        wp_store.
        wp_pures.
        (* Store 3: state ← 2 (Writing → Valid) *)
        wp_bind (_ <- _)%E.
        iInv "Hinv" as (Lr hr tr lvr hbr tbr capr blocksr hir tir Cr Wr)
          ">(Har & Hbar & Hhr & Htr & Hclr & Hwrr & %Htr & %Hhtr & Hlkr & %Hlvr &
             Hhbr & Hhlr & Htbr & Htlr & Hcpr &
             %Hner & %Hhir & %Htb_inr & %Htir & %Htilastr & %Hbidsr & %Hcfr & %Hwfr & Hgvlkr & Hgvr & Hchr)".
        iDestruct (own_valid_2 with "Hbar Hlb_blocks") as %[_ Hpfxr]%mono_list_both_dfrac_valid_L.
        assert (blocksr.*1 !! ci = Some cursor) as Hcir
          by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxr]).
        assert (∃ br, blocksr !! ci = Some (cursor, br)) as [br Hblkr].
        { rewrite list_lookup_fmap in Hcir.
          destruct (blocksr !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
        assert (br = Z.of_nat ci) as -> by (apply (Hbidsr _ _ Hblkr)).
        destruct blocksr as [|[fr fbr] blocksr']; first done.
        iDestruct (big_sepL_lookup_acc with "Hchr") as "[Hblk2 Hrest2]"; first exact Hblkr.
        iDestruct "Hblk2" as (ecr) "(Hn2 & Hb2 & Hecr & Hsl2)".
        iDestruct (big_sepL_lookup_acc with "Hsl2") as "[Hslot2 Hsl2_rest]"; first exact Hseq.
        replace (Z.of_nat si) with slot_idx
          by (subst si; symmetry; apply Z2Nat.id; unfold slot_idx; apply Z.rem_nonneg; lia).
        iDestruct "Hslot2" as (str) "[Hstr Hcr]".
        iDestruct "Hcr" as "[H0r|[H1r|[H2r|H3r]]]".
        ** (* Empty — contradiction, we deposited the write token *)
           iDestruct "H0r" as "[_ Hwr]". iDestruct "Hwr" as (w2) "Hwr".
           by iDestruct (pointsto_ne with "Hv Hwr") as %[].
        ** (* Writing — expected: we deposited the write token at state←1 *)
           iDestruct "H1r" as "[% Hwk]". subst str.
           wp_store.
           iDestruct (own_valid_2 with "Har Hlb_L") as %[_ HpL]%mono_list_both_dfrac_valid_L.
           assert (Lr !! pos = Some v) as HLr_lookup
             by (eapply prefix_lookup_Some; [exact Hlookup | exact HpL]).
           iDestruct ("Hsl2_rest" with "[Hstr Hv Hwk]") as "Hsl2".
           { iExists 2. iFrame. iRight. iRight. iLeft. iSplit; [done|].
             iExists v. rewrite Hpos_eq. iFrame. done. }
           iDestruct ("Hrest2" with "[Hn2 Hb2 Hecr Hsl2]") as "Hch2"; first (iExists ecr; iFrame).
           iModIntro. iSplitR "HΦ".
           { iNext. iExists Lr,hr,tr,lvr,hbr,tbr,capr,((fr,fbr)::blocksr'),hir,tir,Cr,Wr. iFrame. done. }
           wp_pures. iApply "HΦ". iLeft. done.
        ** (* Valid — contradiction: slot ↦ v' but we hold slot ↦ v *)
           iDestruct "H2r" as "[_ Hvr]". iDestruct "Hvr" as (v') "(Hvr & _ & _)".
           by iDestruct (pointsto_ne with "Hv Hvr") as %[].
        ** (* Claimed — store succeeds, close with Valid *)
           iDestruct "H3r" as "(% & Hclr2 & Hwkr)". subst str.
           wp_store.
           iDestruct (own_valid_2 with "Har Hlb_L") as %[_ HpLr]%mono_list_both_dfrac_valid_L.
           assert (Lr !! pos = Some v) as HLr_lookup2
             by (eapply prefix_lookup_Some; [exact Hlookup | exact HpLr]).
           iDestruct ("Hsl2_rest" with "[Hstr Hv Hwkr]") as "Hsl2".
           { iExists 2. iFrame. iRight. iRight. iLeft. iSplit; [done|].
             iExists v. rewrite Hpos_eq. iFrame. done. }
           iDestruct ("Hrest2" with "[Hn2 Hb2 Hecr Hsl2]") as "Hch2"; first (iExists ecr; iFrame).
           iModIntro. iSplitR "HΦ".
           { iNext. iExists Lr,hr,tr,lvr,hbr,tbr,capr,((fr,fbr)::blocksr'),hir,tir,Cr,Wr. iFrame. done. }
           wp_pures. iApply "HΦ". iLeft. done.
      + (* Writing — contradiction, we hold write token *)
        iDestruct "H1" as "[% Hw1]". subst st.
        iDestruct (ghost_map_elem_ne with "Hwtok Hw1") as %Hneq.
        exfalso. apply Hneq. lia.
      + (* Valid — contradiction, we hold write token *)
        iDestruct "H2" as "[% Hd]". subst st.
        iDestruct "Hd" as (v2) "(_ & _ & Hw2)".
        iDestruct (ghost_map_elem_ne with "Hwtok Hw2") as %Hneq.
        exfalso. apply Hneq. lia.
      + (* Claimed — contradiction, we hold write token *)
        iDestruct "H3" as "(% & _ & Hw3)". subst st.
        iDestruct (ghost_map_elem_ne with "Hwtok Hw3") as %Hneq.
        exfalso. apply Hneq. lia.
    - (* Wrong block — follow next pointer *)
      rewrite bool_decide_eq_false_2; last (intros Hinj; inversion Hinj; lia).
      wp_pures. wp_bind (! _)%E.
      iInv "Hinv" as (Ln hn tn lvn hbn tbn capn blocksn hin tin Cn Wn)
        ">(Han & Hban & Hhn & Htn & Hcln & Hwrn & %Htn & %Hhtn & Hlkn & %Hlvn &
           Hhbn & Hhln & Htbn & Htln & Hcpn &
           %Hnen & %Hhin & %Htb_inn & %Htin & %Htilastn & %Hbidsn & %Hcfn & %Hwfn & Hgvlkn & Hgvn & Hchn)".
      iDestruct (own_valid_2 with "Hban Hlb_blocks") as %[_ Hpfxn]%mono_list_both_dfrac_valid_L.
      assert (blocksn.*1 !! ci = Some cursor) as Hcin
        by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxn]).
      assert (∃ bn, blocksn !! ci = Some (cursor, bn)) as [bn Hblkn].
      { rewrite list_lookup_fmap in Hcin.
        destruct (blocksn !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
      assert (bn = Z.of_nat ci) as -> by (apply (Hbidsn _ _ Hblkn)).
      destruct blocksn as [|[fn fbn] blocksn']; first done.
      iDestruct (big_sepL_lookup_acc with "Hchn") as "[Hblk Hrest]"; first exact Hblkn.
      iDestruct "Hblk" as (ecn) "(Hn & Hb & Hecn & Hsl)".
      set (nxt := block_next ((fn,fbn)::blocksn') ci fn). wp_load.
      assert (∃ ni, ((fn,fbn)::blocksn').*1 !! ni = Some nxt) as [ni Hni].
      { unfold nxt, block_next.
        destruct (((fn,fbn)::blocksn') !! S ci) as [[? ?]|] eqn:?;
          [exists (S ci); rewrite list_lookup_fmap; rewrite Heqo; done | exists 0%nat; done]. }
      iDestruct (own_mono _ _ (◯ML (((fn,fbn)::blocksn').*1 : list (leibnizO loc))) with "Hban") as "#Hlbn".
      { apply mono_list_included. }
      iDestruct ("Hrest" with "[Hn Hb Hecn Hsl]") as "Hch"; first (iExists ecn; iFrame).
      iModIntro. iSplitR "Hwtok HΦ".
      { iNext. iExists Ln,hn,tn,lvn,hbn,tbn,capn,((fn,fbn)::blocksn'),hin,tin,Cn,Wn. iFrame. done. }
      wp_pures.
      destruct (decide (nxt = start)) as [->|Hns].
      + rewrite bool_decide_eq_true_2; last done.
        wp_pures. iApply "HΦ". iRight. iFrame. done.
      + rewrite bool_decide_eq_false_2; last (intros H; apply Hns; inversion H; done).
        wp_if_false. iApply ("IH" $! nxt ni ((fn,fbn)::blocksn') Hni with "Hwtok HΦ Hlbn").
  Defined.

  Lemma push_find_block_loop_spec γ (q : loc) (pos : nat) (v : val)
      (L : list val)
      (Hlookup : L !! pos = Some v) :
    {{{ is_queue γ q ∗
        own γ.(γ_list) (◯ML (L : list (leibnizO val))) ∗
        pos ↪[γ.(γ_writes)] () }}}
      chunked_queue_push_find_block_loop #q
        #(Z.quot (Z.of_nat pos) CHUNKED_QUEUE_BLOCK_SIZE)
        #(Z.rem (Z.of_nat pos) CHUNKED_QUEUE_BLOCK_SIZE)
        v
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hlb & Hwtok) HΦ".
    unfold chunked_queue_push_find_block_loop.
    iLöb as "IH" forall (Φ).
    wp_rec. wp_pures.
    wp_bind (! _)%E.
    iInv "Hinv" as (L' h t lock_val hb tb cap blocks hi ti C W')
      ">(Ha & Hba & Hh & Ht & Hcl & Hwl & %Ht_eq & %Hht & Hlk & %Hlv &
         Hhb & Hhl & Htb & Htl & Hcap &
         %Hne & %Hhi & %Htb_in & %Hti & %Htilast & %Hbids & %Hcfresh & %Hwfresh & Hgvlk & Hgv & Hch)".
    wp_load.
    iDestruct (own_mono _ _ (◯ML (blocks.*1 : list (leibnizO loc))) with "Hba") as "#Hlb_blocks".
    { apply mono_list_included. }
    pose proof Htb_in as [ci_tb Hci_tb].
    assert (∃ ci, blocks.*1 !! ci = Some tb) as Hcursor_in.
    { exists ci_tb. rewrite list_lookup_fmap Hci_tb. done. }
    iModIntro. iSplitR "HΦ Hwtok".
    { iNext. iExists L', h, t, lock_val, hb, tb, cap, blocks, hi, ti, C, W'.
      iFrame. done. }
    wp_pures.
    wp_bind (chunked_queue_push_find_block _ _ _ _ _)%E.
    wp_apply (push_find_block_inner_spec _ _ _ _ _ _ _ blocks
      with "[$Hinv $Hlb Hlb_blocks $Hwtok]"); [done|done|iFrame "#"|].
    iIntros (r) "[%Hsome | [%Hnone Hwtok]]".
    - subst r. wp_pures. by iApply "HΦ".
    - subst r. do 5 wp_pure _. iApply ("IH" with "Hwtok HΦ").
  Defined.

  (** @spec: logically atomic push that appends data to L.
      @linpoint: FAA on queue.tail_idx. *)
  Lemma chunked_queue_push_spec γ (q : loc) (v : val) :
    is_queue γ q -∗
    <<{ ∀∀ (L : list val) (h : nat), queue_content γ L h }>>
      chunked_queue_push #q v @ ↑queueN
    <<{ queue_content γ (L ++ [v]) h | RET #() }>>.
  Proof.
    iIntros "#Hinv" (Φ) "AU".
    unfold chunked_queue_push. wp_pures.
    (* === FAA linearization point === *)
    wp_bind (FAA _ _).
    iInv "Hinv" as (L h t lock_val hb tb cap blocks hi ti C W)
      ">(Hauth & Hblk_auth & Hhead & Htail & Hclaims & Hwrites & %Ht & %Hht & Hlock & %Hlock_val &
         Hhb & Hh & Htb & Htail_loc & Hcap &
         %Hblocks_ne & %Hhi & %Htb_in & %Hti & %Htilast & %Hbids & %Hcfresh & %Hwfresh & Hgvlk & Hgv & Hchain)".
    wp_faa.
    (* Open AU, agree on ghost state *)
    iMod "AU" as (L' h') "[Hcontent [_ Hclose]]".
    unfold queue_content.
    iDestruct "Hcontent" as "(Hauth2 & Hhead2 & Htail2)".
    iCombine "Hauth" "Hauth2" as "Hauth_full".
    iDestruct (own_valid with "Hauth_full") as %Hvalid.
    rewrite mono_list_auth_dfrac_op_valid in Hvalid.
    destruct Hvalid as [_ HL]. apply leibniz_equiv in HL. subst L'.
    iDestruct (mono_nat_auth_own_agree with "Hhead Hhead2") as %[_ Hheq].
    subst h'.
    iDestruct (mono_nat_auth_own_agree with "Htail Htail2") as %[_ Htlen].
    (* Update mono_list: L → L ++ [v] *)
    iMod (own_update with "Hauth_full") as "Hauth_full".
    { rewrite -mono_list_auth_dfrac_op dfrac_op_own Qp.half_half.
      apply (mono_list_update (L ++ [v])). apply prefix_app_r. done. }
    iDestruct "Hauth_full" as "[Hauth1 Hauth2]".
    (* Update mono_nat tail: length L → length (L ++ [v]) *)
    iCombine "Htail" "Htail2" as "Htail". rewrite Htlen.
    iDestruct "Htail" as "[Htail Htail2]".
    iCombine "Htail" "Htail2" as "Htail".
    iMod (mono_nat_own_update (length (L ++ [v])) with "Htail")
      as "[[Htail Htail2] _]".
    { rewrite app_length. simpl. lia. }
    (* Allocate write token for position (length L) *)
    assert (W !! (length L) = None) as Hwfresh_pos by (apply Hwfresh; lia).
    iMod (ghost_map_insert (length L) () with "Hwrites") as "[Hwrites Hwtok]".
    { exact Hwfresh_pos. }
    (* Snapshot mono_list fragment *)
    iDestruct (own_mono _ _ (◯ML ((L ++ [v]) : list (leibnizO val))) with "Hauth1") as "#Hlb_L".
    { apply mono_list_included. }
    (* Close AU *)
    iMod ("Hclose" with "[Hauth2 Hhead2 Htail2]") as "HΦ".
    { iFrame. }
    (* Close invariant *)
    iSplitR "HΦ Hwtok".
    { iModIntro. iNext. unfold queue_inv_inner.
      iExists (L ++ [v]), h, (length L + 1)%nat, lock_val, hb, tb,
        cap, blocks, hi, ti, C, (<[length L := ()]> W).
      replace (length L + 1)%Z with (Z.of_nat (length L + 1)%nat) in *
        by lia.
      rewrite app_length. simpl.
      iFrame "Hauth1 Hblk_auth Hhead Htail Hclaims Hwrites Hlock Hhb Hh Htb Htail_loc Hcap Hgvlk Hgv".
      repeat iSplit; try (iPureIntro; first [done | lia]).
      { iPureIntro. intros k Hk. rewrite lookup_insert_ne; [apply Hwfresh; lia | lia]. }
      destruct blocks as [|[first bid] blocks']; first done.
      iApply (big_sepL_mono with "Hchain").
      iIntros (k [b bid'] Hlookup) "Hblock".
      unfold is_block. iDestruct "Hblock" as (ec_k) "(Hnext & Hbid & Hec_k & Hslots)".
      iExists ec_k. iFrame "Hnext Hbid Hec_k".
      iApply (big_sepL_mono with "Hslots").
      iIntros (i x Hlookup2) "Hslot".
      unfold slot_inv. iDestruct "Hslot" as (state) "[Hstate Hcases]".
      iExists state. iFrame "Hstate".
      iDestruct "Hcases" as "[H | [H | [H | H]]]".
      - iLeft. done.
      - iRight. iLeft. done.
      - iRight. iRight. iLeft.
        iDestruct "H" as "[%Hs2 H]". iSplit; first done.
        iDestruct "H" as (w0) "(Hval & %HLw & Hw)".
        iExists w0. iFrame "Hval Hw".
        iPureIntro. apply lookup_app_l_Some. done.
      - iRight. iRight. iRight. done. }
    (* === Continuation: grow + find_block + slot writes === *)
    iModIntro. wp_pures.
    assert (Hlookup : (L ++ [v]) !! (length L) = Some v).
    { rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag. done. }
    (* Conditional grow: if (slot_idx = 0) && (0 < pos) *)
    case_bool_decide as Hslot.
    - injection Hslot as Hslot. wp_pures.
      case_bool_decide as Hpos_gt.
      + (* Need to grow: slot_idx = 0 and pos > 0 *)
        wp_pures.
        (* acquire lock *)
        wp_bind (acquire _)%E.
        iLöb as "IH_acq".
        unfold acquire. wp_rec. wp_pures.
        wp_bind (CmpXchg _ _ _)%E.
        iInv "Hinv" as (La ha ta lva hba tba capa blocksa hia tia Ca Wa)
          ">(Haa & Hbaa & Hha & Hta & Hcla & Hwra & %Hta_eq & %Hhta & Hlka & %Hlva &
             Hhba & Hhla & Htba & Htla & Hcapa &
             %Hnea & %Hhia & %Htb_ina & %Htia & %Htilasta & %Hbidsa & %Hcfresha & %Hwfresha & Hgvlka & Hgva & Hcha)".
        destruct Hlva as [Hlv0|Hlv1].
        ** (* lock = 0, CAS succeeds *)
           subst lva. simpl in Htia, Htilasta.
           wp_cmpxchg_suc. { done. }
           (* Save CAS-time facts before closing invariant *)
           iDestruct (own_mono _ _ (◯ML (blocksa.*1 : list (leibnizO loc))) with "Hbaa") as "#Hlb_a".
           { apply mono_list_included. }
           iModIntro.
           iSplitR "HΦ Hwtok Hgvlka".
           { iNext. iExists La,ha,ta,1%Z,hba,tba,capa,blocksa,hia,tia,Ca,Wa.
             iFrame. simpl. repeat iSplit; try (iPureIntro; first [done | lia | right; done]). }
           wp_pures.
           (* load tail pointer *)
           wp_bind (! _)%E.
           iInv "Hinv" as (Lb hb_ tb_ lvb hbb tbb capb blocksb hib tib Cb Wb)
             ">(Hab & Hbab & Hhb_ & Htb_ & Hclb & Hwrb & %Htb_eq & %Hhtb & Hlkb & %Hlvb &
                Hhbb & Hhlb & Htbb & Htlb & Hcapb &
                %Hneb & %Hhib_ & %Htb_inb & %Htib & %Htilastb & %Hbidsb & %Hcfreshb & %Hwfreshb & Hgvlkb & Hgvb & Hchb)".
           wp_load.
           iDestruct (own_mono _ _ (◯ML (blocksb.*1 : list (leibnizO loc))) with "Hbab") as "#Hlb_tail".
           { apply mono_list_included. }
           iDestruct (ghost_var_agree with "Hgvlka Hgvb") as %Hblk_eq_ab.
           injection Hblk_eq_ab as Hblk_len_eq Htb_eq_ab.
           (* Derive blocksa = blocksb using prefix + same length + bids *)
           iDestruct (own_valid_2 with "Hbab Hlb_a") as %[_ Hpfx_ab]%mono_list_both_dfrac_valid_L.
           assert (blocksa = blocksb) as Hblocks_eq.
           { apply list_eq. intros i.
             destruct (blocksa !! i) as [[ba za]|] eqn:Ha.
             - assert (blocksb.*1 !! i = Some ba) as Hbi.
               { eapply prefix_lookup_Some; [|exact Hpfx_ab].
                 rewrite list_lookup_fmap Ha. done. }
               rewrite list_lookup_fmap in Hbi.
               destruct (blocksb !! i) as [[bb zb]|] eqn:Hb; [|done].
               simpl in Hbi. injection Hbi as <-.
               f_equal. f_equal.
               assert (za = Z.of_nat i) as -> by (apply (Hbidsa _ _ Ha)).
               symmetry. apply (Hbidsb _ _ Hb).
             - apply lookup_ge_None_1 in Ha.
               symmetry. apply lookup_ge_None_2. lia. }
           (* tbb = tba (same blocks, same q+ₗ3 value) *)
           (* From Htia: blocksa !! tia = Some (tba, Z.of_nat tia) *)
           (* From Htb_inb: ∃ ci, blocksb !! ci = Some (tbb, Z.of_nat ci) *)
           (* From Hblocks_eq: blocksa = blocksb *)
           (* So tba is at tia in blocksb, and is last (S tia = length blocksb) *)
           assert (blocksb !! tia = Some (tba, Z.of_nat tia)) as Htba_in_b.
           { rewrite -Hblocks_eq. exact Htia. }
           assert (length blocksa > 0) as Hlen_pos_a.
           { apply lookup_lt_Some in Htia. lia. }
           assert (S tia = length blocksb) as Htia_last_b.
           { lia. }
           iModIntro.
           iSplitR "HΦ Hwtok Hgvlka".
           { iNext. iExists Lb,hb_,tb_,lvb,hbb,tbb,capb,blocksb,hib,tib,Cb,Wb. iFrame. done. }
           wp_pures.
           (* call grow loop *)
           wp_bind (chunked_queue_push_grow_loop _ _ _)%E.
           wp_apply (push_grow_loop_spec _ _ _ tba _ blocksb (length blocksb)
             with "[$Hinv Hlb_tail Hgvlka]").
           { exists tia. split; [rewrite Htb_eq_ab in Htba_in_b; exact Htba_in_b|exact Htia_last_b]. }
           { lia. }
           { rewrite -Hblk_len_eq. iFrame "# Hgvlka". }
           iIntros (new_tail grow_blocks) "(#Hlb_grow & %Hnt_in & Hgvtok)".
           destruct Hnt_in as [nt [Hnt_lookup Hnt_last]].
           wp_pures.
           (* store new tail *)
           wp_bind (_ <- _)%E.
           iInv "Hinv" as (Lc hc tc lvc hbc tbc capc blocksc hic tic Cc Wc)
             ">(Hac & Hbac & Hhc & Htc & Hclc & Hwrc & %Htc_eq & %Hhtc & Hlkc & %Hlvc &
                Hhbc & Hhlc & Htbc & Htlc & Hcapc &
                %Hnec & %Hhic & %Htb_inc & %Htic & %Htilastc & %Hbidsc & %Hcfreshc & %Hwfreshc & Hgvlkc & Hgvc & Hchc)".
           iDestruct (own_valid_2 with "Hbac Hlb_grow") as %[_ Hpfx_grow]%mono_list_both_dfrac_valid_L.
           assert (blocksc.*1 !! nt = Some new_tail) as Hnt_fmap.
           { eapply prefix_lookup_Some; [|exact Hpfx_grow].
             rewrite list_lookup_fmap. rewrite Hnt_lookup. done. }
           assert (blocksc !! nt = Some (new_tail, Z.of_nat nt)) as Hnt_in_cur.
           { rewrite list_lookup_fmap in Hnt_fmap.
             destruct (blocksc !! nt) as [[? z]|] eqn:Heq; [|done].
             simpl in Hnt_fmap. simplify_eq.
             assert (z = Z.of_nat nt) as -> by (apply (Hbidsc _ _ Heq)). done. }
           wp_store.
           iDestruct (ghost_var_agree with "Hgvtok Hgvc") as %Hgvc_eq.
           injection Hgvc_eq as Hgvc_len Hgvc_tb.
           assert (S nt = length blocksc) as Hnt_lastc by lia.
           destruct Hlvc as [Hlvc_zero|Hlvc_one].
           { subst lvc. simpl.
             iCombine "Hgvc Hgvlkc" as "Hgv_full".
             iDestruct (ghost_var_valid_2 with "Hgvtok Hgv_full") as %[Hfrac _].
             exfalso. rewrite Qp.add_comm in Hfrac. by apply Qp.not_add_le_l in Hfrac. }
           replace lvc with 1%Z by lia.
           iMod (ghost_var_update_halves (length blocksc, new_tail) with "Hgvtok Hgvc") as "[Hgvtok Hgvc]".
           iModIntro.
           iSplitR "HΦ Hwtok Hgvtok".
           { iNext. iExists Lc,hc,tc,1%Z,hbc,new_tail,capc,blocksc,hic,nt,Cc,Wc.
             simpl. iFrame. repeat iSplit; try (iPureIntro; first [done | lia]).
             iPureIntro. exists nt. exact Hnt_in_cur. }
           wp_pures.
           (* release lock: store 0 to lock *)
           wp_bind (release _)%E.
           unfold release. wp_pures.
           wp_bind (_ <- _)%E.
           iInv "Hinv" as (Ld hd td lvd hbd tbd capd blocksd hid tid Cd Wd)
             ">(Had & Hbad & Hhd & Htd & Hcld & Hwrd & %Htd_eq & %Hhtd & Hlkd & %Hlvd &
                Hhbd & Hhld & Htbd & Htld & Hcapd &
                %Hned & %Hhid & %Htb_ind & %Htid & %Htilastd & %Hbidsd & %Hcfreshd & %Hwfreshd & Hgvlkd & Hgvd & Hchd)".
           wp_store.
           iDestruct (ghost_var_agree with "Hgvtok Hgvd") as %Hgv_eq_d.
           injection Hgv_eq_d as Hgv_len_d Hgv_tb_d.
           iEval (rewrite Hgv_len_d Hgv_tb_d) in "Hgvtok".
           iDestruct (own_valid_2 with "Hbad Hlb_grow") as %[_ Hpfx_gd]%mono_list_both_dfrac_valid_L.
           assert (blocksd.*1 !! nt = Some new_tail) as Hnt_fmap_d.
           { eapply prefix_lookup_Some; [|exact Hpfx_gd].
             rewrite list_lookup_fmap Hnt_lookup. done. }
           assert (blocksd !! nt = Some (new_tail, Z.of_nat nt)) as Hnt_in_d.
           { rewrite list_lookup_fmap in Hnt_fmap_d.
             destruct (blocksd !! nt) as [[? z]|] eqn:Heq_d; [|done].
             simpl in Hnt_fmap_d. injection Hnt_fmap_d as <-.
             assert (z = Z.of_nat nt) as -> by (apply (Hbidsd _ _ Heq_d)). done. }
           destruct Hlvd as [Hlvd_zero|Hlvd_one].
           { subst lvd. simpl.
             iCombine "Hgvd Hgvlkd" as "Hgv_full_d".
             iDestruct (ghost_var_valid_2 with "Hgvtok Hgv_full_d") as %[Hfrac _].
             exfalso. rewrite Qp.add_comm in Hfrac. by apply Qp.not_add_le_l in Hfrac. }
           replace lvd with 1%Z by lia. simpl in Htid, Htilastd.
           iModIntro.
           iSplitR "HΦ Hwtok".
           { iNext. iExists Ld,hd,td,0%Z,hbd,tbd,capd,blocksd,hid,nt,Cd,Wd.
             simpl. iFrame.
             repeat iSplit; try (iPureIntro; first [done | lia | left; done
               | (exists nt; rewrite -Hgv_tb_d; exact Hnt_in_d)
               | (rewrite -Hgv_tb_d; exact Hnt_in_d)]). }
           wp_pures.
           wp_apply (push_find_block_loop_spec with "[$Hinv $Hlb_L $Hwtok]"); [exact Hlookup|].
           iIntros "_". by iApply "HΦ".
        ** (* lock = 1, CAS fails *)
           replace lva with (1 : Z) by lia.
           wp_cmpxchg_fail. iModIntro.
           iSplitR "HΦ Hwtok".
           { iNext. iExists La,ha,ta,1%Z,hba,tba,capa,blocksa,hia,tia,Ca,Wa.
             iFrame. repeat iSplit; try (iPureIntro; first [done | lia | right; done]). }
           do 2 wp_pure _. fold acquire. iApply ("IH_acq" with "HΦ Hwtok").
      + (* slot_idx = 0 but pos = 0, no grow *)
        wp_pures.
        wp_apply (push_find_block_loop_spec with "[$Hinv $Hlb_L $Hwtok]"); [exact Hlookup|].
        iIntros "_". by iApply "HΦ".
    - (* slot_idx ≠ 0, no grow *)
      wp_pures.
      wp_apply (push_find_block_loop_spec with "[$Hinv $Hlb_L $Hwtok]"); [exact Hlookup|].
      iIntros "_". by iApply "HΦ".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  Pop helpers                                                      *)
  (* ---------------------------------------------------------------- *)

  Lemma pop_find_slot_inner_spec γ (q : loc) (cursor start : loc)
      (h1 : nat) (L : list val) (blocks : list (loc * Z)) (d : val)
      (Hlookup : L !! h1 = Some d)
      (Hcursor_in : ∃ ci, blocks.*1 !! ci = Some cursor) :
    {{{ is_queue γ q ∗
        own γ.(γ_list) (◯ML (L : list (leibnizO val))) ∗
        own γ.(γ_blocks) (◯ML (blocks.*1 : list (leibnizO loc))) ∗
        h1 ↪[γ.(γ_claims)] () }}}
      chunked_queue_pop_find_slot #cursor #start
        #(Z.quot (Z.of_nat h1) CHUNKED_QUEUE_BLOCK_SIZE)
        #(Z.rem (Z.of_nat h1) CHUNKED_QUEUE_BLOCK_SIZE)
    {{{ r, RET r;
        (⌜r = SOMEV d⌝) ∨
        (⌜r = NONEV⌝ ∗ h1 ↪[γ.(γ_claims)] ()) }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hlb_L & #Hlb_blocks & Hclaim) HΦ".
    destruct Hcursor_in as [ci Hci].
    set (block_id := Z.quot (Z.of_nat h1) CHUNKED_QUEUE_BLOCK_SIZE).
    set (slot_idx := Z.rem (Z.of_nat h1) CHUNKED_QUEUE_BLOCK_SIZE).
    unfold chunked_queue_pop_find_slot.

    (* Precompute arithmetic facts outside Löb *)
    assert (Z.to_nat slot_idx < BS) as Hsi_lt.
    { unfold slot_idx, BS, CHUNKED_QUEUE_BLOCK_SIZE.
      apply Z2Nat.inj_lt.
      - apply Z.rem_nonneg; lia.
      - lia.
      - apply Z.rem_bound_pos; lia. }
    assert (∀ c : nat, Z.of_nat c = block_id →
            h1 = c * BS + Z.to_nat slot_idx) as Hdecomp_pre.
    { unfold block_id, slot_idx, BS, CHUNKED_QUEUE_BLOCK_SIZE. intros c Heq.
      assert (Hnn: (0 ≤ Z.rem (Z.of_nat h1) 64)%Z) by (apply Z.rem_nonneg; lia).
      assert (Hqr: (Z.of_nat h1 = 64 * Z.quot (Z.of_nat h1) 64 + Z.rem (Z.of_nat h1) 64)%Z)
        by (apply Z.quot_rem'; lia).
      rewrite <- Heq in Hqr. lia. }

    iLöb as "IH" forall (cursor ci blocks Hci) "Hlb_blocks".
    wp_rec. wp_pures.
    (* Load cursor.block_id *)
    wp_bind (! _)%E.
    iInv "Hinv" as (Li hi ti lvi hbi tbi capi blocksi hii tii Ci Wi)
      ">(Hai & Hbai & Hhi & Hti & Hclaimsi & Hwritesi & %Hti_eq & %Hhti & Hlki & %Hlvi &
         Hhbi & Hhli & Htbi & Htli & Hcapi &
         %Hnei & %Hhii & %Htb_ini & %Htii & %Htilasti & %Hbidsi & %Hcfreshi & %Hwfreshi & Hgvlki & Hgvi & Hchi)".
    iDestruct (own_valid_2 with "Hbai Hlb_blocks") as %[_ Hpfx]%mono_list_both_dfrac_valid_L.
    assert (blocksi.*1 !! ci = Some cursor) as Hci_cur
      by (eapply prefix_lookup_Some; [exact Hci | exact Hpfx]).
    assert (∃ bid_i, blocksi !! ci = Some (cursor, bid_i)) as [bid_i Hcur_blk].
    { rewrite list_lookup_fmap in Hci_cur.
      destruct (blocksi !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
    assert (bid_i = Z.of_nat ci) as -> by (apply (Hbidsi _ _ Hcur_blk)).
    destruct blocksi as [|[firsti fbi] blocksi']; first done.
    iDestruct (big_sepL_lookup_acc with "Hchi") as "[Hblk Hrest]"; first exact Hcur_blk.
    iDestruct "Hblk" as (eci2) "(Hnext & Hbid & Heci2 & Hslots)". wp_load.
    iDestruct ("Hrest" with "[Hnext Hbid Heci2 Hslots]") as "Hchi"; first (iExists eci2; iFrame).
    iModIntro. iSplitR "Hclaim HΦ".
    { iNext. iExists Li,hi,ti,lvi,hbi,tbi,capi,((firsti,fbi)::blocksi'),hii,tii,Ci,Wi. iFrame. done. }
    wp_pures.
    destruct (decide (Z.of_nat ci = block_id)) as [Heq|Hne].
    - (* Correct block — enter wait loop *)
      rewrite bool_decide_eq_true_2; last (subst block_id; rewrite Heq; done).
      wp_pures.
      pose proof (Hdecomp_pre ci Heq) as Hh1_decomp.
      set (si := Z.to_nat slot_idx).
      assert (seq 0 BS !! si = Some si) as Hseq by (apply lookup_seq; lia).
      iLöb as "IH_wait".
      wp_pures. wp_bind (! _)%E.
      iInv "Hinv" as (Lw hw tw lvw hbw tbw capw blocksw hiw tiw Cw Ww)
        ">(Haw & Hbaw & Hhw & Htw & Hclaimsw & Hwritesw & %Htw & %Hhtw & Hlkw & %Hlvw &
           Hhbw & Hhlw & Htbw & Htlw & Hcapw &
           %Hnew & %Hhiw & %Htb_inw & %Htiw & %Htilastw & %Hbidsw & %Hcfw & %Hwfw & Hgvlkw & Hgvw & Hchw)".
      iDestruct (own_valid_2 with "Hbaw Hlb_blocks") as %[_ Hpfxw]%mono_list_both_dfrac_valid_L.
      assert (blocksw.*1 !! ci = Some cursor) as Hciw
        by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxw]).
      assert (∃ bw, blocksw !! ci = Some (cursor, bw)) as [bw Hblkw].
      { rewrite list_lookup_fmap in Hciw.
        destruct (blocksw !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
      assert (bw = Z.of_nat ci) as -> by (apply (Hbidsw _ _ Hblkw)).
      destruct blocksw as [|[fw fbw] blocksw']; first done.
      iDestruct (big_sepL_lookup_acc with "Hchw") as "[Hblk Hrest]"; first exact Hblkw.
      iDestruct "Hblk" as (ecw2) "(Hn & Hb & Hecw2 & Hsl)".
      iDestruct (big_sepL_lookup_acc with "Hsl") as "[Hslot Hsl_rest]"; first exact Hseq.
      replace (Z.of_nat si) with slot_idx
        by (subst si; symmetry; apply Z2Nat.id; unfold slot_idx; apply Z.rem_nonneg; lia).
      assert (Hpos_eq : Z.to_nat (Z.of_nat ci) * BS + si = h1)
        by (rewrite Nat2Z.id; lia).
      iDestruct "Hslot" as (st) "[Hst Hcases]". wp_load.
      iDestruct "Hcases" as "[H0|[H1|[H2|H3]]]".
      + (* Empty *)
        iDestruct "H0" as "[% Hv]". subst st.
        iDestruct ("Hsl_rest" with "[Hst Hv]") as "Hsl".
        { iExists 0. iFrame. iLeft. iFrame. done. }
        iDestruct ("Hrest" with "[Hn Hb Hecw2 Hsl]") as "Hch"; first (iExists ecw2; iFrame).
        iModIntro. iSplitR "Hclaim HΦ IH_wait".
        { iNext. iExists Lw,hw,tw,lvw,hbw,tbw,capw,((fw,fbw)::blocksw'),hiw,tiw,Cw,Ww. iFrame. done. }
        wp_pures.
        iApply ("IH_wait" with "Hclaim HΦ").
      + (* Writing *)
        iDestruct "H1" as "[% Hw1]". subst st.
        iDestruct ("Hsl_rest" with "[Hst Hw1]") as "Hsl".
        { iExists 1. iFrame. iRight. iLeft. iFrame. done. }
        iDestruct ("Hrest" with "[Hn Hb Hecw2 Hsl]") as "Hch"; first (iExists ecw2; iFrame).
        iModIntro. iSplitR "Hclaim HΦ IH_wait".
        { iNext. iExists Lw,hw,tw,lvw,hbw,tbw,capw,((fw,fbw)::blocksw'),hiw,tiw,Cw,Ww. iFrame. done. }
        wp_pures.
        iApply ("IH_wait" with "Hclaim HΦ").
      + (* Valid with data *)
        iDestruct "H2" as "[% Hd]". subst st.
        iDestruct "Hd" as (v) "(Hv & %HLv & Hw2)".
        iDestruct (own_valid_2 with "Haw Hlb_L") as %[_ HpL]%mono_list_both_dfrac_valid_L.
        assert (v = d) as ->.
        { assert (Lw !! h1 = Some d) by (eapply prefix_lookup_Some; [exact Hlookup | exact HpL]).
          rewrite Hpos_eq in HLv. congruence. }
        (* Deposit claim, keep value *)
        iDestruct ("Hsl_rest" with "[Hst Hclaim Hw2]") as "Hsl".
        { iExists 2. iFrame. iRight. iRight. iRight. iSplit; [done|]. rewrite Hpos_eq. iFrame. }
        iDestruct ("Hrest" with "[Hn Hb Hecw2 Hsl]") as "Hch"; first (iExists ecw2; iFrame).
        iModIntro. iSplitR "Hv HΦ".
        { iNext. iExists Lw,hw,tw,lvw,hbw,tbw,capw,((fw,fbw)::blocksw'),hiw,tiw,Cw,Ww. iFrame. done. }
        wp_pures. wp_load. wp_pures.
        (* Store state ← 0 *)
        wp_bind (_ <- _)%E.
        iInv "Hinv" as (Lr hr tr lvr hbr tbr capr blocksr hir tir Cr Wr)
          ">(Har & Hbar & Hhr & Htr & Hclr & Hwrr & %Htr & %Hhtr & Hlkr & %Hlvr &
             Hhbr & Hhlr & Htbr & Htlr & Hcpr &
             %Hner & %Hhir & %Htb_inr & %Htir & %Htilastr & %Hbidsr & %Hcfr & %Hwfr & Hgvlkr & Hgvr & Hchr)".
        iDestruct (own_valid_2 with "Hbar Hlb_blocks") as %[_ Hpfxr]%mono_list_both_dfrac_valid_L.
        assert (blocksr.*1 !! ci = Some cursor) as Hcir
          by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxr]).
        assert (∃ br, blocksr !! ci = Some (cursor, br)) as [br Hblkr].
        { rewrite list_lookup_fmap in Hcir.
          destruct (blocksr !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
        assert (br = Z.of_nat ci) as -> by (apply (Hbidsr _ _ Hblkr)).
        destruct blocksr as [|[fr fbr] blocksr']; first done.
        iDestruct (big_sepL_lookup_acc with "Hchr") as "[Hblk Hrest2]"; first exact Hblkr.
        iDestruct "Hblk" as (ecr2) "(Hn2 & Hb2 & Hecr2 & Hsl2)".
        iDestruct (big_sepL_lookup_acc with "Hsl2") as "[Hslot2 Hsl2_rest]"; first exact Hseq.
        replace (Z.of_nat si) with slot_idx
          by (subst si; symmetry; apply Z2Nat.id; unfold slot_idx; apply Z.rem_nonneg; lia).
        iDestruct "Hslot2" as (str) "[Hstr Hcr]".
        iDestruct "Hcr" as "[H0r|[H1r|[H2r|H3r]]]".
        ** iDestruct "H0r" as "[_ Hwr]". iDestruct "Hwr" as (w) "Hwr".
           by iDestruct (pointsto_ne with "Hv Hwr") as %[].
        ** iDestruct "H1r" as "[% Hwr1]". subst str. wp_store.
           iDestruct ("Hsl2_rest" with "[Hstr Hv Hwr1]") as "Hsl2".
           { iExists 0. iFrame. iLeft. iSplit; [done|]. iExists d. iFrame. }
           iDestruct ("Hrest2" with "[Hn2 Hb2 Hecr2 Hsl2]") as "Hch2"; first (iExists ecr2; iFrame).
           iModIntro. iSplitR "HΦ".
           { iNext. iExists Lr,hr,tr,lvr,hbr,tbr,capr,((fr,fbr)::blocksr'),hir,tir,Cr,Wr. iFrame. done. }
           wp_pures. iApply "HΦ". iLeft. done.
        ** iDestruct "H2r" as "[_ Hvr]". iDestruct "Hvr" as (v') "(Hvr & _ & _)".
           by iDestruct (pointsto_ne with "Hv Hvr") as %[].
        ** iDestruct "H3r" as "(% & Hclr2 & _)". subst str. wp_store.
           iDestruct ("Hsl2_rest" with "[Hstr Hv]") as "Hsl2".
           { iExists 0. iFrame. iLeft. iSplit; [done|]. iExists d. iFrame. }
           iDestruct ("Hrest2" with "[Hn2 Hb2 Hecr2 Hsl2]") as "Hch2"; first (iExists ecr2; iFrame).
           iModIntro. iSplitR "HΦ".
           { iNext. iExists Lr,hr,tr,lvr,hbr,tbr,capr,((fr,fbr)::blocksr'),hir,tir,Cr,Wr. iFrame. done. }
           wp_pures. iApply "HΦ". iLeft. done.
      + (* Claimed — contradiction, we hold the claim *)
        iDestruct "H3" as "(% & Hcl2 & _)". subst st.
        iDestruct (ghost_map_elem_ne with "Hclaim Hcl2") as %Hneq.
        exfalso. apply Hneq. lia.
    - (* Wrong block — follow next pointer *)
      rewrite bool_decide_eq_false_2; last (intros Hinj; inversion Hinj; lia).
      wp_pures. wp_bind (! _)%E.
      iInv "Hinv" as (Ln hn tn lvn hbn tbn capn blocksn hin tin Cn Wn)
        ">(Han & Hban & Hhn & Htn & Hcln & Hwrn & %Htn & %Hhtn & Hlkn & %Hlvn &
           Hhbn & Hhln & Htbn & Htln & Hcpn &
           %Hnen & %Hhin & %Htb_inn & %Htin & %Htilastn & %Hbidsn & %Hcfn & %Hwfn & Hgvlkn & Hgvn & Hchn)".
      iDestruct (own_valid_2 with "Hban Hlb_blocks") as %[_ Hpfxn]%mono_list_both_dfrac_valid_L.
      assert (blocksn.*1 !! ci = Some cursor) as Hcin
        by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxn]).
      assert (∃ bn, blocksn !! ci = Some (cursor, bn)) as [bn Hblkn].
      { rewrite list_lookup_fmap in Hcin.
        destruct (blocksn !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
      assert (bn = Z.of_nat ci) as -> by (apply (Hbidsn _ _ Hblkn)).
      destruct blocksn as [|[fn fbn] blocksn']; first done.
      iDestruct (big_sepL_lookup_acc with "Hchn") as "[Hblk Hrest]"; first exact Hblkn.
      iDestruct "Hblk" as (ecn2) "(Hn & Hb & Hecn2 & Hsl)".
      set (nxt := block_next ((fn,fbn)::blocksn') ci fn). wp_load.
      assert (∃ ni, ((fn,fbn)::blocksn').*1 !! ni = Some nxt) as [ni Hni].
      { unfold nxt, block_next.
        destruct (((fn,fbn)::blocksn') !! S ci) as [[? ?]|] eqn:?;
          [exists (S ci); rewrite list_lookup_fmap; rewrite Heqo; done | exists 0%nat; done]. }
      iDestruct (own_mono _ _ (◯ML (((fn,fbn)::blocksn').*1 : list (leibnizO loc))) with "Hban") as "#Hlbn".
      { apply mono_list_included. }
      iDestruct ("Hrest" with "[Hn Hb Hecn2 Hsl]") as "Hch"; first (iExists ecn2; iFrame).
      iModIntro. iSplitR "Hclaim HΦ".
      { iNext. iExists Ln,hn,tn,lvn,hbn,tbn,capn,((fn,fbn)::blocksn'),hin,tin,Cn,Wn. iFrame. done. }
      wp_pures.
      destruct (decide (nxt = start)) as [->|Hns].
      + rewrite bool_decide_eq_true_2; last done.
        wp_pures. iApply "HΦ". iRight. iFrame. done.
      + rewrite bool_decide_eq_false_2; last (intros H; apply Hns; inversion H; done).
        wp_if_false. iApply ("IH" $! nxt ni ((fn,fbn)::blocksn') Hni with "Hclaim HΦ Hlbn").
  Defined.

  (* Helper: the find_slot_loop finds the block with the target block_id,
     waits for the slot to become Valid, reads the value, resets state to Empty,
     and returns the value. *)
  Lemma find_slot_loop_spec γ (q : loc) (h1 : nat)
      (L3 : list val) (blocks3 : list (loc * Z)) (d : val)
      (Hlookup : L3 !! h1 = Some d) :
    {{{ is_queue γ q ∗
        own γ.(γ_list) (◯ML (L3 : list (leibnizO val))) ∗
        own γ.(γ_blocks) (◯ML (blocks3.*1 : list (leibnizO loc))) ∗
        h1 ↪[γ.(γ_claims)] () }}}
      chunked_queue_pop_find_slot_loop #q
         #(Z.quot (Z.of_nat h1) CHUNKED_QUEUE_BLOCK_SIZE)
         #(Z.rem (Z.of_nat h1) CHUNKED_QUEUE_BLOCK_SIZE)
    {{{ RET d; True }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hlb_L & #Hlb_blocks & Hclaim) HΦ".
    unfold chunked_queue_pop_find_slot_loop.
    iLöb as "IH" forall (Φ).
    wp_rec. wp_pures.
    wp_bind (! _)%E.
    iInv "Hinv" as (Lf hf tf lvf hbf tbf capf blocksf hif tif Cf Wf)
      ">(Haf & Hbaf & Hhf & Htf & Hclaimsf & Hwritesf & %Htf_eq & %Hhtf & Hlkf & %Hlvf &
         Hhbf & Hhfl & Htbf & Htfl & Hcapf &
         %Hnef & %Hhif & %Htb_inf & %Htif & %Htilastf & %Hbidsf & %Hcfreshf & %Hwfreshf & Hgvlkf & Hgvf & Hchf)".
    wp_load.
    iDestruct (own_mono _ _ (◯ML (blocksf.*1 : list (leibnizO loc))) with "Hbaf") as "#Hlb_blocksf".
    { apply mono_list_included. }
    iModIntro. iSplitR "HΦ Hclaim".
    { iNext. iExists Lf, hf, tf, lvf, hbf, tbf, capf, blocksf, hif, tif, Cf, Wf.
      iFrame. done. }
    wp_pures.
    wp_bind (chunked_queue_pop_find_slot _ _ _ _)%E.
    assert (∃ ci, blocksf.*1 !! ci = Some hbf) as Hcursor_in.
    { exists hif. rewrite list_lookup_fmap. rewrite Hhif. done. }
    wp_apply (pop_find_slot_inner_spec _ _ _ _ _ _ blocksf
      with "[$Hinv $Hlb_L Hlb_blocksf $Hclaim]"); [done|done|iFrame "#"|].
    iIntros (r) "[%Hsome | [%Hnone Hclaim]]".
    - subst r. wp_pures. by iApply "HΦ".
    - subst r. do 5 wp_pure _. iApply ("IH" with "Hclaim HΦ").
  Defined.

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
  Proof.
    iIntros "#Hinv" (Φ) "AU".
    unfold chunked_queue_pop. wp_pures.
    wp_bind (chunked_queue_pop_cas_loop _)%E.
    unfold chunked_queue_pop_cas_loop.
    iLöb as "IH".
    wp_rec. wp_pures.
    (* Load head_idx *)
    wp_bind (! _)%E.
    iInv "Hinv" as (L1 h1 t1 lv1 hb1 tb1 cap1 blocks1 hi1 ti1 C1 W1)
      ">(Ha1 & Hba1 & Hh1 & Ht1 & Hclaims1 & Hwrites1 & %Ht1 & %Hht1 & Hlk1 & %Hlv1 &
         Hhb1 & Hh1l & Htb1 & Htl1 & Hcap1 &
         %Hne1 & %Hhi1 & %Htb_in1 & %Hti1 & %Htilast1 & %Hbids1 & %Hcfresh1 & %Hwfresh1 & Hgvlk1 & Hgv1 & Hch1)".
    wp_load.
    iDestruct (mono_nat_lb_own_get with "Hh1") as "#Hlb_h1".
    iModIntro. iSplitR "AU".
    { iNext. unfold queue_inv_inner.
      iExists L1, h1, t1, lv1, hb1, tb1, cap1, blocks1, hi1, ti1, C1, W1.
      iFrame. done. }
    wp_pures.
    (* Load tail_idx *)
    wp_bind (! _)%E.
    iInv "Hinv" as (L2 h2 t2 lv2 hb2 tb2 cap2 blocks2 hi2 ti2 C2 W2)
      ">(Ha2 & Hba2 & Hh2 & Ht2 & Hclaims2 & Hwrites2 & %Ht2 & %Hht2 & Hlk2 & %Hlv2 &
         Hhb2 & Hh2l & Htb2 & Htl2 & Hcap2 &
         %Hne2 & %Hhi2 & %Htb_in2 & %Hti2 & %Htilast2 & %Hbids2 & %Hcfresh2 & %Hwfresh2 & Hgvlk2 & Hgv2 & Hch2)".
    wp_load.
    iDestruct (mono_nat_lb_own_valid with "Hh2 Hlb_h1") as %[_ Hh1_le_h2].
    iDestruct (mono_nat_lb_own_get with "Ht2") as "#Hlb_t2".
    destruct (decide (Z.of_nat t2 ≤ Z.of_nat h1)%Z) as [Hdec|Hdec].
    + (* Empty case: t2 ≤ h1, so h2 = t2 = h1 = length L2 *)
      assert (h2 = t2) as -> by lia.
      assert (t2 = h1) as -> by lia.
      iMod "AU" as (L' h') "[Hcontent [_ Hclose]]".
      unfold queue_content.
      iDestruct "Hcontent" as "(Hauth' & Hhead' & Htail')".
      iCombine "Ha2" "Hauth'" as "Hauth_full".
      iDestruct (own_valid with "Hauth_full") as %Hvalid.
      rewrite mono_list_auth_dfrac_op_valid in Hvalid.
      destruct Hvalid as [_ HLeq]. apply leibniz_equiv in HLeq. subst L'.
      iDestruct "Hauth_full" as "[Ha2 Hauth']".
      iDestruct (mono_nat_auth_own_agree with "Hh2 Hhead'") as %[_ Hheq]. subst h'.
      iDestruct (mono_nat_auth_own_agree with "Ht2 Htail'") as %[_ Htleq].
      iMod ("Hclose" $! (InjLV #()) false with "[Hauth' Hhead' Htail']") as "HΦ".
      { iRight. iSplit; first done. iSplit; first done. iSplit.
        - iPureIntro. lia.
        - unfold queue_content. iFrame. }
      iModIntro. iSplitR "HΦ".
      { iNext. unfold queue_inv_inner.
        iExists L2, h1, h1, lv2, hb2, tb2, cap2, blocks2, hi2, ti2, C2, W2.
        iFrame. done. }
      wp_pures.
      rewrite bool_decide_eq_true_2; last lia.
      wp_pures. done.
    + (* Non-empty case: h1 < t2 *)
      iModIntro. iSplitR "AU".
      { iNext. unfold queue_inv_inner.
        iExists L2, h2, t2, lv2, hb2, tb2, cap2, blocks2, hi2, ti2, C2, W2.
        iFrame. done. }
      wp_pures.
      rewrite bool_decide_eq_false_2; last lia.
      wp_pures.
      (* CAS on head_idx *)
      wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as (L3 h3 t3 lv3 hb3 tb3 cap3 blocks3 hi3 ti3 C3 W3)
        ">(Ha3 & Hba3 & Hh3 & Ht3 & Hclaims3 & Hwrites3 & %Ht3 & %Hht3 & Hlk3 & %Hlv3 &
           Hhb3 & Hh3l & Htb3 & Htl3 & Hcap3 &
           %Hne3 & %Hhi3 & %Htb_in3 & %Hti3 & %Htilast3 & %Hbids3 & %Hcfresh3 & %Hwfresh3 & Hgvlk3 & Hgv3 & Hch3)".
      destruct (decide (h3 = h1)) as [->|Hne].
      - (* CAS success *)
        wp_cmpxchg_suc.
        iMod "AU" as (L' h') "[Hcontent [_ Hclose]]".
        unfold queue_content.
        iDestruct "Hcontent" as "(Hauth' & Hhead' & Htail')".
        iCombine "Ha3" "Hauth'" as "Hauth_full".
        iDestruct (own_valid with "Hauth_full") as %Hvalid.
        rewrite mono_list_auth_dfrac_op_valid in Hvalid.
        destruct Hvalid as [_ HLeq]. apply leibniz_equiv in HLeq. subst L'.
        iDestruct "Hauth_full" as "[Ha3 Hauth']".
        iDestruct (mono_nat_auth_own_agree with "Hh3 Hhead'") as %[_ Hheq]. subst h'.
        iDestruct (mono_nat_auth_own_agree with "Ht3 Htail'") as %[_ Htleq].
        iDestruct (mono_nat_lb_own_valid with "Ht3 Hlb_t2") as %[_ Ht2_le_t3].
        assert (h1 < t3) as Hh1_lt_t3 by lia.
        assert (h1 < length L3) as Hh1_lt_len by lia.
        destruct (L3 !! h1) as [d|] eqn:Hlookup;
          last by (exfalso; apply lookup_ge_None in Hlookup; lia).
        iCombine "Hh3" "Hhead'" as "Hhead_full".
        iMod (mono_nat_own_update (S h1) with "Hhead_full") as "[[Hh3 Hhead'] _]".
        { lia. }
        (* Persistent lower bounds for continuation proofs *)
        iDestruct (own_mono _ _ (◯ML (L3 : list (leibnizO val))) with "Ha3") as "#Hlb_L3".
        { apply mono_list_included. }
        iDestruct (own_mono _ _ (◯ML (blocks3.*1 : list (leibnizO loc))) with "Hba3") as "#Hlb_blocks3".
        { apply mono_list_included. }
        (* Allocate consumer claim token *)
        iMod (ghost_map_insert h1 () with "Hclaims3") as "[Hclaims3 Hclaim]".
        { apply Hcfresh3. lia. }
        iMod ("Hclose" $! (InjRV d) true with "[Hauth' Hhead' Htail']") as "HΦ".
        { iLeft. iSplit; first done. iExists d. iSplit; first done. iSplit; first done.
          unfold queue_content. iFrame. }
        replace (h1 + 1)%Z with (Z.of_nat (S h1)) by lia.
        iModIntro. iSplitR "HΦ Hclaim".
        { iNext. unfold queue_inv_inner.
          iExists L3, (S h1), t3, lv3, hb3, tb3, cap3, blocks3, hi3, ti3, (<[h1 := ()]> C3), W3.
          iFrame. iPureIntro. repeat split; try done; try lia.
          intros k Hk. rewrite lookup_insert_ne; [apply Hcfresh3; lia | lia]. }
        wp_pures.
        (* Continuation: advance_head_loop + find_slot_loop *)
        destruct (bool_decide (#(h1 `rem` CHUNKED_QUEUE_BLOCK_SIZE) = #0)) eqn:Hrem_dec.
        ** (* slot_idx = 0 *)
           wp_pures.
           destruct (decide (0 < h1)%nat) as [Hh1_pos|Hh1_zero].
           --- (* h1 > 0 && slot_idx = 0: advance_head_loop needed *)
               rewrite bool_decide_eq_true_2; last lia.
               wp_pures.
               wp_bind (chunked_queue_pop_advance_head_loop _ _).
               unfold chunked_queue_pop_advance_head_loop.
               iLöb as "IH_adv".
               wp_rec. wp_pures.
               (* Load old_head = queue.head_block *)
               wp_bind (! _)%E.
               iInv "Hinv" as (La ha ta lva hba tba capa blocksa hia tia Ca Wa)
                 ">(Haa & Hbaa & Hha & Hta & Hclaimsa & Hwritesa & %Hta_eq & %Hhta & Hlka & %Hlva &
                    Hhba & Hhla & Htba & Htla & Hcapa &
                    %Hnea & %Hhia & %Htb_ina & %Htia & %Htilasta & %Hbidsa & %Hcfresha & %Hwfresha & Hgvlka & Hgva & Hcha)".
               wp_load.
               (* Save persistent lower bound for blocksa *)
               iDestruct (own_mono _ _ (◯ML (blocksa.*1 : list (leibnizO loc))) with "Hbaa") as "#Hlb_blocksa".
               { apply mono_list_included. }
               iModIntro. iSplitR "IH_adv HΦ Hclaim".
               { iNext. unfold queue_inv_inner.
                 iExists La, ha, ta, lva, hba, tba, capa, blocksa, hia, tia, Ca, Wa.
                 iFrame. done. }
               wp_pures.
               (* Now need to read hba.block_id — open invariant again *)
               wp_bind (! _)%E.
               iInv "Hinv" as (Lb hb0 tb0 lvb hbb tbb capb blocksb hib tib Cb Wb)
                 ">(Hab & Hbab & Hhb & Htb & Hclaimsb & Hwritesb & %Htb_eq & %Hhtb & Hlkb & %Hlvb &
                    Hhbb & Hhlb & Htbb & Htlb & Hcapb &
                    %Hneb & %Hhib & %Htb_inb & %Htib & %Htilastb & %Hbidsb & %Hcfreshb & %Hwfreshb & Hgvlkb & Hgvb & Hchb)".
               (* Prove hba is in current blocks via prefix *)
               iDestruct (own_valid_2 with "Hbab Hlb_blocksa") as %Hpfx_ab.
               rewrite mono_list_both_dfrac_valid_L in Hpfx_ab.
               destruct Hpfx_ab as [_ Hpfx_ab].
               assert (hia < length blocksa) as Hhia_lt by (eapply lookup_lt_Some; eauto).
               assert (hia < length blocksb) as Hhia_lt_b.
               { apply prefix_length in Hpfx_ab. rewrite !length_fmap in Hpfx_ab. lia. }
               assert (blocksa.*1 !! hia = Some hba) as Hhba_in_a.
               { rewrite list_lookup_fmap. rewrite Hhia. done. }
               assert (blocksb.*1 !! hia = Some hba) as Hhba_in_b.
               { eapply prefix_lookup_Some; eauto. }
               assert (∃ bid_b, blocksb !! hia = Some (hba, bid_b)) as [bid_b Hhba_blk_b].
               { rewrite list_lookup_fmap in Hhba_in_b.
                 destruct (blocksb !! hia) as [[lb bidb]|] eqn:Hlb; [|discriminate].
                 simpl in Hhba_in_b. inversion Hhba_in_b. subst. eauto. }
               assert (bid_b = Z.of_nat hia) as -> by (apply (Hbidsb _ _ Hhba_blk_b)).
               destruct blocksb as [|[firstb firstbid] blocksb']; first done.
               iDestruct (big_sepL_lookup_acc with "Hchb") as "[Hblk Hchb_rest]"; first exact Hhba_blk_b.
               unfold is_block.
               iDestruct "Hblk" as (ec_hb) "(Hnext_b & Hbid_b & Hec_hb & Hslots_b)".
               wp_load.
               iDestruct ("Hchb_rest" with "[Hnext_b Hbid_b Hec_hb Hslots_b]") as "Hchb".
               { unfold is_block. iExists ec_hb. iFrame. }
               iModIntro. iSplitR "IH_adv HΦ Hclaim".
               { iNext. unfold queue_inv_inner.
                 iExists Lb, hb0, tb0, lvb, hbb, tbb, capb, ((firstb, firstbid) :: blocksb'), hib, tib, Cb, Wb.
                 iFrame. done. }
               wp_pures.
               (* block_id ≤ hia? *)
               destruct (decide (Z.quot (Z.of_nat h1) CHUNKED_QUEUE_BLOCK_SIZE ≤ Z.of_nat hia)%Z) as [Hbd_le|Hbd_gt].
               +++ (* block_id ≤ hia: loop done *)
                   rewrite bool_decide_eq_true_2; last done.
                   wp_pures.
                   wp_apply (find_slot_loop_spec with "[$Hinv $Hlb_L3 $Hlb_blocks3 $Hclaim]"); [done|].
                   iIntros "_". wp_pures. done.
               +++ (* block_id > hia: need to advance, read next, CAS, loop *)
                   rewrite bool_decide_eq_false_2; last done.
                   wp_pures.
                   (* Read next pointer from hba *)
                   wp_bind (! _)%E.
                   iInv "Hinv" as (Lc hc tc lvc hbc tbc capc blocksc hic tic Cc Wc)
                     ">(Hac & Hbac & Hhc & Htc & Hclaimsc & Hwritesc & %Htc_eq & %Hhtc & Hlkc & %Hlvc &
                        Hhbc & Hhlc & Htbc & Htlc & Hcapc &
                        %Hnec & %Hhic & %Htb_inc & %Htic & %Htilastc & %Hbidsc & %Hcfreshc & %Hwfreshc & Hgvlkc & Hgvc & Hchc)".
                   iDestruct (own_valid_2 with "Hbac Hlb_blocksa") as %Hpfx_ac.
                   rewrite mono_list_both_dfrac_valid_L in Hpfx_ac.
                   destruct Hpfx_ac as [_ Hpfx_ac].
                   assert (hia < length blocksc) as Hhia_lt_c.
                   { apply prefix_length in Hpfx_ac. rewrite !length_fmap in Hpfx_ac. lia. }
                   assert (blocksc.*1 !! hia = Some hba) as Hhba_in_c.
                   { eapply prefix_lookup_Some. exact Hhba_in_a. exact Hpfx_ac. }
                   assert (∃ bid_c, blocksc !! hia = Some (hba, bid_c)) as [bid_c Hhba_blk_c].
                   { rewrite list_lookup_fmap in Hhba_in_c.
                     destruct (blocksc !! hia) as [[lc bidc]|] eqn:Hlc; [|discriminate].
                     simpl in Hhba_in_c. inversion Hhba_in_c. subst. eauto. }
                   assert (bid_c = Z.of_nat hia) as -> by (apply (Hbidsc _ _ Hhba_blk_c)).
                   (* Save persistent lb for blocksc before destructing *)
                   iDestruct (own_mono _ _ (◯ML (blocksc.*1 : list (leibnizO loc))) with "Hbac") as "#Hlb_blocksc".
                   { apply mono_list_included. }
                   destruct blocksc as [|[firstc firstcidb] blocksc']; first done.
                   iDestruct (big_sepL_lookup_acc with "Hchc") as "[Hblk_c Hchc_rest]"; first exact Hhba_blk_c.
                   unfold is_block.
                   iDestruct "Hblk_c" as (ec_hc) "(Hnext_c & Hbid_c & Hec_hc & Hslots_c)".
                   wp_load.
                   iDestruct ("Hchc_rest" with "[Hnext_c Hbid_c Hec_hc Hslots_c]") as "Hchc".
                   { unfold is_block. iExists ec_hc. iFrame. }
                   iModIntro. iSplitR "IH_adv HΦ Hclaim".
                   { iNext. unfold queue_inv_inner.
                     iExists Lc, hc, tc, lvc, hbc, tbc, capc, ((firstc, firstcidb) :: blocksc'), hic, tic, Cc, Wc.
                     iFrame. done. }
                   wp_pures.
                   (* CAS on queue.head_block *)
                   wp_bind (CmpXchg _ _ _).
                   iInv "Hinv" as (Ld hd td lvd hbd tbd capd blocksd hid tid Cd Wd)
                     ">(Had & Hbad & Hhd & Htd & Hclaimsd & Hwritesd & %Htd_eq & %Hhtd & Hlkd & %Hlvd &
                        Hhbd & Hhld & Htbd & Htld & Hcapd &
                        %Hned & %Hhid & %Htb_ind & %Htid & %Htilastd & %Hbidsd & %Hcfreshd & %Hwfreshd & Hgvlkd & Hgvd & Hchd)".
                   destruct (decide (hbd = hba)) as [->|Hne_hbd].
                   *** (* CAS success: head_block = hba, update to next *)
                       wp_cmpxchg_suc.
                       (* blocksc.*1 prefix of blocksd.*1 *)
                       iDestruct (own_valid_2 with "Hbad Hlb_blocksc") as %Hpfx_cd.
                       rewrite mono_list_both_dfrac_valid_L in Hpfx_cd.
                       destruct Hpfx_cd as [_ Hpfx_cd].
                       (* block_next case split: S hia within blocksc or wraps to firstc *)
                       set (bnext := block_next ((firstc, firstcidb) :: blocksc') hia firstc).
                       destruct (((firstc, firstcidb) :: blocksc') !! (S hia)) as [[next_loc next_bid]|] eqn:Hnext_blk.
                       ---- (* S hia within blocksc: next = block at S hia *)
                         assert (bnext = next_loc) as Hbn.
                         { unfold bnext, block_next. rewrite Hnext_blk. done. }
                         assert (((firstc, firstcidb) :: blocksc').*1 !! (S hia) = Some next_loc) as Hnext_in_c.
                         { rewrite list_lookup_fmap. rewrite Hnext_blk. done. }
                         assert (blocksd.*1 !! (S hia) = Some next_loc) as Hnext_in_d.
                         { eapply prefix_lookup_Some; eauto. }
                         assert (∃ bid_d, blocksd !! (S hia) = Some (next_loc, bid_d)) as [bid_d2 Hnext_blk_d].
                         { rewrite list_lookup_fmap in Hnext_in_d.
                           destruct (blocksd !! S hia) as [[ld bidd]|] eqn:Hsd; [|discriminate].
                           simpl in Hnext_in_d. injection Hnext_in_d as <-. eauto. }
                         assert (bid_d2 = Z.of_nat (S hia)) as -> by (apply (Hbidsd _ _ Hnext_blk_d)).
                         rewrite Hbn.
                         iModIntro. iSplitR "IH_adv HΦ Hclaim".
                         { iNext. unfold queue_inv_inner.
                           iExists Ld, hd, td, lvd, next_loc, tbd, capd, blocksd, (S hia), tid, Cd, Wd.
                           iFrame. iPureIntro. repeat split; try done; try lia. }
                         wp_proj. wp_seq.
                         iApply ("IH_adv" with "HΦ Hclaim").
                       ---- (* S hia out of bounds: next wraps to firstc = block 0 *)
                         assert (bnext = firstc) as Hbn.
                         { unfold bnext, block_next. rewrite Hnext_blk. done. }
                         assert (blocksd.*1 !! 0 = Some firstc) as Hfirst_in_d.
                         { eapply prefix_lookup_Some; last exact Hpfx_cd.
                           done. }
                         assert (∃ bid_d, blocksd !! 0 = Some (firstc, bid_d)) as [bid_d2 Hfirst_blk_d].
                         { rewrite list_lookup_fmap in Hfirst_in_d.
                           destruct (blocksd !! 0) as [[ld bidd]|] eqn:Hsd; [|discriminate].
                           simpl in Hfirst_in_d. injection Hfirst_in_d as <-. eauto. }
                         assert (bid_d2 = Z.of_nat 0) as -> by (apply (Hbidsd _ _ Hfirst_blk_d)).
                         rewrite Hbn.
                         iModIntro. iSplitR "IH_adv HΦ Hclaim".
                         { iNext. unfold queue_inv_inner.
                           iExists Ld, hd, td, lvd, firstc, tbd, capd, blocksd, 0%nat, tid, Cd, Wd.
                           iFrame. iPureIntro. repeat split; try done; try lia. }
                         wp_proj. wp_seq.
                         iApply ("IH_adv" with "HΦ Hclaim").
                   *** (* CAS fail: head_block ≠ hba *)
                       wp_cmpxchg_fail.
                       iModIntro. iSplitR "IH_adv HΦ Hclaim".
                       { iNext. unfold queue_inv_inner.
                         iExists Ld, hd, td, lvd, hbd, tbd, capd, blocksd, hid, tid, Cd, Wd.
                         iFrame. done. }
                       wp_proj. wp_seq.
                       iApply ("IH_adv" with "HΦ Hclaim").
           --- (* h1 = 0: no advance needed *)
               assert (h1 = 0) as -> by lia.
               rewrite bool_decide_eq_false_2; last lia.
               wp_pures.
               wp_apply (find_slot_loop_spec with "[$Hinv $Hlb_L3 $Hlb_blocks3 $Hclaim]"); [done|].
               iIntros "_". wp_pures. done.
        ** (* slot_idx ≠ 0 case - no advance_head_loop *)
           wp_pures.
           wp_apply (find_slot_loop_spec with "[$Hinv $Hlb_L3 $Hlb_blocks3 $Hclaim]"); [done|].
           iIntros "_". wp_pures. done.
      - (* CAS fail *)
        wp_cmpxchg_fail. { intros H. inversion H. lia. }
        iModIntro. iSplitR "AU".
        { iNext. unfold queue_inv_inner.
          iExists L3, h3, t3, lv3, hb3, tb3, cap3, blocks3, hi3, ti3, C3, W3.
          iFrame. done. }
        wp_proj. wp_if. iApply ("IH" with "AU").
  Defined.

End spec.
