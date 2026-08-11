From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import invariants mono_nat ghost_map.
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
  cq_mono_list_locG :: inG Σ (mono_listR (leibnizO loc));
  cq_mono_natG :: mono_natG Σ;
  cq_ghost_mapG :: ghost_mapG Σ nat ();
}.

Definition chunked_queueΣ : gFunctors :=
  #[ GFunctor (mono_listR (leibnizO val));
     GFunctor (mono_listR (leibnizO loc));
     mono_natΣ;
     ghost_mapΣ nat () ].

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
  (*  Block: [next, block_id, slot_0_val, slot_0_state, ...]         *)
  (* -------------------------------------------------------------- *)
  Definition is_block (γc γw : gname) (L : list val) (b : loc) (bid : Z)
      (next : loc) : iProp Σ :=
    (b +ₗ 0) ↦ #next ∗
    (b +ₗ 1) ↦ #bid ∗
    [∗ list] i ∈ seq 0 BS,
      slot_inv γc γw L (Z.to_nat bid * BS + i) (b +ₗ (2 + 2 * Z.of_nat i)).

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
    ⌜cap = (Z.of_nat (length blocks) * CHUNKED_QUEUE_BLOCK_SIZE)%Z⌝ ∗
    ⌜blocks !! hi = Some (hb, Z.of_nat hi)⌝ ∗
    ⌜blocks !! ti = Some (tb, Z.of_nat ti)⌝ ∗
    ⌜∀ i blk, blocks !! i = Some blk → snd blk = Z.of_nat i⌝ ∗
    ⌜∀ k : nat, h ≤ k → C !! k = None⌝ ∗
    ⌜∀ k : nat, t ≤ k → W !! k = None⌝ ∗
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
    change (Z.to_nat BLOCK_ALLOC_SIZE) with 130%nat.
    iDestruct (array_cons with "Hblock") as "[Hb0 Hblock]".
    iDestruct (array_cons with "Hblock") as "[Hb1 Hblock]".
    rewrite Loc.add_0. wp_store. wp_pures.
    wp_store. wp_pures. wp_store. wp_pures. wp_store. wp_pures.
    wp_store. wp_pures. wp_store. wp_pures. wp_store.
    replace (block +ₗ 1 +ₗ 1) with (block +ₗ 2) in * by (rewrite Loc.add_assoc; done).
    iMod (own_alloc (●ML{# (1/2)%Qp} ([] : list (leibnizO val)) ⋅ ●ML{# (1/2)%Qp} ([] : list (leibnizO val)))) as (γ_list) "[Hauth1 Hauth2]".
    { rewrite -mono_list_auth_dfrac_op. rewrite dfrac_op_own Qp.half_half. apply mono_list_auth_valid. }
    iMod (own_alloc (●ML{# 1%Qp} ([block] : list (leibnizO loc)))) as (γ_blocks) "Hblk_auth".
    { apply mono_list_auth_valid. }
    iMod (mono_nat_own_alloc 0) as (γ_head) "[Hhead_auth _]".
    iMod (mono_nat_own_alloc 0) as (γ_tail) "[Htail_auth _]".
    iMod (ghost_map_alloc_empty) as (γ_claims) "Hclaims".
    iMod (ghost_map_alloc_empty) as (γ_writes) "Hwrites".
    iDestruct "Hhead_auth" as "[Hhead1 Hhead2]".
    iDestruct "Htail_auth" as "[Htail1 Htail2]".
    set (γ := QueueName γ_list γ_blocks γ_head γ_tail γ_claims γ_writes).
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
    iSplit; first (iPureIntro; unfold CHUNKED_QUEUE_BLOCK_SIZE; lia).
    iSplit; first (iPureIntro; reflexivity).
    iSplit; first (iPureIntro; reflexivity).
    iSplit; first (iPureIntro; intros i blk Hi; destruct i as [|[|]]; simpl in Hi; [inversion Hi; done|discriminate|discriminate]).
    iSplit; first (iPureIntro; intros k _; apply lookup_empty).
    iSplit; first (iPureIntro; intros k _; apply lookup_empty).
    unfold is_block_chain. simpl. unfold is_block. rewrite Loc.add_0. iFrame "Hb0 Hb1".
    change BS with 64%nat. change (Z.to_nat 0) with 0%nat.
    iAssert (∀ (n : nat), ⌜(n ≤ 64)%nat⌝ -∗
      (block +ₗ (2 + 2 * Z.of_nat (64 - n))) ↦∗ replicate (2 * n) #0 -∗
      [∗ list] i ∈ seq (64 - n) n, slot_inv γ_claims γ_writes [] (0 * 64 + i)%nat (block +ₗ (2 + 2 * Z.of_nat i)))%I as "Hind".
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
          replace (block +ₗ (2 + 2 * (64 - n' - 1)%nat) +ₗ 1) with (block +ₗ (2 + 2 * Z.of_nat (64 - n' - 1)) +ₗ 1) by (f_equal; lia).
          iFrame "Hstate". iLeft. iSplit; [done|]. iExists #0. iExact "Hval". }
        replace (S (64 - n' - 1)) with (64 - n')%nat by lia.
        iApply ("IH" with "[%] [Hrest]").
        { lia. }
        replace (block +ₗ (2 + 2 * (64 - n' - 1)%nat) +ₗ 2%nat) with (block +ₗ (2 + 2 * Z.of_nat (64 - n'))) by (rewrite Loc.add_assoc; f_equal; lia).
        replace (n' + (n' + 0))%nat with (2 * n')%nat by lia.
        done. }
    iSpecialize ("Hind" $! 64%nat with "[%] [Hblock]").
    { lia. }
    { change (2 + 2 * Z.of_nat (64 - 64))%Z with 2%Z. done. }
    replace (64 - 64)%nat with 0%nat by lia. done.
  Defined.

  (* ---------------------------------------------------------------- *)
  (*  Push helpers                                                     *)
  (* ---------------------------------------------------------------- *)

  Lemma push_grow_loop_spec γ (q tail : loc) (block_id : Z) :
    {{{ is_queue γ q }}}
      chunked_queue_push_grow_loop #q #tail #block_id
    {{{ (new_tail : loc) (blocks : list (loc * Z)), RET #new_tail;
        own γ.(γ_blocks) (◯ML (blocks.*1 : list (leibnizO loc))) ∗
        ⌜∃ nt, blocks !! nt = Some (new_tail, Z.of_nat nt)⌝ }}}.
  Proof. Admitted.

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
         %Hnei & %Hcei & %Hhii & %Htii & %Hbidsi & %Hcfreshi & %Hwfreshi & Hchi)".
    iDestruct (own_valid_2 with "Hbai Hlb_blocks") as %[_ Hpfx]%mono_list_both_dfrac_valid_L.
    assert (blocksi.*1 !! ci = Some cursor) as Hci_cur
      by (eapply prefix_lookup_Some; [exact Hci | exact Hpfx]).
    assert (∃ bid_i, blocksi !! ci = Some (cursor, bid_i)) as [bid_i Hcur_blk].
    { rewrite list_lookup_fmap in Hci_cur.
      destruct (blocksi !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
    assert (bid_i = Z.of_nat ci) as -> by (apply (Hbidsi _ _ Hcur_blk)).
    destruct blocksi as [|[firsti fbi] blocksi']; first done.
    iDestruct (big_sepL_lookup_acc with "Hchi") as "[Hblk Hrest]"; first exact Hcur_blk.
    iDestruct "Hblk" as "(Hnext & Hbid & Hslots)". wp_load.
    iDestruct ("Hrest" with "[Hnext Hbid Hslots]") as "Hchi"; first (iFrame).
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
           %Hnew & %Hcew & %Hhiw & %Htiw & %Hbidsw & %Hcfw & %Hwfw & Hchw)".
      iDestruct (own_valid_2 with "Hbaw Hlb_blocks") as %[_ Hpfxw]%mono_list_both_dfrac_valid_L.
      assert (blocksw.*1 !! ci = Some cursor) as Hciw
        by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxw]).
      assert (∃ bw, blocksw !! ci = Some (cursor, bw)) as [bw Hblkw].
      { rewrite list_lookup_fmap in Hciw.
        destruct (blocksw !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
      assert (bw = Z.of_nat ci) as -> by (apply (Hbidsw _ _ Hblkw)).
      destruct blocksw as [|[fw fbw] blocksw']; first done.
      iDestruct (big_sepL_lookup_acc with "Hchw") as "[Hblk Hrest]"; first exact Hblkw.
      iDestruct "Hblk" as "(Hn & Hb & Hsl)".
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
        iDestruct ("Hrest" with "[Hn Hb Hsl]") as "Hch"; first iFrame.
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
             %Hner & %Hcer & %Hhir & %Htir & %Hbidsr & %Hcfr & %Hwfr & Hchr)".
        iDestruct (own_valid_2 with "Hbar Hlb_blocks") as %[_ Hpfxr]%mono_list_both_dfrac_valid_L.
        assert (blocksr.*1 !! ci = Some cursor) as Hcir
          by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxr]).
        assert (∃ br, blocksr !! ci = Some (cursor, br)) as [br Hblkr].
        { rewrite list_lookup_fmap in Hcir.
          destruct (blocksr !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
        assert (br = Z.of_nat ci) as -> by (apply (Hbidsr _ _ Hblkr)).
        destruct blocksr as [|[fr fbr] blocksr']; first done.
        iDestruct (big_sepL_lookup_acc with "Hchr") as "[Hblk2 Hrest2]"; first exact Hblkr.
        iDestruct "Hblk2" as "(Hn2 & Hb2 & Hsl2)".
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
           iDestruct ("Hrest2" with "[Hn2 Hb2 Hsl2]") as "Hch2"; first iFrame.
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
           iDestruct ("Hrest2" with "[Hn2 Hb2 Hsl2]") as "Hch2"; first iFrame.
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
           %Hnen & %Hcen & %Hhin & %Htin & %Hbidsn & %Hcfn & %Hwfn & Hchn)".
      iDestruct (own_valid_2 with "Hban Hlb_blocks") as %[_ Hpfxn]%mono_list_both_dfrac_valid_L.
      assert (blocksn.*1 !! ci = Some cursor) as Hcin
        by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxn]).
      assert (∃ bn, blocksn !! ci = Some (cursor, bn)) as [bn Hblkn].
      { rewrite list_lookup_fmap in Hcin.
        destruct (blocksn !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
      assert (bn = Z.of_nat ci) as -> by (apply (Hbidsn _ _ Hblkn)).
      destruct blocksn as [|[fn fbn] blocksn']; first done.
      iDestruct (big_sepL_lookup_acc with "Hchn") as "[Hblk Hrest]"; first exact Hblkn.
      iDestruct "Hblk" as "(Hn & Hb & Hsl)".
      set (nxt := block_next ((fn,fbn)::blocksn') ci fn). wp_load.
      assert (∃ ni, ((fn,fbn)::blocksn').*1 !! ni = Some nxt) as [ni Hni].
      { unfold nxt, block_next.
        destruct (((fn,fbn)::blocksn') !! S ci) as [[? ?]|] eqn:?;
          [exists (S ci); rewrite list_lookup_fmap; rewrite Heqo; done | exists 0%nat; done]. }
      iDestruct (own_mono _ _ (◯ML (((fn,fbn)::blocksn').*1 : list (leibnizO loc))) with "Hban") as "#Hlbn".
      { apply mono_list_included. }
      iDestruct ("Hrest" with "[Hn Hb Hsl]") as "Hch"; first iFrame.
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
         %Hne & %Hce & %Hhi & %Hti & %Hbids & %Hcfresh & %Hwfresh & Hch)".
    wp_load.
    iDestruct (own_mono _ _ (◯ML (blocks.*1 : list (leibnizO loc))) with "Hba") as "#Hlb_blocks".
    { apply mono_list_included. }
    assert (∃ ci, blocks.*1 !! ci = Some tb) as Hcursor_in.
    { exists ti. rewrite list_lookup_fmap. rewrite Hti. done. }
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
         %Hblocks_ne & %Hcap_eq & %Hhi & %Hti & %Hbids & %Hcfresh & %Hwfresh & Hchain)".
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
      iFrame "Hauth1 Hblk_auth Hhead Htail Hclaims Hwrites Hlock Hhb Hh Htb Htail_loc Hcap".
      repeat iSplit; try (iPureIntro; first [done | lia]).
      { iPureIntro. intros k Hk. rewrite lookup_insert_ne; [apply Hwfresh; lia | lia]. }
      destruct blocks as [|[first bid] blocks']; first done.
      iApply (big_sepL_mono with "Hchain").
      iIntros (k [b bid'] Hlookup) "Hblock".
      unfold is_block. iDestruct "Hblock" as "(Hnext & Hbid & Hslots)".
      iFrame "Hnext Hbid".
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
             %Hnea & %Hcea & %Hhia & %Htia & %Hbidsa & %Hcfresha & %Hwfresha & Hcha)".
        destruct Hlva as [Hlv0|Hlv1].
        ** (* lock = 0, CAS succeeds *)
           replace lva with (0 : Z) by lia.
           wp_cmpxchg_suc. iModIntro.
           iSplitR "HΦ Hwtok".
           { iNext. iExists La,ha,ta,1%Z,hba,tba,capa,blocksa,hia,tia,Ca,Wa.
             iFrame. repeat iSplit; try (iPureIntro; first [done | lia | right; done]). }
           wp_pures.
           (* load tail pointer *)
           wp_bind (! _)%E.
           iInv "Hinv" as (Lb hb_ tb_ lvb hbb tbb capb blocksb hib tib Cb Wb)
             ">(Hab & Hbab & Hhb_ & Htb_ & Hclb & Hwrb & %Htb_eq & %Hhtb & Hlkb & %Hlvb &
                Hhbb & Hhlb & Htbb & Htlb & Hcapb &
                %Hneb & %Hceb & %Hhib_ & %Htib & %Hbidsb & %Hcfreshb & %Hwfreshb & Hchb)".
           wp_load. iModIntro.
           iSplitR "HΦ Hwtok".
           { iNext. iExists Lb,hb_,tb_,lvb,hbb,tbb,capb,blocksb,hib,tib,Cb,Wb. iFrame. done. }
           wp_pures.
           (* call grow loop *)
           wp_bind (chunked_queue_push_grow_loop _ _ _)%E.
           wp_apply (push_grow_loop_spec with "[$Hinv]").
           iIntros (new_tail grow_blocks) "[#Hlb_grow %Hnt_in]".
           destruct Hnt_in as [nt Hnt_lookup].
           wp_pures.
           (* store new tail *)
           wp_bind (_ <- _)%E.
           iInv "Hinv" as (Lc hc tc lvc hbc tbc capc blocksc hic tic Cc Wc)
             ">(Hac & Hbac & Hhc & Htc & Hclc & Hwrc & %Htc_eq & %Hhtc & Hlkc & %Hlvc &
                Hhbc & Hhlc & Htbc & Htlc & Hcapc &
                %Hnec & %Hcec & %Hhic & %Htic & %Hbidsc & %Hcfreshc & %Hwfreshc & Hchc)".
           iDestruct (own_valid_2 with "Hbac Hlb_grow") as %[_ Hpfx_grow]%mono_list_both_dfrac_valid_L.
           assert (blocksc.*1 !! nt = Some new_tail) as Hnt_fmap.
           { eapply prefix_lookup_Some; [|exact Hpfx_grow].
             rewrite list_lookup_fmap. rewrite Hnt_lookup. done. }
           assert (blocksc !! nt = Some (new_tail, Z.of_nat nt)) as Hnt_in_cur.
           { rewrite list_lookup_fmap in Hnt_fmap.
             destruct (blocksc !! nt) as [[? z]|] eqn:Heq; [|done].
             simpl in Hnt_fmap. simplify_eq.
             assert (z = Z.of_nat nt) as -> by (apply (Hbidsc _ _ Heq)). done. }
           wp_store. iModIntro.
           iSplitR "HΦ Hwtok".
           { iNext. iExists Lc,hc,tc,lvc,hbc,new_tail,capc,blocksc,hic,nt,Cc,Wc.
             iFrame. repeat iSplit; try (iPureIntro; first [done | lia]). }
           wp_pures.
           (* release lock: store 0 to lock *)
           wp_bind (release _)%E.
           unfold release. wp_pures.
           wp_bind (_ <- _)%E.
           iInv "Hinv" as (Ld hd td lvd hbd tbd capd blocksd hid tid Cd Wd)
             ">(Had & Hbad & Hhd & Htd & Hcld & Hwrd & %Htd_eq & %Hhtd & Hlkd & %Hlvd &
                Hhbd & Hhld & Htbd & Htld & Hcapd &
                %Hned & %Hced & %Hhid & %Htid & %Hbidsd & %Hcfreshd & %Hwfreshd & Hchd)".
           wp_store. iModIntro.
           iSplitR "HΦ Hwtok".
           { iNext. iExists Ld,hd,td,0%Z,hbd,tbd,capd,blocksd,hid,tid,Cd,Wd.
             iFrame. repeat iSplit; try (iPureIntro; first [done | lia | left; done]). }
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
  Admitted.

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
         %Hnei & %Hcei & %Hhii & %Htii & %Hbidsi & %Hcfreshi & %Hwfreshi & Hchi)".
    iDestruct (own_valid_2 with "Hbai Hlb_blocks") as %[_ Hpfx]%mono_list_both_dfrac_valid_L.
    assert (blocksi.*1 !! ci = Some cursor) as Hci_cur
      by (eapply prefix_lookup_Some; [exact Hci | exact Hpfx]).
    assert (∃ bid_i, blocksi !! ci = Some (cursor, bid_i)) as [bid_i Hcur_blk].
    { rewrite list_lookup_fmap in Hci_cur.
      destruct (blocksi !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
    assert (bid_i = Z.of_nat ci) as -> by (apply (Hbidsi _ _ Hcur_blk)).
    destruct blocksi as [|[firsti fbi] blocksi']; first done.
    iDestruct (big_sepL_lookup_acc with "Hchi") as "[Hblk Hrest]"; first exact Hcur_blk.
    iDestruct "Hblk" as "(Hnext & Hbid & Hslots)". wp_load.
    iDestruct ("Hrest" with "[Hnext Hbid Hslots]") as "Hchi"; first (iFrame).
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
           %Hnew & %Hcew & %Hhiw & %Htiw & %Hbidsw & %Hcfw & %Hwfw & Hchw)".
      iDestruct (own_valid_2 with "Hbaw Hlb_blocks") as %[_ Hpfxw]%mono_list_both_dfrac_valid_L.
      assert (blocksw.*1 !! ci = Some cursor) as Hciw
        by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxw]).
      assert (∃ bw, blocksw !! ci = Some (cursor, bw)) as [bw Hblkw].
      { rewrite list_lookup_fmap in Hciw.
        destruct (blocksw !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
      assert (bw = Z.of_nat ci) as -> by (apply (Hbidsw _ _ Hblkw)).
      destruct blocksw as [|[fw fbw] blocksw']; first done.
      iDestruct (big_sepL_lookup_acc with "Hchw") as "[Hblk Hrest]"; first exact Hblkw.
      iDestruct "Hblk" as "(Hn & Hb & Hsl)".
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
        iDestruct ("Hrest" with "[Hn Hb Hsl]") as "Hch"; first iFrame.
        iModIntro. iSplitR "Hclaim HΦ IH_wait".
        { iNext. iExists Lw,hw,tw,lvw,hbw,tbw,capw,((fw,fbw)::blocksw'),hiw,tiw,Cw,Ww. iFrame. done. }
        wp_pures.
        iApply ("IH_wait" with "Hclaim HΦ").
      + (* Writing *)
        iDestruct "H1" as "[% Hw1]". subst st.
        iDestruct ("Hsl_rest" with "[Hst Hw1]") as "Hsl".
        { iExists 1. iFrame. iRight. iLeft. iFrame. done. }
        iDestruct ("Hrest" with "[Hn Hb Hsl]") as "Hch"; first iFrame.
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
        iDestruct ("Hrest" with "[Hn Hb Hsl]") as "Hch"; first iFrame.
        iModIntro. iSplitR "Hv HΦ".
        { iNext. iExists Lw,hw,tw,lvw,hbw,tbw,capw,((fw,fbw)::blocksw'),hiw,tiw,Cw,Ww. iFrame. done. }
        wp_pures. wp_load. wp_pures.
        (* Store state ← 0 *)
        wp_bind (_ <- _)%E.
        iInv "Hinv" as (Lr hr tr lvr hbr tbr capr blocksr hir tir Cr Wr)
          ">(Har & Hbar & Hhr & Htr & Hclr & Hwrr & %Htr & %Hhtr & Hlkr & %Hlvr &
             Hhbr & Hhlr & Htbr & Htlr & Hcpr &
             %Hner & %Hcer & %Hhir & %Htir & %Hbidsr & %Hcfr & %Hwfr & Hchr)".
        iDestruct (own_valid_2 with "Hbar Hlb_blocks") as %[_ Hpfxr]%mono_list_both_dfrac_valid_L.
        assert (blocksr.*1 !! ci = Some cursor) as Hcir
          by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxr]).
        assert (∃ br, blocksr !! ci = Some (cursor, br)) as [br Hblkr].
        { rewrite list_lookup_fmap in Hcir.
          destruct (blocksr !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
        assert (br = Z.of_nat ci) as -> by (apply (Hbidsr _ _ Hblkr)).
        destruct blocksr as [|[fr fbr] blocksr']; first done.
        iDestruct (big_sepL_lookup_acc with "Hchr") as "[Hblk Hrest2]"; first exact Hblkr.
        iDestruct "Hblk" as "(Hn2 & Hb2 & Hsl2)".
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
           iDestruct ("Hrest2" with "[Hn2 Hb2 Hsl2]") as "Hch2"; first iFrame.
           iModIntro. iSplitR "HΦ".
           { iNext. iExists Lr,hr,tr,lvr,hbr,tbr,capr,((fr,fbr)::blocksr'),hir,tir,Cr,Wr. iFrame. done. }
           wp_pures. iApply "HΦ". iLeft. done.
        ** iDestruct "H2r" as "[_ Hvr]". iDestruct "Hvr" as (v') "(Hvr & _ & _)".
           by iDestruct (pointsto_ne with "Hv Hvr") as %[].
        ** iDestruct "H3r" as "(% & Hclr2 & _)". subst str. wp_store.
           iDestruct ("Hsl2_rest" with "[Hstr Hv]") as "Hsl2".
           { iExists 0. iFrame. iLeft. iSplit; [done|]. iExists d. iFrame. }
           iDestruct ("Hrest2" with "[Hn2 Hb2 Hsl2]") as "Hch2"; first iFrame.
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
           %Hnen & %Hcen & %Hhin & %Htin & %Hbidsn & %Hcfn & %Hwfn & Hchn)".
      iDestruct (own_valid_2 with "Hban Hlb_blocks") as %[_ Hpfxn]%mono_list_both_dfrac_valid_L.
      assert (blocksn.*1 !! ci = Some cursor) as Hcin
        by (eapply prefix_lookup_Some; [exact Hci | exact Hpfxn]).
      assert (∃ bn, blocksn !! ci = Some (cursor, bn)) as [bn Hblkn].
      { rewrite list_lookup_fmap in Hcin.
        destruct (blocksn !! ci) as [[? ?]|]; [simpl in *; simplify_eq; eauto|done]. }
      assert (bn = Z.of_nat ci) as -> by (apply (Hbidsn _ _ Hblkn)).
      destruct blocksn as [|[fn fbn] blocksn']; first done.
      iDestruct (big_sepL_lookup_acc with "Hchn") as "[Hblk Hrest]"; first exact Hblkn.
      iDestruct "Hblk" as "(Hn & Hb & Hsl)".
      set (nxt := block_next ((fn,fbn)::blocksn') ci fn). wp_load.
      assert (∃ ni, ((fn,fbn)::blocksn').*1 !! ni = Some nxt) as [ni Hni].
      { unfold nxt, block_next.
        destruct (((fn,fbn)::blocksn') !! S ci) as [[? ?]|] eqn:?;
          [exists (S ci); rewrite list_lookup_fmap; rewrite Heqo; done | exists 0%nat; done]. }
      iDestruct (own_mono _ _ (◯ML (((fn,fbn)::blocksn').*1 : list (leibnizO loc))) with "Hban") as "#Hlbn".
      { apply mono_list_included. }
      iDestruct ("Hrest" with "[Hn Hb Hsl]") as "Hch"; first iFrame.
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
         %Hnef & %Hcef & %Hhif & %Htif & %Hbidsf & %Hcfreshf & %Hwfreshf & Hchf)".
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
         %Hne1 & %Hce1 & %Hhi1 & %Hti1 & %Hbids1 & %Hcfresh1 & %Hwfresh1 & Hch1)".
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
         %Hne2 & %Hce2 & %Hhi2 & %Hti2 & %Hbids2 & %Hcfresh2 & %Hwfresh2 & Hch2)".
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
           %Hne3 & %Hce3 & %Hhi3 & %Hti3 & %Hbids3 & %Hcfresh3 & %Hwfresh3 & Hch3)".
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
                    %Hnea & %Hcea & %Hhia & %Htia & %Hbidsa & %Hcfresha & %Hwfresha & Hcha)".
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
                    %Hneb & %Hceb & %Hhib & %Htib & %Hbidsb & %Hcfreshb & %Hwfreshb & Hchb)".
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
               iDestruct "Hblk" as "(Hnext_b & Hbid_b & Hslots_b)".
               wp_load.
               iDestruct ("Hchb_rest" with "[Hnext_b Hbid_b Hslots_b]") as "Hchb".
               { unfold is_block. iFrame. }
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
                        %Hnec & %Hcec & %Hhic & %Htic & %Hbidsc & %Hcfreshc & %Hwfreshc & Hchc)".
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
                   iDestruct "Hblk_c" as "(Hnext_c & Hbid_c & Hslots_c)".
                   wp_load.
                   iDestruct ("Hchc_rest" with "[Hnext_c Hbid_c Hslots_c]") as "Hchc".
                   { unfold is_block. iFrame. }
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
                        %Hned & %Hced & %Hhid & %Htid & %Hbidsd & %Hcfreshd & %Hwfreshd & Hchd)".
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
