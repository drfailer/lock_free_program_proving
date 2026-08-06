From iris.heap_lang Require Import lang proofmode notation.

Definition CHUNKED_QUEUE_BLOCK_SIZE : Z := 64.
Definition CHUNKED_QUEUE_BLOCK_ALLOC_SIZE : Z := 2 + 2 * CHUNKED_QUEUE_BLOCK_SIZE.

Definition chunked_queue_init : val :=
  λ: "queue",
    let: "block" := AllocN #CHUNKED_QUEUE_BLOCK_ALLOC_SIZE #0 in
    "block" +ₗ #0 <- "block";;
    "block" +ₗ #1 <- #0;;
    "queue" +ₗ #0 <- #();;
    "queue" +ₗ #1 <- "block";;
    "queue" +ₗ #2 <- #0;;
    "queue" +ₗ #3 <- "block";;
    "queue" +ₗ #4 <- #0;;
    "queue" +ₗ #5 <- #CHUNKED_QUEUE_BLOCK_SIZE;;
    #().

Definition chunked_queue_push_find_block : val :=
  rec: "find" "cursor" "start" "block_id" "slot_idx" "data" :=
    if: !"cursor" +ₗ #1 = "block_id"
    then
      let: "slot_base" := #2 + #2 * "slot_idx" in
      "cursor" +ₗ ("slot_base" + #1) <- #1;;
      "cursor" +ₗ ("slot_base" + #1) <- #2;;
      "cursor" +ₗ ("slot_base" + #0) <- "data";;
      #()
    else
      let: "next" := !"cursor" +ₗ #0 in
      if: "next" = "start"
      then "find" "cursor" "start" "block_id" "slot_idx" "data"
      else "find" "next" "start" "block_id" "slot_idx" "data".

Definition chunked_queue_push_find_block_loop : val :=
  rec: "loop" "queue" "block_id" "slot_idx" "data" :=
    let: "cursor" := !"queue" +ₗ #4 in
    let: "start" := "cursor" in
    chunked_queue_push_find_block "cursor" "start" "block_id" "slot_idx" "data";;
    #().

Definition chunked_queue_push_grow_loop : val :=
  rec: "grow" "tail" "block_id" :=
    if: !"tail" +ₗ #1 < "block_id"
    then
      let: "new_block" := AllocN #CHUNKED_QUEUE_BLOCK_ALLOC_SIZE #0 in
      "new_block" +ₗ #1 <- (!"tail" +ₗ #1 + #1);;
      "new_block" +ₗ #0 <- !"tail" +ₗ #0;;
      "tail" +ₗ #0 <- "new_block";;
      "grow" "new_block" "block_id"
    else #().

Definition chunked_queue_push : val :=
  λ: "queue" "data",
    let: "pos" := FAA ("queue" +ₗ #4) #1 in
    let: "block_id" := "pos" `quot` #CHUNKED_QUEUE_BLOCK_SIZE in
    let: "slot_idx" := "pos" `rem` #CHUNKED_QUEUE_BLOCK_SIZE in
    if: ("slot_idx" = #0) && (#0 < "pos")
    then
      let: "tail" := !"queue" +ₗ #4 in
      chunked_queue_push_grow_loop "tail" "block_id";;
      "queue" +ₗ #4 <- "tail";;
      #()
    else #();;
    chunked_queue_push_find_block_loop "queue" "block_id" "slot_idx" "data";;
    #().

Definition chunked_queue_pop_cas_loop : val :=
  rec: "loop" "queue" :=
    let: "head" := !"queue" +ₗ #2 in
    let: "tail" := !"queue" +ₗ #4 in
    if: "tail" ≤ "head"
    then InjL #()
    else
      if: CAS ("queue" +ₗ #2) "head" ("head" + #1)
      then InjR "head"
      else "loop" "queue".

Definition chunked_queue_pop_advance_head_loop : val :=
  rec: "loop" "queue" "block_id" :=
    let: "old_head" := !"queue" +ₗ #1 in
    if: "block_id" ≤ !"old_head" +ₗ #1
    then #()
    else
      let: "next" := !"old_head" +ₗ #0 in
      CAS ("queue" +ₗ #1) "old_head" "next";;
      "loop" "queue" "block_id".

Definition chunked_queue_pop_find_slot : val :=
  rec: "find" "cursor" "start" "block_id" "slot_idx" :=
    if: !"cursor" +ₗ #1 = "block_id"
    then
      let: "slot_base" := #2 + #2 * "slot_idx" in
      (rec: "wait" <> :=
        if: !"cursor" +ₗ ("slot_base" + #1) = #2
        then #()
        else "wait" #()) #();;
      let: "data" := !"cursor" +ₗ ("slot_base" + #0) in
      "cursor" +ₗ ("slot_base" + #1) <- #0;;
      "data"
    else
      let: "next" := !"cursor" +ₗ #0 in
      if: "next" = "start"
      then "find" "cursor" "start" "block_id" "slot_idx"
      else "find" "next" "start" "block_id" "slot_idx".

Definition chunked_queue_pop_find_slot_loop : val :=
  rec: "loop" "queue" "block_id" "slot_idx" :=
    let: "cursor" := !"queue" +ₗ #1 in
    let: "start" := "cursor" in
    chunked_queue_pop_find_slot "cursor" "start" "block_id" "slot_idx".

Definition chunked_queue_pop : val :=
  λ: "queue",
    match: chunked_queue_pop_cas_loop "queue" with
      InjL <> => (InjL #(), #false)
    | InjR "pos" =>
      let: "block_id" := "pos" `quot` #CHUNKED_QUEUE_BLOCK_SIZE in
      let: "slot_idx" := "pos" `rem` #CHUNKED_QUEUE_BLOCK_SIZE in
      if: ("slot_idx" = #0) && (#0 < "pos")
      then chunked_queue_pop_advance_head_loop "queue" "block_id"
      else #();;
      let: "data" := chunked_queue_pop_find_slot_loop "queue" "block_id" "slot_idx" in
      (InjR "data", #true)
    end.

Definition chunked_queue_destroy_loop : val :=
  rec: "loop" "cursor" "head" :=
    if: "cursor" = "head"
    then #()
    else
      let: "next" := !"cursor" +ₗ #0 in
      Free #CHUNKED_QUEUE_BLOCK_ALLOC_SIZE "cursor";;
      "loop" "next" "head".

Definition chunked_queue_destroy : val :=
  λ: "queue",
    let: "head" := !"queue" +ₗ #1 in
    if: "head" = #0
    then #()
    else
      let: "cursor" := !"head" +ₗ #0 in
      chunked_queue_destroy_loop "cursor" "head";;
      Free #CHUNKED_QUEUE_BLOCK_ALLOC_SIZE "head";;
      "queue" +ₗ #1 <- #0;;
      "queue" +ₗ #4 <- #0;;
      #().

Definition chunked_queue_size : val :=
  λ: "queue",
    let: "tail" := !"queue" +ₗ #4 in
    let: "head" := !"queue" +ₗ #2 in
    if: "head" < "tail"
    then "tail" - "head"
    else #0.
