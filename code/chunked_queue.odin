package chunked_queue

import "core:sync"
import "core:testing"

//
// How the queue works:
// - the queue is a list of contiguous blocks.
// - head_block (resp tail_block) contains a pointer to the head block of the queue.
// - head_idx is the index of the head element (next pop index).
// - tail_idx is the index after the last inserted element (next push index).
// - head_idx and tail_idx are monolitic counters
//   - block_id = head_idx / CHUNKED_QUEUE_BLOCK_SIZE,
//   - index_in_block = head_idx % CHUNKED_QUEUE_BLOCK_SIZE
// - When pushing, if the tail block is full, a new block is allocated and added to the queue.
// - A block is never removed from the queue (they form a circular linked list).
// - The following rule must be satisfied when pushing:
//   @inv: if (queue.tail_idx % CHUNKED_QUEUE_BLOCK_SIZE) < (queue.head_idx % CHUNKED_QUEUE_BLOCK_SIZE) then queue.tail_block != queue.head_block
//
// [....xxxx] -> [xxxxxxxx] -> [xx......]
//      ^                         ^
//      head                      tail
//

CHUNKED_QUEUE_BLOCK_SIZE :: 64

// @inv(Slot Ownership):
// The state of the slot dictates memory permissions in Separation Logic:
// - Empty: The queue invariant owns the state. No thread has permission to
//          read/write `value`.
// - Writing: The producer thread holds exclusive permission (`value ↦ _`) to
//            write. The queue invariant does NOT own `value`.
// - Valid: The producer has relinquished permission. The queue invariant now
//          owns `value ↦ data`, and `data` maps to the corresponding logical
//          index in the ghost state.
Slot_State :: enum {
	Empty,   // Ready for a producer to claim
	Writing, // Producer is writing (do not read)
	Valid,   // Data is written and ready for consumer
}

Chunked_Queue_Slot :: struct($T: typeid) {
	value: T,
	state: Slot_State,
}

Chunked_Queue_Block :: struct($T: typeid) {
	next: ^Chunked_Queue_Block(T),
	block_id: u64,
	empty_count: int,
	data: [CHUNKED_QUEUE_BLOCK_SIZE]Chunked_Queue_Slot(T),
}

// @inv(Queue State):
// - Ghost state: An authoritative append-only list `L` representing the
//                logical history of all pushed elements.
// - `tail_idx` is a monotonically increasing ticket counter. Its value equals
//   the length of `L`.
// - `head_idx` is a monotonically increasing ticket counter representing the
//   number of popped elements.
Chunked_Queue :: struct($T: typeid) #align(64) {
	grow_mutex: sync.Mutex,
	head_block: ^Chunked_Queue_Block(T),
	head_idx: int,
	_pad0: [64 - size_of(sync.Mutex) - size_of(^Chunked_Queue_Block(T)) - size_of(int)]u8,
	tail_block: ^Chunked_Queue_Block(T),
	tail_idx: int,
	_pad1: [64 - size_of(^Chunked_Queue_Block(T)) - size_of(int)]u8,
	capacity: uint,
}

chunked_queue_init :: proc(queue: ^Chunked_Queue($T)) {
	block, _ := new(Chunked_Queue_Block(T))
	block.next = block
	block.block_id = 0
	queue.head_block = block
	queue.tail_block = block
	queue.head_idx = 0
	queue.tail_idx = 0
	queue.capacity = CHUNKED_QUEUE_BLOCK_SIZE
}

//
// @spec: logically atomic push that appends `data` to the ghost state list `L`.
// @linpoint: The atomic FAA on `queue.tail_idx`.
//
chunked_queue_push :: proc(queue: ^Chunked_Queue($T), data: T) {
	// @inv: if (queue.tail_idx % CHUNKED_QUEUE_BLOCK_SIZE) < (queue.head_idx % CHUNKED_QUEUE_BLOCK_SIZE) then queue.tail_block != queue.head_block
	pos := sync.atomic_add_explicit(&queue.tail_idx, 1, .Release)
	block_id := u64(pos / CHUNKED_QUEUE_BLOCK_SIZE)
	slot_idx := pos % CHUNKED_QUEUE_BLOCK_SIZE

	if slot_idx == 0 && pos > 0 {
		sync.mutex_lock(&queue.grow_mutex)
		tail := sync.atomic_load_explicit(&queue.tail_block, .Relaxed)
		for tail.block_id < block_id {
			next := tail.next
			if sync.atomic_load_explicit(&next.empty_count, .Acquire) == CHUNKED_QUEUE_BLOCK_SIZE {
				sync.atomic_store_explicit(&next.empty_count, 0, .Release)
				next.block_id = tail.block_id + 1
				tail = next
			} else {
				new_block, _ := new(Chunked_Queue_Block(T))
				new_block.block_id = tail.block_id + 1
				new_block.next = tail.next
				sync.atomic_store_explicit(&tail.next, new_block, .Release)
				tail = new_block
				queue.capacity += CHUNKED_QUEUE_BLOCK_SIZE
			}
		}
		sync.atomic_store_explicit(&queue.tail_block, tail, .Release)
		sync.mutex_unlock(&queue.grow_mutex)
	}

	for {
		cursor := sync.atomic_load_explicit(&queue.tail_block, .Acquire)
		start := cursor
		for {
			if cursor.block_id == block_id {
				slot := &cursor.data[slot_idx]
				sync.atomic_store_explicit(&slot.state, .Writing, .Relaxed)
				slot.value = data
				sync.atomic_store_explicit(&slot.state, .Valid, .Release)
				return
			}
			cursor = cursor.next
			if cursor == start { break }
		}
		sync.cpu_relax()
	}
}

//
// @spec: logically atomic pop that removes `data` from the ghost state list `L`.
// @linpoint: The atomic FAA on `queue.head_idx`.
//
chunked_queue_pop :: proc(queue: ^Chunked_Queue($T)) -> (data: T, poped: bool) {
	pos: int
	for {
		head := sync.atomic_load_explicit(&queue.head_idx, .Acquire)
		tail := sync.atomic_load_explicit(&queue.tail_idx, .Acquire)
		if head >= tail {
			return data, false
		}
		_, ok := sync.atomic_compare_exchange_weak_explicit(
			&queue.head_idx, head, head + 1, .Acq_Rel, .Relaxed,
		)
		if ok {
			pos = head
			break
		}
	}

	block_id := u64(pos / CHUNKED_QUEUE_BLOCK_SIZE)
	slot_idx := pos % CHUNKED_QUEUE_BLOCK_SIZE

	if slot_idx == 0 && pos > 0 {
		for {
			old_head := sync.atomic_load_explicit(&queue.head_block, .Acquire)
			if old_head.block_id >= block_id { break }
			next := old_head.next
			sync.atomic_compare_exchange_weak_explicit(
				&queue.head_block, old_head, next, .Release, .Relaxed,
			)
		}
	}

	for {
		cursor := sync.atomic_load_explicit(&queue.head_block, .Acquire)
		start := cursor
		for {
			if cursor.block_id == block_id {
				slot := &cursor.data[slot_idx]
				for sync.atomic_load_explicit(&slot.state, .Acquire) != .Valid {
					sync.cpu_relax()
				}
				data = slot.value
				sync.atomic_store_explicit(&slot.state, .Empty, .Release)
				sync.atomic_add_explicit(&cursor.empty_count, 1, .Release)
				return data, true
			}
			cursor = cursor.next
			if cursor == start { break }
		}
		sync.cpu_relax()
	}
}

chunked_queue_destroy :: proc(queue: ^Chunked_Queue($T)) {
	if queue.head_block == nil { return }
	cursor := queue.head_block.next
	for cursor != queue.head_block {
		next := cursor.next
		free(cursor)
		cursor = next
	}
	free(queue.head_block)
	queue.head_block = nil
	queue.tail_block = nil
}

chunked_queue_size :: proc(queue: ^Chunked_Queue($T)) -> int {
	tail := sync.atomic_load_explicit(&queue.tail_idx, .Relaxed)
	head := sync.atomic_load_explicit(&queue.head_idx, .Relaxed)
	return max(0, tail - head)
}

@(test)
test_chunked_queue :: proc(t: ^testing.T) {
	q: Chunked_Queue(int)
	chunked_queue_init(&q)
	defer chunked_queue_destroy(&q)

	{
		_, ok := chunked_queue_pop(&q)
		testing.expect(t, !ok, "pop from empty queue should return false")
	}

	chunked_queue_push(&q, 42)
	{
		val, ok := chunked_queue_pop(&q)
		testing.expect(t, ok, "pop should succeed after push")
		testing.expect_value(t, val, 42)
	}

	for i in 0 ..< 10 {
		chunked_queue_push(&q, i)
	}
	for i in 0 ..< 10 {
		val, ok := chunked_queue_pop(&q)
		testing.expect(t, ok, "pop should succeed")
		testing.expect_value(t, val, i)
	}

	for i in 0 ..< 200 {
		chunked_queue_push(&q, i)
	}
	testing.expect_value(t, chunked_queue_size(&q), 200)
	for i in 0 ..< 200 {
		val, ok := chunked_queue_pop(&q)
		testing.expect(t, ok, "pop should succeed after growth")
		testing.expect_value(t, val, i)
	}

	{
		_, ok := chunked_queue_pop(&q)
		testing.expect(t, !ok, "pop from drained queue should return false")
	}
	testing.expect_value(t, chunked_queue_size(&q), 0)
}
