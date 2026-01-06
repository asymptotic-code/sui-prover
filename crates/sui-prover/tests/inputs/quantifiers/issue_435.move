module 0x42::foo;

public struct Queue<T: store> has store {
    contents: vector<T>,
    head: u64,
    tail: u64,
}

#[spec_only, ext(pure)]
fun queue_borrow_or_default(queue: &Queue<u64>, i: u64): u64 {
    if (i < queue.contents.length()) {
        queue.contents[i]
    } else {
        0
    }
}

#[spec_only, ext(pure)]
fun queue_as_vector(queue: &Queue<u64>): &vector<u64> {
    prover::vector_iter::range_map!(queue.head, queue.tail, |i| queue_borrow_or_default(queue, i))
}

#[spec_only, ext(pure)]
fun foo_spec(queue: &Queue<u64>): &vector<u64> {
    queue_as_vector(queue)
}
