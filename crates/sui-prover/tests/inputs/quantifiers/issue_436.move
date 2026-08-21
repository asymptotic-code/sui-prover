module 0x42::foo;

public struct Queue<T: copy + drop + store> has store {
    contents: vector<T>,
    head: u64,
    tail: u64,
}

#[mode(spec), ext(pure)]
native fun as_vector<T: copy + drop + store>(queue: &Queue<T>): &vector<T>;

#[mode(spec), ext(axiom)]
#[allow(unused_function)]
fun as_vector_definition<T: copy + drop + store>(queue: &Queue<T>, i: u64): bool {
    queue.head <= queue.contents.length() &&
    queue.tail <= queue.contents.length() &&
    queue.head <= queue.tail &&
    queue.as_vector().length() == queue.tail - queue.head &&
    if (i < queue.as_vector().length()) {
        queue.as_vector()[i] == queue.contents[i + queue.head]
    } else {
        true
    }
}

#[mode(spec), ext(pure)]
fun foo(queue: &Queue<u64>): &vector<u64> {
    as_vector(queue)
}

#[spec(prove)]
fun foo_spec(queue: &Queue<u64>): &vector<u64> {
    foo(queue)
}
