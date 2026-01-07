function {:inline} $42_foo_as_vector'u64'$pure(q: $42_foo_Queue'u64'): Vec (int) {
    q->$contents
}

procedure {:inline 1} $42_foo_as_vector'u64'(q: $42_foo_Queue'u64') returns (ret: Vec (int)) {
    ret := q->$contents;
}
