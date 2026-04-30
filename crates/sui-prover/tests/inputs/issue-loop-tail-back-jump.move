module 0x42::loop_tail_back_jump;

// Regression: a function whose stackless bytecode ends with an unconditional
// back-jump (infinite `loop { ... }` whose only exits are mid-loop returns)
// used to panic the CFG reconstruction's collect_blocks assertion.
fun search(needle: u64, limit: u64): u64 {
    let mut i: u64 = 0;
    loop {
        if (i == needle) return i;
        if (i == limit) return 0;
        i = i + 1;
    }
}

#[spec(prove, ignore_abort)]
fun search_spec(needle: u64, limit: u64): u64 {
    search(needle, limit)
}
