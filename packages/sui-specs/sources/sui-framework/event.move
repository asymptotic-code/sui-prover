#[spec_only]
module specs::event_spec;

use sui::event::{emit, num_events, events_by_type};

#[spec(target = sui::event::emit)]
public fun emit_spec<T: copy + drop>(event: T) {
    emit(event)
}

#[spec(target = sui::event::num_events)]
public fun num_events_spec(): u32 {
    num_events()
}

#[spec(target = sui::event::events_by_type)]
public fun events_by_type_spec<T: copy + drop>(): vector<T> {
    events_by_type<T>()
}
