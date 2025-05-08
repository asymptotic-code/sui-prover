module specs::event_spec;

use sui::event::emit;

#[spec(target = sui::event::emit)]
public fun emit_spec<T: copy + drop>(event: T) {
    emit(event)
}
