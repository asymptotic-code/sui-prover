// Pure function declarations for sui::tx_context native functions
// These are needed because the prover generates calls to $pure variants
// when verifying spec functions that call these native functions

function {:inline} $2_tx_context_native_sender$pure(): int;

function {:inline} $2_tx_context_native_epoch$pure(): int;

function {:inline} $2_tx_context_native_epoch_timestamp_ms$pure(): int;

function {:inline} $2_tx_context_fresh_id$pure(): int;

function {:inline} $2_tx_context_native_rgp$pure(): int;

function {:inline} $2_tx_context_native_gas_price$pure(): int;

function {:inline} $2_tx_context_native_ids_created$pure(): int;

function {:inline} $2_tx_context_native_gas_budget$pure(): int;

function {:inline} $2_tx_context_last_created_id$pure(): int;

function {:inline} $2_tx_context_native_sponsor$pure(): Vec (int);
