module specs::nitro_attestation_spec;

use sui::nitro_attestation::{NitroAttestationDocument, load_nitro_attestation_internal};

#[spec(target = sui::nitro_attestation::load_nitro_attestation_internal)]
public fun load_nitro_attestation_internal_spec(
    attestation: &vector<u8>,
    current_timestamp: u64,
): NitroAttestationDocument {
    load_nitro_attestation_internal(attestation, current_timestamp)
}
