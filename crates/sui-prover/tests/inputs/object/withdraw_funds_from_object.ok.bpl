// `protocol_config::is_feature_enabled` is not modelled by the prover; the
// feature gating `balance::withdraw_funds_from_object` is enabled on-chain.
procedure {:inline 1} $2_protocol_config_is_feature_enabled($feature: Vec int) returns ($ret: bool)
{
    $ret := true;
}
