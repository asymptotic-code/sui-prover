module 0x42::inv_types_detection;

use sui::balance::{Self, Balance};
use sui::sui::SUI;
use sui::table::{Self, Table};

public struct StakingPoolWrap has key, store {
    id: UID,
    pool: StakingPool,
}

public struct StakingPool has store {
    activation_epoch: Option<u64>,
    deactivation_epoch: Option<u64>,
    sui_balance: u64,
    rewards_pool: Balance<SUI>,
    pool_token_balance: u64,
    exchange_rates: Table<u64, PoolTokenExchangeRate>,
    pending_stake: u64,
    pending_total_sui_withdraw: u64,
    pending_pool_token_withdraw: u64,
}

public struct PoolTokenExchangeRate has store, copy, drop {
    sui_amount: u64,
    pool_token_amount: u64,
}

public struct StakedSui has key, store {
    id: UID,
    pool_id: ID,
    stake_activation_epoch: u64,
}

public(package) fun new_staking_pool(
    exchange_rates: Table<u64, PoolTokenExchangeRate>,
): StakingPool {
    StakingPool {
        activation_epoch: option::none(),
        deactivation_epoch: option::none(),
        sui_balance: 0,
        rewards_pool: balance::zero(),
        pool_token_balance: 0,
        exchange_rates,
        pending_stake: 0,
        pending_total_sui_withdraw: 0,
        pending_pool_token_withdraw: 0,
    }
}

public(package) fun new(ctx: &mut TxContext): StakingPoolWrap {
    let exchange_rates = table::new(ctx);
    StakingPoolWrap {
        id: object::new(ctx),
        pool: new_staking_pool(exchange_rates),
    }
}

public fun is_preactive(pw: &StakingPoolWrap): bool{
    pw.pool.activation_epoch.is_none()
}

public fun is_equal_staking_metadata(self: &StakedSui, other: &StakedSui): bool {
    (self.pool_id == other.pool_id) &&
    (self.stake_activation_epoch == other.stake_activation_epoch)
}

public fun pool_token_exchange_rate_at_epoch(pw: &StakingPoolWrap, epoch: u64): PoolTokenExchangeRate {
    if (is_preactive_at_epoch(pw, epoch)) {
        return initial_exchange_rate()
    };
    let clamped_epoch = pw.pool.deactivation_epoch.get_with_default(epoch);
    let mut epoch = clamped_epoch.min(epoch);
    let activation_epoch = *pw.pool.activation_epoch.borrow();
    while (epoch >= activation_epoch) {
        if (pw.pool.exchange_rates.contains(epoch)) {
            return pw.pool.exchange_rates[epoch]
        };
        epoch = epoch - 1;
    };
    initial_exchange_rate()
}

fun is_preactive_at_epoch(pw: &StakingPoolWrap, epoch: u64): bool{
    is_preactive(pw) || (*pw.pool.activation_epoch.borrow() > epoch)
}

fun initial_exchange_rate(): PoolTokenExchangeRate {
    PoolTokenExchangeRate { sui_amount: 0, pool_token_amount: 0 }
}

#[spec_only]
use prover::prover::requires;

#[spec(prove, no_opaque)]
public fun is_equal_staking_metadata_spec(self: &StakedSui, other: &StakedSui): bool {
    is_equal_staking_metadata(self, other)
}

#[spec_only]
public fun activation_epoch_is_positive(pw: &StakingPoolWrap): bool {
    pw.pool.activation_epoch.is_some() &&
    *pw.pool.activation_epoch.borrow() > 0
}

#[spec()]
public fun pool_token_exchange_rate_at_epoch_spec(
    pw: &StakingPoolWrap,
    epoch: u64,
): PoolTokenExchangeRate {
    requires(!pw.is_preactive());
    requires(activation_epoch_is_positive(pw));
    pool_token_exchange_rate_at_epoch(pw, epoch)
}


#[spec_only(inv_target=std::option::Option)]
fun Option_inv<T>(self: &Option<T>): bool {
    if (self.is_some()) {
        let o = prover::prover::val(self.borrow());
        let x = std::option::some(o);
        let b = self == x;
        prover::prover::drop(x);
        b
    } else {
        true
    }
}
