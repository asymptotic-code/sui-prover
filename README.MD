# Sui Prover

A tool for verifying the correctness of Move smart contracts on the Sui blockchain. Based on the Boogie verification engine and the Z3 SMT solver.

Go to [Sui Prover Documentation](https://info.asymptotic.tech/sui-prover) for more information.

## Quick Start

### Install from brew

```bash
brew install asymptotic-code/sui-prover/sui-prover
```

## Basic Usage

Write specifications for your smart contract that the Sui Prover will verify.

### Package Layout

Keep the implementation and specifications in sibling Move packages. The spec
package depends on the implementation package:

```text
workspace/
├── project/
│   ├── Move.toml
│   └── sources/
└── specs/
    ├── Move.toml       # local dependency on ../project
    └── sources/        # specification modules
```

Use `target` to specify implementation functions. When specifications need
private implementation state, expose it through `#[test_only]` accessor
functions in the implementation module and call them with method syntax.

### Specification Structure

```move
#[spec(prove, target = project::module::function)]
fun function_spec<T>(args): ReturnType {
    // Preconditions on arguments
    
    let result = original_function(args);
    
    // Postconditions that must hold
    
    result
}
```

### Example

Consider a simplified LP (Liquidity Pool) smart contract:

```move
module amm::simple_lp;

use sui::balance::{Balance, Supply, zero};

public struct LP<phantom T> has drop {}

public struct Pool<phantom T> has store {
    balance: Balance<T>,
    shares: Supply<LP<T>>,
}

public fun withdraw<T>(pool: &mut Pool<T>, shares_in: Balance<LP<T>>): Balance<T> {
    if (shares_in.value() == 0) {
        shares_in.destroy_zero();
        return zero()
    };

    let balance = pool.balance.value();
    let shares = pool.shares.supply_value();

    let balance_to_withdraw = (((shares_in.value() as u128) * (balance as u128)) / (shares as u128)) as u64;

    pool.shares.decrease_supply(shares_in);
    pool.balance.split(balance_to_withdraw)
}

#[test_only]
#[ext(pure)]
public fun balance_value<T>(self: &Pool<T>): u64 {
    self.balance.value()
}

#[test_only]
#[ext(pure)]
public fun shares_value<T>(self: &Pool<T>): u64 {
    self.shares.supply_value()
}
```

### Example Specification

A specification to verify that the price of a share doesn't decrease when withdrawing funds:

```move
module amm_specs::simple_lp_specs;

use amm::simple_lp::{LP, Pool};
use sui::balance::Balance;

#[spec_only]
use prover::prover::{clone, ensures, requires};

#[spec(prove, target = amm::simple_lp::withdraw)]
fun withdraw_spec<T>(pool: &mut Pool<T>, shares_in: Balance<LP<T>>): Balance<T> {
    requires(shares_in.value() <= pool.shares_value());

    let old_pool = clone!(pool);

    let result = pool.withdraw(shares_in);

    let old_balance = old_pool.balance_value().to_int();
    let new_balance = pool.balance_value().to_int();

    let old_shares = old_pool.shares_value().to_int();
    let new_shares = pool.shares_value().to_int();

    ensures(new_shares.mul(old_balance).lte(old_shares.mul(new_balance)));

    result
}
```

## Running the Sui Prover

Run against the specification package:

```bash
sui-prover --path ./specs
```

## Claude Code Integration

Install the Sui Prover skill for [Claude Code](https://docs.anthropic.com/en/docs/claude-code) to get AI-assisted specification writing, verification debugging, and prover guidance.

Add the plugin source:
```
/plugin marketplace add asymptotic-code/sui-prover
```

Install the plugin:
```
/plugin install sui-prover@sui-prover
```

Once installed, Claude Code can help you write specifications, run the prover, and debug verification failures using the `/sui-prover` command.

## See Also

[Sui Prover Documentation](https://info.asymptotic.tech/sui-prover)
