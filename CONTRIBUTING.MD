# Contributing to Sui Prover

Sui Prover is a formal verification tool for Move smart contracts on the Sui blockchain. This guide will help you set up your development environment and contribute to the project.

## Prerequisites

The following dependencies are required:
- [Rust](https://www.rust-lang.org/tools/install) (latest stable)
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3)
- [.NET 8 SDK](https://dotnet.microsoft.com/download/dotnet/8.0) (required for Boogie)
- [Boogie](https://github.com/boogie-org/boogie) verification framework

### macOS Installation (using Homebrew)

```bash
# Install .NET 8 and Z3
brew install dotnet@8 z3

# Set environment variables
export DOTNET_ROOT="$(brew --prefix dotnet@8)/libexec"
export PATH="$DOTNET_ROOT/bin:$PATH"

# Install Boogie
git clone --branch master https://github.com/boogie-org/boogie.git boogie-src
cd boogie-src
dotnet build Source/Boogie.sln -c Release

export BOOGIE_EXE=$(which boogie)
export Z3_EXE=$(which z3)

```

## Installation

```bash
# Install Sui Prover
cargo install --locked --path ./crates/sui-prover
```

## Usage

```bash
# Basic usage
sui-prover [OPTIONS]
```

## Testing

```bash
# Run tests
cd crates/sui-prover
cargo test
```

## Debugging

Use this VSCode launch configuration for debugging:

```json
{
    "version": "0.2.0",
    "configurations": [
        {
            "type": "lldb",
            "request": "launch",
            "name": "Debug unit tests in executable 'sui-prover'",
            "cargo": {
                "args": [
                    "install",
                    "--debug",
                    "--path",
                    "./crates/sui-prover"
                ],
            },
            "env": {
                "BOOGIE_EXE": "/usr/local/bin/boogie",
                "DOTNET_ROOT": "/opt/homebrew/opt/dotnet@8/libexec",
                "Z3_EXE": "/opt/homebrew/opt/z3/bin/z3",
            },
            "args": [],
            "stopOnEntry": false,
            "cwd": "${workspaceFolder}"
        },
    ]
}
```

## Project Structure

- `crates/sui-prover/` - Main crate for the Sui Prover tool
- `crates/move-model/` - Move language model for formal verification
- `crates/move-stackless-bytecode/` - Stackless bytecode for verification
- `crates/move-prover-boogie-backend/` - Backend for Boogie verification

## Pull Request Process

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Run tests to ensure your changes work
5. Submit a pull request

## Resources

- [Sui Framework](https://github.com/asymptotic-code/sui)
- [Sui Kit Examples](https://github.com/asymptotic-code/sui-kit)
- [Sui Prover Workshop](https://github.com/asymptotic-code/sui-prover-workshop) 