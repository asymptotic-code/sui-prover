# Sui Prover

## Install
`cargo install --locked --path ./crates/sui-prover`

## Use
`sui-prover [OPTIONS]`

## Test
`cd crates/sui-prover`

`cargo test`

## Debug 
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
                // please check if your local deps mathces given ones
                "BOOGIE_EXE": "/usr/local/bin/boogie",
                "DOTNET_ROOT": "/opt/homebrew/opt/dotnet@8/libexec",
                "Z3_EXE": "/opt/homebrew/opt/z3/bin/z3",
            },
            "args": [],
            "stopOnEntry": false,
            // please add execution folder for prover
            "cwd": "<>"
        },
    ]
}
```
