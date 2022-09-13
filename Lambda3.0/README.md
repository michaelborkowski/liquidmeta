# liquidmeta

The software requirements to run the artifact (compile with `GHC` and check with `LiquidHaskell`) are:
  - a recent version of `stack` such as `2.7.3` or `2.7.5`
  - The `Z3` SMT solver.

Our development triggers some bugs in some older versions of `Z3`; however our testing succeeded with `4.8.12`, `4.8.13`, `4.8.16`, and `4.8.17`. It is not required to have `GHC` or `LiquidHaskell` installed because `stack` will take care of those. 

If you are running WSL in Windows, then WSL2 is required because recent versions of GHC will not compile in WSL1.

To build and check the mechanization, run `stack clean --full; stack build`. The first time `stack build` is run it may take 15 minutes or more to compile `GHC` and `LiquidHaskell` and its dependencies.  Compiling and checking the mechanization will take at least 30 minutes. These times are dependent on your system, and particularly on how many physical cores your CPU has.

If you stop checking part of the way through, you can continue from the same module with `stack build` or start from the beginning with `stack clean --full`.
