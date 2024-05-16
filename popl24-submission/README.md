# README

This artifact consists of two separate mechanized proofs:

* the Coq version

* the LiquidHaskell version

Below we give "kick the tires" instructions on how to get the mechanized proofs running.
First we give installation instructions for your own system. Because LiquidHaskell requires
a lot of memory and disk space, the verification peformance will likely be better if it
can be run on your own system. We also include instructions for using a virtual machine image.

## Kick the Tires: the Coq Mechanization

The only real requirement to run the Coq mechanization is a modern version of Coq on your
system. We've tested this development with 8.15.1, 8.17.0, and 8.18.0.

If you need to install Coq, here are step-by-step instructions.

1. First install the `opam` package manager, which you can most likely do with your
system's package manager. For instance, on a debian-like distribution, you can run

```
apt install opam
```

2. To set up `opam` run

```
opam init
```

followed by

```
eval $(opam env)
```

3. Install `coq` by running

```
opam install coq
```

You can verify the installation and your path by running `which coqc` and `coqc --version`.

Now that you've installed Coq (or already had it installed), download the research artifact
and `cd` into the `coq-SystemRF` directory.

To build and check the mechanization, run the `configure` script to build a makefile as follows:

```
./configure
make
```

Checking the mechanization should take 30 seconds to a minute or two, depending on your system.

### Virtual Machine instructions

We have included a VirtualBox image for Debian 12.2 with all of the necessary packages
and dependencies installed. For this mechanization, this comprises opam 2.1.2 and coq 8.18.0.

The username and password for the linux user is vboxuser/vboxuser. This is also the root password.

Load up the virtual machine image, log in to Debian, and open a terminal in Debian. The artifact
has already been placed into the home directory; just `cd` into `coq-SystemRF`.

Follow the instructions above starting with "To build and check the mechanization..."

## Kick the Tires: the LiquidHaskell Mechanization

The LiquidHaskell mechanization has more dependencies: the Z3 SMT sovler and the Haskell ecosystem.

First, let's install the Z3 SMT solver, which is not part of the Haskell ecosystem.
A version like 4.8.12 or newer should be fine. We have tested successfully with 4.8.12, 4.8.13, 4.8.16, and 4.8.17.

You can most likely get a version at least 4.8.12 or above with your package manager by running a command such as (for Debian):

```
sudo apt install z3
```

If your package manager only has an older version available, you can download the binaries for the most recent release here:

```
https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip
```

Next, we need the Haskell toolchain (specifically we need `stack`). The easiest way to do this is to 
install GHCup. Run the following *without* sudo (if you don't have cURL, you can get that with
`sudo apt install curl` for example):

```
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

To build and check the mechanization, run 

```
stack clean --full; stack build
```

 he first time stack build is run it may take 15 minutes or more to compile GHC and LiquidHaskell and its dependencies. Compiling and checking the mechanization will take at least 30 minutes. These times are dependent on your system, and particularly on how many physical cores your CPU has.

If you stop checking part of the way through, you can continue from the same module with stack build or start from the beginning with `stack clean --full`.

### Virtual Machine instructions

The VirtualBox image we've provided also contains everything to run the LiquidHaskell mechanization. 
Load up the virtual machine image, log in to Debian, and open a terminal in Debian. The artifact
has already been placed into the home directory; just `cd` into `liquid-SystemRF`.

Follow the instructions above starting with "To build and check the mechanization..."

## List of Claims/Theorems

Requirement 1 of the paper (ln 577) corresponds to the following in the Coq mechanization:

 * Part (1) is proven in `lem_wf_tybc` and `lem_wf_tyic` in `SystemRF/PrimitivesWFType.v`.

 * Part (2) is proven in `lem_wf_ty` in `SystemRF/PrimitivesWFType.v`.

 * Part (3) is proven in `lem_delta_ty'c` in `SystemRF/PrimitivesDeltaTyping.v`.

 * Part (4) is proven in `lem_deltaT_ty'c` in `SystemRF/PrimitivesDeltaTyping.v`.

In the LiquidHaskell mechanization:

 * Part (1) is *assumed* in `lem_wf_tybc` and `lem_wf_tyic` in `PrimitivesWFType.hs`.

 * Part (2) is *assumed* in `lem_wf_ty` in `PrimitivesWFType.hs`.

 * Part (3) is *assumed* in `lem_delta_ty'c` in `PrimitivesWFType.hs`.

 * Part (4) is *assumed* in `lem_deltaT_ty'c` in `PrimitivesWFType.hs`.

Requirement 2 of the paper (ln 665) is implemented in Coq in the definition of datatype `Implies`
in `Typing.hs`.

Theorem 5.1 of the paper (Denotational Soundness, ln 787) is proven in Coq in `lem_denote_sound`
in `Denotations/DenotationalSoundness.v`.
This is not found in the LiquidHaskell mechanization because the Denotational Semantics could
not be encoded in LiquidHaskell (ln 1020).

Lemma 5.2 of the paper (Selfified Denotations, ln 793) is proven in Coq in
`lem_denotations_selfify'` and `lem_denotations_selfify` in `Denotations/SelfifyDenotations.v`.
This is not found in the LiquidHaskell mechanization because the Denotational Semantics could
not be encoded in LiquidHaskell (ln 1020).

Theorem 5.3 of the paper (Type Safety, ln 801)  is proven in Coq for System RF in 
`thm_soundness` in `SystemRF/MainTheorems.v`. 
In LiquidHaskell, it is proven in `thm_soundness` in `MainTheorems.hs`.
We explicitly prove part (1). Part (2) follows trivially because `error` cannot be typed.


Lemma 5.4 of the paper (Progress, ln 809) is proven in Coq for System RF in 
`thm_progress'` and `thm_progress` in `SystemRF/MainTheorems.v`.
In LiquidHaskell, it is proven in `thm_progress` in `MainTheorems.hs`.

Lemma 5.5 of the paper (Preservation, ln 814) is proven in Coq for System RF in 
`thm_preservation'` and `thm_preservation` in `SystemRF/MainTheorems.v`.
In LiquidHaskell, it is proven in `thm_preservation` in `MainTheorems.hs`.

Lemma 5.6 of the paper (Transitivity, ln 825) is proven in Coq for System RF in 
`lem_sub_trans'` and `lem_sub_trans` in `SystemRF/LemmasTransitive.v`.
In LiquidHaskell, it is proven in `lem_sub_trans` in `LemmasTransitive.hs`.

Lemma 5.7 of the paper (Inversion of T-Abs/T-TAbs, ln 834) is proven in Coq for System RF in 
`lem_invert_tabs` and `lem_invert_tabst` in `SystemRF/LemmasInversion.v`.
In LiquidHaskell, it is proven in  em_invert_tabs` and `lem_invert_tabst` 
in `LemmasInversion.hs`.

Lemma 5.8 of the paper (Substitution, ln 851) is proven in Coq for SystemRF in 
`lem_subst_typ'` in `SystemRF/SubstitutionLemmaTyp.v`
and in `lem_subst_tv_typ'` in `SystemRF/SubstitutionLemmaTypTV.v`.
In LiquidHaskell, it is proven in `lem_subst_typ` and `lem_subst_sub`
in `SubstitutionLemmaTyp.hs` and in lem_subst_tv_typ` and `lem_subst_tv_sub`
in `SubstitutionLemmaTypTV.hs`.

Lemma 5.9 of the paper (Weakening, ln 862) is proven in Coq for SystemRF in 
`lem_weaken_typ'` in `SystemRF/LemmasWeakenTyp.v`
and in `lem_weaken_tv_typ'` in `SystemRF/LemmasWeakenTypTV.v`.
In LiquidHaskell, it is proven in `lem_weaken_typ` and `lem_weaken_subtype`
in `LemmasWeakenTyp.hs` and in lem_weaken_tv_typ` and `lem_weaken_tv_subtype`
in `LemmasWeakenTypTV.hs`.

For Lemma 5.10 of the paper (Narrowing, ln 872),
part (1) is proven in Coq for SystemRF in `lem_narrow_wf` in `SystemRF/LemmasWellFormedness.v`, and
parts (2-3) are proven in Coq for SystemRF in `lem_narrow_typ'` in `SystemRF/LemmasNarrowing.v`.
In LiquidHaskell, part (1) is proven in `lem_narrow_wf` in `LemmasWellFormedness.hs`,
and parts (2-3) are proven in `lem_narrow_typ` and `lem_narrow_sub` in `LemmasNarrowingTyp.hs`.

For Lemma 5.11 of the paper (Exact Typing, ln 879),
part (1) is proven in Coq for SystemRF in `lem_exact_subtype` in `SystemRF/LemmasExactness.v`, and
part (2) is proven in Coq for SystemRF in `lem_exact_type` in `SystemRF/LemmasExactness.v`.
In LiquidHaskell, part (1) is proven in `lem_exact_subtype` in `LemmasExactness.hs`,
and part (2) is proven in `lem_exact_type` in `LemmasExactness.hs`.
