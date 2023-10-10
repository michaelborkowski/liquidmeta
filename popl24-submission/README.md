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
