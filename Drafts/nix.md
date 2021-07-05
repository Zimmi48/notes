Nix is a ["purely functional package manager"](https://nixos.org/nix/) I have been using for almost two years now. It is the package manager of the NixOS GNU/Linux distribution, but it is also usable in other Unix environments (in particular, other GNU/Linux distributions, MacOS and Windows Subsystem for Linux). And it is great for setting up development environments, for instance to use Coq with the [MathComp library](https://math-comp.github.io/math-comp/).

## How to install an external package for Coq

While most Linux distributions should have a package for Coq (generally pretty outdated, unless your distribution uses a rolling release model like Arch Linux), if a user wants to use an external Coq package, it's pretty unlikely to find it in the distribution. So most people will recommend you to install the package using OPAM instead.

OPAM is a source-based package manager for OCaml which is also used to distribute Coq packages (even when these packages only contain Coq source files and no OCaml). Explanations on how to use it can be found on the [official Coq website](https://coq.inria.fr/opam/www/using.html). Installing a Coq package using OPAM generally supposes to also build Coq from sources using OPAM (because Coq is listed as a dependency of the package). This can take quite a while.

The good news is an alternative exists, and it's Nix. Nix is also a source-based package manager but with a binary cache. Installing Coq with Nix should be pretty fast because it will download the software from the binary cache. Coq packages are also available through Nix (as an alternative to OPAM) but their compilation output is not cached, so you will still have to wait for them to build.

To give you a taste of how it may feel, here is a way to install Nix:

```
curl https://nixos.org/nix/install | sh
```

And once it is done, here is a way to open CoqIDE 8.8 with the Math-Classes library ready to be imported (the first time you run this command it will take a few minutes and print a lot of stuff including many warnings, that's Math-Classes and its dependencies being compiled; the second time it should be almost instantaneous):

```
nix-shell -p coq_8_8 coqPackages_8_8.math-classes --run coqide
```

You may also remove the `--run coqide` part, in which case you will be dropped into a shell where `coqtop`, `coqc`, `coq_makefile`, and associated commands, are available and the Math-Classes library is listed in `$COQPATH`, ready to compile one of your project, run Emacs, etc.

Another advantage that comes for free with Nix is the ability to switch easily between different versions of the same software. Say now that you want to run Coq 8.7 with Math-Classes:

```
nix-shell coq_8_7 coqPackages_8_7.mathcomp -c coqide
```

You can go back and forth between the two versions: both will be compiled only once. Achieving the same thing with OPAM requires quite a few tricks.

### Some basic principles about Nix

With Nix, you can also install packages, like Coq. But if you try to install a Coq library, you won't be able to load it. It took me a while to get this but the Nix-way to use libraries is not to install them but to load them in a `nix-shell` and Coq is no exception. Let me now explain why it is so.

What does the "purely functional" part in "Nix is a purely functional package manager" mean? It means that, once installed with Nix, a package is immutable, which wouldn't be the case with most other package managers. To achieve this, Nix installs packages in a non-standard location, for instance `/nix/store/z0qfka9n4fdbd1gak7s26g4i80pqcbf5-coq-8.8.0`. Updating a package means installing a new version, *somewhere else* (in particular, the hash in the path will be different) then updating a symbolic link to point to the latest version. It has lots of advantages. Upgrades are atomic: if the upgrade fails in the middle, it won't leave your system in a bad state; so if you feel like it is taking too long, you can just kill it. You can have several versions installed in parallel and switch from one to the other. And so on.

But Coq, like lots of other programming languages, expects its extensions to be installed at a very specific place: the `lib/coq/user-contrib/` sub-directory of the Coq install location. Nix can't do that, so instead it installs Coq packages in other locations and then it updates the `$COQPATH` environment variable to point to them. Because this is an environment variable, it can't just be set once and for all at install time. So it sets it when you open a `nix-shell`. And that's why you need to be in a `nix-shell` to load Coq packages.

## Nix tricks

### Searching for packages

What packages are available in nixpkgs (the collection of packages for Nix) for a given Coq version? My preferred way of finding this information is by using auto-completion in `nix repl`.

`nix repl` is a Read-Eval-Print-Loop. Run it like this to load the nixpkgs collection:

```
nix-repl '<nixpkgs>'
```

Then type `coqP` and use tab to auto-complete into one of the Coq package sets, then add a dot and use tab again to see what is available in there. At the time of writing, there is much more available in the `coqPackages_8_7` set than in `coqPackages_8_8` which is still too recent.

### Saving a complex environment

Instead of loading your development environment with a long command each time you may also create a file called `default.nix` in the directory where you have your project. Then just typing `nix-shell` when in this directory will load it.

Here is an example of such a file:

```
{ pkgs ? (import <nixpkgs> {}), coqPackages ? pkgs.coqPackages_8_7 }:

with pkgs;
with coqPackages;

stdenv.mkDerivation rec {

  name = "my-coq-env";

  buildInputs = [
    coq
    math-classes
    equations
  ];

}
```

This file contains the definition of a function whose parameters are all optional. You may use the second one to change the version of Coq you use:

```
nix-shell --arg coqPackages "with import <nixpkgs> {}; coqPackages_8_6
```
