# archive-opam

Archive opam packages from the main opam-repository to the
opam-repository-archive. This adds the required fields for the archive, also
upper bounds.

## Installation

  opam pin add archive-opam git+https://github.com/hannesm/archive-opam.git

## Usage

For development, the set of flags are pretty useful:

  archive-opam --unavailable --dry-run --no-upper-bound=ocaml --no-upper-bound=dune --no-upper-bound=odoc --ignore-tezos --color=always | less -R

## LICENSE

ISC