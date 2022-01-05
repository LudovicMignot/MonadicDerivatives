# MonadicDerivatives

## Backend

- to compile the backend: stack build
- to run it (to launch the server): stack exec Regexp-exe

## Frontend

- to run the reflex-platform: reflex-platform/try-reflex
- to compile (in the reflex-platform nix-shell):
  nix-shell -A shells.ghcjs --run "cabal --project-file=cabal-ghcjs.project --builddir=dist-ghcjs new-build all"
  
The local path to the index.html file (root of the app) is printed at the end of the frontend compilation

