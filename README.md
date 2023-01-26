# MonadicDerivatives

## Backend

- to compile the backend: stack build
- to run it (to launch the server): stack exec RegExp-exe

## Frontend

- to run the reflex-platform: reflex-platform/try-reflex
- to compile (in the reflex-platform nix-shell):
  cabal --project-file=cabal-ghcjs.project --builddir=dist-ghcjs new-build all
  
The local path to the index.html file (root of the app) is printed at the end of the frontend compilation, and can be
launch with a classic browser while the server is running.

