# default.nix
{ system ? builtins.currentSystem }:
(import ./reflex-platform { inherit system; }).project ({ pkgs, ... }: {
  packages = {
    common = ./common;
    frontend = ./frontend;
  };

  shells = {
    ghcjs = ["common" "frontend"];
  };

  overrides = self: super: {
      prim-uniq = self.callHackage "prim-uniq" "0.1.0.1" {};
      dependent-map = self.callHackage "dependent-map" "0.3.1.0" {};
      dependent-sum = self.callHackage "dependent-sum" "0.6.2.0" {};
      reflex = self.callHackage "reflex" "0.7.1.0" {};
      reflex-dom-core = self.callHackage "reflex-dom-core" "0.6.0.0" {};
      reflex-dom = self.callHackage "reflex-dom" "0.6.0.0" {};
      servant-reflex = self.callHackage "servant-reflex" "0.3.5" {};
    }; 
})
