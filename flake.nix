{
  description = "A flake for building Liquid Haskell";

  inputs.nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.rest-rewrite.url = "github:connorbaker/rest/eb12a7107ec98e2b06cf33777479148514aff4ce";

  outputs =
    { self
    , nixpkgs
    , flake-utils
    , rest-rewrite
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      compiler = "ghc8107";
      pkgs = nixpkgs.legacyPackages.${system};
      rest-rewrite-deps = rest-rewrite.devShells.${system}.default.nativeBuildInputs;
    in
    {
      devShells.default = pkgs.mkShell {
        nativeBuildInputs = with pkgs; [ haskell.compiler.${compiler} cabal-install z3 ] ++ rest-rewrite-deps;
        NIX_PATH = "nixpkgs=${nixpkgs}";
      };
    });
}
