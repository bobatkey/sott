{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-25.11";
  };
  outputs = { self, flake-utils, nixpkgs }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_5_3;
      in
        {
          devShells.default = pkgs.mkShell {
            nativeBuildInputs = with ocamlPackages; [
              ocaml
              findlib
              pkgs.dune
              ocaml-lsp
              utop
            ];
            buildInputs = with ocamlPackages; [
              menhir
              cmdliner
            ];
          };
        });
}
