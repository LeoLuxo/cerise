{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    opam-nix.url = "github:tweag/opam-nix";

    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    opam-coq = {
      url = "github:coq/opam";
      flake = false;
    };
  };

  outputs =
    {
      self,
      flake-utils,
      nixpkgs,
      opam-nix,

      opam-repository,
      opam-coq,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        on = opam-nix.lib.${system};

        name = "coq-cerise";

        repos = [
          "${opam-repository}"
          "${opam-coq}/released" # Contains iris, equations and stdpp
          "${opam-coq}/extra-dev" # Contains coq-lsp and vscoq
        ];

        # Extra dependencies to add to the project; the ones from the .opam file will be loaded automatically
        extraQuery = {
          ocaml-base-compiler = "4.14.1"; # Required for version 8.18 of coq
          coq-lsp = "*";
          vscoq-language-server = "2.2.5";
        };

        # Build the opam project
        project = on.buildOpamProject' { inherit pkgs repos; } ./. extraQuery;
      in
      {

        devShells.default = pkgs.mkShell (
          let
            inherit (project.${name}) pname buildInputs;
          in
          {
            name = pname + "-dev";
            packages = buildInputs ++ [
              pkgs.gnumake

              # Add both LSPs, use whichever is preferred
              project.coq-lsp
              project.vscoq-language-server
            ];
          }
        );
      }
    );
}
