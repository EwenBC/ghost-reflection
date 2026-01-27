{
  description = "Environment for GTT";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.11";
  };

  outputs = {nixpkgs, ...}:
  let
    lib = nixpkgs.lib;
    system = "x86_64-linux";
    pkgs = import nixpkgs {inherit system; };
  in {
    devShells.x86_64-linux.default = pkgs.mkShell {
      packages = with pkgs; [
        coq_8_19
        coqPackages_8_19.coq.ocamlPackages.findlib 
        # Rocq extensions are bugged without findlib
        coqPackages_8_19.stdlib
        coqPackages_8_19.equations

        coqPackages_8_19.autosubst-ocaml
      ];
    };
  };

}
