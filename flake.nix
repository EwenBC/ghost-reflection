{
  description = "Environment for GTT";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.11";
  };

  outputs = {nixpkgs, ...}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs {inherit system; };
  in {
    devShells.x86_64-linux.default = pkgs.mkShell {
      packages = with pkgs; [
        coqPackages_9_0.coq
        coqPackages_9_0.coq.ocamlPackages.findlib 
        # Rocq extensions are bugged without findlib
        coqPackages_9_0.stdlib
        coqPackages_9_0.equations

        coqPackages_9_0.autosubst-ocaml

        rocqPackages.vsrocq-language-server
      ];
      shellHook = ''unset COQPATH''; # only ROCQPATH sould exists
    };
  };

}
