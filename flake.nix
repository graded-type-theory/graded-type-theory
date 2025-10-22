{
  inputs = {
    nixpkgs.url = "nixpkgs/nixpkgs-unstable";
  };

  outputs = inputs@{ self, nixpkgs, ... }: let
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
  in {
    packages.${system} = rec {
      default = html;

      html = pkgs.stdenv.mkDerivation {
        name = "html";
        src = ./.;

        nativeBuildInputs = [
          (pkgs.agda.withPackages (ps: [ ps.standard-library ]))
        ];

        buildPhase = ''
          agda --html Everything.agda
        '';

        installPhase = ''
          cp -a html/README.html html/index.html
          mv html "$out"
        '';
      };
    };
  };
}
