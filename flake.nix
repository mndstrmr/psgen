{
  inputs.nixpkgs.url = "nixpkgs/nixos-25.05";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  inputs.gomod2nix = {
    url = "github:tweag/gomod2nix";
    inputs.nixpkgs.follows = "nixpkgs";
    inputs.flake-utils.follows = "flake-utils";
  };

  outputs = {self, ...}@inputs:
    let

      # Generate a user-friendly version number.
      lastModifiedDate = self.lastModifiedDate or self.lastModified or "19700101";
      version = builtins.substring 0 8 lastModifiedDate;

      # System types to support.
      supportedSystems = with inputs.flake-utils.lib.system; [
        x86_64-linux
        # Below not tested but no reason why they shouldn't work.
        x86_64-darwin
        aarch64-linux
        aarch64-darwin
      ];

    in inputs.flake-utils.lib.eachSystem supportedSystems (system:
      let

        pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [ inputs.gomod2nix.overlays.default ];
        };

        psgen = pkgs.buildGoApplication {
          pname = "psgen";
          inherit version;
          src = ./.;
          pwd = ./.;
          modules = ./gomod2nix.toml;
          meta = with pkgs.lib; {
            description = "A theorem proving type language which generates SystemVerilog and TCL.";
            longDescription = ''
              psgen is a theorem proving type language which generates SystemVerilog and TCL.
              It dramatically simplifies case splitting, inductive proofs and similar strategies often found in formal verification.
            '';
            mainProgram = "psgen";
            homepage = "https://github.com/mndstrmr/psgen";
            maintainers = [ ];
            # license = ;
          };
        };

        psgen_env = pkgs.mkGoEnv {inherit (psgen) pwd modules;};

      in {

        packages = {
          inherit psgen;
          default = psgen;
        };
        devShells = {
          default = pkgs.mkShellNoCC {
            buildInputs = [
              psgen_env
            ];
          };
        };
        apps = let
          mkApp = package: {type = "app"; program = "${package}/bin/${package.meta.mainProgram or package.pname}";};
          psgen_app = mkApp psgen;
          update = mkApp pkgs.gomod2nix;
        in rec {
          psgen = psgen_app;
          default = psgen_app;
          inherit update;
        };

      });
}
